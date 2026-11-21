// Shopping Sessions pipeline. Implements rules.md exactly.
use memmap2::Mmap;

use rayon::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::hash::{BuildHasherDefault, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Instant;

const DAY: i64 = 86_400_000;
const WEEK: i64 = 7 * DAY;
const GAP: i64 = 1_800_000;
const NB: usize = 64; // coarse buckets by event id
const NP: usize = 64; // coarse buckets by user / person
const NS: usize = 64; // fine buckets inside a coarse one

// ---------------------------------------------------------------- keys
// A string packed exactly into a u128 when it has at most 15 bytes:
// bytes big-endian in the high 15 bytes, length in the low byte. Comparing two
// packed keys as integers gives byte-wise order. Longer strings get the low
// byte 0xFF and a 120-bit hash; their bytes are kept in LONG.
type Key = u128;
static LONG: OnceLock<Mutex<HashMap<Key, Vec<u8>>>> = OnceLock::new();

#[inline]
fn pack(s: &[u8]) -> Key {
    let n = s.len();
    if n <= 15 {
        let (hi, lo) = if n >= 8 {
            let a = u64::from_be_bytes(s[0..8].try_into().unwrap());
            let b = u64::from_be_bytes(s[n - 8..n].try_into().unwrap());
            (a, if n == 8 { 0 } else { b << (8 * (16 - n)) })
        } else if n >= 4 {
            let a = u32::from_be_bytes(s[0..4].try_into().unwrap()) as u64;
            let b = u32::from_be_bytes(s[n - 4..n].try_into().unwrap()) as u64;
            // bytes 0..4 from a, bytes 4..n from the tail of b
            let tail = if n == 4 { 0 } else { (b << (8 * (8 - n))) & (u64::MAX >> 32) };
            ((a << 32) | tail, 0)
        } else {
            let mut v = 0u64;
            for (i, &c) in s.iter().enumerate() {
                v |= (c as u64) << (56 - 8 * i);
            }
            (v, 0)
        };
        ((hi as u128) << 64) | (lo | n as u64) as u128
    } else {
        pack_long(s)
    }
}

#[cold]
fn pack_long(s: &[u8]) -> Key {
    let mut h1: u64 = 0xcbf29ce484222325;
    let mut h2: u64 = 0x84222325cbf29ce4;
    for &b in s {
        h1 = (h1 ^ b as u64).wrapping_mul(0x100000001b3);
        h2 = (h2 ^ b as u64).wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29);
    }
    let k = ((h1 as u128) << 64 | (h2 as u128)) | 0xFF;
    LONG.get_or_init(|| Mutex::new(HashMap::new()))
        .lock()
        .unwrap()
        .entry(k)
        .or_insert_with(|| s.to_vec());
    k
}

fn unpack(k: Key) -> Vec<u8> {
    let n = (k & 0xFF) as usize;
    if n == 0xFF {
        LONG.get().unwrap().lock().unwrap()[&k].clone()
    } else {
        k.to_be_bytes()[..n].to_vec()
    }
}

#[inline]
fn key_cmp(a: Key, b: Key) -> std::cmp::Ordering {
    if (a & 0xFF) == 0xFF || (b & 0xFF) == 0xFF {
        unpack(a).cmp(&unpack(b))
    } else {
        a.cmp(&b)
    }
}

#[inline]
fn mix(k: Key) -> u64 {
    let x = (k as u64) ^ ((k >> 64) as u64).wrapping_mul(0x9E3779B97F4A7C15);
    let x = (x ^ (x >> 31)).wrapping_mul(0xBF58476D1CE4E5B9);
    x ^ (x >> 29)
}

#[derive(Default)]
struct KeyHasher(u64);
impl Hasher for KeyHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x100000001b3);
        }
    }
    fn write_u128(&mut self, k: u128) {
        self.0 = mix(k);
    }
}
type KMap<V> = HashMap<Key, V, BuildHasherDefault<KeyHasher>>;

// ---------------------------------------------------------------- time
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

static YEAR_DAYS: OnceLock<Vec<i32>> = OnceLock::new();
const CUM: [[i32; 13]; 2] = [
    [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334, 365],
    [0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335, 366],
];
fn year_days() -> &'static [i32] {
    YEAR_DAYS.get_or_init(|| (0..10000).map(|y| days_from_civil(y, 1, 1) as i32).collect())
}

/// Parses F1, F2 or F3 into epoch ms. None for anything else, including F3
/// values too big for i64 (they are outside every window anyway).
#[inline(always)]
fn parse_ts(s: &[u8]) -> Option<i64> {
    let n = s.len();
    if (n == 20 || n == 25) && s[4] == b'-' {
        return parse_iso(s);
    }
    if n == 0 {
        return None;
    }
    let mut v: i64 = 0;
    for &c in s {
        let d = c.wrapping_sub(b'0');
        if d > 9 {
            return None;
        }
        v = v.checked_mul(10)?.checked_add(d as i64)?;
    }
    Some(v)
}

#[inline(always)]
fn parse_iso(s: &[u8]) -> Option<i64> {
    let n = s.len();
    let g = |i: usize| s[i].wrapping_sub(b'0') as u32;
    let d = [g(0), g(1), g(2), g(3), g(5), g(6), g(8), g(9), g(11), g(12), g(14), g(15), g(17), g(18)];
    let mut big = 0u32;
    for &x in &d {
        big |= (x > 9) as u32;
    }
    let sep = (s[7] != b'-') as u32 | (s[10] != b'T') as u32 | (s[13] != b':') as u32 | (s[16] != b':') as u32;
    if big | sep != 0 {
        return None;
    }
    let y = (d[0] * 1000 + d[1] * 100 + d[2] * 10 + d[3]) as usize;
    let mo = (d[4] * 10 + d[5]) as usize;
    let dd = (d[6] * 10 + d[7]) as i32;
    let h = (d[8] * 10 + d[9]) as i64;
    let mi = (d[10] * 10 + d[11]) as i64;
    let se = (d[12] * 10 + d[13]) as i64;
    if !(1..=12).contains(&mo) || dd < 1 || h > 23 || mi > 59 || se > 59 {
        return None;
    }
    let leap = ((y % 4 == 0 && y % 100 != 0) || y % 400 == 0) as usize;
    let cum = &CUM[leap];
    if dd > cum[mo] - cum[mo - 1] {
        return None;
    }
    let days = (year_days()[y] + cum[mo - 1] + dd - 1) as i64;
    let base = (days * 86400 + h * 3600 + mi * 60 + se) * 1000;
    if n == 20 {
        if s[19] != b'Z' {
            return None;
        }
        Some(base)
    } else {
        let sign = match s[19] {
            b'+' => 1,
            b'-' => -1,
            _ => return None,
        };
        let (a, b, c, e) = (g(20), g(21), g(23), g(24));
        if s[22] != b':' || a > 9 || b > 9 || c > 9 || e > 9 {
            return None;
        }
        let oh = (a * 10 + b) as i64;
        let om = (c * 10 + e) as i64;
        if oh > 23 || om > 59 {
            return None;
        }
        Some(base - sign * (oh * 3600 + om * 60) * 1000)
    }
}

// ---------------------------------------------------------------- inputs
struct Chunk {
    data: &'static [u8],
}

fn list_csv(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().map(|x| x == "csv").unwrap_or(false) && p.is_file())
            .collect(),
        Err(_) => vec![],
    };
    v.sort();
    v
}

fn map_file(p: &Path) -> &'static [u8] {
    let f = File::open(p).unwrap();
    let len = f.metadata().unwrap().len();
    if len == 0 {
        return &[];
    }
    let m = unsafe { Mmap::map(&f).unwrap() };
    let _ = m.advise(memmap2::Advice::Sequential);
    let m: &'static Mmap = Box::leak(Box::new(m));
    &m[..]
}

/// Data part of a file (after the header line), cut into chunks at line ends.
fn chunks_of(files: &[PathBuf], target: usize) -> Vec<Chunk> {
    let mut out = vec![];
    for p in files {
        let all = map_file(p);
        let body = match memchr::memchr(b'\n', all) {
            Some(i) => &all[i + 1..],
            None => continue,
        };
        let mut s = 0;
        while s < body.len() {
            let mut e = (s + target).min(body.len());
            if e < body.len() {
                e = match memchr::memchr(b'\n', &body[e..]) {
                    Some(r) => e + r + 1,
                    None => body.len(),
                };
            }
            out.push(Chunk { data: &body[s..e] });
            s = e;
        }
    }
    out
}

fn read_small(p: &Path) -> Vec<u8> {
    std::fs::read(p).unwrap_or_default()
}

// ---------------------------------------------------------------- fast scanner
// Two bit masks per 64 bytes: delimiters (comma or newline) and quotes. Lines
// are walked by delimiter bits; quotes are checked with bit tests, so there is
// no branch on where quotes happen to be.
#[inline(always)]
fn masks_scalar(b: &[u8]) -> (u64, u64) {
    let (mut d, mut q) = (0u64, 0u64);
    for (i, &c) in b.iter().enumerate() {
        d |= ((c == b',' || c == b'\n') as u64) << i;
        q |= ((c == b'"') as u64) << i;
    }
    (d, q)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn fill_masks_avx2(buf: &[u8], dm: &mut Vec<u64>, qm: &mut Vec<u64>) {
    use std::arch::x86_64::*;
    let n = buf.len() / 64;
    let cm = _mm256_set1_epi8(b',' as i8);
    let qq = _mm256_set1_epi8(b'"' as i8);
    let nm = _mm256_set1_epi8(b'\n' as i8);
    for w in 0..n {
        unsafe {
            let p = buf.as_ptr().add(w * 64) as *const __m256i;
            let v0 = _mm256_loadu_si256(p);
            let v1 = _mm256_loadu_si256(p.add(1));
            let d0 = _mm256_or_si256(_mm256_cmpeq_epi8(v0, cm), _mm256_cmpeq_epi8(v0, nm));
            let d1 = _mm256_or_si256(_mm256_cmpeq_epi8(v1, cm), _mm256_cmpeq_epi8(v1, nm));
            let q0 = _mm256_cmpeq_epi8(v0, qq);
            let q1 = _mm256_cmpeq_epi8(v1, qq);
            *dm.get_unchecked_mut(w) = (_mm256_movemask_epi8(d0) as u32 as u64) | ((_mm256_movemask_epi8(d1) as u32 as u64) << 32);
            *qm.get_unchecked_mut(w) = (_mm256_movemask_epi8(q0) as u32 as u64) | ((_mm256_movemask_epi8(q1) as u32 as u64) << 32);
        }
    }
}

fn fill_masks(buf: &[u8], dm: &mut Vec<u64>, qm: &mut Vec<u64>) {
    let words = buf.len().div_ceil(64) + 1;
    dm.clear();
    qm.clear();
    dm.resize(words, 0);
    qm.resize(words, 0);
    let full = buf.len() / 64;
    #[cfg(target_arch = "x86_64")]
    let done = if is_x86_feature_detected!("avx2") {
        unsafe { fill_masks_avx2(buf, dm, qm) };
        full
    } else {
        0
    };
    #[cfg(not(target_arch = "x86_64"))]
    let done = 0;
    for w in done..full {
        let (d, q) = masks_scalar(&buf[w * 64..w * 64 + 64]);
        dm[w] = d;
        qm[w] = q;
    }
    if buf.len() % 64 != 0 {
        let (d, q) = masks_scalar(&buf[full * 64..]);
        dm[full] = d;
        qm[full] = q;
    }
}

#[inline(always)]
fn bit(m: &[u64], p: usize) -> u32 {
    unsafe { ((*m.get_unchecked(p >> 6) >> (p & 63)) & 1) as u32 }
}

#[inline(always)]
fn popcnt_range(m: &[u64], a: usize, b: usize) -> u32 {
    // bits in [a, b)
    if a >= b {
        return 0;
    }
    let (wa, wb) = (a >> 6, (b - 1) >> 6);
    let lo_mask = u64::MAX << (a & 63);
    let hi_mask = u64::MAX >> (63 - ((b - 1) & 63));
    unsafe {
        if wa == wb {
            return (*m.get_unchecked(wa) & lo_mask & hi_mask).count_ones();
        }
        let mut c = (*m.get_unchecked(wa) & lo_mask).count_ones() + (*m.get_unchecked(wb) & hi_mask).count_ones();
        for w in wa + 1..wb {
            c += m.get_unchecked(w).count_ones();
        }
        c
    }
}

thread_local! {
    static MASKS: std::cell::RefCell<(Vec<u64>, Vec<u64>)> = const { std::cell::RefCell::new((Vec::new(), Vec::new())) };
}

/// Calls cb(buf, fields) for every well-formed line with exactly N fields.
fn scan<const N: usize, F: FnMut(&[u8], &[(u32, u32); N])>(buf: &[u8], mut cb: F) {
    MASKS.with(|mk| {
        let mut mk = mk.borrow_mut();
        let (dm, qm) = &mut *mk;
        fill_masks(buf, dm, qm);
        let len = buf.len();
        let mut fields = [(0u32, 0u32); N];
        let mut f = 0usize;
        let mut fs = 0usize;
        let mut ls = 0usize;
        let mut line = |ls: usize, end: usize, f: usize, fields: &mut [(u32, u32); N]| {
            if f != N {
                return;
            }
            let mut bad = 0u32;
            let mut cnt = 0u32;
            for fl in fields.iter_mut() {
                let (a, e) = (fl.0 as usize, fl.1 as usize);
                let l = e - a;
                let qs = if l > 0 { bit(qm, a) } else { 0 };
                let qe = if l > 0 { bit(qm, e - 1) } else { 0 };
                bad |= (qs ^ qe) | (qs & (l < 2) as u32);
                cnt += 2 * qs;
                fl.0 += qs;
                fl.1 -= qs;
            }
            if bad == 0 && popcnt_range(qm, ls, end) == cnt {
                cb(buf, fields);
            }
        };
        for w in 0..dm.len() {
            let mut m = dm[w];
            while m != 0 {
                let p = (w << 6) + m.trailing_zeros() as usize;
                m &= m - 1;
                if f < N {
                    fields[f] = (fs as u32, p as u32);
                }
                f += 1;
                fs = p + 1;
                if unsafe { *buf.get_unchecked(p) } == b'\n' {
                    line(ls, p, f, &mut fields);
                    f = 0;
                    ls = p + 1;
                }
            }
        }
        if ls < len {
            if f < N {
                fields[f] = (fs as u32, len as u32);
            }
            f += 1;
            line(ls, len, f, &mut fields);
        }
    });
}

#[inline(always)]
fn fl<'a>(buf: &'a [u8], r: (u32, u32)) -> &'a [u8] {
    unsafe { buf.get_unchecked(r.0 as usize..r.1 as usize) }
}

// ---------------------------------------------------------------- records
#[inline(always)]
fn hl(k: Key) -> (u64, u64) {
    ((k >> 64) as u64, k as u64)
}
#[inline(always)]
fn kk(h: u64, l: u64) -> Key {
    ((h as u128) << 64) | l as u128
}
#[inline(always)]
fn bkt(k: Key) -> usize {
    ((mix(k) >> 40) as usize) & (NP - 1)
}
#[inline(always)]
fn sbkt(k: Key) -> usize {
    ((mix(k) >> 46) as usize) & (NS - 1)
}
#[inline(always)]
fn esbkt(k: Key) -> usize {
    ((mix(k) >> 26) as usize) & (NS - 1)
}
#[inline(always)]
fn ebkt(k: Key) -> usize {
    ((mix(k) >> 20) as usize) & (NB - 1)
}

#[derive(Clone, Copy)]
struct Ev {
    e0: u64,
    e1: u64,
    ing: i64,
    u0: u64, // u0 == u1 == 0: invalid or late
    u1: u64,
    ts: u32, // ms since T0
    pc: u32, // price | cat << 24, 0 when not a purchase
}

#[derive(Clone, Copy)]
struct Sv {
    u0: u64,
    u1: u64,
    ts: u32,
    pc: u32,
}

#[derive(Clone, Copy)]
struct Cl {
    u0: u64,
    u1: u64,
    c0: u64,
    c1: u64,
    ts: u32,
    camp: u32,
}

struct URow {
    name: Key,
    day: i32,
    sessions: u32,
    events: u32,
    revenue: i64,
    top: u16, // u16::MAX = null
}

fn buckets<T>(n: usize) -> Vec<Vec<T>> {
    (0..n).map(|_| Vec::new()).collect()
}

/// Counting sort of v into `out` by a key in 0..nb; returns nb + 1 offsets.
fn partition<T: Copy>(v: &[T], nb: usize, key: impl Fn(&T) -> usize, out: &mut Vec<T>) -> Vec<usize> {
    let mut cnt = vec![0usize; nb + 1];
    for x in v {
        cnt[key(x) + 1] += 1;
    }
    for i in 0..nb {
        cnt[i + 1] += cnt[i];
    }
    out.clear();
    out.reserve(v.len());
    let mut pos = cnt.clone();
    unsafe {
        let o = out.as_mut_ptr();
        for x in v {
            let k = key(x);
            *o.add(*pos.get_unchecked(k)) = *x;
            *pos.get_unchecked_mut(k) += 1;
        }
        out.set_len(v.len());
    }
    cnt
}

fn gather<T: Copy>(parts: &[Vec<Vec<T>>], b: usize, extra: usize) -> Vec<T> {
    let n: usize = parts.iter().map(|p| p[b].len()).sum();
    let mut v = Vec::with_capacity(n + extra);
    for p in parts {
        v.extend_from_slice(&p[b]);
    }
    v
}

fn read_table2(p: &Path, mut f: impl FnMut(&[u8], &[u8])) {
    let b = read_small(p);
    let body = match memchr::memchr(b'\n', &b) {
        Some(i) => &b[i + 1..],
        None => &b[0..0],
    };
    scan::<2, _>(body, |buf, r| f(fl(buf, r[0]), fl(buf, r[1])));
}

fn main() {
    let t0 = Instant::now();
    let data = PathBuf::from(std::env::var("DATA_DIR").unwrap_or("/data".into()));
    let out = PathBuf::from(std::env::var("OUTPUT_DIR").unwrap_or("/output".into()));
    let verbose = std::env::var("VERBOSE").is_ok();
    if let Some(n) = std::env::var("NCPU").ok().and_then(|v| v.parse::<usize>().ok()).filter(|&n| n > 0) {
        let _ = rayon::ThreadPoolBuilder::new().num_threads(n).build_global();
    }
    let lap = |what: &str| {
        if verbose {
            let st = std::fs::read_to_string("/proc/self/stat").unwrap_or_default();
            let f: Vec<&str> = st.rsplit(')').next().unwrap_or("").split_whitespace().collect();
            let g = |i: usize| f.get(i).and_then(|x| x.parse::<f64>().ok()).unwrap_or(0.0);
            eprintln!("{:>8.3}s {:<16} minflt {:>9} user {:>6.2} sys {:>6.2}", t0.elapsed().as_secs_f64(), what, g(7), g(11) / 100.0, g(12) / 100.0);
        }
    };

    // manifest
    let man = String::from_utf8_lossy(&read_small(&data.join("manifest.json"))).into_owned();
    let getv = |k: &str| -> i64 {
        let i = man.find(&format!("\"{k}\"")).unwrap() + k.len() + 2;
        let rest = &man[i..];
        let a = rest.find('"').unwrap() + 1;
        let b = a + rest[a..].find('"').unwrap();
        parse_ts(rest[a..b].as_bytes()).unwrap()
    };
    let ws = getv("window_start");
    let we = getv("window_end");
    let t_zero = ws - WEEK; // every kept event and click is at or after this
    assert!(we - t_zero < u32::MAX as i64, "window too long for u32 offsets");
    let base_day = ws.div_euclid(DAY);
    let ndays = ((we - 1).div_euclid(DAY) - base_day + 1).max(1) as usize;

    // products and categories
    let mut cat_names: Vec<Vec<u8>> = vec![];
    let mut cat_idx: HashMap<Vec<u8>, u16> = HashMap::new();
    let mut prod: KMap<u32> = KMap::default();
    read_table2(&data.join("products.csv"), |p, c| {
        let n = cat_names.len() as u16;
        let ci = *cat_idx.entry(c.to_vec()).or_insert_with(|| {
            cat_names.push(c.to_vec());
            n
        });
        prod.insert(pack(p), ci as u32);
    });
    let unknown = cat_names.len() as u32;
    cat_names.push(b"unknown".to_vec());
    let ncat = cat_names.len();
    assert!(ncat <= 255);
    let mut order: Vec<usize> = (0..ncat).collect();
    order.sort_by(|&a, &b| cat_names[a].cmp(&cat_names[b]));
    let mut cat_rank = vec![0usize; ncat];
    for (r, &c) in order.iter().enumerate() {
        cat_rank[c] = r;
    }

    // campaigns
    let mut camp_ids: Vec<Vec<u8>> = vec![];
    let mut camp_ch: Vec<Vec<u8>> = vec![];
    let mut camp: KMap<u32> = KMap::default();
    read_table2(&data.join("campaigns.csv"), |id, ch| {
        let k = pack(id);
        if !camp.contains_key(&k) {
            camp.insert(k, camp_ids.len() as u32);
            camp_ids.push(id.to_vec());
            camp_ch.push(ch.to_vec());
        }
    });
    let ncamp = camp_ids.len();
    let organic = ncamp;
    lap("small files");

    let ev_files = list_csv(&data.join("events"));
    let cl_files = list_csv(&data.join("clicks"));
    let link_files = list_csv(&data.join("links"));

    // ------------------------------------------------ links -> per-bucket id -> name tables
    let link_tables: Vec<KMap<Key>> = {
        let link_chunks = chunks_of(&link_files, 4 << 20);
        let pairs: Vec<(Key, Key)> = link_chunks
            .par_iter()
            .flat_map_iter(|c| {
                let mut v = vec![];
                scan::<2, _>(c.data, |buf, r| {
                    let a = fl(buf, r[0]);
                    let b = fl(buf, r[1]);
                    if !a.is_empty() && !b.is_empty() {
                        v.push((pack(a), pack(b)));
                    }
                });
                v
            })
            .collect();
        lap("links parsed");
        let mut ent: Vec<(Key, u32)> = Vec::with_capacity(pairs.len() * 2);
        for (i, &(a, b)) in pairs.iter().enumerate() {
            ent.push((a, 2 * i as u32));
            ent.push((b, 2 * i as u32 + 1));
        }
        ent.par_sort_unstable_by_key(|e| e.0);
        lap("ids sorted");
        let mut ids: Vec<Key> = Vec::with_capacity(ent.len());
        let mut flat = vec![0u32; ent.len()];
        for &(k, at) in &ent {
            if ids.last() != Some(&k) {
                ids.push(k);
            }
            flat[at as usize] = ids.len() as u32 - 1;
        }
        drop(ent);
        let pidx: Vec<(u32, u32)> = flat.chunks_exact(2).map(|c| (c[0], c[1])).collect();
        lap("pidx");
        let mut parent: Vec<u32> = (0..ids.len() as u32).collect();
        fn find(p: &mut [u32], mut x: u32) -> u32 {
            while p[x as usize] != x {
                let g = p[p[x as usize] as usize];
                p[x as usize] = g;
                x = g;
            }
            x
        }
        for &(a, b) in &pidx {
            let ra = find(&mut parent, a);
            let rb = find(&mut parent, b);
            if ra != rb {
                if ra < rb {
                    parent[rb as usize] = ra;
                } else {
                    parent[ra as usize] = rb;
                }
            }
        }
        lap("union");
        // ids is sorted by u128, which is byte order for short keys, so the
        // smallest index in a set is its smallest ID unless long keys are involved.
        let any_long = ids.iter().any(|&k| (k & 0xFF) == 0xFF);
        let mut best: Vec<u32> = (0..ids.len() as u32).collect();
        let mut root = vec![0u32; ids.len()];
        for i in 0..ids.len() as u32 {
            let r = find(&mut parent, i);
            root[i as usize] = r;
            if any_long && key_cmp(ids[i as usize], ids[best[r as usize] as usize]).is_lt() {
                best[r as usize] = i;
            }
        }
        lap("roots");
        let mut per: Vec<Vec<(Key, Key)>> = buckets(NP);
        for i in 0..ids.len() {
            let name = ids[best[root[i] as usize] as usize];
            if name != ids[i] {
                per[bkt(ids[i])].push((ids[i], name));
            }
        }
        lap("per");
        per.into_par_iter()
            .map(|v| {
                let mut m: KMap<Key> = KMap::default();
                m.reserve(v.len());
                for (a, b) in v {
                    m.insert(a, b);
                }
                m
            })
            .collect()
    };
    lap("links");

    // ------------------------------------------------ events: parse into event-id buckets
    let ev_chunks = chunks_of(&ev_files, 8 << 20);
    let wlo = ws;
    let whi = we;
    let parsed: Vec<Vec<Vec<Ev>>> = ev_chunks
        .par_iter()
        .fold(
            || buckets::<Ev>(NB),
            |mut bk, c| {
                scan::<7, _>(c.data, |buf, r| {
                    let eid = fl(buf, r[0]);
                    if eid.is_empty() {
                        return;
                    }
                    let ek = pack(eid);
                    let ing = parse_ts(fl(buf, r[3])).unwrap_or(i64::MAX);
                    let (e0, e1) = hl(ek);
                    let mut e = Ev { e0, e1, ing, u0: 0, u1: 0, ts: 0, pc: 0 };
                    'v: {
                        let u = fl(buf, r[1]);
                        if u.is_empty() {
                            break 'v;
                        }
                        let ts = match parse_ts(fl(buf, r[2])) {
                            Some(t) if t >= wlo && t < whi => t,
                            _ => break 'v,
                        };
                        if ing != i64::MAX && ing - ts > DAY {
                            break 'v; // late
                        }
                        let p = fl(buf, r[5]);
                        if p.is_empty() {
                            break 'v;
                        }
                        let ty = fl(buf, r[4]);
                        match ty {
                            b"view" | b"cart" => {}
                            b"purchase" => {
                                let pr = fl(buf, r[6]);
                                if pr.is_empty() {
                                    break 'v;
                                }
                                let mut v: u64 = 0;
                                for &ch in pr {
                                    let d = ch.wrapping_sub(b'0');
                                    if d > 9 {
                                        break 'v;
                                    }
                                    v = v * 10 + d as u64;
                                    if v > 10_000_000 {
                                        break 'v;
                                    }
                                }
                                if v < 1 {
                                    break 'v;
                                }
                                let cat = *prod.get(&pack(p)).unwrap_or(&unknown);
                                e.pc = v as u32 | (cat << 24);
                            }
                            _ => break 'v,
                        }
                        e.ts = (ts - t_zero) as u32;
                        let (u0, u1) = hl(pack(u));
                        e.u0 = u0;
                        e.u1 = u1;
                    }
                    bk[ebkt(ek)].push(e);
                });
                bk
            },
        )
        .collect();
    lap("events parsed");

    // ------------------------------------------------ clicks: parse into user buckets
    let cl_chunks = chunks_of(&cl_files, 8 << 20);
    let clo = ws - WEEK;
    let cparsed: Vec<Vec<Vec<Cl>>> = cl_chunks
        .par_iter()
        .fold(
            || buckets::<Cl>(NP),
            |mut bk, c| {
                scan::<4, _>(c.data, |buf, r| {
                    let cid = fl(buf, r[0]);
                    if cid.is_empty() {
                        return;
                    }
                    let u = fl(buf, r[1]);
                    if u.is_empty() {
                        return;
                    }
                    let ts = match parse_ts(fl(buf, r[3])) {
                        Some(t) if t >= clo && t < whi => t,
                        _ => return,
                    };
                    let cp = match camp.get(&pack(fl(buf, r[2]))) {
                        Some(&c) => c,
                        None => return,
                    };
                    let uk = pack(u);
                    let (u0, u1) = hl(uk);
                    let (c0, c1) = hl(pack(cid));
                    bk[bkt(uk)].push(Cl { u0, u1, c0, c1, ts: (ts - t_zero) as u32, camp: cp });
                });
                bk
            },
        )
        .collect();
    lap("clicks parsed");

    // ------------------------------------------------ dedup events -> user buckets
    let deduped: Vec<Vec<Vec<Sv>>> = (0..NB)
        .into_par_iter()
        .fold(
            || (buckets::<Sv>(NP), Vec::<Ev>::new(), Vec::<u32>::new()),
            |(mut bk, mut sub, mut table), b| {
                let v = gather(&parsed, b, 0);
                let offs = partition(&v, NS, |e| esbkt(kk(e.e0, e.e1)), &mut sub);
                drop(v);
                for si in 0..NS {
                    let part = &sub[offs[si]..offs[si + 1]];
                    if part.is_empty() {
                        continue;
                    }
                    let size = (part.len() * 2).next_power_of_two();
                    let mask = size - 1;
                    table.clear();
                    table.resize(size, u32::MAX);
                    let mut kept: Vec<u32> = Vec::with_capacity(part.len());
                    for (i, e) in part.iter().enumerate() {
                        let mut h = mix(kk(e.e0, e.e1)) as usize & mask;
                        loop {
                            let t = table[h];
                            if t == u32::MAX {
                                table[h] = kept.len() as u32;
                                kept.push(i as u32);
                                break;
                            }
                            let k = &part[kept[t as usize] as usize];
                            if k.e0 == e.e0 && k.e1 == e.e1 {
                                if e.ing < k.ing {
                                    kept[t as usize] = i as u32;
                                }
                                break;
                            }
                            h = (h + 1) & mask;
                        }
                    }
                    for &i in &kept {
                        let e = part[i as usize];
                        if (e.u0 | e.u1) == 0 {
                            continue;
                        }
                        bk[bkt(kk(e.u0, e.u1))].push(Sv { u0: e.u0, u1: e.u1, ts: e.ts, pc: e.pc });
                    }
                }
                (bk, sub, table)
            },
        )
        .map(|(bk, _, _)| bk)
        .collect();
    drop(parsed);
    lap("events deduped");

    // ------------------------------------------------ map user ids to people
    // Within bucket b only IDs of bucket b occur, so the link table is small.
    // Linked IDs whose person lives in another bucket move there.
    struct Moved {
        ev: Vec<Vec<Sv>>,
        cl: Vec<Vec<Cl>>,
    }
    let (stays, moved): (Vec<(Vec<Sv>, Vec<Cl>)>, Vec<Moved>) = {
        let r: Vec<(Vec<(usize, Vec<Sv>, Vec<Cl>)>, Moved)> = (0..NP)
            .into_par_iter()
            .fold(
                || (Vec::new(), Moved { ev: buckets(NP), cl: buckets(NP) }),
                |(mut st, mut mv), b| {
                    let lt = &link_tables[b];
                    let mut ev = gather(&deduped, b, 0);
                    let mut cl = gather(&cparsed, b, 0);
                    if !lt.is_empty() {
                        let mut w = 0;
                        for i in 0..ev.len() {
                            let mut e = ev[i];
                            if let Some(&name) = lt.get(&kk(e.u0, e.u1)) {
                                let (a, c) = hl(name);
                                e.u0 = a;
                                e.u1 = c;
                                let nb = bkt(name);
                                if nb != b {
                                    mv.ev[nb].push(e);
                                    continue;
                                }
                            }
                            ev[w] = e;
                            w += 1;
                        }
                        ev.truncate(w);
                        let mut w = 0;
                        for i in 0..cl.len() {
                            let mut e = cl[i];
                            if let Some(&name) = lt.get(&kk(e.u0, e.u1)) {
                                let (a, c) = hl(name);
                                e.u0 = a;
                                e.u1 = c;
                                let nb = bkt(name);
                                if nb != b {
                                    mv.cl[nb].push(e);
                                    continue;
                                }
                            }
                            cl[w] = e;
                            w += 1;
                        }
                        cl.truncate(w);
                    }
                    st.push((b, ev, cl));
                    (st, mv)
                },
            )
            .collect();
        let mut stays: Vec<(Vec<Sv>, Vec<Cl>)> = (0..NP).map(|_| (vec![], vec![])).collect();
        let mut moved = vec![];
        for (st, mv) in r {
            for (b, ev, cl) in st {
                stays[b] = (ev, cl);
            }
            moved.push(mv);
        }
        (stays, moved)
    };
    drop(deduped);
    drop(cparsed);
    lap("mapped");

    // ------------------------------------------------ sessions per person bucket
    let width = ndays;
    let ncs = ncamp + 1;
    struct Acc {
        v: Vec<[i64; 4]>, // sessions, purchasing, revenue, assisted
    }
    let new_acc = || Acc { v: vec![[0; 4]; ncs * width] };
    let day_of = |rel: u32| -> i64 { (rel as i64 + t_zero).div_euclid(DAY) };
    let stays = Mutex::new(stays.into_iter().map(Some).collect::<Vec<_>>());
    let results: Vec<(Vec<URow>, Acc)> = (0..NP)
        .into_par_iter()
        .fold(
            || (Vec::<URow>::new(), new_acc()),
            |(mut rows, mut acc), b| {
                let (mut ev, mut cl) = stays.lock().unwrap()[b].take().unwrap();
                for m in &moved {
                    ev.extend_from_slice(&m.ev[b]);
                    cl.extend_from_slice(&m.cl[b]);
                }
                let mut evp = Vec::new();
                let eoff = partition(&ev, NS, |e| sbkt(kk(e.u0, e.u1)), &mut evp);
                drop(ev);
                let mut clp = Vec::new();
                let coff = partition(&cl, NS, |e| sbkt(kk(e.u0, e.u1)), &mut clp);
                drop(cl);
                let mut catsum = vec![0i64; ncat];
                let mut touched: Vec<u32> = vec![];
                let mut starts: Vec<u32> = vec![];
                let mut cbuf: Vec<(u32, u32)> = vec![];
                for si in 0..NS {
                let ev = &mut evp[eoff[si]..eoff[si + 1]];
                let cl = &mut clp[coff[si]..coff[si + 1]];
                ev.sort_unstable_by(|x, y| (x.u0, x.u1, x.ts).cmp(&(y.u0, y.u1, y.ts)));
                cl.sort_unstable_by(|x, y| {
                    (x.u0, x.u1, x.ts)
                        .cmp(&(y.u0, y.u1, y.ts))
                        .then_with(|| key_cmp(kk(y.c0, y.c1), kk(x.c0, x.c1)))
                });
                let ev = &*ev;
                let cl = &*cl;
                let mut ci = 0usize;
                let mut i = 0usize;
                while i < ev.len() {
                    let (p0, p1) = (ev[i].u0, ev[i].u1);
                    let mut j = i + 1;
                    while j < ev.len() && ev[j].u1 == p1 && ev[j].u0 == p0 {
                        j += 1;
                    }
                    while ci < cl.len() && (cl[ci].u0, cl[ci].u1) < (p0, p1) {
                        ci += 1;
                    }
                    let c0 = ci;
                    while ci < cl.len() && cl[ci].u0 == p0 && cl[ci].u1 == p1 {
                        ci += 1;
                    }
                    let pcl = &cl[c0..ci];
                    let evs = &ev[i..j];
                    i = j;
                    let person = kk(p0, p1);

                    starts.clear();
                    let mut cp = 0usize;
                    let mut k = 0;
                    let mut row: Option<URow> = None;
                    while k < evs.len() {
                        let s = evs[k].ts;
                        let day = day_of(s);
                        if let Some(r) = &row {
                            if r.day as i64 != day {
                                let mut r = row.take().unwrap();
                                r.top = pick_top(&mut catsum, &mut touched, &cat_rank);
                                rows.push(r);
                            }
                        }
                        let r = row.get_or_insert(URow { name: person, day: day as i32, sessions: 0, events: 0, revenue: 0, top: u16::MAX });
                        let mut prev = s;
                        let mut nev = 0u32;
                        let mut rev = 0i64;
                        let mut has_p = false;
                        while k < evs.len() && evs[k].ts - prev <= GAP as u32 {
                            let e = evs[k];
                            prev = e.ts;
                            nev += 1;
                            if e.pc != 0 {
                                has_p = true;
                                let price = (e.pc & 0xFF_FFFF) as i64;
                                let cat = (e.pc >> 24) as usize;
                                rev += price;
                                if catsum[cat] == 0 {
                                    touched.push(cat as u32);
                                }
                                catsum[cat] += price;
                            }
                            k += 1;
                        }
                        r.sessions += 1;
                        r.events += nev;
                        r.revenue += rev;
                        starts.push(s);
                        while cp < pcl.len() && pcl[cp].ts <= s {
                            cp += 1;
                        }
                        let credited = if cp > 0 && (s - pcl[cp - 1].ts) as i64 <= WEEK { pcl[cp - 1].camp as usize } else { organic };
                        let slot = &mut acc.v[credited * width + (day - base_day) as usize];
                        slot[0] += 1;
                        slot[1] += has_p as i64;
                        slot[2] += rev;
                    }
                    if let Some(mut r) = row {
                        r.top = pick_top(&mut catsum, &mut touched, &cat_rank);
                        rows.push(r);
                    }

                    // assists: union of [click, click + 7d] per campaign
                    if !pcl.is_empty() {
                        cbuf.clear();
                        cbuf.extend(pcl.iter().map(|c| (c.camp, c.ts)));
                        cbuf.sort_unstable();
                        let mut q = 0;
                        while q < cbuf.len() {
                            let c = cbuf[q].0;
                            let a = cbuf[q].1;
                            let mut e = a as i64 + WEEK;
                            q += 1;
                            while q < cbuf.len() && cbuf[q].0 == c && cbuf[q].1 as i64 <= e {
                                e = e.max(cbuf[q].1 as i64 + WEEK);
                                q += 1;
                            }
                            let lo = starts.partition_point(|&x| x < a);
                            let hi = starts.partition_point(|&x| (x as i64) <= e);
                            if hi - lo <= 32 {
                                for &s in &starts[lo..hi] {
                                    acc.v[c as usize * width + (day_of(s) - base_day) as usize][3] += 1;
                                }
                            } else {
                                // count by day with binary searches on day boundaries
                                let mut at = lo;
                                while at < hi {
                                    let d = day_of(starts[at]);
                                    let next_day = ((d + 1) * DAY - t_zero).min(u32::MAX as i64) as u32;
                                    let end = at + starts[at..hi].partition_point(|&x| x < next_day);
                                    acc.v[c as usize * width + (d - base_day) as usize][3] += (end - at) as i64;
                                    at = end;
                                }
                            }
                        }
                    }
                }
                }
                (rows, acc)
            },
        )
        .collect();
    drop(moved);
    lap("sessions");

    let mut tot = vec![[0i64; 4]; ncs * width];
    let mut all_rows: Vec<Vec<URow>> = vec![];
    for (rows, a) in results {
        for x in 0..ncs * width {
            for y in 0..4 {
                tot[x][y] += a.v[x][y];
            }
        }
        all_rows.push(rows);
    }
    let sess: Vec<i64> = tot.iter().map(|x| x[0]).collect();
    let purch: Vec<i64> = tot.iter().map(|x| x[1]).collect();
    let rev: Vec<i64> = tot.iter().map(|x| x[2]).collect();
    let assist: Vec<i64> = tot.iter().map(|x| x[3]).collect();
    write_outputs(&out, all_rows, &sess, &purch, &rev, &assist, &camp_ids, &camp_ch, &cat_names, base_day, width);
    lap("written");
}

fn pick_top(catsum: &mut [i64], touched: &mut Vec<u32>, cat_rank: &[usize]) -> u16 {
    let mut best: Option<u32> = None;
    for &c in touched.iter() {
        match best {
            None => best = Some(c),
            Some(b) => {
                let (sc, sb) = (catsum[c as usize], catsum[b as usize]);
                if sc > sb || (sc == sb && cat_rank[c as usize] < cat_rank[b as usize]) {
                    best = Some(c);
                }
            }
        }
    }
    for &c in touched.iter() {
        catsum[c as usize] = 0;
    }
    touched.clear();
    best.map(|b| b as u16).unwrap_or(u16::MAX)
}

// ---------------------------------------------------------------- output
use arrow_array::{ArrayRef, Date32Array, Int64Array, RecordBatch, StringArray};
use arrow_schema::{DataType, Field, Schema};
use parquet::arrow::ArrowWriter;
use parquet::file::properties::WriterProperties;

fn props() -> WriterProperties {
    WriterProperties::builder()
        .set_dictionary_enabled(false)
        .set_statistics_enabled(parquet::file::properties::EnabledStatistics::None)
        .build()
}

fn write_batch(path: &Path, batch: RecordBatch) {
    let f = File::create(path).unwrap();
    let mut w = ArrowWriter::try_new(f, batch.schema(), Some(props())).unwrap();
    w.write(&batch).unwrap();
    w.close().unwrap();
}

#[allow(clippy::too_many_arguments)]
fn write_outputs(
    out: &Path,
    rows: Vec<Vec<URow>>,
    sess: &[i64],
    purch: &[i64],
    rev: &[i64],
    assist: &[i64],
    camp_ids: &[Vec<u8>],
    camp_ch: &[Vec<u8>],
    cat_names: &[Vec<u8>],
    base_day: i64,
    width: usize,
) {
    let ud = out.join("user_daily");
    let cd = out.join("campaign_daily");
    std::fs::create_dir_all(&ud).unwrap();
    std::fs::create_dir_all(&cd).unwrap();
    let uschema = Arc::new(Schema::new(vec![
        Field::new("user_id", DataType::Utf8, false),
        Field::new("day", DataType::Date32, false),
        Field::new("sessions", DataType::Int64, false),
        Field::new("events", DataType::Int64, false),
        Field::new("revenue_cents", DataType::Int64, false),
        Field::new("top_category", DataType::Utf8, true),
    ]));
    let cat_str: Vec<String> = cat_names.iter().map(|c| String::from_utf8_lossy(c).into_owned()).collect();
    let nonempty: Vec<(usize, Vec<URow>)> = rows.into_iter().enumerate().collect();
    nonempty.into_par_iter().for_each(|(i, r)| {
        let names: Vec<String> = r.iter().map(|x| bytes_to_string(unpack(x.name))).collect();
        let cols: Vec<ArrayRef> = vec![
            Arc::new(StringArray::from(names)),
            Arc::new(Date32Array::from(r.iter().map(|x| x.day).collect::<Vec<_>>())),
            Arc::new(Int64Array::from(r.iter().map(|x| x.sessions as i64).collect::<Vec<_>>())),
            Arc::new(Int64Array::from(r.iter().map(|x| x.events as i64).collect::<Vec<_>>())),
            Arc::new(Int64Array::from(r.iter().map(|x| x.revenue).collect::<Vec<_>>())),
            Arc::new(StringArray::from(
                r.iter()
                    .map(|x| if x.top == u16::MAX { None } else { Some(cat_str[x.top as usize].as_str()) })
                    .collect::<Vec<_>>(),
            )),
        ];
        let batch = RecordBatch::try_new(uschema.clone(), cols).unwrap();
        write_batch(&ud.join(format!("part-{i:04}.parquet")), batch);
    });

    let mut cid = vec![];
    let mut ch = vec![];
    let mut day = vec![];
    let (mut s, mut p, mut rv, mut a) = (vec![], vec![], vec![], vec![]);
    for c in 0..=camp_ids.len() {
        for d in 0..width {
            let x = c * width + d;
            if sess[x] == 0 && assist[x] == 0 {
                continue;
            }
            if c == camp_ids.len() {
                cid.push("organic".to_string());
                ch.push("organic".to_string());
            } else {
                cid.push(bytes_to_string(camp_ids[c].clone()));
                ch.push(bytes_to_string(camp_ch[c].clone()));
            }
            day.push((base_day + d as i64) as i32);
            s.push(sess[x]);
            p.push(purch[x]);
            rv.push(rev[x]);
            a.push(assist[x]);
        }
    }
    let cschema = Arc::new(Schema::new(vec![
        Field::new("campaign_id", DataType::Utf8, false),
        Field::new("channel", DataType::Utf8, false),
        Field::new("day", DataType::Date32, false),
        Field::new("sessions", DataType::Int64, false),
        Field::new("purchasing_sessions", DataType::Int64, false),
        Field::new("revenue_cents", DataType::Int64, false),
        Field::new("assisted_sessions", DataType::Int64, false),
    ]));
    let cols: Vec<ArrayRef> = vec![
        Arc::new(StringArray::from(cid)),
        Arc::new(StringArray::from(ch)),
        Arc::new(Date32Array::from(day)),
        Arc::new(Int64Array::from(s)),
        Arc::new(Int64Array::from(p)),
        Arc::new(Int64Array::from(rv)),
        Arc::new(Int64Array::from(a)),
    ];
    write_batch(&cd.join("part-0000.parquet"), RecordBatch::try_new(cschema, cols).unwrap());
}

fn bytes_to_string(b: Vec<u8>) -> String {
    match String::from_utf8(b) {
        Ok(s) => s,
        Err(e) => {
            // Inputs are UTF-8 per the rules; keep the bytes as lossless as possible.
            String::from_utf8_lossy(e.as_bytes()).into_owned()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn reference(s: &[u8]) -> Key {
        let mut buf = [0u8; 16];
        buf[..s.len()].copy_from_slice(s);
        buf[15] = s.len() as u8;
        u128::from_be_bytes(buf)
    }
    #[test]
    fn pack_matches() {
        let mut x: u64 = 88172645463325252;
        for _ in 0..200000 {
            x ^= x << 13; x ^= x >> 7; x ^= x << 17;
            let n = (x % 16) as usize;
            let s: Vec<u8> = (0..n).map(|i| (x >> (i * 4)) as u8 ^ (i as u8 * 37)).collect();
            assert_eq!(pack(&s), reference(&s), "{:?}", s);
        }
    }
    #[test]
    fn ts() {
        assert_eq!(parse_ts(b"2026-10-03T19:58:10-04:00"), parse_ts(b"2026-10-03T23:58:10Z"));
        assert_eq!(parse_ts(b"2026-10-03T23:58:10Z"), Some(1791071890000));
        assert_eq!(parse_ts(b"0001791071890000"), Some(1791071890000));
        assert_eq!(parse_ts(b"2028-02-29T00:00:00Z").is_some(), true);
        assert_eq!(parse_ts(b"2027-02-29T00:00:00Z"), None);
        assert_eq!(parse_ts(b"2026-10-03T23:58:10+0200"), None);
    }
}
