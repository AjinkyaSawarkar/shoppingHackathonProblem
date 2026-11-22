# Shopping Sessions: Rust pipeline

One Rust binary that implements `rules.md` exactly. It passes all 36 fixtures and matches the published 1M-event dev answer (scorer v5) row for row.

## How it works

1. **Read the small files.** `manifest.json`, `products.csv` and `campaigns.csv`.
2. **Links.** Parse `links/`, give every ID a number by sorting, join IDs with union-find, and name each person by the smallest ID. The result is split into 64 small lookup tables by a hash of the ID.
3. **Events.** All event files are memory-mapped and cut into 8 MB pieces at line ends. Each thread finds commas, quotes and line ends 64 bytes at a time with AVX2, checks the CSV rules with bit tests, parses the timestamps, validates the row and sends it to one of 64 groups by a hash of `event_id`.
4. **Clicks.** The same, grouped by a hash of `user_id`.
5. **Dedup.** Each `event_id` group is split again into 64 small pieces, and a small hash table keeps the copy with the smallest `ingest_ts`. Kept, valid events are grouped by a hash of `user_id`.
6. **People.** Each user group only needs its own small link table, so the lookup stays in the CPU cache. Linked IDs whose person belongs to another group move there.
7. **Sessions.** Each person group is split into 64 pieces, sorted by person and time, and cut into sessions. Each session is credited to the latest click within 7 days. Assists are counted from the union of `[click, click + 7 days]` intervals per campaign.
8. **Output.** Parquet files, one per worker for `user_daily` and one for `campaign_daily`.

Every ID of up to 15 bytes is packed exactly into a 128-bit number, so matching and byte-wise ordering are exact and cheap. Longer IDs (scorer v5 gives one in eight IDs a 32-character hex suffix) become a 120-bit hash, computed with no shared state. Their original bytes are recorded per thread only where the text matters: person names, click_id tie-breaks and the output.

## Run and test

```sh
cargo build --release
make local-fixtures                    # all 36 fixtures, no Docker
DATA_DIR=dev OUTPUT_DIR=out VERBOSE=1 target/release/sess
python3 scripts/compare.py out dev-answer

make fixtures                          # the same through Docker, with the scorer's flags
make run-dev check-dev
```

`VERBOSE=1` prints the time of each stage to stderr.
