# Shopping Sessions: a single Rust binary.
# Stage 1 compiles; stage 2 is a small runtime image with only the binary.
FROM rust:1-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY .cargo .cargo
COPY src src
RUN cargo build --release --locked

FROM debian:bookworm-slim
# The scorer runs the container as uid 1000.
RUN useradd --uid 1000 --no-create-home --home-dir /scratch app
COPY --from=build /src/target/release/sess /app/sess
WORKDIR /app
CMD ["/app/sess"]
