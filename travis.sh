#!/bin/bash -x

cargo build &&
    cargo test --features regex &&
    cargo test --features regex --examples &&
    cargo check --bench json &&
    cargo check --bench http &&
    cargo check --bench mp4 --features mp4 &&
    cargo build --no-default-features &&
    cargo test --no-default-features --examples
