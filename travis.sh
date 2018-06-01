#!/bin/bash -x
set -ex

echo "TRAVIS_RUST_VERSION=$TRAVIS_RUST_VERSION"
if [ "$TRAVIS_RUST_VERSION" == "1.20.0" ]; then
    cargo test --lib
    cargo build --no-default-features
else
    cargo build
    cargo test --features doc
    cargo test --features doc --examples

    [ "$TRAVIS_RUST_VERSION" != "nightly" ] || cargo check --bench json

    cargo check --bench http
    cargo check --bench mp4 --features mp4

    cargo build --no-default-features
    cargo test --no-default-features --examples
fi
