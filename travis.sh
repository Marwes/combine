#!/bin/bash -x
set -ex

echo "TRAVIS_RUST_VERSION=$TRAVIS_RUST_VERSION"
if [ "$TRAVIS_RUST_VERSION" == "1.20.0" ]; then
    cargo generate-lockfile
    cargo update -p tokio-io --precise 0.1.7
    cargo update -p lazy_static --precise 1.1.0

    cargo build --no-default-features
else
    cargo build
    cargo test --features doc
    cargo test --features doc --examples

    cargo check --bench json
    cargo check --bench http
    cargo check --bench mp4 --features mp4

    cargo build --no-default-features
    cargo test --no-default-features --examples
fi
