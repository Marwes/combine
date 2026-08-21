#!/bin/bash

VERSION=$1

git cliff --unreleased --tag $VERSION --prepend CHANGELOG.md && \
    git add CHANGELOG.md && \
    git commit -m "Updated changelog" && \
    cargo release --execute $VERSION
