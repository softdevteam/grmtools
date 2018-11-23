#!/bin/bash

# build books for each tag
for tag in $(git tag)
do
    echo "Building book for $tag"
    git checkout $tag
    mdbook build -d release/$tag/book/
done

# build book/apidoc for master
git checkout master
echo "Building book for master"
mdbook build -d release/master/book
echo "Building docs for master"
RUSTDOCFLAGS="-Z unstable-options --enable-index-page" cargo +nightly doc --no-deps
mv ../target/doc release/master/api
