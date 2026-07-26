#!/bin/sh
# Regenerate sgn.json from the REAL, published signum-sign 0.1.4 source.
# Provenance: PROVENANCE.md (crates.io tarball, sha256-pinned).
set -eu

REPO_ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"  # prebuilt stage2, do NOT rebuild
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

curl -sL "https://static.crates.io/crates/signum-sign/signum-sign-0.1.4.crate" -o "$WORK/signum-sign-0.1.4.crate"
echo "887a8345877c4c1454d35034fcaf040fdebfe86688362674739824e12077ac9f  $WORK/signum-sign-0.1.4.crate" | shasum -a 256 -c -
tar xzf "$WORK/signum-sign-0.1.4.crate" -C "$WORK"

DUMP="$WORK/dump"
mkdir -p "$DUMP"
LIBRARY_PATH=/opt/homebrew/lib \
  "$TRUSTC" --edition 2021 --crate-type lib \
  -Z"trust-dump=mir:$DUMP" -Ztrust-policy=advisory \
  -o "$WORK/out.rlib" "$WORK/signum-sign-0.1.4/src/lib.rs"

cp "$DUMP/sgn.json" "$(dirname "$0")/sgn.json"
echo "regenerated sgn.json"
