#!/usr/bin/env bash
# Regenerate the level-fold-corpus dumps: build the census extract crate
# (census-m6-cleankernel-2026-07-08/extract-foldmemo — REAL, byte-for-byte
# clean-kernel `level/mod.rs`/`expr/*`/`name.rs` sources; see ITS provenance)
# with the prebuilt stage2 trustc in dump-only survey mode, then copy the
# Level-family rows this corpus pins.
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../../../.." && pwd)"
EXTRACT="$HERE/../census-m6-cleankernel-2026-07-08/extract-foldmemo"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"   # prebuilt stage2, do NOT rebuild
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

# Homebrew installations may need this to locate the stage2 LLVM libraries.
# Leave a caller-supplied value alone, and do not inject a macOS-only path on
# other hosts.
if [[ -d /opt/homebrew/lib && -z "${LIBRARY_PATH:-}" ]]; then
  export LIBRARY_PATH=/opt/homebrew/lib
fi

cp -R "$EXTRACT" "$SCRATCH/extract"
(cd "$SCRATCH/extract" && \
  CARGO_TARGET_DIR="$SCRATCH/target" \
  RUSTC="$TRUSTC" \
  RUSTFLAGS="-Ztrust-verify=off" \
  cargo rustc --offline --lib -- \
    -Ztrust-verify=on \
    \
    -Ztrust-dump=mir-only:"$SCRATCH/dump" \
    -Ztrust-policy=advisory)

for f in \
  'level__Level__is_zero' \
  'level__Level__is_nonzero' \
  'level__Level__has_params' \
  'level__Level__has_params__{closure#0}' \
  'level__Level__has_params_impl' \
  'level__Level__has_params_impl__{closure#0}' \
  'level__Level__has_params_impl__{closure#1}' \
  'level__Level__has_params_impl__{closure#2}' \
  'expr__stack_safe' \
  'level__Level__substitute_map' \
  'level__Level__substitute_map_impl' \
  'level__Level__substitute_map_impl_opt' \
  'level__Level__substitute_slice_impl_opt' \
  'level__Level__collect_params_impl' \
; do
  cp "$SCRATCH/dump/$f.json" "$HERE/"
done
echo "regenerated $(ls "$HERE"/*.json | wc -l | tr -d ' ') level-fold-corpus dumps"
