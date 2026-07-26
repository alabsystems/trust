#!/usr/bin/env bash
# Regenerate the structural-fold-corpus dumps from SOURCE.rs with the prebuilt
# stage2 trustc — the SAME recipe as census-m6-cleankernel-2026-07-08 (dump-only,
# survey mode, no verification dispatch).
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../../../.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"   # prebuilt stage2, do NOT rebuild
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

# Homebrew installations may need this to locate the stage2 LLVM libraries.
# Leave a caller-supplied value alone, and do not inject a macOS-only path on
# other hosts.
if [[ -d /opt/homebrew/lib && -z "${LIBRARY_PATH:-}" ]]; then
  export LIBRARY_PATH=/opt/homebrew/lib
fi

"$TRUSTC" --edition 2021 --crate-type lib \
    \
    -Ztrust-dump=mir-only:"$SCRATCH/dump" \
    -Ztrust-policy=advisory \
    -o "$SCRATCH/out.rlib" "$HERE/SOURCE.rs"

ls "$SCRATCH/dump"
cp "$SCRATCH/dump"/*.json "$HERE/"
echo "regenerated $(ls "$SCRATCH/dump" | wc -l | tr -d ' ') dumps into $HERE"
