#!/usr/bin/env bash
# regenerate.sh: Re-dump the container-corpus fixtures.
#
# Compiles SOURCE.rs with `trustc -Ztrust-dump=mir-only:<dir>`, emitting the exact
# `trust_types::VerifiableFunction` JSON `prove_dump_dir` consumes — mirrors
# `fixtures/call-spine-corpus/regenerate.sh` byte-for-byte (same TMP-dir
# convention, so the dumped spans carry the stable relative `SOURCE.rs` name,
# not a path tied to this fixture directory). `Stack` is a realistic bounded
# container (fixed-capacity `buf: [u64; 32]` + `len`/`cap` fields); the 8
# methods span the corpus's per-method shape split — see PROVENANCE.md.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Resolve trustc from the stage2 sysroot (fall back to PATH).
TRUSTC="${TRUSTC:-}"
if [[ -z "$TRUSTC" ]]; then
  for cand in \
    "$HERE/../../../../build/host/stage2/bin/trustc" \
    "$(command -v trustc || true)"; do
    if [[ -n "$cand" && -x "$cand" ]]; then TRUSTC="$cand"; break; fi
  done
fi
if [[ -z "$TRUSTC" ]]; then
  echo "error: trustc not found (set TRUSTC=/path/to/trustc)" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# Compile from inside $TMP with the file named SOURCE.rs so the dumped spans
# carry the stable relative name (matching the sibling corpora).
cp "$HERE/SOURCE.rs" "$TMP/SOURCE.rs"

# `--crate-type lib` so every `pub fn` is reachable and gets a MIR dump. The
# legacy exec-projection flag is intentionally absent: these methods have no
# clauses, and Trust test enforcement is now the certified-monitor lane.
(cd "$TMP" && \
  LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
    "$TRUSTC" -Ztrust-policy=advisory "-Ztrust-dump=mir-only:$TMP" \
      --edition 2021 --crate-type lib SOURCE.rs \
      --out-dir "$TMP")

for f in Stack__len Stack__capacity Stack__is_empty Stack__is_full \
         Stack__remaining Stack__has_len Stack__at_least Stack__double_len; do
  if [[ -f "$TMP/$f.json" ]]; then
    cp "$TMP/$f.json" "$HERE/$f.json"
    echo "regenerated $f.json"
  else
    echo "error: expected dump $f.json was not produced" >&2
    exit 1
  fi
done
