#!/usr/bin/env bash
# regenerate.sh: Re-dump the call-spine-corpus fixtures.
#
# Compiles SOURCE.rs with `trustc -Ztrust-dump=mir-only:<dir>`, emitting the exact
# `trust_types::VerifiableFunction` JSON `prove_dump_dir` consumes. These are
# the call-spine increment's fixtures: the thin-dispatcher pair (helper/caller)
# plus the call-requires establishment trio (caller_establishes /
# caller_const_ok — positives; caller_violates — the epistemic-hole regression
# control) and the two original negative controls (caller_uncertified —
# uncertified callee; self_loop — self-recursion). See SOURCE.rs for the
# corpus rationale and the FLIPPED expectation on `caller`.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
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

# `--crate-type lib` so every `pub fn` is reachable and gets a MIR dump.
(cd "$TMP" && \
  LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
    "$TRUSTC" -Ztrust-policy=advisory "-Ztrust-dump=mir-only:$TMP" \
      --edition 2021 --crate-type lib SOURCE.rs --out-dir "$TMP")

for f in helper caller caller_establishes caller_const_ok caller_violates \
         wild_helper caller_uncertified self_loop; do
  if [[ -f "$TMP/$f.json" ]]; then
    cp "$TMP/$f.json" "$HERE/$f.json"
    echo "regenerated $f.json"
  else
    echo "error: expected dump $f.json was not produced" >&2
    exit 1
  fi
done
