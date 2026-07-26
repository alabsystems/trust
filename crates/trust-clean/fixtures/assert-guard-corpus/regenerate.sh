#!/usr/bin/env bash
# regenerate.sh: Re-dump the assert-guard-corpus fixtures from SOURCE.rs (the
# assert!()-guarded arithmetic positive controls) and NEG_SOURCE.rs (the negative
# controls: a genuine two-arm branch, a non-panic "guard" arm, and an unguarded
# overflow).
#
# Compiles both files with `trustc -Ztrust-dump=mir-only:<dir>`, emitting the exact
# `trust_types::VerifiableFunction` JSON `prove_dump_dir` consumes. See
# PROVENANCE.md for the corpus rationale.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

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

# --- positive controls: assert!()-guarded arithmetic --------------------------
cp "$HERE/SOURCE.rs" "$TMP/SOURCE.rs"
(cd "$TMP" && \
  LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
    "$TRUSTC" -Ztrust-policy=advisory "-Ztrust-dump=mir-only:$TMP" \
      --crate-type lib SOURCE.rs -o "$TMP/ag.rlib")

for f in checked_id bounded_double bounded_sum; do
  if [[ -f "$TMP/$f.json" ]]; then
    cp "$TMP/$f.json" "$HERE/$f.json"
    echo "regenerated $f.json"
  else
    echo "error: expected dump $f.json was not produced" >&2
    exit 1
  fi
done

# --- negative controls ---------------------------------------------------------
rm -f "$TMP"/*.json
cp "$HERE/NEG_SOURCE.rs" "$TMP/NEG_SOURCE.rs"
(cd "$TMP" && \
  LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
    "$TRUSTC" -Ztrust-policy=advisory "-Ztrust-dump=mir-only:$TMP" \
      --crate-type lib NEG_SOURCE.rs -o "$TMP/neg.rlib")

for f in either weird_guard unsafe_double non_panic_helper; do
  if [[ -f "$TMP/$f.json" ]]; then
    cp "$TMP/$f.json" "$HERE/$f.json"
    echo "regenerated $f.json"
  else
    echo "error: expected dump $f.json was not produced" >&2
    exit 1
  fi
done
