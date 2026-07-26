#!/usr/bin/env bash
# regenerate.sh: Re-dump the leaf-call-corpus fixtures from the REAL `arrayvec`
# 0.7.7 crate (see PROVENANCE.md — unlike the sibling corpora these are copied
# verbatim from an external, unmodified crate, not compiled from a checked-in
# SOURCE.rs).
#
# Requires: a built stage2 `trustc` (see the repo root CLAUDE.md) and the
# `arrayvec` 0.7.7 source in the local crates.io registry cache (populate it
# with `cargo add arrayvec@=0.7.7` in a scratch crate + `cargo fetch` if it is
# not already there).
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

ARRAYVEC_SRC="$(ls -d "${HOME}"/.cargo/registry/src/*/arrayvec-0.7.7/src/lib.rs 2>/dev/null | head -1 || true)"
if [[ -z "$ARRAYVEC_SRC" ]]; then
  echo "error: arrayvec-0.7.7 source not found under ~/.cargo/registry/src/**/arrayvec-0.7.7/" >&2
  echo "       populate it: (cd \$(mktemp -d) && cargo init --lib && cargo add arrayvec@=0.7.7 && cargo fetch)" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
  "$TRUSTC" -Ztrust-policy=advisory "-Ztrust-dump=mir-only:$TMP" \
    --edition 2021 --crate-type lib \
    -o "$TMP/out.rlib" "$ARRAYVEC_SRC"

declare -A MAP=(
  ["arrayvec__ArrayVec__<T, CAP>__len.json"]="arrayvec_len.json"
  ["<arrayvec__ArrayVec<T, CAP> as arrayvec_impl__ArrayVecImpl>__len.json"]="arrayvec_impl_len.json"
  ["arrayvec__ArrayVec__<T, CAP>__is_empty.json"]="arrayvec_is_empty.json"
)
for src in "${!MAP[@]}"; do
  dst="${MAP[$src]}"
  if [[ -f "$TMP/$src" ]]; then
    cp "$TMP/$src" "$HERE/$dst"
    echo "regenerated $dst (from $src)"
  else
    echo "error: expected dump '$src' was not produced" >&2
    exit 1
  fi
done
