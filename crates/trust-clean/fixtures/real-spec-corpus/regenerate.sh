#!/usr/bin/env bash
# regenerate.sh: Re-dump `count_to.json` from the checked-in, byte-verified
# reconstruction `count_to.rs` (see PROVENANCE.md).
#
# SCOPE (honest): this script regenerates ONLY count_to.json. The other
# fixtures in this corpus were dumped from per-function scratch files
# (count_up.rs, NEWSHAPES.rs, ...) that were never checked in; their source
# text lives in the consolidated SOURCE.rs, which does NOT byte-reproduce
# their span metadata. count_to.rs is the one fixture with a verified
# byte-identical regeneration path (2026-07-07).
#
# NOTE: the retired legacy exec projection is absent; live upstream contract-
# checker scaffolding changes the dumped MIR (see PROVENANCE.md).
#
# Requires: a built stage2 `trustc` (see the repo root CLAUDE.md).
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

# The fixture's span.file is the RELATIVE path "count_to.rs", so compile with
# the file's directory as cwd and pass the bare filename.
cp "$HERE/count_to.rs" "$TMP/count_to.rs"
(cd "$TMP" && \
  LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
    "$TRUSTC" --crate-type lib -Z"trust-dump=mir:$TMP" \
      -Ztrust-policy=advisory \
      count_to.rs -o "$TMP/count_to.rlib") || true

if [[ -f "$TMP/count_to.json" ]]; then
  if cmp -s "$TMP/count_to.json" "$HERE/count_to.json"; then
    echo "count_to.json: re-dump is BYTE-IDENTICAL to the checked-in fixture"
  else
    echo "warning: re-dump DIFFERS from the checked-in fixture (toolchain drift?)" >&2
    echo "         new dump left at $TMP/count_to.json is NOT copied in; inspect first" >&2
    cp "$TMP/count_to.json" "$HERE/count_to.json.redump"
    exit 1
  fi
else
  echo "error: expected dump count_to.json was not produced" >&2
  exit 1
fi
