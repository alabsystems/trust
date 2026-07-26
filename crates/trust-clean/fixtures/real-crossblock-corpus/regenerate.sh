#!/usr/bin/env bash
# regenerate.sh: Re-dump the real-crossblock-corpus fixtures from the
# checked-in, span-pinned reconstructions SOURCE.rs (count_ret) and
# NEG_SOURCE.rs (double_bump). See PROVENANCE.md.
#
# BYTE-IDENTITY QUIRK: the checked-in JSONs embed the dump directory in every
# span `file` string, normalized to the neutral placeholder `<dump-root>` at
# publication. This script compiles the sources under their original names
# (xblock_src.rs / xblock_neg.rs) in a scratch directory, then applies the
# same `<dump-root>` normalization to the fresh dump before comparing.
#
# Requires: a built stage2 `trustc` (see README.md).
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

# The fixtures' spans record the dump directory as `<dump-root>` (normalized
# at publication; see PROVENANCE.md). Compile from any scratch directory and
# normalize the fresh dump the same way before comparing.
SRC_DIR="$(mktemp -d)"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

cp "$HERE/SOURCE.rs" "$SRC_DIR/xblock_src.rs"
cp "$HERE/NEG_SOURCE.rs" "$SRC_DIR/xblock_neg.rs"

LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
  "$TRUSTC" --crate-type lib \
  -Z"trust-dump=mir:$TMP" -Ztrust-policy=advisory \
  "$SRC_DIR/xblock_src.rs" -o "$TMP/xb.rlib" || true
LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}" \
  "$TRUSTC" --crate-type lib \
  -Z"trust-dump=mir:$TMP" -Ztrust-policy=advisory \
  "$SRC_DIR/xblock_neg.rs" -o "$TMP/xbn.rlib" || true

status=0
for f in count_ret double_bump; do
  if [[ ! -f "$TMP/$f.json" ]]; then
    echo "error: expected dump $f.json was not produced" >&2
    exit 1
  fi
  # Normalize the span `file` directory to the placeholder used in the
  # checked-in fixtures, then compare byte-for-byte.
  sed -e "s|$SRC_DIR|<dump-root>|g" "$TMP/$f.json" > "$TMP/$f.normalized.json"
  mv "$TMP/$f.normalized.json" "$TMP/$f.json"
  if cmp -s "$TMP/$f.json" "$HERE/$f.json"; then
    echo "$f.json: re-dump is BYTE-IDENTICAL to the checked-in fixture"
  else
    echo "warning: $f.json re-dump DIFFERS from the checked-in fixture" >&2
    cp "$TMP/$f.json" "$HERE/$f.json.redump"
    echo "         new dump left at $HERE/$f.json.redump (NOT copied in); inspect first" >&2
    status=1
  fi
done
exit $status
