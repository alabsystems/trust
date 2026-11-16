#!/usr/bin/env bash
# THE ORDINARY-RUST SWEEP — forty programs nobody aimed at a known boundary.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# Unlike `daily_driver_probes.sh`, this pins NO per-file expectation. A curated
# probe set measures the boundaries you already know about; this one exists to
# surface the ones you do not. Read the count, then read the classification.
#
# Usage:  scripts/ordinary_rust_sweep.sh [path-to-trustc]
set -uo pipefail
TC="${1:-$(cd "$(dirname "$0")/.." && pwd)/build/host/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC (build it, or pass a path)"; exit 2; }
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
echo "compiler: $("$TC" --version 2>&1 | head -1)"
pass=0; fail=0
for f in "$ROOT"/tests/ordinary-rust-sweep/*.rs; do
  n="$(basename "$f" .rs)"
  "$TC" --crate-type=lib --edition 2021 --out-dir "$WORK" "$f" > "$WORK/$n.log" 2>&1
  if [ $? -eq 0 ]; then
    pass=$((pass+1))
  else
    fail=$((fail+1))
    why="$(grep -oE '\[[a-z_:-]+\] (FAILED|UNKNOWN|runtime-checked)[^;]{0,44}|lowering did not complete|uses GEP[^,]{0,24}' "$WORK/$n.log" | head -1)"
    printf '  fail  %-6s %s\n' "$n" "${why:-<no classified reason>}"
  fi
done
echo
echo "ordinary-rust sweep: $pass / $((pass+fail)) verify"
echo "a FAILED on a program you believe is correct is a false refutation; an"
echo "UNKNOWN is the honest fail-closed outcome and a different (smaller) problem."
true
