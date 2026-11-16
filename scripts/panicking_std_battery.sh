#!/usr/bin/env bash
# THE PANICKING-STD BATTERY — the falsification gate for any change to the
# absent-callee tolerance (the highest-frequency blocker in ordinary Rust).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# Every program here can panic at runtime on some input. The battery records
# what the compiler does TODAY so that a widening of the tolerance which starts
# admitting one of them is visible immediately. See the README for why `p07`
# compiles and why that is not a false proof.
set -uo pipefail
TC="${1:-$(cd "$(dirname "$0")/.." && pwd)/build/host/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC (build it, or pass a path)"; exit 2; }
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
echo "compiler: $("$TC" --version 2>&1 | head -1)"
# p07 is the one documented conditional pass; everything else must be refused.
ok=0; bad=0
for f in "$ROOT"/tests/panicking-std-battery/*.rs; do
  n="$(basename "$f" .rs)"
  if [ "$n" = "p07" ]; then expect=pass; else expect=fail; fi
  "$TC" --crate-type=lib --edition 2021 --out-dir "$WORK" "$f" > "$WORK/$n.log" 2>&1
  # Capture the COMPILER's status immediately: `$?` after any intervening test
  # reads that test instead, which is how the first cut of this script reported
  # 14 divergences that were not there.
  rc=$?
  got=pass; [ "$rc" -eq 0 ] || got=fail
  if [ "$n" = "p07" ] && [ "$got" = pass ]; then
    # A conditional pass is only honest while the row stays runtime-checked.
    if ! grep -q 'runtime-checked' "$WORK/$n.log"; then
      bad=$((bad+1)); printf '  WRONG %-5s compiled WITHOUT a runtime-checked row — that is a false proof\n' "$n"; continue
    fi
  fi
  if [ "$got" = "$expect" ]; then ok=$((ok+1)); else
    bad=$((bad+1)); printf '  WRONG %-5s expected %s, got %s\n' "$n" "$expect" "$got"
  fi
done
echo
echo "panicking-std battery: $ok as recorded, $bad diverged"
[ "$bad" -eq 0 ] || exit 1
true
