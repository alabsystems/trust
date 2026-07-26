#!/usr/bin/env bash
# Trust dual-oracle classifier — single-witness false-proof triage.
#
# Complements scripts/trust_falseproof_search.py (which sweeps a fixed FAMILY of
# witnesses): this classifies ONE ad-hoc witness during an investigation/hunt. Give
# it a lib defining `pub fn f(...)` and a `fn main(){...}` driver that calls f with
# black_box'd ADVERSARIAL inputs (the worst case that triggers the panic). It runs
# both oracles and prints one line:
#
#   FALSE_PROOF    static fully-proved AND runtime panics   <-- SOUNDNESS BUG (the target)
#   SOUND_PROOF    static fully-proved AND runtime safe     <-- superiority win
#   CORRECT_REJECT static NOT proved   AND runtime panics   <-- sound + useful
#   COMPLETENESS   static NOT proved   AND runtime safe     <-- a proving frontier
#   INCONCLUSIVE   driver compile error / function emits no obligations (unmodeled)
#
# "Fully proved" = headline "N proved, …" with N>0 and 0 failed/unknown/timed-out/
# runtime-checked. The runtime oracle builds the lib+driver with overflow-checks and
# debug-assertions on, so integer overflow / OOB / capacity-overflow panic.
#
# Usage:  scripts/trust_dualoracle.sh <name> <lib.rs> <driver_main.rs>
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
# ay's host LLVM links z3; keep the local link/runtime shims on the path (mirrors the gates).
# The shims dir must EXIST: a missing LIBRARY_PATH entry makes ld warn
# "search path not found", which leaks into diagnostics-sensitive tests.
mkdir -p /tmp/trust_link_shims
export LIBRARY_PATH="/tmp/trust_link_shims:/opt/homebrew/opt/z3/lib:${LIBRARY_PATH:-}"

if [ "$#" -ne 3 ]; then
  echo "usage: $0 <name> <lib.rs> <driver_main.rs>" >&2
  exit 2
fi
if [ ! -x "$TRUSTC" ]; then
  echo "ERROR: trustc not found at $TRUSTC (build it: ./x.py build --stage 2 compiler/rustc)" >&2
  exit 2
fi
NAME="$1"; LIB="$2"; DRV="$3"
WD="$(mktemp -d)"; trap 'rm -rf "$WD"' EXIT

# --- static: explicit advisory-verifier headline ---
SUM="$("$TRUSTC" --edition 2021 --crate-type lib -Z trust-policy=advisory "$LIB" 2>&1 \
        | grep -m1 'Trust verification:' | sed 's/.*verification: //')"
PROVED=0
if [ -n "$SUM" ]; then
  P=$(echo "$SUM" | grep -oE '^[0-9]+ proved' | grep -oE '^[0-9]+')
  REST=$(echo "$SUM" | grep -oE '[0-9]+ (failed|unknown|timed out|runtime-checked)' \
          | grep -oE '^[0-9]+' | paste -sd+ - | bc 2>/dev/null)
  REST=${REST:-0}
  if [ "${P:-0}" -gt 0 ] && [ "$REST" -eq 0 ]; then PROVED=1; fi
fi

# --- runtime: overflow / debug-assertion / capacity-overflow oracle ---
cat "$LIB" > "$WD/m.rs"
cat "$DRV" >> "$WD/m.rs"
RT_PANIC=0; RT_OK=0
if "$TRUSTC" --edition 2021 -Z trust-verify=off \
      -C overflow-checks=on -C debug-assertions=on \
      --crate-type bin "$WD/m.rs" -o "$WD/m.bin" 2>"$WD/cerr"; then
  if "$WD/m.bin" >/dev/null 2>&1; then RT_OK=1; else RT_PANIC=1; fi
else
  printf 'INCONCLUSIVE  %s  (driver compile error)\n' "$NAME"; exit 0
fi

if [ -z "$SUM" ]; then
  printf 'INCONCLUSIVE  %s  (no static obligations / no summary — likely unmodeled)\n' "$NAME"; exit 0
fi
if [ "$PROVED" -eq 1 ] && [ "$RT_PANIC" -eq 1 ]; then
  printf 'FALSE_PROOF   %s  static="%s" runtime=PANIC\n' "$NAME" "$SUM"; exit 0
fi
if [ "$PROVED" -eq 1 ] && [ "$RT_OK" -eq 1 ]; then
  printf 'SOUND_PROOF   %s  static="%s"\n' "$NAME" "$SUM"; exit 0
fi
if [ "$PROVED" -eq 0 ] && [ "$RT_PANIC" -eq 1 ]; then
  printf 'CORRECT_REJECT %s  static="%s"\n' "$NAME" "$SUM"; exit 0
fi
printf 'COMPLETENESS  %s  static="%s"\n' "$NAME" "$SUM"
