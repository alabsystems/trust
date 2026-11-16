#!/usr/bin/env bash
# The open-dispatch ladder.
#
# Every row records the disposition it was MEASURED at, not one it was aimed at,
# and the ladder's whole point is the pairs: g2/h2 is one trait method at a
# concrete receiver versus through `&mut dyn Write`; r1/r2 is the discharge
# lattice versus a panicking impl of the same contract. A `verifies` row that
# goes red says the toolchain regressed; a `refuses` row that goes green is the
# more dangerous direction and must be read as a possible FALSE PROOF until the
# row it was refusing is shown to have been discharged on purpose.
#
# A third disposition, `conditional`, records a row that exits 0 under the
# default (strict) policy ONLY because an obligation was admitted as a disclosed
# assumption — OD-1's `assumption:instance-hypothesis` for an open generic call.
# It is stronger than `verifies`, not weaker: the row must exit 0, must carry its
# `trust-ladder-row` needle (default: the instance-hypothesis disclosure), AND a
# second build of the same unit under `-Ztrust-policy=certify` must exit non-zero
# with `Trust certify verification failed`. A conditional row whose hypothesis
# disappears, or that certify accepts, has turned a disclosed assumption into an
# undisclosed one and diverges.
#
# Usage: scripts/open_dispatch_ladder.sh [path-to-trustc]
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
DIR="$ROOT/tests/open-dispatch-ladder"
TC="${1:-$ROOT/build/aarch64-apple-darwin/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC" >&2; exit 2; }

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
pass=0; diverged=0

COND_NEEDLE='recorded as `assumption:instance-hypothesis` (skipped, NOT proved)'
CERT_NEEDLE='Trust certify verification failed'

check() { # name expected rc logfile rowneedle [certify-rc certify-logfile]
  local n="$1" exp="$2" rc="$3" log="$4" needle="${5:-}" crc="${6:-}" clog="${7:-}"
  local got; if [ "$rc" -eq 0 ]; then got=verifies; else got=refuses; fi
  if [ "$exp" = conditional ]; then
    if [ "$got" != verifies ]; then
      echo "DIVERGED $n: recorded=conditional measured=refuses (rc=$rc)"
      sed -n '/^error/{p;q;}' "$log" | cut -c1-140
      diverged=$((diverged+1)); return
    fi
    [ -n "$needle" ] || needle="$COND_NEEDLE"
    if [ -z "$crc" ] || [ "$crc" -eq 0 ] || ! grep -qF -- "$CERT_NEEDLE" "$clog"; then
      echo "DIVERGED $n: conditional as recorded, but certify did not refuse it (rc=${crc:-unrun})"
      diverged=$((diverged+1)); return
    fi
    got=conditional
  fi
  if [ "$got" != "$exp" ]; then
    echo "DIVERGED $n: recorded=$exp measured=$got (rc=$rc)"
    sed -n '/^error/{p;q;}' "$log" | cut -c1-140
    diverged=$((diverged+1)); return
  fi
  if [ -n "$needle" ] && ! grep -qF -- "$needle" "$log"; then
    echo "DIVERGED $n: $exp as recorded, but the decisive row is gone"
    echo "  expected to find: $needle"
    diverged=$((diverged+1)); return
  fi
  pass=$((pass+1))
}

for f in "$DIR"/*.rs; do
  n="$(basename "$f" .rs)"
  exp="$(sed -n 's|^//@ trust-ladder: *||p' "$f" | head -1)"
  [ -n "$exp" ] || continue
  needle="$(sed -n 's|^//@ trust-ladder-row: *||p' "$f" | head -1)"
  ct="$(sed -n 's|^//@ trust-ladder-crate-type: *||p' "$f" | head -1)"
  if [ "$ct" = bin ]; then ctflag=(); else ctflag=(--crate-type=lib); fi
  o="$WORK/$n"; mkdir -p "$o"
  TRUST_VANILLA_DEBUG=1 "$TC" --edition 2021 ${ctflag[@]+"${ctflag[@]}"} --out-dir "$o" "$f" > "$WORK/$n.log" 2>&1
  rc=$?; crc=""
  if [ "$exp" = conditional ]; then
    mkdir -p "$o.certify"
    "$TC" --edition 2021 ${ctflag[@]+"${ctflag[@]}"} -Ztrust-policy=certify --out-dir "$o.certify" "$f" \
      > "$WORK/$n.certify.log" 2>&1
    crc=$?
  fi
  check "$n" "$exp" "$rc" "$WORK/$n.log" "$needle" "$crc" "$WORK/$n.certify.log"
done

# The cross-crate rows. Each names the dependency crate it is built against
# (default `libt`, the Phi-carrying trait); the dependency must build cleanly on
# its own, because a rail that fails for the WRONG reason proves nothing.
#
# Every dependency is built with `-Zalways-encode-mir`, as `targo` builds every
# unit, plus its own `//@ trust-ladder-dep-flags:` (e.g. `-Ztrust-verify=off`
# for a dependency whose panicking body is the rail). A user row may DECLARE its
# dependency with `//@ trust-ladder-xcrate-declare: <crate>`, which passes
# `-Ztrust-bundle-foreign-crate=<crate>` (D4-A: the dependency's bodies are then
# RE-DERIVED in the user's compilation; nothing is imported).
for dep in "$DIR"/xcrate/lib*.rs; do
  dn="$(basename "$dep" .rs)"
  L="$WORK/$dn"; mkdir -p "$L"
  # Word-split on purpose: the header holds a flag list.
  # shellcheck disable=SC2206
  depflags=($(sed -n 's|^//@ trust-ladder-dep-flags: *||p' "$dep" | head -1))
  if ! "$TC" --edition 2021 --crate-type=lib -Zalways-encode-mir ${depflags[@]+"${depflags[@]}"} \
      --out-dir "$L" "$dep" > "$WORK/$dn.log" 2>&1; then
    echo "DIVERGED xcrate/$dn: the dependency crate itself failed to build"
    sed -n '/^error/{p;q;}' "$WORK/$dn.log" | cut -c1-140
    diverged=$((diverged+1))
  fi
done
for f in "$DIR"/xcrate/user_*.rs; do
  n="$(basename "$f" .rs)"
  exp="$(sed -n 's|^//@ trust-ladder-xcrate: *||p' "$f" | head -1)"
  [ -n "$exp" ] || continue
  dn="$(sed -n 's|^//@ trust-ladder-xcrate-dep: *||p' "$f" | head -1)"; dn="${dn:-libt}"
  L="$WORK/$dn"
  [ -f "$L/lib$dn.rlib" ] || { echo "DIVERGED xcrate/$n: dependency $dn absent"; diverged=$((diverged+1)); continue; }
  decl="$(sed -n 's|^//@ trust-ladder-xcrate-declare: *||p' "$f" | head -1)"
  if [ -n "$decl" ]; then declflag=("-Ztrust-bundle-foreign-crate=$decl"); else declflag=(); fi
  # A user row is a binary unless it says `lib` (D4 increment B: the foreign-trait
  # closure is whole-program only, and its library twin is a rail).
  xct="$(sed -n 's|^//@ trust-ladder-crate-type: *||p' "$f" | head -1)"
  if [ "$xct" = lib ]; then xctflag=(--crate-type=lib); else xctflag=(); fi
  needle="$(sed -n 's|^//@ trust-ladder-row: *||p' "$f" | head -1)"
  o="$WORK/xc-$n"; mkdir -p "$o"
  "$TC" --edition 2021 ${xctflag[@]+"${xctflag[@]}"} --extern "$dn=$L/lib$dn.rlib" -L "$L" \
    ${declflag[@]+"${declflag[@]}"} --out-dir "$o" "$f" > "$WORK/$n.log" 2>&1
  rc=$?; crc=""
  if [ "$exp" = conditional ]; then
    mkdir -p "$o.certify"
    "$TC" --edition 2021 ${xctflag[@]+"${xctflag[@]}"} --extern "$dn=$L/lib$dn.rlib" -L "$L" \
      ${declflag[@]+"${declflag[@]}"} -Ztrust-policy=certify --out-dir "$o.certify" "$f" \
      > "$WORK/$n.certify.log" 2>&1
    crc=$?
  fi
  check "xcrate/$n" "$exp" "$rc" "$WORK/$n.log" "$needle" "$crc" "$WORK/$n.certify.log"
done

echo "open-dispatch ladder: $pass as recorded, $diverged diverged"
[ "$diverged" -eq 0 ]
