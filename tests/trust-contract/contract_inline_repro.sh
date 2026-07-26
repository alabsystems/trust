#!/bin/sh
# Caller contracts must survive MIR inlining.
#
# A1 — `requires` is a CALLER-side obligation derived from `Call` terminators in
#      FINAL optimized MIR (trust_verify.rs:13033 `body_has_call_terminator`,
#      :13051 early-out). MIR inlining runs much earlier (lib.rs:790 ForceInline,
#      :793 Inline) than TrustVerify (lib.rs:858), so an inlined call's
#      precondition is never obligated and a violating caller compiles clean.
#
# A2 — with proof-directed check-elision layered on top, the same loss becomes
#      WRONG CODE: the inliner fetches callees via try_instance_mir ->
#      tcx.instance_mir (inline.rs:635,:1389), which for a local def IS
#      optimized_mir, i.e. the body TrustVerify already elided. The check and the
#      obligation that licensed removing it both disappear, and the program
#      silently wraps where vanilla Rust must panic.
#
# "TrustVerify is the last pass" is a PER-BODY property. It does not survive
# interprocedural inlining.
#
# Controls pinned here, which together isolate inlining as the cause:
#   -O0 · -Zinline-mir=no · #[inline(never)] · cross-crate
#
# Full analysis: reports/audit-2026-07-25-contract-loss-under-inlining.md
set -eu

REPO=$(cd "$(dirname "$0")/../.." && pwd)
TRUSTC=${TRUSTC:-$REPO/build/host/stage2/bin/trustc}
[ -x "$TRUSTC" ] || { echo "SKIP: no stage2 trustc at $TRUSTC (run ./x.py build --stage 2)"; exit 0; }

W=$(mktemp -d); trap 'rm -rf "$W"' EXIT; cd "$W"
fail=0
note() { printf '  %-52s %s\n' "$1" "$2"; }

# Returns the trustc exit code for a source file under the given extra flags.
run() {
  src=$1; shift
  TRUST_SEED_STAIRCASE=1 "$TRUSTC" -Zthreads=1 -Ztrust-verify=on \
    -Coverflow-checks=on --emit=metadata --out-dir "$W/o$$" "$@" "$src" \
    >/dev/null 2>"$W/err.txt" || return $?
  return 0
}

# A non-zero exit is NOT sufficient: a renamed flag, a missing file or an ICE all
# exit non-zero and would silently turn this battery green while the defect it
# exists to catch is wide open. Require a real VERIFICATION rejection.
expect_reject() {
  desc=$1; src=$2; shift 2
  if run "$src" "$@"; then
    note "$desc" "FAIL (accepted a contract violation)"; fail=1
    return
  fi
  if grep -qE "unknown unstable option|Unrecognized option|error: couldn't read" "$W/err.txt"; then
    note "$desc" "FAIL (harness broken: $(grep -oE 'unknown unstable option: .[a-z-]*.' "$W/err.txt" | head -1))"
    fail=1
    return
  fi
  if grep -qE "Trust (strict )?(verification|Level 0)" "$W/err.txt"; then
    note "$desc" "ok (rejected by the verifier)"
  else
    note "$desc" "FAIL (non-zero exit, but not a verification rejection)"; fail=1
  fi
}

# ---------------------------------------------------------------- A1
cat > a1.rs <<'EOF'
#![crate_type="lib"]
#[inline] pub fn identity(x: u32) -> u32 requires x < 1000 { x }
pub fn bad() -> u32 { identity(u32::MAX) }
EOF
cat > a1_never.rs <<'EOF'
#![crate_type="lib"]
#[inline(never)] pub fn identity(x: u32) -> u32 requires x < 1000 { x }
pub fn bad() -> u32 { identity(u32::MAX) }
EOF

echo "A1 — requires must be enforced at every optimization level:"
expect_reject "-Copt-level=0"                      a1.rs -Copt-level=0
expect_reject "-Copt-level=1"                      a1.rs -Copt-level=1
expect_reject "-Copt-level=3"                      a1.rs -Copt-level=3
expect_reject "-Copt-level=3 -Zinline-mir=no  [ctl]" a1.rs -Copt-level=3 -Zinline-mir=no
expect_reject "-Copt-level=3 #[inline(never)] [ctl]" a1_never.rs -Copt-level=3

# `ensures` is a CALLEE-side obligation and must stay enforced (it always was).
cat > a1_ens.rs <<'EOF'
#![crate_type="lib"]
#[inline] pub fn wrong(x: u32) -> u32 ensures result > x { x }
pub fn use_it() -> u32 { wrong(5) }
EOF
expect_reject "ensures at -Copt-level=3       [ctl]" a1_ens.rs -Copt-level=3

# ---------------------------------------------------------------- A2
echo "A2 — elision must not outlive the obligation that licensed it:"
cat > a2.rs <<'EOF'
#![crate_type="staticlib"]
pub fn inc(x: u32) -> u32 requires x < 1000 { x + 1 }
#[no_mangle] pub extern "C" fn bad() -> u32 { inc(u32::MAX) }
EOF
expect_reject "-Copt-level=3 (overflow + elision)" a2.rs -Copt-level=3

# If it was accepted, prove it is wrong code rather than merely undiagnosed.
if TRUST_SEED_STAIRCASE=1 "$TRUSTC" -Zthreads=1 -Ztrust-verify=on \
     -Coverflow-checks=on -Copt-level=3 --emit=link --out-dir lk a2.rs >/dev/null 2>&1; then
  cat > drv.c <<'EOF'
#include <stdio.h>
unsigned int bad(void);
int main(void){ printf("%u\n", bad()); return 0; }
EOF
  if cc -O2 drv.c lk/liba2.a -o prog 2>/dev/null; then
    got=$(./prog 2>/dev/null || echo panic)
    if [ "$got" = "panic" ]; then note "linked binary behaviour" "ok (panicked)"
    else note "linked binary behaviour" "FAIL (returned $got; vanilla must panic)"; fail=1; fi
  fi
fi

# ---------------------------------------------------------------- cross-crate
echo "Cross-crate — an #[inline] contract must bind downstream callers:"
mkdir -p xc && cd xc
cat > lib.rs <<'EOF'
#![crate_type="lib"]
#![crate_name="ctrlib"]
#[inline] pub fn inc(x: u32) -> u32 requires x < 1000 { x + 1 }
EOF
cat > user.rs <<'EOF'
#![crate_type="lib"]
extern crate ctrlib;
pub fn bad() -> u32 { ctrlib::inc(u32::MAX) }
EOF
TRUST_SEED_STAIRCASE=1 "$TRUSTC" -Zthreads=1 -Ztrust-verify=on -Coverflow-checks=on \
  -Copt-level=3 --emit=link --out-dir . lib.rs >/dev/null 2>&1 || true
if TRUST_SEED_STAIRCASE=1 "$TRUSTC" -Zthreads=1 -Ztrust-verify=on -Coverflow-checks=on \
     -Copt-level=3 --extern ctrlib=libctrlib.rlib -L . --emit=metadata --out-dir . user.rs \
     >/dev/null 2>&1; then
  note "downstream violating caller" "FAIL (accepted)"; fail=1
else
  note "downstream violating caller" "ok (rejected)"
fi
cd "$W"

echo
if [ "$fail" -ne 0 ]; then
  echo "FAILED — a caller contract was dropped. See reports/audit-2026-07-25-contract-loss-under-inlining.md"
  exit 1
fi
echo "PASSED — caller contracts survive inlining at every pinned configuration."
