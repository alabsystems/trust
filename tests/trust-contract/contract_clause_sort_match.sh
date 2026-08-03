#!/bin/sh
# Contract clauses over NON-INTEGER (chiefly `bool`) places.
#
# THE DEFECT this battery exists to catch, and why the previous battery could
# not catch it. `contract_field_projection.sh` asserts only "proved" vs
# "rejected", and a fail-closed UNKNOWN is a rejection. Every `bool` clause in
# this repo was rejected that way — the FALSE twin "passed" for the wrong
# reason, so the negative half was VACUOUS. This battery asserts on the
# obligation OUTCOMES themselves (`-Ztrust-verify-output=json`), so a clause
# that merely refuses can never be mistaken for one that is refuted.
#
# ROOT CAUSE (measured). `trust_types::parse_spec_expr` takes a bare `&str` and
# has no type environment, so `Parser::variable` stamps every unbound leaf with
# the default `Sort::Int` (trust-types/src/spec_parse.rs:793-802). The
# compiler's own contract lowering carries the REAL sort. `Formula` derives
# structural `PartialEq` and `Var(String, Sort)` COMPARES THE SORT, so:
#
#     ensures !self.storage.f
#       typed lowering : Not(Var("self*.0.0", Bool))
#       re-parsed text : Not(Var("self*.0.0", Int))    <- differs ONLY in sort
#
# An INTEGER clause matches by coincidence (the sentinel IS `Int`). A `bool`
# clause never matches its own source text, with two consequences, both in
# crates/trust-vcgen/src/generate/contract_vcs.rs:
#
#   1. the dedup at the `seen_posts` loop appended a SECOND, ill-sorted copy of
#      the postcondition. It cannot lower to typed TrustIr, so it has no
#      `trust.vc.formula.payload` and lands Unknown — AND it denies the whole
#      function native evidence, which is why even the FALSE twin came back
#      `unknown` instead of `failed`.
#   2. `unique_source_contract_index_for_formula` returned `None`, so the typed
#      postcondition carried no `source_contract_index`; `trust_verify.rs:32245`
#      needs that index to build the body link, so the source-clause marker sat
#      at "awaits sealed private body authorities" forever.
#
# THE AXIS IS THE SORT, NOT THE NESTING DEPTH. Integer projections already
# proved AND refuted at depth 1, 2 and 3 before this fix; `bool` failed at
# depth 1 exactly as much as at depth 2. Both are pinned below so a future
# regression cannot be mis-blamed on nesting again.
#
# OBLIGATION COUNT IS PART OF THE CONTRACT. A clause of this shape must produce
# exactly TWO obligations — the source-clause marker plus one body VC. Three
# means the ill-sorted duplicate is back.
set -eu

REPO=$(cd "$(dirname "$0")/../.." && pwd)
TRUSTC=${TRUSTC:-$REPO/build/host/stage2/bin/trustc}
[ -x "$TRUSTC" ] || { echo "SKIP: no stage2 trustc at $TRUSTC (run ./x.py build --stage 2)"; exit 0; }
command -v python3 >/dev/null 2>&1 || { echo "SKIP: python3 required to read verifier JSON"; exit 0; }

W=$(mktemp -d); trap 'rm -rf "$W"' EXIT; cd "$W"
fail=0
note() { printf '  %-58s %s\n' "$1" "$2"; }

# Print "<total> <proved> <failed> <unknown>" over every obligation the
# verifier reported for the crate.
tally() {
  "$TRUSTC" -Zthreads=1 -Coverflow-checks=on --edition 2021 \
    --emit=metadata --out-dir "$W/o$$" -Ztrust-verify-output=json "$1" \
    >"$W/out.txt" 2>"$W/err.txt" || true
  python3 - "$W/err.txt" "$W/out.txt" <<'PY'
import json, sys
tot = pr = fa = un = 0
for path in sys.argv[1:]:
    try:
        fh = open(path)
    except OSError:
        continue
    for line in fh:
        line = line.strip()
        marker = "TRUST_JSON:"
        if marker not in line:
            continue
        try:
            d = json.loads(line[line.index(marker) + len(marker):])
        except ValueError:
            continue
        if d.get("type") != "function_result":
            continue
        for r in d.get("results", []):
            tot += 1
            o = r.get("outcome")
            if o == "proved":
                pr += 1
            elif o == "failed":
                fa += 1
            else:
                un += 1
print(tot, pr, fa, un)
PY
}

# The clause must be fully DISCHARGED: N obligations, all proved, none unknown.
expect_proved() {
  desc=$1; src=$2; want_total=$3
  set -- $(tally "$src")
  if [ "$1" = "$want_total" ] && [ "$2" = "$want_total" ] && [ "$3" = 0 ] && [ "$4" = 0 ]; then
    note "$desc" "ok (proved $2/$1)"
  else
    note "$desc" "FAIL (total=$1 proved=$2 failed=$3 unknown=$4; want ${want_total} proved)"
    fail=1
  fi
}

# The clause must be REFUTED — actually `failed`, never merely `unknown`.
# THIS IS THE NON-VACUITY GATE: an Unknown here means the verifier declined,
# which is exactly the pre-fix behaviour and must not be scored as a pass.
expect_refuted() {
  desc=$1; src=$2; want_total=$3
  set -- $(tally "$src")
  if [ "$1" = "$want_total" ] && [ "$3" -gt 0 ] && [ "$4" = 0 ]; then
    note "$desc" "ok (refuted $3/$1)"
  elif [ "$4" -gt 0 ]; then
    note "$desc" "FAIL (VACUOUS: total=$1 proved=$2 failed=$3 unknown=$4 — declined, not refuted)"
    fail=1
  else
    note "$desc" "FAIL (total=$1 proved=$2 failed=$3 unknown=$4; want a refutation)"
    fail=1
  fi
}

# --------------------------------------------- THE TARGET: nested `bool` field
# aterm's real blocker: `ensures !self.storage.scrollback_detached_for_reflow`.
cat > nb_true.rs <<'EOF'
#![crate_type="lib"]
pub struct St { pub f: bool }
pub struct G  { pub storage: St }
impl G {
    pub fn a(&mut self) ensures !self.storage.f { self.storage.f = false; }
}
EOF
cat > nb_false.rs <<'EOF'
#![crate_type="lib"]
pub struct St { pub f: bool }
pub struct G  { pub storage: St }
impl G {
    // The clause asserts the field is TRUE; the body makes it FALSE.
    pub fn a(&mut self) ensures self.storage.f { self.storage.f = false; }
}
EOF

echo "NESTED two-level bool field (the reported blocker):"
expect_proved  "ensures !self.storage.f      (body sets false)" nb_true.rs  2
expect_refuted "ensures  self.storage.f      (body sets false)" nb_false.rs 2

# ------------------------------------------- SAME DEFECT, ONE LEVEL (bool)
# Pinned to keep the axis honest: this failed identically before the fix, so a
# regression here is a SORT regression, not a nesting regression.
cat > b1_true.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub f: bool }
impl S { pub fn a(&mut self) ensures !self.f { self.f = false; } }
EOF
cat > b1_false.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub f: bool }
impl S { pub fn a(&mut self) ensures self.f { self.f = false; } }
EOF

echo "one-level bool field (broken by the SAME sort mismatch):"
expect_proved  "ensures !self.f              (body sets false)" b1_true.rs  2
expect_refuted "ensures  self.f              (body sets false)" b1_false.rs 2

# ------------------------------------------------------ bool RETURN VALUE
cat > br_true.rs <<'EOF'
#![crate_type="lib"]
pub fn g(x: bool) -> bool ensures result == x { x }
EOF
cat > br_false.rs <<'EOF'
#![crate_type="lib"]
pub fn g(x: bool) -> bool ensures result == x { !x }
EOF

echo "bool return value (no projection at all):"
expect_proved  "ensures result == x          (returns x)"      br_true.rs  2
expect_refuted "ensures result == x          (returns !x)"     br_false.rs 2

# ============================================================ CONTROLS
# Integer projections were ALREADY correct at every depth. They must not move.
cat > i1_true.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
impl S { pub fn d(&mut self) ensures self.n == 0 { self.n = 0; } }
EOF
cat > i1_false.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
impl S { pub fn d(&mut self) ensures self.n == 1 { self.n = 0; } }
EOF
cat > i2_true.rs <<'EOF'
#![crate_type="lib"]
pub struct St { pub n: u64 }
pub struct G  { pub storage: St }
impl G { pub fn a(&mut self) ensures self.storage.n == 0 { self.storage.n = 0; } }
EOF
cat > i2_false.rs <<'EOF'
#![crate_type="lib"]
pub struct St { pub n: u64 }
pub struct G  { pub storage: St }
impl G { pub fn a(&mut self) ensures self.storage.n == 1 { self.storage.n = 0; } }
EOF
cat > i3_true.rs <<'EOF'
#![crate_type="lib"]
pub struct U { pub n: u64 }
pub struct T { pub u: U }
pub struct G { pub s: T }
impl G { pub fn a(&mut self) ensures self.s.u.n == 0 { self.s.u.n = 0; } }
EOF

echo "integer controls (already correct at depth 1/2/3 — must not move):"
expect_proved  "ensures self.n == 0          (depth 1)"        i1_true.rs  2
expect_refuted "ensures self.n == 1          (depth 1, false)" i1_false.rs 2
expect_proved  "ensures self.storage.n == 0  (depth 2)"        i2_true.rs  2
expect_refuted "ensures self.storage.n == 1  (depth 2, false)" i2_false.rs 2
expect_proved  "ensures self.s.u.n == 0      (depth 3)"        i3_true.rs  2

# ------------------------------------------------------------- FAIL-CLOSED
# `ensures false` must stay refuted, and shapes with no sound positional name
# must stay UNPROVED. The sort relaxation forgives only a leaf's `Sort::Int`
# sentinel; it must never admit a clause that was previously refused.
cat > x1_false.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
impl S { pub fn d(&mut self) ensures false { self.n = 0; } }
EOF

echo "fail-closed regressions:"
expect_refuted "ensures false                (must stay refuted)" x1_false.rs 2

# A method call and an enum field have no unconditional place. These must NOT
# become proved; either a refusal or a refutation is acceptable, but a PROOF is
# a soundness regression.
cat > x2_enum.rs <<'EOF'
#![crate_type="lib"]
pub enum E { A(bool), B }
pub struct S { pub e: E }
pub fn f(s: &S) -> bool ensures result == s.e.0 { false }
EOF
cat > x3_method.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub f: bool }
impl S { pub fn get(&self) -> bool { self.f } }
pub fn f(s: &S) -> bool ensures result == s.get() { s.get() }
EOF

for c in x2_enum x3_method; do
  set -- $(tally "$c.rs")
  if [ "$3" -gt 0 ] || [ "$4" -gt 0 ]; then
    note "$c (no sound place: must not be admitted)" "ok (not admitted)"
  else
    note "$c (no sound place: must not be admitted)" "FAIL (ADMITTED: total=$1 proved=$2)"
    fail=1
  fi
done

echo
if [ "$fail" -ne 0 ]; then
  echo "FAILED"
  exit 1
fi
echo "All contract clause-sort checks passed."
