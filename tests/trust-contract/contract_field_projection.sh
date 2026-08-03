#!/bin/sh
# Field projections in first-class (KEYWORD) contract clauses.
#
# THE DEFECT this battery exists to catch: `tokenize_contract_snippet` in
# compiler/rustc_mir_transform/src/trust_contract_query.rs had no `Dot` token,
# so ANY clause containing a single `.` failed to LEX and the whole predicate
# was minted `Unsupported` ("unsupported contract predicate expression"). That
# made every lifecycle/temporal property — all of which are statements about
# STRUCT FIELDS mutated across methods — unstateable in the keyword form.
#
# It was never field-specific: `requires x <= 1.5` on a bare scalar parameter
# failed identically, because a float literal also contains a lone `.`. The
# three plausible-looking `?` sites in `lower_projection_base` were red
# herrings — that is the `#[ensures(..)]` ATTRIBUTE lane, which a keyword
# clause never enters (it is `ContractClauseOrigin::Native`, no HIR predicate).
#
# THE NAME CONTRACT this pins. `trust_vcgen::place_to_var_name` renders
# `Projection::Field(i)` as `.i` (POSITIONAL, never by source name) and
# `Projection::Deref` as a POSTFIX `*`, so a `&mut self` field `(*_1).0.0` is
# the var `self*.0.0`. The contract side must therefore emit the TEXT
# `(*self).0.0` — `spec_parse` lowers that, and only that, to `self*.0.0`
# (a literal `self*` tokenizes as multiplication and does not parse).
#
# NON-VACUITY IS THE POINT: every PROVE case below is paired with a REFUTED
# case of the same shape whose body falsifies the postcondition. If the
# positive cases pass while the negative ones also "pass", the check is inert
# and this battery must fail.
set -eu

REPO=$(cd "$(dirname "$0")/../.." && pwd)
TRUSTC=${TRUSTC:-$REPO/build/host/stage2/bin/trustc}
[ -x "$TRUSTC" ] || { echo "SKIP: no stage2 trustc at $TRUSTC (run ./x.py build --stage 2)"; exit 0; }

W=$(mktemp -d); trap 'rm -rf "$W"' EXIT; cd "$W"
fail=0
note() { printf '  %-56s %s\n' "$1" "$2"; }

run() {
  src=$1; shift
  # Verification is ON by default; deliberately no -Ztrust-verify flag, whose
  # spelling has changed across toolchains and would silently break this
  # battery (the old stage0 takes `-Zno-trust-verify=yes`, current takes
  # `-Ztrust-verify=on`). The harness guard below catches such a break.
  "$TRUSTC" -Zthreads=1 -Coverflow-checks=on \
    --edition 2021 --emit=metadata --out-dir "$W/o$$" "$@" "$src" \
    >"$W/out.txt" 2>"$W/err.txt" || return $?
  return 0
}

# The clause must LOWER (not be rejected at the source boundary) AND every
# obligation must be discharged.
expect_prove() {
  desc=$1; src=$2; shift 2
  if ! run "$src" "$@"; then
    reason=$(grep -oE 'unsupported contract predicate expression `[^`]*`' "$W/err.txt" | head -1)
    [ -n "$reason" ] || reason=$(grep -m1 -E '^error' "$W/err.txt" || echo 'unknown error')
    note "$desc" "FAIL (not proved: $reason)"; fail=1
    return
  fi
  # A clause that silently became Unsupported/Opaque can still exit 0 in some
  # configurations; require the predicate to have actually been lowered.
  if grep -q "was not lowered into a typed verifier formula" "$W/err.txt" "$W/out.txt"; then
    note "$desc" "FAIL (compiled, but predicate was not typed)"; fail=1
    return
  fi
  note "$desc" "ok (proved)"
}

# The clause must lower and then be REFUTED or left unproved — never accepted.
expect_reject() {
  desc=$1; src=$2; shift 2
  if run "$src" "$@"; then
    note "$desc" "FAIL (accepted a false postcondition)"; fail=1
    return
  fi
  if grep -qE "unknown unstable option|Unrecognized option|error: couldn't read" "$W/err.txt"; then
    note "$desc" "FAIL (harness broken)"; fail=1
    return
  fi
  if grep -qE "Trust (strict )?(verification|Level 0)" "$W/err.txt"; then
    note "$desc" "ok (rejected by the verifier)"
  else
    note "$desc" "FAIL (non-zero exit, but not a verification rejection)"; fail=1
  fi
}

# ------------------------------------------------------- ONE-LEVEL, bool field
cat > p1_true.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub flag: bool }
impl S {
    pub fn clear(&mut self) ensures !self.flag { self.flag = false; }
}
EOF
cat > p1_false.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub flag: bool }
impl S {
    // The body ESTABLISHES THE OPPOSITE. Must never prove.
    pub fn clear(&mut self) ensures !self.flag { self.flag = true; }
}
EOF

echo "one-level bool field postcondition:"
expect_prove  "ensures !self.flag           (body sets false)" p1_true.rs
expect_reject "ensures !self.flag           (body sets TRUE)"  p1_false.rs

# ------------------------------------------------------ ONE-LEVEL, integer field
cat > p2_true.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
impl S {
    pub fn reset(&mut self) ensures self.n == 0 { self.n = 0; }
}
EOF
cat > p2_false.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
impl S {
    pub fn reset(&mut self) ensures self.n == 0 { self.n = 1; }
}
EOF

echo "one-level integer field postcondition:"
expect_prove  "ensures self.n == 0          (body stores 0)"   p2_true.rs
expect_reject "ensures self.n == 0          (body stores 1)"   p2_false.rs

# ----------------------------------------------------- NESTED (two levels deep)
# The real target: aterm's `ensures !self.storage.<field>`.
cat > p3_true.rs <<'EOF'
#![crate_type="lib"]
pub struct Storage { pub detached: bool }
pub struct Grid { pub storage: Storage }
impl Grid {
    pub fn abort(&mut self) ensures !self.storage.detached {
        self.storage.detached = false;
    }
}
EOF
cat > p3_false.rs <<'EOF'
#![crate_type="lib"]
pub struct Storage { pub detached: bool }
pub struct Grid { pub storage: Storage }
impl Grid {
    pub fn abort(&mut self) ensures !self.storage.detached {
        self.storage.detached = true;
    }
}
EOF

echo "NESTED two-level field postcondition:"
expect_prove  "ensures !self.storage.detached  (body sets false)" p3_true.rs
expect_reject "ensures !self.storage.detached  (body sets TRUE)"  p3_false.rs

# ------------------------------------------------- projection over a NON-self param
cat > p4_true.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
pub fn get(s: &S) -> u64 ensures result == s.n { s.n }
EOF
cat > p4_false.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
pub fn get(s: &S) -> u64 ensures result == s.n { s.n + 1 }
EOF

echo "field projection over a plain reference parameter:"
expect_prove  "ensures result == s.n        (returns s.n)"     p4_true.rs
expect_reject "ensures result == s.n        (returns s.n + 1)" p4_false.rs

# ------------------------------------------------------------- FAIL-CLOSED cases
# Each of these has NO sound positional name, so the clause must stay
# unsupported (a hard build error) rather than be admitted under a guess.
cat > n1_enum.rs <<'EOF'
#![crate_type="lib"]
pub enum E { A(u64), B }
pub struct S { pub e: E }
// A field behind a discriminant has no unconditional place.
pub fn f(s: &S) -> u64 ensures result == s.e.0 { 0 }
EOF
cat > n2_method.rs <<'EOF'
#![crate_type="lib"]
pub struct S { pub n: u64 }
impl S { pub fn get(&self) -> u64 { self.n } }
// A method call is not a place.
pub fn f(s: &S) -> u64 ensures result == s.get() { s.get() }
EOF

echo "fail-closed shapes (must NOT be admitted):"
expect_reject "ensures result == s.e.0      (enum field)"      n1_enum.rs
expect_reject "ensures result == s.get()    (method call)"     n2_method.rs

# ------------------------------------------------------------------ REGRESSIONS
cat > r1.rs <<'EOF'
#![crate_type="lib"]
pub fn ident(x: u64) -> u64 ensures result == x { x }
EOF
cat > r2.rs <<'EOF'
#![crate_type="lib"]
pub fn ident(x: u64) -> u64 ensures result == x + 1 { x }
EOF

echo "scalar regressions (unchanged by the projection work):"
expect_prove  "ensures result == x          (returns x)"       r1.rs
expect_reject "ensures result == x + 1      (returns x)"       r2.rs

# ================================================================= OUT-PARAMETER
# A postcondition over a place written THROUGH a `&mut` parameter. This is a
# DIFFERENT defect from the lexer bug above, and it is not field-specific:
# `ensures *x == 0` over `{ *x = 0; }` failed identically to `ensures self.n ==
# 0`, and so did the FALSE twin — the two were indistinguishable.
#
# ROOT CAUSE (measured, trust-vcgen): the block-def extraction DOES produce the
# fact `Eq(Var("x*"), Int(0))` for the store `(*_1) = 0`, but
# `version_block_def_at_establish` cannot stamp it — it looks up the establish
# point of the `*`-STRIPPED base (`x`), and a `&mut` PARAMETER is never assigned
# in-body, so `block_def_establish_stmt` returns None and the fact is left BARE.
# The obligation body meanwhile IS versioned (`x*#s0_0`), so the bare fact is
# name-disjoint and `combine_relevant_block_defs` prunes it as irrelevant. The
# VC collapses to `Not(Eq(Var("x*#s0_0"), Int(0)))` — a query about a FREE
# variable, which the solver "refutes" whatever the body does.
#
# The fix is the out-parameter pin in
# `trust-vcgen/src/generate/contract_vcs.rs` (`with_out_param_pins`).
cat > o1_true.rs <<'EOF'
#![crate_type="lib"]
pub fn set_zero(x: &mut u64) ensures *x == 0 { *x = 0; }
EOF
cat > o1_false.rs <<'EOF'
#![crate_type="lib"]
pub fn set_zero(x: &mut u64) ensures *x == 0 { *x = 1; }
EOF

echo "out-parameter (write through a &mut scalar parameter):"
expect_prove  "ensures *x == 0              (body stores 0)"   o1_true.rs
expect_reject "ensures *x == 0              (body stores 1)"   o1_false.rs

# SOUNDNESS: the pin must name the REACHING definition only. If the stale
# statement-0 fact were pinned under the reaching-definition's version token the
# VC would read `x*#s0_1 == 7 AND NOT(x*#s0_1 == 7)` — UNSAT, i.e. a silent
# FALSE PROVE of a plainly false clause (the final value is 0, not 7).
cat > o2_stale.rs <<'EOF'
#![crate_type="lib"]
pub fn overwrite(x: &mut u64) ensures *x == 7 { *x = 7; *x = 0; }
EOF

echo "out-parameter soundness (stale store must never prove):"
expect_reject "ensures *x == 7              (7 then OVERWRITTEN by 0)" o2_stale.rs

# A shared `&` parameter cannot be stored through, so nothing changes for it.
cat > o3_shared.rs <<'EOF'
#![crate_type="lib"]
pub fn get(x: &u64) -> u64 ensures result == *x { *x }
EOF
echo "shared reference regression:"
expect_prove  "ensures result == *x         (returns *x)"      o3_shared.rs

echo
if [ "$fail" -ne 0 ]; then
  echo "FAILED"
  exit 1
fi
echo "All field-projection contract checks passed."
