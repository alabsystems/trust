//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E6 widening increment 5, CLAUSE HALF — the decision-function lane, end to end.
//!
//! The body mint (`fn le(a, b) -> bool { a <= b }` → `Decidable.decide`) landed
//! first and was, for one release, unreachable: every spelling of its
//! postcondition was outside the clause fragment. `result == (a <= b)` typed the
//! whole atom from the nested comparison's `i64` variables and was reported as a
//! "mixed domains in one comparison" error; `result == le_isl(a, b)` built an
//! `Eq (BitVec 64)` around two Bool-valued sides, which the ill-typed-goal gate
//! (correctly) refused; and a bare `le_isl(a, b)` in PROPOSITION position was
//! refused unconditionally. All three are here, all three discharge.
//!
//! What makes it work is one recorded fact — an `Admission` now carries the
//! RETURN domain its mint declared — plus the split it enables: the OPERANDS of
//! `(a <= b)` keep their `BitVec 64` carrier while the RELATION becomes an
//! `Eq Bool`. The clause's decided comparison is emitted through the SAME
//! `decidable_comparison` pair the mint scrutinizes, so the two sides are
//! syntactically identical and `Eq.refl` closes them. An `Iff`, or the
//! equally-true `Nat.ble` spelling, would be stuck at a different head constant
//! and no reducibility setting would bridge it — the iota lesson of
//! docs/design/2026-07-25-select-encoding-ergonomics.md, restated for `Bool`.
//!
//! Each uncited clause pairs the two spellings in one conjunction. That is not
//! padding: the uncited defeq route owns only clauses that CALL an island
//! definition, and stating both together says the stronger thing — that the
//! author's `(a <= b)` and the island's `decide (Nat.le ..)` are the SAME term,
//! because both close against one minted body.

clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def le_isl (a : BitVec 64) (b : BitVec 64) : Bool :=
        decide (Nat.le (key64 a) (key64 b))
    def le_u (a : UInt64) (b : UInt64) : Bool := decide (a <= b)
    def in_range (a : BitVec 64) : Bool := Bool.true
}

// (1) The canonical spelling at a SIGNED carrier, uncited: the clause's
// `(a <= b)` IS the minted body, so definitional equality closes it. `key64` is
// a reducible helper; kernel delta-reduction bridges it to the mint's inlined
// keys.
pub fn le_i64(a: i64, b: i64) -> bool
    ensures result == (a <= b) && result == le_isl(a, b)
{
    a <= b
}

// (2) The UNSIGNED twin, and the `>=` operand-swap normalization: the clause
// says `b >= a` while the body computes `a <= b`. At an unsigned carrier the
// decision goes through Clean's own `instLEUInt64`/`instDecidableUInt64Le`
// rather than the signed sign-flip keys, which is why the island spells it as
// plain `decide (a <= b)`.
pub fn le_u64(a: u64, b: u64) -> bool
    ensures result == (b >= a) && result == le_u(a, b)
{
    a <= b
}

// (3) The guard-layer spelling: a `-> Bool` decision standing in PROPOSITION
// position on its own, read as `in_range(a) = true`. That reading is what this
// fixture pins, and it is the shape every decidable guard mirror is written in;
// before this change the arm refused EVERY call in proposition position, with a
// comment saying so. The island body is deliberately trivial, because a
// non-trivial one would not close by reflexivity: `decide (Nat.le k k)` on a
// NEUTRAL `k` is stuck, so proving it needs a cited theorem — and a cited clause
// that calls an island definition is a different lane, NOT exercised here.
// (That lane exists: the cited routes and the citation sweep admit the island
// definitions a clause names into a clause-local facet table, as the uncited
// defeq route always did — see `e9_cited_island_def_discharge`. It used to
// report "no diagnostic E6 facet record exists"; it is orthogonal to this.)
pub fn prop_position(a: i64) -> bool
    ensures in_range(a)
{
    true
}

fn main() {
    let _ = le_i64(1, 2);
    let _ = le_u64(1, 2);
    let _ = prop_position(1);
}
