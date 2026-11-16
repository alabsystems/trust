//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//! THE MAGIC-NUMBER GUARD, written the way an author writes it: an island
//! definition that compares a machine-integer parameter against a LITERAL, in
//! the plain `decide (d < 21)` sugar, discharging an uncited `ensures`.
//!
//! ## What this fixture is for
//!
//! `decide (a < b)` at an unsigned carrier with two PARAMETERS has discharged
//! since E6 widening increment 5 (`e9_comparison_bool_discharge`). With a
//! LITERAL operand it did not: `decide (d < 21)`, `decide (d < UInt32.ofNat
//! 21)` and `decide (Nat.lt (UInt32.toNat d) 21)` all reported *"the two sides
//! are not definitionally equal (Eq.refl does not check)"*, and the only
//! spelling that worked named its own instance —
//! `Decidable.decide (LT.lt d (UInt32.ofNat 21)) (instDecidableUInt32Lt d
//! (UInt32.ofNat 21))` — which no author would write. Comparison against a
//! constant is the most common contract shape there is (bounds, caps, magic
//! numbers), so that made the surface unusable for exactly the guards the
//! two-language conversion is built out of.
//!
//! ## The cause was on the Clean side, and is fixed there
//!
//! `decide X` binds `X` to `decide`'s implicit `{p : Prop}` and the assignment
//! stores the weak-head-normalised proposition, so the `Decidable` goal is
//! already `Nat`-level. Recovering `instDecidableUInt32Lt` from that goal means
//! inverting `BitVec.toNat 32 (UInt32.toBitVec ?b)` — which succeeds while the
//! operand is a variable and fails once it is `UInt32.ofNat 21`, so the search
//! falls through to `instDecidableNatLt`. That fall-through was fatal only
//! because `UInt32.decLt` was a bespoke `dite` over `Nat.ble` while `Nat.decLt`
//! is a `Bool.rec` dispatcher: the two were not convertible even with NO
//! literal anywhere. Clean's BitVec-carrier wrapper builder now defines
//! `<T>.decLe`/`<T>.decLt` as `Nat.decLe`/`Nat.decLt` on the `toNat` images —
//! the shape the Nat-carrier branch of the same builder already used — so
//! whichever instance is resolved, the kernel sees one decision.
//!
//! Nothing in the compiler changed: the mint still emits `Decidable.decide
//! <prop> (instDecidable<Carrier>Lt l r)` and the clause is still closed by the
//! kernel's own `Eq.refl`. This fixture therefore lands WITH the
//! `first-party/clean` gitlink that carries that repair, and not before.
//!
//! The negative direction is `e9_island_literal_decide_sugar_divergent`: the
//! same sugar against a DIFFERENT constant stays refused.
//!
//! `dont-check-compiler-stderr` because this file is written in the lane that
//! repairs Clean and cannot rebuild a stage to bless the output; under strict
//! verification a `check-pass` IS the assertion (an undischarged clause is a
//! build error, never a downgraded unknown — `..._divergent` measures that).
//! Drop the directive and `--bless` once a stage carries the gitlink.

clean {
    def depth_fits_isl (d : UInt32) : Bool := decide (d < 21)
}

fn octree_depth_fits(depth: u32) -> bool
    ensures result == depth_fits_isl(depth)
{
    depth < 21
}

fn main() {
    let _ = octree_depth_fits(3);
}
