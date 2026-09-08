//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: RECLASSIFIED 2026-08-23 (ill-typed-goal gate): the elaborated goal was
//@ probe-note: ALWAYS ill-typed -- a variable-less atom defaults to the Nat domain, so the
//@ probe-note: UInt64 island call sat under an `Eq Nat`. The defeq route used to reach the
//@ probe-note: judgment and fail as not-defeq; both routes now type the goal FIRST and fail
//@ probe-note: closed at the clause with the carrier named in the diagnostic. Same verdict
//@ probe-note: direction, earlier and honest about WHERE the boundary is.
//@ probe-note: Identity def applied to a literal — the clause side is a closed term,
//@ probe-note: so this isolates literal handling from constant-function minting.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): DISCHARGES. The
//@ probe-note: literal argument takes the atom's domain exactly as it did before; what
//@ probe-note: changed is that the ATOM now has one (`Machine(U64)`, from the self mint)
//@ probe-note: instead of defaulting to `Nat`, and `cid`'s declared `UInt64` parameter
//@ probe-note: carrier is checked against it before the argument is built.
clean { def cid (x : UInt64) : UInt64 := x }
pub fn answer() -> u64
    ensures result == cid(42)
{
    42
}
