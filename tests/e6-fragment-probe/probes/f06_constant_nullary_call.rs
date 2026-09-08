//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: RECLASSIFIED 2026-08-23 (ill-typed-goal gate): the elaborated goal was
//@ probe-note: ALWAYS ill-typed -- a variable-less atom defaults to the Nat domain, so the
//@ probe-note: UInt64 island call sat under an `Eq Nat`. The defeq route used to reach the
//@ probe-note: judgment and fail as not-defeq; both routes now type the goal FIRST and fail
//@ probe-note: closed at the clause with the carrier named in the diagnostic. Same verdict
//@ probe-note: direction, earlier and honest about WHERE the boundary is.
//@ probe-note: A nullary Rust fn citing a one-parameter def applied to a literal.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): this row now
//@ probe-note: DISCHARGES. The obstacle was never the constant lane — it was the clause
//@ probe-note: elaborator taking a variable-less atom's domain from a DEFAULT (`Nat`) rather
//@ probe-note: than from the declared signature of the calls in it, so `UInt64` values sat
//@ probe-note: under an `Eq Nat` that could not type. The atom now takes the `Machine(U64)`
//@ probe-note: domain the SELF mint recorded (a mint knows the domain it built its own
//@ probe-note: declaration at), and `c42`'s declared `UInt64` result and parameter carriers
//@ probe-note: are CHECKED against it rather than guessed from. `c42 (UInt64.ofNat 0)`
//@ probe-note: delta-unfolds to the same `UInt64.ofNat 42` the mint carries.
clean { def c42 (x : UInt64) : UInt64 := 42 }
pub fn answer() -> u64
    ensures result == c42(0)
{
    42
}
