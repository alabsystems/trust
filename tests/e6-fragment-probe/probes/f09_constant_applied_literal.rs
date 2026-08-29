//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: WIDENED 2026-08-22 by 0acfcc223a2 (fix(spec-elab)) on 74f315aa368's
//@ probe-note: return-domain attach sites: the closed clause term is variable-free, so
//@ probe-note: it was the Nat default — not literal handling — that refused it.
//@ probe-note: Identity def applied to a literal — the clause side is a closed term,
//@ probe-note: so this isolates literal handling from constant-function minting.
clean { def cid (x : UInt64) : UInt64 := x }
pub fn answer() -> u64
    ensures result == cid(42)
{
    42
}
