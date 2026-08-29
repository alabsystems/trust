//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: WIDENED 2026-08-22 by 0acfcc223a2 (fix(spec-elab)) on 74f315aa368's
//@ probe-note: return-domain attach sites: `island_return_domain` reads the Pi-codomain
//@ probe-note: of the kernel-checked type, so `c42()` types the atom at UInt64.
//@ probe-note: Zero-arity def, called with an empty argument list from the clause.
clean { def c42 : UInt64 := UInt64.ofNat 42 }
pub fn answer() -> u64
    ensures result == c42()
{
    42
}
