//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (#182): the short-circuit `&&`/`||` join merges the BINDING ENVIRONMENT,
//! not just the boolean result.
//!
//! `lower_logical_op`'s doc comment used to say it "replicate[s] `lower_if`'s
//! block plumbing directly". The replication copied the result merge and omitted
//! the environment merge, which made this the ONLY join in the producer that let
//! an arm's rebinding escape its dominance region:
//!
//! ```text
//!   bb1:  %3 = const i32 3          ; z = 3, defined ONLY on this path
//!         br bb3(%4)
//!   bb2:  br bb3(%5)                ; z never assigned here
//!   bb3(%0: bool): condbr %0, bb4, bb5
//!   bb4:  %7 = icmp eq i32 %3, %6   ; reads %3 — bb1 does NOT dominate bb4
//! ```
//!
//! `bb3` joins `bb1` and `bb2`, so `bb1` does not dominate `bb4` and `%3` is out
//! of scope there. The read is *dynamically* safe — short-circuiting means bb4 is
//! only reachable via bb1 — but SSA scoping is a dominance property, not a
//! reachability one, and any consumer that allocates registers by dominance (the
//! trust-cg backend) is entitled to miscompile it.
//!
//! WHY NO DIFFERENTIAL CAUGHT THIS, AND WHY THAT IS THE POINT. The interpreter
//! resolves values through a global map, so it computes the RIGHT answer from the
//! ill-formed module and reports `verdict = agreed`. An interpreter that does not
//! model scoping cannot observe a scoping violation, so no amount of differential
//! sampling would ever have found it. `validate_module` is the only instrument
//! that can see it — this bug is the argument for the module well-formedness
//! ratchet, found as `UseBeforeDefInBlock` on
//! `tests/ui/rfcs/rfc-2497-if-let-chains/chains-without-let.rs`.
//!
//! The fix routes this join through the same `merged_locals` /
//! `seal_arm_into_join` helpers `lower_if` uses, so a hand-rolled `Br` to a join
//! no longer exists in this function.

// The shape that must now MERGE: `z` is bound BEFORE the `&&`, so the join can
// type a block-param for it and both predecessors pass their own version.
pub fn merged_across_and(c: bool) -> i32 {
    let mut z = 0;
    if c && {
        z = 3;
        true
    } {}
    z
}

pub fn merged_across_or(c: bool) -> i32 {
    let mut z = 0;
    if c || {
        z = 7;
        false
    } {}
    z
}

// The `||` twin, reading the merged local in the tail rather than after an `if`.
pub fn merged_tail(c: bool) -> i32 {
    let mut z = 1;
    let _b = c || {
        z = 9;
        true
    };
    z
}

// Nested short-circuits: the inner join's merge must survive the outer one.
pub fn merged_nested(c: bool, d: bool) -> i32 {
    let mut z = 0;
    let _b = c && {
        z = 2;
        d
    } && {
        z = 5;
        true
    };
    z
}

// A local NOT bound before the `&&` (`let z;`) has no pre-split version, so
// `merged_locals` cannot type a join param for it. It must stay UNBOUND after the
// join and fail closed as `VarRef(unbound)` — never silently read the RHS arm's
// value. Merging this honestly needs a maybe-initialized lattice (a poison edge
// value), which is B4 memory-model work. The `if`-shaped spelling
// (`let z; if c { z = 1 } else { z = 2 }`) already declines the same way, so this
// only makes the two spellings agree.
pub fn deferred_init_declines(c: bool) -> bool {
    let z;
    c && {
        z = 3;
        true
    } && z == 3
}

fn main() {}
