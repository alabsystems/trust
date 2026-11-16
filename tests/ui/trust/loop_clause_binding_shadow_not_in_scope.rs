//@ revisions: alias2 alias0 alias_o3 alias_cert const2 const0 req2 req0 proj2
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[alias2] compile-flags: -Cdebuginfo=2
//@[alias0] compile-flags: -Cdebuginfo=0
//@[alias_o3] compile-flags: -Copt-level=3 -Cdebuginfo=2
//@[alias_cert] compile-flags: -Cdebuginfo=2 -Ztrust-policy=certify -Cpanic=abort
//@[const2] compile-flags: -Cdebuginfo=2
//@[const0] compile-flags: -Cdebuginfo=0
//@[req2] compile-flags: -Cdebuginfo=2
//@[req0] compile-flags: -Cdebuginfo=0
//@[proj2] compile-flags: -Cdebuginfo=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! VS-1 follow-up (2026-10-04): a loop clause's identifier means the binding IN
//! SCOPE AT THE LOOP. VC generation bound it by debug spelling over the whole
//! body, and a binding whose only `var_debug_info` row is a constant
//! (`let x = 50u32;`) or a projection (`let x = p.0;`) names no local, so the
//! spelling fell back to the PARAMETER `x`. Every invariant below is FALSE for
//! the `x` in scope, and each revision must fail on its function, with the
//! refusal naming the clause.
//!
//! `lp_alias` is the review's fixture. Its rows before TrustVerify are
//! `x => _1, k => _2, z => _1, z => _2, i => _3, x => const 50_u32`. VS-1 drops
//! `z`, which is on two locals, so `_1` falls back to `x`: the clause bound
//! `_3 >= _1`, and at `lp_alias(0, 0)` the loop head has `i = 0`, `x = 50`.
//! Measured on a stage 1 with VS-1 (before this fix): `3 proved`, exit 0, at
//! -Cdebuginfo=2, -Cdebuginfo=0 and -Copt-level=3, and exit 0 with
//! `of which 1 kernel-certified` under certify. The old last-write collapse
//! left `z` on `_1`, so `x` named nothing and the clause failed closed (read
//! from the collapse rules, not re-measured on a pre-VS-1 build): VS-1 widened
//! the hazard. `lp_const` is the same body without the alias, and `lp_requires` is
//! KNOWN_HAZARDS residual 1 (`requires x < 10` makes the PARAMETER satisfy
//! `x < 10`): both reported `3 proved` at both levels before this fix, the
//! latter with 3 rows kernel-certified. `lp_proj` is a projection shadow. MIR
//! keeps `let x = p.0;` in its own local here (at -Cdebuginfo=2, -Copt-level=1
//! and 3 alike), so `x` has rows on two locals, VS-1's rule makes it name
//! nothing, and the clause is unknown before and after this fix without
//! reaching this check; it pins that the shape stays refused. A projection ROW
//! is refused by the same evidence rule as a constant row (unit tests in
//! trust-mir-extract's `loop_clause_binding.rs`).
//!
//! Re-pinned 2026-10-15 (the merge of 2026-10-14): every revision is still refused on its
//! function, and the refusal still names the clause, but one step EARLIER. The loop-clause
//! identity binding (97a55c9d86f, loop-clause names bind by HIR identity) already fails to
//! bind `x` to the binding in scope, so the clause reaches VC generation as
//! `UserLoopContractUnsupported` ("loop invariant `i >= x` references an unsupported or
//! ambiguous MIR value", an `unknown` row) and the VS-1 scope check after it has nothing left
//! to rewrite, so its "loop clause is not verified" warning is not printed. That note is now
//! pinned at the function in place of the warning at the clause.
#![allow(unused_variables, unused_assignments)]

#[cfg(any(alias2, alias0, alias_o3, alias_cert))]
pub fn lp_alias(x: u32, k: u32) -> u32 {
    //[alias2,alias0,alias_o3,alias_cert]~^ ERROR strict verification failed for
    //[alias2,alias0,alias_o3,alias_cert]~| NOTE loop invariant `i >= x` references an unsupported or ambiguous MIR value
    let z = x;
    {
        let z = k;
    }
    let mut i = x;
    let x = 50u32;
    while i < 5
        invariant i >= x
        // (re-pinned 2026-10-15: refused by name at the function; see the header)
    {
        i += 1;
    }
    i
}

#[cfg(any(const2, const0))]
pub fn lp_const(x: u32) -> u32 {
    //[const2,const0]~^ ERROR strict verification failed for
    //[const2,const0]~| NOTE loop invariant `i >= x` references an unsupported or ambiguous MIR value
    let mut i = x;
    let x = 50u32;
    while i < 5
        invariant i >= x
        // (re-pinned 2026-10-15: refused by name at the function; see the header)
    {
        i += 1;
    }
    i
}

#[cfg(any(req2, req0))]
pub fn lp_requires(x: u32) -> u32
    //[req2,req0]~^ ERROR strict verification failed for
    //[req2,req0]~| NOTE loop invariant `x < 10` references an unsupported or ambiguous MIR value
    requires x < 10
{
    let x = 50u32;
    let mut i = 0u32;
    while i < 3
        invariant x < 10
        // (re-pinned 2026-10-15: refused by name at the function; see the header)
    {
        i += 1;
    }
    i
}

#[cfg(proj2)]
pub fn lp_proj(x: u32, p: (u32, u32)) -> u32
    //[proj2]~^ ERROR strict verification failed for
    requires x < 10
{
    let x = p.0;
    let mut i = 0u32;
    while i < 3
        invariant x < 10
    {
        i += 1;
    }
    i
}
