// TRAP (σ-fidelity): the recursive call forwards a REASSIGNED parameter — `i` is
// mutated to `i + 3` between the entry (where P = `i < 4` holds and the access
// `a[i]` is safe) and the call, so the recursion receives i+3, not the entry `i`
// the invariant constrains (0 -> 3 -> 6: OOB at depth 2). A substitution σ that
// naively rendered the forwarded actual as the FORMAL name `i` (the entry value)
// would falsely certify the preservation step `P ∧ guards ⇒ P[σ]`; the faithful
// SSA-versioned σ makes it uncertifiable. Genuinely violable ⇒ MUST stay failed.
fn creep(a: &[u32; 4], n: usize, mut i: usize) -> u32 {
    let x = a[i];
    i += 3;
    if n > 0 { creep(a, n - 1, i) } else { x }
}
pub fn go() -> u32 { creep(&[1, 2, 3, 4], 2, 0) }
