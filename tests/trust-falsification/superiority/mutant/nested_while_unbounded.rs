#![crate_type = "lib"]
// SOUNDNESS REGRESSION for the product trip count (#50). The inner loop is an UNBOUNDED
// `while j < n` (n a parameter), so the self-add runs `4 * n` times — unbounded — and `t`
// genuinely overflows u16 for a large `n`. `block_execution_bound` must NOT emit a bound
// here: the add sits in the `while` loop, which has no `next` driver and no counter test
// with a bounded limit, so that containing loop has no driver and it returns None. If the product
// trip count ever counted only the bounded loops and ignored the unbounded `while`, it would
// UNDER-count the self-add's executions and FALSELY prove no overflow. The check stays sound:
// every loop must be a const-bounded iterator or no bound is emitted.
pub fn nested_while_unbounded(a: &[u8; 4], n: usize) -> u16 {
    let mut t: u16 = 0;
    for i in 0..4 {
        let _ = i;
        let mut j = 0usize;
        while j < n {
            t += a[j % 4] as u16;
            j += 1;
        }
    }
    t
}
