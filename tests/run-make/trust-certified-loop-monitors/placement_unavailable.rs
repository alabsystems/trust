#[inline(never)]
fn nonself(n: u32) -> u32 {
    n
}

pub fn function_measure_without_direct_self_topology(n: u32) -> u32
    decreases n
{
    nonself(n)
}

pub fn invariant_without_a_runtime_loop(n: u32) {
    while false invariant n == n {
        unreachable!();
    }
}
