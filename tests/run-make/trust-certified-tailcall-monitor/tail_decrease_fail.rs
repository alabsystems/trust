#![expect(incomplete_features)]
#![feature(explicit_tail_calls)]

// There is intentionally no `ensures` clause in this fixture. `fuel` makes the
// program terminate if TailCall E5 instrumentation is missing, while the
// authored measure remains unchanged on the first recursive edge.
fn tail_stalls(n: u8, fuel: u8) -> u8
    decreases n
{
    if fuel == 0 {
        return n;
    }
    become tail_stalls(n, fuel - 1);
}

#[test]
fn non_decreasing_recursive_tail_edge_fires_its_e5_monitor() {
    assert_eq!(tail_stalls(7, 2), 7);
}
