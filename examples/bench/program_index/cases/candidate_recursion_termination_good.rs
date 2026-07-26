// Candidate proof fixture: structurally decreasing recursion.

fn countdown_sum(n: u32) -> u32 {
    if n == 0 { 0 } else { n + countdown_sum(n - 1) }
}

fn main() {
    let value = countdown_sum(4);
    assert_eq!(value, 10);
}
