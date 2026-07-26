// Candidate proof fixture: recursion that does not decrease on the recursive path.

fn countdown_stuck(n: u32) -> u32 {
    if n == 0 { 0 } else { 1 + countdown_stuck(n) }
}

fn main() {
    let value = countdown_stuck(0);
    assert_eq!(value, 0);
}
