// Candidate proof fixture: flawed ownership/borrowing transfer invariant.

fn transfer_unchecked(src: &mut u32, dst: &mut u32, amount: u32) -> bool {
    *src -= amount;
    *dst += amount;
    true
}

fn main() {
    let mut left = 7;
    let mut right = 3;
    let before = left + right;
    let moved = transfer_unchecked(&mut left, &mut right, 4);
    let after = left + right;
    assert!(moved);
    assert_eq!(before, after);
}
