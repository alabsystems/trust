// Candidate proof fixture: ownership/borrowing with a preserved balance invariant.

fn transfer_guarded(src: &mut u32, dst: &mut u32, amount: u32) -> bool {
    if amount > *src {
        false
    } else if let Some(next_dst) = (*dst).checked_add(amount) {
        *src -= amount;
        *dst = next_dst;
        true
    } else {
        false
    }
}

fn main() {
    let mut left = 7;
    let mut right = 3;
    let before = left + right;
    let moved = transfer_guarded(&mut left, &mut right, 4);
    let after = left + right;
    assert!(moved);
    assert_eq!(before, after);
}
