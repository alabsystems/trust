pub fn overlapping_mutable_borrows() {
    let mut value = 0_u32;
    let first = &mut value;
    let second = &mut value;
    *first += 1;
    *second += 1;
}
