pub fn first_even(v: &[u32]) -> Option<u32> {
    v.iter().copied().find(|x| x % 2 == 0)
}
