pub fn f(v: &mut Vec<u32>, i: usize) -> Vec<u32> {
    v.split_off(i)
}
