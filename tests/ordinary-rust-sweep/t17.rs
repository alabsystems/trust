pub fn flag_set(bits: u32, i: u32) -> bool {
    i < 32 && (bits & (1u32 << i)) != 0
}
