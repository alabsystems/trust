#![crate_type = "lib"]
// MUTANT + CRITICAL SOUNDNESS guard for the windows/chunks recognizer: the ONLY
// one-token change from proved/chunks_len.rs is `chunks(3)` → `chunks(0)`.
// `<[T]>::chunks(0)` PANICS at runtime (`assert!(chunk_size != 0)`). The bridge
// recognizes the constructor as total ONLY when the size is a literal `>= 1`, so a
// `0` size is NOT certified and the call fails closed. MUST be refused (exit 1) —
// if the recognizer ignored the size argument it would falsely prove a guaranteed
// panic. This is the discriminating guard that the panic-on-zero is never elided.
pub fn chunks_zero(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for c in s.chunks(0) {
        t = t.wrapping_add(c.len() as u32);
    }
    t
}
