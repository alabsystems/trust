#![crate_type = "lib"]
// A match destructuring a NESTED struct payload: `Option<Pair>` where `Pair` is a
// 2-field struct. The Some payload is a struct (registered in the trust-ir module),
// so this exercises the nested-STRUCT aggregate path (distinct from the tuple path)
// — which requires the struct-id assignment to be collision-free (#46). Exhaustive
// and panic-free, so it proves under the default strict policy.
pub struct Pair {
    x: u32,
    y: u32,
}
pub fn match_struct_payload(o: Option<Pair>) -> u32 {
    match o {
        Some(p) => p.x.wrapping_add(p.y),
        None => 0,
    }
}
