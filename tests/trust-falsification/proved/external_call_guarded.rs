#![crate_type = "lib"]
// The safe, MODELED equivalent of an unwrap: an exhaustive match on an `Option`
// parameter. Every path is panic-free and no unmodeled external call is reached,
// so the function proves under the default strict policy. Pairs with the mutant,
// which reaches `Option::unwrap` — an unmodeled external call that CAN panic — and
// must therefore fail closed. Guards #47: the external-call panic-soundness fix
// must refuse the unmodeled call WITHOUT over-rejecting the safe modeled idiom.
pub fn external_call_guarded(o: Option<u32>) -> u32 {
    match o {
        Some(v) => v,
        None => 0,
    }
}
