#![crate_type = "lib"]
// A match destructuring a NESTED `Option<(u32, u32)>` tuple payload — the shape an
// `enumerate`/`?` desugar produces. The Some payload is itself a 2-field tuple, so
// the match projects `Downcast(Some).Field(0).Field(0/1)`, a nested aggregate the
// CHC now tracks (recursive `AggregateValue`, #46). The match is exhaustive and
// panic-free, so it proves under the default strict policy.
pub fn match_nested_tuple(o: Option<(u32, u32)>) -> u32 {
    match o {
        Some((a, b)) => a.wrapping_add(b),
        None => 0,
    }
}
