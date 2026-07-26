#![crate_type = "lib"]
// Trust R3 (generics WIN W1): a T-INDEPENDENT bounds obligation inside an
// alias-generic fn (`I::Item` is the pre-monomorphization projection alias)
// must PROVE for all I: the guard `i < xs.len()` discharges the index. Before
// R3 the alias declaration marker forced the whole function to Unknown and
// native lowering aborted on the marker type. Pairs with the mutant (`xs[i+1]`
// under the same guard), which must REFUTE.
pub fn r3_pick<I: Iterator>(xs: &[I::Item], i: usize) -> Option<&I::Item> {
    if i < xs.len() { Some(&xs[i]) } else { None }
}
