#![crate_type = "lib"]
// Trust R3 TRAP T3: genuinely-OOB generic index — the slice's length is
// symbolic and may be <= 10, so `&xs[10]` must REFUTE (runtime oracle: any
// instantiation with a short slice panics). Never provable for all I.
pub fn r3_t_oob<I: Iterator>(xs: &[I::Item]) -> &I::Item {
    &xs[10]
}
