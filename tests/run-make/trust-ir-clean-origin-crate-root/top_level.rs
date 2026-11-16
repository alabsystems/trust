// Trust: a CRATE-ROOT Clean island. Before WS5.2 the `local-unlowered`
// declaration assemble pass 2 minted for `ctrl_min` was named by the def's
// canonical `def_path` and the appended Clean definition by its Clean name — at
// the crate root ONE string, the collision this test was written for. Since
// WS5.2 both are named by the Rust item's link-time symbol, so they are one row.
clean {
    def ctrl_min (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
}

pub fn ctrl(a: u64, b: u64) -> u64 {
    ctrl_min(a, b)
}
