#![crate_type = "lib"]
// A constant index into a fixed-size array. rustc inserts a runtime bounds-check
// panic; Trust discharges it STATICALLY. The bounds obligation is the
// single-variable interval contradiction `_2 = 2 ∧ _2 >= 4` (the index `2` is a
// constant, the length `4` is const-folded). ay's zero-trust Farkas
// reconstruction handles bounds that meet at a point but not a constant GAP, so
// the clean CIC kernel certifies it via the interval-refutation path
// (`Int.le_trans` into the closed false `4 <= 2`, then `Int.lt_irrefl`). Default
// AND -full report kernel-Certified (task #37 — superior to rustc).
pub fn const_array_index() -> i32 {
    let arr = [10, 20, 30, 40];
    arr[2]
}
