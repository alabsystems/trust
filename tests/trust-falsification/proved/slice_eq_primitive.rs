#![crate_type = "lib"]
// PROVED (Imp4, slice/str PartialEq total-builtin): comparing two byte slices (or a
// `&str`, modeled as `Slice<u8>`) via `==` lowers `<[u8] as PartialEq>::eq` as a TOTAL
// builtin — the elementwise compare runs no user code and cannot panic. Before Imp4 the
// call had no arm in `total_trait_call_on_total_type` (only primitive-Copy and
// element-free std leaves), so it hit `resolve_call_target -> UnsupportedOp` and POISONED
// the whole function to UNKNOWN. Now the `Ty::Slice { elem }` PartialEq arm (gated on a
// primitive-Copy element) discharges it. Mirrors astream `subject.rs` `seg == lit`.
// `x == x` is reflexively true; the function is panic-free. MUST verify (exit 0).
pub fn eq_bytes(a: &[u8], b: &[u8]) -> bool {
    a == b
}

pub fn eq_str(s: &str, t: &str) -> bool {
    s == t
}
