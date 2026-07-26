#![crate_type = "lib"]
// Exhaustive match whose `Some` arm dereferences a reference payload:
// `match o { Some(&x) => x, None => 0 }`. The `*&i32` load is through a SAFE
// reference, which the borrow checker guarantees is valid, so the native CHC
// models it as a fresh-symbolic value (annotated `ValidBorrow`) instead of
// fail-closing on the unknown address. Combined with the exhaustive-match lane
// (discriminant assume + Unreachable-as-obligation), the whole function is
// statically panic-free under the default strict policy.
pub fn match_ref_payload(o: Option<&i32>) -> i32 {
    match o {
        Some(&x) => x,
        None => 0,
    }
}
