//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-AI2, over wave-HM): `(*p)[K] = v` and `(*p)[K] op= v` through
//! a `&mut [T; N]` PARAM lower as the `(*p).field = v` chain arm's RMW shape
//! one aggregate kind over — Load the pointee, `InsertElement` at the
//! constant index, Store it back. wave-HM registers the scalar-element array
//! param as a mut borrow pointer (nrvo.rs's `init` is the measured shape). A
//! dynamic index, a constant OOB index, and a `&mut` of an array LOCAL keep
//! failing closed. Under `strict`.

pub fn init(buf: &mut [u8; 4]) {
    buf[1] = 3;
    buf[2] += 4;
}

// A `&mut` of an ARRAY LOCAL is not promotable and is deliberately absent:
// the lane is the param form (nrvo.rs's `init`), pinned above.
fn main() {}
