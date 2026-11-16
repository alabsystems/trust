//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: assertion failed: s.tag == 0
//@ ignore-emscripten no processes
//! The WITNESS for `struct_field_named_tag_is_not_a_discriminant.rs` (TAG-FIELD-1):
//! the `tag_field` whose `assert!(s.tag == 0)` that file's BEFORE compiler read as
//! `assert proved` (the bridge stored the variant tag `0` in the field named `tag`),
//! called with `a = 5`.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the assertion really fails, not the verdict. Measured 2026-10-04 on the
//! stage 1 of `38e6c69b1c` (`scratchpad/stage1-w11fix`): this file built
//! `-Ztrust-verify=off` exits 101 with the message above. Built `-Ztrust-verify=on`
//! (default policy) it builds exit 0 with no Trust diagnostic, `tag_field` and `main`
//! both reading `assert proved`, and exits 101 the same way.

pub struct Tag {
    pub tag: i64,
    pub x: i64,
}

#[inline(never)]
pub fn tag_field(a: i64, b: i64) {
    let t = core::hint::black_box(a);
    let s = Tag { tag: t, x: b };
    assert!(s.tag == 0);
}

fn main() {
    tag_field(core::hint::black_box(5), 0);
}
