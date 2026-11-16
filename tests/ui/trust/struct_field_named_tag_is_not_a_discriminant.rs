//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@[default] check-pass
//@[certify] check-fail
//@[memsafe] check-fail
//@ dont-check-compiler-stderr
//! A struct field NAMED `tag`, `discriminant` or `__tag` is data, not an enum tag
//! (TAG-FIELD-1).
//!
//! The trust-ir bridge built a struct aggregate in declaration order only when the
//! ADT carried a `layout`, which the extractor fills only on the faithful lane. On
//! the verifier lane every user struct took the flat-enum loop, where a field named
//! `__tag`, `tag` or `discriminant` got the variant tag (`0` for a struct) instead
//! of its operand, and the later operands shifted one field left. So `S { tag:
//! black_box(a), x: b }` stored `tag = 0`, and `assert!(s.tag == 0)` read `assert
//! proved` (`trust-full-verifier`, "no assertion ... is reachable") under every
//! policy. With `a = 5` the program panics `assertion failed: s.tag == 0` (the
//! witness, `struct_field_named_tag_is_not_a_discriminant_run.rs`). The `i64` field
//! matters (a `u32` one fails trust-ir validation instead), and so does
//! `black_box` (it keeps the operand symbolic).
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, 2026-10-04; each
//! revision's flags with `--emit=metadata`): `tag_field`, `discriminant_field` and
//! `dunder_tag_field` read `assert proved` in all three revisions and drew no
//! diagnostic; only the `tg_field` control did (its annotations fire BEFORE as
//! well). The lie annotations below did not fire.
//!
//! AFTER (predicted, then measured): a `Struct`-stamped aggregate takes the
//! declaration-order arm whatever its `layout`, so every field takes its own
//! operand and each lie function is the `tg_field` control under another field
//! name. The annotations on the three lie functions are what the BEFORE compiler
//! prints for a twin of this file with the three fields renamed (`tgx`, `discx`,
//! `__tgx`): exactly the control's diagnostics, `assert runtime_checked` —
//! default two WARNs, certify two ERRORs, memory-safe a WARN and an ERROR.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. The three lie functions read `assert
//! runtime_checked`, as `tg_field` does.

pub struct Tag {
    pub tag: i64,
    pub x: i64,
}

pub struct Disc {
    pub discriminant: i64,
    pub x: i64,
}

pub struct UTag {
    pub __tag: i64,
    pub x: i64,
}

pub struct Tg {
    pub tg: i64,
    pub x: i64,
}

#[inline(never)]
pub fn tag_field(a: i64, b: i64) {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::tag_field`
    //[default]~^^ WARN Trust verification advisory for `struct_field_named_tag_is_not_a_discriminant::tag_field`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::tag_field`
    //[certify]~^^^^ ERROR Trust strict verification failed for `struct_field_named_tag_is_not_a_discriminant::tag_field`
    //[memsafe]~^^^^^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::tag_field`
    //[memsafe]~^^^^^^ ERROR Trust memory-safe verification failed for `struct_field_named_tag_is_not_a_discriminant::tag_field`
    let t = core::hint::black_box(a);
    let s = Tag { tag: t, x: b };
    assert!(s.tag == 0);
}

#[inline(never)]
pub fn discriminant_field(a: i64, b: i64) {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::discriminant_field`
    //[default]~^^ WARN Trust verification advisory for `struct_field_named_tag_is_not_a_discriminant::discriminant_field`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::discriminant_field`
    //[certify]~^^^^ ERROR Trust strict verification failed for `struct_field_named_tag_is_not_a_discriminant::discriminant_field`
    //[memsafe]~^^^^^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::discriminant_field`
    //[memsafe]~^^^^^^ ERROR Trust memory-safe verification failed for `struct_field_named_tag_is_not_a_discriminant::discriminant_field`
    let t = core::hint::black_box(a);
    let s = Disc { discriminant: t, x: b };
    assert!(s.discriminant == 0);
}

#[inline(never)]
pub fn dunder_tag_field(a: i64, b: i64) {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::dunder_tag_field`
    //[default]~^^ WARN Trust verification advisory for `struct_field_named_tag_is_not_a_discriminant::dunder_tag_field`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::dunder_tag_field`
    //[certify]~^^^^ ERROR Trust strict verification failed for `struct_field_named_tag_is_not_a_discriminant::dunder_tag_field`
    //[memsafe]~^^^^^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::dunder_tag_field`
    //[memsafe]~^^^^^^ ERROR Trust memory-safe verification failed for `struct_field_named_tag_is_not_a_discriminant::dunder_tag_field`
    let t = core::hint::black_box(a);
    let s = UTag { __tag: t, x: b };
    assert!(s.__tag == 0);
}

// The control: the same body with a field name no recognizer reads.
#[inline(never)]
pub fn tg_field(a: i64, b: i64) {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::tg_field`
    //[default]~^^ WARN Trust verification advisory for `struct_field_named_tag_is_not_a_discriminant::tg_field`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::tg_field`
    //[certify]~^^^^ ERROR Trust strict verification failed for `struct_field_named_tag_is_not_a_discriminant::tg_field`
    //[memsafe]~^^^^^ WARN Trust Level 0 safety verification incomplete for `struct_field_named_tag_is_not_a_discriminant::tg_field`
    //[memsafe]~^^^^^^ ERROR Trust memory-safe verification failed for `struct_field_named_tag_is_not_a_discriminant::tg_field`
    let t = core::hint::black_box(a);
    let s = Tg { tg: t, x: b };
    assert!(s.tg == 0);
}
