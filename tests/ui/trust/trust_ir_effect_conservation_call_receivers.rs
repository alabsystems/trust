//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! The effect-conservation gate pairs a trait-method call by its SITE — the `FnDef` AND the
//! receiver / generic args — and matches effectful calls before audited-equivalence ones.
//!
//! The first gate (97de0ab9ac) paired by `FnDef` alone and in MIR order. Its 2026-10-01 review
//! found the false REFUSALS below (strict errors on faithful bodies): an exempt
//! `<str as PartialEq>::eq` (a string-pattern `match`, lowered byte-wise) or `Range::next` (a
//! range loop, lowered arithmetically) listed before a user `<Foo as PartialEq>::eq` /
//! `<Fds as Iterator>::next` took the trust-ir call the user one needed, and the user call — which
//! the trust-ir DOES carry — was reported lost. The same calls in the other order passed. The
//! false PASS the same rule allowed is pinned in
//! `trust_ir_effect_conservation_review_lost_effects.rs`.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub struct Foo(pub i32);

impl PartialEq for Foo {
    fn eq(&self, o: &Foo) -> bool {
        unsafe { close(o.0) == 0 }
    }
}

pub fn str_then_user(s: &str, a: &Foo, b: &Foo) -> u32 {
    let k = match s {
        "x" => 1,
        _ => 2,
    };
    if *a == *b { k } else { 0 }
}

pub fn user_then_str(s: &str, a: &Foo, b: &Foo) -> u32 {
    let e = *a == *b;
    let k = match s {
        "x" => 1,
        _ => 2,
    };
    if e { k } else { 0 }
}

pub struct Fds {
    pub i: i32,
    pub n: i32,
}

impl Iterator for Fds {
    type Item = i32;
    fn next(&mut self) -> Option<i32> {
        if self.i < self.n {
            self.i += 1;
            unsafe { close(self.i) };
            Some(self.i)
        } else {
            None
        }
    }
}

pub fn range_then_user(n: u32, it: &mut Fds) -> u32 {
    let mut c = 0;
    for _ in 0..n {
        if it.next().is_some() {
            c += 1;
        }
    }
    c
}

pub fn user_only(it: &mut Fds) -> u32 {
    if it.next().is_some() { 1 } else { 0 }
}
