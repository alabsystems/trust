//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-PR): a POINTER-LANE field read — `x.r` on a struct holding
//! `&u32`, `x.s` holding `&str` — yields the lane's pointer value unledgered:
//! it may be carried into a call, forwarded through a shared reborrow, or
//! returned; a deref of it keeps failing closed and is absent here. Under
//! `strict`. (`main` constructs only the `&u32` holder: a `&str` FIELD SEED
//! is a separately recorded refusal, `Adt(non-scalar field seed)`.)

pub struct R<'a> {
    r: &'a u32,
    n: u32,
}

pub struct S<'a> {
    s: &'a str,
}

fn take_ref(_x: &u32) {}

fn take_str(_s: &str) {}

fn a_ref(x: &R<'_>) {
    take_ref(x.r);
}

fn b_str(x: &S<'_>) {
    take_str(x.s);
}

fn c_str_len(x: &S<'_>) -> usize {
    x.s.len()
}

fn d_ret_ref<'a>(x: &R<'a>) -> &'a u32 {
    x.r
}

fn main() {
    let v = 41u32;
    let x = R { r: &v, n: 1 };
    a_ref(&x);
    take_ref(d_ret_ref(&x));
    if x.n != 1 {
        std::process::exit(1);
    }
}
