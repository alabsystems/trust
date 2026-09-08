//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-HM): `&mut T` PARAMS whose pointee is a bare type parameter, a
//! tuple, an enum, or a scalar-element array are registered as mut borrow
//! pointers (the wave-23 `&mut Struct` argument, one pointee kind over each):
//! forwarding (`g(state)`, `&mut *state`, the `state.m()` receiver reborrow)
//! resolves; writes and reads keep their own gates. The derive(Hash)
//! `state: &mut H` forward is the measured shape. Under `strict`.

fn sink<H>(_h: &mut H) {}

fn forward_param<H>(state: &mut H) {
    sink(state);
    sink(&mut *state);
}

fn forward_tuple(t: &mut (u8, u16)) -> u8 {
    sink(t);
    t.0
}

fn forward_enum(o: &mut Option<u32>) -> bool {
    sink(&mut *o);
    o.is_some()
}

fn main() {
    let mut h = 5u64;
    forward_param(&mut h);
    let mut t = (1u8, 2u16);
    if forward_tuple(&mut t) != 1 {
        std::process::exit(1);
    }
    let mut o = Some(3u32);
    if !forward_enum(&mut o) {
        std::process::exit(2);
    }
}
