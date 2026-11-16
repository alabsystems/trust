//@ dont-check-compiler-stderr
//@ check-fail
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// Re-pinned 2026-10-15 (the merge of 2026-10-14 brought WS5.2, 87388a9d3ec and aa2f22aa306):
// `Function.name` is now the link-time symbol, and a GENERIC definition has none until
// per-instance lowering (B8), so `-Ztrust-ir-lower=strict` refuses each one by name at crate
// assembly ("lowered for coverage, never spliced"). Those refusals are pinned below; every
// other body must still lower, and any other strict error fails this test.
//! Trust (wave-HM): `&mut T` PARAMS whose pointee is a bare type parameter, a
//! tuple, an enum, or a scalar-element array are registered as mut borrow
//! pointers (the wave-23 `&mut Struct` argument, one pointee kind over each):
//! forwarding (`g(state)`, `&mut *state`, the `state.m()` receiver reborrow)
//! resolves; writes and reads keep their own gates. The derive(Hash)
//! `state: &mut H` forward is the measured shape. Under `strict`.

fn sink<H>(_h: &mut H) {}
    //~^ ERROR NoLinkTimeSymbol(sink): no link-time symbol for `sink`

fn forward_param<H>(state: &mut H) {
    //~^ ERROR NoLinkTimeSymbol(forward_param): no link-time symbol for `forward_param`
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
