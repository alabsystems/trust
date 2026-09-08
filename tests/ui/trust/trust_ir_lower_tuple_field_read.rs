//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-FT): a TUPLE-typed field read — `(t.0).0`'s inner link and
//! `s.pair` on a struct holding a tuple — is admitted by the `Field` arm
//! exactly as a registered-struct link is; each element read that follows is
//! gated at its own site. Under `strict`.

struct S {
    pair: (u8, u16),
}

fn nested_tuple(t: ((u32,), u8)) -> u32 {
    (t.0).0
}

fn tuple_field(s: S) -> u16 {
    s.pair.1
}

fn main() {
    if nested_tuple(((41,), 0)) + 1 != 42 {
        std::process::exit(1);
    }
    if tuple_field(S { pair: (1, 42) }) != 42 {
        std::process::exit(2);
    }
}
