//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// wave-ZB: a `Ty::Unit` enum-payload BIND (a genuine drop-free ZST field, or
// the degraded param-placeholder lane of a generic enum) is SKIPPED at the
// by-value classifier instead of refusing the body: no bind is pushed, the
// local stays UNBOUND, and the wave-UV value-less-unit invariant holds by
// construction. The variant TEST is untouched. Every actual USE of the var
// adjudicates itself — a genuine `()` read takes wave-UV's value-less no-op;
// any other read fails closed at its own site with `VarRef(unbound)` (see
// `used` below, which must NOT lower). Skipping a bind can never manufacture
// a value. The by-REF arm, the nested-payload arms, and the emitter keep the
// two-way reject verbatim.

pub enum Opt<T> {
    None_,
    Some_(T),
}

// The measured population: an UNREAD param-typed payload binding. The whole
// body used to refuse on `EnumMatch(zst payload binding)` for a value nobody
// consumed; it now lowers (generic-tag-match's `altfoo` shape).
pub fn unread<T>(o: Opt<T>) -> isize {
    match o {
        Opt::None_ => 1,
        Opt::Some_(_t) => 5,
    }
}

// A genuinely-unit payload, also unread.
pub fn unit_payload(o: Opt<()>) -> i32 {
    match o {
        Opt::None_ => 0,
        Opt::Some_(_u) => 7,
    }
}

// NEGATIVE — the payload var is READ: the skip leaves it unbound and the
// read fails closed (`VarRef(unbound)`). This body must NOT lower; it pins
// that the skip never manufactures a value.
pub fn used<T>(o: Opt<T>) -> T {
    match o {
        Opt::None_ => panic!(),
        Opt::Some_(t) => t,
    }
}
