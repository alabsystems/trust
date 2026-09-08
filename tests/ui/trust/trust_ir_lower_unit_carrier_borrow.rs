//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-CBU: a SHARED borrow of an UNBOUND local whose pointee maps to
// `Ty::Unit` — a wave-ZB-skipped param-degraded payload binding
// (`E::A(a) => sink(&a)` in a generic body) or a genuine `()` local, both
// of which never bind by the value-less-unit and skip conventions. The
// borrow takes an OPAQUE UNIT SNAPSHOT: `Alloca Unit` + a fresh fact-free
// `PhantomData` store, the pointer joining `borrow_ptrs` only (no write
// channel — the local stays unbound, so every by-value read keeps failing
// closed at its own site). The pointee content is an abstraction for the
// degraded case, so `contains_call` is FORCED: structurally NotRun, never
// interpreted (the wave-EL/EMO discipline).

pub enum E<T> {
    A(T),
    B(i64),
}
pub fn sink<T>(_: &T) {}

// The measured shape: the ZB-skipped payload bind, borrowed as a call arg.
pub fn use_carrier<T>(e: E<T>) -> i64 {
    match e {
        E::A(a) => {
            sink(&a);
            1
        }
        E::B(n) => n,
    }
}

// The genuine-unit twin.
pub fn unit_borrow() -> i64 {
    let x = ();
    sink(&x);
    4
}
