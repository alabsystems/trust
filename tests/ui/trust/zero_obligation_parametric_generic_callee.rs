//@ revisions: default strict certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//@ forbid-output: native-verification-gap
//@ forbid-output: "outcome":"unknown"
//@ forbid-output: this function has no obligation of its own
//! R43-ZERO-ROW-PARITY (2026-10-13, docs/DECISION_QUEUE.md): a zero-obligation body
//! whose only call is to a GENERIC local function that the R43 parametric premises
//! discharge (registered panic-free, its MIR holds no panic-capable terminator at
//! all, and the call resolves to that very `InstanceKind::Item`) is vacuously clean.
//! The bundle's proven-total lane already credited the call; the zero-row call gate
//! read only the argument-free registry, which a turbofish key never meets, so these
//! bodies published the `unknown` gap row and were refused under strict
//! (`tests/run-make/trust-cg-f1-generic-instance`, subject A). The twin that must stay
//! refused is `zero_obligation_parametric_generic_callee_boundary.rs`.

#[inline(never)]
fn ident<T>(x: T) -> T {
    x
}

#[inline(never)]
fn konst<const N: usize>() -> usize {
    N
}

pub struct W<T>(T);

impl<T> W<T> {
    #[inline(never)]
    fn take(self) -> T {
        self.0
    }
}

// The subject of `tests/run-make/trust-cg-f1-generic-instance`, verbatim.
#[unsafe(no_mangle)]
pub extern "C" fn f(x: u64) -> u64 {
    ident::<u64>(x) ^ 7
}

pub fn two_instances(x: u8, y: u32) -> (u8, u32) {
    (ident::<u8>(x), ident::<u32>(y))
}

pub fn const_instance() -> usize {
    konst::<4>()
}

pub fn inherent_instance(x: u16) -> u16 {
    W(x).take()
}

// A generic caller: the call's arguments name the caller's own parameter, and the
// callee's shape is panic-free at every instantiation.
pub fn generic_caller<U: Copy>(u: U) -> U {
    ident::<U>(u)
}
