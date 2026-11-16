//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ forbid-output: REFUSED at crate assembly
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! RE-PINNED 2026-09-29 to `check-pass` (thir-generic-instance-callee). This file was
//! `check-fail` with one annotated "REFUSED at crate assembly" error per derived body, and its
//! own text asked to be re-pinned the day the generic-instance residue closed for this edge.
//! It has: the edge below (`std::cmp::impls::<impl std::cmp::PartialEq<&B> for &A>::eq`) takes a REFERENCE TO A POINTER (`&&T`), and the producer
//! declined to sign that parameter — the dropped-borrow guard in `recover_callee_param_tys` —
//! so the declaration kept the unknown-signature encoding and every body minting it was
//! refused. The signature was never missing: an extern generic callee is read at its resolved
//! instance. The guard stood in for a call-site defect (a value-for-pointer carrier passing `P`
//! where `&P` was due), which is now closed at the call site (`ref_arg_pointee_may_be_pointer`),
//! so the parameter is signed `ptr` and the derived bodies splice against a real parameter list.
//! Under `strict` every body in this file must lower and none may be refused at crate
//! assembly; an error anywhere is a regression.
//!
//! History (2026-09-19): strict could not SEE the per-body refusal until `FinalizeSummary`
//! grew its `refused_bodies` channel; before that this file compiled at exit 0 over a refused
//! body. See `reports/2026-09-14-rust-abi-vararg-producer-half.md`.
//!
//! Trust (wave-DPE): a tuple match whose elements are `&Enum` references
//! matched THROUGH the reference — `#[derive(PartialEq)]`'s
//! `match (self, other) { (E::A(a), E::A(b)) => *a == *b, .. }` — lowers by
//! loading the enum through each element pointer, testing its tag, and
//! binding each by-ref scalar payload field as a snapshot pointer. Under
//! `strict`: the derived `eq` bodies must lower, and so must the explicit
//! form below.

#[derive(PartialEq, Clone, Copy)]
pub enum E {
    A(u32),
    B(u8, u8),
    C,
}

fn same_a(x: &E, y: &E) -> bool {
    match (x, y) {
        (E::A(a), E::A(b)) => *a == *b,
        (E::B(p, _), E::B(q, _)) => *p == *q,
        _ => false,
    }
}

fn main() {
    if !(E::A(1) == E::A(1)) || E::A(1) == E::A(2) || E::B(1, 2) == E::C {
        std::process::exit(1);
    }
    if !same_a(&E::A(7), &E::A(7)) || same_a(&E::B(1, 2), &E::A(1)) {
        std::process::exit(2);
    }
}
