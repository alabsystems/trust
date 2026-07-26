//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ build-pass
//! Regression for the trust-thir-lower "seal_with cannot seal the same block
//! twice" ICE (found compiling memchr 2.7.6's `memmem::Searcher::new`): an
//! explicit `return` of a value `if`/`else` whose arms BOTH fail closed —
//! here each arm constructs a struct wrapping a union literal, an unsupported
//! lowering shape — used to double-seal. `capture_arm` seals each no-value arm
//! `Unreachable` (Diverged), `lower_if_value` step 7 then returns `None` with
//! the cursor already sealed, and the `ExprKind::Return` arm sealed again
//! without checking. The fix mirrors `lower_fn`'s `!self.sealed` tail guard:
//! a `return` reached with a sealed cursor is unreachable — skip the seal.
//! The function still compiles (the trust lowering fails closed and skips
//! verification for it); it must never ICE.

pub union U {
    b: u8,
}

pub struct S(U);

pub fn f(c: bool) -> S {
    return if c { S(U { b: 0 }) } else { S(U { b: 1 }) };
}

fn main() {
    let _ = f(true);
}
