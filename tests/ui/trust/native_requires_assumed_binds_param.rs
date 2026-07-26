//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ build-pass
//! Trust #14 positive: a native first-class `requires` clause binds its
//! parameter at the DEFAULT `-Cdebuginfo` (where the verification body's
//! `var_debug_info` is empty) and is ASSUMED for body verification, so the
//! overflow it guards is discharged — the report shows `1 proved` (the
//! arithmetic-safety obligation). Before the signature-name recovery this
//! clause dropped with "predicate references `x`, which is not a parameter"
//! and the report showed `0 proved`. Nonfatal `-Ztrust-policy=advisory` isolates this
//! from the separate whole-function-harness authority gap (the `1 unknown`).
//! The soundness twin — that a body local shadowing `x` does NOT inherit the
//! assumption — is `native_requires_shadow_not_assumed.rs`.

fn add_one(x: u64) -> u64
    //~^ NOTE Trust verification: 2 proved
    requires x < 10
{
    x + 1
}

fn main() {
    let _ = add_one(3);
}
