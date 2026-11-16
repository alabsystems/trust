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
//! arithmetic-safety obligation) plus `1 assumed (requires)` (the clause
//! itself), out of 2.
//!
//! The pinned line said `2 proved` until 2026-09-16 and CONTRADICTED the
//! sentence above it, which has said `1 proved` since the file was written. The
//! prose was right: `688d2058fd` stopped the summary counting a
//! definition-entry `requires` row as proved — its own comment already said the
//! row "has no proof strength" — and the two now agree. The clause is an
//! ASSUMPTION every caller owes, and this file's whole subject is that it BINDS
//! its parameter; a row that binds is not a row that is proved. Before the signature-name recovery this
//! clause dropped with "predicate references `x`, which is not a parameter"
//! and the report showed `0 proved`. Nonfatal `-Ztrust-policy=advisory` isolates this
//! from the separate whole-function-harness authority gap (the `1 unknown`).
//! The soundness twin — that a body local shadowing `x` does NOT inherit the
//! assumption — is `native_requires_shadow_not_assumed.rs`.

fn add_one(x: u64) -> u64
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 2
    requires x < 10
{
    x + 1
}

fn main() {
    let _ = add_one(3);
}
