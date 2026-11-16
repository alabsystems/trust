//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-dump=spec-clean:{{build-base}}/trust_spec_emit_citation.spec
//@ check-pass
//@ dont-require-annotations: NOTE
//! Trust (v6/D1): the `targo trust spec --emit clean` session artifact, driven
//! through the typed `-Ztrust-dump=spec-clean:` sink on a direct trustc
//! invocation. Same E6+E9 flagship shape as
//! `e9_definitional_call_discharge.rs`: the cited theorem kernel-discharges
//! the ensures clause, so the discharge lane's grade call runs — and with the
//! sink requested, the compiler must (a) write one `row:"goal"` JSONL line
//! whose `goal_clean` is the kernel Display of the exact goal the grade call
//! elaborated, with `verdict:"certified"`, and (b) seal the file with a
//! `row:"session"` line whose `goals` count matches, at the end of the
//! enabled whole-crate walk. The build still passes: emission is
//! disclosure-only and can never change a verdict.
//!
//! (Byte-identity of `goal_clean` with the graded goal is pinned at crate
//! level in `crates/trust-certify/tests/spec_emit_goal_render_identity.rs`;
//! this fixture pins that the sink is accepted and the discharge lane still
//! passes with emission on.)

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

pub fn ident(x: u64) -> u64 { x }

pub fn caller(x: u64) -> u64 ensures ident(x) >= ident(x) by u64_ge_refl { x }

fn main() {}
