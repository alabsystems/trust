//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! callarg-unit: an OPAQUE-LANE enum payload binding must not reach a SIGNED EXTERN
//! call edge as the unit carrier.
//!
//! `E::S(&[u8])` declines first-class registration (`enum_variant_field_admissible`
//! admits `FatPtr(Str)` only, not `FatPtr(Slice(_))`; the decline census reads
//! `field:FatPtr(Slice(TyId(0)))+&[u8]`), so the `match` takes
//! `lower_enum_match_opaque`, which binds `v` to `Const { ty: Unit, PhantomData }`.
//! The receiver of `<[u8] as ToOwned>::to_owned` is that carrier, and the callee's
//! declaration is signed from rustc's `fn_sig` as `(fatptr<slice u8>) -> struct`.
//!
//! MEASURED 2026-09-22 on trustc 3e7b7b15ba (before the fix), this file warned:
//!   trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [CallArgTypeMismatch] in `g`: CallArgTypeMismatch { block: 1,
//!   callee: "std::slice::<impl std::borrow::ToOwned for [T]>::to_owned",
//!   arg_index: 0, expected: "fatptr<slice ty.0>", actual: "()", .. }
//! which is the ay-test-support `symlink_target_stays_within_snapshot::{closure#1}`
//! shape (`Component::Normal(value) => value.to_owned()`, `&OsStr` =
//! `FatPtr(ContainerLen)`) reduced to a std-only enum.
//!
//! After the fix `lower_call_args` refuses the arg at its typed sink
//! (`Call(opaque carrier typed argument)`), the body is a coverage skip, and the crate
//! module validates: no spanless WARN, so no annotation is expected here (the
//! `dont-require-annotations: WARN` waiver is deliberately ABSENT).

pub enum E<'a> {
    S(&'a [u8]),
    N,
}

pub fn g(c: E<'_>) -> Option<Vec<u8>> {
    match c {
        E::S(v) => Some(v.to_owned()),
        E::N => None,
    }
}

// The `&OsStr` original. `Component` declines too (census: first on
// `Prefix(PrefixComponent)`, a struct payload it cannot register; `Normal(&OsStr)` is
// `FatPtr(ContainerLen)`, inadmissible as well), same opaque lane, same carrier:
// measured `expected: "fatptr<container_len>", actual: "()"` on its own.
pub fn h(c: std::path::Component<'_>) -> Option<std::ffi::OsString> {
    match c {
        std::path::Component::Normal(value) => Some(value.to_owned()),
        _ => None,
    }
}
