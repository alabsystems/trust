//! trust-types: the PANIC-FREEDOM-ONLY intrinsic stamp (std-call-summaries P2, lever L1).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! # Why a second intrinsic stamp exists
//!
//! [`crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX`] (`@trust-rustc-intrinsic::`) means
//! more than "cannot panic": the facet gates (`trust-vcgen`'s `facets.rs`,
//! `trust-types`' `facet_inference.rs`) read a callee carrying it as pure, total,
//! DETERMINISTIC and panic-free. Two families of real `core` intrinsics are
//! panic-free and yet fail that reading, so the deterministic stamp withholds them
//! on purpose (`pure_total_intrinsic_marker_allowed` in trust-mir-extract):
//!
//! * the transcendentals (`sinf64`, `powif64`, `expf32`, …): `library/std/src/num/
//!   f64.rs` documents their precision as "non-deterministic. This means it varies
//!   by platform, Rust version, and can even differ within the same execution from
//!   one invocation to the next";
//! * the `nsz` selections (`minimum_number_nsz_f64`, `maximum_number_nsz_f32`, …),
//!   whose own doc comment says "If the inputs compare equal (such as for the case
//!   of `+0.0` and `-0.0`), either input may be returned non-deterministically".
//!   They also carry a FALLBACK BODY (they are not `must_be_overridden`), as do the
//!   IEEE `minimum*`/`maximum*` selections.
//!
//! Before this stamp every one of them took the bridge's absent-callee arm
//! (`Assert(false)` plus one undischargeable `[trust-absent-callee-assumption]`
//! row), and the bridge's `is_total_rustc_intrinsic` listed them as total under
//! the deterministic prefix the extractor never stamps them with: dead names in a
//! counted TCB list. This stamp is the panic-freedom-only home for them, in a
//! namespace the facet and determinism gates NEVER read (`facets.rs` and
//! `facet_inference.rs` test `starts_with(TRUST_RUSTC_INTRINSIC_PATH_PREFIX)`, and
//! `@trust-rustc-panic-free-intrinsic::` does not start with it).
//!
//! # What the stamp means
//!
//! Minted ONLY by `trust_mir_extract::convert::tcx_marked_panic_free_intrinsic_path`
//! when ALL of the following hold, each read from `TyCtxt`:
//!
//! 1. `TyCtxt::intrinsic` authenticates the direct `FnDef` as a genuine
//!    `#[rustc_intrinsic]` item, defined in the compiler's OWN `core` (name and
//!    sysroot artifact residency);
//! 2. its intrinsic name is an exact entry of [`PANIC_FREE_RUSTC_INTRINSICS`] (never
//!    a prefix or suffix rule), and the entry's declared body shape agrees with the
//!    item's `must_be_overridden` fact (a `core` change that gives a listed
//!    intrinsic a fallback body, or removes one, fails closed);
//! 3. the item carries `#[rustc_nounwind]` (`CodegenFnAttrFlags::NEVER_UNWIND`) and
//!    a SAFE signature;
//! 4. a fallback-bodied entry's fallback body is PINNED panic-free: its optimized
//!    MIR, and that of every function it calls (non-generic, non-trait,
//!    non-intrinsic, safe `core` functions, to a fixed depth), ends every block in
//!    a terminator that cannot panic. For a fallback-bodied intrinsic the backend
//!    may run EITHER its own lowering or the fallback body, so both must be
//!    panic-free; the nounwind fact is the backend half.
//!
//! The bridge then lowers the call with no panic row and a FRESH, unconstrained
//! destination (`FreshSymbolicHavoc`): PANIC-FREEDOM ONLY, never a value fact. In
//! particular nothing is exported for the `nsz` pair, whose sign of zero is
//! nondeterministic. Authority: Trusted (docs/TCB.md), never Certified.
//!
//! As with the other `@trust-rustc-…` markers, `@` cannot occur in a Rust
//! identifier, so authored source cannot spell the namespace; a serialized
//! artifact's authority still comes from the authenticated compiler transport.

/// Prefix stamped onto a direct call path only after rustc's `TyCtxt` confirms the
/// callee is one of [`PANIC_FREE_RUSTC_INTRINSICS`] under the module-level gates.
///
/// Deliberately DISTINCT from [`crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX`] and not
/// an extension of it: no `starts_with` test on the deterministic prefix accepts
/// this one, which is what keeps the facet and determinism gates from reading it.
pub const TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX: &str =
    "@trust-rustc-panic-free-intrinsic::";

/// The operand shape of a panic-free float intrinsic, read by the bridge's call
/// prelude (arity and carrier types). Every listed intrinsic returns the float of
/// the entry's width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicFreeIntrinsicShape {
    /// `fn(x: fW) -> fW`.
    Unary,
    /// `fn(x: fW, y: fW) -> fW`.
    Binary,
    /// `fn(a: fW, x: i32) -> fW` — the `powi` family.
    PowI,
}

impl PanicFreeIntrinsicShape {
    /// Number of call operands.
    #[must_use]
    pub fn arity(self) -> usize {
        match self {
            Self::Unary => 1,
            Self::Binary | Self::PowI => 2,
        }
    }
}

/// One admitted intrinsic: exact `core::intrinsics` item name, float width, operand
/// shape, and whether `core` declares it WITH a fallback body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PanicFreeIntrinsicEntry {
    pub name: &'static str,
    pub width: u32,
    pub shape: PanicFreeIntrinsicShape,
    /// `true` iff `core` gives the intrinsic a fallback body (it is NOT
    /// `must_be_overridden`). The extractor requires this to agree with the item's
    /// own `IntrinsicDef::must_be_overridden` and then pins the fallback body.
    pub fallback_bodied: bool,
}

const fn entry(
    name: &'static str,
    width: u32,
    shape: PanicFreeIntrinsicShape,
    fallback_bodied: bool,
) -> PanicFreeIntrinsicEntry {
    PanicFreeIntrinsicEntry { name, width, shape, fallback_bodied }
}

use PanicFreeIntrinsicShape::{Binary, PowI, Unary};

/// THE COUNTED LIST (docs/TCB.md, generated by `tools/gen_tcb_std_lists.py`).
///
/// Every entry is a `#[rustc_intrinsic] #[rustc_nounwind]` SAFE item of this tree's
/// `library/core/src/intrinsics/mod.rs`, transcribed with its width and whether it
/// has a fallback body. Each was listed by the bridge's `is_total_rustc_intrinsic`
/// under the deterministic prefix the extractor never stamped it with (a dead TCB
/// name); this list is where those names now live, under the panic-freedom-only
/// meaning. Widths are spelled out per entry, never derived by a suffix rule, for
/// the reason `pure_total_intrinsic_marker_allowed` gives: a suffix rule is how a
/// new sibling gets admitted unread.
pub const PANIC_FREE_RUSTC_INTRINSICS: &[PanicFreeIntrinsicEntry] = &[
    // Nondeterministic transcendentals (precision varies by platform and call).
    // Upstream 1.101: ONE generic item per family (`sin<T: FloatPrimitive>`),
    // declared by `intrinsic_dispatch_on_type!` WITH a fallback body that
    // dispatches per width into the `libm` crate. The entries record that
    // fact; the mint's fallback pin then declines them (a trait dispatch into
    // a non-`core` crate is outside its rules), so these names are currently
    // admitted by NO stamp — recorded capability loss, fail-closed (see
    // docs/DECISION_QUEUE.md, 1.101 migration).
    entry("sinf16", 16, Unary, true),
    entry("sinf32", 32, Unary, true),
    entry("sinf64", 64, Unary, true),
    entry("sinf128", 128, Unary, true),
    entry("cosf16", 16, Unary, true),
    entry("cosf32", 32, Unary, true),
    entry("cosf64", 64, Unary, true),
    entry("cosf128", 128, Unary, true),
    entry("expf16", 16, Unary, true),
    entry("expf32", 32, Unary, true),
    entry("expf64", 64, Unary, true),
    entry("expf128", 128, Unary, true),
    entry("exp2f16", 16, Unary, true),
    entry("exp2f32", 32, Unary, true),
    entry("exp2f64", 64, Unary, true),
    entry("exp2f128", 128, Unary, true),
    entry("logf16", 16, Unary, true),
    entry("logf32", 32, Unary, true),
    entry("logf64", 64, Unary, true),
    entry("logf128", 128, Unary, true),
    entry("log2f16", 16, Unary, true),
    entry("log2f32", 32, Unary, true),
    entry("log2f64", 64, Unary, true),
    entry("log2f128", 128, Unary, true),
    entry("log10f16", 16, Unary, true),
    entry("log10f32", 32, Unary, true),
    entry("log10f64", 64, Unary, true),
    entry("log10f128", 128, Unary, true),
    // Upstream 1.101: `powf` and `powi` are ONE generic item each
    // (`powf<T: FloatPrimitive>`, `powi<T: FloatPrimitive>`), declared by
    // `intrinsic_dispatch_on_type!` WITH a fallback body dispatching into
    // the `libm` crate. The mint's pin declines them for the same reason
    // as the transcendentals, so no entry in this list is body-less.
    entry("powf16", 16, Binary, true),
    entry("powf32", 32, Binary, true),
    entry("powf64", 64, Binary, true),
    entry("powf128", 128, Binary, true),
    entry("powif16", 16, PowI, true),
    entry("powif32", 32, PowI, true),
    entry("powif64", 64, PowI, true),
    entry("powif128", 128, PowI, true),
    // `nsz` selections: either signed zero may be returned (nondeterministic).
    // Fallback-bodied.
    entry("minimum_number_nsz_f16", 16, Binary, true),
    entry("minimum_number_nsz_f32", 32, Binary, true),
    entry("minimum_number_nsz_f64", 64, Binary, true),
    entry("minimum_number_nsz_f128", 128, Binary, true),
    entry("maximum_number_nsz_f16", 16, Binary, true),
    entry("maximum_number_nsz_f32", 32, Binary, true),
    entry("maximum_number_nsz_f64", 64, Binary, true),
    entry("maximum_number_nsz_f128", 128, Binary, true),
    // IEEE 754-2019 minimum/maximum: deterministic, but fallback-bodied, so the
    // deterministic stamp (which requires `must_be_overridden`) never admits them.
    entry("minimumf16", 16, Binary, true),
    entry("minimumf32", 32, Binary, true),
    entry("minimumf64", 64, Binary, true),
    entry("minimumf128", 128, Binary, true),
    entry("maximumf16", 16, Binary, true),
    entry("maximumf32", 32, Binary, true),
    entry("maximumf64", 64, Binary, true),
    entry("maximumf128", 128, Binary, true),
];

/// The `core::intrinsics` module path every admitted entry is rendered under.
const CORE_INTRINSICS_PATH: &str = "core::intrinsics::";

/// The admitted entry for an exact intrinsic NAME, for the extractor's mint.
#[must_use]
pub fn panic_free_intrinsic_entry(name: &str) -> Option<PanicFreeIntrinsicEntry> {
    PANIC_FREE_RUSTC_INTRINSICS.iter().copied().find(|entry| entry.name == name)
}

/// The admitted entry for a GENERIC intrinsic item (upstream 1.101 made the
/// transcendental families `sin`/`cos`/`exp`/`exp2`/`log`/`log2`/`log10`
/// and the power families `powf`/`powi` generic over `FloatPrimitive`,
/// replacing the per-width items).
///
/// Admission is still exact-entry only: the candidate per-width name is
/// constructed and must be an exact [`PANIC_FREE_RUSTC_INTRINSICS`] entry —
/// the same counted list, read the same way. Two spellings occur in `core`:
/// `sin` + `f64` (`sinf64`, also `powif64`) and `powf` + `64` (`powf64`);
/// both candidates are tried and only an exact entry admits. The stamped
/// grammar keeps the per-width entry name, so every consumer classifies as
/// before; only the mint's name gate learns that `core` now spells the
/// item generically.
#[must_use]
pub fn panic_free_intrinsic_entry_for_generic(
    base_name: &str,
    width: u32,
) -> Option<PanicFreeIntrinsicEntry> {
    let (f_suffix, plain_suffix) = match width {
        16 => ("f16", "16"),
        32 => ("f32", "32"),
        64 => ("f64", "64"),
        128 => ("f128", "128"),
        _ => return None,
    };
    PANIC_FREE_RUSTC_INTRINSICS
        .iter()
        .copied()
        .find(|entry| entry.width == width && entry.name.strip_prefix(base_name) == Some(f_suffix))
        .or_else(|| {
            PANIC_FREE_RUSTC_INTRINSICS.iter().copied().find(|entry| {
                entry.width == width && entry.name.strip_prefix(base_name) == Some(plain_suffix)
            })
        })
}

/// Classify an exact compiler-stamped panic-free intrinsic call path.
///
/// The ONLY accepted spelling is `@trust-rustc-panic-free-intrinsic::core::
/// intrinsics::<name>` with `<name>` an exact [`PANIC_FREE_RUSTC_INTRINSICS`]
/// entry. Every listed intrinsic is non-generic, so a turbofish, an extra segment,
/// another module (`std::intrinsics`, `core::intrinsics::simd`), the deterministic
/// prefix, and an unprefixed path all decline. Classification is strict even
/// though only the compiler can mint the prefix: the mint and every consumer share
/// this one grammar.
#[must_use]
pub fn classify_panic_free_intrinsic(callee: &str) -> Option<PanicFreeIntrinsicEntry> {
    let path = callee.strip_prefix(TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX)?;
    let name = path.strip_prefix(CORE_INTRINSICS_PATH)?;
    if name.contains(':') || name.contains('<') {
        return None;
    }
    panic_free_intrinsic_entry(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifier_accepts_exactly_the_stamped_core_path() {
        let ok = classify_panic_free_intrinsic(
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::maximum_number_nsz_f64",
        )
        .expect("stamped nsz max");
        assert_eq!(ok, entry("maximum_number_nsz_f64", 64, Binary, true));
        assert_eq!(
            classify_panic_free_intrinsic(
                "@trust-rustc-panic-free-intrinsic::core::intrinsics::powif64"
            )
            .map(|e| (e.width, e.shape, e.fallback_bodied)),
            Some((64, PowI, true))
        );
        // The generic-item gate resolves both `core` spellings to the same
        // exact entries, and nothing else.
        assert_eq!(
            panic_free_intrinsic_entry_for_generic("sin", 64).map(|e| e.name),
            Some("sinf64")
        );
        assert_eq!(
            panic_free_intrinsic_entry_for_generic("powi", 64).map(|e| e.name),
            Some("powif64")
        );
        assert_eq!(
            panic_free_intrinsic_entry_for_generic("powf", 64).map(|e| e.name),
            Some("powf64")
        );
        assert_eq!(panic_free_intrinsic_entry_for_generic("sqrt", 64), None);
        assert_eq!(panic_free_intrinsic_entry_for_generic("powf", 8), None);
        for bad in [
            // Unstamped and wrongly stamped spellings.
            "core::intrinsics::powif64",
            "@trust-rustc-intrinsic::core::intrinsics::powif64",
            "@trust-rustc-panic-free-intrinsic::powif64",
            // Another module, an extra segment, a turbofish.
            "@trust-rustc-panic-free-intrinsic::std::intrinsics::powif64",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::simd::powif64",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::powif64::<f64>",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::powif64::x",
            // A local lookalike path and unlisted siblings.
            "@trust-rustc-panic-free-intrinsic::mycrate::intrinsics::powif64",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::fmuladdf64",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::powif64x",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::",
            "@trust-rustc-panic-free-intrinsic::core::intrinsics::sqrtf64",
        ] {
            assert_eq!(classify_panic_free_intrinsic(bad), None, "{bad}");
        }
    }

    #[test]
    fn the_prefix_is_not_read_by_the_deterministic_prefix_test() {
        // The facet gates admit a callee by
        // `starts_with(TRUST_RUSTC_INTRINSIC_PATH_PREFIX)`; that must never accept
        // this namespace.
        let stamped = format!(
            "{TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX}core::intrinsics::maximum_number_nsz_f64"
        );
        assert!(!stamped.starts_with(crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX));
        assert!(
            !crate::TRUST_RUSTC_INTRINSIC_PATH_PREFIX
                .starts_with(TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX)
        );
    }

    #[test]
    fn the_list_is_exact_and_widths_match_the_names() {
        let mut seen = std::collections::BTreeSet::new();
        for e in PANIC_FREE_RUSTC_INTRINSICS {
            assert!(seen.insert(e.name), "duplicate entry {}", e.name);
            assert!(
                e.name.ends_with(&format!("f{}", e.width))
                    || e.name.ends_with(&format!("_f{}", e.width)),
                "width {} does not match {}",
                e.width,
                e.name
            );
            // Upstream 1.101 facts: NO entry is body-less. The min/max
            // selections always had fallback bodies; 1.101 gave one to every
            // transcendental and to `powf`/`powi` (the generic
            // `intrinsic_dispatch_on_type!` dispatch body into `libm`).
            assert!(e.fallback_bodied, "{}", e.name);
            assert_eq!(e.shape == PowI, e.name.starts_with("powi"));
        }
        // The deterministic stamp's exact operations must never be listed here:
        // listing one would silently move it off the facet gates' marker.
        for deterministic in ["fabs", "sqrtf64", "fmaf64", "floorf64", "copysignf64", "ctpop"] {
            assert!(panic_free_intrinsic_entry(deterministic).is_none(), "{deterministic}");
        }
    }
}
