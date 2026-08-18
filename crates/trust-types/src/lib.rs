//! trust-types: Verification IR for the Trust compiler
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow unused crate deps when compiled in compiler context
// (serde_json used by downstream, thiserror reserved for error types)
// Trust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// Trust: `?` that propagates FAIL-CLOSED (see `discharge`) needs the custom-`Try`
// feature. This is the mechanistic kernel that turns the soundness-bug class —
// "an unmodeled construct silently defaults to PROVED" — into a structural
// impossibility: a dropped/`?`'d obligation can no longer mean "safe".
//
// Gated behind the default-on `try-sugar` feature so the nightly requirement is
// opt-out: stable-only consumers depend with `default-features = false` and keep
// the full `Discharge` API minus the `?` operator (see `discharge`).
#![cfg_attr(feature = "try-sugar", feature(try_trait_v2, try_trait_v2_residual))]
// dead_code audit: crate-level suppression removed

// Deterministic hash collections for compilation reproducibility.
pub mod fx;

/// Prefix stamped onto a direct call path only after rustc's `TyCtxt` confirms
/// that the callee is one of Trust's modeled compiler intrinsics.
///
/// `@` cannot occur in a Rust identifier, so authored source cannot manufacture
/// this namespace merely by declaring a lookalike `intrinsics::ctpop` function.
/// Consumers must still validate the exact intrinsic name and call shape after
/// removing the prefix. The marker prevents source-spellable DefPath collisions
/// during compiler extraction, but is forgeable in hand-edited serialized IR;
/// artifact authority still comes from the authenticated compiler transport and
/// session that produced the IR.
pub const TRUST_RUSTC_INTRINSIC_PATH_PREFIX: &str = "@trust-rustc-intrinsic::";

/// Prefix stamped onto a direct call path only after rustc's `TyCtxt` confirms
/// that the callee is one of Trust's modeled total primitive methods.
///
/// This namespace is intentionally distinct from
/// [`TRUST_RUSTC_INTRINSIC_PATH_PREFIX`]: `wrapping_add`/`wrapping_sub`/
/// `wrapping_mul` are `core` library methods, not rustc intrinsics. As with the
/// intrinsic marker, `@` makes the prefix impossible to author as a Rust
/// identifier, while artifact authority still comes from the authenticated
/// compiler transport/session rather than from a serialized string alone.
pub const TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX: &str =
    "@trust-rustc-total-primitive-method::";

/// Prefix stamped onto an integer wrapping call whose exact `core` method
/// identity is needed only by the full-mode assertion-refutation model.
///
/// This is deliberately separate from
/// [`TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX`]. The E6 import lane admits
/// only unsigned `u8`/`u16`/`u32`/`u64` add/sub/mul, while the refutation-only
/// model also understands signed and pointer-sized add/sub. A refutation model
/// must not recover that broader identity from a source-spellable method suffix:
/// otherwise a user function merely named `wrapping_add` could be modeled as
/// modular arithmetic and manufacture a false counterexample.
pub const TRUST_RUSTC_WRAPPING_REFUTATION_METHOD_PATH_PREFIX: &str =
    "@trust-rustc-wrapping-refutation-method::";

/// Prefix stamped onto a def path whose CRATE NAME is not a usable identity.
///
/// Two INDEPENDENT producer rules mint it, and both mean the same thing to every
/// consumer — *the root segment of this path is not evidence of anything*:
///
///  1. **DUPLICATE NAME.** Two loaded crates render the same name, so the name
///     cannot pick one of them (`trust_mir_extract::convert::
///     disambiguate_direct_call_path`). This rule fires on ANY name, sysroot or
///     not, and is about UNIQUENESS.
///  2. **SYSROOT IMPERSONATION.** The defining crate's name is `core`/`alloc`/
///     `std` but its `StableCrateId` is not one of the compiler's real sysroot
///     crates (`trust_mir_extract::convert::impersonates_sysroot_crate`, whose
///     sysroot identity comes from compiler-owned lang/diagnostic-item anchors,
///     never from a name). This rule is about IDENTITY.
///
/// # RULE 1 DOES NOT IMPLY RULE 2 — a corrected claim, MEASURED 2026-08-17
///
/// A previous revision of this comment asserted that an impersonator is ALWAYS
/// caught by rule 1, "because the real `core`/`alloc` arrive via `std`". That is
/// FALSE, and the counterexample compiles:
///
/// ```text
/// // aux, built `--crate-name std`, exposing an ENDLESS `std::vec::Vec::<T>::iter`
/// // consumer:
/// #![no_std]
/// extern crate alloc;   // real alloc — but NOT real std
/// extern crate std;     // the impersonator, the only `std` in the graph
/// pub fn boom(v: &std::vec::Vec<u8>) -> alloc::vec::Vec<u8> { v.iter().collect() }
/// ```
///
/// In a `#![no_std]` graph the real `std` is never injected, so the impersonator
/// is the ONLY crate named `std`, rule 1 does not fire, and the callee was
/// emitted UNSTAMPED as `std::vec::Vec::<u8>::iter`. Measured on
/// `stage2/bin/trustc` at `0a3cd0152`: **exit 0, zero diagnostics**, versus exit
/// 1 with two errors for byte-identical aux bytes named `mycrate`. Rule 2 exists
/// because of that measurement; see fixture
/// `trust-vcgen/fixtures/no-std-sysroot-impersonation-2026-08-17`.
///
/// `@` cannot occur in a Rust identifier, so the stamped namespace is
/// unspellable from source.
///
/// WHAT THE STAMP DOES AND DOES NOT GUARANTEE. It is a PRODUCER-side fact about
/// a string. It makes a fail-closed check possible; it is not a check. Nothing
/// in the pipeline refuses a stamped path unless the reader asks. Consequences,
/// each of which cost an obligation when it was missed:
///
///  * a matcher that tests `callee.contains("alloc::vec::")` matches the stamped
///    spelling `__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter`,
///    because a substring test cannot tell a root from a suffix; and
///  * rule 2 is applied to CALLEE def paths AND to the `Ty::Adt`/`Ty::Datatype`/
///    `AggregateKind::Adt` NAMES the extractor renders, because the iterator in
///    the exploit above is authenticated purely by its printed type root
///    (`Ty::Adt { name: "std::vec::Endless" }`). Rule 1 is still callee-only.
///    A type-name test is therefore not a substitute for a callee-path test, nor
///    the reverse — see `trust_vcgen::generate::alloc_vcs`, which needs BOTH.
pub const TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX: &str = "__trust_crate@";

/// The crate names whose ROOT segment any consumer is allowed to read as
/// evidence of sysroot provenance. Exactly the three the pipeline's `core::`/
/// `alloc::`/`std::` root anchors accept, so the producer's impersonation rule
/// and the consumer's anchor cannot drift apart.
pub const SYSROOT_CRATE_NAMES: [&str; 3] = ["core", "alloc", "std"];

/// True when `crate_name` is spelled like a sysroot crate. A NAME test and
/// nothing more — it says only that the consumer-side root anchors
/// ([`path_root_is_authenticated_sysroot_crate`]) would accept paths rooted at
/// this crate, which is precisely why the producer must then check the crate's
/// IDENTITY.
#[must_use]
pub fn crate_name_wears_sysroot_spelling(crate_name: &str) -> bool {
    SYSROOT_CRATE_NAMES.contains(&crate_name)
}

/// THE producer-side decision: must this rendered def path carry the
/// [`TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX`] stamp?
///
/// Factored out of the extractor (which cannot be unit-tested without a full
/// compiler build) so the truth table itself is testable under stable cargo. The
/// extractor supplies the four facts; each one is read from `TyCtxt`, never from
/// a string:
///
/// * `defining_crate_is_local` — `DefId::is_local()`;
/// * `crate_name_wears_sysroot_spelling` — [`crate_name_wears_sysroot_spelling`]
///   on `tcx.crate_name(krate)`;
/// * `defining_crate_is_real_sysroot` — `trust_mir_extract::convert::
///   is_real_sysroot_crate`, i.e. the crate's `StableCrateId` equals that of a
///   crate owning one of the compiler's own lang/diagnostic-item anchors. Those
///   anchors are ATTRIBUTES: a crate that writes `#![feature(rustc_attrs)]` can
///   register one, and rustc only rejects it when the real owner is also loaded.
///   That bound is measured and named at `impersonates_sysroot_crate`; do not
///   read this predicate as saying the stamp is unforgeable;
/// * `crate_name_is_ambiguous` — some OTHER loaded crate renders the same name.
///
/// # Why `defining_crate_is_local` does not appear in the sysroot arm
///
/// The duplicate-name rule exempts the local crate because a local path is
/// unambiguous BY CONSTRUCTION (there is exactly one crate under compilation).
/// The impersonation rule must NOT take that exemption, or a crate built
/// `--crate-name std` would self-verify with sysroot grants for its own items.
/// The discriminator that keeps the REAL std from being stamped while it is
/// being built is `defining_crate_is_real_sysroot`, evaluated on the LOCAL
/// crate: `std` owns the `HashMap`/`HashSet` diagnostic items, `alloc` owns
/// `Vec` and the `owned_box` lang item, `core` owns `Option` and the `clone`
/// lang item, so each of them authenticates ITSELF while it is the local crate.
/// A crate that merely calls itself `std` owns none of them and is stamped.
/// FAIL CLOSED: if the anchors are absent the answer is "stamp", which costs
/// precision (a visible unproved obligation) and never a grant.
#[must_use]
pub fn sysroot_identity_stamp_required(
    defining_crate_is_local: bool,
    crate_name_wears_sysroot_spelling: bool,
    defining_crate_is_real_sysroot: bool,
    crate_name_is_ambiguous: bool,
) -> bool {
    let duplicate_name = !defining_crate_is_local && crate_name_is_ambiguous;
    let impersonates_sysroot =
        crate_name_wears_sysroot_spelling && !defining_crate_is_real_sysroot;
    duplicate_name || impersonates_sysroot
}

/// Apply [`sysroot_identity_stamp_required`]'s verdict to a rendered path.
///
/// IDEMPOTENT: a path that already carries the stamp at its FRONT is returned
/// unchanged, so a renderer that composes two stamping layers cannot mint
/// `__trust_crate@a::__trust_crate@b::…`.
#[must_use]
pub fn stamp_unauthenticated_crate_path(
    path: String,
    stable_crate_id: u64,
    stamp_required: bool,
) -> String {
    if !stamp_required || path.starts_with(TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX) {
        path
    } else {
        format!("{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}{stable_crate_id:016x}::{path}")
    }
}

/// True when `path` contains any [`TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX`]
/// stamp, i.e. some component of it was rendered from a crate whose name rustc
/// declined to authenticate. Such a path may never be read as `core`/`alloc`/
/// `std`.
///
/// Scans the WHOLE path, not just the front: a std-rooted spelling can carry an
/// unauthenticated component in a generic argument or in a qualified
/// `<Self as Trait>` header, and the root alone then says nothing about the part
/// the summary is really about.
#[must_use]
pub fn path_has_unauthenticated_crate_stamp(path: &str) -> bool {
    path.contains(TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX)
}

/// The ROOT segment of `path` is an AUTHENTICATED sysroot crate.
///
/// The one predicate a matcher must use before it GRANTS anything on the
/// strength of a `core`/`alloc`/`std` spelling. Two conditions, and BOTH are
/// load-bearing — either alone was measured insufficient:
///
///  * **anchored**, because `contains("alloc::vec::")` is satisfied by the
///    stamped string `__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter`
///    — a substring test cannot tell a root from a suffix, so a stamp placed at
///    the front is simply read past. This is not hypothetical: it is exactly how
///    `trust_vcgen::generate::alloc_vcs::is_std_collection_iter_producer` kept
///    granting std-collection treatment to a crate built `--crate-name alloc`
///    after the extractor had already stamped it.
///  * **unstamped anywhere**, for the reason given on
///    [`path_has_unauthenticated_crate_stamp`].
///
/// It performs no normalization: a caller holding a qualified
/// `<Self as Trait>::m` spelling must split it and authenticate the halves it
/// actually depends on (the leading `<` is not a sysroot root).
///
/// WHAT AN UNSTAMPED `core::`/`alloc::`/`std::` ROOT IS WORTH. Only as much as
/// the producer's stamping rules: this helper is the CONSUMER half of
/// [`sysroot_identity_stamp_required`], and the two must be read together. Since
/// 2026-08-17 the producer stamps on IDENTITY (rule 2 on
/// [`TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX`]), so an unstamped sysroot root
/// means "rustc resolved this to a crate carrying the sysroot's own
/// lang/diagnostic-item anchors" — no more and no less. Before that it meant only
/// "no OTHER crate of this name is loaded", which a `#![no_std]` graph makes
/// trivially true for a crate built `--crate-name std` — measured, exit 0, zero
/// diagnostics. It still does NOT mean "loaded from the compiler's sysroot": the
/// anchors are attributes, and residual R2 at
/// `trust_mir_extract::convert::impersonates_sysroot_crate` records, with the
/// measurement, exactly which adversary can still register one.
#[must_use]
pub fn path_root_is_authenticated_sysroot_crate(path: &str) -> bool {
    !path_has_unauthenticated_crate_stamp(path)
        && (path.starts_with("core::") || path.starts_with("alloc::") || path.starts_with("std::"))
}

#[cfg(test)]
mod authenticated_sysroot_root_tests {
    use super::*;

    /// FALSIFY-ONCE for the ANCHOR half. The planted violation is the matcher
    /// shape this helper exists to replace — an unanchored `contains` — run on
    /// the exact stamped spelling the extractor emitted in the measured
    /// `--crate-name alloc` run (fixture
    /// `trust-vcgen/fixtures/trusted-root-spoof-endless-iter-2026-08-16`). It
    /// matches (the stamp is read past); the helper does not.
    #[test]
    fn an_unanchored_contains_reads_past_the_stamp_and_this_helper_does_not() {
        let stamped = "__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter";
        assert!(
            stamped.contains("alloc::vec::"),
            "planted violation is gone: the unanchored substring test no longer matches \
             the stamped spelling, so this test proves nothing"
        );
        assert!(!path_root_is_authenticated_sysroot_crate(stamped));
        // Control: the genuine spelling, byte-identical to what the extractor
        // renders for the real `core::slice`, still authenticates.
        assert!(path_root_is_authenticated_sysroot_crate("core::slice::<impl [u8]>::iter"));
    }

    /// The `__trust_args@<hash>` argument fingerprint is a DIFFERENT marker and
    /// must NOT be read as an unauthenticated-crate stamp: the extractor appends
    /// it to genuine sysroot callees whenever the graph merely CONTAINS a
    /// duplicate crate name. Measured spelling, from the real dump corpus
    /// (`trust-clean/fixtures/.../extract_foldmemo` bundles).
    #[test]
    fn the_argument_fingerprint_marker_is_not_a_crate_stamp() {
        let real = "core::slice::<impl [extract_foldmemo::level::Level]>::iter\
                    ::<__trust_args@cb41af7cc8f0962be19cf147890eca17>";
        assert!(!path_has_unauthenticated_crate_stamp(real));
        assert!(path_root_is_authenticated_sysroot_crate(real));
    }

    /// FALSIFY-ONCE for the STAMP half: a genuinely `core::`-rooted spelling
    /// whose generic argument came from an unauthenticated crate is refused,
    /// while the same shape with an authenticated argument is not.
    #[test]
    fn a_stamped_component_under_an_authenticated_root_is_refused() {
        let inner = "core::slice::<impl [__trust_crate@0000000000000022::core::Evil]>::iter";
        assert!(inner.starts_with("core::"), "planted violation is gone: root no longer anchors");
        assert!(!path_root_is_authenticated_sysroot_crate(inner));
        assert!(path_root_is_authenticated_sysroot_crate(
            "core::slice::<impl [core::option::Option<u8>]>::iter"
        ));
    }

    /// A user crate's own path never authenticates, stamp or no stamp — the
    /// helper is a ROOT test, not a substring test. The third case is the
    /// crate-free forgery class this campaign is about: a user MODULE named like
    /// a std one.
    #[test]
    fn a_nested_user_module_named_like_a_sysroot_crate_never_authenticates() {
        assert!(!path_root_is_authenticated_sysroot_crate("mycrate::alloc::vec::Vec::<u8>::iter"));
        assert!(!path_root_is_authenticated_sysroot_crate("<T as mycrate::core::Iter>::iter"));
        assert!(!path_root_is_authenticated_sysroot_crate("mycrate::hash_map::Endless::iter"));
    }
}

#[cfg(test)]
mod sysroot_identity_stamp_tests {
    use super::*;

    /// Argument order is easy to transpose and the compiler cannot catch it
    /// (four `bool`s). Name the four facts once here.
    struct Facts {
        local: bool,
        sysroot_name: bool,
        real_sysroot: bool,
        ambiguous: bool,
    }

    fn required(f: Facts) -> bool {
        sysroot_identity_stamp_required(f.local, f.sysroot_name, f.real_sysroot, f.ambiguous)
    }

    /// FALSIFY-ONCE for the whole point of this round, BOTH states asserted in
    /// one test. The planted violation is the pre-2026-08-17 producer rule
    /// (uniqueness only); it is `false` on the measured `#![no_std]` exploit
    /// facts, which is exactly why that build compiled clean.
    #[test]
    fn the_no_std_impersonator_is_unique_and_therefore_missed_by_the_uniqueness_rule() {
        // MEASURED facts of `--crate-name std` consumed by a `#![no_std]` crate:
        // external, wears a sysroot name, is not a real sysroot crate, and — the
        // point — is the ONLY crate of that name in the graph.
        let exploit =
            Facts { local: false, sysroot_name: true, real_sysroot: false, ambiguous: false };

        // BEFORE: uniqueness alone. Planted violation — assert it is really
        // absent, or the AFTER assertion below proves nothing.
        let uniqueness_only = !exploit.local && exploit.ambiguous;
        assert!(
            !uniqueness_only,
            "planted violation is gone: the duplicate-name rule now fires on the no_std \
             exploit, so this test no longer witnesses the hole it exists for"
        );

        // AFTER: identity.
        assert!(required(exploit));
    }

    /// The other direction, and the one a round-1-style over-decline would break:
    /// an HONEST graph must be byte-identical. Every genuine sysroot callee is
    /// unambiguous and authenticates, so nothing is stamped.
    #[test]
    fn a_genuine_sysroot_crate_in_an_ordinary_graph_is_never_stamped() {
        for local in [false, true] {
            assert!(!required(Facts {
                local,
                sysroot_name: true,
                real_sysroot: true,
                ambiguous: false
            }));
        }
        // …and neither is an ordinary user dependency.
        assert!(!required(Facts {
            local: false,
            sysroot_name: false,
            real_sysroot: false,
            ambiguous: false
        }));
    }

    /// The real `core`/`alloc`/`std` being BUILT is the local crate and owns its
    /// own anchors, so it is not stamped — while a crate that merely calls itself
    /// `std` owns none and is stamped even for its own local items, which is what
    /// stops it self-verifying with sysroot grants. Same `local: true`, opposite
    /// verdicts: the discriminator is identity, not locality.
    #[test]
    fn the_real_std_being_built_is_not_stamped_but_a_local_impersonator_is() {
        assert!(!required(Facts {
            local: true,
            sysroot_name: true,
            real_sysroot: true,
            ambiguous: false
        }));
        assert!(required(Facts {
            local: true,
            sysroot_name: true,
            real_sysroot: false,
            ambiguous: false
        }));
    }

    /// The duplicate-name rule keeps its local exemption and keeps firing on
    /// NON-sysroot names — round 2's behavior, unchanged.
    #[test]
    fn the_duplicate_name_rule_is_preserved_exactly() {
        assert!(required(Facts {
            local: false,
            sysroot_name: false,
            real_sysroot: false,
            ambiguous: true
        }));
        assert!(!required(Facts {
            local: true,
            sysroot_name: false,
            real_sysroot: false,
            ambiguous: true
        }));
    }

    /// FAIL CLOSED when the compiler's anchors are missing (`#![no_core]`-style
    /// graphs, or std's own `cfg(test)` build, where `HashMap`'s diagnostic item
    /// is not registered): the sysroot-named crate cannot authenticate, so it is
    /// stamped. That costs precision — a visible unproved obligation — never a
    /// grant.
    #[test]
    fn a_sysroot_name_that_cannot_authenticate_fails_closed_to_stamped() {
        assert!(required(Facts {
            local: false,
            sysroot_name: true,
            real_sysroot: false,
            ambiguous: false
        }));
    }

    /// The producer has TWO entry points — the callee renderer, which applies
    /// both rules, and the type-name renderer, which applies rule 2 alone as
    /// `trust_mir_extract::convert::impersonates_sysroot_crate` (`name && !real`).
    /// Pin the equivalence over the whole 2^3 space so the two cannot drift into
    /// disagreeing about what an impersonator is — the failure mode this campaign
    /// has now hit three times is one authenticator with several producers.
    #[test]
    fn rule_two_alone_is_exactly_the_impersonation_predicate() {
        for local in [false, true] {
            for sysroot_name in [false, true] {
                for real_sysroot in [false, true] {
                    assert_eq!(
                        sysroot_identity_stamp_required(
                            local,
                            sysroot_name,
                            real_sysroot,
                            /* ambiguous */ false,
                        ),
                        sysroot_name && !real_sysroot,
                        "rule 2 drifted at local={local} name={sysroot_name} real={real_sysroot}"
                    );
                }
            }
        }
    }

    #[test]
    fn only_the_three_sysroot_roots_wear_the_spelling() {
        for name in ["core", "alloc", "std"] {
            assert!(crate_name_wears_sysroot_spelling(name));
        }
        for name in ["mycrate", "std_detect", "core2", "", "proc_macro", "test"] {
            assert!(!crate_name_wears_sysroot_spelling(name));
        }
    }

    /// The stamp text is the EXACT spelling
    /// [`path_has_unauthenticated_crate_stamp`] scans for and
    /// [`path_root_is_authenticated_sysroot_crate`] refuses, and applying it
    /// twice cannot double it.
    #[test]
    fn the_stamp_is_the_spelling_the_consumer_refuses_and_is_idempotent() {
        let raw = "std::vec::Vec::<u8>::iter".to_string();
        assert!(path_root_is_authenticated_sysroot_crate(&raw), "planted violation is gone");

        let once = stamp_unauthenticated_crate_path(raw, 0x1973_d11b_2baa_21fa, true);
        assert_eq!(once, "__trust_crate@1973d11b2baa21fa::std::vec::Vec::<u8>::iter");
        assert!(path_has_unauthenticated_crate_stamp(&once));
        assert!(!path_root_is_authenticated_sysroot_crate(&once));

        let twice = stamp_unauthenticated_crate_path(once.clone(), 0xdead_beef, true);
        assert_eq!(twice, once);

        assert_eq!(
            stamp_unauthenticated_crate_path("core::slice::iter".to_string(), 7, false),
            "core::slice::iter"
        );
    }
}

/// Callee spelling of an INDIRECT call — one whose target is a runtime code
/// address (a fn-pointer value), not a statically-known symbol.
///
/// rustc's MIR spells such a call `TerminatorKind::Call { func: Copy/Move(_p) }`,
/// so there is no `DefId` and no path to render. Extraction records the callee
/// VALUE as `args[0]` and stamps this reserved name; `args[1..]` are the call's
/// real arguments. `@` cannot occur in a Rust identifier and every real callee
/// spelling is a def path, so this name can never collide with one.
///
/// It NAMES a callee, it does not resolve one: nothing may treat it as a known
/// function, a summary key, or a totality claim. A consumer that cannot model an
/// open dispatch must fail closed on it exactly as it would on any other callee
/// whose body is absent.
pub const TRUST_INDIRECT_CALLEE_PATH: &str = "@trust-indirect-callee";

/// The element-byte-size authority token trust-mir-extract appends — as the
/// TRAILING turbofish group `::<__trust_elem_bytes@N>` — to a bulk-allocation
/// sink callee (`Vec::with_capacity` / `from_elem` / `collect`), carrying the
/// exact `tcx.layout_of` byte size of the resolved element type.
///
/// `@` cannot occur in a Rust identifier (the `__trust_args@` convention), so
/// authored source cannot manufacture the token by naming a type or type
/// parameter after it. The previous `__trust_elem_bytes_N` underscore
/// spelling WAS a legal identifier and therefore forgeable (batch-6
/// adversarial review D1): a user type or type param named
/// `__trust_elem_bytes_1` survives in the rendered path exactly when the
/// extractor omits the real token (still-generic element / layout error), and
/// the old substring parse read it as stride 1 — a false capacity ceiling.
/// [`parse_trailing_elem_bytes_token`] is the ONLY admitted grammar; producer
/// and every consumer share this one spelling so they can never drift apart.
/// As with the other `@` markers, the string is forgeable in hand-edited
/// serialized IR; artifact authority still comes from the authenticated
/// compiler transport/session that produced the IR.
pub const TRUST_ELEM_BYTES_TOKEN_PREFIX: &str = "::<__trust_elem_bytes@";

/// Render the trailing element-byte-size token for `elem_bytes`
/// (`::<__trust_elem_bytes@N>`) — the single producer spelling.
/// `trust-mir-extract` appends exactly this string, and
/// [`parse_trailing_elem_bytes_token`] round-trips it.
#[must_use]
pub fn render_trailing_elem_bytes_token(elem_bytes: u64) -> String {
    format!("{TRUST_ELEM_BYTES_TOKEN_PREFIX}{elem_bytes}>")
}

/// Parse the element-byte-size token from a callee, admitting ONLY the exact
/// trailing-position grammar the extractor emits: the callee must END with
/// `::<__trust_elem_bytes@N>`, `N` a non-empty all-ASCII-digit run.
///
/// Trailing position plus the non-identifier `@` make the token unforgeable
/// from source: a lookalike anywhere else in the path (a middle
/// `Vec::<Lookalike>` turbofish, a `{closure@…file-name…}` rendering, a
/// nested generic argument) never parses. Anything else — including the
/// retired `__trust_elem_bytes_N` underscore spelling — returns `None`, and
/// callers must fail closed (an unknown element size is NEVER assumed).
#[must_use]
pub fn parse_trailing_elem_bytes_token(callee: &str) -> Option<i128> {
    let (_, after) = callee.rsplit_once(TRUST_ELEM_BYTES_TOKEN_PREFIX)?;
    let digits = after.strip_suffix('>')?;
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

#[cfg(test)]
mod elem_bytes_token_tests {
    use super::*;

    #[test]
    fn round_trips_the_producer_spelling() {
        let callee = format!(
            "alloc::vec::Vec::<u8>::with_capacity{}",
            render_trailing_elem_bytes_token(4096)
        );
        assert_eq!(callee, "alloc::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes@4096>");
        assert_eq!(parse_trailing_elem_bytes_token(&callee), Some(4096));
    }

    #[test]
    fn user_spellable_lookalikes_never_parse() {
        // Batch-6 review D1 (probe-verified Some(1) under the old spelling):
        // `__trust_elem_bytes_1` is a LEGAL Rust identifier.
        assert_eq!(
            parse_trailing_elem_bytes_token(
                "alloc::vec::Vec::<__trust_elem_bytes_1>::with_capacity"
            ),
            None
        );
        // The retired underscore spelling is rejected even in trailing
        // position: it is identifier-spellable, hence never an authority.
        assert_eq!(
            parse_trailing_elem_bytes_token(
                "alloc::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes_1>"
            ),
            None
        );
        // An `@` lookalike OUTSIDE the trailing turbofish (e.g. smuggled via
        // a file name inside a closure rendering) never parses.
        assert_eq!(
            parse_trailing_elem_bytes_token("f::<{closure@src/__trust_elem_bytes@7.rs:1:1}>"),
            None
        );
        assert_eq!(
            parse_trailing_elem_bytes_token(
                "alloc::vec::Vec::<__trust_elem_bytes@1>::with_capacity"
            ),
            None
        );
        // Grammar strictness: empty digits, non-digits, missing closer,
        // i128 overflow — all fail closed.
        assert_eq!(parse_trailing_elem_bytes_token("v::f::<__trust_elem_bytes@>"), None);
        assert_eq!(parse_trailing_elem_bytes_token("v::f::<__trust_elem_bytes@1x>"), None);
        assert_eq!(parse_trailing_elem_bytes_token("v::f::<__trust_elem_bytes@1"), None);
        assert_eq!(
            parse_trailing_elem_bytes_token(
                "v::f::<__trust_elem_bytes@999999999999999999999999999999999999999999>"
            ),
            None
        );
    }
}

/// The integer carrier authenticated for a refutation-only wrapping method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcWrappingRefutationCarrier {
    Fixed { width: u32, signed: bool },
    PointerSized { signed: bool },
}

impl RustcWrappingRefutationCarrier {
    /// Whether the extracted operand width/sign agrees with this carrier.
    ///
    /// Pointer-sized integers are currently pinned to the 64-bit Trust target.
    /// Checking that width here is essential: signedness alone would let a
    /// forged pointer-sized marker authorize modular semantics for (for
    /// example) an unrelated `u8` call in serialized IR.
    #[must_use]
    pub fn matches(self, width: u32, signed: bool) -> bool {
        match self {
            Self::Fixed { width: expected, signed: expected_signed } => {
                width == expected && signed == expected_signed
            }
            Self::PointerSized { signed: expected_signed } => {
                width == 64 && signed == expected_signed
            }
        }
    }
}

/// The refutation-only wrapping operation authenticated by rustc.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcWrappingRefutationOp {
    Add,
    Sub,
}

/// An exact compiler-authenticated `core` integer wrapping add/sub method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RustcWrappingRefutationMethod {
    pub op: RustcWrappingRefutationOp,
    pub carrier: RustcWrappingRefutationCarrier,
}

impl RustcWrappingRefutationMethod {
    /// Classify a closed refutation-only method marker.
    ///
    /// Fixed signed/unsigned carriers through 128 bits and pointer-sized
    /// carriers have exact spellings. The downstream arithmetic model retains
    /// its own width cap and fails closed outside it.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        let path = callee.strip_prefix(TRUST_RUSTC_WRAPPING_REFUTATION_METHOD_PATH_PREFIX)?;
        let mut segments = path.split("::");
        let (Some(root), Some(module), Some(primitive_impl), Some(method)) =
            (segments.next(), segments.next(), segments.next(), segments.next())
        else {
            return None;
        };
        if segments.next().is_some() || root != "core" || module != "num" {
            return None;
        }
        let carrier = match primitive_impl {
            "<impl u8>" => RustcWrappingRefutationCarrier::Fixed { width: 8, signed: false },
            "<impl u16>" => RustcWrappingRefutationCarrier::Fixed { width: 16, signed: false },
            "<impl u32>" => RustcWrappingRefutationCarrier::Fixed { width: 32, signed: false },
            "<impl u64>" => RustcWrappingRefutationCarrier::Fixed { width: 64, signed: false },
            "<impl u128>" => RustcWrappingRefutationCarrier::Fixed { width: 128, signed: false },
            "<impl usize>" => RustcWrappingRefutationCarrier::PointerSized { signed: false },
            "<impl i8>" => RustcWrappingRefutationCarrier::Fixed { width: 8, signed: true },
            "<impl i16>" => RustcWrappingRefutationCarrier::Fixed { width: 16, signed: true },
            "<impl i32>" => RustcWrappingRefutationCarrier::Fixed { width: 32, signed: true },
            "<impl i64>" => RustcWrappingRefutationCarrier::Fixed { width: 64, signed: true },
            "<impl i128>" => RustcWrappingRefutationCarrier::Fixed { width: 128, signed: true },
            "<impl isize>" => RustcWrappingRefutationCarrier::PointerSized { signed: true },
            _ => return None,
        };
        let op = match method {
            "wrapping_add" => RustcWrappingRefutationOp::Add,
            "wrapping_sub" => RustcWrappingRefutationOp::Sub,
            _ => return None,
        };
        Some(Self { op, carrier })
    }
}

/// A compiler-authenticated, pure-total primitive method admitted without a
/// same-unit body.
///
/// Classification is deliberately strict even though the marker itself can
/// only be minted by the compiler in an authoritative run. Keeping the grammar
/// here gives facet inference, E6 body recognition, and TrustIr lowering one
/// fail-closed source of truth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcTotalPrimitiveMethod {
    WrappingAdd(u32),
    WrappingSub(u32),
    WrappingMul(u32),
}

impl RustcTotalPrimitiveMethod {
    /// Classify an exact compiler-marked `core` primitive method path.
    ///
    /// Only the E6 machine widths are admitted. Signed integers, `u128`,
    /// `usize`, foreign roots, extra path segments, unmarked paths, and
    /// same-suffix lookalikes all decline.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        let path = callee.strip_prefix(TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX)?;
        let mut segments = path.split("::");
        let (Some(root), Some(module), Some(primitive_impl), Some(method)) =
            (segments.next(), segments.next(), segments.next(), segments.next())
        else {
            return None;
        };
        if segments.next().is_some() || root != "core" || module != "num" {
            return None;
        }
        let width = match primitive_impl {
            "<impl u8>" => 8,
            "<impl u16>" => 16,
            "<impl u32>" => 32,
            "<impl u64>" => 64,
            _ => return None,
        };
        match method {
            "wrapping_add" => Some(Self::WrappingAdd(width)),
            "wrapping_sub" => Some(Self::WrappingSub(width)),
            "wrapping_mul" => Some(Self::WrappingMul(width)),
            _ => None,
        }
    }

    #[must_use]
    pub fn width(self) -> u32 {
        match self {
            Self::WrappingAdd(width) | Self::WrappingSub(width) | Self::WrappingMul(width) => width,
        }
    }
}

#[cfg(test)]
mod rustc_total_primitive_method_tests {
    use super::*;

    #[test]
    fn wrapping_refutation_method_classifier_is_exact_and_fail_closed() {
        assert!(
            RustcWrappingRefutationCarrier::PointerSized { signed: false }.matches(64, false)
        );
        assert!(
            !RustcWrappingRefutationCarrier::PointerSized { signed: false }.matches(8, false),
            "pointer-sized identity must validate the pinned target width as well as signedness"
        );

        for (path, op, carrier) in [
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl u128>::wrapping_add",
                RustcWrappingRefutationOp::Add,
                RustcWrappingRefutationCarrier::Fixed { width: 128, signed: false },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_sub",
                RustcWrappingRefutationOp::Sub,
                RustcWrappingRefutationCarrier::Fixed { width: 32, signed: true },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_add",
                RustcWrappingRefutationOp::Add,
                RustcWrappingRefutationCarrier::PointerSized { signed: false },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl isize>::wrapping_sub",
                RustcWrappingRefutationOp::Sub,
                RustcWrappingRefutationCarrier::PointerSized { signed: true },
            ),
        ] {
            assert_eq!(
                RustcWrappingRefutationMethod::classify(path),
                Some(RustcWrappingRefutationMethod { op, carrier })
            );
        }

        for path in [
            "core::num::<impl i32>::wrapping_add",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl f32>::wrapping_add",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_mul",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_add::suffix",
            "@trust-rustc-wrapping-refutation-method::evil::num::<impl i32>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl i32>::wrapping_add",
        ] {
            assert_eq!(RustcWrappingRefutationMethod::classify(path), None, "{path}");
        }
    }

    #[test]
    fn total_primitive_method_classifier_is_exact_and_fail_closed() {
        for (path, expected) in [
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u8>::wrapping_add",
                RustcTotalPrimitiveMethod::WrappingAdd(8),
            ),
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u16>::wrapping_sub",
                RustcTotalPrimitiveMethod::WrappingSub(16),
            ),
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_mul",
                RustcTotalPrimitiveMethod::WrappingMul(32),
            ),
            (
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
                RustcTotalPrimitiveMethod::WrappingAdd(64),
            ),
        ] {
            assert_eq!(RustcTotalPrimitiveMethod::classify(path), Some(expected));
        }

        for bad in [
            "core::num::<impl u64>::wrapping_add",
            "@trust-rustc-intrinsic::core::num::<impl u64>::wrapping_add",
            "@trust-rustc-total-primitive-method::std::num::<impl u64>::wrapping_add",
            "@trust-rustc-total-primitive-method::evil::core::num::<impl u64>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl i64>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u128>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl usize>::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add_signed",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::saturating_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add::suffix",
            "@trust-rustc-total-primitive-method::core::num::wrapping_add",
            "@trust-rustc-total-primitive-method::core::num::<impl u64>",
            "@trust-rustc-total-primitive-method::",
        ] {
            assert_eq!(
                RustcTotalPrimitiveMethod::classify(bad),
                None,
                "malformed or excluded marker must decline: {bad}"
            );
        }
    }
}

/// Marks a loop contract that could not be paired to a MIR loop header.
///
/// This is a semantic signal carried inside the contract BODY, matched with
/// `starts_with` by the consumers that must not treat an unpaired contract as
/// a real obligation. It lives here because producer (trust-vcgen) and
/// consumers (trust-mir-extract, trust-vcgen::termination) are separate crates:
/// while each held its own copy, a one-character drift in either would have
/// silently reclassified unpaired contracts as ordinary ones, and nothing would
/// have failed.
pub const UNPAIRED_LOOP_CONTRACT_PREFIX: &str = "__trust_unpaired_loop_contract__:";

/// The single process-global serialization point for every in-process ay solve.
///
/// ay's direct-execution path carries shared, non-reentrant state (see
/// trust-router's `in_process_ay_backend`): concurrent solves can race and yield
/// NONDETERMINISTIC verdicts — a false-`Certified` risk. Every ay solve entry
/// point (trust-router's `InProcessAyBackend` and trust-certify's
/// `AyProofBackend`) MUST hold this lock ACROSS THE RAW SOLVE ONLY, and never
/// across pure clean-kernel reconstruction — so that the dominant clean-kernel
/// certification work runs unlocked and parallelizes across verification threads.
/// A plain (non-reentrant) `Mutex` is correct because the narrowed critical
/// sections never nest.
pub fn ay_exec_lock() -> &'static std::sync::Mutex<()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    &LOCK
}

// Fail-closed-by-construction discharge result — the mechanistic prevention for
// the false-proof class (the 2026-06-19 soundness sweep found 8 instances where an
// unmodeled construct silently defaulted to PROVED). See `discharge`.
pub mod discharge;

// String interning for Formula variable names.
mod interner;
pub use interner::{Interner, Symbol};

// pub(crate) mod for modules not accessed via trust_types::module:: paths externally.
// Items from these modules are re-exported via `pub use module::*` below where needed.
pub(crate) mod annotation;
// Bitvector theory types for fixed-width integer operations.
pub(crate) mod bitvector;
pub(crate) mod boundary;
pub mod call_graph;
// MIR atomic intrinsic detection and parsing.
mod atomic_intrinsics;
mod concurrency;
mod facts;
mod formula;
// Arena-allocated formula representation for reduced heap allocation.
pub mod formula_arena;
// formula_utils.rs removed — utilities now in formula/ submodules.
pub(crate) mod generics;
pub(crate) mod lifetime;
pub(crate) mod lifetime_analysis;
mod model;
pub(crate) mod resilience;
// sort_check.rs removed — sort checking now in formula/sort.rs.
// SMT-LIB2 pretty printer for formatted solver output.
pub mod smt_printer;
pub mod static_truth;
// Shared matchers for modeled total core/std call summaries (bridge + vcgen must agree).
pub mod admissible_body;
pub mod facet_allowlist;
pub mod facet_inference;
pub mod facet_propagation;
pub mod structural_determinism;
pub mod structural_panic_freedom;
pub mod structural_purity;
pub mod structural_termination;
pub mod total_call_summaries;
// Trust (assumption ledger): shared markers for the compiler↔bridge assumption
// demotion contract (extern print/format/write dispatch, native-lowering gaps).
pub mod assumption;
// Trust (frontend firewall): the enforcement of "an untrusted frontend proposes,
// it never asserts". Lives here for the same reason `assumption` does — it is the
// shared dependency of the frontends that produce proposals, the lanes that admit
// them, and the repair loop that writes clauses back into source.
pub mod frontend_firewall;
// Trust (T9 contract-panic): the SINGLE source of truth that classifies whether a
// non-proved obligation is a DECLARED contract panic (a conditional pass) vs a
// genuine refutation. Every gate — the two compiler abort gates, the memory-safe
// UB counter, the transport-row rewrite, and targo's partition — projects its own
// data into `tolerance::ContractPanicView` and asks this module, so the decision
// cannot drift across the readers (the `ArrayVec::push` regression was exactly
// that drift). Owns the DECISION that reads `assumption`'s marker constants.
pub mod tolerance;
// Trust (R1 corpus): depth-tolerant JSON deserialization for compiler-emitted
// recursive formula payloads (bounded big-stack fallback past serde_json's
// default 128-level recursion limit).
pub mod json_depth;
// Trust (falsification corpus, i128/u128 ICE class): wide-integer-tolerant
// canonical JSON digest material (fast path byte-identical to
// `serde_json::to_value`; out-of-JSON-range i128/u128 become tagged decimal
// strings instead of ICEing the verifier).
pub mod json_digest;
// The one implementation of "what are the bytes of this thing, and what is
// their hash". Two subsystems that hash the same object through different code
// disagree about identity the first time either one changes; the canonical-JSON
// half additionally makes the answer independent of the
// `serde_json/preserve_order` feature, which this repo enables in the root
// workspace and not in `crates/`.
pub mod digest;
// Canonical SMT-LIB2 logic selection, free variable collection, and sort inference.
pub mod smt_logic;
// Ambient per-function verification deadline — lets every synchronous
// preprocessing choke point (extraction, VC gen, spec inference) consult the
// existing per-function budget and fail closed, closing the non-termination
// hole where the cooperative deadline only covered solver dispatch.
pub mod verify_budget;
// SMT-LIB2 string-based pretty printer for debugging and external solver interop.
mod result;
// The §7 multi-axis grade record (two-language design, R-U): the lossless
// successor to the legacy AssuranceLevel ladder.
pub mod grade;
pub mod guidance;
// The single per-obligation outcome vocabulary shared by the compiler
// transport, the report DTOs, and every consumer downstream of them.
pub mod outcome;
pub(crate) mod smtlib2_printer;
pub(crate) mod spec;
pub(crate) mod spec_attrs;
mod spec_parse;
mod spec_render;
// state_machine extraction lives in trust-temporal/extract.rs.
// Types (StateMachine, StateInfo, Transition) live in model.rs.
// Dead state_machine.rs (692 lines) removed — was never in module tree.
pub(crate) mod strengthen;
pub(crate) mod taint;
pub(crate) mod trait_resolution;
pub(crate) mod traits;
// Provenance tracking types for memory model Layer 2.
pub mod provenance;
// Unified memory model for trust-wp/trust-vc cross-function proof composition.
pub mod unified_memory;
// Legacy vulnerability-pattern prototype. The production verifier has its
// own sound VC generation/analysis lanes and nothing calls this heuristic
// scanner; keep its unit tests without compiling duplicate detectors into all
// downstream Trust crates.
#[cfg(test)]
mod patterns;
// Shared utility functions consolidated from multiple crates.
pub(crate) mod utils;
// Translation validation shared types (used by trust_vcgen and trust-transval).
pub mod translation_validation;
// ay_bindings conversion bridge for direct ay integration.
#[cfg(feature = "ay-bridge")]
pub mod ay_bridge;
// trust-wp-core PureExpr conversion bridge for native trust_wp integration.
#[cfg(feature = "trust-wp-bridge")]
pub mod trust_wp_bridge;
// serde-only lowering from `trust_types::Formula` into the
// `trust_wp.trust-formula.v1` claim envelope. Always compiled (no trust_wp_core
// dependency) so the trust-wp bridge and compiler can lower symbolic
// `trust-types.Formula@1` predicates into replayable typed pure-expr claims.
pub mod trust_formula_v1;

#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;

pub use annotation::*;
pub use atomic_intrinsics::parse_atomic_intrinsic;
pub use bitvector::*;
pub use boundary::*;
pub use concurrency::*;
pub use digest::{
    canonical_json_bytes, canonical_json_sha256, canonical_json_value,
    canonicalize_json_in_place, is_canonical_json, is_stable_sha256_hex, lowercase_hex,
    stable_sha256_hex, stable_sha256_hex_parts, stable_sha256_hex_reader,
};
pub use facts::*;
pub use formula::*;
pub use generics::*;
pub use guidance::{AgenticGuidance, SuggestedFix};
pub use json_digest::canonical_digest_json_value;
pub use lifetime::*;
pub use lifetime_analysis::*;
pub use model::*;
pub use outcome::{Outcome, UnknownOutcome};
pub use resilience::*;
pub use result::*;
// Re-export canonical SMT-LIB2 utilities.
pub use smt_logic::{
    FormulaSortError, check_formula_sort, collect_free_var_decls, infer_sort, select_logic,
};
pub use smt_printer::{PrintConfig, SmtPrinter};
pub use smtlib2_printer::{
    SmtLib2Config, SmtLib2Printer, escape_smt_string, is_valid_smt_identifier, operator_to_smt,
    sort_to_smt,
};
pub use spec::*;
pub use spec_attrs::*;
pub use spec_parse::*;
pub use spec_render::*;
pub use strengthen::*;
pub use taint::*;
pub use trait_resolution::*;
pub use traits::*;
// Re-export translation validation types at crate root.
pub use translation_validation::{
    CheckKind, RefinementVc, RefinementVcToVc, SimulationRelation, TranslationCheck,
    TranslationValidationError, block_successors_list, detect_back_edges, infer_identity_relation,
};
pub use utils::{operand_place, strip_generics};
