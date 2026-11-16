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

pub mod interior_mutability;
pub mod local_defs;
pub mod place_ty;

mod machine_remainder;
pub use machine_remainder::unsigned_literal_remainder_is_exact;

mod postcondition_integer_carriers;
pub use postcondition_integer_carriers::{
    conjoin_postcondition_integer_carriers, postcondition_integer_carrier_facts,
};

// Trust (ARGS-FINGERPRINT-READ-1, 2026-10-07): the duplicate-crate-name argument
// fingerprint `::<__trust_args@HEX>` and the one helper that reads past it.
pub mod args_fingerprint;
pub use args_fingerprint::{
    TRUST_ARGS_FINGERPRINT_HEX_LEN, TRUST_ARGS_FINGERPRINT_PREFIX,
    args_display_may_name_a_same_named_crate, render_trailing_args_fingerprint,
    strip_trailing_args_fingerprint,
};

// Trust (unsafe mint, round 7): the COMPILER-MINTED callee key. A safety
// contract is no longer selected by parsing a rendered string; the identity is
// resolved once, in the extractor, from `(TyCtxt, DefId)` — never from
// `generic_args` — and shipped as a closed vocabulary the consumer `match`es.
// See the module docs for the four rounds of scanner defects this retires.
pub mod callee_key;
pub use callee_key::{
    ALL_SYSROOT_ITEMS, CalleeKey, CalleeOwner, DivergingEntry, STD_THREAD_SPAWN_ITEMS, SelfTyHead,
    SysrootItem,
};
// std-call-summaries P2 (lever L1): the panic-freedom-only intrinsic stamp, a
// namespace the facet and determinism gates never read. See the module docs.
pub mod panic_free_intrinsic;
pub use panic_free_intrinsic::{
    PANIC_FREE_RUSTC_INTRINSICS, PanicFreeIntrinsicEntry, PanicFreeIntrinsicShape,
    TRUST_RUSTC_PANIC_FREE_INTRINSIC_PATH_PREFIX, classify_panic_free_intrinsic,
    panic_free_intrinsic_entry, panic_free_intrinsic_entry_for_generic,
};

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

/// Prefix stamped onto a direct call path only after rustc's `TyCtxt` confirms
/// that the callee is one of Trust's modeled overflow-CHECKED signed primitive
/// methods (`iN::checked_add` / `checked_sub` / `checked_mul`).
///
/// Deliberately a THIRD namespace, distinct from both
/// [`TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX`] (wrapping semantics —
/// admitting a checked method there would model `checked_add` as modular
/// arithmetic) and [`TRUST_RUSTC_INTRINSIC_PATH_PREFIX`] (these are `core`
/// library methods, not rustc intrinsics). As with the other markers, `@`
/// cannot occur in a Rust identifier, so authored source cannot manufacture
/// the namespace; artifact authority still comes from the authenticated
/// compiler transport/session rather than from a serialized string alone.
pub const TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX: &str =
    "@trust-rustc-checked-primitive-method::";

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

/// Prefix stamped onto a `<Self as ToString>::to_string` call path only after
/// rustc's `TyCtxt` confirms that the callee is the compiler's own `alloc`'s
/// `ToString::to_string` (by artifact residency — a diagnostic item alone is a
/// source attribute) and that the INSTANTIATED `Self` is one of the
/// foundational types whose `SpecToString` specialization runs no user code and
/// has no panic path.
///
/// # Why this needs a `TyCtxt` stamp and cannot be a path-text rule
///
/// `ToString` has exactly ONE impl in the whole tree — the blanket
/// `impl<T: fmt::Display + ?Sized> ToString for T` — whose `SpecToString`
/// DEFAULT body ends in
/// `.expect("a Display implementation returned an error unexpectedly")`.
/// So `<T as ToString>::to_string` PANICS for every `T` whose `Display::fmt`
/// can return `Err`, i.e. for every caller-written `Display`. Panic-freedom is
/// a property of the SPECIALIZATION chosen for `Self`, not of the trait and not
/// of the `::to_string` method tail.
///
/// A rendered-path gate cannot separate the two. `str` is NOT a keyword: it is
/// a legal generic-parameter name, and `Ty::Param("str")` prints BARE, exactly
/// like `TyKind::Str`. A previous revision of this model matched
/// `<str as ToString>::to_string` on the rendered callee and was REFUTED by
///
/// ```text
/// pub fn attack<str: fmt::Display + ?Sized>(t: &str) -> String { t.to_string() }
/// ```
///
/// whose MIR emits that byte-identical spelling while `Self` is the caller's
/// choice. The stamp below reads `TyKind` from `TyCtxt` instead, where a
/// generic parameter is `TyKind::Param` and can never be mistaken for
/// `TyKind::Str`.
///
/// As with the sibling markers, `@` cannot occur in a Rust identifier, so the
/// namespace is unspellable from source; artifact authority still comes from
/// the authenticated compiler transport/session rather than from a serialized
/// string alone, and the consumer must still re-check the method tail.
pub const TRUST_TOTAL_TO_STRING_PATH_PREFIX: &str = "@trust-total-to-string::";

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
///     `std` but this compiler did not load it out of its own target library
///     directory (`trust_mir_extract::convert::impersonates_sysroot_crate`, whose
///     sysroot identity is ARTIFACT RESIDENCY — never a name, never an attribute
///     the crate carries, and never a fact about which other crates the graph
///     contains). This rule is about IDENTITY.
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

/// Is a crate that WEARS a sysroot name one this COMPILER supplied?
///
/// The identity half of [`sysroot_identity_stamp_required`], factored here for
/// the same reason: the extractor needs a full compiler build to run a test at
/// all, so the rule itself is kept somewhere stable cargo can falsify it.
///
/// # THE INVARIANT ON THE INPUTS — read this before adding one
///
/// Neither input may be a function of WHICH CRATES THE GRAPH CONTAINS. The crate
/// graph is exactly the thing the adversary supplies, so any fact computed over
/// it is a fact the adversary can move. The two admitted inputs are:
///
/// * `loaded_from_this_compilers_sysroot` — every artifact in
///   `tcx.used_crate_source(krate)` sits directly in `sess.target_tlib_path.dir`,
///   i.e. rustc found the crate in its OWN target library directory rather than
///   wherever an `--extern` argument pointed. A fact about ONE crate's artifact
///   paths, decided by the filesystem the compiler was installed into;
/// * `invocation_is_building_the_sysroot` — a COMMAND-LINE fact of this
///   invocation (`trust_mir_extract::convert::invocation_is_building_the_sysroot`
///   reads `-Zforce-unstable-if-unmarked`), spelled by whoever runs rustc. A
///   crate that arrives through `--extern` has no channel to add a `-Z` flag to
///   the invocation that consumes it, so it sits at the same trust boundary as
///   `--sysroot`, which residency already depends on.
///
/// # WHY THE INJECTION RECORD IS NOT AN INPUT — REFUTED 2026-08-21, MEASURED
///
/// A 2026-08-21 revision of this rule read two more facts: whether rustc's own
/// std-imports injection reached the crate (`tcx.extern_crate(krate)`'s span
/// carrying `ExpnKind::AstPass(AstPass::StdImports)`), and whether any loaded
/// crate named `core`/`alloc`/`std` was resident. It authenticated on
/// `resident || (injected && !supplied)`. Both extra facts are adversary-movable
/// and the disjunct was exploitable:
///
/// * `standard_library_imports::inject` writes an `extern crate std;` and then
///   lets it RESOLVE through the ordinary `--extern` map, so `injected` says
///   which crate landed in the injection slot, not that the compiler chose it;
/// * `supplied` is computed over the crates that HAPPEN to be loaded. A forged
///   `std` declaring `#![no_core]` + `#![compiler_builtins]` suppresses
///   `inject_compiler_builtins` (`rustc_metadata/src/creader.rs`), so no real
///   sysroot crate is ever loaded and `supplied` is false.
///
/// MEASURED on `trustc 1.99.0-dev (ddb545d35 2026-08-21)`, read out of
/// `RUSTC_LOG=rustc_metadata::locator=info`: a victim compiled
/// `--crate-type lib --emit=metadata -Ztrust-verify=on --extern std=<forgery>`
/// opens exactly ONE artifact, the forgery, from the `--extern` path — nothing at
/// all from the compiler's target library directory. So `resident` is false for
/// the forgery and `supplied` is false for the whole compilation, and that rule
/// authenticates on its middle term. It does so even for a forgery carrying no
/// forged attribute, which the rule it replaced REFUSES today (measured: exit 1,
/// callee rendered `__trust_crate@e22d88b308847231::…`) — a regression, not an
/// unclosed residual. Both vectors are pinned as falsify-once tests below.
///
/// `injected = true` in that vector is the refutation's reading of
/// `standard_library_imports::inject`, not a direct measurement — and it does not
/// need to be one for THIS rule, which reads neither `injected` nor `supplied`.
/// The measured `resident = false` decides both cases on its own. That is the
/// point of the invariant above: a disjunct a dependency author can trigger is
/// not an authenticator, and the fix is to have no such disjunct rather than a
/// better-argued one.
///
/// FAIL CLOSED: no evidence means "not authenticated" (stamped ⇒ grants refused
/// ⇒ visible unproved obligations), never a grant. What that costs is named at
/// `trust_mir_extract::convert::invocation_is_building_the_sysroot`.
#[must_use]
pub fn sysroot_crate_is_compiler_authenticated(
    loaded_from_this_compilers_sysroot: bool,
    invocation_is_building_the_sysroot: bool,
) -> bool {
    loaded_from_this_compilers_sysroot || invocation_is_building_the_sysroot
}

/// The WHOLE identity rule — name gate, LOCAL arm, EXTERNAL arm — that
/// `trust_mir_extract::convert::is_real_sysroot_crate` applies.
///
/// [`sysroot_crate_is_compiler_authenticated`] above is only the EXTERNAL arm,
/// and for most of this rule's life it was the only arm anything could test: the
/// other two sit next to a `TyCtxt`, which no cargo test can build. That gap was
/// not cosmetic. Residual R2 — a crate compiled `--crate-name std` that
/// authenticated ITSELF, went unstamped, and had its own `std::vec::Endless` read
/// as genuine sysroot by every consumer that trusts a `std::` path root — lived
/// in the LOCAL arm, underneath a test whose NAME claimed the whole rule and
/// whose body called only the external arm. The local arm read
/// `local_crate_owns_a_sysroot_anchor` until 2026-08-23.
///
/// # What each arm may read, and why the local arm reads so little
///
/// * `crate_name_wears_sysroot_spelling` — a GATE, never evidence. It is what
///   holds this predicate's extension at `core`/`alloc`/`std`: a dozen consumers
///   combine it with an ITEM name alone (`Extend`, `HashMap`, `Vec`), and
///   residency by itself would start admitting `hashbrown`, which ships in the
///   compiler's own target library directory.
/// * `defining_crate_is_local` — `DefId::is_local()`. It SELECTS an arm and is
///   never itself a grant; an exemption keyed on locality is exactly the R2
///   shape, because the crate under compilation is the one the adversary wrote.
/// * `loaded_from_this_compilers_sysroot` — EXTERNAL arm only. The compiler holds
///   no `used_crate_source` record for the crate it is compiling, so this is not
///   a fact about that crate at all; the local arm therefore IGNORES it rather
///   than trusting its caller to pass `false`.
/// * `invocation_is_building_the_sysroot` — the only input the local arm reads. A
///   COMMAND-LINE fact (`-Zforce-unstable-if-unmarked`), spelled by whoever runs
///   rustc, at the same trust boundary `--sysroot` and residency already sit on.
///
/// So for the LOCAL crate the answer is exactly "is this the compilation that is
/// building the sysroot", never "does this crate look like the sysroot". FAIL
/// CLOSED in both directions: the genuine `std` built outside that lane is
/// stamped, which costs visible unproved obligations and never a grant.
///
/// # THE CONSUMER MUST DELEGATE TO THIS FUNCTION
///
/// A rule factored here and re-spelled there is a COPY, and a copy is what the
/// tests below would then be measuring — the same disease this factoring exists
/// to cure, one crate over. `the_extractor_delegates_the_whole_rule_to_this_crate`
/// reads `trust-mir-extract`'s source and refuses that drift.
#[must_use]
pub fn crate_is_the_compilers_own_sysroot_crate(
    crate_name_wears_sysroot_spelling: bool,
    defining_crate_is_local: bool,
    loaded_from_this_compilers_sysroot: bool,
    invocation_is_building_the_sysroot: bool,
) -> bool {
    if !crate_name_wears_sysroot_spelling {
        return false;
    }
    if defining_crate_is_local {
        return invocation_is_building_the_sysroot;
    }
    sysroot_crate_is_compiler_authenticated(
        loaded_from_this_compilers_sysroot,
        invocation_is_building_the_sysroot,
    )
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
///   is_real_sysroot_crate`. For an EXTERNAL crate that is
///   [`sysroot_crate_is_compiler_authenticated`]: artifact residency, or a
///   command-line declaration that this invocation is building the sysroot. For
///   the LOCAL crate — the one under compilation, about which the compiler holds
///   no loader record at all — it is still the lang/diagnostic item anchors,
///   which are ATTRIBUTES; that residual is measured and named at
///   `impersonates_sysroot_crate`, and it is the only arm where the stamp is
///   still forgeable by a crate rather than by the invoker;
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
    let impersonates_sysroot = crate_name_wears_sysroot_spelling && !defining_crate_is_real_sysroot;
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
/// [`sysroot_identity_stamp_required`], and the two must be read together. For an
/// EXTERNAL crate an unstamped sysroot root means exactly one of two things — no
/// more, and each is a fact the crate graph cannot write:
///
///  * this compiler loaded the crate's artifacts out of its own target library
///    directory; or
///  * the INVOCATION declared it is building a sysroot
///    (`-Zforce-unstable-if-unmarked`), in which case identity is delegated to
///    whoever spelled the command line, exactly as `--sysroot` already is.
///
/// Three earlier meanings, each measured insufficient. Before 2026-08-17 it meant
/// only "no OTHER crate of this name is loaded", which a `#![no_std]` graph makes
/// trivially true for a crate built `--crate-name std` — measured, exit 0, zero
/// diagnostics. Between 2026-08-17 and 2026-08-21 it meant "the crate carries one
/// of the sysroot's lang/diagnostic-item anchors", which are ATTRIBUTES a crate
/// can register for itself whenever the real owner is absent from the graph. A
/// 2026-08-21 revision then added "or rustc's std-imports injection reached it in
/// a graph containing no resident sysroot-named crate", which was REFUTED the
/// same day: a dependency can empty that graph (`#![no_core]` +
/// `#![compiler_builtins]`) and the disjunct authenticates the forgery. See
/// [`sysroot_crate_is_compiler_authenticated`] for the measurement.
///
/// The LOCAL crate has no loader record — the compiler holds none about the crate
/// it is compiling — so it authenticates from the command-line fact alone
/// (`invocation_is_building_the_sysroot`). Residual R2, which let a crate
/// self-authenticate by owning a lang/diagnostic-item anchor, is CLOSED as of
/// 2026-08-23: the anchors are source-declarable attributes read from a
/// graph-wide registry, i.e. exactly the input this rule forbids.
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
mod compiler_authenticated_sysroot_tests {
    use super::*;

    /// Six `bool`s the compiler cannot keep in order for us. Only the first three
    /// are inputs to the rule under test; the other three are the inputs of the
    /// two rules this one replaces, carried here so every fact vector can state
    /// ALL THREE verdicts instead of asserting a tautology.
    ///
    /// Every vector in this module is a crate that WEARS a sysroot name — that is
    /// the only case the rule has anything to say about — so the name gate is
    /// pinned once, separately, in
    /// `a_name_that_is_not_core_alloc_or_std_never_authenticates`.
    struct Supply {
        /// New rule, input 1: which ARM. `DefId::is_local()` — is this the crate
        /// under compilation, about which no loader record exists?
        local: bool,
        /// New rule, input 2 (EXTERNAL arm only): `used_crate_source` paths sit in
        /// the compiler's own target library directory.
        resident: bool,
        /// New rule, input 3 (both arms): a COMMAND-LINE fact — this invocation is
        /// building a sysroot, so its `core`/`alloc`/`std` legitimately arrive by
        /// `--extern` and residency cannot hold for any of them.
        building_the_sysroot: bool,
        /// 2026-08-21 (refuted) rule: rustc's std-imports injection reached it.
        injected: bool,
        /// 2026-08-21 (refuted) rule: some loaded crate named `core`/`alloc`/`std`
        /// is resident. A fact about the graph, which the adversary supplies.
        sysroot_supplied_one: bool,
        /// 2026-08-17 rule, AND the LOCAL arm until 2026-08-23: the crate owns a
        /// lang/diagnostic-item anchor. A source-declarable ATTRIBUTE.
        owns_an_anchor: bool,
    }

    fn authenticated(s: &Supply) -> bool {
        crate_is_the_compilers_own_sysroot_crate(true, s.local, s.resident, s.building_the_sysroot)
    }

    /// The 2026-08-17 rule, written out so the tests below can assert what it
    /// answered. It is ALSO, verbatim, the LOCAL arm that shipped until
    /// 2026-08-23 (`convert::local_crate_owns_a_sysroot_anchor`), which is why the
    /// local falsify-once test below plants its violation with this function.
    fn the_anchor_rule(s: &Supply) -> bool {
        s.owns_an_anchor
    }

    /// The 2026-08-21 rule, REFUTED and replaced, written out for the same
    /// reason. Its middle term is the disjunct a dependency author can trigger.
    fn the_injection_rule(s: &Supply) -> bool {
        s.resident || (s.injected && !s.sysroot_supplied_one)
    }

    /// FALSIFY-ONCE for residual R2, BOTH states in one test.
    ///
    /// The fact vector is the aux measured at `impersonates_sysroot_crate`: built
    /// `--crate-name std`, handed to a `#![no_std]` consumer as
    /// `--extern std=aux/libstd.rlib`, and carrying
    /// `#[rustc_diagnostic_item = "HashMap"]` under `#![feature(rustc_attrs)]`.
    /// The planted violation is that the ANCHOR rule accepts it — assert that
    /// first, or the refusal below witnesses nothing.
    #[test]
    fn the_attribute_forged_sysroot_is_accepted_by_the_anchor_rule_and_refused_here() {
        let forged = Supply {
            // it arrived through `--extern`, so it is an EXTERNAL crate.
            local: false,
            // `--extern` path, not the compiler's own target lib dir.
            resident: false,
            // an ordinary `cargo check` of a dependent crate sets no `-Z` flag.
            building_the_sysroot: false,
            // `#![no_std]` injects `core`, never `std`; this crate arrived via
            // the consumer's own `extern crate std;`.
            injected: false,
            // the real `core` next to it DID come from the sysroot.
            sysroot_supplied_one: true,
            // and the attribute is spellable, which is the whole of R2.
            owns_an_anchor: true,
        };
        assert!(
            the_anchor_rule(&forged),
            "planted violation is gone: the anchor rule no longer accepts the R2 forgery, \
             so this test no longer witnesses the hole it exists for"
        );
        assert!(!authenticated(&forged));
    }

    /// FALSIFY-ONCE for the refutation of the 2026-08-21 injection rule — the
    /// exploit vector, BOTH states in one test.
    ///
    /// MEASURED on `trustc 1.99.0-dev (ddb545d35 2026-08-21)`: a forged `std`
    /// declaring `#![no_core]` + `#![compiler_builtins]`, handed to an ORDINARY
    /// (non-`no_std`) victim as `--extern std=<forgery>`, is the only crate the
    /// loader reads — `RUSTC_LOG=rustc_metadata::locator=info` reports zero
    /// artifacts from the compiler's target library directory. So the graph
    /// contains no resident sysroot-named crate, `sysroot_supplied_one` is false,
    /// and the injected `extern crate std;` resolves to the forgery.
    ///
    /// That vector — `(resident=false, injected=true, supplied=false)` — is the
    /// one the replaced test asserted must AUTHENTICATE. It is the exploit. The
    /// planted violation asserted first is that the injection rule accepts it.
    #[test]
    fn the_injection_rule_authenticates_a_graph_with_no_sysroot_crate_in_it_and_this_rule_refuses_it()
     {
        let forged_graph_without_a_sysroot_crate = Supply {
            local: false,
            resident: false,
            building_the_sysroot: false,
            // the compiler's own `extern crate std;` resolved to the forgery.
            injected: true,
            // `#![compiler_builtins]` suppressed `inject_compiler_builtins`, so
            // no real sysroot crate was ever loaded. The ADVERSARY set this.
            sysroot_supplied_one: false,
            owns_an_anchor: true,
        };
        assert!(
            the_injection_rule(&forged_graph_without_a_sysroot_crate),
            "planted violation is gone: the injection rule no longer accepts the \
             empty-sysroot-graph forgery, so this test no longer witnesses the hole it \
             exists for"
        );
        assert!(!authenticated(&forged_graph_without_a_sysroot_crate));
    }

    /// FALSIFY-ONCE for the hole the injection rule OPENED, BOTH states in one
    /// test. Same forgery, carrying NO forged attribute at all.
    ///
    /// MEASURED on the same binary, same reproducer: today's anchor rule refuses
    /// it (exit 1, `__trust_crate@e22d88b308847231::<u32 as std::convert::From<u8>
    /// >::from` on the callee), and the injection rule would have authenticated
    /// it — a regression, not merely an unclosed residual. The planted violation
    /// is the pair: the anchor rule refuses AND the injection rule accepts.
    #[test]
    fn the_injection_rule_opened_the_unanchored_forgery_the_anchor_rule_already_refused() {
        let unanchored_forgery = Supply {
            local: false,
            resident: false,
            building_the_sysroot: false,
            injected: true,
            sysroot_supplied_one: false,
            // no `#[rustc_diagnostic_item]`, no `#![feature(rustc_attrs)]`.
            owns_an_anchor: false,
        };
        assert!(
            !the_anchor_rule(&unanchored_forgery),
            "planted violation is gone: the anchor rule no longer refuses the unanchored \
             forgery, so this test no longer witnesses the regression it exists for"
        );
        assert!(
            the_injection_rule(&unanchored_forgery),
            "planted violation is gone: the injection rule no longer accepts the unanchored \
             forgery, so this test no longer witnesses the regression it exists for"
        );
        assert!(!authenticated(&unanchored_forgery));
    }

    /// The other direction, and the one an over-decline would break: every
    /// honest supply configuration still authenticates.
    #[test]
    fn every_honest_supply_configuration_still_authenticates() {
        // ordinary build: sysroot `std`/`alloc`/`core`, loaded out of the
        // compiler's own target library directory.
        assert!(authenticated(&Supply {
            local: false,
            resident: true,
            building_the_sysroot: false,
            injected: true,
            sysroot_supplied_one: true,
            owns_an_anchor: true,
        }));
        // `#![no_std]` + `extern crate alloc;`: `alloc` is NOT injected (the
        // consumer names it itself) but it is the sysroot's own artifact.
        assert!(authenticated(&Supply {
            local: false,
            resident: true,
            building_the_sysroot: false,
            injected: false,
            sysroot_supplied_one: true,
            owns_an_anchor: true,
        }));
        // A sysroot-building lane, taken at its worst case for this rule: the
        // sysroot crates arrive by `--extern` and NOTHING is resident. The
        // invocation carries `-Zforce-unstable-if-unmarked` — MEASURED for
        // `cargo -Zbuild-std` (20 of its 21 rustc invocations), read from
        // `src/bootstrap` for the bootstrap lane — which the crate graph cannot
        // set. Without this case the rule silently becomes residency-only and
        // that lane over-declines.
        assert!(authenticated(&Supply {
            local: false,
            resident: false,
            building_the_sysroot: true,
            injected: true,
            sysroot_supplied_one: false,
            owns_an_anchor: true,
        }));
        // The real `core`/`alloc`/`std` while it IS the crate under compilation:
        // no loader record exists for it, and the only thing that authenticates it
        // is the same command-line fact. Without this case the local arm could be
        // hardened to a constant `false` and every other test here would stay
        // green while bootstrap's own `library/` verification lane lost its
        // sysroot grants.
        assert!(authenticated(&Supply {
            local: true,
            resident: false,
            building_the_sysroot: true,
            injected: false,
            sysroot_supplied_one: false,
            owns_an_anchor: true,
        }));
    }

    /// FAIL CLOSED: no residency and no sysroot-build lane is a refusal, whatever
    /// the graph looks like. Pinned over every combination of the three facts the
    /// rule does NOT read, which is the invariant that broke last round — and over
    /// BOTH arms, which is the invariant this test's own name claimed and its body
    /// did not deliver until 2026-08-24.
    ///
    /// Until then it called [`sysroot_crate_is_compiler_authenticated`], the
    /// EXTERNAL arm, and the LOCAL arm — where residual R2 actually lived — was
    /// unexercised in either state. Sweeping `local` is what makes the name true.
    #[test]
    fn no_fact_about_the_crate_graph_can_grant() {
        for local in [false, true] {
            for injected in [false, true] {
                for sysroot_supplied_one in [false, true] {
                    for owns_an_anchor in [false, true] {
                        let s = Supply {
                            local,
                            resident: false,
                            building_the_sysroot: false,
                            injected,
                            sysroot_supplied_one,
                            owns_an_anchor,
                        };
                        assert!(
                            !authenticated(&s),
                            "graph facts granted at local={local} injected={injected} \
                             supplied={sysroot_supplied_one} anchor={owns_an_anchor}"
                        );
                    }
                }
            }
        }
    }

    /// FALSIFY-ONCE for residual R2's LOCAL arm — the half
    /// `no_fact_about_the_crate_graph_can_grant` never reached, and the half the
    /// hole was actually in. BOTH states in one test.
    ///
    /// The fact vector is the crate under compilation in the measured `#![no_std]`
    /// forgery: built `--crate-name std`, owning `#[rustc_diagnostic_item =
    /// "HashMap"]` under `#![feature(rustc_attrs)]`, with the real `std` kept out
    /// of the graph so rustc's duplicate-registration error never fires. It is
    /// LOCAL, so there is no loader record and `resident` is not even a fact about
    /// it; and it is an ordinary `rustc`/`cargo check` invocation, so no `-Z` flag
    /// is set.
    ///
    /// THE MUTATION THIS WATCHES. Restore the pre-2026-08-23 local arm — i.e. have
    /// [`crate_is_the_compilers_own_sysroot_crate`]'s `defining_crate_is_local`
    /// branch answer from the crate's own anchors instead of from
    /// `invocation_is_building_the_sysroot`, which is `the_anchor_rule` below and
    /// was `convert::local_crate_owns_a_sysroot_anchor` in the shipped extractor.
    /// The first assertion here says that rule ACCEPTS this vector; the second
    /// says today's rule refuses it. Re-point the second assertion at
    /// `the_anchor_rule` and watch it go red — that is the exact shape of the code
    /// that shipped, and it is why `std::vec::Endless` was read as genuine sysroot.
    ///
    /// Nothing else in the tree neutralises that mutation: the local arm has no
    /// other caller under cargo (it needs a `TyCtxt`), and every other vector in
    /// this module is `local: false`, so the external arm's rows cannot answer for
    /// it.
    #[test]
    fn the_local_crate_named_std_is_accepted_by_the_pre_patch_local_rule_and_refused_here() {
        let self_named_std = Supply {
            // the crate under compilation — `DefId::is_local()`.
            local: true,
            // no `used_crate_source` record exists for it at all.
            resident: false,
            // an ordinary compilation sets no `-Zforce-unstable-if-unmarked`.
            building_the_sysroot: false,
            // `#![no_std]`: rustc injects `core`, and this crate is not it.
            injected: false,
            // the forgery is the only sysroot-named crate in the graph.
            sysroot_supplied_one: false,
            // …and the attribute is spellable, which is the whole of R2.
            owns_an_anchor: true,
        };
        assert!(
            the_anchor_rule(&self_named_std),
            "planted violation is gone: the pre-2026-08-23 local arm no longer accepts a \
             crate that declares its own sysroot anchor, so this test no longer witnesses \
             the hole it exists for"
        );
        assert!(
            !authenticated(&self_named_std),
            "a crate compiled `--crate-name std` authenticated ITSELF as the sysroot: its \
             paths go unstamped and every `std::` root anchor downstream reads them as \
             genuine"
        );
    }

    /// The LOCAL arm reads the command line and NOTHING else — asserted as an
    /// equality over all sixteen combinations of the four facts it must ignore,
    /// so the arm cannot acquire a second grant without this going red.
    ///
    /// THREE MUTATIONS THIS WATCHES, none of them reachable by any other test:
    ///
    /// 1. `if defining_crate_is_local { return true }` — the "obviously ours"
    ///    exemption someone will reach for the next time `cargo -Zbuild-std`'s
    ///    user unit over-declines. Red on every `building_the_sysroot == false`
    ///    row.
    /// 2. `if defining_crate_is_local { return loaded_from_this_compilers_sysroot
    ///    || invocation_is_building_the_sysroot }` — dropping the early return and
    ///    letting the external arm answer. Red on `(resident = true, building =
    ///    false)`. That row is not reachable from today's extractor, whose
    ///    `crate_is_sysroot_resident` returns `false` for `LOCAL_CRATE`; it is a
    ///    pin on the RULE, so the rule stays fail-closed no matter what a future
    ///    caller passes rather than depending on the caller to pass `false`.
    /// 3. restoring the anchor arm, as in the falsify-once test above. Red on
    ///    `(anchor = true, building = false)`.
    #[test]
    fn the_local_arm_answers_from_the_command_line_alone() {
        for resident in [false, true] {
            for building_the_sysroot in [false, true] {
                for injected in [false, true] {
                    for sysroot_supplied_one in [false, true] {
                        for owns_an_anchor in [false, true] {
                            let s = Supply {
                                local: true,
                                resident,
                                building_the_sysroot,
                                injected,
                                sysroot_supplied_one,
                                owns_an_anchor,
                            };
                            assert_eq!(
                                authenticated(&s),
                                building_the_sysroot,
                                "the local arm read something other than the command line at \
                                 resident={resident} building={building_the_sysroot} \
                                 injected={injected} supplied={sysroot_supplied_one} \
                                 anchor={owns_an_anchor}"
                            );
                        }
                    }
                }
            }
        }
    }

    /// The NAME GATE is load-bearing, not decoration, and it is the only thing
    /// holding this predicate's extension at `core`/`alloc`/`std`.
    ///
    /// A dozen call sites in `trust_mir_extract::convert` combine
    /// `is_real_sysroot_crate` with an ITEM name alone — `item_name == "Extend"`,
    /// `"HashMap"`, `"Vec"`. `hashbrown` ships INSIDE the compiler's own target
    /// library directory and is therefore resident, and it has both a `HashMap`
    /// and `Extend` impls, so a residency test without the name gate widens those
    /// grants to a crate nobody decided about.
    ///
    /// THE MUTATION: delete the `if !crate_name_wears_sysroot_spelling { return
    /// false }` gate. Red on all four rows. No other test can catch it — every
    /// [`Supply`] vector in this module passes `true` for the gate, and
    /// [`sysroot_identity_stamp_required`]'s own name input is a different
    /// function's, tested next door against the STAMP rule rather than this one.
    #[test]
    fn a_name_that_is_not_core_alloc_or_std_never_authenticates() {
        for local in [false, true] {
            for building_the_sysroot in [false, true] {
                assert!(
                    !crate_is_the_compilers_own_sysroot_crate(
                        false,
                        local,
                        // resident: `hashbrown` really does live in the compiler's
                        // own target library directory.
                        true,
                        building_the_sysroot,
                    ),
                    "a crate that does not wear a sysroot name authenticated at \
                     local={local} building={building_the_sysroot}"
                );
            }
        }
        // Control: the SAME residency, worn under a sysroot name, does authenticate
        // — so the four refusals above come from the gate and not from a predicate
        // that answers `false` for everything.
        assert!(crate_is_the_compilers_own_sysroot_crate(true, false, true, false));
    }

    /// With the sysroot-build lane off — every ordinary compilation — the EXTERNAL
    /// arm is residency and nothing else. Pinned so a later edit cannot slip a
    /// second grant in beside it.
    #[test]
    fn outside_the_sysroot_build_lane_the_rule_is_residency_alone() {
        for resident in [false, true] {
            assert_eq!(sysroot_crate_is_compiler_authenticated(resident, false), resident);
            // and the whole rule agrees, for an EXTERNAL crate wearing the name.
            assert_eq!(
                crate_is_the_compilers_own_sysroot_crate(true, false, resident, false),
                resident
            );
        }
    }

    /// THE REACHABILITY GUARD. A rule factored into a testable crate is worth
    /// exactly nothing if the shipped consumer keeps its own copy, and this file
    /// has now spent two rounds on rules whose tests were measuring something the
    /// compiler did not run.
    ///
    /// `trust-types` is deliberately decoupled from rustc, so it cannot call
    /// `convert::is_real_sysroot_crate` and cannot build a `TyCtxt` to feed it.
    /// What it CAN do is read the extractor's source and refuse the drift. Two
    /// checks, both fail-closed:
    ///
    /// * the extractor CALLS [`crate_is_the_compilers_own_sysroot_crate`] — the
    ///   trailing `(` keeps a doc-comment mention from satisfying it; and
    /// * the pre-2026-08-23 local anchor helper is GONE, so a rewire that
    ///   delegates on one arm while keeping the anchor arm alive on the other
    ///   cannot pass.
    ///
    /// If the sibling crate cannot be read at all, this FAILS rather than skips:
    /// an unreadable consumer is an unchecked consumer.
    ///
    /// THE MUTATION: re-inline the rule in `convert::is_real_sysroot_crate` (which
    /// is precisely the state this crate was in before this test) and it goes red.
    #[test]
    fn the_extractor_delegates_the_whole_rule_to_this_crate() {
        let convert = concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-mir-extract/src/convert.rs");
        let source = std::fs::read_to_string(convert).unwrap_or_else(|e| {
            panic!(
                "cannot read the extractor at `{convert}` ({e}), so the delegation this \
                 module's tests depend on is UNCHECKED. If the crate moved, re-point this \
                 test; do not delete it."
            )
        });
        assert!(
            source.contains("crate_is_the_compilers_own_sysroot_crate("),
            "`convert::is_real_sysroot_crate` does not call \
             `trust_types::crate_is_the_compilers_own_sysroot_crate`, so every test in this \
             module is measuring a COPY of the rule and not the one the compiler runs. \
             Apply the delegation."
        );
        assert!(
            !source.contains("local_crate_owns_a_sysroot_anchor"),
            "the pre-2026-08-23 local anchor helper is still present in the extractor: \
             residual R2's self-authentication route is spelled somewhere the tests in this \
             module cannot see"
        );
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

/// `Rvalue::Unsupported::kind` of a MIR `Transmute` whose destination is a
/// PATTERN TYPE over the source's own integer type
/// (`transmute::<i32, pattern_type!(i32 is ..-1 | 0..)>`, the body of every
/// `define_valid_range_type!` constructor: `NonZero*`, `*NotAllOnes`,
/// `Nanoseconds`, `UsizeNoHighBit`, reached through e.g.
/// `OwnedFd::from_raw_fd`).
///
/// Such a transmute IS the identity on the integer — a pattern type has its
/// base type's layout — and is undefined behaviour unless the value lies in the
/// pattern's valid range. The extractor reads that range off rustc's LAYOUT
/// (`BackendRepr::Scalar`'s `valid_range`, the exact set the compiler's niche
/// optimisation relies on) and records it here, in a sentinel rather than a
/// plain `Rvalue::Cast`, because the trust `Ty` of a pattern type is its base
/// integer (`ty_convert` erases the pattern): a `Cast` would carry no trace of
/// the range, and a consumer that admits it would silently drop the UB charge.
///
/// SHAPE (anything else is malformed and must be refused):
/// `operands == [value, start, end]`, `value` of the source integer type,
/// `start`/`end` integer constants of that type's signedness (`Uint` for an
/// unsigned base, sign-extended `Int` for a signed one) giving rustc's
/// `WrappingRange` — valid iff `start <= value <= end` when `start <= end`,
/// and `value >= start || value <= end` when the range wraps.
///
/// Consumers: `trust-ir-bridge` lowers it EXACTLY — the identity plus an
/// asserted membership (the UB precondition, charged); every other consumer
/// (vcgen's UnsupportedMir row included) keeps it fail-closed as the
/// `Rvalue::Unsupported` it is spelled as.
pub const TRUST_TRANSMUTE_INTO_VALID_RANGE_KIND: &str = "CastKind::Transmute(valid-range)";

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

/// Trust (W4 HASHMAP r2, 2026-09-27): the HASH-TABLE qualifier of the element-size
/// token, `::<__trust_elem_bytes@table@N>` (element size known) or
/// `::<__trust_elem_bytes@table@?>` (the sink IS a std hash table, but the element
/// layout could not be computed — a still-generic element or a layout error).
///
/// A std `HashMap`/`HashSet` does not allocate `count * size_of::<T>()` bytes the
/// way a `Vec` does: hashbrown rounds the requested capacity up to a power-of-two
/// bucket count (about `count * 8 / 7`, at least 4, 8 or 16) and stores one
/// control byte per bucket beside the element array, then panics "Hash table
/// capacity overflow" when THAT layout passes `isize::MAX`. The extractor stamps
/// this qualified token (from the call's DefId and monomorphized types — the
/// callee's impl self type, a `collect`/`collect_into` destination, an `extend`
/// receiver — never from a rendering) so vcgen can charge the bucket layout
/// instead of `count * stride`.
///
/// It SHARES [`TRUST_ELEM_BYTES_TOKEN_PREFIX`] on purpose: every consumer that
/// only asks "does this callee carry a verifier-only element token" (the
/// executable-lowering placeholder check, the def-path pin's `__trust_` marker
/// rule) keeps answering yes, while [`parse_trailing_elem_bytes_token`] — whose
/// grammar is digits only — answers `None` for it, so a consumer that knows only
/// the `Vec` stride can never read a hash table's element size as one.
pub const TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX: &str = "::<__trust_elem_bytes@table@";

/// What a [`TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX`] token says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableElemBytes {
    /// The exact `tcx.layout_of` size of the table's element (`(K, V)` for a
    /// `HashMap`, `T` for a `HashSet`).
    Known(i128),
    /// A std hash table whose element size is not known: the consumer must fail
    /// closed (it may never fall back to a count-only charge).
    Unknown,
}

/// Render the trailing hash-table element-size token (see
/// [`TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX`]) — the single producer spelling.
#[must_use]
pub fn render_trailing_table_elem_bytes_token(elem_bytes: Option<u64>) -> String {
    match elem_bytes {
        Some(n) => format!("{TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX}{n}>"),
        None => format!("{TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX}?>"),
    }
}

/// Parse the trailing hash-table element-size token, admitting ONLY the exact
/// trailing-position grammar the extractor emits (`…::<__trust_elem_bytes@table@N>`
/// with `N` a non-empty all-ASCII-digit run, or `…@table@?>`). Anything else is
/// `None`: not a hash-table token.
#[must_use]
pub fn parse_trailing_table_elem_bytes_token(callee: &str) -> Option<TableElemBytes> {
    let (_, after) = callee.rsplit_once(TRUST_TABLE_ELEM_BYTES_TOKEN_PREFIX)?;
    let body = after.strip_suffix('>')?;
    if body == "?" {
        return Some(TableElemBytes::Unknown);
    }
    if body.is_empty() || !body.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    body.parse().ok().map(TableElemBytes::Known)
}

#[cfg(test)]
mod table_elem_bytes_token_tests {
    use super::*;

    #[test]
    fn round_trips_both_producer_spellings() {
        let known = format!(
            "std::collections::hash::set::HashSet::<[u8; 4]>::with_capacity{}",
            render_trailing_table_elem_bytes_token(Some(4))
        );
        assert!(known.ends_with("::<__trust_elem_bytes@table@4>"));
        assert_eq!(parse_trailing_table_elem_bytes_token(&known), Some(TableElemBytes::Known(4)));
        let unknown = format!("f{}", render_trailing_table_elem_bytes_token(None));
        assert_eq!(unknown, "f::<__trust_elem_bytes@table@?>");
        assert_eq!(parse_trailing_table_elem_bytes_token(&unknown), Some(TableElemBytes::Unknown));
    }

    #[test]
    fn the_vec_stride_parser_never_reads_a_table_token() {
        let known = format!("f{}", render_trailing_table_elem_bytes_token(Some(4096)));
        assert_eq!(parse_trailing_elem_bytes_token(&known), None);
        let unknown = format!("f{}", render_trailing_table_elem_bytes_token(None));
        assert_eq!(parse_trailing_elem_bytes_token(&unknown), None);
        // And the table parser never reads a plain token.
        let plain = format!("f{}", render_trailing_elem_bytes_token(4096));
        assert_eq!(parse_trailing_table_elem_bytes_token(&plain), None);
        // Both share the verifier-only prefix every placeholder check keys on.
        assert!(known.contains(TRUST_ELEM_BYTES_TOKEN_PREFIX));
        assert!(unknown.contains(TRUST_ELEM_BYTES_TOKEN_PREFIX));
    }

    #[test]
    fn table_grammar_is_strict_and_trailing() {
        for bad in [
            "f::<__trust_elem_bytes@table@>",
            "f::<__trust_elem_bytes@table@1x>",
            "f::<__trust_elem_bytes@table@??>",
            "f::<__trust_elem_bytes@table@1",
            "f::<__trust_elem_bytes@table@1>::g",
            "f::<__trust_elem_bytes@table@999999999999999999999999999999999999999999>",
        ] {
            assert_eq!(parse_trailing_table_elem_bytes_token(bad), None, "{bad}");
        }
    }
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
///
/// `Mul` was added 2026-08-29 (verified-sysroot §5 step 1 slice): every
/// consumer decides its own capability per op, fail-closed — the TrustIr
/// bridge lowers all three to the defining modular `BinOp`, while the LIA
/// assert-refutation model keeps declining `Mul` (nonlinear) so a mul-marked
/// callee stays ungrounded there rather than mis-decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcWrappingRefutationOp {
    Add,
    Sub,
    Mul,
}

/// An exact compiler-authenticated `core` integer wrapping add/sub/mul method.
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
            "wrapping_mul" => RustcWrappingRefutationOp::Mul,
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

/// A compiler-authenticated overflow-CHECKED signed primitive method
/// (`iN::checked_add` / `checked_sub` / `checked_mul`, returning `Option<iN>`).
///
/// SIGNED ONLY, by design (checked-arith spec §5.5): `uN::checked_sub` has
/// different semantics (underflow below 0, range `[0, 2^N-1]`, a different
/// `Int` bridge), so unsigned checked methods are a separate, later increment
/// with their own kernel model — they DECLINE here rather than being admitted
/// under the signed model. Classification is deliberately strict even though
/// the marker itself can only be minted by the compiler in an authoritative
/// run; keeping the grammar here gives facet inference, E6 body recognition,
/// and the mint one fail-closed source of truth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcCheckedPrimitiveMethod {
    CheckedAdd(u32),
    CheckedSub(u32),
    CheckedMul(u32),
}

impl RustcCheckedPrimitiveMethod {
    /// Classify an exact compiler-marked `core` checked primitive method path.
    ///
    /// Only SIGNED widths `i8`–`i128` are admitted. Unsigned impls, `isize`,
    /// foreign roots, extra path segments, unmarked paths, same-suffix
    /// lookalikes, and every other checked method (`checked_div`,
    /// `checked_neg`, `checked_shl`, …) all decline.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        let path = callee.strip_prefix(TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX)?;
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
            "<impl i8>" => 8,
            "<impl i16>" => 16,
            "<impl i32>" => 32,
            "<impl i64>" => 64,
            "<impl i128>" => 128,
            _ => return None,
        };
        match method {
            "checked_add" => Some(Self::CheckedAdd(width)),
            "checked_sub" => Some(Self::CheckedSub(width)),
            "checked_mul" => Some(Self::CheckedMul(width)),
            _ => None,
        }
    }

    #[must_use]
    pub fn width(self) -> u32 {
        match self {
            Self::CheckedAdd(width) | Self::CheckedSub(width) | Self::CheckedMul(width) => width,
        }
    }
}

#[cfg(test)]
mod rustc_total_primitive_method_tests {
    use super::*;

    #[test]
    fn wrapping_refutation_method_classifier_is_exact_and_fail_closed() {
        assert!(RustcWrappingRefutationCarrier::PointerSized { signed: false }.matches(64, false));
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
            // The two carriers the 2026-08-29 rustc-hash measurement named as
            // absent callees, plus the signed fixed-width case.
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_mul",
                RustcWrappingRefutationOp::Mul,
                RustcWrappingRefutationCarrier::PointerSized { signed: false },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl u128>::wrapping_mul",
                RustcWrappingRefutationOp::Mul,
                RustcWrappingRefutationCarrier::Fixed { width: 128, signed: false },
            ),
            (
                "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_mul",
                RustcWrappingRefutationOp::Mul,
                RustcWrappingRefutationCarrier::Fixed { width: 32, signed: true },
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
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_div",
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

    #[test]
    fn checked_primitive_method_classifier_is_exact_and_fail_closed() {
        for (path, expected) in [
            (
                "@trust-rustc-checked-primitive-method::core::num::<impl i8>::checked_add",
                RustcCheckedPrimitiveMethod::CheckedAdd(8),
            ),
            (
                "@trust-rustc-checked-primitive-method::core::num::<impl i16>::checked_sub",
                RustcCheckedPrimitiveMethod::CheckedSub(16),
            ),
            (
                "@trust-rustc-checked-primitive-method::core::num::<impl i32>::checked_mul",
                RustcCheckedPrimitiveMethod::CheckedMul(32),
            ),
            (
                "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_add",
                RustcCheckedPrimitiveMethod::CheckedAdd(64),
            ),
            (
                "@trust-rustc-checked-primitive-method::core::num::<impl i128>::checked_mul",
                RustcCheckedPrimitiveMethod::CheckedMul(128),
            ),
        ] {
            assert_eq!(RustcCheckedPrimitiveMethod::classify(path), Some(expected));
        }

        for bad in [
            // Unmarked, source-spellable path — never trusted.
            "core::num::<impl i64>::checked_add",
            // Wrong marker namespaces (each is a different authority).
            "@trust-rustc-intrinsic::core::num::<impl i64>::checked_add",
            "@trust-rustc-total-primitive-method::core::num::<impl i64>::checked_add",
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i64>::checked_add",
            // UNSIGNED receivers decline (spec §5.5: different semantics/model).
            "@trust-rustc-checked-primitive-method::core::num::<impl u8>::checked_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl u64>::checked_sub",
            "@trust-rustc-checked-primitive-method::core::num::<impl u128>::checked_mul",
            "@trust-rustc-checked-primitive-method::core::num::<impl usize>::checked_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl isize>::checked_add",
            // Ops outside {add, sub, mul} decline (div/rem/neg/shl have no
            // overflow-flag form or a different model).
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_div",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_rem",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_neg",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_shl",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::wrapping_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_add_signed",
            // Foreign roots / extra segments / truncated paths.
            "@trust-rustc-checked-primitive-method::std::num::<impl i64>::checked_add",
            "@trust-rustc-checked-primitive-method::evil::core::num::<impl i64>::checked_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>::checked_add::suffix",
            "@trust-rustc-checked-primitive-method::core::num::checked_add",
            "@trust-rustc-checked-primitive-method::core::num::<impl i64>",
            "@trust-rustc-checked-primitive-method::",
        ] {
            assert_eq!(
                RustcCheckedPrimitiveMethod::classify(bad),
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
/// Trust (2026-09-28): the pointer width, in bits, of the target this compilation verifies
/// for, or `None` when no compiler has recorded one. `TrustVerify::run_pass` records it
/// from `tcx.data_layout` before any body is verified, and rustc verifies for one target
/// per process, so a process-wide value is exact. A consumer that rests on a 64-bit
/// address-space fact must read `None` as "unwitnessed" and fail closed.
static TARGET_POINTER_BITS: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

/// Record the verified target's pointer width (`0` clears it). See [`target_pointer_bits`].
pub fn set_target_pointer_bits(bits: u32) {
    TARGET_POINTER_BITS.store(bits, std::sync::atomic::Ordering::Relaxed);
}

/// The verified target's pointer width, or `None` when no compiler has recorded one.
#[must_use]
pub fn target_pointer_bits() -> Option<u32> {
    match TARGET_POINTER_BITS.load(std::sync::atomic::Ordering::Relaxed) {
        0 => None,
        bits => Some(bits),
    }
}

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
// formula_utils.rs removed — utilities now in formula/ submodules.
pub(crate) mod generics;
pub(crate) mod lifetime;
pub(crate) mod lifetime_analysis;
mod model;
pub(crate) mod resilience;
// Trust (2026-09-29): rustc's tuple layouts, carried out of band on the faithful lane.
mod tuple_layouts;
// sort_check.rs removed — sort checking now in formula/sort.rs.
// SMT-LIB2 pretty printer for formatted solver output.
pub mod smt_printer;
pub mod static_truth;
// Shared terminator-obligation recognizers (Unreachable class): trust-vcgen's
// v2_build_terminator_vc and the trust-ir spine must agree — one definition,
// two callers, on the static_truth precedent.
pub mod terminator_obligations;
// Shared matchers for modeled total core/std call summaries (bridge + vcgen must agree).
pub mod admissible_body;
// Trust (ref-self I1): the E6 parameter view — a borrow-erased copy of an
// extracted body, built so the UNCHANGED validator, recognizer and mints can
// run on it. Never edits a refusal; see the module docs for the aliasing
// assumption (R1) it rests on and the grade that discloses it.
pub mod e6_param_view;
// Trust (E6 admission expansion): the E6-ONLY reader's module — consulted by
// the E6 importer after `admissible_body`'s chain answers `None`, never by the
// Clean-origin faithfulness gate (side B). Today it holds the I0 refusal
// diagnostic; see the module docs.
pub mod e6_expr;
pub mod e6_odt;
pub mod facet_allowlist;
pub mod facet_inference;
pub mod facet_propagation;
pub mod structural_determinism;
pub mod structural_panic_freedom;
pub mod structural_purity;
pub mod structural_termination;
pub mod total_call_summaries;
// Per-block execution bounds over the natural-loop nest: trust-vcgen's accumulator
// lane and the bridge's native port of it must agree on `K`.
pub mod loop_nest;
// Trust (assumption ledger): shared markers for the compiler↔bridge assumption
// demotion contract (extern print/format/write dispatch, native-lowering gaps).
pub mod assumption;
// Trust (CB4): the compiler↔targo contract for bodies excluded from the proof
// inventory because rustc's libtest harness synthesized them. Shared for the
// same reason `assumption` is: the verify pass writes the row, targo counts it.
pub mod exclusion;
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
// Trust (2026-10-02, diag-vs-report): the compiler's Level-0 REFUTATION
// reclassifications (known-panicking call, native-unsupported safety, open
// generic dispatch), asked by BOTH the compiler's Level-0 summary line and its
// published transport row so the diagnostic and the gate cannot disagree.
pub mod l0_refutation;
// Trust (R1 corpus): depth-tolerant JSON deserialization for compiler-emitted
// recursive formula payloads (bounded big-stack fallback past serde_json's
// default 128-level recursion limit).
pub mod json_depth;
pub mod original_vc_snapshot;
pub use original_vc_snapshot::OriginalVcSnapshot;
// Trust (TRANSPORT-LINE-BUDGET-1): the size bound on one `TRUST_JSON` line and the
// fail-closed ladder that fits a function's report under it.
pub mod transport_budget;
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
// The one canonical query hash: SHA-256 of every assertion in scope at one
// check-sat, up to one consistent renaming of their free variables.
pub mod formula_hash;
// T3 C03: one SHA-256 Merkle digest per formula-DAG node, the bound-variable
// alpha digest, and the number of context nodes a row reaches (equal to
// `determinism::query_size`, I4). Nothing consumes it yet (design §12, L2′).
pub mod formula_merkle;
// T3 L4 (C06): the per-function VC context's types — rows over one hash-consed DAG, block-def
// spines, row identity, materialization. Nothing outside this crate and trust-vcgen's tests
// reads a context yet (C07 does).
pub mod vc_context;
// Canonical SMT-LIB2 logic selection, free variable collection, and sort inference.
pub mod smt_logic;
// THE ONE SMT-LIB logic-name lattice: the admissibility table (written once, as
// data), the total feature-set -> logic-name selector both SMT lanes call, and
// the exhaustive proof over the whole feature powerset that the selection
// ADMITS what it must. Admissibility is the invariant every consumer rests on;
// a group or batch unions its members' features and selects ONCE, which needs
// nothing else. Monotonicity is NOT a property of this table and must not be
// assumed: when SMT-LIB names no logic for a feature set itself, the least
// admitting row must commit to dimensions the set did not ask for, and a
// superset that SMT-LIB DOES name exactly then admits less than it did. The
// module pins the exact extent and the exact source sets rather than a
// characterization — re-read them there, because both move whenever a row is
// added or a dimension is introduced.
pub mod logic_lattice;
// Ambient per-function verification deadline — lets every synchronous
// preprocessing choke point (extraction, VC gen, spec inference) consult the
// existing per-function budget and fail closed, closing the non-termination
// hole where the cooperative deadline only covered solver dispatch.
pub mod verify_budget;
// Determinism accounting (docs/design/2026-09-29-incremental-deterministic-
// trust-results.md): why each obligation's search ended (`StopCause`), whether
// that is reproducible, the unit outcome, the verdict vector and its digest, the
// backstop ledger and the budget profile.
pub mod determinism;
// T3 L4 (C06a): the audit ledger behind `TRUST_ELIDE_AUDIT`'s CAP, STOP and CERTIFY-STOP
// rows, attributed to the one active body scope. Measurement only.
pub mod audit_ledger;
// The stable, content-addressed obligation key (T9): `<def_path>#<local id>`,
// minted once per function at transport emission, plus the function source
// digest a baseline matches moved functions by.
pub mod expanded_function_identity;
pub mod obligation_identity;
// Stable names for Lean declarations, the same `<name>#<16 hex>` shape as an
// obligation key, so a `.lean` check's records diff like a crate's.
pub mod lean_declaration_identity;
// Distinct-site accounting over refuted rows (a MIR assert's L0 row and its
// hardened panic-boundary twin are two rows at one site). Informational only.
pub mod failure_sites;
// SMT-LIB2 string-based pretty printer for debugging and external solver interop.
mod result;
// The §7 multi-axis grade record (two-language design, R-U): the lossless
// successor to the legacy AssuranceLevel ladder.
pub mod grade;
// The three-axis grade of a passing obligation (R7: encoding, discharge,
// premises), stated per proof-authority class and carried on the transport.
pub mod authority_grade;
// The kernel theory and environment a Certified row was checked in (KR0
// switch): wire mirrors of the Clean reference entry's token.
pub mod kernel_theory;
pub use kernel_theory::{KernelEnvDigest, KernelTheoryId};
pub mod guidance;
// The single per-obligation outcome vocabulary shared by the compiler
// transport, the report DTOs, and every consumer downstream of them.
pub mod outcome;
pub(crate) mod smtlib2_printer;
// The ONE reader of an integer literal written in a contract predicate. Public
// because the compiler's own snippet tokenizer
// (`rustc_mir_transform::trust_contract_query`) reads the same grammar, and two
// copies of one grammar is how this repo's kind-binding tables drifted before.
pub mod int_literal;
pub(crate) mod spec;
pub(crate) mod spec_attrs;
// SPEC-FLOAT-EQ-STRUCTURAL-1: the one rule for what a contract `==` between
// floats means (Rust `PartialEq`, i.e. IEEE `FpEq`, never structural `Eq`).
mod spec_float_eq;
mod spec_parse;
mod spec_render;
// state_machine extraction lives in trust-temporal/extract.rs.
// Types (StateMachine, StateInfo, Transition) live in model.rs.
// Dead state_machine.rs (692 lines) removed — was never in module tree.
pub(crate) mod strengthen;
pub(crate) mod taint;
pub(crate) mod trait_resolution;
// Trust (E5 conservation): the reserved `trust::` attribute vocabulary, enumerated
// from the code that CONSUMES each name. Deliberately dependency-free so the
// resolver can key its hard-error refusal on it without pulling in verification IR.
pub(crate) mod traits;
pub mod trust_attr_namespace;
// Allocation-identity/offset model for pointer values (design of record for
// verified-sysroot-scoping §5 step 3 lives in the module doc).
pub mod alloc_model;
pub mod constant_image;
/// Occurrence/value identity for every operand carrier with no modeled value
/// (OPAQUE-SCALAR-ID-1, OPAQUE-REF-ID-1).
pub mod opaque_identity;
pub use opaque_identity::{
    OPAQUE_REF_SYMBOL_PREFIX, OPAQUE_SCALAR_SYMBOL_PREFIX, OpaqueOrigin,
    UNSUPPORTED_OPERAND_SYMBOL_PREFIX,
};
// Trust (W4 HASHMAP r3): the live-source item bound and the destination-capacity
// tests behind the "bounded std source" allocation grants (extractor + vcgen).
pub mod live_source_bound;
pub use constant_image::*;
// Provenance tracking types for memory model Layer 2.
pub mod provenance;
// Unified memory model for trust-wp/trust-vc cross-function proof composition.
pub mod native_admission;
pub mod unified_memory;
// Legacy vulnerability-pattern prototype. The production verifier has its
// own sound VC generation/analysis lanes and nothing calls this heuristic
// scanner; keep its unit tests without compiling duplicate detectors into all
// downstream Trust crates.
#[cfg(test)]
mod patterns;
// `Formula::ConstArray` across this crate's formula consumers.
#[cfg(test)]
mod const_array_tests;
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
// The portable vocabulary for a caller-side precondition carried by a minted
// Clean-origin `def`. Here, and not on either side, because `trust-vcgen` (the
// consumer) and `trust-clean-carrier` (the producer) share only this crate.
pub mod clean_origin_precondition;

#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;

pub use annotation::*;
pub use atomic_intrinsics::parse_atomic_intrinsic;
pub use bitvector::*;
pub use boundary::*;
pub use clean_origin_precondition::{
    CleanOriginPrecondition, PreconditionOperand, PreconditionRelation,
};
pub use concurrency::*;
pub use digest::{
    canonical_json_bytes, canonical_json_sha256, canonical_json_value, canonicalize_json_in_place,
    is_canonical_json, is_stable_sha256_hex, lowercase_hex, stable_sha256_hex,
    stable_sha256_hex_parts, stable_sha256_hex_reader, stable_sha256_parts,
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
    sorts_agree,
};
pub use smt_printer::{PrintConfig, SmtPrinter};
pub use smtlib2_printer::{
    SmtLib2Config, SmtLib2Printer, escape_smt_string, is_valid_smt_identifier, operator_to_smt,
    sort_to_smt,
};
pub use spec::*;
pub use spec_attrs::*;
pub use spec_float_eq::*;
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
pub use tuple_layouts::{LayoutTarget, TupleLayoutInfo, TupleLayouts};
pub use utils::{operand_place, strip_generics, strip_generics_cow, strip_generics_eq};
