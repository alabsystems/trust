// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cross-crate PROOF-position composition: a dependency crate's `clean { … }`
//! island sources, re-elaborated under THIS build's kernel so a contract may
//! cite the dependency's theorems and definitions.
//!
//! # What this module is, and what it deliberately is not
//!
//! It is the composition and identity half of cross-crate proof citation:
//! given the transported island sources of some dependency crates plus this
//! crate's own islands, it decides whether the two may be checked as ONE
//! environment, and refuses — with the crate named — when they may not.
//!
//! It is **not** a capability. No declaration of a dependency becomes callable
//! from Rust through this module: cross-crate CALL keeps its own, stronger
//! lane (a `VerdictDigest` certificate plus per-def readmission at the extern
//! MIR decode chokepoint, `rustc_mir_transform::clean_origin_import`), and
//! nothing here mints, grants or plans anything. It is also not a transport:
//! the sources arrive as untrusted bytes from the caller, exactly as
//! `trust_clean_island_sources` hands the CALL lane its own.
//!
//! **Nothing calls it.** It is the composition half of an unlanded capability,
//! built first because it is the half whose correctness cannot be established
//! by reading. The design of record is
//! `docs/design-notes/2026-09-18-cross-crate-proof-citation.md`; the compiler
//! seam is its increment 3, which is blocked on decisions R1 (the citation
//! spelling) and R3 (the E9 payload schema).
//!
//! # The acceptance control, unchanged from the CALL lane
//!
//! *"an imported certificate minted under a different kernel version must be
//! re-checked or refused, never accepted on a matching source hash."* Here
//! there is no certificate at all — a `theorem` is never minted and carries no
//! digest — so the rule is applied in its strongest form: **every dependency's
//! sources are re-elaborated and kernel-checked locally, and a recorded kernel
//! version that differs from this build's is refused before any elaboration
//! starts.** Digests in this module identify inputs for diagnostics and for the
//! caller's own binding; they grant nothing and are never compared in place of
//! a check.
//!
//! # The conservative-extension invariant, and why it is the whole point
//!
//! Four seams build "this crate's Clean environment": the resolve-time mint
//! (`rustc_resolve::trust_clean_mint::decide`), the verify pass
//! (`trust_verify::trust_check_clean_islands`), the MIR gate for a minted body
//! and the metadata export (`clean_origin_mir::clean_crate_environment`). The
//! mint seam runs at root-fragment expansion, where — measured, and recorded in
//! `trust_clean_mint.rs` — **no extern crate of the user's is registered yet**.
//! So the mint's environment is necessarily local-only and cannot be made to
//! share one batch with a proof environment that has dependencies in it.
//!
//! What replaces "one batch" is an invariant that is CHECKED, in **both**
//! directions:
//!
//! > the composed batch owns exactly the union of the names its parts own when
//! > checked separately, **and every declaration of every part — this crate's
//! > and each dependency's — has a byte-identical kernel payload in the
//! > composed environment and in the environment where that part was checked
//! > alone.**
//!
//! The name half catches re-homing — a dependency island that opens a
//! `namespace` and never closes it would otherwise register this crate's `foo`
//! as `X.foo`. The payload half catches the changes a name set cannot see: a
//! leaked `open`, a notation declaration or a `set_option` that makes a body
//! elaborate against a different constant. **Both directions matter and they
//! answer different questions.** Local-composed-vs-alone is what lets the
//! mint's local-only environment and this composed one be different
//! environments at all. Dependency-composed-vs-alone is what makes a citation
//! of `krate.thm` name the theorem the DEPENDENCY states: without it, this
//! crate's own islands could silently restate a dependency's theorem, and an
//! auditor re-checking the dependency alone would reproduce a different
//! statement than the one that discharged the contract.
//!
//! ## What the invariant does NOT see
//!
//! It covers the declarations a batch REGISTERS, because the name set is
//! `Environment::constants()` and the payload digest is per constant. It does
//! not cover the rest of the environment state a later clause-goal elaboration
//! reads — instances, the simp set, notation, options. A dependency that
//! registers an instance or a simp lemma can change how a tactic proof
//! elaborates in the composed environment without moving any name or any
//! payload. That is a real residual, not a covered case, and it is why the
//! seam's disposition for every name→symbol site is enumerated in the design
//! note rather than left to the composed environment's contents.
//!
//! # The session this module builds, and the one the compiler builds
//!
//! Every batch here starts from [`CleanIslandSession::new_for_source_batch`],
//! which materializes the kernel's PProd builtin prologue BEFORE the baseline
//! snapshot, so the four deltas this module compares are all relative to the
//! same starting environment. The compiler's verify pass uses
//! `CleanIslandSession::new()`, where PProd is materialized lazily by an
//! `import`. **So "zero units runs one batch" is true of the kernel run over
//! the same sources; it is NOT true that the session is the one the verify
//! pass builds.**
//!
//! The two constructors are therefore NOT to be unified. They were measured to
//! agree about every declaration a crate's own islands own (tests named
//! `the_verify_pass_session_agrees_with_the_composition_*`), so the wiring
//! keeps the verify pass's session exactly as it is and uses the composition
//! as a SECOND session, entered only to grade a crate-qualified citation. What
//! licenses a goal built in the first to be graded in the second is
//! [`ExternProofComposition::reconcile_with_local_environment`], which a
//! caller runs once and treats as fail-closed.
//!
//! The Rust callees are the other half of that reconciliation, and they are an
//! explicit input here: `trust_check_clean_islands` runs
//! `declare_rust_callees(rust_callee_declarations(tcx))` BEFORE `check_all`, so
//! a crate whose island says `def f (x : UInt64) : UInt64 := rust_helper x`
//! compiles today. A composition that did not declare them would reject that
//! crate's own islands the moment any dependency carried proof material.
//! They are declared in the local-only and composed sessions (the two that
//! stand for a compiler seam) and NOT in a dependency's standalone session: a
//! dependency's islands may not name this crate's Rust items, and a dependency
//! declaration that collides with a callee's bare name is refused by name in
//! step 5 rather than discovered by the kernel.
//!
//! # Cost, stated rather than hidden
//!
//! With `n` dependency units the composition runs `n + 2` kernel batches: one
//! per unit standalone (which is what re-establishes each dependency's proof
//! material under the local kernel), one local-only (the mint's environment,
//! re-run because no session survives from resolve time), and one composed.
//! With zero units it runs exactly one batch. There is deliberately no cache: a
//! faithfulness verdict is not incrementally cacheable, the same call the CALL
//! lane made for the same reason.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{Environment, Name};
use trust_types::digest::canonical_json_sha256;

use crate::clean_census::owned_names;
use crate::clean_island::{CleanIslandSession, CleanIslandStandinImport, RustCallee};
use crate::clean_island_batch::CleanIslandBatch;

/// Which crate a declaration in the composed environment came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclarationOrigin {
    /// A `clean { … }` island of the crate being compiled.
    LocalCrate,
    /// An Opaque constant the compiler declared for one of THIS crate's Rust
    /// `fn`s, so an island may call it (the Lean-calls-Rust lane). It occupies
    /// the bare Rust item name in the same kernel namespace as every island
    /// declaration, so it takes part in collision detection.
    LocalRustCallee,
    /// A dependency, by transported identity.
    Dependency(ExternProofUnitId),
}

impl DeclarationOrigin {
    fn describe(&self) -> String {
        match self {
            Self::LocalCrate => "this crate".to_string(),
            Self::LocalRustCallee => "this crate (as a Rust callee an island may call)".to_string(),
            Self::Dependency(id) => format!("`{}`", id.crate_name),
        }
    }
}

/// Transported identity of one dependency crate's Clean proof material.
///
/// `stable_crate_id` is what distinguishes two versions of one crate name. A
/// citation is written against a NAME, so two units that share a name and
/// differ in id are an ambiguity this module refuses rather than ranks.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExternProofUnitId {
    pub crate_name: String,
    pub stable_crate_id: u64,
}

/// One dependency crate's transported proof material. Untrusted input: the
/// bytes are re-elaborated and kernel-checked, and `kernel_version` is a
/// COMPARISON input, never a claim that is believed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternProofUnit {
    pub id: ExternProofUnitId,
    /// The Clean kernel version the dependency recorded when it transported
    /// these sources.
    pub kernel_version: String,
    /// The transport digest the DEPENDENCY published for these exact bytes,
    /// computed by [`extern_proof_source_digest`] on the producing side.
    ///
    /// Compared against the same function recomputed over the bytes that
    /// actually arrived, BEFORE any elaboration. It is an agreement check
    /// between producer and consumer about *which* bytes crossed — never an
    /// acceptance: a unit whose digest matches is still re-elaborated and
    /// kernel-checked here, exactly as one whose digest is unknown would be.
    pub declared_source_digest: String,
    /// The dependency's island sources, in the dependency's authored order.
    pub sources: Vec<String>,
}

/// One island failure, with everything the existing compiler seam needs to put
/// it back on a Rust span: WHICH island of the batch, and the island-relative
/// byte offsets Clean reported.
///
/// `island` indexes the batch the refusal came from — the local islands for
/// [`ExternProofRefusal::LocalBatchRejected`], that unit's own sources for
/// [`ExternProofRefusal::UnitDoesNotElaborate`], and
/// [`ExternProofComposition::sources`] for
/// [`ExternProofRefusal::ComposedBatchRejected`]. A composed index below
/// `local_island_offset` is a dependency's island, whose offsets name no span
/// in this crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternProofDiagnostic {
    pub island: usize,
    pub start: usize,
    pub end: usize,
    pub message: String,
}

impl ExternProofDiagnostic {
    fn render(&self) -> String {
        format!("island {} @{}..{}: {}", self.island, self.start, self.end, self.message)
    }
}

/// One `import` an accepted island wrote that Clean's built-in prelude
/// STAND-IN served, with the crate that wrote it.
///
/// A consumer that reports a green resting on such an island must report these
/// alongside it. For a dependency-owned disclosure, render `import.module`
/// only: `import.start`/`import.end` are offsets into the DEPENDENCY's island
/// text and name no span in the crate being compiled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternProofStandinImport {
    pub origin: DeclarationOrigin,
    /// Index into [`ExternProofComposition::sources`].
    pub island: usize,
    pub import: CleanIslandStandinImport,
}

/// Every way a composition is refused. Each carries a v7/D3 note: what was
/// refused, why, and the options.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternProofRefusal {
    /// The kernel's builtin prologue could not be materialized.
    PreludeInit { detail: String },
    /// This crate's Rust callees could not be declared in the Clean
    /// environment. The compiler treats this as fatal at its own seam; here it
    /// is a refusal, because a composition over a partial callee set would
    /// compare environments that never both existed.
    RustCalleeRefused { detail: String },
    /// A unit arrived with no crate name.
    EmptyCrateName { stable_crate_id: u64 },
    /// A unit arrived with no island sources.
    NoSources { id: ExternProofUnitId },
    /// The same crate identity was supplied twice.
    DuplicateUnit { id: ExternProofUnitId },
    /// Two units share a crate name and differ in stable crate id.
    AmbiguousCrateName { crate_name: String, first: u64, second: u64 },
    /// A unit was produced by a different Clean kernel than this build links.
    KernelSkew { id: ExternProofUnitId, minted: String, local: String },
    /// The island bytes that arrived do not hash to the digest the dependency
    /// published for them: producer and consumer disagree about WHICH sources
    /// crossed. Refused before any elaboration.
    TransportDigestMismatch { id: ExternProofUnitId, declared: String, recomputed: String },
    /// A unit's sources do not elaborate under this build's kernel.
    UnitDoesNotElaborate { id: ExternProofUnitId, diagnostics: Vec<ExternProofDiagnostic> },
    /// This crate's own islands do not elaborate WITHOUT its dependencies'
    /// proof material. Nothing is composed on top of a broken local
    /// environment — and this is a requirement the composition adds. See the
    /// note.
    LocalBatchRejected { diagnostics: Vec<ExternProofDiagnostic> },
    /// One declaration name is owned by two different crates.
    DeclarationCollision { name: String, first: DeclarationOrigin, second: DeclarationOrigin },
    /// The composed batch does not elaborate although every part did.
    ComposedBatchRejected { diagnostics: Vec<ExternProofDiagnostic> },
    /// The composed environment is not the additive union of its parts: a name
    /// appeared that no part owned, or a part's name went missing.
    NonAdditiveComposition { unexpected: Vec<String>, missing: Vec<String> },
    /// A declaration of THIS crate does not mean the same thing with the
    /// dependencies present as it does without them.
    LocalDeclarationsRebound { names: Vec<String> },
    /// A declaration of a DEPENDENCY does not mean the same thing in the
    /// composed environment as it does when that dependency is checked alone —
    /// so a citation of it would not name what the dependency states.
    DependencyDeclarationsRebound { id: ExternProofUnitId, names: Vec<String> },
    /// The session the COMPILER built for this crate's own islands does not
    /// hold this crate's declarations the way the composition does — so the
    /// two environments a cross-crate citation straddles are not the same
    /// environment, and a goal built in one may not be graded in the other.
    LocalSessionDisagrees { missing: Vec<String>, rebound: Vec<String> },
    /// A name a DEPENDENCY owns is already bound in the session the COMPILER
    /// built for this crate — so composing would put a dependency's definition
    /// where this compilation already has one of its own, and a goal built in
    /// the compiler's session would mean something else in the composed one.
    ///
    /// The constructor's [`Self::DeclarationCollision`] cannot see this: it
    /// compares a unit's names against this crate's ISLAND declarations and
    /// the Rust callees its caller passed, while the compiler's session also
    /// carries admissions made after composition — E6 program functions among
    /// them.
    DependencyNameBoundLocally { id: ExternProofUnitId, names: Vec<String> },
    /// A kernel payload could not be read back for hashing.
    PayloadUnreadable { detail: String },
}

impl ExternProofRefusal {
    /// The one-line refusal, for a diagnostic's primary message.
    #[must_use]
    pub fn headline(&self) -> String {
        match self {
            Self::PreludeInit { .. } => {
                "the Clean kernel prologue could not be initialized for a cross-crate proof \
                 batch"
                    .to_string()
            }
            Self::RustCalleeRefused { .. } => {
                "this crate's Rust callees could not be declared in the Clean environment a \
                 cross-crate proof batch is composed in"
                    .to_string()
            }
            Self::EmptyCrateName { stable_crate_id } => format!(
                "a dependency's Clean proof unit (stable crate id {stable_crate_id}) arrived \
                 with no crate name"
            ),
            Self::NoSources { id } => format!(
                "`{}` is listed as carrying Clean proof material but transported no island \
                 sources",
                id.crate_name
            ),
            Self::DuplicateUnit { id } => {
                format!("`{}` was supplied twice as a dependency Clean proof unit", id.crate_name)
            }
            Self::AmbiguousCrateName { crate_name, .. } => format!(
                "two different crates named `{crate_name}` carry Clean proof material, so a \
                 citation naming `{crate_name}` is ambiguous"
            ),
            Self::KernelSkew { id, .. } => format!(
                "`{}`'s Clean proof material was produced by a different Clean kernel than \
                 this build links",
                id.crate_name
            ),
            Self::TransportDigestMismatch { id, .. } => format!(
                "the `clean {{ … }}` island sources that arrived from `{}` are not the bytes \
                 `{}` published a digest for",
                id.crate_name, id.crate_name
            ),
            Self::UnitDoesNotElaborate { id, .. } => format!(
                "`{}`'s `clean {{ … }}` islands do not elaborate under this compiler's Clean \
                 kernel",
                id.crate_name
            ),
            Self::LocalBatchRejected { .. } => {
                "this crate's own `clean { … }` islands were rejected when checked WITHOUT its \
                 dependencies' Clean proof material"
                    .to_string()
            }
            Self::DeclarationCollision { name, first, second } => format!(
                "the Clean declaration `{name}` is declared by both {} and {}",
                first.describe(),
                second.describe()
            ),
            Self::ComposedBatchRejected { .. } => {
                "this crate's islands and its dependencies' Clean proof material do not \
                 elaborate together, although each elaborates on its own"
                    .to_string()
            }
            Self::NonAdditiveComposition { .. } => {
                "composing the dependencies' Clean proof material with this crate's islands \
                 did not produce the union of their declarations"
                    .to_string()
            }
            Self::LocalDeclarationsRebound { names } => format!(
                "{} of this crate's Clean declaration(s) mean something different once the \
                 dependencies' proof material is present",
                names.len()
            ),
            Self::DependencyDeclarationsRebound { id, names } => format!(
                "{} of `{}`'s Clean declaration(s) mean something different in this crate's \
                 build than they do in `{}` itself",
                names.len(),
                id.crate_name,
                id.crate_name
            ),
            Self::LocalSessionDisagrees { missing, rebound } => format!(
                "the Clean environment this compilation checked its own islands in does not \
                 agree with the composed one about {} declaration(s) of this crate",
                missing.len() + rebound.len()
            ),
            Self::DependencyNameBoundLocally { id, names } => format!(
                "`{}` declares {} name(s) this compilation's own Clean session already binds",
                id.crate_name,
                names.len()
            ),
            Self::PayloadUnreadable { .. } => {
                "a Clean kernel declaration could not be read back while binding the \
                 cross-crate proof composition"
                    .to_string()
            }
        }
    }

    /// Why, and the options (ruling v7/D3).
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::PreludeInit { detail } => format!(
                "{detail}\n\
                 options:\n\
                 - report this with the crate and the toolchain version: the prologue is \
                   kernel-internal and does not depend on your sources."
            ),
            Self::RustCalleeRefused { detail } => format!(
                "{detail}\n\
                 The composition declares the SAME Rust callees the mint declared, because a \
                 local island may call them; a partial callee set would make the composed and \
                 the local-only environment incomparable.\n\
                 options:\n\
                 - fix the callee the message names — its refusal is the same one the crate's \
                   own island batch reports;\n\
                 - report it if the crate's islands compile without any dependency: the two \
                   seams must declare the same set."
            ),
            Self::EmptyCrateName { .. } => {
                "a proof unit is identified by its crate name and stable crate id; an empty \
                 name cannot be cited and cannot be checked for collisions.\n\
                 options:\n\
                 - rebuild the dependency with this toolchain;\n\
                 - report it with both crate hashes if the rebuild reproduces it."
                    .to_string()
            }
            Self::NoSources { id } => format!(
                "the dependency's metadata says `{name}` has Clean proof material but the \
                 island sources it transports are empty, so nothing could be cited from it \
                 and nothing could be re-checked.\n\
                 options:\n\
                 - rebuild `{name}` with this toolchain;\n\
                 - if the rebuild reproduces this, report it: the presence flag and the \
                   source array are two independent encodings and they disagree.",
                name = id.crate_name
            ),
            Self::DuplicateUnit { id } => format!(
                "one crate contributes one proof unit; two identical units mean the \
                 dependency graph was walked twice.\n\
                 options:\n\
                 - report it with `{}`'s crate hash — this is a compiler defect, not \
                   something your sources can cause.",
                id.crate_name
            ),
            Self::AmbiguousCrateName { crate_name, first, second } => format!(
                "stable crate ids {first} and {second} both answer to `{crate_name}`, and a \
                 citation names a crate, not a version.\n\
                 options:\n\
                 - unify the dependency on one version of `{crate_name}`;\n\
                 - drop the dependency you do not cite: every dependency that carries Clean \
                   proof material is composed, so both versions are present here whether or \
                   not either is cited."
            ),
            Self::KernelSkew { id, minted, local } => format!(
                "`{name}`'s Clean proof material was produced under Clean kernel {minted}; \
                 this build links kernel {local}. A proof is re-checked here, never accepted \
                 on a matching hash, and re-checking under a different kernel is exactly the \
                 substitution that must not be silent.\n\
                 options:\n\
                 - rebuild `{name}` with this toolchain, so its islands are produced by the \
                   kernel that will re-check them;\n\
                 - if the two versions above match, this is a transport defect: report it \
                   with both strings.",
                name = id.crate_name
            ),
            Self::TransportDigestMismatch { id, declared, recomputed } => format!(
                "`{name}` published the digest {declared} over the `clean {{ … }}` island \
                 sources it transported; the bytes that arrived hash to {recomputed}. The \
                 digest identifies WHICH bytes crossed — it is not what makes them \
                 acceptable, and it is checked before anything is elaborated so that a \
                 disagreement is reported as one instead of surfacing as a proof about a \
                 declaration `{name}` does not have.\n\
                 options:\n\
                 - rebuild `{name}` and this crate against the same build of `{name}`: a \
                   stale or partially written `.rmeta` is the usual cause;\n\
                 - `cargo clean -p {name}` (or `targo clean -p {name}`) and rebuild, if the \
                   two builds are meant to be the same;\n\
                 - if `{name}` was rebuilt and this crate was not, rebuild this crate: the \
                   digest is over the exact transported bytes, so any island edit moves it;\n\
                 - if neither explains it, report it with both digests: nothing here rewrites \
                   the sources between the two sides.",
                name = id.crate_name
            ),
            Self::UnitDoesNotElaborate { id, diagnostics } => format!(
                "the sources are transport, never authority: they are re-elaborated here and \
                 must pass this kernel. They did not:\n{}\n\
                 options:\n\
                 - rebuild `{name}` with this toolchain;\n\
                 - if `{name}` builds on its own but not here, its islands depend on \
                   something this crate's build does not supply (a Rust callee of its own, \
                   or another crate's Clean declarations) — neither crosses in proof \
                   position yet;\n\
                 - vendor the declarations you need into this crate as a `clean {{ … }}` \
                   island or a `clean mod` unit.",
                render_diagnostics(diagnostics),
                name = id.crate_name
            ),
            Self::LocalBatchRejected { diagnostics } => format!(
                "this crate's islands are checked WITHOUT its dependencies' proof material, \
                 because the resolve-time mint decides this crate's callable definitions in \
                 exactly that environment and the two must agree about every local \
                 declaration. A local island may therefore not name a dependency's \
                 declaration — that is a requirement this composition adds, and it is the \
                 first thing to check if an error below is an unresolved name a dependency \
                 owns. A partially registered environment also mints no positive evidence, so \
                 nothing is composed on top of a rejected local batch:\n{}\n\
                 options:\n\
                 - vendor the declaration you need into this crate as a `clean {{ … }}` \
                   island or a `clean mod` unit;\n\
                 - move the local declaration into the dependency, where the rest of its \
                   mathematics already is;\n\
                 - fix the island errors at their own spans, if they name nothing of a \
                   dependency's.",
                render_diagnostics(diagnostics)
            ),
            Self::DeclarationCollision { name, first, second } => format!(
                "the composed proof environment holds one declaration per name, and `{name}` \
                 is declared by {first_origin} and by {second_origin}. Admitting both would \
                 let a contract be judged against one `{name}` while the rest of the \
                 compilation means the other — the resolve-time mint decides this crate's \
                 callable definitions in an environment that has no dependency material in \
                 it at all.\n\
                 options:\n\
                 - rename one of them;\n\
                 - put `{name}` inside a Clean `namespace` in the crate that declares it;\n\
                 - if both crates get `{name}` from ONE source file shared with \
                   `#[path = \"…\"] clean mod`, the two declarations are the same text but \
                   this composition cannot tell that from a shadow: keep the shared unit in \
                   one crate and cite it from the other. Dropping the citation does not \
                   help — every dependency that carries Clean proof material is composed, \
                   cited or not.",
                first_origin = first.describe(),
                second_origin = second.describe()
            ),
            Self::ComposedBatchRejected { diagnostics } => format!(
                "each part elaborates on its own, so this is an interaction between them — \
                 most often a duplicate generated helper or a dependency's file-state \
                 command (`open`, `set_option`, notation) reaching this crate's \
                 islands:\n{}\n\
                 options:\n\
                 - wrap the dependency's declarations in a Clean `namespace`;\n\
                 - vendor the declarations you need into this crate instead of citing them.",
                render_diagnostics(diagnostics)
            ),
            Self::NonAdditiveComposition { unexpected, missing } => format!(
                "composition must be additive: the environment a contract is judged in has \
                 to be the parts' union, or the mint's local-only environment and this one \
                 would disagree about what a name means.\n\
                 appeared with no owner: {}\n\
                 owned by a part but absent: {}\n\
                 options:\n\
                 - wrap the dependency's declarations in a Clean `namespace` and cite them \
                   there;\n\
                 - vendor the declarations you need into this crate;\n\
                 - report it if neither applies: a dependency whose islands close every \
                   block they open cannot cause this.",
                render_names(unexpected),
                render_names(missing)
            ),
            Self::LocalDeclarationsRebound { names } => format!(
                "these declarations of this crate elaborate to a different kernel term when \
                 the dependencies' proof material is present: {}\n\
                 A dependency may add declarations; it may not change what this crate's own \
                 declarations mean, because the resolve-time mint decided this crate's \
                 callable definitions in the environment WITHOUT them.\n\
                 options:\n\
                 - wrap the dependency's declarations in a Clean `namespace`;\n\
                 - remove the `open`, notation or option command from the dependency's \
                   island that reaches this crate;\n\
                 - vendor the declarations you need into this crate instead of citing them.",
                render_names(names)
            ),
            Self::DependencyDeclarationsRebound { id, names } => format!(
                "these declarations of `{name}` elaborate to a different kernel term in this \
                 crate's composed environment than they do when `{name}` is checked alone: \
                 {}\n\
                 A citation must name what the DEPENDENCY states: if this crate's own \
                 islands can restate a dependency's theorem, an auditor who re-checks \
                 `{name}` on its own reproduces a different statement than the one that \
                 discharged the contract here.\n\
                 options:\n\
                 - wrap this crate's declarations in a Clean `namespace`, or remove the \
                   `open`, notation or option command that reaches `{name}`;\n\
                 - vendor the declarations you need into this crate and stop citing \
                   `{name}`;\n\
                 - report it if this crate's islands declare nothing `{name}` could see.",
                render_names(names),
                name = id.crate_name
            ),
            Self::LocalSessionDisagrees { missing, rebound } => format!(
                "a cross-crate citation is graded in the COMPOSED environment while the goal \
                 is built from this crate's own — and that is only sound while every \
                 declaration of this crate means the same thing in both. It does not:\n\
                 {}{}\
                 options:\n\
                 - report it with this crate's islands: the two environments run the same \
                   sources with the same Rust callees, so a disagreement is a compiler \
                   defect, not something a contract can cause;\n\
                 - until it is understood, nothing cross-crate is graded: this refusal is \
                   the fail-closed arm, and the crate-local lane is unaffected.",
                if missing.is_empty() {
                    String::new()
                } else {
                    format!("  absent from the compilation's own session: {}\n", missing.join(", "))
                },
                if rebound.is_empty() {
                    String::new()
                } else {
                    format!("  different kernel payload: {}\n", rebound.join(", "))
                },
            ),
            Self::DependencyNameBoundLocally { id, names } => format!(
                "the dependency `{krate}` declares these Clean names, and the session this \
                 compilation built for its OWN contracts already binds them: {}\n\
                 A dependency may add declarations; it may not answer for a name this \
                 compilation already gave a meaning — a Rust callee, or a program function \
                 admitted for an `ensures` discharge. Composing would silently re-point \
                 every goal that mentions the name at `{krate}`'s definition.\n\
                 options:\n\
                 - wrap `{krate}`'s declarations in a Clean `namespace` so they cannot \
                   collide with this crate's own names;\n\
                 - rename the Rust item of this crate whose Clean name collides;\n\
                 - until one of those, nothing cross-crate is graded: this refusal is the \
                   fail-closed arm, and the crate-local lane is unaffected.",
                render_names(names),
                krate = id.crate_name
            ),
            Self::PayloadUnreadable { detail } => format!(
                "{detail}\n\
                 options:\n\
                 - report it: the environment enumerated a declaration it then could not \
                   produce, which your sources cannot cause."
            ),
        }
    }
}

fn render_diagnostics(diagnostics: &[ExternProofDiagnostic]) -> String {
    if diagnostics.is_empty() {
        return "  (no diagnostic was recorded)".to_string();
    }
    diagnostics.iter().map(|d| format!("  {}", d.render())).collect::<Vec<_>>().join("\n")
}

fn render_names(names: &[String]) -> String {
    if names.is_empty() { "(none)".to_string() } else { names.join(", ") }
}

/// How a citation spelling resolves against a composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CitedExternResolution {
    /// Not a dependency citation: the existing crate-local lookup applies
    /// unchanged. This is the answer for every crate with no proof units, and
    /// for every spelling the composed environment already resolves without a
    /// dependency (a prelude name such as `Nat.add_comm` keeps working even
    /// when a dependency happens to be named `Nat`).
    LocalLookup,
    /// A crate-qualified citation that resolves: look `kernel_name` up in the
    /// composed environment.
    Dependency { unit: ExternProofUnitId, kernel_name: Name },
    /// A BARE name that a dependency owns. Refused on purpose: an implicit
    /// scope would make "add a theorem to a library" a breaking change for
    /// every dependent, and would let a dependency answer for an identifier
    /// the author never wrote.
    BareDependencyName { unit: ExternProofUnitId, qualified_spelling: String },
    /// The head named a dependency, but that dependency owns no such
    /// declaration.
    NotInDependency { unit: ExternProofUnitId, kernel_name: Name },
    /// The head names a dependency that owns the tail, AND the whole dotted
    /// spelling also resolves without ANY dependency (this crate declared it,
    /// or the prelude owns it). Two readings exist; neither wins silently.
    AmbiguousWithNonDependency { unit: ExternProofUnitId, spelling: String },
    /// The WHOLE dotted spelling is itself a declaration that a DEPENDENCY
    /// owns, so the spelling has a second reading and that reading is also a
    /// dependency's.
    ///
    /// Two shapes reach here, and the second is the idiomatic Lean layout:
    ///
    /// * crate `spec`'s island writes `namespace spec … theorem cap_le … end
    ///   spec`, so `spec` owns the kernel name `spec.cap_le` while owning no
    ///   `cap_le`; and
    /// * crate `beta`'s island writes `namespace alpha …` while `alpha` is
    ///   also a dependency of this crate, so `beta` answers for a citation
    ///   addressed to `alpha`.
    ///
    /// Refused whether or not the head unit owns the tail — ranking the two
    /// readings is exactly the silent capture ruling R1 exists to prevent, and
    /// the R1-correct spelling of the declaring crate's own name is offered as
    /// `ratified_spelling`.
    DottedNameOwnedByDependency {
        head: ExternProofUnitId,
        declaring: ExternProofUnitId,
        spelling: String,
        ratified_spelling: String,
        head_owns_tail: bool,
    },
    /// The citation was spelled with the Rust path separator (`krate::thm`).
    ///
    /// Refused, never translated. Ruling R1 (§10 of the design note, decided
    /// 2026-09-19) takes the DOTTED spelling `krate.thm`, because a citation
    /// name is a Clean name and `.` is what separates its segments; accepting
    /// `::` as well would give one theorem two spellings, and silently
    /// rewriting `::` to `.` would make the accepted surface depend on a
    /// normalization step nothing else in the language performs.
    RustPathSpelling { spelling: String, ratified_spelling: String },
}

impl CitedExternResolution {
    /// The refusal note (ruling v7/D3) for the arms that refuse, and `None`
    /// for the two that do not ([`Self::LocalLookup`], [`Self::Dependency`]).
    ///
    /// The compiler seam renders this verbatim, so the wording — including
    /// which options are offered — lives with the rule it explains rather than
    /// being restated at each diagnostic site.
    #[must_use]
    pub fn note(&self) -> Option<String> {
        match self {
            Self::LocalLookup | Self::Dependency { .. } => None,
            Self::BareDependencyName { unit, qualified_spelling } => Some(format!(
                "that name is not declared by this crate's `clean {{ … }}` islands or by the \
                 Clean prelude; the dependency `{krate}` declares it. A dependency never \
                 answers for a BARE citation name: an implicit scope would make \"add a \
                 theorem to a library\" a breaking change for every dependent, and would let \
                 a crate you did not name decide what your contract was proved from.\n\
                 options:\n\
                 - write the crate-qualified spelling `{qualified_spelling}` (ruling R1: the \
                   dependency's crate name, a `.`, then the declaration's Clean name);\n\
                 - vendor the declaration into this crate as a `clean {{ … }}` island if you \
                   want it to be this crate's.",
                krate = unit.crate_name
            )),
            Self::NotInDependency { unit, kernel_name } => Some(format!(
                "`{krate}` is a dependency of this crate and carries Clean proof material, \
                 but it declares no `{kernel_name}`. The name after the crate name is the \
                 declaration's own Clean name inside `{krate}` — it is NOT re-homed under the \
                 crate name, so a theorem `{krate}` states as `bounds.cap_le` is cited as \
                 `{krate}.bounds.cap_le`.\n\
                 options:\n\
                 - check the declaration's spelling inside `{krate}`'s `clean {{ … }}` island, \
                   including any `namespace` it is declared in;\n\
                 - if the declaration is new in `{krate}`, rebuild `{krate}`: the citation \
                   resolves against the transported islands of the build this crate links.",
                krate = unit.crate_name
            )),
            Self::AmbiguousWithNonDependency { unit, spelling } => Some(format!(
                "`{spelling}` has two readings here: the dependency `{krate}`'s declaration, \
                 and a declaration of that exact dotted name that resolves without `{krate}` \
                 (this crate's own island, or the Clean prelude). Neither wins silently — a \
                 citation that changes meaning when a dependency is added or removed is a \
                 contract whose proof moved without the contract moving.\n\
                 options:\n\
                 - rename this crate's declaration, or the `namespace` it sits in, so only \
                   one reading exists;\n\
                 - if you meant the local one, it is still cited by its own name — the \
                   ambiguity is in the dotted spelling, not in the local lookup.",
                krate = unit.crate_name
            )),
            Self::DottedNameOwnedByDependency {
                head,
                declaring,
                spelling,
                ratified_spelling,
                head_owns_tail,
            } => {
                let tail = spelling.split_once('.').map_or("", |(_, tail)| tail);
                Some(format!(
                    "`{spelling}` has two readings here, and BOTH of them are a dependency's. \
                     Ruling R1 reads it as \"the crate `{head_krate}`, then the declaration \
                     `{tail}`\"{head_clause}; but the dependency `{decl_krate}` declares the \
                     whole dotted name `{spelling}` itself — a Clean `namespace` inside that \
                     crate, which is not re-homed and does not become a crate name. Neither \
                     reading wins silently: a citation that names one crate and is answered \
                     by another is a contract whose proof came from somewhere its author \
                     never wrote.\n\
                     options:\n\
                     - to cite `{decl_krate}`'s declaration, write `{ratified_spelling}` — the \
                       crate name, a `.`, then the declaration's own Clean name, `namespace` \
                       and all;\n\
                     - to cite something else, rename the `namespace` in `{decl_krate}` so it \
                       is not the name of a crate this compilation links.",
                    head_krate = head.crate_name,
                    decl_krate = declaring.crate_name,
                    head_clause = if *head_owns_tail {
                        format!(", and `{}` does declare `{tail}`", head.crate_name)
                    } else {
                        String::new()
                    },
                ))
            }
            Self::RustPathSpelling { spelling, ratified_spelling } => Some(format!(
                "`{spelling}` is spelled with the Rust path separator. A citation name is a \
                 CLEAN name: its segments are separated by `.`, and `{ratified_spelling}` is \
                 how the crate that states it spells its own declaration. Both spellings \
                 are not accepted, because one theorem with two spellings is two names for \
                 one obligation in every diagnostic, ledger and published row that mentions \
                 it (ruling R1, decided 2026-09-19).\n\
                 options:\n\
                 - write `{ratified_spelling}`;\n\
                 - that is the whole rule: the crate name, a `.`, then the declaration's own \
                   Clean name as the dependency declares it.",
            )),
        }
    }
}

/// How a bare CLAUSE identifier — not a `by` citation name — is dispositioned
/// against a composition.
///
/// A clause's ordinary identifiers are resolved at a different seam from the
/// citation name (`trust_verify::admit_clause_island_definitions`), and that
/// seam looks a bare name up in the island environment directly. Handing it a
/// composed environment without this gate would grant unqualified, uncited
/// cross-crate resolution of a dependency's definitions — the cross-crate form
/// of the name-capture family the round-2 clause guard closed. Every
/// name→symbol site must ask.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClauseIdentifierDisposition {
    /// No dependency answers for this name: the crate-local rule applies
    /// unchanged.
    LocalOrPrelude,
    /// Only a dependency owns it. Refused.
    ExternOwned { unit: ExternProofUnitId, qualified_spelling: String },
}

impl ClauseIdentifierDisposition {
    /// The refusal note for [`Self::ExternOwned`] (ruling v7/D3). `None` when
    /// nothing is refused.
    #[must_use]
    pub fn note(&self) -> Option<String> {
        match self {
            Self::LocalOrPrelude => None,
            Self::ExternOwned { unit, qualified_spelling } => Some(format!(
                "`{qualified_spelling}` is a Clean definition of the dependency `{krate}`, and \
                 a clause identifier is resolved against THIS crate's islands and Rust items \
                 only. A dependency may not answer for a bare identifier in a contract: the \
                 clause text would say one thing and the certified goal another, and adding a \
                 definition to a library would change what its dependents' contracts mean.\n\
                 options:\n\
                 - cite a THEOREM of `{krate}` about it in proof position instead \
                   (`ensures … by {krate}.<theorem>`), which is the only cross-crate \
                   surface — `{qualified_spelling}` is a definition and proves nothing on \
                   its own;\n\
                 - vendor the definition into this crate as a `clean {{ … }}` island;\n\
                 - declare a Rust `fn` of that name in this crate, if the clause means the \
                   program's function.",
                krate = unit.crate_name
            )),
        }
    }
}

/// An accepted composition: the composed session plus the bindings a caller
/// needs to resolve citations and to report honestly.
///
/// Only [`compose_extern_proof_batch`] constructs one, and only from a batch
/// that was accepted, was additive, and left every declaration of every part
/// meaning what it meant alone.
pub struct ExternProofComposition {
    units: Vec<ExternProofUnit>,
    unit_digests: Vec<String>,
    unit_owned: Vec<BTreeSet<Name>>,
    standin_imports: Vec<ExternProofStandinImport>,
    local_owned: BTreeSet<Name>,
    /// This crate's own declarations' kernel payload digests AS THE COMPOSED
    /// ENVIRONMENT HOLDS THEM. The constructor has already proved these equal
    /// to the local-only run's; keeping them is what lets a caller ask the
    /// third question the constructor cannot — whether the session the
    /// COMPILER built agrees too ([`ExternProofComposition::
    /// reconcile_with_local_environment`]).
    local_payloads_composed: BTreeMap<Name, String>,
    local_rust_callees: BTreeSet<Name>,
    sources: Vec<String>,
    local_island_offset: usize,
    composition_digest: String,
    batch: CleanIslandBatch,
    session: CleanIslandSession,
}

/// Identity and bindings only. The kernel environment is deliberately NOT
/// rendered: it is megabytes of prelude, and a `Debug` that printed it would
/// invite a reader to compare environments by their rendering instead of by
/// the payload digests the constructor actually compares.
impl std::fmt::Debug for ExternProofComposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExternProofComposition")
            .field("units", &self.units.iter().map(|unit| &unit.id).collect::<Vec<_>>())
            .field("unit_digests", &self.unit_digests)
            .field("local_owned", &self.local_owned.len())
            .field("local_rust_callees", &self.local_rust_callees.len())
            .field("local_island_offset", &self.local_island_offset)
            .field("sources", &self.sources.len())
            .field("composition_digest", &self.composition_digest)
            .finish_non_exhaustive()
    }
}

impl ExternProofComposition {
    /// The composed, accepted kernel environment, **with no ownership gate on
    /// it**.
    ///
    /// The name is the warning. This environment physically contains every
    /// dependency's constants under their own bare kernel names, so any seam
    /// that turns a name into a symbol — the citation lookup, the clause
    /// identifier admission (`admit_clause_island_definitions`), the E6
    /// program-function admission, the uncited island-defeq lane — resolves a
    /// dependency's declaration through it by default. That is the capture the
    /// crate-qualified rule exists to prevent, so a seam asks
    /// [`Self::resolve_cited`] or [`Self::clause_identifier`] FIRST and uses
    /// this only for the lookup those two allowed.
    ///
    /// `None` only if the session were tainted, which the constructor has
    /// already refused.
    #[must_use]
    pub fn ungated_environment(&self) -> Option<&Environment> {
        self.session.environment()
    }

    /// The exact composed batch, in the order it was checked: every
    /// dependency's sources in canonical unit order, then this crate's islands
    /// in authored order.
    #[must_use]
    pub fn sources(&self) -> &[String] {
        &self.sources
    }

    /// The composed batch's own result — one outcome per island in
    /// [`Self::sources`], carrying `registered` and Clean's island-relative
    /// offsets. Handed back whole so a caller keeps the span arithmetic and
    /// the per-island reporting the crate-local seam has today.
    #[must_use]
    pub fn composed_batch(&self) -> &CleanIslandBatch {
        &self.batch
    }

    /// Index of the first LOCAL island in [`Self::sources`]. A caller that maps
    /// batch outcomes back to Rust spans adds this offset and nothing else —
    /// the local islands are a contiguous suffix in their authored order.
    #[must_use]
    pub fn local_island_offset(&self) -> usize {
        self.local_island_offset
    }

    /// The dependency units in canonical order (`crate_name`, then
    /// `stable_crate_id`) — never `CrateNum` order, which is load order.
    #[must_use]
    pub fn units(&self) -> &[ExternProofUnit] {
        &self.units
    }

    /// Canonical-JSON SHA-256 over one unit's identity and its exact
    /// transported bytes. Identification for diagnostics and for the caller's
    /// own binding; it is never compared in place of the re-check.
    #[must_use]
    pub fn unit_digest(&self, index: usize) -> Option<&str> {
        self.unit_digests.get(index).map(String::as_str)
    }

    /// Canonical-JSON SHA-256 over the whole composition: the local kernel
    /// version, every unit's digest in canonical order (which binds each
    /// unit's identity AND its own byte partition), and this crate's island
    /// bytes in authored order.
    #[must_use]
    pub fn composition_digest(&self) -> &str {
        &self.composition_digest
    }

    /// Which crate declared `name`, or `None` for a prelude name.
    ///
    /// This answers from the per-part deltas, which is a valid report about the
    /// COMPOSED environment only because the constructor proved the two agree:
    /// the composed batch owns exactly the parts' union and every part's
    /// payloads are byte-identical composed and alone. It is a report about a
    /// checked equality, not an observation of the composed environment — a
    /// test that wants to know what composition did must look in
    /// [`Self::ungated_environment`].
    #[must_use]
    pub fn owner_of(&self, name: &Name) -> Option<DeclarationOrigin> {
        if self.local_owned.contains(name) {
            return Some(DeclarationOrigin::LocalCrate);
        }
        if self.local_rust_callees.contains(name) {
            return Some(DeclarationOrigin::LocalRustCallee);
        }
        self.unit_owned
            .iter()
            .position(|owned| owned.contains(name))
            .map(|index| DeclarationOrigin::Dependency(self.units[index].id.clone()))
    }

    /// The dependency that owns `name`, when a BARE use of it would silently
    /// reach into a dependency. The caller refuses on `Some`.
    #[must_use]
    pub fn bare_name_is_extern_owned(&self, name: &Name) -> Option<&ExternProofUnitId> {
        if self.local_owned.contains(name) || self.local_rust_callees.contains(name) {
            return None;
        }
        self.unit_owned
            .iter()
            .position(|owned| owned.contains(name))
            .map(|index| &self.units[index].id)
    }

    /// Every `import` of an accepted island in the COMPOSED batch that Clean's
    /// built-in prelude STAND-IN served, with the crate that wrote it — the
    /// dependencies' and this crate's own.
    ///
    /// Harvested from the composed batch, which is the run whose environment
    /// was accepted; a stand-in served differently there than in a standalone
    /// run is what the dependent's green actually rests on.
    #[must_use]
    pub fn standin_disclosures(&self) -> &[ExternProofStandinImport] {
        &self.standin_imports
    }

    /// Resolve a citation spelling under the crate-qualified rule.
    ///
    /// * a spelling with no dependency head → [`CitedExternResolution::LocalLookup`]
    ///   (unchanged behaviour), including a bare name nothing owns;
    /// * `krate.decl` where `krate` is a dependency that owns `decl`, and the
    ///   whole spelling resolves nowhere else → [`CitedExternResolution::Dependency`];
    /// * a bare name only a dependency owns →
    ///   [`CitedExternResolution::BareDependencyName`] (refused);
    /// * `krate.decl` whose WHOLE dotted spelling is a declaration some
    ///   dependency owns (`spec`'s island wrote `namespace spec`, or `beta`'s
    ///   wrote `namespace alpha`) →
    ///   [`CitedExternResolution::DottedNameOwnedByDependency`] (refused);
    /// * `krate.decl` that also resolves without any dependency →
    ///   [`CitedExternResolution::AmbiguousWithNonDependency`] (refused);
    /// * `krate.decl` where `krate` is a dependency that does not own `decl`
    ///   and nothing else resolves it → [`CitedExternResolution::NotInDependency`].
    #[must_use]
    pub fn resolve_cited(&self, spelling: &str) -> CitedExternResolution {
        // Ruling R1, decided 2026-09-19: the crate-qualified citation is
        // `krate.decl`, a dotted CLEAN name. The Rust path spelling is refused
        // FIRST, before any ownership question, so the answer does not depend
        // on whether a dependency happens to carry the name — the spelling is
        // wrong either way, and a refusal that changed with the dependency
        // graph would teach the wrong rule.
        if spelling.contains("::") {
            return CitedExternResolution::RustPathSpelling {
                spelling: spelling.to_string(),
                ratified_spelling: spelling.replace("::", "."),
            };
        }
        let full = Name::from_string(spelling);
        let head_unit = spelling.split_once('.').and_then(|(head, tail)| {
            self.units.iter().position(|unit| unit.id.crate_name == head).map(|i| (i, tail))
        });
        let Some((index, tail)) = head_unit else {
            if let Some(id) = self.bare_name_is_extern_owned(&full) {
                return CitedExternResolution::BareDependencyName {
                    unit: id.clone(),
                    qualified_spelling: format!("{}.{spelling}", id.crate_name),
                };
            }
            return CitedExternResolution::LocalLookup;
        };
        let unit = self.units[index].id.clone();
        let kernel_name = Name::from_string(tail);
        let owned_by_unit = !tail.is_empty() && self.unit_owned[index].contains(&kernel_name);
        // Is the WHOLE dotted spelling itself a declaration a DEPENDENCY owns?
        // Trust does not re-home a unit's declarations under its crate name —
        // but a unit's island may AUTHOR a `namespace` whose name is a crate
        // name, which is the idiomatic Lean layout, and then that unit owns the
        // full dotted name itself. Asked FIRST, and asked of the unit ownership
        // tables rather than of the composed environment, which physically
        // contains every unit's declarations.
        let declared_by_dependency = self.bare_name_is_extern_owned(&full).cloned();
        if let Some(declaring) = declared_by_dependency {
            let ratified_spelling = format!("{}.{spelling}", declaring.crate_name);
            return CitedExternResolution::DottedNameOwnedByDependency {
                head: unit,
                declaring,
                spelling: spelling.to_string(),
                ratified_spelling,
                head_owns_tail: owned_by_unit,
            };
        }
        // Does the WHOLE dotted spelling resolve without ANY dependency? The
        // local crate's own `namespace spec` answers here, and so does the
        // prelude: a unit named `Nat` must not capture `Nat.add_comm`. The
        // composed environment may be asked only now, because the arm above has
        // already taken every name a unit owns out of the question.
        let resolves_without_any_unit = self.local_owned.contains(&full)
            || self.local_rust_callees.contains(&full)
            || self.ungated_environment().is_some_and(|env| env.get_const(&full).is_some());
        match (owned_by_unit, resolves_without_any_unit) {
            (true, true) => CitedExternResolution::AmbiguousWithNonDependency {
                unit,
                spelling: spelling.to_string(),
            },
            (true, false) => CitedExternResolution::Dependency { unit, kernel_name },
            (false, true) => CitedExternResolution::LocalLookup,
            (false, false) => CitedExternResolution::NotInDependency { unit, kernel_name },
        }
    }

    /// Check this composition against the environment of the session the
    /// COMPILER actually built for this crate's own islands.
    ///
    /// # Why a third comparison exists
    ///
    /// The constructor proves the composed environment agrees with two
    /// environments it built itself: the local-only one and each unit
    /// standalone. It cannot prove anything about the session
    /// `trust_check_clean_islands` builds, which is constructed differently
    /// ([`CleanIslandSession::new`], PProd materialized lazily by an `import`,
    /// rather than [`CleanIslandSession::new_for_source_batch`]) and which is
    /// the environment a clause goal is actually elaborated in.
    ///
    /// **The seam this unblocks.** A cross-crate citation is graded by handing
    /// the composed environment the SAME clause text, binder types and facets
    /// the crate-local lane would hand its own session. That is sound exactly
    /// when the two environments agree about every declaration the goal can
    /// mention — which is what this checks, on the pair that actually exists
    /// at the seam. A caller runs it once, before grading anything, and treats
    /// a refusal as fail-closed: no cross-crate citation is graded, and the
    /// crate-local lane is untouched.
    ///
    /// # What is compared, exactly
    ///
    /// Two things, and neither is "every declaration in either environment":
    ///
    /// 1. every declaration THIS crate's ISLANDS own is present in `env` and
    ///    carries the same kernel payload there
    ///    ([`ExternProofRefusal::LocalSessionDisagrees`]); and
    /// 2. no declaration a DEPENDENCY owns is bound in `env` at all
    ///    ([`ExternProofRefusal::DependencyNameBoundLocally`]).
    ///
    /// (2) is what makes (1) enough. The constructor already refuses a
    /// dependency name that collides with this crate's islands or with the
    /// Rust callees its caller passed, but `env` carries admissions the
    /// constructor never saw — `declare_rust_callees` beyond that set, and the
    /// E6 program functions `admit_program_functions` adds after composition —
    /// and a goal on the E9 discharge path mentions exactly those. Checking
    /// that the composition adds no name `env` already binds closes the whole
    /// capture family at once, whatever the local name's origin, without this
    /// function having to enumerate the compiler's admission seams.
    ///
    /// A dependency's own composed-vs-alone agreement is a different check,
    /// the constructor's
    /// [`ExternProofRefusal::DependencyDeclarationsRebound`].
    pub fn reconcile_with_local_environment(
        &self,
        env: &Environment,
    ) -> Result<(), ExternProofRefusal> {
        // Refused before the payload comparison: a dependency answering for a
        // name this compilation already bound is a capture, not a disagreement
        // about this crate's own declarations, and naming it as the latter
        // would send an author to the wrong crate.
        for (unit, owned) in self.units.iter().zip(&self.unit_owned) {
            let names: Vec<String> = owned
                .iter()
                .filter(|name| env.get_const(name).is_some())
                .map(Name::to_string)
                .collect();
            if !names.is_empty() {
                return Err(ExternProofRefusal::DependencyNameBoundLocally {
                    id: unit.id.clone(),
                    names,
                });
            }
        }
        let mut present: BTreeSet<Name> = BTreeSet::new();
        let mut missing: Vec<String> = Vec::new();
        for name in &self.local_owned {
            if env.get_const(name).is_some() {
                present.insert(name.clone());
            } else {
                missing.push(name.to_string());
            }
        }
        let theirs = payload_digests(env, &present)?;
        let rebound = rebound_names(
            &self
                .local_payloads_composed
                .iter()
                .filter(|(name, _)| present.contains(*name))
                .map(|(name, digest)| (name.clone(), digest.clone()))
                .collect(),
            &theirs,
        );
        if missing.is_empty() && rebound.is_empty() {
            return Ok(());
        }
        Err(ExternProofRefusal::LocalSessionDisagrees { missing, rebound })
    }

    /// Disposition a bare CLAUSE identifier, for the seam that admits island
    /// definitions into a clause's facet table. See
    /// [`ClauseIdentifierDisposition`].
    #[must_use]
    pub fn clause_identifier(&self, name: &str) -> ClauseIdentifierDisposition {
        let kernel = Name::from_string(name);
        match self.bare_name_is_extern_owned(&kernel) {
            None => ClauseIdentifierDisposition::LocalOrPrelude,
            Some(id) => ClauseIdentifierDisposition::ExternOwned {
                unit: id.clone(),
                qualified_spelling: format!("{}.{name}", id.crate_name),
            },
        }
    }
}

/// Compose this crate's islands with its dependencies' transported Clean proof
/// material, or refuse with the crate named.
///
/// `local_islands` are this crate's island sources in AUTHORED order — the same
/// vector the crate-local batch is checked from. `rust_callees` are the SAME
/// callees the compiler declares before its own batch (`rust_callee_
/// declarations(tcx)`); pass an empty slice for a crate with none. `units` may
/// arrive in any order; they are sorted canonically here.
///
/// With `units` empty this runs exactly one batch over `local_islands` and
/// nothing else: an ordinary crate pays no extra kernel run for this lane.
pub fn compose_extern_proof_batch(
    units: Vec<ExternProofUnit>,
    local_islands: &[&str],
    rust_callees: &[RustCallee],
) -> Result<ExternProofComposition, ExternProofRefusal> {
    let local_kernel_version = clean_kernel::VERSION;

    // ── 1. canonical order FIRST: every refusal below must be the same one
    //       whichever order the dependency graph was walked in ──────────────
    let mut units = units;
    units.sort_by(|a, b| a.id.cmp(&b.id));

    // ── 2. preflight, before any kernel run ────────────────────────────────
    for unit in &units {
        if unit.id.crate_name.is_empty() {
            return Err(ExternProofRefusal::EmptyCrateName {
                stable_crate_id: unit.id.stable_crate_id,
            });
        }
        if unit.sources.is_empty() {
            return Err(ExternProofRefusal::NoSources { id: unit.id.clone() });
        }
        if unit.kernel_version != local_kernel_version {
            return Err(ExternProofRefusal::KernelSkew {
                id: unit.id.clone(),
                minted: unit.kernel_version.clone(),
                local: local_kernel_version.to_string(),
            });
        }
        // The transport agreement check, also before any elaboration: did the
        // bytes that arrived hash to what the dependency published for them?
        // Recomputed over the unit's OWN recorded kernel version, so this
        // question stays independent of the skew check above rather than
        // reporting a skew as a corrupted transport.
        let recomputed = unit_digest(unit)?;
        if recomputed != unit.declared_source_digest {
            return Err(ExternProofRefusal::TransportDigestMismatch {
                id: unit.id.clone(),
                declared: unit.declared_source_digest.clone(),
                recomputed,
            });
        }
    }
    for pair in units.windows(2) {
        if pair[0].id == pair[1].id {
            return Err(ExternProofRefusal::DuplicateUnit { id: pair[0].id.clone() });
        }
        if pair[0].id.crate_name == pair[1].id.crate_name {
            return Err(ExternProofRefusal::AmbiguousCrateName {
                crate_name: pair[0].id.crate_name.clone(),
                first: pair[0].id.stable_crate_id,
                second: pair[1].id.stable_crate_id,
            });
        }
    }
    let callee_names: BTreeSet<Name> =
        rust_callees.iter().map(|callee| Name::from_string(&callee.clean_name)).collect();

    // ── 3. the LOCAL-ONLY batch: the mint's environment, re-run ────────────
    let (mut local_session, local_before) = fresh_session(rust_callees)?;
    let local_batch = local_session.check_all(local_islands);
    if local_batch.is_rejected() || local_session.is_tainted() {
        return Err(ExternProofRefusal::LocalBatchRejected {
            diagnostics: batch_diagnostics(&local_batch),
        });
    }
    let local_env = local_session.environment().ok_or_else(|| ExternProofRefusal::PreludeInit {
        detail: "an accepted local island batch produced no environment".to_string(),
    })?;
    let local_owned: BTreeSet<Name> =
        owned_names(local_env).difference(&local_before).cloned().collect();
    let local_payloads = payload_digests(local_env, &local_owned)?;

    // The zero-unit fast path. One batch, no composition, no extra kernel run.
    if units.is_empty() {
        let sources: Vec<String> = local_islands.iter().map(|s| (*s).to_string()).collect();
        let composition_digest = composition_digest(local_kernel_version, &[], local_islands)?;
        let standin_imports = harvest_standins(&local_batch, 0, &[]);
        return Ok(ExternProofComposition {
            units,
            unit_digests: Vec::new(),
            unit_owned: Vec::new(),
            standin_imports,
            local_owned,
            local_payloads_composed: local_payloads,
            local_rust_callees: callee_names,
            local_island_offset: 0,
            sources,
            composition_digest,
            batch: local_batch,
            session: local_session,
        });
    }

    // ── 4. each unit STANDALONE, under this build's kernel ─────────────────
    //
    // No Rust callee is declared here: a dependency's islands may not name
    // this crate's Rust items, and a unit that declares a callee's bare name
    // is refused by name in step 5 rather than by a kernel duplicate.
    let mut unit_owned: Vec<BTreeSet<Name>> = Vec::with_capacity(units.len());
    let mut unit_payloads: Vec<BTreeMap<Name, String>> = Vec::with_capacity(units.len());
    let mut unit_digests: Vec<String> = Vec::with_capacity(units.len());
    for unit in &units {
        let (mut session, before) = fresh_session(&[])?;
        let sources: Vec<&str> = unit.sources.iter().map(String::as_str).collect();
        let batch = session.check_all(&sources);
        if batch.is_rejected() || session.is_tainted() {
            return Err(ExternProofRefusal::UnitDoesNotElaborate {
                id: unit.id.clone(),
                diagnostics: batch_diagnostics(&batch),
            });
        }
        let env = session.environment().ok_or_else(|| ExternProofRefusal::PreludeInit {
            detail: format!(
                "an accepted island batch for `{}` produced no environment",
                unit.id.crate_name
            ),
        })?;
        let owned: BTreeSet<Name> = owned_names(env).difference(&before).cloned().collect();
        unit_payloads.push(payload_digests(env, &owned)?);
        unit_owned.push(owned);
        unit_digests.push(unit_digest(unit)?);
    }

    // ── 5. collisions, named before the kernel can report them as a Clean
    //       duplicate pointing into a file the author never opened ──────────
    let mut owner: BTreeMap<&Name, DeclarationOrigin> = BTreeMap::new();
    for name in &local_owned {
        owner.insert(name, DeclarationOrigin::LocalCrate);
    }
    for name in &callee_names {
        owner.insert(name, DeclarationOrigin::LocalRustCallee);
    }
    for (unit, owned) in units.iter().zip(&unit_owned) {
        for name in owned {
            let origin = DeclarationOrigin::Dependency(unit.id.clone());
            if let Some(first) = owner.get(name) {
                return Err(ExternProofRefusal::DeclarationCollision {
                    name: name.to_string(),
                    first: first.clone(),
                    second: origin,
                });
            }
            owner.insert(name, origin);
        }
    }

    // ── 6. the COMPOSED batch ──────────────────────────────────────────────
    let mut sources: Vec<String> = Vec::new();
    for unit in &units {
        sources.extend(unit.sources.iter().cloned());
    }
    let local_island_offset = sources.len();
    sources.extend(local_islands.iter().map(|s| (*s).to_string()));

    let (mut session, before) = fresh_session(rust_callees)?;
    let borrowed: Vec<&str> = sources.iter().map(String::as_str).collect();
    let batch = session.check_all(&borrowed);
    if batch.is_rejected() || session.is_tainted() {
        return Err(ExternProofRefusal::ComposedBatchRejected {
            diagnostics: batch_diagnostics(&batch),
        });
    }
    let env = session.environment().ok_or_else(|| ExternProofRefusal::PreludeInit {
        detail: "an accepted composed batch produced no environment".to_string(),
    })?;
    let composed_owned: BTreeSet<Name> = owned_names(env).difference(&before).cloned().collect();

    // ── 7. the conservative-extension invariant, in BOTH directions ────────
    let mut expected: BTreeSet<Name> = local_owned.clone();
    for owned in &unit_owned {
        expected.extend(owned.iter().cloned());
    }
    check_name_additivity(&expected, &composed_owned)?;

    let composed_local_payloads = payload_digests(env, &local_owned)?;
    let rebound = rebound_names(&local_payloads, &composed_local_payloads);
    if !rebound.is_empty() {
        return Err(ExternProofRefusal::LocalDeclarationsRebound { names: rebound });
    }
    for (index, unit) in units.iter().enumerate() {
        let composed_unit_payloads = payload_digests(env, &unit_owned[index])?;
        let rebound = rebound_names(&unit_payloads[index], &composed_unit_payloads);
        if !rebound.is_empty() {
            return Err(ExternProofRefusal::DependencyDeclarationsRebound {
                id: unit.id.clone(),
                names: rebound,
            });
        }
    }

    let composition_digest =
        composition_digest(local_kernel_version, &unit_digests, local_islands)?;
    // One `(exclusive end index, unit id)` per unit, in composed order, so a
    // stand-in disclosure names the crate whose island wrote the `import`.
    let mut unit_ends: Vec<(usize, ExternProofUnitId)> = Vec::with_capacity(units.len());
    let mut at = 0usize;
    for unit in &units {
        at += unit.sources.len();
        unit_ends.push((at, unit.id.clone()));
    }
    let standin_imports = harvest_standins(&batch, local_island_offset, &unit_ends);
    Ok(ExternProofComposition {
        units,
        unit_digests,
        unit_owned,
        standin_imports,
        local_owned,
        local_payloads_composed: composed_local_payloads,
        local_rust_callees: callee_names,
        local_island_offset,
        sources,
        composition_digest,
        batch,
        session,
    })
}

/// The additive half of the conservative-extension invariant, as a function of
/// two name sets so it can be exercised directly: a refusal nothing can make
/// fire is not a control.
fn check_name_additivity(
    expected: &BTreeSet<Name>,
    composed: &BTreeSet<Name>,
) -> Result<(), ExternProofRefusal> {
    let unexpected: Vec<String> = composed.difference(expected).map(Name::to_string).collect();
    let missing: Vec<String> = expected.difference(composed).map(Name::to_string).collect();
    if unexpected.is_empty() && missing.is_empty() {
        return Ok(());
    }
    Err(ExternProofRefusal::NonAdditiveComposition { unexpected, missing })
}

/// The payload half, likewise: the names whose kernel payload is not
/// byte-identical in the two environments, sorted.
fn rebound_names(
    standalone: &BTreeMap<Name, String>,
    composed: &BTreeMap<Name, String>,
) -> Vec<String> {
    standalone
        .iter()
        .filter(|(name, digest)| composed.get(*name) != Some(*digest))
        .map(|(name, _)| name.to_string())
        .collect()
}

/// A fresh strict session with the kernel's builtin prologue materialized and
/// this crate's Rust callees declared, plus the baseline names taken AFTER
/// both. Every batch in this module starts from the same baseline, so the
/// deltas are comparable.
fn fresh_session(
    rust_callees: &[RustCallee],
) -> Result<(CleanIslandSession, BTreeSet<Name>), ExternProofRefusal> {
    let mut session = CleanIslandSession::new_for_source_batch()
        .map_err(|detail| ExternProofRefusal::PreludeInit { detail })?;
    session
        .declare_rust_callees(rust_callees)
        .map_err(|refusal| ExternProofRefusal::RustCalleeRefused { detail: refusal.to_string() })?;
    let before =
        owned_names(session.environment().ok_or_else(|| ExternProofRefusal::PreludeInit {
            detail: "a fresh session produced no environment".to_string(),
        })?);
    Ok((session, before))
}

/// Every island failure of a batch, keeping the island index and the
/// island-relative offsets the compiler's span arithmetic needs.
fn batch_diagnostics(batch: &CleanIslandBatch) -> Vec<ExternProofDiagnostic> {
    let mut lines: Vec<ExternProofDiagnostic> = Vec::new();
    for cycle in &batch.cycles {
        let site = cycle.sites.first();
        lines.push(ExternProofDiagnostic {
            island: site.map_or(0, |site| site.island),
            start: site.map_or(0, |site| site.start),
            end: site.map_or(0, |site| site.end),
            message: format!("dependency cycle: {} — {}", cycle.render(), cycle.message),
        });
    }
    for (index, outcome) in batch.outcomes.iter().enumerate() {
        for error in &outcome.errors {
            lines.push(ExternProofDiagnostic {
                island: index,
                start: error.start,
                end: error.end,
                message: error.message.clone(),
            });
        }
    }
    lines
}

/// Stand-in disclosures from the batch whose environment was ACCEPTED, with
/// each island attributed to the crate that wrote it. `unit_ends` holds one
/// `(exclusive end index, unit id)` per unit, in composed order.
fn harvest_standins(
    batch: &CleanIslandBatch,
    local_island_offset: usize,
    unit_ends: &[(usize, ExternProofUnitId)],
) -> Vec<ExternProofStandinImport> {
    let mut out = Vec::new();
    for (island, outcome) in batch.outcomes.iter().enumerate() {
        let origin = if island >= local_island_offset {
            DeclarationOrigin::LocalCrate
        } else {
            unit_ends
                .iter()
                .find(|(end, _)| island < *end)
                .map_or(DeclarationOrigin::LocalCrate, |(_, id)| {
                    DeclarationOrigin::Dependency(id.clone())
                })
        };
        for import in &outcome.standin_imports {
            out.push(ExternProofStandinImport {
                origin: origin.clone(),
                island,
                import: import.clone(),
            });
        }
    }
    out
}

/// Per-declaration kernel payload digest: the full `ConstantInfo` plus the
/// inductive / constructor / recursor / quotient rows, exactly the tuple the
/// standalone `.lean` lane binds — not just the name.
fn payload_digests(
    env: &Environment,
    names: &BTreeSet<Name>,
) -> Result<BTreeMap<Name, String>, ExternProofRefusal> {
    let mut digests = BTreeMap::new();
    for name in names {
        let info = env.get_const(name).ok_or_else(|| ExternProofRefusal::PayloadUnreadable {
            detail: format!("the environment enumerated `{name}` but has no declaration for it"),
        })?;
        let row = (
            "trust.clean.extern-proof-payload/v1",
            name.to_string(),
            info,
            env.get_inductive(name),
            env.get_constructor(name),
            env.get_recursor(name),
            env.quotients().find(|value| &value.name == name),
        );
        let digest =
            canonical_json_sha256(&row).map_err(|error| ExternProofRefusal::PayloadUnreadable {
                detail: format!("cannot bind the kernel payload of `{name}`: {error}"),
            })?;
        digests.insert(name.clone(), digest);
    }
    Ok(digests)
}

/// The transport digest over one crate's Clean proof material: canonical-JSON
/// SHA-256 of `(tag, crate_name, stable_crate_id, kernel_version, sources)`.
///
/// **One function, both sides.** The producing compiler records this value
/// beside the bytes it transports; the consuming compiler recomputes it over
/// the bytes that arrived and refuses
/// [`ExternProofRefusal::TransportDigestMismatch`] when they differ. A digest
/// computed by two spellings of the same idea is a digest that disagrees at the
/// first refactor, so there is exactly one spelling and it lives here.
///
/// It identifies inputs. It grants nothing: a unit whose digest matches is
/// re-elaborated and kernel-checked locally exactly like one whose digest is
/// unknown, and no path anywhere accepts a declaration on a matching hash.
pub fn extern_proof_source_digest(
    crate_name: &str,
    stable_crate_id: u64,
    kernel_version: &str,
    sources: &[String],
) -> Result<String, String> {
    canonical_json_sha256(&(
        "trust.clean.extern-proof-unit/v1",
        crate_name,
        stable_crate_id,
        kernel_version,
        sources,
    ))
    .map_err(|error| error.to_string())
}

/// [`extern_proof_source_digest`] over a unit, under the unit's OWN recorded
/// kernel version — so an accepted composition's `unit_digest(i)` is exactly
/// the string the dependency published, and the two can be compared as
/// identities anywhere downstream.
fn unit_digest(unit: &ExternProofUnit) -> Result<String, ExternProofRefusal> {
    extern_proof_source_digest(
        &unit.id.crate_name,
        unit.id.stable_crate_id,
        &unit.kernel_version,
        &unit.sources,
    )
    .map_err(|error| ExternProofRefusal::PayloadUnreadable {
        detail: format!("cannot bind the proof unit of `{}`: {error}", unit.id.crate_name),
    })
}

/// The composition's identity. It folds the PER-UNIT digests rather than the
/// flattened source vector, so two different unit→source partitions that
/// concatenate to the same bytes have different identities.
fn composition_digest(
    kernel_version: &str,
    unit_digests: &[String],
    local_islands: &[&str],
) -> Result<String, ExternProofRefusal> {
    canonical_json_sha256(&(
        "trust.clean.extern-proof-composition/v2",
        kernel_version,
        unit_digests,
        local_islands,
    ))
    .map_err(|error| ExternProofRefusal::PayloadUnreadable {
        detail: format!("cannot bind the cross-crate proof composition: {error}"),
    })
}

#[cfg(test)]
mod tests;
