// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust-symbols` — **one** symbol graph, written by **two** producers.
//!
//! Decision of record:
//! `docs/design/2026-08-04-two-language-compiler-architecture.md` §3.
//! Increment: **I1** (header-first, two-phase Clean environment; one parse; one
//! graph; source-order independent; **zero values produced, zero CALL**).
//!
//! Trust compiles two authoritative languages. A Rust `fn` and a Clean `def`
//! are not two kinds of thing that happen to live in one file — they are one
//! kind of thing with two spellings, and `crate::m::f` and `Crate.m.f` denote
//! the *same* segment sequence. This crate is that sentence made a type, so
//! the property is delivered by structure rather than by a resolver special
//! case.
//!
//! # The dependency list is the soundness argument
//!
//! This crate depends on `trust-types` and on **nothing else**. It cannot name
//! `clean-kernel`, `clean-elab`, `clean-parser`, or any `rustc_*` crate.
//!
//! That poverty is bought with the build graph, not with a comment. The
//! strongest claim in the two-language compiler is
//! [`KernelStatus::KernelChecked`] — "the Clean CIC kernel re-checked this
//! declaration's own obligation". A crate that can *spell* that claim and also
//! *run a parser* is one careless line away from a parse-time success implying
//! a kernel-checked declaration, which is the binding prohibition this whole
//! increment is organised around. Here it is not a review failure. It does not
//! compile: there is nothing in scope to parse with, and the only route to the
//! claim is [`KernelAuthority::kernel_checked`], which is sealed.
//!
//! Corollary, stated so it is not eroded later: **do not add a second
//! dependency to this crate.** If something here needs a kernel type, the
//! answer is that the thing belongs in `trust-clean-env`, not that this crate
//! grows an edge.
//!
//! # There is deliberately no `serde` here either
//!
//! Not an omission. `#[derive(Deserialize)]` on [`KernelStatus`] would be a
//! public, unaudited constructor for [`KernelStatus::KernelChecked`] reachable
//! from any byte string — it would defeat the private constructor of §5(a)
//! completely, and it would do it silently, because a derive looks like
//! plumbing. The cross-crate wire unit is I7's problem and I7's decision is
//! already recorded: the wire unit is a **verdict digest** (kernel version,
//! environment digest, axiom closure, carrier decision, defeq certificate)
//! re-admitted on import — never a status deserialized back into standing.
//!
//! # What is here
//!
//! | Type | Role |
//! |---|---|
//! | [`Segment`], [`SegmentPath`] | The producer-neutral path. `crate::m::f` and `Crate.m.f` parse to one value. |
//! | [`Sort`], [`Namespace`] | Multi-sorted identity. A flat namespace would reject valid Rust (`mod m` beside `fn m`). |
//! | [`Producer`] | Which language wrote the header. Recorded, never authority. |
//! | [`Capability`], [`CarrierEvidence`] | PROOF/CALL. At I1 nothing can reach `Call`. |
//! | [`TermDigest`] | Identity of the checked term. |
//! | [`Assumption`], [`AxiomClosure`] | The disclosure surface. Non-empty ⇒ never `Certified`. |
//! | [`KernelStatus`], [`KernelVerdict`] | Parsed / Elaborated / Reflected / KernelChecked. |
//! | [`Certification`] | The composite verdict. Not an enum variant anyone can stamp. |
//! | [`KernelAuthority`], [`CicKernelRecheck`] | The one sealed seam. |
//! | [`SymbolHeader`], [`SymbolGraph`] | Phase 1 declares every header; phase 2 elaborates. |
//!
//! # Fail-closed defaults, listed
//!
//! * [`AxiomClosure::default`] is [`AxiomClosure::unrecorded`], which can never
//!   be `Certified`. A `#[derive(Default)]` downstream therefore cannot mint an
//!   empty closure by omission.
//! * [`SymbolHeader::new`] starts at [`Capability::Proof`] and
//!   [`KernelStatus::Parsed`]. Both escalations are explicit.
//! * [`AxiomClosure::merge`] is *absorbing* on `unrecorded`: an audited-empty
//!   closure merged with an unrecorded one is unrecorded. A transitive closure
//!   is only as good as its worst component.
//! * Every refusal in this crate names the fix **with options** (author ruling
//!   v7/D3). "Unsupported" with no next step is a defect; the reader is an AI
//!   programmer.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------

/// The canonical spelling of the current-crate root segment.
///
/// Rust spells it `crate`; Clean spells it `Crate`. Both parse to this.
pub const CRATE_ROOT: &str = "crate";

/// Clean's spelling of [`CRATE_ROOT`].
pub const CRATE_ROOT_CLEAN: &str = "Crate";

/// The Rust path separator.
pub const RUST_SEP: &str = "::";

/// The Clean path separator.
pub const CLEAN_SEP: &str = ".";

/// A single, separator-free path component.
///
/// The smart constructor is the whole point. If a segment could contain a
/// separator then `crate::["m::f"]` and `crate::m::f` would render identically
/// and compare unequal — two symbols with one printed name, which is exactly
/// how a diagnostic ends up naming the wrong declaration and how a duplicate
/// check ends up not firing.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Segment(String);

impl Segment {
    /// Build a segment, rejecting anything that could be confused with a path.
    ///
    /// # Errors
    ///
    /// [`PathError::EmptySegment`] for an empty or whitespace-only component,
    /// [`PathError::SeparatorInSegment`] for a component carrying `.`, `:` or
    /// internal whitespace.
    pub fn new(text: impl Into<String>) -> Result<Self, PathError> {
        let text = text.into();
        if text.trim().is_empty() {
            return Err(PathError::EmptySegment);
        }
        if let Some(bad) = text.chars().find(|c| *c == '.' || *c == ':' || c.is_whitespace()) {
            return Err(PathError::SeparatorInSegment { segment: text, offender: bad });
        }
        Ok(Self(text))
    }

    /// The segment text.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Whether this is the canonical current-crate root.
    #[must_use]
    pub fn is_crate_root(&self) -> bool {
        self.0 == CRATE_ROOT
    }
}

impl fmt::Display for Segment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A hierarchical, producer-neutral symbol path.
///
/// One value, two spellings. [`SegmentPath::parse_rust`] and
/// [`SegmentPath::parse_clean`] agree by construction, which is what makes
/// §4.1.1's "same segment sequence" a fact about the type rather than a policy
/// the resolver has to remember.
///
/// # Boundary, stated rather than hidden
///
/// Only the *current crate's* root is aliased (`crate` ⟷ `Crate`). A leading
/// segment that is some other crate's name is taken literally in both
/// spellings, so `foo::m::f` and `Foo.m.f` are two different paths. That is
/// fail-closed (they are never conflated) and it is honest: cross-crate root
/// identity is I7's problem, together with the rest of the import story.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SegmentPath {
    segments: Vec<Segment>,
}

impl SegmentPath {
    /// Build a path from already-validated segments.
    ///
    /// # Errors
    ///
    /// [`PathError::EmptyPath`] if the iterator is empty. A symbol with no
    /// segments has no name, and an unnameable symbol cannot be disclosed.
    pub fn from_segments(
        segments: impl IntoIterator<Item = Segment>,
    ) -> Result<Self, PathError> {
        let segments: Vec<Segment> = segments.into_iter().collect();
        if segments.is_empty() {
            return Err(PathError::EmptyPath);
        }
        Ok(Self { segments })
    }

    /// Parse the Rust spelling, e.g. `crate::m::f`.
    ///
    /// # Errors
    ///
    /// Any [`PathError`] the component segments raise.
    pub fn parse_rust(text: &str) -> Result<Self, PathError> {
        Self::parse(text, RUST_SEP)
    }

    /// Parse the Clean spelling, e.g. `Crate.m.f`.
    ///
    /// # Errors
    ///
    /// Any [`PathError`] the component segments raise.
    pub fn parse_clean(text: &str) -> Result<Self, PathError> {
        Self::parse(text, CLEAN_SEP)
    }

    fn parse(text: &str, sep: &str) -> Result<Self, PathError> {
        if text.trim().is_empty() {
            return Err(PathError::EmptyPath);
        }
        let mut segments = Vec::new();
        for (index, raw) in text.split(sep).enumerate() {
            // Root aliasing is positional: only the LEADING component may be a
            // crate-root spelling. A `Crate` deeper in the path is an ordinary
            // namespace called `Crate`, and normalizing it would silently merge
            // two distinct symbols.
            let normalized =
                if index == 0 && (raw == CRATE_ROOT || raw == CRATE_ROOT_CLEAN) {
                    CRATE_ROOT
                } else {
                    raw
                };
            segments.push(Segment::new(normalized)?);
        }
        Self::from_segments(segments)
    }

    /// Extend this path by one component — the "parented to the enclosing Rust
    /// module" rule of §4.
    #[must_use]
    pub fn child(&self, segment: Segment) -> Self {
        let mut segments = self.segments.clone();
        segments.push(segment);
        Self { segments }
    }

    /// The enclosing path, or `None` at the root.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        if self.segments.len() <= 1 {
            return None;
        }
        let mut segments = self.segments.clone();
        segments.pop();
        Some(Self { segments })
    }

    /// The final component.
    #[must_use]
    pub fn leaf(&self) -> &Segment {
        // `from_segments` rejects the empty path, so this cannot fail.
        &self.segments[self.segments.len() - 1]
    }

    /// The components, root first.
    #[must_use]
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }

    /// Render the Rust spelling.
    #[must_use]
    pub fn render_rust(&self) -> String {
        self.render(RUST_SEP, CRATE_ROOT)
    }

    /// Render the Clean spelling.
    #[must_use]
    pub fn render_clean(&self) -> String {
        self.render(CLEAN_SEP, CRATE_ROOT_CLEAN)
    }

    fn render(&self, sep: &str, root: &str) -> String {
        let mut out = String::new();
        for (index, segment) in self.segments.iter().enumerate() {
            if index > 0 {
                out.push_str(sep);
            }
            if index == 0 && segment.is_crate_root() {
                out.push_str(root);
            } else {
                out.push_str(segment.as_str());
            }
        }
        out
    }
}

impl fmt::Display for SegmentPath {
    /// Renders the **Rust** spelling. Diagnostics that address a Clean author
    /// should call [`SegmentPath::render_clean`] explicitly rather than relying
    /// on this.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render_rust())
    }
}

/// Why a path or segment was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PathError {
    /// A path with no components.
    EmptyPath,
    /// A component with no text.
    EmptySegment,
    /// A component carrying a path separator or whitespace.
    SeparatorInSegment {
        /// The offending component.
        segment: String,
        /// The character that made it ambiguous.
        offender: char,
    },
}

impl fmt::Display for PathError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyPath => write!(
                f,
                "a symbol path must have at least one segment; an unnameable \
                 symbol cannot be disclosed in a diagnostic.\n\
                 options: (1) pass the enclosing module path plus the \
                 declaration name; (2) for a crate-root declaration pass \
                 `crate::<name>` (Rust) or `Crate.<name>` (Clean)"
            ),
            Self::EmptySegment => write!(
                f,
                "a path segment must have text.\n\
                 options: (1) drop the empty component; (2) if the input came \
                 from splitting a rendered path, check it was split on the \
                 right separator — Rust uses `::`, Clean uses `.`"
            ),
            Self::SeparatorInSegment { segment, offender } => write!(
                f,
                "path segment `{segment}` contains `{offender}`, which would \
                 make it print as more than one segment; two symbols would \
                 then share one printed name.\n\
                 options: (1) build the path with `SegmentPath::parse_rust` / \
                 `parse_clean`, which split first; (2) call \
                 `SegmentPath::child` once per component; (3) if the \
                 identifier really contains that character, it is not \
                 expressible in this graph — say so at the declaration site \
                 rather than encoding it"
            ),
        }
    }
}

impl std::error::Error for PathError {}

// ---------------------------------------------------------------------------
// Sorts, namespaces, producers
// ---------------------------------------------------------------------------

/// What kind of thing a symbol is.
///
/// Decision of record §3. Multi-sorted rather than flat because **a flat
/// namespace rejects valid Rust**: `mod m` and `fn m` coexist in one module,
/// and so do `struct Foo` and `fn Foo`. Collapsing them would make Trust
/// reject programs stock rustc accepts, which is a release-gate failure, not a
/// design simplification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Sort {
    /// A module or a Clean `namespace`.
    Module,
    /// A type: Rust `struct`/`enum`/`type`, Clean `inductive`/`structure`.
    Type,
    /// A value-level definition: Rust `fn`/`const`/`static`, Clean `def`.
    Term,
    /// A proposition and its proof: Clean `theorem`/`example`/`axiom`.
    ///
    /// Deliberately **not** in the value namespace. Rust cannot cite a theorem
    /// in a value position, which is why §2 rejects a new `DefKind` for it.
    Prop,
    /// A trait / type class.
    Trait,
    /// An impl block or instance. Anonymous; never name-resolved.
    Impl,
}

impl Sort {
    /// The namespace this sort competes in.
    ///
    /// Two headers collide iff they share a path **and** a namespace — that is
    /// the E0428 rule, and it is why the graph is keyed on
    /// [`SymbolId`] rather than on the path alone.
    #[must_use]
    pub fn namespace(self) -> Namespace {
        match self {
            // Rust puts modules, types and traits in one namespace: `mod Foo`
            // beside `struct Foo` is E0428 today and must stay E0428.
            Self::Module | Self::Type | Self::Trait => Namespace::Type,
            Self::Term => Namespace::Value,
            Self::Prop => Namespace::Proof,
            Self::Impl => Namespace::Impl,
        }
    }

    /// The stable wire name used in diagnostics and evidence rows.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Module => "module",
            Self::Type => "type",
            Self::Term => "term",
            Self::Prop => "prop",
            Self::Trait => "trait",
            Self::Impl => "impl",
        }
    }
}

/// The namespaces a path can be resolved in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Namespace {
    /// Modules, types, traits.
    Type,
    /// Values. The only namespace a rustc `DefId` is minted into at I5.
    Value,
    /// Propositions. PROOF-side only; never reachable from a Rust call site.
    Proof,
    /// Impls and instances. Anonymous.
    Impl,
}

impl Namespace {
    /// The stable wire name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Type => "type",
            Self::Value => "value",
            Self::Proof => "proof",
            Self::Impl => "impl",
        }
    }
}

/// Which producer wrote a header.
///
/// Recorded for diagnostics and for the I5 parity fixture. **It is not
/// authority**: a Clean-produced header is not more trusted than a Rust one,
/// and neither is trusted at all until [`KernelStatus`] says otherwise.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Producer {
    /// A Rust item.
    Rust,
    /// A Clean declaration, from an island or (at I8) a `.clean` unit.
    Clean,
}

impl Producer {
    /// The stable wire name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Rust => "rust",
            Self::Clean => "clean",
        }
    }
}

// ---------------------------------------------------------------------------
// Capability
// ---------------------------------------------------------------------------

/// The visibility axis: PROOF is total observer capability, CALL is ordinary.
///
/// This is **not** built on `trust_types::frontend_firewall::ProofRole`, and
/// §2 of the decision doc records why: `ProofRole` is a provenance-vs-belief
/// axis ("which side of the turnstile the term lands on"), not a visibility
/// axis. Merging them would make the firewall's meaning depend on how good the
/// extractor happened to be that day.
///
/// `Call` subsumes `Proof`: a callable symbol is also observable. The converse
/// is the firewall.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Capability {
    /// Nameable from proof contexts only.
    Proof,
    /// Nameable from ordinary Rust code, and therefore able to **produce a
    /// value**. A divergence here is a wrong binary, not a failed proof.
    Call,
}

impl Capability {
    /// Whether holding `self` permits a use that requires `required`.
    #[must_use]
    pub fn permits(self, required: Self) -> bool {
        match (self, required) {
            (Self::Call, _) => true,
            (Self::Proof, Self::Proof) => true,
            (Self::Proof, Self::Call) => false,
        }
    }

    /// The stable wire name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Proof => "proof",
            Self::Call => "call",
        }
    }
}

/// Evidence that a Clean type has a faithful Rust carrier.
///
/// Shaped deliberately like `SingleWriterEvidence` in `trust-vcgen`, for the
/// reason recorded in `CLAUDE.md`: **an unverified caller promise may not
/// shrink the state space a proof is taken over**, and it may not mint a
/// capability either. A carrier that is merely *declared* does not grant CALL;
/// only a carrier whose representation-faithfulness obligation has been
/// discharged does.
///
/// **Nothing constructs [`CarrierEvidence::Total`] at I1.** `trust-clean-carrier`
/// (I4) is the seam it plugs into, and I4 lands before any `DefId` is minted
/// precisely so that `Nat → u64` cannot be blessed by a defeq check that is
/// already true of a wrapping binary (§5(b)).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[non_exhaustive]
pub enum CarrierEvidence {
    /// No carrier. The default, and the only state reachable at I1.
    #[default]
    None,
    /// A carrier was asserted by a caller and not proved. Grants nothing.
    Declared,
    /// A carrier that is total on its domain, with the
    /// representation-faithfulness obligation discharged.
    Total,
}

// ---------------------------------------------------------------------------
// Term digest
// ---------------------------------------------------------------------------

/// Identity of the exact term the kernel re-checked.
///
/// Hashing goes through `trust_types::digest`, which is the repo's single
/// digest implementation on purpose — "two subsystems that disagree about the
/// bytes of the same object silently disagree about whether a proof applies".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermDigest(String);

impl TermDigest {
    /// Digest of a serialized term.
    #[must_use]
    pub fn of_bytes(bytes: &[u8]) -> Self {
        Self(trust_types::digest::stable_sha256_hex(bytes))
    }

    /// Adopt a digest already computed by the producer.
    ///
    /// # Errors
    ///
    /// [`DigestError`] if `hex` is not 64 lowercase hex characters. A digest
    /// that is not in canonical form would compare unequal to the same term
    /// hashed here, which silently turns a cache hit into a cache miss and, at
    /// I7, an accepted certificate into a rejected one.
    pub fn from_hex(hex: &str) -> Result<Self, DigestError> {
        if hex.len() != 64 || !hex.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(DigestError { got: hex.to_string() });
        }
        Ok(Self(hex.to_string()))
    }

    /// The canonical lowercase hex rendering.
    #[must_use]
    pub fn as_hex(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for TermDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A digest that was not in canonical form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigestError {
    /// What was supplied.
    pub got: String,
}

impl fmt::Display for DigestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "`{}` is not a canonical term digest (expected 64 lowercase hex \
             characters).\n\
             options: (1) build it with `TermDigest::of_bytes` over the \
             serialized term; (2) lowercase an upper-case hex string before \
             adopting it; (3) if this came off the wire, re-check the term \
             rather than repairing the digest — I7's wire unit is a verdict \
             digest that is re-admitted, never a hash that is trusted",
            self.got
        )
    }
}

impl std::error::Error for DigestError {}

// ---------------------------------------------------------------------------
// Axiom closure
// ---------------------------------------------------------------------------

/// What kind of assumption a closure member is.
///
/// The distinction is load-bearing and it is why this crate does not simply
/// reuse `trust_types::grade::AxiomClosure`: that type carries an untyped
/// `BTreeSet<String>`, so a consumer cannot tell "this proof reached `sorry`"
/// from "this proof cites a domain axiom the author stated on purpose". Those
/// are different conversations with the author, and v7/D3 says a refusal has to
/// name the fix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum AssumptionKind {
    /// A trust-envelope marker: `sorry`, `sorryAx`, `trustedArith`,
    /// `trustedAy`. The proof is incomplete or was delegated to a solver.
    TrustMarker,
    /// A non-foundational axiom the author stated. Mathematically it may well
    /// be true; the kernel did not prove it.
    DomainAxiom,
}

impl AssumptionKind {
    /// The stable wire name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::TrustMarker => "trust-marker",
            Self::DomainAxiom => "domain-axiom",
        }
    }

    /// Human phrasing for a diagnostic.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::TrustMarker => "trust marker",
            Self::DomainAxiom => "domain axiom",
        }
    }
}

/// One named assumption in a declaration's transitive definitional closure.
///
/// # Why this crate does not classify names itself
///
/// The authoritative list of trust markers lives in exactly one place —
/// `clean_kernel::env::axiom_audit::is_trust_marker` — and it has already been
/// wrong once in a way that mattered (`sorryAx` was mistakenly whitelisted as
/// foundational, so theorems reaching `sorry` reported `Constructive`). A copy
/// of that list here would be a second place to be wrong, in a crate that
/// cannot be corrected by the kernel's own tests. The **producer** classifies;
/// this crate only carries.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assumption {
    // Name first so the derived `Ord` sorts by name — the disclosure order.
    name: String,
    kind: AssumptionKind,
}

impl Assumption {
    /// A trust-envelope marker reached by the proof.
    ///
    /// # Errors
    ///
    /// [`AssumptionNameError`] for an empty name. An assumption that cannot be
    /// named cannot be disclosed by name, and the binding rule is that they
    /// **are** disclosed by name — so an unnameable one is refused rather than
    /// carried.
    pub fn trust_marker(name: impl Into<String>) -> Result<Self, AssumptionNameError> {
        Self::new(name, AssumptionKind::TrustMarker)
    }

    /// A non-foundational axiom the proof rests on.
    ///
    /// # Errors
    ///
    /// [`AssumptionNameError`] for an empty name.
    pub fn domain_axiom(name: impl Into<String>) -> Result<Self, AssumptionNameError> {
        Self::new(name, AssumptionKind::DomainAxiom)
    }

    fn new(name: impl Into<String>, kind: AssumptionKind) -> Result<Self, AssumptionNameError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(AssumptionNameError);
        }
        Ok(Self { name, kind })
    }

    /// The assumption's name, as the kernel spells it.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Whether this is a trust marker or a domain axiom.
    #[must_use]
    pub fn kind(&self) -> AssumptionKind {
        self.kind
    }
}

impl fmt::Display for Assumption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{}` ({})", self.name, self.kind.label())
    }
}

/// An assumption with no name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssumptionNameError;

impl fmt::Display for AssumptionNameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "an assumption must carry the kernel's name for it: a non-empty \
             axiom closure is disclosed BY NAME, so an unnameable member \
             cannot be recorded.\n\
             options: (1) pass the `Name` the kernel returned from its \
             transitive audit; (2) if the producer genuinely does not know \
             the names, record the closure as `AxiomClosure::unrecorded()` — \
             which is never `Certified` — instead of inventing a blank one"
        )
    }
}

impl std::error::Error for AssumptionNameError {}

/// The `axiom` / `sorry` / `trusted*` constants in a declaration's transitive
/// definitional closure.
///
/// **Non-empty means never `Certified`, and the names are retrievable for
/// disclosure.** That is the single sentence this type exists to enforce; §5(a)
/// of the decision doc calls the alternative "the cleanest false-`Certified`
/// available" — a user writes `axiom key_lemma : …`, the kernel honestly
/// re-checks the dependent theorem, and the compiler's strongest verdict lands
/// on a proposition whose proof bottoms out in a user assumption.
///
/// # `unrecorded` is not `empty`
///
/// Three states, not two:
///
/// | State | Constructor | Certifiable |
/// |---|---|---|
/// | audited, nothing found | [`AxiomClosure::audited`] with an empty iterator | yes |
/// | audited, assumptions found | [`AxiomClosure::audited`] | **no**, and they are named |
/// | never audited | [`AxiomClosure::unrecorded`] (the [`Default`]) | **no** |
///
/// The third row is the one that gets skipped, and it is exactly the gap
/// measured in this area: `clean_kernel`'s `axiom_deps(&Name)` returns a
/// *name list* and never re-typechecks, so it cannot see `StructuralOnly`,
/// `MissingValue` or `NonCanonicalFoundation` — a structurally-inserted theorem
/// has an empty `axiom_deps` and is not thereby clean. **A producer holding
/// only `axiom_deps` must pass [`AxiomClosure::unrecorded`].**
/// [`AxiomClosure::audited`] means `Environment::audit_certification`
/// (equivalently `cert_meter::grade`) returned a positive grade for this
/// declaration's own `(goal, term)` pair.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct AxiomClosure {
    /// `false` is "the producing pipeline did not record closure information",
    /// which must never soften into "empty" — the same rule
    /// `trust_types::grade::AxiomClosure::Unrecorded` records for imports.
    recorded: bool,
    assumptions: BTreeSet<Assumption>,
}

impl AxiomClosure {
    /// The closure was not computed. Never `Certified`. This is the
    /// [`Default`], so an omission fails closed.
    #[must_use]
    pub fn unrecorded() -> Self {
        Self { recorded: false, assumptions: BTreeSet::new() }
    }

    /// The closure as a full certification audit reported it.
    ///
    /// The name is deliberately loud. Passing an empty iterator here is an
    /// assertion that the audit ran and found nothing — the only route to
    /// `Certified` in this crate. If the audit did not run, call
    /// [`AxiomClosure::unrecorded`].
    #[must_use]
    pub fn audited(assumptions: impl IntoIterator<Item = Assumption>) -> Self {
        Self { recorded: true, assumptions: assumptions.into_iter().collect() }
    }

    /// Whether an audit was performed at all.
    #[must_use]
    pub fn is_recorded(&self) -> bool {
        self.recorded
    }

    /// Whether the audit ran and found no assumptions.
    ///
    /// Note the conjunction: an unrecorded closure holds no assumptions but is
    /// **not** empty in this sense, and this method is the one certification
    /// consults.
    #[must_use]
    pub fn is_audited_empty(&self) -> bool {
        self.recorded && self.assumptions.is_empty()
    }

    /// The assumptions, sorted by name — the disclosure order.
    pub fn assumptions(&self) -> impl Iterator<Item = &Assumption> {
        self.assumptions.iter()
    }

    /// Just the names, sorted. The disclosure surface the binding rule names.
    #[must_use]
    pub fn names(&self) -> Vec<&str> {
        self.assumptions.iter().map(Assumption::name).collect()
    }

    /// The trust-envelope members (`sorry` and friends).
    pub fn trust_markers(&self) -> impl Iterator<Item = &Assumption> {
        self.assumptions.iter().filter(|a| a.kind == AssumptionKind::TrustMarker)
    }

    /// The domain-axiom members.
    pub fn domain_axioms(&self) -> impl Iterator<Item = &Assumption> {
        self.assumptions.iter().filter(|a| a.kind == AssumptionKind::DomainAxiom)
    }

    /// Union of two closures — a declaration's own closure joined with a
    /// dependency's.
    ///
    /// **Absorbing on `unrecorded`.** If either side was never audited the
    /// result is unrecorded, because a transitive closure is only as good as
    /// its worst component: joining an audited-empty closure with an unaudited
    /// one and reporting "empty" is precisely how a dependency's `sorry`
    /// disappears from a disclosure.
    #[must_use]
    pub fn merge(&self, other: &Self) -> Self {
        if !self.recorded || !other.recorded {
            return Self::unrecorded();
        }
        let mut assumptions = self.assumptions.clone();
        assumptions.extend(other.assumptions.iter().cloned());
        Self { recorded: true, assumptions }
    }

    /// Project onto the existing five-axis grade record's axiom axis.
    ///
    /// Total, and never widening: `unrecorded` maps to `Unrecorded` (not
    /// `Empty`), an audited-empty closure to `Empty`, and anything else to
    /// `Named`. The projection exists so this type and
    /// `trust_types::grade::GradeRecord::is_certified` cannot disagree about
    /// the same declaration; the agreement is pinned by a test.
    #[must_use]
    pub fn to_grade_axis(&self) -> trust_types::grade::AxiomClosure {
        use trust_types::grade::AxiomClosure as Axis;
        if !self.recorded {
            return Axis::Unrecorded;
        }
        if self.assumptions.is_empty() {
            return Axis::Empty;
        }
        Axis::Named(self.assumptions.iter().map(|a| a.name.clone()).collect())
    }
}

// ---------------------------------------------------------------------------
// Kernel status
// ---------------------------------------------------------------------------

/// The payload of [`KernelStatus::KernelChecked`].
///
/// **Its fields are private and it has no public constructor.** Outside this
/// crate the only way to obtain one is [`KernelAuthority::kernel_checked`], and
/// [`KernelAuthority`] is sealed. That is the §5(a) "typed" layer: a grep for a
/// naming convention is an audit procedure; a private constructor is an
/// invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelVerdict {
    digest: TermDigest,
    closure: AxiomClosure,
}

impl KernelVerdict {
    /// Identity of the term the kernel re-checked.
    #[must_use]
    pub fn digest(&self) -> &TermDigest {
        &self.digest
    }

    /// The assumptions the re-checked proof rests on.
    #[must_use]
    pub fn closure(&self) -> &AxiomClosure {
        &self.closure
    }
}

/// How far a symbol has got, and on whose authority.
///
/// The states are a ladder in *evidence*, not a workflow: nothing here says a
/// declaration must pass through `Elaborated` on its way anywhere. Consumers
/// should ask [`KernelStatus::certification`] rather than matching, which is
/// also why the enum is `#[non_exhaustive]`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum KernelStatus {
    /// The surface syntax parsed. Phase 1 of the header-first environment
    /// leaves every header here.
    ///
    /// **A successful parse buys a name and a sort. It never buys a
    /// proposition** — and at I5 it does not even buy a name in the value
    /// namespace.
    #[default]
    Parsed,
    /// Elaborated to a core term. Not re-checked; the elaborator is not the
    /// kernel, and an elaborator bug is a wrong term, not a caught one.
    Elaborated,
    /// A **reflected carrier** — a Rust item projected into the Clean
    /// environment by `crates/trust-clean`'s R functor (I2).
    ///
    /// Distinct from [`KernelStatus::KernelChecked`] on purpose: the
    /// reflection is TCB (`docs/TCB.md` row "Clean-origin faithfulness
    /// reflection"), and the status has to say so rather than let a reflected
    /// carrier be cited where a kernel-checked declaration is required. I2's
    /// control is exactly that refusal.
    Reflected,
    /// The Clean CIC kernel re-checked this declaration's own obligation.
    ///
    /// The strongest status in the compiler, and still **not** the same thing
    /// as `Certified`: see [`KernelStatus::certification`], which also
    /// consults the axiom closure.
    KernelChecked(KernelVerdict),
}

impl KernelStatus {
    /// Whether the kernel re-checked this declaration at all.
    ///
    /// Deliberately separate from [`Certification::is_certified`]: `true` here
    /// with a non-empty closure is the assumption-bearing row.
    #[must_use]
    pub fn is_kernel_checked(&self) -> bool {
        matches!(self, Self::KernelChecked(_))
    }

    /// The verdict payload, if any.
    #[must_use]
    pub fn verdict(&self) -> Option<&KernelVerdict> {
        match self {
            Self::KernelChecked(verdict) => Some(verdict),
            _ => None,
        }
    }

    /// The axiom closure, if one was carried. `Parsed`, `Elaborated` and
    /// `Reflected` have none — and that is `unrecorded`, never `empty`.
    #[must_use]
    pub fn closure(&self) -> AxiomClosure {
        match self {
            Self::KernelChecked(verdict) => verdict.closure.clone(),
            _ => AxiomClosure::unrecorded(),
        }
    }

    /// The composite verdict for this status.
    #[must_use]
    pub fn certification(&self) -> Certification {
        match self {
            Self::KernelChecked(verdict) => {
                if verdict.closure.is_audited_empty() {
                    Certification { tier: CertificationTier::Certified, assumptions: Vec::new() }
                } else {
                    Certification {
                        tier: CertificationTier::AssumptionBearing,
                        assumptions: verdict
                            .closure
                            .assumptions
                            .iter()
                            .cloned()
                            .collect::<Vec<_>>(),
                    }
                }
            }
            _ => Certification {
                tier: CertificationTier::NotKernelChecked,
                assumptions: Vec::new(),
            },
        }
    }

    /// Shorthand for `self.certification().is_certified()`.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        self.certification().is_certified()
    }

    /// The stable wire name.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Parsed => "parsed",
            Self::Elaborated => "elaborated",
            Self::Reflected => "reflected",
            Self::KernelChecked(_) => "kernel-checked",
        }
    }
}

/// The three tiers a status can report.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CertificationTier {
    /// No kernel re-check of this row's own obligation.
    NotKernelChecked,
    /// Kernel re-checked, resting on named assumptions. Reported `Trusted`.
    AssumptionBearing,
    /// Kernel re-checked with an audited-empty closure.
    Certified,
}

/// The composite verdict — what a row may be *reported* as.
///
/// `Certified` is a **conjunction** ("kernel-rechecked ∧ audited-empty axiom
/// closure"), not something a caller can stamp: this struct has private fields
/// and no public constructor, so the only way to hold one is
/// [`KernelStatus::certification`]. That mirrors
/// `trust_types::grade::GradeRecord::is_certified`, which is deliberately a
/// predicate over axes rather than an enum variant, for the same reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certification {
    tier: CertificationTier,
    assumptions: Vec<Assumption>,
}

impl Certification {
    /// Which tier this row reports.
    #[must_use]
    pub fn tier(&self) -> CertificationTier {
        self.tier
    }

    /// Only a kernel re-check over an audited-empty closure earns this.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        self.tier == CertificationTier::Certified && self.assumptions.is_empty()
    }

    /// True when the kernel re-checked but the proof rests on assumptions.
    #[must_use]
    pub fn is_assumption_bearing(&self) -> bool {
        self.tier == CertificationTier::AssumptionBearing
    }

    /// The assumptions, by name, sorted. Empty unless assumption-bearing.
    #[must_use]
    pub fn assumptions(&self) -> &[Assumption] {
        &self.assumptions
    }

    /// The disclosure text for a diagnostic or a report row.
    ///
    /// Names every assumption, and — per v7/D3 — names the fix with options.
    #[must_use]
    pub fn disclosure(&self, symbol: &SegmentPath) -> String {
        match self.tier {
            CertificationTier::Certified => {
                format!("`{symbol}` is Certified: kernel re-checked, no assumptions in its closure")
            }
            CertificationTier::NotKernelChecked => format!(
                "`{symbol}` was NOT re-checked by the Clean CIC kernel, so it \
                 cannot be reported Certified.\n\
                 options: (1) let the two-phase environment elaborate and \
                 check it — a header-only symbol reaches this state when \
                 phase 2 has not run for it; (2) if it is a reflected Rust \
                 carrier, note that reflection is TCB and never Certified by \
                 construction; (3) cite it from a PROOF context only"
            ),
            CertificationTier::AssumptionBearing => {
                let listed = self
                    .assumptions
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "`{symbol}` is kernel-checked but ASSUMPTION-BEARING: its \
                     proof rests on {count} assumption(s): {listed}. It is \
                     reported Trusted, never Certified.\n\
                     options: (1) prove the assumption(s) and delete the \
                     `axiom` / `sorry` they come from; (2) remove the \
                     dependency on them, so the closure becomes empty; (3) \
                     keep them and accept a disclosed assumption — the row \
                     stays Trusted and every name above is printed with it",
                    count = self.assumptions.len(),
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The sealed kernel-authority seam
// ---------------------------------------------------------------------------

mod sealed {
    /// Private supertrait. Nothing outside `trust-symbols` can name it, so
    /// nothing outside `trust-symbols` can implement [`super::KernelAuthority`].
    pub trait Sealed {}
}

/// The one route from a kernel re-check to [`KernelStatus::KernelChecked`].
///
/// # What this buys, exactly
///
/// [`KernelVerdict`]'s fields are private, so the variant cannot be written as
/// a literal anywhere outside this crate. The only public route is this trait,
/// and the trait is sealed by a private supertrait, so the set of implementors
/// is fixed here and cannot grow. The compiler's strongest claim therefore has
/// **one named seam** instead of N struct literals scattered across the tree,
/// and that seam is a `grep` with a single hit rather than an audit procedure.
///
/// # What it does not buy, stated so it is not overclaimed
///
/// This crate cannot name the kernel — that is the point of §5(a)'s structural
/// layer — so it cannot itself verify that whoever calls
/// [`CicKernelRecheck::held_by_kernel_recheck`] really holds a kernel return
/// value. That last step is a review obligation on exactly **one** call site
/// (`trust-clean-env`, the only crate in the tree that links `clean-kernel` and
/// this crate together), which is the smallest surface it can be reduced to.
///
/// It is deliberately **not** a cargo feature. Cargo unifies features across a
/// build, so a `kernel-authority` feature enabled by `trust-clean-env` would be
/// enabled for every crate resolving `trust-symbols` in the same graph, and the
/// gate would be decoration. A decorative gate is worse than none: it reads as
/// an invariant in review.
pub trait KernelAuthority: sealed::Sealed {
    /// Mint the kernel-checked status.
    ///
    /// `closure` must come from a **full certification audit** of this
    /// declaration's own `(goal, term)` pair — `Environment::audit_certification`
    /// or `cert_meter::grade`. A caller holding only `axiom_deps(&Name)` has a
    /// name list, not an authority verdict, and must pass
    /// [`AxiomClosure::unrecorded`]: `axiom_deps` never re-typechecks and grades
    /// a structurally-inserted theorem as clean.
    fn kernel_checked(&self, digest: TermDigest, closure: AxiomClosure) -> KernelStatus;
}

/// The single implementor of [`KernelAuthority`].
///
/// A zero-sized capability token. Hold one only where a Clean CIC kernel
/// re-check has just returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CicKernelRecheck {
    // Private field: no struct-literal construction outside this crate either.
    _private: (),
}

impl CicKernelRecheck {
    /// Assert that the caller holds a Clean CIC kernel re-check result.
    ///
    /// The name is an assertion, and it is meant to read as one at the call
    /// site. The contract, which this crate cannot check and does not pretend
    /// to:
    ///
    /// 1. the Clean CIC kernel re-checked the declaration's own obligation —
    ///    not a sibling's, not a synthetic `name = name`, not a parse;
    /// 2. the caller can produce the exact term that was checked, for
    ///    [`TermDigest`];
    /// 3. the caller ran the **full certification audit**, so the
    ///    [`AxiomClosure`] it passes distinguishes "audited, empty" from "not
    ///    audited".
    #[must_use]
    pub fn held_by_kernel_recheck() -> Self {
        Self { _private: () }
    }
}

impl sealed::Sealed for CicKernelRecheck {}

impl KernelAuthority for CicKernelRecheck {
    fn kernel_checked(&self, digest: TermDigest, closure: AxiomClosure) -> KernelStatus {
        KernelStatus::KernelChecked(KernelVerdict { digest, closure })
    }
}

// ---------------------------------------------------------------------------
// Headers and the graph
// ---------------------------------------------------------------------------

/// A symbol's identity: a path **and** a namespace.
///
/// Not the path alone. `mod m` and `fn m` are two symbols with one path, and a
/// graph keyed on the path would refuse a program stock rustc accepts.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId {
    path: SegmentPath,
    namespace: Namespace,
}

impl SymbolId {
    /// Build an id.
    #[must_use]
    pub fn new(path: SegmentPath, namespace: Namespace) -> Self {
        Self { path, namespace }
    }

    /// The path.
    #[must_use]
    pub fn path(&self) -> &SegmentPath {
        &self.path
    }

    /// The namespace.
    #[must_use]
    pub fn namespace(&self) -> Namespace {
        self.namespace
    }
}

impl fmt::Display for SymbolId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({} namespace)", self.path, self.namespace.name())
    }
}

/// One declaration's header — everything phase 1 knows before any body is
/// elaborated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolHeader {
    id: SymbolId,
    sort: Sort,
    producer: Producer,
    capability: Capability,
    carrier: CarrierEvidence,
    status: KernelStatus,
}

impl SymbolHeader {
    /// A fresh header: PROOF capability, no carrier, [`KernelStatus::Parsed`].
    ///
    /// Every escalation from here is explicit, which is what makes I1's "zero
    /// CALL" a property of the type rather than a promise about the code.
    #[must_use]
    pub fn new(path: SegmentPath, sort: Sort, producer: Producer) -> Self {
        Self {
            id: SymbolId::new(path, sort.namespace()),
            sort,
            producer,
            capability: Capability::Proof,
            carrier: CarrierEvidence::None,
            status: KernelStatus::Parsed,
        }
    }

    /// This header's identity.
    #[must_use]
    pub fn id(&self) -> &SymbolId {
        &self.id
    }

    /// The declaration's path.
    #[must_use]
    pub fn path(&self) -> &SegmentPath {
        self.id.path()
    }

    /// The declaration's sort.
    #[must_use]
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// Which producer wrote it.
    #[must_use]
    pub fn producer(&self) -> Producer {
        self.producer
    }

    /// The capability it currently grants.
    #[must_use]
    pub fn capability(&self) -> Capability {
        self.capability
    }

    /// The carrier evidence recorded for it.
    #[must_use]
    pub fn carrier(&self) -> CarrierEvidence {
        self.carrier
    }

    /// Its kernel status.
    #[must_use]
    pub fn status(&self) -> &KernelStatus {
        &self.status
    }

    /// Replace the status. The only way to reach
    /// [`KernelStatus::KernelChecked`] is still [`KernelAuthority`].
    #[must_use]
    pub fn with_status(mut self, status: KernelStatus) -> Self {
        self.status = status;
        self
    }

    /// Record carrier evidence (I4).
    #[must_use]
    pub fn with_carrier(mut self, carrier: CarrierEvidence) -> Self {
        self.carrier = carrier;
        self
    }

    /// Grant CALL — the capability that lets Rust name this symbol and
    /// therefore lets it **produce a value**.
    ///
    /// Refused unless *both* hold, matching §4's I5 rule exactly:
    ///
    /// 1. the status is `Certified` — kernel-checked with an audited-empty
    ///    closure; and
    /// 2. the carrier is [`CarrierEvidence::Total`].
    ///
    /// At I1 neither is reachable in this tree, so CALL is unreachable — not
    /// as a matter of discipline but because there is no value to pass. That is
    /// the "capability is withheld by not minting the symbol" mechanism of
    /// §5(b), expressed one layer earlier.
    ///
    /// # Errors
    ///
    /// [`CapabilityRefused`], naming which of the two conditions failed and
    /// what to do about it.
    pub fn grant_call(mut self) -> Result<Self, CapabilityRefused> {
        let certification = self.status.certification();
        if !certification.is_certified() {
            return Err(CapabilityRefused::NotCertified {
                symbol: self.id.path.clone(),
                tier: certification.tier(),
                assumptions: certification.assumptions().iter().map(ToString::to_string).collect(),
            });
        }
        if self.carrier != CarrierEvidence::Total {
            return Err(CapabilityRefused::NoTotalCarrier {
                symbol: self.id.path.clone(),
                carrier: self.carrier,
            });
        }
        self.capability = Capability::Call;
        Ok(self)
    }
}

/// Why CALL was withheld.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CapabilityRefused {
    /// The declaration is not `Certified`.
    NotCertified {
        /// The declaration.
        symbol: SegmentPath,
        /// What it does report.
        tier: CertificationTier,
        /// Its assumptions, rendered, if any.
        assumptions: Vec<String>,
    },
    /// No total Rust carrier for the declaration's type.
    NoTotalCarrier {
        /// The declaration.
        symbol: SegmentPath,
        /// What carrier evidence exists.
        carrier: CarrierEvidence,
    },
}

impl fmt::Display for CapabilityRefused {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotCertified { symbol, tier, assumptions } => {
                let detail = if assumptions.is_empty() {
                    String::new()
                } else {
                    format!(" (assumptions: {})", assumptions.join(", "))
                };
                write!(
                    f,
                    "`{symbol}` is PROOF-only: CALL requires a Certified \
                     declaration and this one reports {tier:?}{detail}.\n\
                     options: (1) discharge the remaining obligation so the \
                     Clean CIC kernel re-checks it; (2) if it is \
                     assumption-bearing, prove or remove the assumptions \
                     listed above — an assumed proposition may be observed \
                     from a proof context but may never produce a value; (3) \
                     keep it PROOF-only and cite it from `requires`/`ensures` \
                     rather than calling it"
                )
            }
            Self::NoTotalCarrier { symbol, carrier } => write!(
                f,
                "`{symbol}` has no total Rust carrier (carrier evidence: \
                 {carrier:?}), so calling it could emit a wrong binary even \
                 though the kernel is satisfied: a `Nat -> u64` extraction \
                 composed with a `u64 -> Nat` admission is definitionally \
                 equal while the emitted code wraps.\n\
                 options: (1) give the declaration a fixed-width Clean type \
                 whose carrier is total (I5's first fragment); (2) wait for \
                 the bignum carrier (I6), which closes this without any source \
                 change; (3) keep it PROOF-only — a dependent or unbounded \
                 type keeps PROOF and loses CALL, and is never approximated"
            ),
        }
    }
}

impl std::error::Error for CapabilityRefused {}

/// Two declarations claimed one name in one namespace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplicateSymbol {
    /// The contested identity.
    pub id: SymbolId,
    /// The header already in the graph.
    pub existing: (Producer, Sort),
    /// The header that was refused.
    pub incoming: (Producer, Sort),
}

impl fmt::Display for DuplicateSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "duplicate definition of `{path}` in the {ns} namespace: first \
             declared by the {p1} producer as a `{s1}`, then by the {p2} \
             producer as a `{s2}`.\n\
             options: (1) rename one of the two; (2) move the Clean \
             declaration into a different module — island declarations are \
             parented to the ENCLOSING RUST MODULE, not to the island, so two \
             islands in one module share a namespace; (3) if the Clean \
             declaration is a proposition, declare it as a `prop`, which does \
             not enter the value namespace and therefore does not collide with \
             a Rust `fn`",
            path = self.id.path,
            ns = self.id.namespace.name(),
            p1 = self.existing.0.name(),
            s1 = self.existing.1.name(),
            p2 = self.incoming.0.name(),
            s2 = self.incoming.1.name(),
        )
    }
}

impl std::error::Error for DuplicateSymbol {}

/// A status update was aimed at a symbol that was never declared.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnknownSymbol {
    /// The identity that was not found.
    pub id: SymbolId,
}

impl fmt::Display for UnknownSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "no header for `{id}`.\n\
             options: (1) declare it in phase 1 — every header from every \
             island is collected before any body is elaborated, and phase 2 \
             may only update symbols phase 1 saw; (2) check the namespace: a \
             `prop` and a `term` with the same path are different symbols; (3) \
             check the path spelling — `crate::m::f` and `Crate.m.f` are the \
             same path, but `foo::m::f` and `Foo.m.f` are not",
            id = self.id
        )
    }
}

impl std::error::Error for UnknownSymbol {}

/// The one symbol graph.
///
/// Phase 1 (`declare`) collects **every** header from **every** island and
/// every Rust item before phase 2 (`record_status`) elaborates anything. That
/// ordering is the whole of I1: today `trust_check_clean_islands` sorts islands
/// by `(span.lo(), span.hi())` and feeds each island's text into a single
/// stateful session, so a declaration in a later island is not in the
/// environment when an earlier island is checked and **source order is
/// load-bearing**. A `BTreeMap` keyed on [`SymbolId`] has no order to be
/// load-bearing about; the property is pinned by
/// `declaration_order_does_not_change_the_graph` below.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolGraph {
    headers: BTreeMap<SymbolId, SymbolHeader>,
}

impl SymbolGraph {
    /// An empty graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Phase 1: declare a header.
    ///
    /// # Errors
    ///
    /// [`DuplicateSymbol`] if the path is already claimed in that namespace.
    /// This is a *capability gain* over today's behaviour, not a new
    /// restriction: the source-order loop rejects macro-collapsed islands
    /// outright, so a genuine duplicate could not be diagnosed as one.
    pub fn declare(&mut self, header: SymbolHeader) -> Result<&SymbolHeader, DuplicateSymbol> {
        let id = header.id.clone();
        if let Some(existing) = self.headers.get(&id) {
            return Err(DuplicateSymbol {
                id,
                existing: (existing.producer, existing.sort),
                incoming: (header.producer, header.sort),
            });
        }
        Ok(self.headers.entry(id).or_insert(header))
    }

    /// Phase 2: record what elaboration and (maybe) the kernel found.
    ///
    /// # Errors
    ///
    /// [`UnknownSymbol`] if phase 1 never saw this symbol.
    pub fn record_status(
        &mut self,
        id: &SymbolId,
        status: KernelStatus,
    ) -> Result<(), UnknownSymbol> {
        match self.headers.get_mut(id) {
            Some(header) => {
                header.status = status;
                Ok(())
            }
            None => Err(UnknownSymbol { id: id.clone() }),
        }
    }

    /// Look a header up.
    #[must_use]
    pub fn header(&self, id: &SymbolId) -> Option<&SymbolHeader> {
        self.headers.get(id)
    }

    /// Resolve a path in a namespace.
    #[must_use]
    pub fn resolve(&self, path: &SegmentPath, namespace: Namespace) -> Option<&SymbolHeader> {
        self.headers.get(&SymbolId::new(path.clone(), namespace))
    }

    /// Every header, in path order.
    pub fn headers(&self) -> impl Iterator<Item = &SymbolHeader> {
        self.headers.values()
    }

    /// How many headers are declared.
    #[must_use]
    pub fn len(&self) -> usize {
        self.headers.len()
    }

    /// Whether the graph is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.headers.is_empty()
    }

    /// Every kernel-checked-but-assumption-bearing row, with its disclosure.
    ///
    /// This is the surface the binding rule names: the assumptions are
    /// disclosed **by name**, per declaration, and they survive to whatever
    /// consumes the graph rather than being stringified into one island's error
    /// and thrown away.
    pub fn assumption_bearing(&self) -> impl Iterator<Item = (&SymbolHeader, Certification)> {
        self.headers.values().filter_map(|header| {
            let certification = header.status.certification();
            certification.is_assumption_bearing().then_some((header, certification))
        })
    }
}

// ---------------------------------------------------------------------------
// Compile-fail controls (real tests: rustdoc compiles these as external crates)
// ---------------------------------------------------------------------------

/// Controls that must **fail to compile**. `cargo test` runs them.
///
/// These are doctests marked `compile_fail`, which rustdoc builds as separate
/// crates linking `trust-symbols` from outside. That is the only way to
/// exercise "a crate that cannot name the kernel cannot fabricate the status" —
/// an in-crate `#[test]` has private access and would prove nothing.
///
/// # 1. The sealed trait cannot be implemented downstream
///
/// A crate that wants to mint `KernelChecked` without a kernel would implement
/// [`KernelAuthority`] for its own type. It cannot: the supertrait is private.
///
/// ```compile_fail,E0277
/// struct ForgedAuthority;
/// impl trust_symbols::KernelAuthority for ForgedAuthority {
///     fn kernel_checked(
///         &self,
///         digest: trust_symbols::TermDigest,
///         closure: trust_symbols::AxiomClosure,
///     ) -> trust_symbols::KernelStatus {
///         unimplemented!()
///     }
/// }
/// ```
///
/// # 2. The verdict payload cannot be written as a literal
///
/// The other way in is to construct the variant's payload directly. The fields
/// are private, so this does not compile either.
///
/// ```compile_fail,E0451
/// let verdict = trust_symbols::KernelVerdict {
///     digest: trust_symbols::TermDigest::of_bytes(b"anything"),
///     closure: trust_symbols::AxiomClosure::audited([]),
/// };
/// let _ = trust_symbols::KernelStatus::KernelChecked(verdict);
/// ```
///
/// # 3. `Certification` cannot be stamped
///
/// `Certified` is a conjunction over a status, not a value a caller can hand
/// out. [`Certification`] has private fields and no public constructor.
///
/// ```compile_fail,E0451
/// let _ = trust_symbols::Certification {
///     tier: trust_symbols::CertificationTier::Certified,
///     assumptions: Vec::new(),
/// };
/// ```
///
/// # 4. The positive control — this one MUST compile
///
/// If the three above failed for an unrelated reason (a typo, a renamed item)
/// they would still "pass", so the same API is exercised positively here. A
/// `compile_fail` block without this partner is not evidence.
///
/// ```
/// use trust_symbols::{AxiomClosure, CicKernelRecheck, KernelAuthority, TermDigest};
///
/// let authority = CicKernelRecheck::held_by_kernel_recheck();
/// let status = authority.kernel_checked(TermDigest::of_bytes(b"term"), AxiomClosure::audited([]));
/// assert!(status.is_certified());
/// ```
#[derive(Clone, Copy, Debug)]
pub struct CompileFailControls;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn seg(text: &str) -> Segment {
        Segment::new(text).expect("valid segment")
    }

    fn rust_path(text: &str) -> SegmentPath {
        SegmentPath::parse_rust(text).expect("valid rust path")
    }

    fn certified_status() -> KernelStatus {
        CicKernelRecheck::held_by_kernel_recheck()
            .kernel_checked(TermDigest::of_bytes(b"t"), AxiomClosure::audited([]))
    }

    // -- Paths ------------------------------------------------------------

    /// §4.1.1 / §4: `crate::m::f` and `Crate.m.f` are two spellings of ONE
    /// path. If this ever fails, the resolver needs a special case and the
    /// whole "one symbol graph" spine is gone.
    #[test]
    fn rust_and_clean_spellings_are_one_path() {
        assert_eq!(rust_path("crate::m::f"), SegmentPath::parse_clean("Crate.m.f").unwrap());
        assert_eq!(rust_path("crate::m::f").render_clean(), "Crate.m.f");
        assert_eq!(SegmentPath::parse_clean("Crate.m.f").unwrap().render_rust(), "crate::m::f");
    }

    /// Both spellings of the root normalize, in both parsers, so a Clean author
    /// who writes `crate.m.f` and one who writes `Crate.m.f` name one symbol.
    #[test]
    fn either_root_spelling_normalizes_in_either_parser() {
        let canonical = rust_path("crate::m::f");
        assert_eq!(SegmentPath::parse_clean("crate.m.f").unwrap(), canonical);
        assert_eq!(SegmentPath::parse_rust("Crate::m::f").unwrap(), canonical);
    }

    /// FAILING CASE FIRST: root aliasing is positional. A `Crate` deeper in
    /// the path is an ordinary namespace and must NOT be normalized — doing so
    /// would merge two distinct symbols into one.
    #[test]
    fn non_leading_crate_spelling_is_not_normalized() {
        let path = SegmentPath::parse_clean("A.Crate.f").unwrap();
        assert_eq!(
            path.segments().iter().map(Segment::as_str).collect::<Vec<_>>(),
            vec!["A", "Crate", "f"]
        );
        assert_ne!(path, rust_path("A::crate::f"));
    }

    /// FAILING CASE FIRST: a segment carrying a separator would render as two
    /// segments, so `crate::["m::f"]` and `crate::m::f` would print the same
    /// name while comparing unequal. That is how a duplicate check silently
    /// stops firing.
    #[test]
    fn a_segment_may_not_smuggle_a_separator() {
        assert_eq!(
            Segment::new("m::f"),
            Err(PathError::SeparatorInSegment {
                segment: "m::f".to_string(),
                offender: ':'
            })
        );
        assert!(matches!(
            Segment::new("m.f"),
            Err(PathError::SeparatorInSegment { offender: '.', .. })
        ));
        assert_eq!(Segment::new(""), Err(PathError::EmptySegment));
        assert_eq!(Segment::new("  "), Err(PathError::EmptySegment));
        assert_eq!(SegmentPath::from_segments([]), Err(PathError::EmptyPath));
    }

    /// The "parented to the enclosing Rust module" rule of §4, as arithmetic
    /// on paths rather than as a comment.
    #[test]
    fn island_declarations_are_parented_to_the_enclosing_module() {
        let module = rust_path("crate::m");
        assert_eq!(module.child(seg("f")), rust_path("crate::m::f"));
        assert_eq!(rust_path("crate::m::f").parent(), Some(module));
        assert_eq!(rust_path("crate").parent(), None);
        assert_eq!(rust_path("crate::m::f").leaf().as_str(), "f");
    }

    /// Cross-crate roots are NOT aliased, and that is deliberate: conflating
    /// `foo` with `Foo` is not injective, and cross-crate identity is I7's.
    #[test]
    fn foreign_crate_roots_are_not_aliased() {
        assert_ne!(rust_path("foo::m::f"), SegmentPath::parse_clean("Foo.m.f").unwrap());
    }

    // -- Sorts ------------------------------------------------------------

    /// A FLAT namespace would reject valid Rust. `mod m` and `fn m` coexist in
    /// one module; so do `struct Foo` and `fn Foo`. Compiling all valid Rust
    /// identically is a release gate, so this is not a nicety.
    #[test]
    fn a_flat_namespace_would_reject_valid_rust() {
        let path = rust_path("crate::m");
        let mut graph = SymbolGraph::new();
        graph
            .declare(SymbolHeader::new(path.clone(), Sort::Module, Producer::Rust))
            .expect("mod m");
        // Same path, different namespace: valid Rust, and the graph must
        // accept it.
        graph
            .declare(SymbolHeader::new(path.clone(), Sort::Term, Producer::Rust))
            .expect("fn m beside mod m");
        assert_eq!(graph.len(), 2);
        assert!(graph.resolve(&path, Namespace::Type).is_some());
        assert!(graph.resolve(&path, Namespace::Value).is_some());
    }

    /// The converse control: same path, same namespace, and it MUST be
    /// refused — otherwise the test above only proves the graph accepts
    /// everything.
    #[test]
    fn same_path_and_namespace_is_a_duplicate() {
        let path = rust_path("crate::m::f");
        let mut graph = SymbolGraph::new();
        graph.declare(SymbolHeader::new(path.clone(), Sort::Term, Producer::Rust)).unwrap();
        let err = graph
            .declare(SymbolHeader::new(path.clone(), Sort::Term, Producer::Clean))
            .expect_err("a Clean def must collide with a same-module Rust fn");
        assert_eq!(err.existing, (Producer::Rust, Sort::Term));
        assert_eq!(err.incoming, (Producer::Clean, Sort::Term));
        // v7/D3: the refusal names the fix, with options.
        let rendered = err.to_string();
        assert!(rendered.contains("crate::m::f"), "{rendered}");
        assert!(rendered.contains("options:"), "{rendered}");
    }

    /// A Clean `theorem` shares a module with a Rust `fn` of the same name and
    /// does NOT collide: propositions never enter the value namespace, which
    /// is precisely why §2 rejects a new `DefKind` for them.
    #[test]
    fn a_theorem_does_not_collide_with_a_fn() {
        let path = rust_path("crate::m::f");
        let mut graph = SymbolGraph::new();
        graph.declare(SymbolHeader::new(path.clone(), Sort::Term, Producer::Rust)).unwrap();
        graph
            .declare(SymbolHeader::new(path.clone(), Sort::Prop, Producer::Clean))
            .expect("a prop is in a different namespace");
        assert_eq!(Sort::Prop.namespace(), Namespace::Proof);
        assert_eq!(Sort::Module.namespace(), Namespace::Type);
        assert_eq!(Sort::Trait.namespace(), Namespace::Type);
    }

    // -- Source-order independence (the I1 property) -----------------------

    /// THE I1 PROPERTY. Two islands declared in either order produce the same
    /// graph. Today `trust_check_clean_islands` sorts by `(span.lo, span.hi)`
    /// and feeds one text at a time into a stateful session, so a forward
    /// reference across islands fails. Here there is no order to depend on.
    #[test]
    fn declaration_order_does_not_change_the_graph() {
        let later = SymbolHeader::new(rust_path("crate::a::Later::step"), Sort::Term, Producer::Clean);
        let uses = SymbolHeader::new(rust_path("crate::b::uses_later"), Sort::Prop, Producer::Clean);

        let mut forward = SymbolGraph::new();
        forward.declare(uses.clone()).unwrap();
        forward.declare(later.clone()).unwrap();

        let mut backward = SymbolGraph::new();
        backward.declare(later).unwrap();
        backward.declare(uses).unwrap();

        assert_eq!(forward, backward);
        assert_eq!(forward.len(), 2);
    }

    /// Phase 2 may only speak about symbols phase 1 saw, and the refusal names
    /// the fix.
    #[test]
    fn phase_two_cannot_invent_a_symbol() {
        let mut graph = SymbolGraph::new();
        let id = SymbolId::new(rust_path("crate::ghost"), Namespace::Value);
        let err = graph.record_status(&id, KernelStatus::Elaborated).expect_err("no header");
        assert_eq!(err.id, id);
        assert!(err.to_string().contains("options:"));
    }

    // -- Axiom closure ----------------------------------------------------

    /// THE BINDING RULE. A non-empty closure is never `Certified`, and every
    /// assumption is disclosed BY NAME.
    #[test]
    fn a_non_empty_closure_is_never_certified() {
        let closure = AxiomClosure::audited([
            Assumption::domain_axiom("key_lemma").unwrap(),
            Assumption::trust_marker("sorry").unwrap(),
        ]);
        let status = CicKernelRecheck::held_by_kernel_recheck()
            .kernel_checked(TermDigest::of_bytes(b"t"), closure);

        let certification = status.certification();
        assert!(!certification.is_certified());
        assert!(!status.is_certified());
        assert!(certification.is_assumption_bearing());
        assert_eq!(certification.tier(), CertificationTier::AssumptionBearing);
        assert!(status.is_kernel_checked(), "the kernel really did re-check it");

        // Disclosed by name, sorted, with the kind distinguished.
        let recorded = status.closure();
        assert_eq!(recorded.names(), vec!["key_lemma", "sorry"]);
        let disclosure = certification.disclosure(&rust_path("crate::m::thm"));
        assert!(disclosure.contains("key_lemma"), "{disclosure}");
        assert!(disclosure.contains("sorry"), "{disclosure}");
        assert!(disclosure.contains("trust marker"), "{disclosure}");
        assert!(disclosure.contains("domain axiom"), "{disclosure}");
        assert!(disclosure.contains("never Certified"), "{disclosure}");
        assert!(disclosure.contains("options:"), "{disclosure}");
    }

    /// The partner control. The SAME theorem with a real proof must report
    /// `Certified`; if the two produced the same row the disclosure would be
    /// inert and both tests worthless (§6, the axiom-disclosure pair).
    #[test]
    fn the_same_theorem_with_a_real_proof_is_certified() {
        let status = certified_status();
        assert!(status.is_certified());
        assert_eq!(status.certification().tier(), CertificationTier::Certified);
        assert!(status.certification().assumptions().is_empty());
        assert_ne!(status.certification(), {
            let bearing = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
                TermDigest::of_bytes(b"t"),
                AxiomClosure::audited([Assumption::domain_axiom("key_lemma").unwrap()]),
            );
            bearing.certification()
        });
    }

    /// `unrecorded` is not `empty`. A producer holding only `axiom_deps(&Name)`
    /// has a name list, not an authority verdict — `axiom_deps` never
    /// re-typechecks, so a structurally-inserted theorem has an empty one and
    /// is not thereby clean. Recording that as `unrecorded` must fail closed.
    #[test]
    fn an_unrecorded_closure_is_never_certified() {
        let status = CicKernelRecheck::held_by_kernel_recheck()
            .kernel_checked(TermDigest::of_bytes(b"t"), AxiomClosure::unrecorded());
        assert!(status.is_kernel_checked());
        assert!(!status.is_certified());
        assert_eq!(status.certification().tier(), CertificationTier::AssumptionBearing);
        assert!(!AxiomClosure::unrecorded().is_audited_empty());
        assert!(!AxiomClosure::unrecorded().is_recorded());
        // The Default must be the fail-closed state, so a `#[derive(Default)]`
        // downstream cannot mint an empty closure by omission.
        assert_eq!(AxiomClosure::default(), AxiomClosure::unrecorded());
        assert_ne!(AxiomClosure::default(), AxiomClosure::audited([]));
    }

    /// The transitive case, which the shallow per-declaration scan
    /// (`ConstantInfo::trust_summary`) provably cannot catch: a declaration
    /// whose OWN body is clean but whose dependency carries `sorry`. The merged
    /// closure must name the transitive assumption.
    #[test]
    fn a_transitive_assumption_survives_the_merge() {
        let own = AxiomClosure::audited([]);
        let dependency =
            AxiomClosure::audited([Assumption::trust_marker("sorryAx").unwrap()]);
        let merged = own.merge(&dependency);

        assert!(!merged.is_audited_empty());
        assert_eq!(merged.names(), vec!["sorryAx"]);
        assert_eq!(merged.trust_markers().count(), 1);
        assert_eq!(merged.domain_axioms().count(), 0);

        let status = CicKernelRecheck::held_by_kernel_recheck()
            .kernel_checked(TermDigest::of_bytes(b"t"), merged);
        assert!(!status.is_certified());
    }

    /// FAILING CASE FIRST: merge is ABSORBING on `unrecorded`. An audited-empty
    /// closure joined with an unaudited one is unaudited — otherwise a
    /// dependency's `sorry` disappears from the disclosure by arithmetic.
    #[test]
    fn merging_with_an_unrecorded_closure_fails_closed() {
        let audited_empty = AxiomClosure::audited([]);
        assert!(audited_empty.is_audited_empty());

        let merged = audited_empty.merge(&AxiomClosure::unrecorded());
        assert!(!merged.is_recorded());
        assert!(!merged.is_audited_empty());
        assert_eq!(AxiomClosure::unrecorded().merge(&audited_empty), AxiomClosure::unrecorded());
    }

    /// An assumption that cannot be named cannot be disclosed by name, so it
    /// is refused rather than carried as a blank.
    #[test]
    fn an_unnameable_assumption_is_refused() {
        assert_eq!(Assumption::domain_axiom(""), Err(AssumptionNameError));
        assert_eq!(Assumption::trust_marker("   "), Err(AssumptionNameError));
        assert!(AssumptionNameError.to_string().contains("options:"));
    }

    /// This crate and the existing five-axis grade record must not disagree
    /// about the same declaration. Two subsystems that grade the same thing
    /// differently is how a false `Certified` reaches a report.
    #[test]
    fn the_grade_projection_agrees_with_grade_record() {
        use trust_types::grade::{
            AxiomClosure as Axis, CoverageBound, Executability, GradeRecord, ProofValidation,
            ReflectionTier,
        };

        let cases = [
            (AxiomClosure::audited([]), Axis::Empty, true),
            (
                AxiomClosure::audited([Assumption::domain_axiom("key_lemma").unwrap()]),
                Axis::Named(["key_lemma".to_string()].into_iter().collect()),
                false,
            ),
            (AxiomClosure::unrecorded(), Axis::Unrecorded, false),
        ];

        for (closure, expected_axis, expected_certified) in cases {
            assert_eq!(closure.to_grade_axis(), expected_axis);
            let record = GradeRecord {
                validation: ProofValidation::KernelRechecked,
                axiom_closure: closure.to_grade_axis(),
                coverage: CoverageBound::Unbounded,
                executability: Executability::Unmonitored,
                reflection: ReflectionTier::Unlinked,
            };
            let status = CicKernelRecheck::held_by_kernel_recheck()
                .kernel_checked(TermDigest::of_bytes(b"t"), closure);
            assert_eq!(record.is_certified(), expected_certified);
            assert_eq!(status.is_certified(), record.is_certified());
        }
    }

    // -- Statuses ---------------------------------------------------------

    /// `Parsed` is the default and buys nothing. "A successful parse buys a
    /// name and a sort. It never buys a proposition."
    #[test]
    fn a_parse_buys_no_authority() {
        let status = KernelStatus::default();
        assert_eq!(status, KernelStatus::Parsed);
        assert!(!status.is_kernel_checked());
        assert!(!status.is_certified());
        assert_eq!(status.certification().tier(), CertificationTier::NotKernelChecked);
        assert!(!status.closure().is_audited_empty(), "no closure means unrecorded, not empty");
    }

    /// I2's control, available already: `Reflected` is a DISTINCT state from
    /// `KernelChecked`, because the reflection is TCB. A reflected carrier must
    /// never satisfy a kernel-check requirement.
    #[test]
    fn reflected_is_not_kernel_checked() {
        let status = KernelStatus::Reflected;
        assert!(!status.is_kernel_checked());
        assert!(!status.is_certified());
        assert_ne!(status, KernelStatus::Elaborated);
        assert_ne!(status.name(), certified_status().name());
        assert_eq!(status.certification().tier(), CertificationTier::NotKernelChecked);
        // And the refusal explains itself.
        let disclosure = status.certification().disclosure(&rust_path("crate::m::f"));
        assert!(disclosure.contains("NOT re-checked"), "{disclosure}");
        assert!(disclosure.contains("options:"), "{disclosure}");
    }

    /// Elaboration is not checking: the elaborator is not the kernel, and an
    /// elaborator bug is a wrong term rather than a caught one.
    #[test]
    fn elaboration_is_not_kernel_checking() {
        assert!(!KernelStatus::Elaborated.is_kernel_checked());
        assert!(!KernelStatus::Elaborated.is_certified());
    }

    // -- Capability -------------------------------------------------------

    /// I1 SCOPE: ZERO CALL capability. A fresh header is PROOF-only, and the
    /// two escalation conditions are both unreachable in this tree today.
    #[test]
    fn a_fresh_header_is_proof_only() {
        let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean);
        assert_eq!(header.capability(), Capability::Proof);
        assert_eq!(header.carrier(), CarrierEvidence::None);
        assert_eq!(header.status(), &KernelStatus::Parsed);
        assert!(!header.capability().permits(Capability::Call));
        assert!(header.capability().permits(Capability::Proof));
        assert!(Capability::Call.permits(Capability::Proof));
    }

    /// FAILING CASE FIRST: CALL is refused for a parsed header, and the
    /// refusal says which condition failed and what the options are.
    #[test]
    fn call_is_refused_without_a_kernel_check() {
        let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean);
        let err = header.grant_call().expect_err("a parsed header may not produce a value");
        assert!(matches!(
            err,
            CapabilityRefused::NotCertified { tier: CertificationTier::NotKernelChecked, .. }
        ));
        let rendered = err.to_string();
        assert!(rendered.contains("PROOF-only"), "{rendered}");
        assert!(rendered.contains("options:"), "{rendered}");
    }

    /// FAILING CASE FIRST: an assumption-bearing declaration may be OBSERVED
    /// from a proof context but may never produce a value.
    #[test]
    fn call_is_refused_for_an_assumption_bearing_declaration() {
        let status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
            TermDigest::of_bytes(b"t"),
            AxiomClosure::audited([Assumption::domain_axiom("key_lemma").unwrap()]),
        );
        let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean)
            .with_status(status)
            .with_carrier(CarrierEvidence::Total);
        let err = header.grant_call().expect_err("assumption-bearing may not CALL");
        assert!(matches!(err, CapabilityRefused::NotCertified { .. }));
        assert!(err.to_string().contains("key_lemma"));
    }

    /// FAILING CASE FIRST, and it is the `Nat -> u64` miscompile: a Certified
    /// declaration with a merely DECLARED carrier is still refused. Kernel
    /// defeq does not subsume representation faithfulness — a `Nat -> u64`
    /// extraction composed with a `u64 -> Nat` admission is definitionally
    /// equal while the emitted code wraps (§5(b), G3).
    #[test]
    fn call_is_refused_without_a_total_carrier() {
        for carrier in [CarrierEvidence::None, CarrierEvidence::Declared] {
            let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean)
                .with_status(certified_status())
                .with_carrier(carrier);
            let err = header.grant_call().expect_err("a declared carrier grants nothing");
            assert!(matches!(err, CapabilityRefused::NoTotalCarrier { .. }));
            let rendered = err.to_string();
            assert!(rendered.contains("wrong binary"), "{rendered}");
            assert!(rendered.contains("options:"), "{rendered}");
        }
        assert_eq!(CarrierEvidence::default(), CarrierEvidence::None);
    }

    /// The positive control, so the four refusals above are not just "grant_call
    /// always errors". BOTH conditions together grant CALL — and neither is
    /// constructible from anywhere in this tree at I1.
    #[test]
    fn call_is_granted_only_when_both_conditions_hold() {
        let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean)
            .with_status(certified_status())
            .with_carrier(CarrierEvidence::Total)
            .grant_call()
            .expect("certified + total carrier");
        assert_eq!(header.capability(), Capability::Call);
        assert!(header.capability().permits(Capability::Proof));
    }

    // -- Graph reporting --------------------------------------------------

    /// The closure survives to the graph, per declaration, instead of being
    /// stringified into one island's error and thrown away — which is what the
    /// current whole-session taint bit does.
    #[test]
    fn assumption_bearing_rows_survive_to_the_graph() {
        let mut graph = SymbolGraph::new();
        let clean_path = rust_path("crate::m::good");
        let debt_path = rust_path("crate::m::shaky");
        graph
            .declare(SymbolHeader::new(clean_path.clone(), Sort::Prop, Producer::Clean))
            .unwrap();
        graph
            .declare(SymbolHeader::new(debt_path.clone(), Sort::Prop, Producer::Clean))
            .unwrap();

        graph
            .record_status(&SymbolId::new(clean_path, Namespace::Proof), certified_status())
            .unwrap();
        graph
            .record_status(
                &SymbolId::new(debt_path.clone(), Namespace::Proof),
                CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
                    TermDigest::of_bytes(b"t"),
                    AxiomClosure::audited([Assumption::trust_marker("sorry").unwrap()]),
                ),
            )
            .unwrap();

        let bearing: Vec<_> = graph.assumption_bearing().collect();
        assert_eq!(bearing.len(), 1, "the certified sibling is not assumption-bearing");
        assert_eq!(bearing[0].0.path(), &debt_path);
        assert_eq!(bearing[0].1.assumptions().len(), 1);
        assert_eq!(bearing[0].1.assumptions()[0].name(), "sorry");
        assert_eq!(bearing[0].1.assumptions()[0].kind(), AssumptionKind::TrustMarker);
    }

    // -- Digest -----------------------------------------------------------

    #[test]
    fn digests_are_canonical_or_refused() {
        let digest = TermDigest::of_bytes(b"term");
        assert_eq!(digest.as_hex().len(), 64);
        assert_eq!(TermDigest::from_hex(digest.as_hex()).unwrap(), digest);
        assert!(TermDigest::from_hex("").is_err());
        assert!(TermDigest::from_hex("XY").is_err());
        // Upper-case hex is the same bytes but not the same string, and string
        // identity is what caches and I7 certificates compare on.
        assert!(TermDigest::from_hex(&digest.as_hex().to_uppercase()).is_err());
        assert!(TermDigest::from_hex(&digest.as_hex()[..63]).is_err());
        assert!(DigestError { got: "x".to_string() }.to_string().contains("options:"));
    }

    #[test]
    fn a_digest_identifies_the_term() {
        assert_ne!(TermDigest::of_bytes(b"a"), TermDigest::of_bytes(b"b"));
        assert_eq!(TermDigest::of_bytes(b"a"), TermDigest::of_bytes(b"a"));
    }
}
