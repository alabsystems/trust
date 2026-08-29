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
//! | [`Capability`], [`CarrierEvidence`] | PROOF/CALL, a declared two-element lattice. At I1 nothing can reach `Call`. |
//! | [`ReferenceSet`], [`EffectiveCapability`], [`CapabilityClosure`] | I3's transitive proof-only firewall: what a declaration references, and the meet over it. |
//! | [`ProofOnlyRefusal`] | The one spelling of "visible but not executable". |
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
//! * [`ReferenceSet::default`] is [`ReferenceSet::Unrecorded`] and
//!   [`EffectiveCapability::meet`] is absorbing on it, for the same reason and
//!   by the same rule: an edge nobody enumerated poisons the capability closure
//!   instead of being assumed benign. `Recorded(∅)` — a leaf — is a *positive
//!   finding* and is a different value.
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
    pub fn from_segments(segments: impl IntoIterator<Item = Segment>) -> Result<Self, PathError> {
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
            let normalized = if index == 0 && (raw == CRATE_ROOT || raw == CRATE_ROOT_CLEAN) {
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
///
/// # It is a lattice, and the order is DECLARED rather than inherited (I3)
///
/// This is a two-element chain **ordered by executable authority**:
///
/// ```text
///   Call     ⊤  — observable AND able to produce a value
///    │
///   Proof    ⊥  — observable only
/// ```
///
/// The derived `Ord` agrees with that order, but agreeing by *declaration
/// order* is an accident of how the variants happen to be typed out, and a
/// later edit that reorders them would silently invert every `meet`. The order
/// is therefore pinned by [`Capability::AUTHORITY_ASCENDING`] and by the
/// `the_capability_order_is_declared_not_accidental` control, so reordering the
/// variants breaks a test instead of breaking the firewall.
///
/// # Two orders, dual to each other — say which one you mean
///
/// * **Authority** (this order, and the one [`Capability::join`] /
///   [`Capability::meet`] use): `Proof < Call`. CALL can do strictly more.
/// * **Observation** (the dual, [`Capability::observes_at_least`]): a PROOF
///   *context* observes strictly more symbols than a CALL context, because
///   §4.1.1 lets PROOF name every declaration including private internals with
///   zero annotations, while CALL obeys the declaring language's ordinary
///   visibility.
///
/// Those two sentences are not in tension and the confusion between them is the
/// likeliest way to get this backwards: PROOF sees more *symbols*, CALL holds
/// more *authority over one symbol*. **Observation grants no executable
/// authority — that is what makes total proof visibility sound.**
///
/// # `meet` is the operator the transitive firewall runs on
///
/// A declaration is at most as executable as the weakest thing it references:
/// a `def` whose body names a proof-only symbol cannot emit a call or a load,
/// so it is itself proof-only. That is [`Capability::meet`] folded over a
/// reference set — see [`SymbolGraph::capability_closure`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Capability {
    /// Nameable from proof contexts only. The **bottom** of the authority
    /// lattice, and therefore the fail-closed answer.
    Proof,
    /// Nameable from ordinary Rust code, and therefore able to **produce a
    /// value**. A divergence here is a wrong binary, not a failed proof. The
    /// **top** of the authority lattice.
    Call,
}

impl Capability {
    /// The bottom of the authority lattice: observable, never executable.
    ///
    /// Named `LEAST` rather than `DEFAULT` on purpose — there is no `Default`
    /// impl, because a capability that arrives by `..Default::default()` is a
    /// capability nobody decided.
    pub const LEAST: Self = Self::Proof;

    /// The top of the authority lattice.
    pub const GREATEST: Self = Self::Call;

    /// Every capability in **ascending authority order**.
    ///
    /// The declared order of record. `Capability::AUTHORITY_ASCENDING` and the
    /// derived `Ord` must agree, which is what the order control checks.
    pub const AUTHORITY_ASCENDING: [Self; 2] = [Self::Proof, Self::Call];

    /// Whether holding `self` permits a use that requires `required`.
    ///
    /// This is the order relation `required ≤ self` in the authority order,
    /// spelled out rather than derived so that it reads as the rule it is.
    #[must_use]
    pub fn permits(self, required: Self) -> bool {
        match (self, required) {
            (Self::Call, _) => true,
            (Self::Proof, Self::Proof) => true,
            (Self::Proof, Self::Call) => false,
        }
    }

    /// Least upper bound in the authority order — the **stronger** capability.
    ///
    /// Deliberately rare in consumers. Joining capabilities *raises* authority,
    /// and every escalation to CALL in this crate goes through
    /// [`SymbolHeader::grant_call`], which demands evidence. `join` exists for
    /// completeness of the lattice (and so `meet`'s absorbing behaviour can be
    /// stated against its dual), not as a back door: it operates on capability
    /// *values*, never on a header.
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        if self.permits(other) { self } else { other }
    }

    /// Greatest lower bound in the authority order — the **weaker** capability.
    ///
    /// This is the firewall's operator. Folding `meet` over a reference set
    /// gives "as executable as the weakest thing reachable", which is exactly
    /// the transitive proof-only rule: one proof-only edge anywhere in the
    /// closure pulls the whole thing to [`Capability::Proof`].
    #[must_use]
    pub fn meet(self, other: Self) -> Self {
        if self.permits(other) { other } else { self }
    }

    /// The **observation** order, dual to the authority order: whether a use
    /// site holding `self` may *name* a symbol whose declared capability is
    /// `symbol`.
    ///
    /// A PROOF context names everything (§4.1.1, zero annotations). A CALL
    /// context names only what is executable. Note this is not `permits` with
    /// the arguments swapped in disguise — it is the statement that makes the
    /// asymmetry explicit at the call site rather than leaving the reader to
    /// work out which side of `permits` is which.
    #[must_use]
    pub fn observes_at_least(self, symbol: Self) -> bool {
        match self {
            // PROOF is total observer capability.
            Self::Proof => true,
            // CALL obeys the declaring language's ordinary visibility.
            Self::Call => symbol.permits(Self::Call),
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

/// A capability after the transitive firewall has run, or the fail-closed
/// admission that it could not be run (I3).
///
/// The third state is not a third capability. It is the statement "the
/// reference closure this answer would have to be taken over is incomplete",
/// and it is deliberately shaped like [`AxiomClosure::unrecorded`]: the rule
/// recorded in this crate's header — *a closure merged with an unrecorded one
/// is unrecorded* — is the same rule, applied to a different closure. An
/// unknown edge poisons the result rather than being assumed benign.
///
/// Fail-closed here means **falling to the bottom of the lattice, not
/// erroring**: [`EffectiveCapability::Unrecorded`] permits exactly what
/// [`Capability::LEAST`] permits, i.e. observation and nothing else. That is
/// the right answer rather than a lenient one — observation grants no
/// executable authority, so an unknown edge cannot make an observation unsound;
/// it can only make an *execution* unsound, and execution is what is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum EffectiveCapability {
    /// The closure was complete and this is its meet.
    Determined(Capability),
    /// Some edge on some path was never recorded, or named a symbol the graph
    /// has no header for.
    Unrecorded,
}

impl EffectiveCapability {
    /// The strongest capability that may be *claimed* — `Unrecorded` claims
    /// [`Capability::LEAST`].
    #[must_use]
    pub fn claimable(self) -> Capability {
        match self {
            Self::Determined(capability) => capability,
            Self::Unrecorded => Capability::LEAST,
        }
    }

    /// Whether this permits a use requiring `required`.
    #[must_use]
    pub fn permits(self, required: Capability) -> bool {
        self.claimable().permits(required)
    }

    /// Whether this symbol may never emit a call or a load.
    #[must_use]
    pub fn is_proof_only(self) -> bool {
        !self.permits(Capability::Call)
    }

    /// Greatest lower bound, with `Unrecorded` **absorbing**.
    ///
    /// This is the line that makes the closure fail closed. It is stated as its
    /// own method, not inlined into the fixpoint, so that the absorbing
    /// behaviour is one testable fact rather than a property of a loop.
    #[must_use]
    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unrecorded, _) | (_, Self::Unrecorded) => Self::Unrecorded,
            (Self::Determined(a), Self::Determined(b)) => Self::Determined(a.meet(b)),
        }
    }

    /// The stable wire name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Determined(capability) => capability.name(),
            Self::Unrecorded => "unrecorded",
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
/// **`trust-clean-carrier` (I4) is the seam [`CarrierEvidence::Total`] plugs
/// into**, and I4 lands before any `DefId` is minted precisely so that
/// `Nat → u64` cannot be blessed by a defeq check that is already true of a
/// wrapping binary (§5(b)).
///
/// Since I4, `Total` is **not constructible by assignment**. It is reachable
/// only through [`SymbolHeader::with_total_carrier`], which demands a
/// [`CarrierWitness`], which in turn exists only as the `Ok` of
/// [`RepresentationObligation::discharge`]. [`SymbolHeader::with_carrier`]
/// cannot express it: its parameter type is [`UnwitnessedCarrier`], which has
/// no `Total` variant, so "someone set `Total` without an obligation" is not a
/// review failure — it does not compile.
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

/// Carrier evidence a caller may record without a witness.
///
/// Deliberately a *different type* from [`CarrierEvidence`] rather than a
/// runtime check on it: [`CarrierEvidence::Total`] is the one value that lets a
/// Clean declaration produce a Rust value, so the type system, not a code
/// review, is what keeps it out of an unchecked setter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[non_exhaustive]
pub enum UnwitnessedCarrier {
    /// No carrier.
    #[default]
    None,
    /// A carrier asserted by a caller and not proved. Grants nothing.
    Declared,
}

impl From<UnwitnessedCarrier> for CarrierEvidence {
    fn from(value: UnwitnessedCarrier) -> Self {
        match value {
            UnwitnessedCarrier::None => Self::None,
            UnwitnessedCarrier::Declared => Self::Declared,
        }
    }
}

/// How many distinct values a type can hold, as far as the carrier map knows.
///
/// This is the fact the faithfulness obligation turns on, and the reason it is
/// spelled as an enum rather than a `u32`: "unbounded" and "bounded by a number
/// I do not know yet" are different facts from "bounded by 64 bits", and
/// collapsing either onto a width is how `Nat` becomes `u64`.
///
/// **Deliberately NOT `#[non_exhaustive]`**, unlike everything else in this
/// crate's public vocabulary. `#[non_exhaustive]` forces every downstream match
/// to carry a wildcard arm, and a wildcard arm over a soundness classification
/// is a fail-open default waiting for a fifth variant. Adding a variant here
/// *should* break `trust-clean-carrier` at compile time and make someone decide
/// what it means — that is cheaper than a carrier map that silently sorts a new
/// kind of extent into whatever its `_` arm happened to do.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CarrierExtent {
    /// Exactly `2^bits` values, and arithmetic wraps at that modulus.
    Bits(u32),
    /// Unboundedly many values (`Nat`, `Int`). Never has a fixed-width carrier.
    Unbounded,
    /// Bounded, but by a width this compilation has not resolved (`USize`,
    /// whose width is `System.Platform.numBits`).
    TargetDependent,
    /// Not a type of values at all (`Prop`, a `Sort`). A proposition is
    /// observed, never produced.
    NotAValue,
}

/// Whether the carrier's operations agree with the Clean type's, not merely its
/// values.
///
/// Value-level injectivity is **not** sufficient and this enum is why. Clean
/// `UInt8` embeds injectively into Rust `u64`, yet `UInt8.add 200 100 = 44`
/// while `200u64 + 100u64 = 300`: a carrier faithful on values can still be
/// unfaithful on arithmetic, and the emitted binary follows the arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[non_exhaustive]
pub enum OperationAgreement {
    /// Nobody established it. The default, and it discharges nothing.
    #[default]
    Unestablished,
    /// Every operation of the Clean type is the carrier's operation on the
    /// nose — same result for every input, including at the wrap boundary.
    ExactOnEveryOperation,
    /// The carrier is a **trusted runtime**: a Trust-owned implementation of
    /// the Clean type's semantics, shipped and executed, whose agreement with
    /// the kernel is **evidence, not proof** — this variant is a TCB row by
    /// name (`docs/TCB.md`, "Bignum carrier runtime").
    ///
    /// Categorically different from [`Self::ExactOnEveryOperation`], which
    /// states a same-wrap-modulus fact checkable from the two extents alone.
    /// Here there is no modulus and nothing width-shaped to re-check: the claim
    /// is that `trust_bignum::Nat` (crates/trust-bignum) implements Lean `Nat`
    /// semantics exactly. The evidence class, stated honestly: (1)
    /// hardware-referenced `u128` agreement tests
    /// (crates/trust-bignum/tests/u64_agreement.rs, multi_limb.rs); (2)
    /// hand-transcribed Lean semantics pinned as tests with clean-kernel source
    /// citations (tests/lean_semantics.rs); (3) an **executed differential**
    /// against the real `clean_kernel` reduction lanes — kernel `whnf` of
    /// `Nat.add/sub/mul/div/mod/beq/ble` on randomized multi-limb literals
    /// versus this runtime (tests/kernel_differential.rs, a dev-dependency
    /// only; the shipped runtime stays independently authored and
    /// zero-dependency). A semantic mismatch here is a WRONG BINARY the kernel
    /// still accepts — which is why [`RepresentationObligation::discharge`]
    /// additionally pins the exact `(clean_type, rust_carrier)` pairing and
    /// refuses this agreement kind everywhere else.
    TrustedRuntimeAgreement,
}

/// How wide a discharged carrier is: a fixed number of bits, or unbounded and
/// exact via a trusted runtime.
///
/// **Deliberately NOT `#[non_exhaustive]`** — same rationale as
/// [`CarrierExtent`]: a wildcard arm over a soundness classification is a
/// fail-open default. A consumer that sizes a wire record or picks a rustc
/// type by width must decide what "unbounded" means for it, at compile time,
/// the day a variant is added.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CarrierWidth {
    /// Exactly this many bits, exact on every operation at that modulus.
    Bits(u32),
    /// Unbounded, exact on every value and operation **by trusted runtime**
    /// ([`OperationAgreement::TrustedRuntimeAgreement`] — a TCB row, not a
    /// proof).
    UnboundedExact,
}

/// The exact `(clean_type, rust_carrier)` pairings a
/// [`OperationAgreement::TrustedRuntimeAgreement`] discharge may witness —
/// one entry per shipped trusted runtime, kept in lockstep with the
/// `docs/TCB.md` carrier-runtime rows.
///
/// This table is what makes a witness for a pairing the runtime does not
/// carry **unconstructible** rather than merely undeclared. Both `Nat` and
/// `Int` honestly report [`CarrierExtent::Unbounded`], and
/// [`RepresentationObligation::new`] is public — so without the pin, any
/// unbounded/unbounded string pair stating `TrustedRuntimeAgreement` would
/// discharge, though ℤ is not carried by a ℕ runtime. An unverified caller
/// declaration may not shrink what the re-check is taken over (the
/// single-writer rule, applied here).
const TRUSTED_RUNTIME_CARRIERS: &[(&str, &str)] = &[("Nat", "trust_bignum::Nat")];

/// The representation-faithfulness obligation, stated so that **this** crate
/// can re-check it without an elaborator, a parser, or a kernel.
///
/// The producer (I4's `trust-clean-carrier`) supplies the facts; the re-check
/// below decides whether those facts entail faithfulness. That division is the
/// point. This crate cannot verify that `clean_extent` really is the extent of
/// `clean_type` — it deliberately cannot name a Clean parser. What it *can* do,
/// and does, is refuse to mint [`CarrierEvidence::Total`] for any obligation
/// whose own statement does not entail a faithful carrier, which is exactly the
/// `Nat → u64` case: an obligation that honestly reports
/// [`CarrierExtent::Unbounded`] can never discharge at any **fixed width**.
/// The sole unbounded lane (I6) is the pinned trusted-runtime pairing table
/// [`TRUSTED_RUNTIME_CARRIERS`] — `Nat` at `trust_bignum::Nat` — which is a
/// disclosed TCB row, not a width check, and is refused for every other pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepresentationObligation {
    clean_type: String,
    rust_carrier: String,
    clean_extent: CarrierExtent,
    rust_extent: CarrierExtent,
    operations: OperationAgreement,
}

impl RepresentationObligation {
    /// State the obligation.
    #[must_use]
    pub fn new(
        clean_type: impl Into<String>,
        rust_carrier: impl Into<String>,
        clean_extent: CarrierExtent,
        rust_extent: CarrierExtent,
        operations: OperationAgreement,
    ) -> Self {
        Self {
            clean_type: clean_type.into(),
            rust_carrier: rust_carrier.into(),
            clean_extent,
            rust_extent,
            operations,
        }
    }

    /// The Clean type the obligation is about.
    #[must_use]
    pub fn clean_type(&self) -> &str {
        &self.clean_type
    }

    /// The Rust carrier proposed for it.
    #[must_use]
    pub fn rust_carrier(&self) -> &str {
        &self.rust_carrier
    }

    /// Discharge it, or say precisely which clause failed.
    ///
    /// Two arms, each fail-closed on the agreement KIND its extents require:
    ///
    /// * **Fixed-width** — both extents are [`CarrierExtent::Bits`], the two
    ///   widths are **equal** (not `≤`: a narrowing truncates; a widening
    ///   preserves values but changes the wrap modulus, and the binary follows
    ///   the modulus), and the operations agree
    ///   [`OperationAgreement::ExactOnEveryOperation`]. A fixed-width pairing
    ///   claiming [`OperationAgreement::TrustedRuntimeAgreement`] is refused —
    ///   a width fact is checkable here and must be checked, never trusted.
    /// * **Trusted runtime (I6)** — both extents are
    ///   [`CarrierExtent::Unbounded`], the `(clean_type, rust_carrier)` pair is
    ///   in the pinned [`TRUSTED_RUNTIME_CARRIERS`] table, and the operations
    ///   are stated [`OperationAgreement::TrustedRuntimeAgreement`]. The
    ///   pairing pin comes FIRST: a witness for a pair no shipped runtime
    ///   carries (`Int` at `trust_bignum::Nat`) is unconstructible whatever
    ///   agreement was stated.
    ///
    /// Every other extent combination — mixed, target-dependent, non-value —
    /// refuses via [`ObligationNotDischarged::NoFixedExtent`].
    ///
    /// # Errors
    ///
    /// [`ObligationNotDischarged`], naming the failing clause and the fix.
    pub fn discharge(self) -> Result<CarrierWitness, ObligationNotDischarged> {
        match (self.clean_extent, self.rust_extent) {
            (CarrierExtent::Bits(clean_bits), CarrierExtent::Bits(rust_bits)) => {
                if clean_bits != rust_bits {
                    return Err(ObligationNotDischarged::ExtentMismatch {
                        clean_type: self.clean_type,
                        rust_carrier: self.rust_carrier,
                        clean_bits,
                        rust_bits,
                    });
                }
                match self.operations {
                    OperationAgreement::ExactOnEveryOperation => Ok(CarrierWitness {
                        clean_type: self.clean_type,
                        rust_carrier: self.rust_carrier,
                        width: CarrierWidth::Bits(clean_bits),
                    }),
                    // A trusted-runtime claim on a FIXED-WIDTH pairing is the
                    // wrong kind of evidence, not merely absent evidence: the
                    // width fact is checkable, so trusting is refused.
                    stated @ OperationAgreement::TrustedRuntimeAgreement => {
                        Err(ObligationNotDischarged::WrongAgreementKind {
                            clean_type: self.clean_type,
                            rust_carrier: self.rust_carrier,
                            stated,
                            required: OperationAgreement::ExactOnEveryOperation,
                        })
                    }
                    _ => Err(ObligationNotDischarged::OperationsUnestablished {
                        clean_type: self.clean_type,
                        rust_carrier: self.rust_carrier,
                    }),
                }
            }
            (CarrierExtent::Unbounded, CarrierExtent::Unbounded) => {
                // THE PAIRING PIN, first. Both `Nat` and `Int` honestly report
                // `Unbounded` and `RepresentationObligation::new` is public, so
                // without this check any unbounded/unbounded string pair
                // stating `TrustedRuntimeAgreement` would witness — including
                // pairs no shipped runtime carries. Producer discipline in the
                // carrier map is not a re-check.
                if !TRUSTED_RUNTIME_CARRIERS
                    .contains(&(self.clean_type.as_str(), self.rust_carrier.as_str()))
                {
                    return Err(ObligationNotDischarged::UntrustedRuntimePairing {
                        clean_type: self.clean_type,
                        rust_carrier: self.rust_carrier,
                    });
                }
                match self.operations {
                    OperationAgreement::TrustedRuntimeAgreement => Ok(CarrierWitness {
                        clean_type: self.clean_type,
                        rust_carrier: self.rust_carrier,
                        width: CarrierWidth::UnboundedExact,
                    }),
                    OperationAgreement::Unestablished => {
                        Err(ObligationNotDischarged::OperationsUnestablished {
                            clean_type: self.clean_type,
                            rust_carrier: self.rust_carrier,
                        })
                    }
                    // `ExactOnEveryOperation` states a wrap-modulus fact, and
                    // an unbounded type has no modulus: the statement itself is
                    // ill-formed here, so it is refused as the wrong KIND
                    // rather than folded into the trusted lane. (Any future
                    // agreement variant lands here too — fail-closed.)
                    stated => Err(ObligationNotDischarged::WrongAgreementKind {
                        clean_type: self.clean_type,
                        rust_carrier: self.rust_carrier,
                        stated,
                        required: OperationAgreement::TrustedRuntimeAgreement,
                    }),
                }
            }
            (clean_extent, rust_extent) => Err(ObligationNotDischarged::NoFixedExtent {
                clean_type: self.clean_type,
                rust_carrier: self.rust_carrier,
                clean_extent,
                rust_extent,
            }),
        }
    }
}

/// Proof-of-discharge for one carrier. **The only thing that mints
/// [`CarrierEvidence::Total`].**
///
/// Its fields are private and it has no public constructor: the sole way to
/// obtain one is [`RepresentationObligation::discharge`], so a `CarrierWitness`
/// in hand *is* the statement "the faithfulness obligation was stated and it
/// passed the re-check".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierWitness {
    clean_type: String,
    rust_carrier: String,
    width: CarrierWidth,
}

impl CarrierWitness {
    /// The Clean type carried.
    #[must_use]
    pub fn clean_type(&self) -> &str {
        &self.clean_type
    }

    /// The Rust carrier.
    #[must_use]
    pub fn rust_carrier(&self) -> &str {
        &self.rust_carrier
    }

    /// The discharged width: a common fixed width, or unbounded-exact by
    /// trusted runtime. (Replaces the old `bits() -> u32` — a hard rename, so
    /// every consumer decides what "unbounded" means for it.)
    #[must_use]
    pub fn width(&self) -> CarrierWidth {
        self.width
    }
}

impl fmt::Display for CarrierWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.width {
            CarrierWidth::Bits(bits) => write!(
                f,
                "{} carried by {} ({} bits, exact)",
                self.clean_type, self.rust_carrier, bits
            ),
            CarrierWidth::UnboundedExact => write!(
                f,
                "{} carried by {} (unbounded, exact by trusted runtime)",
                self.clean_type, self.rust_carrier
            ),
        }
    }
}

/// Why the representation-faithfulness obligation did not discharge.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ObligationNotDischarged {
    /// One of the two types has no fixed number of bits.
    NoFixedExtent {
        /// The Clean type.
        clean_type: String,
        /// The proposed Rust carrier.
        rust_carrier: String,
        /// What the Clean type's extent was stated to be.
        clean_extent: CarrierExtent,
        /// What the Rust carrier's extent was stated to be.
        rust_extent: CarrierExtent,
    },
    /// Both are fixed-width, but the widths differ.
    ExtentMismatch {
        /// The Clean type.
        clean_type: String,
        /// The proposed Rust carrier.
        rust_carrier: String,
        /// The Clean type's width.
        clean_bits: u32,
        /// The carrier's width.
        rust_bits: u32,
    },
    /// The widths line up but nobody established that the operations do.
    OperationsUnestablished {
        /// The Clean type.
        clean_type: String,
        /// The proposed Rust carrier.
        rust_carrier: String,
    },
    /// The agreement KIND stated is not the kind this pairing's extents
    /// require: a fixed-width pairing claiming a trusted runtime (a checkable
    /// fact must be checked, never trusted), or an unbounded pairing claiming
    /// a wrap-modulus fact (there is no modulus to state).
    WrongAgreementKind {
        /// The Clean type.
        clean_type: String,
        /// The proposed Rust carrier.
        rust_carrier: String,
        /// The agreement the obligation stated.
        stated: OperationAgreement,
        /// The agreement kind this pairing's extents require.
        required: OperationAgreement,
    },
    /// An unbounded/unbounded pairing outside the pinned
    /// [`TRUSTED_RUNTIME_CARRIERS`] table: no shipped trusted runtime carries
    /// it, so a trusted-runtime discharge is unconstructible for it — `Int` at
    /// `trust_bignum::Nat` is the canonical instance (ℤ is not carried by a ℕ
    /// runtime, though both honestly report `Unbounded`).
    UntrustedRuntimePairing {
        /// The Clean type.
        clean_type: String,
        /// The proposed Rust carrier.
        rust_carrier: String,
    },
}

impl fmt::Display for ObligationNotDischarged {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoFixedExtent { clean_type, rust_carrier, clean_extent, rust_extent } => write!(
                f,
                "`{clean_type}` has no faithful `{rust_carrier}` carrier: its extent is \
                 {clean_extent:?} and the carrier's is {rust_extent:?}, so no total map \
                 exists — the carrier would have to truncate, and a truncating carrier \
                 emits a wrong binary that the kernel still accepts.\n\
                 options: (1) give the declaration a fixed-width Clean type (`UInt8`, \
                 `UInt16`, `UInt32`, `UInt64`, `Bool`) and take the exact carrier; \
                 (2) keep it PROOF-only — an unbounded or dependent type keeps PROOF and \
                 loses CALL, and is never approximated; (3) if the value is genuinely \
                 unbounded, drop the fixed-width request and take the default carrier — \
                 `Nat` is carried by `trust_bignum::Nat`, exactly and unboundedly, with \
                 no source change"
            ),
            Self::ExtentMismatch { clean_type, rust_carrier, clean_bits, rust_bits } => write!(
                f,
                "`{clean_type}` is {clean_bits} bits and `{rust_carrier}` is {rust_bits} \
                 bits, so the carrier is not exact. A narrowing truncates; a widening \
                 keeps every value but changes the wrap modulus, and the emitted \
                 arithmetic follows the modulus.\n\
                 options: (1) request the exact carrier for a {clean_bits}-bit Clean \
                 type; (2) change the Clean type to the {rust_bits}-bit one, so both \
                 sides agree by construction; (3) keep it PROOF-only"
            ),
            Self::OperationsUnestablished { clean_type, rust_carrier } => write!(
                f,
                "`{clean_type}` and `{rust_carrier}` are the same width, but nobody \
                 established that their operations agree — equal cardinality is not \
                 representation faithfulness.\n\
                 options: (1) supply `OperationAgreement::ExactOnEveryOperation` from a \
                 carrier map that models the type's arithmetic; (2) keep it PROOF-only"
            ),
            Self::WrongAgreementKind { clean_type, rust_carrier, stated, required } => write!(
                f,
                "`{clean_type}` at `{rust_carrier}` stated the wrong KIND of operation \
                 agreement: {stated:?}, where this pairing's extents require \
                 {required:?}. A fixed-width pairing must state the checkable \
                 wrap-modulus fact — a checkable fact is checked, never trusted; an \
                 unbounded pairing has no modulus to state and can only be carried by \
                 a trusted runtime, disclosed as such.\n\
                 options: (1) state {required:?} from a carrier map that actually \
                 establishes it for this pairing; (2) keep the declaration PROOF-only; \
                 (3) if this is a new runtime-carried pairing, extend the trusted \
                 runtime AND the pinned pairing table AND the docs/TCB.md row \
                 together — extending capability extends the CHECK, never trust (v7/D2)"
            ),
            Self::UntrustedRuntimePairing { clean_type, rust_carrier } => write!(
                f,
                "`{clean_type}` at `{rust_carrier}`: both are unbounded, but no shipped \
                 trusted runtime carries this pairing, so the trusted-runtime discharge \
                 is refused. Unbounded extents alone do not make a carrier — `Int` at \
                 `trust_bignum::Nat` is the canonical wrong pair: a natural-number \
                 runtime carries no negative value, and the emitted binary would follow \
                 the runtime.\n\
                 options: (1) if the value is a natural number, declare it `Nat` and \
                 take the pinned carrier `trust_bignum::Nat`; (2) keep the declaration \
                 PROOF-only, where an unbounded type is free; (3) if this pairing should \
                 be carried, ship its runtime and extend the pinned table AND the \
                 docs/TCB.md row together — extending capability extends the CHECK, \
                 never trust (v7/D2)"
            ),
        }
    }
}

impl std::error::Error for ObligationNotDischarged {}

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
    /// reflection is TCB, and the status has to say so rather than let a
    /// reflected carrier be cited where a kernel-checked declaration is
    /// required. I2's control is exactly that refusal, and
    /// [`KernelStatus::require_kernel_check`] is the seam that performs it.
    ///
    /// Where the trust actually sits, in `docs/TCB.md` terms: the reflection is
    /// the "construction of the goal" clause of the `EnsuresCitationDischarge`
    /// row — *"that the goal really is the authored clause with `result` bound
    /// to the E6-imported defining equation"*. The kernel re-checks the cited
    /// theorem against that goal; nothing re-checks that the imported constant
    /// denotes the Rust `fn` it was minted from.
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
            _ => {
                Certification { tier: CertificationTier::NotKernelChecked, assumptions: Vec::new() }
            }
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

    /// Whether this symbol is a reflected Rust carrier (I2).
    #[must_use]
    pub fn is_reflected(&self) -> bool {
        matches!(self, Self::Reflected)
    }

    /// Demand a kernel re-check **at a citation site**, and refuse anything
    /// else.
    ///
    /// This is I2's enforcement seam. The decision of record
    /// (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7)
    /// states the control this method exists to pass: *"a `Reflected` symbol
    /// cited where `KernelChecked` is required must be REFUSED, not silently
    /// accepted."*
    ///
    /// The reason it cannot be a `matches!` at each call site is the reason
    /// [`Certification`] is not an enum variant: the refusal has to *explain
    /// itself*, and the explanation for a reflected carrier is specific —
    /// the kernel checked that the carrier's body inhabits its type, and never
    /// checked that the carrier **denotes** the Rust item, because that
    /// correspondence is asserted by the compiler and is TCB. A caller that
    /// accepts a `Reflected` symbol here reports a claim the kernel never made.
    ///
    /// Fail-closed by construction: every non-`KernelChecked` status — including
    /// any variant added later, since the enum is `#[non_exhaustive]` — refuses.
    ///
    /// # Errors
    ///
    /// [`KernelCheckRequired`] whenever the kernel did not re-check this
    /// declaration's own obligation.
    pub fn require_kernel_check(
        &self,
        cited_as: &str,
    ) -> Result<&KernelVerdict, KernelCheckRequired> {
        match self {
            Self::KernelChecked(verdict) => Ok(verdict),
            other => Err(KernelCheckRequired {
                cited_as: cited_as.to_string(),
                status: other.name(),
                reflected: other.is_reflected(),
            }),
        }
    }
}

/// A symbol was cited where a Clean CIC kernel re-check is required, and it
/// does not carry one.
///
/// Produced only by [`KernelStatus::require_kernel_check`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelCheckRequired {
    cited_as: String,
    status: &'static str,
    reflected: bool,
}

impl KernelCheckRequired {
    /// The name as it was cited.
    #[must_use]
    pub fn cited_as(&self) -> &str {
        &self.cited_as
    }

    /// The wire name of the status the symbol actually carries.
    #[must_use]
    pub fn status_name(&self) -> &'static str {
        self.status
    }

    /// Whether the refused symbol was a reflected Rust carrier — the I2 case,
    /// which gets the reflection-specific explanation.
    #[must_use]
    pub fn is_reflected(&self) -> bool {
        self.reflected
    }
}

impl fmt::Display for KernelCheckRequired {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { cited_as, status, reflected } = self;
        write!(
            f,
            "`{cited_as}` is a `{status}` symbol, but this position requires a \
             declaration the Clean CIC kernel re-checked (`kernel-checked`)."
        )?;
        if *reflected {
            write!(
                f,
                " A reflected symbol is a Rust item projected into the Clean \
                 environment by the compiler (I2): the kernel checked that the \
                 carrier's body inhabits its type, but it never re-checked that \
                 the carrier DENOTES the Rust item — that correspondence is \
                 asserted by the compiler and is TCB (`docs/TCB.md`).\n\
                 options: (1) cite the Clean declaration this position is for — \
                 a `def` written in a `clean {{ … }}` island, which the kernel \
                 does re-check; (2) if you meant to reason ABOUT the Rust item, \
                 state a Clean `theorem` over the reflected carrier and cite \
                 THAT theorem: the theorem is kernel-checked even though the \
                 carrier it mentions is not; (3) keep the reflected carrier and \
                 use it where a reflected carrier is what is required — a spec \
                 call site — where it is admitted and reported without a \
                 kernel-check claim"
            )
        } else {
            write!(
                f,
                "\noptions: (1) let the kernel re-check it — a `{status}` symbol \
                 has not reached the certification audit yet; (2) cite a \
                 declaration that has; (3) keep it and accept a row that is not \
                 reported Certified"
            )
        }
    }
}

impl std::error::Error for KernelCheckRequired {}

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
                let listed =
                    self.assumptions.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ");
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
/// value. That last step is a review obligation on the call sites that link
/// `clean-kernel` and this crate together, which is the smallest surface it can
/// be reduced to. Today that is **one** site, and it is enumerated here so the
/// count cannot drift silently:
///
/// * `trust_certify::clean_island::admit_certified_island_definition` (I2) —
///   mints the status for a Clean island `def` after `cert_meter::grade`
///   returns `Certified`. Reviewed against the three clauses below at the call
///   site itself.
///
/// `trust-clean-env` (the planned I1 crate) will be the second when it lands.
/// A reflected Rust carrier is deliberately **not** on this list: it gets
/// [`KernelStatus::Reflected`], which any crate may set, precisely because the
/// reflection is TCB.
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
    /// The discharge that justified `carrier == Total`, kept for audit. `None`
    /// for every other carrier state, and the two move together: `Total` is set
    /// only by `with_total_carrier`, which sets this at the same time.
    carrier_witness: Option<CarrierWitness>,
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
            carrier_witness: None,
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

    /// The discharge that justified a `Total` carrier, if there is one.
    ///
    /// `Some` exactly when [`Self::carrier`] is [`CarrierEvidence::Total`].
    #[must_use]
    pub fn carrier_witness(&self) -> Option<&CarrierWitness> {
        self.carrier_witness.as_ref()
    }

    /// Record carrier evidence that needs no witness (I4).
    ///
    /// [`CarrierEvidence::Total`] is **not expressible here** — the parameter
    /// is [`UnwitnessedCarrier`], which has no `Total` variant. That is the
    /// whole mechanism: the value that grants CALL cannot be assigned, only
    /// witnessed. Use [`Self::with_total_carrier`].
    ///
    /// Recording an unwitnessed carrier over a witnessed one also drops the
    /// witness, so the pair can never disagree.
    #[must_use]
    pub fn with_carrier(mut self, carrier: UnwitnessedCarrier) -> Self {
        self.carrier = carrier.into();
        self.carrier_witness = None;
        self
    }

    /// Record a carrier whose representation-faithfulness obligation is
    /// discharged (I4) — the **only** route to [`CarrierEvidence::Total`] and
    /// therefore the only route to CALL.
    ///
    /// The witness is retained on the header so that an audit can ask *which*
    /// obligation justified the capability, rather than finding a bare enum
    /// value with no provenance.
    #[must_use]
    pub fn with_total_carrier(mut self, witness: CarrierWitness) -> Self {
        self.carrier = CarrierEvidence::Total;
        self.carrier_witness = Some(witness);
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
                 whose carrier is total (I5's first fragment); (2) if the \
                 value is a genuinely unbounded natural, declare it `Nat` — \
                 the I6 bignum carrier `trust_bignum::Nat` carries `Nat` \
                 exactly and unboundedly, with no width to pick; (3) keep it \
                 PROOF-only — a dependent or unbounded type keeps PROOF and \
                 loses CALL, and is never approximated"
            ),
        }
    }
}

impl std::error::Error for CapabilityRefused {}

/// What one declaration references, or the admission that we do not know.
///
/// Shaped like [`AxiomClosure`] on purpose: `Recorded(∅)` — "we looked and it
/// references nothing" — and `Unrecorded` — "nobody looked" — are different
/// facts, and collapsing them is how a closure silently becomes a promise.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReferenceSet {
    /// The producer enumerated this declaration's references. An empty set is
    /// a positive finding: a leaf.
    Recorded(BTreeSet<SymbolId>),
    /// No producer enumerated them. Poisons the closure.
    Unrecorded,
}

impl ReferenceSet {
    /// A recorded, audited-empty reference set — a leaf declaration.
    #[must_use]
    pub fn leaf() -> Self {
        Self::Recorded(BTreeSet::new())
    }
}

impl Default for ReferenceSet {
    /// [`ReferenceSet::Unrecorded`]. A `#[derive(Default)]` downstream must not
    /// be able to mint a leaf by omission — same reason
    /// [`AxiomClosure::default`] is `unrecorded`.
    fn default() -> Self {
        Self::Unrecorded
    }
}

/// Why a symbol may be observed but not executed.
///
/// One spelling of the refusal, in the crate that owns the lattice, so the
/// elaborator and any future CALL-position consumer cannot drift into two
/// different sentences about one rule. The wording is mandated: **"visible but
/// not executable"**, never "not found" — the symbol *is* found, and saying
/// otherwise sends the reader to look for a typo that is not there.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofOnlyRefusal {
    /// The symbol itself grants PROOF only.
    Declared {
        /// The symbol, as the use site spelled it.
        symbol: String,
    },
    /// The symbol grants CALL, but its reference closure reaches something
    /// that does not.
    Transitive {
        /// The symbol, as the use site spelled it.
        symbol: String,
        /// A proof-only symbol reachable from it. One witness, not the set —
        /// the first one is what the reader has to fix.
        via: String,
    },
    /// The reference closure is incomplete, so no CALL claim can be made.
    ClosureUnrecorded {
        /// The symbol, as the use site spelled it.
        symbol: String,
    },
}

impl ProofOnlyRefusal {
    /// The symbol the refusal is about, as spelled by the use site.
    #[must_use]
    pub fn symbol(&self) -> &str {
        match self {
            Self::Declared { symbol }
            | Self::Transitive { symbol, .. }
            | Self::ClosureUnrecorded { symbol } => symbol,
        }
    }
}

impl fmt::Display for ProofOnlyRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declared { symbol } => write!(
                f,
                "`{symbol}` is visible but not executable: it is a PROOF-only \
                 declaration, and this position needs a value. Observation \
                 grants no executable authority — that is what makes total \
                 proof visibility sound, so this is a capability refusal and \
                 NOT a name-resolution failure; the declaration is right where \
                 you think it is.\n\
                 options: (1) name it from a proof position instead — a \
                 `requires`/`ensures` clause or a `clean {{ … }}` island may \
                 name it with no annotation at all, including private \
                 internals; (2) if you need the value, give the declaration a \
                 total Rust carrier so CALL can be granted (increment I4 \
                 mints the carrier, I5 the `DefId`); (3) state the property \
                 you wanted through the declaration's operational relation and \
                 keep the executable path in Rust"
            ),
            Self::Transitive { symbol, via } => write!(
                f,
                "`{symbol}` is visible but not executable: it is PROOF-only \
                 transitively, because its reference closure reaches the \
                 PROOF-only `{via}`. A declaration is at most as executable as \
                 the weakest thing it references — a proof-only edge can never \
                 emit a call or a load, feed const evaluation, determine \
                 layout, dispatch or monomorphization, or discharge an unsafe \
                 obligation, and that restriction is inherited by everything \
                 built on it.\n\
                 options: (1) name `{symbol}` from a proof position, where the \
                 whole closure is observable; (2) make `{via}` executable — it \
                 is the binding edge, and granting it CALL lifts `{symbol}` \
                 with no other change; (3) split `{symbol}` so the executable \
                 half does not reference `{via}`"
            ),
            Self::ClosureUnrecorded { symbol } => write!(
                f,
                "`{symbol}` is visible but not executable: its reference \
                 closure is INCOMPLETE, so no CALL claim can be made about it. \
                 This is not a finding that `{symbol}` is proof-only — it is \
                 the refusal to guess. A closure is only as good as its worst \
                 component, so an unrecorded edge poisons the answer rather \
                 than being assumed benign.\n\
                 options: (1) record the declaration's references (a leaf \
                 records `ReferenceSet::leaf()`, which is a positive finding \
                 and not the same as recording nothing); (2) name it from a \
                 proof position, which needs no closure at all because \
                 observation grants no executable authority; (3) if the \
                 producer genuinely cannot enumerate references for this sort \
                 of declaration, it keeps PROOF — that is the fail-closed \
                 state and it is never widened by default"
            ),
        }
    }
}

impl std::error::Error for ProofOnlyRefusal {}

/// The transitive proof-only firewall, computed (I3).
///
/// One [`EffectiveCapability`] per symbol, being the meet of the symbol's own
/// declared capability with the effective capability of everything reachable
/// from it. Built by [`SymbolGraph::capability_closure`]; there is no
/// constructor that takes a map, because a closure someone assembled by hand
/// is a promise, and this type exists to not be one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityClosure {
    effective: BTreeMap<SymbolId, EffectiveCapability>,
    /// The proof-only witness for each transitively-demoted symbol.
    witness: BTreeMap<SymbolId, SymbolId>,
}

impl CapabilityClosure {
    /// The effective capability of `id`.
    ///
    /// A symbol the graph never saw answers [`EffectiveCapability::Unrecorded`]
    /// rather than `None`: a consumer that cannot determine a capability must
    /// refuse, and an `Option` invites `unwrap_or(Call)`.
    #[must_use]
    pub fn effective(&self, id: &SymbolId) -> EffectiveCapability {
        self.effective.get(id).copied().unwrap_or(EffectiveCapability::Unrecorded)
    }

    /// Whether `id` may never emit a call or a load.
    #[must_use]
    pub fn is_proof_only(&self, id: &SymbolId) -> bool {
        self.effective(id).is_proof_only()
    }

    /// Every row, in path order.
    pub fn rows(&self) -> impl Iterator<Item = (&SymbolId, EffectiveCapability)> {
        self.effective.iter().map(|(id, capability)| (id, *capability))
    }

    /// Enforce the firewall at a use site.
    ///
    /// `use_site` is the capability the *position* holds — PROOF for a spec
    /// clause or a `clean { … }` island, CALL for anything that will emit a
    /// call, a load, a const evaluation or a layout decision. `spelled` is how
    /// the use site named the symbol, so the refusal quotes the user's text.
    ///
    /// # Errors
    ///
    /// [`ProofOnlyRefusal`] when the position needs CALL and the closure does
    /// not grant it. A PROOF use site never errors — §4.1.1 gives it total
    /// observer capability, and that is control (b) of I3.
    pub fn require(
        &self,
        id: &SymbolId,
        use_site: Capability,
        spelled: &str,
    ) -> Result<(), ProofOnlyRefusal> {
        let effective = self.effective(id);
        if use_site.observes_at_least(effective.claimable()) {
            return Ok(());
        }
        Err(match effective {
            EffectiveCapability::Unrecorded => {
                ProofOnlyRefusal::ClosureUnrecorded { symbol: spelled.to_string() }
            }
            EffectiveCapability::Determined(_) => match self.witness.get(id) {
                Some(via) => ProofOnlyRefusal::Transitive {
                    symbol: spelled.to_string(),
                    via: via.path().to_string(),
                },
                None => ProofOnlyRefusal::Declared { symbol: spelled.to_string() },
            },
        })
    }
}

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
///
/// # I3 — it is a graph now, and the edges are what the firewall runs on
///
/// Before I3 this type was a `BTreeMap` with a graph's name: it stored headers
/// and no relation, so "proof-private references are tagged proof-only,
/// **transitively**" had nothing to be transitive over. `references` is that
/// relation. It is kept beside `headers` rather than inside [`SymbolHeader`]
/// because a header is phase-1 information — available before any body is
/// elaborated — whereas what a declaration references is phase-2 information,
/// and a field that is `Unrecorded` for the entire first phase invites a reader
/// to treat `Unrecorded` as "not yet" rather than as "refuse".
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolGraph {
    headers: BTreeMap<SymbolId, SymbolHeader>,
    references: BTreeMap<SymbolId, ReferenceSet>,
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

    /// Phase 2: record what `id` references.
    ///
    /// An empty `refs` is a **positive finding** — this declaration is a leaf —
    /// and is not the same as never calling this method, which leaves the
    /// symbol [`ReferenceSet::Unrecorded`] and poisons every closure through
    /// it. That asymmetry is the whole fail-closed rule; see
    /// [`SymbolGraph::capability_closure`].
    ///
    /// References to symbols the graph has no header for are accepted and
    /// recorded: they are not a caller error, they are a *finding*, and the
    /// closure turns them into [`EffectiveCapability::Unrecorded`] there. A
    /// producer that had to drop an unknown edge to satisfy this method would
    /// be recording a smaller, cleaner, wrong closure.
    ///
    /// # Errors
    ///
    /// [`UnknownSymbol`] if phase 1 never saw `id` itself.
    pub fn record_references<I>(&mut self, id: &SymbolId, refs: I) -> Result<(), UnknownSymbol>
    where
        I: IntoIterator<Item = SymbolId>,
    {
        if !self.headers.contains_key(id) {
            return Err(UnknownSymbol { id: id.clone() });
        }
        self.references.insert(id.clone(), ReferenceSet::Recorded(refs.into_iter().collect()));
        Ok(())
    }

    /// What `id` references. A symbol phase 2 never spoke about answers
    /// [`ReferenceSet::Unrecorded`].
    #[must_use]
    pub fn references(&self, id: &SymbolId) -> &ReferenceSet {
        const UNRECORDED: &ReferenceSet = &ReferenceSet::Unrecorded;
        self.references.get(id).unwrap_or(UNRECORDED)
    }

    /// Compute the transitive proof-only firewall (I3).
    ///
    /// The equation, stated once so the loop below is only its implementation:
    ///
    /// ```text
    ///   eff(s) = declared(s) ⊓ ⨅ { eff(t) | t ∈ refs(s) }
    /// ```
    ///
    /// with `⊓` [`EffectiveCapability::meet`], `refs(s) = Unrecorded` and any
    /// `t` with no header both yielding [`EffectiveCapability::Unrecorded`],
    /// which is absorbing. Read plainly: **a declaration is at most as
    /// executable as the weakest thing it references, and not knowing what it
    /// references is worse than knowing something bad.**
    ///
    /// Computed as a greatest fixpoint descending from the declared
    /// capabilities. That polarity matters: starting at the top and descending
    /// makes a **cycle** — two mutually-referencing declarations — settle at
    /// the meet of the cycle rather than deadlock or default to `Call`, so a
    /// recursive `def` is handled by the algorithm and not by a special case.
    /// The chain has height 3 (`Unrecorded < Proof < Call`), so the loop
    /// converges in at most `len` rounds; the bound is asserted rather than
    /// assumed.
    #[must_use]
    pub fn capability_closure(&self) -> CapabilityClosure {
        let mut effective: BTreeMap<SymbolId, EffectiveCapability> = self
            .headers
            .iter()
            .map(|(id, header)| (id.clone(), EffectiveCapability::Determined(header.capability)))
            .collect();
        let mut witness: BTreeMap<SymbolId, SymbolId> = BTreeMap::new();

        // Descend to the fixpoint. `len + 1` rounds is a strict upper bound:
        // each round that changes anything lowers at least one symbol along a
        // 3-high chain, and the extra round is the one that observes stability.
        for _ in 0..=self.headers.len() {
            let mut changed = false;
            for id in self.headers.keys() {
                let declared = EffectiveCapability::Determined(self.headers[id].capability);
                let (folded, found) = match self.references(id) {
                    ReferenceSet::Unrecorded => (EffectiveCapability::Unrecorded, None),
                    ReferenceSet::Recorded(refs) => {
                        let mut acc = declared;
                        let mut first_proof_only = None;
                        for target in refs {
                            let target_effective = match effective.get(target) {
                                Some(value) => *value,
                                // An edge to a symbol with no header: we know
                                // the edge exists and nothing about where it
                                // goes. Poison, do not skip.
                                None => EffectiveCapability::Unrecorded,
                            };
                            if first_proof_only.is_none() && target_effective.is_proof_only() {
                                first_proof_only = Some(target.clone());
                            }
                            acc = acc.meet(target_effective);
                        }
                        (acc, first_proof_only)
                    }
                };
                if effective[id] != folded {
                    effective.insert(id.clone(), folded);
                    changed = true;
                }
                // Record the witness only when the symbol's OWN capability was
                // adequate and an edge is what removed it — otherwise the
                // refusal would blame a neighbour for a local decision.
                if declared.permits(Capability::Call) && folded.is_proof_only() {
                    if let Some(via) = found {
                        witness.insert(id.clone(), via);
                    }
                }
            }
            if !changed {
                return CapabilityClosure { effective, witness };
            }
        }
        // Unreachable for a 3-high chain; if the lattice ever grows, this is
        // the fail-closed exit rather than a silently truncated iteration.
        CapabilityClosure {
            effective: effective
                .into_keys()
                .map(|id| (id, EffectiveCapability::Unrecorded))
                .collect(),
            witness: BTreeMap::new(),
        }
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
/// # 4. `CarrierEvidence::Total` cannot be assigned (I4)
///
/// The carrier seam is the same shape as the kernel seam one layer down, and
/// it matters more: a false `KernelChecked` costs a wrong *claim*, a false
/// `Total` costs a wrong *binary*. `with_carrier` takes an
/// [`UnwitnessedCarrier`], which has no `Total` variant, so the assignment is
/// not a review item — it is a type error.
///
/// ```compile_fail,E0308
/// use trust_symbols::{CarrierEvidence, Producer, SegmentPath, Sort, SymbolHeader};
///
/// let path = SegmentPath::parse_rust("crate::f").unwrap();
/// let _ = SymbolHeader::new(path, Sort::Term, Producer::Clean)
///     .with_carrier(CarrierEvidence::Total);
/// ```
///
/// # 5. `CarrierWitness` cannot be written as a literal
///
/// The other way in is to build the witness directly. Its fields are private
/// and it has no public constructor: `RepresentationObligation::discharge` is
/// the only producer.
///
/// ```compile_fail,E0451
/// let _ = trust_symbols::CarrierWitness {
///     clean_type: "Nat".into(),
///     rust_carrier: "u64".into(),
///     width: trust_symbols::CarrierWidth::Bits(64),
/// };
/// ```
///
/// # 6. The positive control — this one MUST compile
///
/// If the five above failed for an unrelated reason (a typo, a renamed item)
/// they would still "pass", so the same API is exercised positively here. A
/// `compile_fail` block without this partner is not evidence.
///
/// ```
/// use trust_symbols::{
///     AxiomClosure, CarrierExtent, CarrierWidth, CicKernelRecheck, KernelAuthority,
///     OperationAgreement, RepresentationObligation, TermDigest,
/// };
///
/// let authority = CicKernelRecheck::held_by_kernel_recheck();
/// let status = authority.kernel_checked(TermDigest::of_bytes(b"term"), AxiomClosure::audited([]));
/// assert!(status.is_certified());
///
/// let witness = RepresentationObligation::new(
///     "UInt64",
///     "u64",
///     CarrierExtent::Bits(64),
///     CarrierExtent::Bits(64),
///     OperationAgreement::ExactOnEveryOperation,
/// )
/// .discharge()
/// .expect("exact carrier");
/// assert_eq!(witness.width(), CarrierWidth::Bits(64));
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

    /// The one discharged carrier obligation these tests use: Clean `UInt64`
    /// carried by Rust `u64`, exact on both extent and operations.
    ///
    /// It goes through `discharge()` rather than being fabricated, so every
    /// test that reaches `CarrierEvidence::Total` below reaches it the same way
    /// production code must.
    fn uint64_witness() -> CarrierWitness {
        RepresentationObligation::new(
            "UInt64",
            "u64",
            CarrierExtent::Bits(64),
            CarrierExtent::Bits(64),
            OperationAgreement::ExactOnEveryOperation,
        )
        .discharge()
        .expect("UInt64 -> u64 is exact on extent and operations")
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
            Err(PathError::SeparatorInSegment { segment: "m::f".to_string(), offender: ':' })
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
        let later =
            SymbolHeader::new(rust_path("crate::a::Later::step"), Sort::Term, Producer::Clean);
        let uses =
            SymbolHeader::new(rust_path("crate::b::uses_later"), Sort::Prop, Producer::Clean);

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

    /// **I2's control at the vocabulary level.** A `Reflected` symbol cited
    /// where a kernel re-check is required must be REFUSED, and the refusal
    /// must name the reflection specifically — "unsupported" with no next step
    /// is a defect (v7/D3).
    #[test]
    fn a_reflected_symbol_is_refused_where_a_kernel_check_is_required() {
        let reflected = KernelStatus::Reflected;
        let refusal = reflected
            .require_kernel_check("trust_import_crate__min2")
            .expect_err("a reflected carrier must be refused where KernelChecked is required");
        assert_eq!(refusal.status_name(), "reflected");
        assert!(refusal.is_reflected());
        assert_eq!(refusal.cited_as(), "trust_import_crate__min2");
        let text = refusal.to_string();
        assert!(text.contains("TCB"), "the refusal must say why: {text}");
        assert!(text.contains("options:"), "v7/D3: the refusal carries the fix: {text}");

        // Every other non-kernel-checked status refuses too — fail-closed is
        // the `_` arm, not an enumeration that a new variant can slip past.
        for status in [KernelStatus::Parsed, KernelStatus::Elaborated] {
            let refusal = status.require_kernel_check("x").expect_err("must refuse");
            assert!(!refusal.is_reflected());
            assert!(refusal.to_string().contains("options:"));
        }

        // And the kernel-checked one is admitted, carrying its verdict.
        let checked = certified_status();
        let verdict = checked.require_kernel_check("island_def").expect("kernel-checked passes");
        assert!(verdict.closure().is_audited_empty());
        assert!(!checked.is_reflected());
    }

    /// A reflected carrier is never Certified and never CALL-able, and the
    /// disclosure says which of the two it is.
    #[test]
    fn a_reflected_carrier_is_proof_only_and_not_certified() {
        let path = SegmentPath::parse_rust("crate::min2").unwrap();
        let header = SymbolHeader::new(path, Sort::Term, Producer::Rust)
            .with_status(KernelStatus::Reflected)
            .with_total_carrier(uint64_witness());
        assert_eq!(header.status().name(), "reflected");
        assert!(!header.status().is_certified());
        assert_eq!(header.status().certification().tier(), CertificationTier::NotKernelChecked);
        // A total carrier is NOT enough: CALL also needs Certified, which a
        // reflection can never reach.
        assert!(matches!(header.grant_call(), Err(CapabilityRefused::NotCertified { .. })));
        // `Reflected` carries no closure at all, and that is `unrecorded`,
        // never `empty` — the fail-closed side.
        assert!(!KernelStatus::Reflected.closure().is_recorded());
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
        let dependency = AxiomClosure::audited([Assumption::trust_marker("sorryAx").unwrap()]);
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

    // -- Capability: the lattice (I3) --------------------------------------

    /// The order of record is `Proof < Call` in AUTHORITY. The derived `Ord`
    /// agrees with it today only because the variants happen to be typed out
    /// in that order — so pin it, and a reorder breaks a test instead of
    /// silently inverting every `meet` in the firewall.
    #[test]
    fn the_capability_order_is_declared_not_accidental() {
        assert_eq!(Capability::AUTHORITY_ASCENDING, [Capability::Proof, Capability::Call]);
        assert!(Capability::Proof < Capability::Call, "derived Ord must be the authority order");
        assert_eq!(Capability::LEAST, Capability::Proof);
        assert_eq!(Capability::GREATEST, Capability::Call);
        for (i, weaker) in Capability::AUTHORITY_ASCENDING.iter().enumerate() {
            for stronger in &Capability::AUTHORITY_ASCENDING[i..] {
                assert!(stronger.permits(*weaker), "{stronger:?} must permit {weaker:?}");
            }
        }
    }

    /// A two-element chain, checked exhaustively: `join`/`meet` are the lub/glb
    /// of the authority order, absorbing/idempotent/commutative/associative.
    #[test]
    fn capability_is_a_lattice() {
        let all = Capability::AUTHORITY_ASCENDING;
        for a in all {
            assert_eq!(a.join(a), a, "idempotent");
            assert_eq!(a.meet(a), a, "idempotent");
            assert_eq!(a.join(Capability::LEAST), a, "LEAST is the join identity");
            assert_eq!(a.meet(Capability::GREATEST), a, "GREATEST is the meet identity");
            for b in all {
                assert_eq!(a.join(b), b.join(a), "commutative");
                assert_eq!(a.meet(b), b.meet(a), "commutative");
                assert!(a.join(b).permits(a), "join is an upper bound");
                assert!(a.permits(a.meet(b)), "meet is a lower bound");
                assert_eq!(a.join(b), std::cmp::max(a, b));
                assert_eq!(a.meet(b), std::cmp::min(a, b));
                for c in all {
                    assert_eq!(a.join(b).join(c), a.join(b.join(c)), "associative");
                    assert_eq!(a.meet(b).meet(c), a.meet(b.meet(c)), "associative");
                }
            }
        }
        // The sentence the whole firewall rests on.
        assert_eq!(Capability::Call.meet(Capability::Proof), Capability::Proof);
    }

    /// AUTHORITY and OBSERVATION are dual, and the duality is the ratified
    /// semantics: PROOF sees more SYMBOLS, CALL holds more AUTHORITY over one.
    /// If these ever coincide, someone has collapsed §4.1.1 into one axis.
    #[test]
    fn observation_is_the_dual_of_authority() {
        // §4.1.1: PROOF is total observer capability — it names EVERYTHING.
        assert!(Capability::Proof.observes_at_least(Capability::Proof));
        assert!(Capability::Proof.observes_at_least(Capability::Call));
        // CALL obeys ordinary visibility: it may not name a proof-only symbol.
        assert!(Capability::Call.observes_at_least(Capability::Call));
        assert!(!Capability::Call.observes_at_least(Capability::Proof));
        // Strictly more: the observation order is not the authority order.
        assert!(Capability::Proof.observes_at_least(Capability::Call));
        assert!(!Capability::Proof.permits(Capability::Call));
    }

    /// The visibility axis must not become a function of the frontend
    /// firewall's provenance axis (decision doc §2, and the rationale carried
    /// in `Capability`'s own doc comment). This is a *documentation* control:
    /// if the rationale is deleted, the reason the two are separate is gone and
    /// the next reader merges them.
    #[test]
    fn the_reason_capability_is_not_proofrole_survives_in_the_source() {
        let source = include_str!("lib.rs");
        assert!(
            source.contains("provenance-vs-belief"),
            "the ProofRole rationale must stay in-source next to `Capability`"
        );
        assert!(
            source.contains("how good the extractor happened to be"),
            "the ProofRole rationale must stay in-source next to `Capability`"
        );
    }

    // -- Capability: the transitive firewall (I3) ---------------------------

    fn term(graph: &mut SymbolGraph, path: &str) -> SymbolId {
        let header = SymbolHeader::new(rust_path(path), Sort::Term, Producer::Clean);
        let id = header.id().clone();
        graph.declare(header).expect("fresh path");
        id
    }

    fn callable_term(graph: &mut SymbolGraph, path: &str) -> SymbolId {
        let header = SymbolHeader::new(rust_path(path), Sort::Term, Producer::Rust)
            .with_status(certified_status())
            .with_total_carrier(uint64_witness())
            .grant_call()
            .expect("certified + total carrier");
        let id = header.id().clone();
        graph.declare(header).expect("fresh path");
        id
    }

    /// The closure's fail-closed default: a symbol whose references were never
    /// enumerated is `Unrecorded`, which permits observation and nothing else.
    /// `Recorded(∅)` is a DIFFERENT value — a positive leaf finding — and that
    /// difference is the entire rule.
    #[test]
    fn an_unrecorded_reference_set_is_not_an_empty_one() {
        assert_eq!(ReferenceSet::default(), ReferenceSet::Unrecorded);
        assert_ne!(ReferenceSet::leaf(), ReferenceSet::Unrecorded);

        let mut graph = SymbolGraph::new();
        let leaf = callable_term(&mut graph, "crate::leaf");
        let silent = callable_term(&mut graph, "crate::silent");
        graph.record_references(&leaf, []).expect("declared");

        let closure = graph.capability_closure();
        assert_eq!(closure.effective(&leaf), EffectiveCapability::Determined(Capability::Call));
        assert_eq!(closure.effective(&silent), EffectiveCapability::Unrecorded);
        assert!(closure.is_proof_only(&silent), "an unrecorded closure may not execute");
        assert!(!closure.effective(&silent).permits(Capability::Call));
        assert!(closure.effective(&silent).permits(Capability::Proof), "observation is unaffected");
    }

    /// The transitive rule itself: `g -> h -> proof_only` demotes BOTH, and the
    /// refusal names the binding edge rather than blaming the symbol the user
    /// wrote.
    #[test]
    fn proof_only_is_inherited_transitively() {
        let mut graph = SymbolGraph::new();
        let secret = term(&mut graph, "crate::secret"); // PROOF by construction
        let h = callable_term(&mut graph, "crate::h");
        let g = callable_term(&mut graph, "crate::g");
        graph.record_references(&secret, []).expect("declared");
        graph.record_references(&h, [secret.clone()]).expect("declared");
        graph.record_references(&g, [h.clone()]).expect("declared");

        let closure = graph.capability_closure();
        assert!(closure.is_proof_only(&secret));
        assert!(closure.is_proof_only(&h), "one proof-only edge demotes the referrer");
        assert!(closure.is_proof_only(&g), "and the demotion is transitive");

        // PROOF observes all three with no annotation (control (b), in-graph).
        for id in [&secret, &h, &g] {
            closure.require(id, Capability::Proof, "spelled").expect("PROOF names everything");
        }
        // CALL is refused, and the refusal names the WITNESS, not `g` itself.
        let err = closure.require(&g, Capability::Call, "g").expect_err("CALL must be refused");
        assert!(matches!(err, ProofOnlyRefusal::Transitive { .. }), "{err:?}");
        assert!(err.to_string().contains("visible but not executable"), "{err}");
        assert!(!err.to_string().contains("not found"), "{err}");
        assert!(err.to_string().contains("crate::h"), "the binding edge must be named: {err}");
        assert!(err.to_string().contains("options:"), "{err}");

        // A locally proof-only symbol is refused as DECLARED, not transitively.
        let err = closure.require(&secret, Capability::Call, "secret").expect_err("refused");
        assert!(matches!(err, ProofOnlyRefusal::Declared { .. }), "{err:?}");
    }

    /// An edge to a symbol with NO header poisons the closure. It is not
    /// skipped: "we know there is an edge and nothing about where it goes" is
    /// strictly worse than knowing it goes somewhere proof-only.
    #[test]
    fn an_edge_to_an_undeclared_symbol_poisons_the_closure() {
        let mut graph = SymbolGraph::new();
        let g = callable_term(&mut graph, "crate::g");
        let dangling = SymbolId::new(rust_path("crate::nowhere"), Namespace::Value);
        graph.record_references(&g, [dangling]).expect("declared");

        let closure = graph.capability_closure();
        assert_eq!(closure.effective(&g), EffectiveCapability::Unrecorded);
        let err = closure.require(&g, Capability::Call, "g").expect_err("refused");
        assert!(matches!(err, ProofOnlyRefusal::ClosureUnrecorded { .. }), "{err:?}");
        assert!(err.to_string().contains("visible but not executable"), "{err}");
        assert!(err.to_string().contains("INCOMPLETE"), "{err}");
    }

    /// `Unrecorded` is absorbing under `meet`, exactly as `AxiomClosure::merge`
    /// is on its own `unrecorded` — same rule, different closure.
    #[test]
    fn the_capability_meet_is_absorbing_on_unrecorded() {
        use EffectiveCapability::{Determined, Unrecorded};
        for value in [Determined(Capability::Call), Determined(Capability::Proof), Unrecorded] {
            assert_eq!(value.meet(Unrecorded), Unrecorded);
            assert_eq!(Unrecorded.meet(value), Unrecorded);
        }
        assert_eq!(
            Determined(Capability::Call).meet(Determined(Capability::Proof)),
            Determined(Capability::Proof)
        );
        assert_eq!(Unrecorded.claimable(), Capability::LEAST);
    }

    /// A reference CYCLE settles at the meet of the cycle instead of
    /// deadlocking or defaulting to `Call`. Recursion is handled by the
    /// fixpoint's polarity, not by a special case.
    #[test]
    fn a_reference_cycle_settles_at_the_meet() {
        let mut graph = SymbolGraph::new();
        let a = callable_term(&mut graph, "crate::a");
        let b = callable_term(&mut graph, "crate::b");
        graph.record_references(&a, [b.clone()]).expect("declared");
        graph.record_references(&b, [a.clone()]).expect("declared");
        let closure = graph.capability_closure();
        assert_eq!(closure.effective(&a), EffectiveCapability::Determined(Capability::Call));
        assert_eq!(closure.effective(&b), EffectiveCapability::Determined(Capability::Call));

        // Now poison the cycle from outside: both members must fall.
        let secret = term(&mut graph, "crate::secret");
        graph.record_references(&secret, []).expect("declared");
        graph.record_references(&b, [a.clone(), secret]).expect("declared");
        let closure = graph.capability_closure();
        assert!(closure.is_proof_only(&b), "the poisoned member falls");
        assert!(closure.is_proof_only(&a), "and drags the cycle with it");
    }

    /// Phase 2 may not invent references for a symbol phase 1 never saw — the
    /// same rule `record_status` already enforces, so the two phases cannot
    /// disagree about which symbols exist.
    #[test]
    fn references_cannot_be_recorded_for_an_undeclared_symbol() {
        let mut graph = SymbolGraph::new();
        let ghost = SymbolId::new(rust_path("crate::ghost"), Namespace::Value);
        let err = graph.record_references(&ghost, []).expect_err("undeclared");
        assert_eq!(err.id, ghost);
    }

    /// The closure never *raises* a capability: whatever a producer records, a
    /// symbol's effective capability is bounded by its declared one.
    #[test]
    fn the_closure_only_ever_lowers() {
        let mut graph = SymbolGraph::new();
        let proof_only = term(&mut graph, "crate::p");
        let callable = callable_term(&mut graph, "crate::c");
        graph.record_references(&proof_only, [callable.clone()]).expect("declared");
        graph.record_references(&callable, []).expect("declared");
        let closure = graph.capability_closure();
        assert!(
            closure.is_proof_only(&proof_only),
            "referencing a CALL symbol cannot promote a PROOF-only declaration"
        );
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
            .with_total_carrier(uint64_witness());
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
        for carrier in [UnwitnessedCarrier::None, UnwitnessedCarrier::Declared] {
            let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean)
                .with_status(certified_status())
                .with_carrier(carrier);
            assert!(header.carrier_witness().is_none(), "an unwitnessed carrier has no witness");
            let err = header.grant_call().expect_err("a declared carrier grants nothing");
            assert!(matches!(err, CapabilityRefused::NoTotalCarrier { .. }));
            let rendered = err.to_string();
            assert!(rendered.contains("wrong binary"), "{rendered}");
            assert!(rendered.contains("options:"), "{rendered}");
        }
        assert_eq!(CarrierEvidence::default(), CarrierEvidence::None);
        assert_eq!(UnwitnessedCarrier::default(), UnwitnessedCarrier::None);
    }

    /// **I4's seam control.** `CarrierEvidence::Total` is not assignable: it is
    /// minted only by `with_total_carrier`, which requires a `CarrierWitness`,
    /// which is only ever the `Ok` of `RepresentationObligation::discharge`.
    ///
    /// The compile-time half of this claim is that `with_carrier` cannot even
    /// be *called* with `Total` — its parameter type has no such variant — so
    /// it is checked by the type system on every build rather than here.
    #[test]
    fn total_is_reachable_only_through_a_discharged_obligation() {
        // The `Nat -> u64` obligation, stated HONESTLY, cannot discharge — at
        // any width. This is the miscompile, refused at its source.
        for width in [8_u32, 16, 32, 64] {
            let err = RepresentationObligation::new(
                "Nat",
                format!("u{width}"),
                CarrierExtent::Unbounded,
                CarrierExtent::Bits(width),
                OperationAgreement::ExactOnEveryOperation,
            )
            .discharge()
            .expect_err("an unbounded Clean type has no fixed-width carrier");
            assert!(matches!(err, ObligationNotDischarged::NoFixedExtent { .. }));
            let text = err.to_string();
            assert!(text.contains("Nat"), "{text}");
            assert!(text.contains("options:"), "v7/D3: {text}");
        }

        // A width disagreement is refused in BOTH directions: narrowing
        // truncates, widening changes the wrap modulus.
        for (clean_bits, rust_bits) in [(64_u32, 32_u32), (8, 64)] {
            let err = RepresentationObligation::new(
                format!("UInt{clean_bits}"),
                format!("u{rust_bits}"),
                CarrierExtent::Bits(clean_bits),
                CarrierExtent::Bits(rust_bits),
                OperationAgreement::ExactOnEveryOperation,
            )
            .discharge()
            .expect_err("an inexact width is not a faithful carrier");
            assert!(matches!(err, ObligationNotDischarged::ExtentMismatch { .. }));
        }

        // Equal cardinality is NOT faithfulness: the operations must agree too.
        let err = RepresentationObligation::new(
            "UInt64",
            "u64",
            CarrierExtent::Bits(64),
            CarrierExtent::Bits(64),
            OperationAgreement::Unestablished,
        )
        .discharge()
        .expect_err("unestablished operations discharge nothing");
        assert!(matches!(err, ObligationNotDischarged::OperationsUnestablished { .. }));

        // A `Prop` is observed, never produced.
        assert!(matches!(
            RepresentationObligation::new(
                "Prop",
                "bool",
                CarrierExtent::NotAValue,
                CarrierExtent::Bits(1),
                OperationAgreement::ExactOnEveryOperation,
            )
            .discharge(),
            Err(ObligationNotDischarged::NoFixedExtent { .. })
        ));

        // A target-dependent width is bounded but not KNOWN, which is not the
        // same fact and does not discharge either.
        assert!(matches!(
            RepresentationObligation::new(
                "USize",
                "usize",
                CarrierExtent::TargetDependent,
                CarrierExtent::Bits(64),
                OperationAgreement::ExactOnEveryOperation,
            )
            .discharge(),
            Err(ObligationNotDischarged::NoFixedExtent { .. })
        ));

        // I6 — the trusted-runtime lane, positive: the ONE pinned pairing, at
        // the ONE agreement kind its extents require, discharges.
        let bignum_witness = RepresentationObligation::new(
            "Nat",
            "trust_bignum::Nat",
            CarrierExtent::Unbounded,
            CarrierExtent::Unbounded,
            OperationAgreement::TrustedRuntimeAgreement,
        )
        .discharge()
        .expect("the pinned Nat/trust_bignum::Nat pairing discharges");
        assert_eq!(bignum_witness.width(), CarrierWidth::UnboundedExact);
        assert!(
            bignum_witness.to_string().contains("trusted runtime"),
            "the witness must SAY it rests on a trusted runtime: {bignum_witness}"
        );

        // I6 negative 1: an unbounded pairing claiming the fixed-width
        // agreement kind states a modulus fact that has no modulus.
        let err = RepresentationObligation::new(
            "Nat",
            "trust_bignum::Nat",
            CarrierExtent::Unbounded,
            CarrierExtent::Unbounded,
            OperationAgreement::ExactOnEveryOperation,
        )
        .discharge()
        .expect_err("an unbounded pairing cannot state a wrap-modulus agreement");
        assert!(matches!(err, ObligationNotDischarged::WrongAgreementKind { .. }), "{err:?}");
        assert!(err.to_string().contains("options:"), "v7/D3: {err}");

        // I6 negative 2: a fixed-width pairing claiming the trusted runtime —
        // a checkable fact must be checked, never trusted.
        let err = RepresentationObligation::new(
            "UInt64",
            "u64",
            CarrierExtent::Bits(64),
            CarrierExtent::Bits(64),
            OperationAgreement::TrustedRuntimeAgreement,
        )
        .discharge()
        .expect_err("a fixed-width pairing may not substitute trust for the width check");
        assert!(matches!(err, ObligationNotDischarged::WrongAgreementKind { .. }), "{err:?}");

        // I6 negative 3 — THE PAIRING PIN. `Int` honestly reports Unbounded,
        // exactly like `Nat`, and the constructor is public: without the pin
        // this would witness, and ℤ is not carried by a ℕ runtime.
        let err = RepresentationObligation::new(
            "Int",
            "trust_bignum::Nat",
            CarrierExtent::Unbounded,
            CarrierExtent::Unbounded,
            OperationAgreement::TrustedRuntimeAgreement,
        )
        .discharge()
        .expect_err("a pairing no shipped runtime carries must be unconstructible");
        assert!(matches!(err, ObligationNotDischarged::UntrustedRuntimePairing { .. }), "{err:?}");
        let text = err.to_string();
        assert!(text.contains("Int"), "{text}");
        assert!(text.contains("options:"), "v7/D3: {text}");

        // I6 negative 4: the same pin, from the carrier side — an impersonator
        // runtime under a different path is not the pinned pairing.
        assert!(matches!(
            RepresentationObligation::new(
                "Nat",
                "evil::Nat",
                CarrierExtent::Unbounded,
                CarrierExtent::Unbounded,
                OperationAgreement::TrustedRuntimeAgreement,
            )
            .discharge(),
            Err(ObligationNotDischarged::UntrustedRuntimePairing { .. })
        ));

        // The positive: the witness records WHAT justified the capability.
        let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean)
            .with_status(certified_status())
            .with_total_carrier(uint64_witness());
        assert_eq!(header.carrier(), CarrierEvidence::Total);
        let witness = header.carrier_witness().expect("Total carries its witness");
        assert_eq!(witness.clean_type(), "UInt64");
        assert_eq!(witness.rust_carrier(), "u64");
        assert_eq!(witness.width(), CarrierWidth::Bits(64));

        // Recording an unwitnessed carrier over it drops BOTH, so the pair can
        // never disagree.
        let downgraded = header.with_carrier(UnwitnessedCarrier::Declared);
        assert_eq!(downgraded.carrier(), CarrierEvidence::Declared);
        assert!(downgraded.carrier_witness().is_none());
        assert!(matches!(downgraded.grant_call(), Err(CapabilityRefused::NoTotalCarrier { .. })));
    }

    /// The positive control, so the four refusals above are not just "grant_call
    /// always errors". BOTH conditions together grant CALL — and neither is
    /// constructible from anywhere in this tree at I1.
    #[test]
    fn call_is_granted_only_when_both_conditions_hold() {
        let header = SymbolHeader::new(rust_path("crate::m::f"), Sort::Term, Producer::Clean)
            .with_status(certified_status())
            .with_total_carrier(uint64_witness())
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
        graph.declare(SymbolHeader::new(clean_path.clone(), Sort::Prop, Producer::Clean)).unwrap();
        graph.declare(SymbolHeader::new(debt_path.clone(), Sort::Prop, Producer::Clean)).unwrap();

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
