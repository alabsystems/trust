// trust-types/formula/vc: Verification condition and related types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::Formula;
use super::contracts::ContractMetadata;
use super::vc_kind::VcKind;
use crate::Symbol;
use crate::model::SourceSpan;

/// A verification condition — the thing we send to solvers.
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VcKind, Formula, Sort, SourceSpan, Symbol};
///
/// // Division-by-zero check: denominator != 0
/// let denom = Formula::Var("d".into(), Sort::Int);
/// let vc = VerificationCondition {
///     kind: VcKind::DivisionByZero,
///     function: Symbol::intern("my_crate::div"),
///     location: SourceSpan::default(),
///     formula: Formula::Eq(Box::new(denom), Box::new(Formula::Int(0))),
///     contract_metadata: None,
///     obligation: None,
/// };
///
/// assert_eq!(vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
/// assert!(!vc.has_contracts());
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationCondition {
    pub kind: VcKind,
    // Interned function name — reduces heap allocations for repeated
    // function names across verification conditions.
    pub function: Symbol,
    pub location: SourceSpan,
    /// The formula to check. Convention: we assert this formula and check SAT.
    /// If UNSAT, the property holds (no violation exists).
    /// If SAT, the model is a counterexample.
    pub formula: Formula,
    // Trust: Contract metadata for deductive verification routing.
    #[serde(default)]
    pub contract_metadata: Option<ContractMetadata>,
    /// Trust: authenticated-obligation record (the emitter's own account of WHICH
    /// sub-formula of `formula` is the obligation, plus the wrappers it applied and,
    /// where the kind implies them, the subject/width). This is a CLAIM checked by
    /// recomputation at consumption (reconstruct-and-equate against `formula`, and
    /// MIR cross-check for subject/width) — NEVER trusted. `#[serde(default)]` keeps
    /// every existing fixture dump byte-compatible: they deserialize this as `None`.
    /// Populated today only for the vertical-slice arms (div/rem-by-zero, negation
    /// overflow); every other producer leaves it `None`.
    #[serde(default)]
    pub obligation: Option<ObligationRecord>,
}

impl VerificationCondition {
    /// Why the Clean kernel may not mint proof authority for this VC, if it may not.
    ///
    /// First the kind gate (`VcKind::kind_authority_refusal`: a kind whose violation
    /// formula is not a statement about the program); then, for a kind whose formula
    /// must be SITUATED, a structural check of its obligation record. Every walk is
    /// iterative and bounded, because consumers run this on deserialized VCs before any
    /// depth gate.
    ///
    /// `VcKind::TypeInvariant` is admitted by kind since TINV step 7.7, so for a TINV row
    /// this is exactly [`Self::type_invariant_situatedness_refusal`] (TINV-9(j)).
    ///
    /// TINV step 10.1 (TINV-23): a VC that carries a type-invariant ASSUMPTION TAG
    /// ([`TINV_ASSUME_TAG_PREFIX`]) anywhere, or whose tag scan exceeds
    /// [`TINV_TAG_SCAN_MAX_NODES`], is refused, whatever its kind. A tagged row rests on
    /// a TINV certificate's whole-crate induction, which no kernel re-check of the row
    /// covers, so it may be at most `Trusted` (composed), never `Certified`. There is no
    /// kernel entry that accepts a tagged VC.
    ///
    /// A bare Boolean assertion violation has no hypotheses relating its free name
    /// to program execution. In particular, the whole-function `panic_reachable`
    /// placeholder cannot borrow a native CHC verdict as a CIC hypothesis. A checked
    /// body/violation relation must first replace the placeholder; an obligation
    /// record merely repeating it supplies no such relation. This refusal depends
    /// on the typed formula, never a function, variable or assertion display name.
    #[must_use]
    pub fn kernel_authority_refusal(&self) -> Option<&'static str> {
        if let Some(why) = self.kind.kind_authority_refusal() {
            return Some(why);
        }
        match self.type_invariant_tags() {
            TinvTagScan::None => {}
            TinvTagScan::Tags(_) => {
                return Some(
                    "the VC assumes a type invariant (it carries a `$tinv_assume_` tag): a \
                     TINV-premised row is never kernel authority (TINV-23)",
                );
            }
            TinvTagScan::Unbounded => {
                return Some(
                    "the VC is too large to scan for type-invariant assumption tags (TINV-23)",
                );
            }
        }
        if matches!(self.kind, VcKind::TypeInvariant { .. }) {
            return self.type_invariant_situatedness_refusal();
        }
        if matches!(self.kind, VcKind::Assertion { .. })
            && matches!(self.formula, Formula::Var(_, crate::Sort::Bool))
        {
            return Some(
                "a bare Boolean assertion violation has no checked body/violation relation: \
                 its free variable is satisfiable, so native success cannot supply a CIC refutation",
            );
        }
        None
    }

    /// TINV (design §P4, TINV-8, TINV-9(j)): the structural shape a type-invariant row must have
    /// before the kernel may certify it.
    ///
    /// * it carries an obligation record, and the record REPLAYS to the formula;
    /// * the record body is `Not(core)` or `And([h.., Not(core)])`, the negated core last;
    /// * there is at least one hypothesis (in the body, a `ConjoinFactsLast` fact, or a
    ///   path guard), and every free name of the core occurs in one;
    /// * an EDGE PART (TINV-9(a), `edge: Some(p)`) carries its edge guard as the FIRST body
    ///   conjunct, always (`true` for an unguarded edge), so its body is
    ///   `And([guard, h.., Not(core)])`. The guard is a routing condition, not a binding of
    ///   program state: it is SKIPPED here, never counted as binding a core name, so a part
    ///   whose core names only the edge guard binds is refused. An edge part whose body has
    ///   no guard slot is refused. The record replay is unaffected (the guard is an
    ///   ordinary body conjunct).
    ///
    /// LIMITS. This is a regression guard against record-less, bare and forged rows
    /// only. It proves nothing about whether the hypotheses are true program facts or
    /// satisfiable; the producer and Houdini's vacuity filter are the real guards.
    #[must_use]
    pub fn type_invariant_situatedness_refusal(&self) -> Option<&'static str> {
        const NOT_SITUATED: &str = "a type-invariant row is not situated: its core names \
                                    program state no hypothesis binds";
        let Some(record) = &self.obligation else {
            return Some("a type-invariant row carries no obligation record to replay");
        };
        if record.reconstruct().as_ref() != Some(&self.formula) {
            return Some("a type-invariant row's obligation record does not replay to its formula");
        }
        let (body_hyps, core): (&[Formula], &Formula) = match &record.body {
            Formula::Not(core) => (&[], core),
            Formula::And(parts) => match parts.split_last() {
                Some((Formula::Not(core), hyps)) => (hyps, core),
                _ => {
                    return Some(
                        "a type-invariant row's body is not a negated core conjoined last",
                    );
                }
            },
            _ => return Some("a type-invariant row's body is not a negated core conjoined last"),
        };
        // TINV-9(a): an edge part's first body conjunct is its edge guard, which binds
        // nothing.
        let body_hyps = match &self.kind {
            VcKind::TypeInvariant { edge: Some(_), .. } => match body_hyps.split_first() {
                Some((_guard, rest)) => rest,
                None => return Some("a type-invariant edge part carries no edge-guard conjunct"),
            },
            _ => body_hyps,
        };
        let mut hyps: Vec<&Formula> = body_hyps.iter().collect();
        for wrapper in &record.wrappers {
            match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => hyps.extend(facts),
                ObligationWrapper::PathGuardOr { paths } => {
                    for path in paths {
                        if let PathGuardTerm::Guarded { guards } = path {
                            hyps.extend(guards);
                        }
                    }
                }
            }
        }
        if hyps.is_empty() {
            return Some(NOT_SITUATED);
        }
        let mut budget = RECORD_MAX_FORMULA_NODES;
        let Some(core_names) = bounded_var_names([core], &mut budget) else {
            return Some("a type-invariant row is too large to check");
        };
        let Some(hyp_names) = bounded_var_names(hyps, &mut budget) else {
            return Some("a type-invariant row is too large to check");
        };
        if core_names.is_empty() || !core_names.is_subset(&hyp_names) {
            return Some(NOT_SITUATED);
        }
        None
    }

    /// TINV step 10.1: the type-invariant assumption tags this VC carries.
    ///
    /// Every formula the VC holds is scanned: the violation formula and, when present,
    /// the obligation record's body, subject and every wrapper fact and guard (the
    /// record is a claim that a consumer replays, so a tag hidden in it counts too). A
    /// name counts as a tag when it starts with [`TINV_ASSUME_TAG_PREFIX`], wherever it
    /// occurs: a `Var` or `SymVar`, a quantifier binder, or a `Pred` symbol. The prefix
    /// alone decides, so a malformed or forged tag spelling is still a tag.
    ///
    /// The walk is iterative and bounded by [`TINV_TAG_SCAN_MAX_NODES`] over all the
    /// formulas together; past it the answer is [`TinvTagScan::Unbounded`], which every
    /// consumer must treat as tagged.
    #[must_use]
    pub fn type_invariant_tags(&self) -> TinvTagScan {
        let mut pending: Vec<&Formula> = Vec::with_capacity(16);
        pending.push(&self.formula);
        if let Some(record) = &self.obligation {
            pending.push(&record.body);
            pending.extend(record.subject.as_ref());
            for wrapper in &record.wrappers {
                match wrapper {
                    ObligationWrapper::ConjoinFactsLast { facts } => pending.extend(facts),
                    ObligationWrapper::PathGuardOr { paths } => {
                        for path in paths {
                            match path {
                                PathGuardTerm::Raw | PathGuardTerm::Collapsed => {}
                                PathGuardTerm::Guarded { guards } => pending.extend(guards),
                            }
                        }
                    }
                }
            }
        }
        let mut tags: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut budget = TINV_TAG_SCAN_MAX_NODES;
        let mut note = |name: &str| {
            if is_type_invariant_assume_tag(name) {
                tags.insert(name.to_owned());
            }
        };
        while let Some(f) = pending.pop() {
            let Some(rest) = budget.checked_sub(1) else { return TinvTagScan::Unbounded };
            budget = rest;
            match f {
                Formula::Var(name, _) => note(name),
                Formula::SymVar(sym, _) | Formula::Pred(sym, _) => note(sym.as_str()),
                Formula::Forall(binders, _) | Formula::Exists(binders, _) => {
                    for (sym, _) in binders {
                        note(sym.as_str());
                    }
                }
                _ => {}
            }
            super::for_each_formula_child(f, |child| pending.push(child));
        }
        if tags.is_empty() { TinvTagScan::None } else { TinvTagScan::Tags(tags) }
    }

    /// Returns true if this VC has any contract annotations.
    #[must_use]
    pub fn has_contracts(&self) -> bool {
        self.contract_metadata.as_ref().is_some_and(|m| m.has_any())
    }
}

/// TINV step 10.1: the prefix of every type-invariant ASSUMPTION TAG.
///
/// A use-site fact `I_k(σ)` of a certified type invariant is conjoined as
/// `And([Var(tag, Bool), I_k(σ)])`, where `tag` = [`type_invariant_assume_tag`]. Every
/// model sets the tag `true`, so it never changes validity; it is a disclosure channel,
/// and [`VerificationCondition::kernel_authority_refusal`] refuses any VC that carries
/// one. The `$` cannot begin a name the generator mints for a MIR place.
pub const TINV_ASSUME_TAG_PREFIX: &str = "$tinv_assume_";

/// The hex digits of the digest in a [`type_invariant_assume_tag`] (64 bits).
pub const TINV_ASSUME_TAG_HEX_DIGITS: usize = 16;

/// The node bound of [`VerificationCondition::type_invariant_tags`], over every formula
/// of one VC together. Deliberately far above the record replay bound (16 384): the scan
/// is linear and allocation-free per node, and every VC past it is refused kernel
/// authority, so a lower bound would cost certificates of large untagged VCs for no
/// soundness gain.
pub const TINV_TAG_SCAN_MAX_NODES: usize = 1 << 20;

/// The assumption tag naming conjunct `conjunct` of the type invariant of `def_path`:
/// `$tinv_assume_` followed by the first [`TINV_ASSUME_TAG_HEX_DIGITS`] lowercase hex
/// digits of `sha256(def_path ‖ 0x00 ‖ conjunct as 4 big-endian bytes)`.
///
/// The spelling is the prefix's ASCII letters, `$` and `_`, then `[0-9a-f]`: never a
/// `#` (the vcgen version-token separator, split at dozens of sites), `:`, `.` or `*`
/// (the place-path separators), so no version renamer, seal or place parser can read a
/// tag as a versioned or projected place. A def path cannot be read back from a tag;
/// the use set keeps the map (`trust_vcgen::type_invariant::TinvUseSet`) and refuses a
/// collision.
#[must_use]
pub fn type_invariant_assume_tag(def_path: &str, conjunct: u32) -> String {
    use std::fmt::Write as _;

    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(def_path.as_bytes());
    hasher.update([0u8]);
    hasher.update(conjunct.to_be_bytes());
    let digest = hasher.finalize();
    let mut tag = String::with_capacity(TINV_ASSUME_TAG_PREFIX.len() + TINV_ASSUME_TAG_HEX_DIGITS);
    tag.push_str(TINV_ASSUME_TAG_PREFIX);
    for byte in &digest[..TINV_ASSUME_TAG_HEX_DIGITS / 2] {
        let _ = write!(tag, "{byte:02x}");
    }
    tag
}

/// TINV step 10.7: the prefix of every type-invariant premise DISCLOSURE, the one spelling
/// every output surface (proof results, telemetry, transport, the JSON proof report and
/// its renderings, the terminal note) uses for a row whose verdict rests on conjunct `k`
/// of the certified type invariant of `S`: `assumes type_invariant(S)#k`.
pub const TINV_ASSUMES_PREFIX: &str = "assumes type_invariant(";

/// The disclosure label of conjunct `conjunct` of the type invariant of `def_path`:
/// `assumes type_invariant(<def_path>)#<conjunct>`. A surface may append provenance after
/// it (the conjunct's text and the certificate it comes from), never anything before it.
#[must_use]
pub fn type_invariant_assumes_label(def_path: &str, conjunct: u32) -> String {
    format!("{TINV_ASSUMES_PREFIX}{def_path})#{conjunct}")
}

/// Whether `name` is a type-invariant assumption tag: it starts with
/// [`TINV_ASSUME_TAG_PREFIX`]. The prefix alone decides (fail closed): a forged or
/// malformed spelling under the prefix is a tag too.
#[must_use]
pub fn is_type_invariant_assume_tag(name: &str) -> bool {
    name.starts_with(TINV_ASSUME_TAG_PREFIX)
}

/// The result of [`VerificationCondition::type_invariant_tags`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TinvTagScan {
    /// The whole VC was scanned and carries no tag.
    None,
    /// The tags found, by name.
    Tags(std::collections::BTreeSet<String>),
    /// The scan passed [`TINV_TAG_SCAN_MAX_NODES`]: treat as tagged.
    Unbounded,
}

// Serializable VC for serde boundaries (JSON proof certificates, caches).
//
// `SerializableVc` holds an owned `Formula` and implements Serialize/Deserialize,
// used at persistence boundaries (proof certificates, JSON output).

/// A serializable verification condition — always holds an owned `Formula`.
///
/// Use this at persistence boundaries (proof certificates, JSON caches). Convert
/// using `from_vc()` / `into_vc()`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableVc {
    pub kind: VcKind,
    // Interned function name for consistency with VerificationCondition.
    pub function: Symbol,
    pub location: SourceSpan,
    /// The formula to check (always an owned `Formula` for serialization).
    pub formula: Formula,
    #[serde(default)]
    pub contract_metadata: Option<ContractMetadata>,
    /// Trust: mirror of [`VerificationCondition::obligation`] across the serde
    /// boundary. Threaded explicitly through `from_vc`/`into_vc` (both enumerate
    /// every field) so the authenticated-obligation record survives a
    /// certificate/cache round-trip instead of being silently dropped.
    #[serde(default)]
    pub obligation: Option<ObligationRecord>,
}

impl SerializableVc {
    /// Create from a `VerificationCondition`.
    #[must_use]
    pub fn from_vc(vc: &VerificationCondition) -> Self {
        Self {
            kind: vc.kind.clone(),
            function: vc.function,
            location: vc.location.clone(),
            formula: vc.formula.clone(),
            contract_metadata: vc.contract_metadata,
            obligation: vc.obligation.clone(),
        }
    }

    /// Convert back to a `VerificationCondition`.
    #[must_use]
    pub fn into_vc(self) -> VerificationCondition {
        VerificationCondition {
            kind: self.kind,
            function: self.function,
            location: self.location,
            formula: self.formula,
            contract_metadata: self.contract_metadata,
            obligation: self.obligation,
        }
    }
}

/// Trust: the emitter's authenticated account of the obligation carried by a
/// [`VerificationCondition`]. This is a **claim**, checked by recomputation at
/// consumption — it is never a grant. The soundness of the mechanism rests on
/// the consumer authenticating it, not on this data being trusted:
///
/// * `body` + `wrappers` are authenticated by pure **reconstruct-and-equate**:
///   replaying every wrapper (innermost-first) onto `body` must reproduce
///   `vc.formula` *structurally, bit-for-bit* (including `#token` version stamps).
///   Any wrapper spelling outside the closed vocabulary, or any rename mismatch,
///   makes reconstruction diverge from `formula` and the consumer DECLINES —
///   fail-closed, costing certificates but never soundness.
/// * `subject` / `width`, where the kind implies them, are authenticated against
///   the function's MIR (the type that DEFINES the width), not against a literal
///   inside `body` — the [10]-class width-forgery guard.
///
/// The emitter records these from what it is already building at the point it
/// KNOWS them (the raw violation, the negated operand, `ty.int_width()`), never by
/// re-parsing the finished formula.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationRecord {
    /// The raw violation predicate — the SAME versioning that appears inside
    /// `formula`. Replaying `wrappers` onto this must reproduce `formula`.
    pub body: Formula,
    /// The wrappers the emitter applied to `body`, innermost-first. Replaying them
    /// in order onto `body` reconstructs `formula`.
    pub wrappers: Vec<ObligationWrapper>,
    /// The negated/shifted operand, where the kind implies one (negation, shift);
    /// cross-checked against MIR at consumption. `None` for div/rem (payload-free).
    #[serde(default)]
    pub subject: Option<Formula>,
    /// The TRUE UB width the certificate is about, where the kind implies one;
    /// cross-checked against the MIR type width at consumption, NOT against `body`.
    /// `None` for div/rem (payload-free).
    #[serde(default)]
    pub width: Option<u32>,
}

/// The variable names in `formulas`, walked iteratively; `None` once `budget` nodes
/// have been visited.
fn bounded_var_names<'a>(
    formulas: impl IntoIterator<Item = &'a Formula>,
    budget: &mut usize,
) -> Option<std::collections::BTreeSet<&'a str>> {
    let mut names = std::collections::BTreeSet::new();
    let mut pending: Vec<&Formula> = formulas.into_iter().collect();
    while let Some(f) = pending.pop() {
        *budget = budget.checked_sub(1)?;
        if let Formula::Var(name, _) = f {
            names.insert(name.as_str());
        }
        super::for_each_formula_child(f, |child| pending.push(child));
    }
    Some(names)
}

/// Bound on the formula nodes a record replay may read or build (TINV step 7.1; moved
/// from `trust_vcgen::refutation_scope`).
const RECORD_MAX_FORMULA_NODES: usize = 16_384;

impl ObligationRecord {
    /// Replay this record's wrappers onto its body ([`Self::reconstruct_parts`]).
    #[must_use]
    pub fn reconstruct(&self) -> Option<Formula> {
        Self::reconstruct_parts(&self.body, &self.wrappers)
    }

    /// Replay `wrappers` onto `body`, bounded BEFORE any cloning: at most 128
    /// wrappers and 128 paths per wrapper, 16 384 formula nodes and depth 128 for the
    /// inputs and for every intermediate result. `None` past any bound. Every walk is
    /// iterative, so a deserialized record cannot overflow the stack here.
    #[must_use]
    pub fn reconstruct_parts(body: &Formula, wrappers: &[ObligationWrapper]) -> Option<Formula> {
        // Bound TOTAL borrowed input and prospective wrapper fanout BEFORE any
        // cloning. Individually small facts/paths can otherwise multiply a body
        // into an enormous allocation before a post-construction check runs.
        let mut cost = formula_cost(body)?;
        let mut input_nodes = cost.0;
        if wrappers.len() > 128 {
            return None;
        }
        for wrapper in wrappers {
            cost = match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => {
                    let facts = borrowed_cost(facts, &mut input_nodes)?;
                    combined_cost(facts.0.checked_add(cost.0)?, facts.1.max(cost.1))?
                }
                ObligationWrapper::PathGuardOr { paths } => {
                    if paths.len() > 128 {
                        return None;
                    }
                    let mut nodes = 0usize;
                    let mut depth = 0usize;
                    for path in paths {
                        let next = match path {
                            PathGuardTerm::Raw | PathGuardTerm::Collapsed => cost,
                            PathGuardTerm::Guarded { guards } => {
                                let guards = borrowed_cost(guards, &mut input_nodes)?;
                                // Count an unflattened body: a conservative upper
                                // bound on the guarded And-splice, never too small.
                                combined_cost(guards.0.checked_add(cost.0)?, guards.1.max(cost.1))?
                            }
                        };
                        nodes = nodes.checked_add(next.0)?;
                        depth = depth.max(next.1);
                        if nodes > RECORD_MAX_FORMULA_NODES {
                            return None;
                        }
                    }
                    match paths.len() {
                        0 => cost,
                        1 => (nodes, depth),
                        _ => combined_cost(nodes, depth)?,
                    }
                }
            };
        }
        let mut current = body.clone();
        for wrapper in wrappers {
            current = match wrapper {
                ObligationWrapper::ConjoinFactsLast { facts } => {
                    let mut parts = Vec::with_capacity(facts.len() + 1);
                    parts.extend_from_slice(facts);
                    parts.push(current);
                    Formula::And(parts)
                }
                ObligationWrapper::PathGuardOr { paths } => {
                    let mut terms = Vec::with_capacity(paths.len());
                    for path in paths {
                        terms.push(match path {
                            PathGuardTerm::Raw | PathGuardTerm::Collapsed => current.clone(),
                            PathGuardTerm::Guarded { guards } => {
                                let extra = match &current {
                                    Formula::And(inner) => inner.len(),
                                    _ => 1,
                                };
                                let mut parts = Vec::with_capacity(guards.len() + extra);
                                parts.extend_from_slice(guards);
                                match &current {
                                    Formula::And(inner) => parts.extend_from_slice(inner),
                                    _ => parts.push(current.clone()),
                                }
                                Formula::And(parts)
                            }
                        });
                    }
                    match terms.len() {
                        0 => current,
                        1 => terms.pop()?,
                        _ => Formula::Or(terms),
                    }
                }
            };
            formula_cost(&current)?;
        }
        Some(current)
    }
}

fn combined_cost(children: usize, child_depth: usize) -> Option<(usize, usize)> {
    let nodes = children.checked_add(1)?;
    let depth = child_depth.checked_add(1)?;
    (nodes <= RECORD_MAX_FORMULA_NODES && depth <= 128).then_some((nodes, depth))
}

fn borrowed_cost(formulas: &[Formula], input_nodes: &mut usize) -> Option<(usize, usize)> {
    if formulas.len() > RECORD_MAX_FORMULA_NODES {
        return None;
    }
    let mut nodes = 0usize;
    let mut depth = 0usize;
    for formula in formulas {
        let cost = formula_cost(formula)?;
        nodes = nodes.checked_add(cost.0)?;
        *input_nodes = input_nodes.checked_add(cost.0)?;
        if *input_nodes > RECORD_MAX_FORMULA_NODES {
            return None;
        }
        depth = depth.max(cost.1);
    }
    Some((nodes, depth))
}

fn formula_cost(formula: &Formula) -> Option<(usize, usize)> {
    let mut pending = Vec::with_capacity(16);
    pending.push((formula, 0usize));
    let mut count = 0;
    let mut max_depth = 0;
    while let Some((formula, depth)) = pending.pop() {
        count += 1;
        if count > RECORD_MAX_FORMULA_NODES || depth > 128 {
            return None;
        }
        max_depth = max_depth.max(depth);
        super::for_each_formula_child(formula, |child| pending.push((child, depth + 1)));
    }
    Some((count, max_depth))
}

/// Trust: the CLOSED vocabulary of wrappers a safety emitter applies to a raw
/// violation body. There are exactly two shapes, and that is the point: every
/// conjoining site pushes the body LAST (one shape), and the sole non-conjoining
/// wrapper is the dominating path-guard map (the other shape). There is deliberately
/// **no** `Implies`, **no** `Not`, and **no** free-disjunct variant — that omission
/// is what structurally closes the `Implies(Not(decoy), core)` twin and the mixed
/// `Or([core, decoy])` decoy: no sequence of these wrappers can reconstruct such a
/// spelling, so reconstruct-and-equate DECLINES it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObligationWrapper {
    /// `inner ↦ And([facts.., inner])` — the body is conjoined LAST. Reproduces
    /// every block-def / guard-fact / precondition / semantic-guard conjoin site.
    ConjoinFactsLast { facts: Vec<Formula> },
    /// `inner ↦ Or([per-path term..])` — the dominating path-guard map. Each term is
    /// `Raw` (`inner` whole) or `Guarded { guards }` (`And([guards.., <inner spliced
    /// flat>])`). Collapses to the single term when there is one path, and to `inner`
    /// when there are none — mirroring `v2_formula_with_path_guards`.
    PathGuardOr { paths: Vec<PathGuardTerm> },
}

/// Trust: one path term of a [`ObligationWrapper::PathGuardOr`]. `Raw` carries the
/// body whole (an unguarded path); `Guarded` conjoins the (already version-renamed)
/// path guards and splices the body flat (mirroring the `And`-flatten in
/// `v2_formula_with_path_guards`).
///
/// `Serialize` is written by hand so that [`Self::Collapsed`] SERIALIZES EXACTLY AS
/// [`Self::Raw`] (variant 0, `"Raw"`): every byte-level identity of a VC —
/// `trust-certify`'s `ObligationIdentity::from_vc` and
/// `functional_vc_lineage_digest`, both `bincode::serialize(vc)` — is unchanged by
/// the marker. The other two variants serialize as the derive would.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub enum PathGuardTerm {
    Raw,
    Guarded {
        guards: Vec<Formula>,
    },
    /// Trust (2026-10-16, S1): renders exactly as [`Self::Raw`] — the body whole, no
    /// guard — so the formula and its reconstruction are unchanged, and it
    /// serializes as `Raw` (see the type's doc), so no serialized identity or
    /// digest moves. It records WHY the path is unguarded: the block's path list
    /// COLLAPSED (the path-guard walk's global step budget tripped, or the block's
    /// path count saturated) and the walk left the single empty path in place of the
    /// guards that really dominate the block. A `Raw` term is a genuinely
    /// unconditional path; a `Collapsed` one is an over-approximation whose SAT
    /// models need not reach the block. Negative-only: the generic refutation scope
    /// withholds a counterexample over a `Collapsed` term, and no proof-direction
    /// consumer distinguishes the two.
    ///
    /// IN-PROCESS ONLY: a serialized record reads back as `Raw`, which is the
    /// pre-marker behaviour (the refutation is not held), never a proof.
    Collapsed,
}

impl Serialize for PathGuardTerm {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStructVariant;
        match self {
            PathGuardTerm::Raw | PathGuardTerm::Collapsed => {
                serializer.serialize_unit_variant("PathGuardTerm", 0, "Raw")
            }
            PathGuardTerm::Guarded { guards } => {
                let mut variant =
                    serializer.serialize_struct_variant("PathGuardTerm", 1, "Guarded", 1)?;
                variant.serialize_field("guards", guards)?;
                variant.end()
            }
        }
    }
}

/// Trust: #178 Ownership metadata extracted from VCs for trust-vc-enriched encoding.
///
/// Carries region identifiers, borrow relationships, lifetime outlives relations,
/// and provenance tracking flags. Used by the trust_vc backend to generate
/// ownership axioms (region non-aliasing, Stacked Borrows permissions, borrow
/// validity constraints) instead of plain SMT-LIB2.
///
/// Not stored on VerificationCondition directly (that would break 477+ existing
/// construction sites). Instead, trust_vc extracts this from VcKind::Assertion
/// messages tagged with the `[memory:region]` prefix by region_encoding.rs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OwnershipMetadata {
    /// Region identifiers involved in this VC (e.g., "region_0", "region_1").
    pub regions: Vec<String>,
    /// Active borrow relationships (e.g., "region_1 borrows region_0").
    pub borrows: Vec<String>,
    /// Lifetime outlives relations (e.g., "'a: 'b" encoded as "a outlives b").
    #[serde(default)]
    pub lifetime_constraints: Vec<String>,
    /// Whether provenance tracking is needed (raw pointer casts, addr_of).
    #[serde(default)]
    pub has_provenance: bool,
}

impl OwnershipMetadata {
    /// Trust: Returns true if this metadata has any ownership-related content.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.regions.is_empty() && self.borrows.is_empty() && self.lifetime_constraints.is_empty()
    }
}

#[cfg(test)]
mod obligation_field_backward_compat_tests {
    use super::*;
    use crate::Sort;

    // A legacy VC dump minted BEFORE the `obligation` field existed: it carries no
    // `obligation` key. `#[serde(default)]` must deserialize it as `None` — the
    // backward-compat guarantee every one of the committed fixture dumps relies on.
    // Falsified by removing `#[serde(default)]` on the field (deserialization then
    // errors on the missing key).
    #[test]
    fn legacy_vc_json_without_obligation_deserializes_as_none() {
        // A pre-`obligation` dump is EXACTLY a current dump with the `obligation` key
        // removed. Build one that way (so every OTHER field — SourceSpan shape, etc. —
        // is authentic) and prove `#[serde(default)]` fills it as None rather than
        // erroring on the missing key. Falsified by dropping `#[serde(default)]`.
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: crate::Symbol::intern("my_crate::div"),
            location: crate::model::SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("d".into(), crate::Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        let mut value: serde_json::Value = serde_json::to_value(&vc).unwrap();
        assert!(value.as_object_mut().unwrap().remove("obligation").is_some());
        let legacy = serde_json::to_string(&value).unwrap();

        let back: VerificationCondition = serde_json::from_str(&legacy)
            .expect("legacy VC dump (no obligation key) must deserialize");
        assert!(back.obligation.is_none(), "missing obligation must default to None, not error");

        // Same guarantee for the persistence-boundary twin.
        let svc: SerializableVc =
            serde_json::from_str(&legacy).expect("legacy SerializableVc dump must deserialize");
        assert!(svc.obligation.is_none());
    }

    // A populated obligation survives a serialize -> deserialize round-trip, and
    // rides through the `from_vc`/`into_vc` conversion instead of being dropped at
    // the serde boundary. Falsified by omitting `obligation` from either conversion.
    #[test]
    fn populated_obligation_roundtrips_and_threads_through_conversions() {
        let body =
            Formula::Eq(Box::new(Formula::Var("d".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: crate::Symbol::intern("my_crate::div"),
            location: crate::model::SourceSpan::default(),
            formula: body.clone(),
            contract_metadata: None,
            obligation: Some(ObligationRecord {
                body: body.clone(),
                wrappers: vec![ObligationWrapper::ConjoinFactsLast {
                    facts: vec![Formula::Bool(true)],
                }],
                subject: None,
                width: None,
            }),
        };

        // JSON round-trip preserves the record.
        let text = serde_json::to_string(&vc).unwrap();
        let back: VerificationCondition = serde_json::from_str(&text).unwrap();
        assert_eq!(back.obligation, vc.obligation);

        // from_vc / into_vc must carry it, not drop it.
        let svc = SerializableVc::from_vc(&vc);
        assert_eq!(svc.obligation, vc.obligation);
        let vc2 = svc.into_vc();
        assert_eq!(vc2.obligation, vc.obligation);
    }
}

#[cfg(test)]
mod path_guard_term_serialization_tests {
    use super::*;

    /// S1: the `Collapsed` marker moves no serialized identity. It encodes byte
    /// for byte as `Raw` under bincode (what `trust-certify` hashes) and JSON, and
    /// `Raw`/`Guarded` encode as the derive did (variant indices 0 and 1).
    #[test]
    fn collapsed_serializes_exactly_as_raw() {
        let guarded = PathGuardTerm::Guarded { guards: vec![Formula::Bool(true)] };
        for codec in [
            |t: &PathGuardTerm| bincode::serialize(t).expect("bincode"),
            |t: &PathGuardTerm| serde_json::to_vec(t).expect("json"),
        ] {
            assert_eq!(codec(&PathGuardTerm::Collapsed), codec(&PathGuardTerm::Raw));
            assert_ne!(codec(&guarded), codec(&PathGuardTerm::Raw));
        }
        assert_eq!(bincode::serialize(&PathGuardTerm::Raw).expect("bincode"), 0u32.to_le_bytes());
        assert_eq!(&bincode::serialize(&guarded).expect("bincode")[..4], 1u32.to_le_bytes());
        let back: PathGuardTerm =
            bincode::deserialize(&bincode::serialize(&guarded).expect("bincode")).expect("de");
        assert_eq!(back, guarded);
        let back: PathGuardTerm =
            serde_json::from_slice(&serde_json::to_vec(&PathGuardTerm::Collapsed).expect("json"))
                .expect("de");
        assert_eq!(back, PathGuardTerm::Raw, "a serialized marker reads back as `Raw`");
    }
}
