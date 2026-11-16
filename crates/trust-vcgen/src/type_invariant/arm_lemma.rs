//! TINV-21 (2026-10-06): kernel-certified `Some`-arm lemmas of inventory getters — design
//! §6 item 2, "peek composition" (`docs/design/2026-10-04-type-invariant-tinv.md`),
//! corrected Option A.
//!
//! THE PROBLEM. `bump(&mut self) { let c = self.peek()?; self.i += 1; Some(c) }` owes
//! `i <= len(b)` at its `Return`, and the increment is safe only because `peek` returned
//! `Some`, which `self.b.get(self.i).copied()` does only when `i < len(b)`. Nothing in
//! `bump` says so: the `get`-`Some` fact lives inside `peek`, and an `Option` result has
//! no grounded discriminant term to carry it across the call.
//!
//! THE LEMMA. For an eligible inventory body `g` (below) and a `&S`/`&mut S` parameter
//! `p` of a candidate type `S`, a lemma is a formula `φ` over `S`'s field placeholders
//! (an atom `x < y` or `x <= y` of two field terms) such that EVERY execution of `g`'s
//! body that reaches `Return` with `_0`'s tag equal to `Some`'s declared discriminant
//! satisfies `φ(*p)` there. It is established by one kernel-certified TINV row of a
//! PROBE of `g` ([`lemma_probe`]):
//! * the probe is `g` with its preconditions, postconditions, contracts and spec cleared,
//!   and its single `Return` block `R` rewritten to `R`'s own statements, then
//!   `d = Discriminant(_0)`, then `SwitchInt(d) [tag(Some) -> A] otherwise N`, with
//!   `A: Goto J`, `N: Goto J`, `J: Return`. The tag is READ OFF `_0`'s type
//!   (`guards::option_some_tag`: the modeled core/std `Option` only), never assumed;
//! * one R row per atom is HAND-BUILT at `(J, terminal)` over `σ(*p)` — not through
//!   `obligation_points`, which owes no R row for a clean `&self` root — with NO entry
//!   preconditions, NO post-call facts, NO construction facts and NO arm facts (lemmas
//!   never consume lemmas), and walked by the ordinary shim (`tinv_check_rows`), which
//!   splits it at `J` into the `A` and `N` edge parts (TINV-9(a));
//! * the lemma is admitted only if the `A` part passes Houdini's own `judge` (situated,
//!   proved by the oracle, a checked vacuity model) AND the caller's `certify` (the
//!   kernel mint and replay). The `N` part is ignored.
//!
//! WHY IT IS SOUND (the lemma). The probe adds no write: one discriminant read into a
//! fresh temp, a switch and gotos. `A` is entered only from the switch's `Some` label,
//! so the `A` part covers exactly the executions of `g`'s real body that reach `Return`
//! with `_0 = Some(..)`. It carries no entry assumption, no post-call `I`, no arm lemma
//! and (inside `tinv_check_rows`) no callee summary or callee write set, so the
//! kernel-certified result is an UNCONDITIONAL partial-correctness fact about `g`'s body.
//! Panics and divergence never reach `Return`. Recursion and mutual recursion are
//! non-circular: no lemma is ever a hypothesis while one is minted. NO DISCRIMINANT TERM
//! IS INTRODUCED OR READ by any fact: the probe's `d` stays an unconstrained local (the
//! walk defines a discriminant only for a fieldless enum), and the `Some`-ness is carried
//! by the CFG region alone, so the unversioned-discriminant hazard of `candidate.rs` is
//! never touched.
//!
//! WHAT PROVES. Inside the probe the `A` arm receives the `get`-`Some` fact through the
//! `copied` hop (`guards::slice_get_some_index_bound_definitions`). A getter of another
//! shape proves only when the ordinary walk routes a fact into `A`. Two routes exist:
//! `enum_construction_demux_definitions` (it routes a construction block's facts only
//! into an arm that reads a `Downcast`, so never into the probe's empty `A`), and
//! `switch_join_variant_arm_definitions` (MATCH-ARM-CALL-CHAIN, 2026-10-07), which seeds
//! at `A` the route guard of the getter's merge arms that may have built `Some`. So an
//! `if i < len { Some(x) } else { None }` getter whose join holds NO statement mints its
//! guard (`i < len`, `i <= len`): the probe's `J` is then exactly `d = discriminant(_0);
//! switchInt(d)` on the `if` partition. Its gates: `J` holds only the discriminant read,
//! `A` entered by exactly one edge, `_0` never mutably borrowed, every merge arm and hop
//! write-checked against the selector (a `Call` hop only with a bare, never mutably
//! borrowed selector). The fact is a SELECTOR guard, not a field fact; the walk relates
//! the selector to `*p` under its ordinary versioning, so a field write, a stale loop
//! selector or a callee between the read and `Return` mints nothing false
//! (`arm_lemma_tests::the_variant_route_mints_no_false_lemma`). A join with any other
//! statement gets no route (precision only).
//!
//! ELIGIBILITY (fail-closed; a miss mints nothing):
//! * the body has a `Some` [`CalleeIdentity`] (it is in the inventory). A trait's own
//!   method body never has one: its identity arguments hold `Self`, a type parameter,
//!   which `callee_identity_for` refuses; and a call through a trait (`<X as Tr>::m`) is
//!   keyed on the TRAIT's `DefId`, so it never equals an impl body's identity. A generic
//!   body has none either. So a lemma is never keyed on a trait item, and a call matches a
//!   lemma only on the EXACT identity it was minted from;
//! * `_0` is the modeled core/std `Option`, there is exactly one `Return` block, the
//!   blocks are indexed by position, and the body has no tail call;
//! * the root is the pointee `*p` of a `&S`/`&mut S` parameter `p` (`param_roots`) that
//!   KEEPS ITS IDENTITY: `p` is never written, the gate `obligations::canonical` applies to
//!   every root (`lemma_param_root`; `is_single_static_assignment_modulo_pointee_borrows`).
//!   A getter that reassigns `p` (`s = t; s.b.get(s.i).copied()`) proves `φ` of `*t` at
//!   `Return`, and the caller instantiates it at the argument bound to `p`: such a root
//!   mints nothing (adversarial review of `fd530b0a54`, 2026-10-06);
//! * `obligations::obligation_points` ACCEPTS the body for `S` under the run's own
//!   inventory, models and facts. The hand-built row skips that enumeration, and with it
//!   every refusal the enumeration makes before it lists a point: an unattributable write
//!   of `S` (`place_write::tinv_refusal`: a raw pointer, an unresolved alias, interior
//!   mutability reached through an unmodelled channel), an `S`-holding constant, an
//!   unclassified unwind point, a cleanup-region call that receives `S`, a rustc-facts
//!   cross-check mismatch. The walk's `σ(*p)` at `Return` is the real value of `*p` only
//!   when every write of `S` is attributed, which is exactly what that enumeration
//!   refuses without. A body it refuses for `S` refuses `S` in every Houdini round as
//!   well, so the gate costs no certificate.
//!
//! AUTHORITY. The lemma's own row is kernel-certified. Its use at a caller
//! (`obligations::arm_fact_sites`: the callee's `*p` is the caller's root at `(T, 0)`,
//! sealed there and kept only in the `Some` region) is a TRUSTED COMPOSITION step, the
//! same class as the post-call `I` assumption (`docs/TCB.md`, "TINV arm-lemma
//! composition"). A row that consumes one keeps the composed TINV class; the lemma never
//! upgrades it.
//!
//! EVIDENCE (TINV-21, 2026-10-06). A consuming row's evidence proves the row UNDER the
//! lemma; it does not re-check the lemma. So the mint keeps the lemma's own evidence
//! ([`mint_body`] returns it beside each lemma), every walk records, PER ROW, the arm
//! facts the row assumed (`TinvBodyRows::row_arm_uses`: the lemma each instantiates and
//! the sealed hypothesis), each published row keeps them (`PublishedTinvRow::lemma_uses`),
//! and Houdini attaches each named lemma, with its `A`-part VC and evidence, to that
//! type's certificate (`houdini::PublishedArmLemma`). A certificate whose rows consumed a
//! lemma it cannot carry, or whose rows and lemmas do not tie, is not published
//! (fail-closed). `TypeInvariantCertificate::replay` re-checks the rows AND the lemmas and
//! ties them: each use names a carried lemma exactly, the use's fact is `φ` instantiated
//! and is the row's sealed hypothesis up to version tokens, and each lemma's VC is a
//! lemma-probe `A` part refuting `¬φ(σ(*p))` ([`strip_versions`], [`is_instance_of`]).

use std::collections::HashSet;

use trust_types::{
    BlockId, CalleeIdentity, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, TypeInvariantPoint, TypeInvariantSite, VerifiableFunction,
    VerificationCondition,
};

use super::houdini::{TinvBody, TinvNote, TinvOracle, judge};
use super::obligations::{
    PreparedBody, SigmaSource, TinvInputs, TinvPointRow, TinvRowKey, TinvStateSpec,
    lemma_param_root, obligation_points_prepared, param_roots, sigma_of_root,
};
use super::unwind::ExactCallModels;
use super::{CandidateConjunct, FieldTerm, Sigma, TinvBodyFacts, TinvType, field_var, instantiate};
use crate::generate::tinv_rows::{RequestRow, RequestType, TinvRowRequest, tinv_check_rows};

/// The conjunct ids a lemma row carries in its `VcKind::TypeInvariant`: far above any id
/// the candidate synthesis assigns, so a lemma VC can never be mistaken for a row of a
/// candidate conjunct. A lemma VC is never published as a TINV row.
pub const LEMMA_CONJUNCT_BASE: u32 = 0xA000_0000;

/// The most atoms one root is probed with (the TINV-9(k) discipline: past it the root
/// mints nothing rather than a truncated set).
pub const MAX_LEMMA_ATOMS: usize = 64;

/// One kernel-certified `Some`-arm lemma (module doc). Only [`mint_arm_lemmas`] builds
/// one outside tests.
#[derive(Debug, Clone)]
pub struct ArmLemma {
    callee: CalleeIdentity,
    function: String,
    ty: String,
    param: usize,
    phi: Formula,
    /// `φ` instantiated, UNVERSIONED, at the callee's root `σ(*p)`: the core whose
    /// negation the lemma's `A` part refutes (`None` only for a test-built lemma).
    core: Option<Formula>,
    vc: Option<VerificationCondition>,
}

impl ArmLemma {
    /// The EXACT identity of the body the lemma was minted from.
    #[must_use]
    pub fn callee(&self) -> CalleeIdentity {
        self.callee
    }

    /// The `def_path` of that body.
    #[must_use]
    pub fn function(&self) -> &str {
        &self.function
    }

    /// The candidate type `S` of the root.
    #[must_use]
    pub fn ty(&self) -> &str {
        &self.ty
    }

    /// The parameter local `p` whose pointee `*p` the lemma is about (argument `p - 1`).
    #[must_use]
    pub fn param(&self) -> usize {
        self.param
    }

    /// `φ` over `S`'s field placeholders ([`field_var`]).
    #[must_use]
    pub fn phi(&self) -> &Formula {
        &self.phi
    }

    /// Relabel a lemma, for the certificate-replay rails only.
    #[cfg(test)]
    pub(crate) fn relabel_for_test(
        &mut self,
        callee: Option<CalleeIdentity>,
        phi_core: Option<(Formula, Option<Formula>)>,
    ) {
        if let Some(c) = callee {
            self.callee = c;
        }
        if let Some((phi, core)) = phi_core {
            self.phi = phi;
            self.core = core;
        }
    }

    /// `φ` instantiated at the callee's root (see the field).
    #[must_use]
    pub fn core(&self) -> Option<&Formula> {
        self.core.as_ref()
    }

    /// The certified `A` edge part the lemma was admitted on (`None` only for a
    /// test-built lemma).
    #[must_use]
    pub fn vc(&self) -> Option<&VerificationCondition> {
        self.vc.as_ref()
    }
}

/// The lemmas of one run.
#[derive(Debug, Clone, Default)]
pub struct ArmLemmas {
    lemmas: Vec<ArmLemma>,
}

impl ArmLemmas {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.lemmas.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &ArmLemma> {
        self.lemmas.iter()
    }

    /// The lemmas minted from the body whose identity is EXACTLY `callee`, about type `ty`.
    pub fn for_callee<'a>(
        &'a self,
        callee: &'a CalleeIdentity,
        ty: &'a str,
    ) -> impl Iterator<Item = &'a ArmLemma> + 'a {
        self.lemmas.iter().filter(move |l| l.callee == *callee && l.ty == ty)
    }

    /// A lemma set built by hand, for the caller-side rails only: production lemmas come
    /// from [`mint_arm_lemmas`] alone.
    #[cfg(test)]
    pub(crate) fn for_test(
        lemmas: impl IntoIterator<Item = (CalleeIdentity, String, String, usize, Formula)>,
    ) -> Self {
        Self {
            lemmas: lemmas
                .into_iter()
                .map(|(callee, function, ty, param, phi)| ArmLemma {
                    callee,
                    function,
                    ty,
                    param,
                    phi,
                    core: None,
                    vc: None,
                })
                .collect(),
        }
    }
}

/// Which lemmas one arm site instantiated: every lemma minted from the body whose identity
/// is EXACTLY `callee`, about type `ty`, at parameter `param` ([`ArmLemmas::for_callee`]
/// filtered by [`ArmLemma::param`]). Reported per walked body
/// through [`ArmLemmaUse`] (`obligations::TinvBodyRows::row_arm_uses`) so that a
/// certificate can carry the lemmas its rows depend on.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ArmLemmaDep {
    pub ty: String,
    pub callee: CalleeIdentity,
    pub param: usize,
}

impl ArmLemmaDep {
    /// Whether `lemma` is one of the lemmas this dependency names.
    #[must_use]
    pub fn names(&self, lemma: &ArmLemma) -> bool {
        lemma.callee == self.callee && lemma.ty == self.ty && lemma.param == self.param
    }
}

/// One lemma a caller's arm fact instantiates: which lemma (`dep` and `phi`) and the
/// UNVERSIONED fact it became at the caller's root (`fact` = `φ(σ(root))`). A row that
/// assumes the fact records it with the sealed hypothesis it carried
/// (`generate::tinv_rows::RowArmUse`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArmLemmaUse {
    pub dep: ArmLemmaDep,
    pub phi: Formula,
    pub fact: Formula,
}

impl ArmLemmaUse {
    /// Whether `lemma` is exactly the lemma this use instantiates.
    #[must_use]
    pub fn names(&self, lemma: &ArmLemma) -> bool {
        self.dep.names(lemma) && lemma.phi == self.phi
    }
}

/// `f` with every variable's version token (`name#tok`) dropped: the UNVERSIONED
/// spelling a field term is instantiated in. Used by certificate replay to compare a
/// sealed hypothesis or a situated core with the instance it was built from.
#[must_use]
pub fn strip_versions(f: &Formula) -> Formula {
    if !trust_types::any_formula_node(f, &mut |g| {
        matches!(g, Formula::Var(name, _) if name.contains('#'))
    }) {
        return f.clone();
    }
    f.clone().map(&mut |g| match g {
        Formula::Var(mut name, sort) => {
            if let Some(pos) = name.find('#') {
                name.truncate(pos);
            }
            Formula::Var(name, sort)
        }
        other => other,
    })
}

/// Whether `needle` occurs as a sub-formula of `hay`.
#[must_use]
pub fn formula_contains(hay: &Formula, needle: &Formula) -> bool {
    trust_types::any_formula_node(hay, &mut |g| g == needle)
}

/// Whether `f` is `phi` with each field placeholder replaced by a variable, the SAME
/// placeholder always by the same variable and distinct placeholders by distinct ones
/// (the shape `instantiate` produces), and nothing else changed.
#[must_use]
pub fn is_instance_of(phi: &Formula, f: &Formula) -> bool {
    fn go<'a>(phi: &Formula, f: &'a Formula, map: &mut Vec<(FieldTerm, &'a str)>) -> bool {
        if let Some(t) = super::as_field_var(phi) {
            let Some(name) = f.var_name() else { return false };
            if let Some((_, n)) = map.iter().find(|(k, _)| *k == t) {
                return *n == name;
            }
            if map.iter().any(|(_, n)| *n == name) {
                return false;
            }
            map.push((t, name));
            return true;
        }
        if std::mem::discriminant(phi) != std::mem::discriminant(f) {
            return false;
        }
        let mut has_children = false;
        let children_ok = trust_types::all_formula_children_zip(phi, f, |a, b| {
            has_children = true;
            go(a, b, map)
        });
        if !has_children {
            phi == f
        } else {
            children_ok
        }
    }
    go(phi, f, &mut Vec::new())
}

/// What [`mint_body`] / [`mint_arm_lemmas`] read beside the bodies: the run's inventory and
/// models, which `obligations::obligation_points` needs to accept a body for a type.
pub(crate) struct LemmaEnv<'a> {
    pub(crate) inventory: &'a HashSet<CalleeIdentity>,
    pub(crate) models: &'a dyn ExactCallModels,
    pub(crate) may_run_user_drop: &'a dyn Fn(&Ty) -> bool,
}

/// The blocks of a lemma probe ([`lemma_probe`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProbeShape {
    /// The original `Return` block, now the switch on `_0`'s tag.
    pub r: BlockId,
    /// The `Some` arm.
    pub a: BlockId,
    /// The `otherwise` arm.
    pub n: BlockId,
    /// The new `Return` block.
    pub j: BlockId,
    /// `Some`'s declared discriminant, read off `_0`'s type.
    pub tag: u128,
}

/// The lemma probe of `func` (module doc), or `None` when `func` is not eligible: `_0`
/// is not the modeled core/std `Option`, there is not exactly one `Return` block, a
/// block's id is not its position, or the body has a tail call.
#[must_use]
pub fn lemma_probe(func: &VerifiableFunction) -> Option<(VerifiableFunction, ProbeShape)> {
    let tag = crate::guards::option_some_tag(func, 0)?;
    let blocks = &func.body.blocks;
    let mut return_block = None;
    for (i, b) in blocks.iter().enumerate() {
        if b.id.0 != i {
            return None;
        }
        match b.terminator {
            Terminator::TailCall { .. } => return None,
            Terminator::Return => {
                if return_block.replace(i).is_some() {
                    return None;
                }
            }
            _ => {}
        }
    }
    let r = return_block?;

    let mut probe = func.clone();
    probe.preconditions.clear();
    probe.postconditions.clear();
    probe.contracts.clear();
    probe.spec = Default::default();

    let d = probe.body.locals.len();
    probe.body.locals.push(LocalDecl {
        index: d,
        // The discriminant of an `Option` is an `isize`, as rustc's own temp (`bump`'s
        // `_6` in the P1 fixture) is extracted.
        ty: Ty::Int { width: 64, signed: true },
        name: None,
    });
    let n0 = probe.body.blocks.len();
    let (a, n, j) = (BlockId(n0), BlockId(n0 + 1), BlockId(n0 + 2));
    let span: SourceSpan = func.span.clone();
    let rb = &mut probe.body.blocks[r];
    rb.stmts.push(Statement::Assign {
        place: Place::local(d),
        rvalue: Rvalue::Discriminant(Place::local(0)),
        span: span.clone(),
    });
    rb.terminator = Terminator::SwitchInt {
        discr: Operand::Move(Place::local(d)),
        targets: vec![(tag, a)],
        otherwise: n,
        exhaustive_enum_unreachable: false,
        span,
    };
    for (id, terminator) in
        [(a, Terminator::Goto(j)), (n, Terminator::Goto(j)), (j, Terminator::Return)]
    {
        probe.body.blocks.push(trust_types::BasicBlock { id, stmts: Vec::new(), terminator });
    }
    Some((probe, ProbeShape { r: BlockId(r), a, n, j, tag }))
}

/// The candidate lemma atoms over `sigma`'s present terms: `x < y` and `x <= y` for every
/// ordered pair of distinct field terms, in a fixed order. `None` past
/// [`MAX_LEMMA_ATOMS`].
#[must_use]
pub fn lemma_atoms(sigma: &Sigma) -> Option<Vec<Formula>> {
    let mut terms: Vec<FieldTerm> = Vec::with_capacity(sigma.value.len() + sigma.len.len());
    for (i, v) in sigma.value.iter().enumerate() {
        if v.is_some() {
            terms.push(FieldTerm::Value(i));
        }
    }
    for (i, l) in sigma.len.iter().enumerate() {
        if l.is_some() {
            terms.push(FieldTerm::Len(i));
        }
    }
    let mut out = Vec::with_capacity(
        (terms.len().saturating_mul(terms.len().saturating_sub(1)) * 2).min(MAX_LEMMA_ATOMS + 2),
    );
    for &x in &terms {
        for &y in &terms {
            if x == y {
                continue;
            }
            let (fx, fy) = (Box::new(field_var(x)), Box::new(field_var(y)));
            out.push(Formula::Lt(fx.clone(), fy.clone()));
            out.push(Formula::Le(fx, fy));
            if out.len() > MAX_LEMMA_ATOMS {
                return None;
            }
        }
    }
    Some(out)
}

/// A candidate lemma before the walk.
struct Pending {
    key: TinvRowKey,
    param: usize,
    phi: Formula,
    core: Formula,
}

/// The lemmas of one body (module doc), each admitted by `judge` and `certify` on its `A`
/// edge part, each with the evidence `certify` returned for that part. Empty when the body
/// is not eligible or the walk refuses.
#[allow(clippy::too_many_arguments)]
pub(crate) fn mint_body<E>(
    func: &VerifiableFunction,
    facts: Option<&TinvBodyFacts>,
    identity: CalleeIdentity,
    types: &[&TinvType],
    env: &LemmaEnv<'_>,
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    step_budget: u64,
) -> Vec<(ArmLemma, E)> {
    let mut prepared = None;
    mint_body_with_prepared(
        func,
        facts,
        identity,
        types,
        env,
        oracle,
        certify,
        step_budget,
        &mut prepared,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn mint_body_with_prepared<'a, E>(
    func: &'a VerifiableFunction,
    facts: Option<&'a TinvBodyFacts>,
    identity: CalleeIdentity,
    types: &[&TinvType],
    env: &LemmaEnv<'a>,
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    step_budget: u64,
    prepared: &mut Option<PreparedBody<'a>>,
) -> Vec<(ArmLemma, E)> {
    if crate::guards::option_some_tag(func, 0).is_none() {
        return Vec::new();
    }
    let mut probe_shape: Option<(VerifiableFunction, ProbeShape)> = None;
    let mut request_types: Vec<RequestType> = Vec::new();
    let mut rows: Vec<RequestRow> = Vec::new();
    let mut pending: Vec<Pending> = Vec::new();
    let mut next_id = LEMMA_CONJUNCT_BASE;
    for ty in types {
        // Only the pointee of a `&S`/`&mut S` parameter that keeps its identity
        // (`lemma_param_root`, read on the body as extracted).
        let roots: Vec<Place> = param_roots(func, &ty.def_path)
            .into_iter()
            .filter(|r| r.projections == [Projection::Deref])
            .filter(|r| lemma_param_root(func, r).as_ref() == Some(r))
            .collect();
        if roots.is_empty() {
            continue;
        }
        let (probe, shape) = match &probe_shape {
            Some(pair) => pair,
            None => {
                let Some(pair) = lemma_probe(func) else { return Vec::new() };
                probe_shape.insert(pair)
            }
        };
        let site = TypeInvariantSite { block: shape.j.0, statement_index: 0 };
        let prep = prepared.get_or_insert_with(|| PreparedBody::new(func, facts, env.models));
        // The enumeration's refusals (module doc, ELIGIBILITY), on the body as extracted.
        let inp = TinvInputs {
            ty,
            inventory: env.inventory,
            models: env.models,
            may_run_user_drop: env.may_run_user_drop,
        };
        if obligation_points_prepared(prep, facts, &inp).is_err() {
            continue;
        }
        let ti = request_types.len();
        request_types.push(RequestType {
            def_path: ty.def_path.clone(),
            post_calls: Vec::new(),
            constructions: Vec::new(),
            arm_facts: Vec::new(),
        });
        for (ordinal, root) in roots.into_iter().enumerate() {
            let sigma = sigma_of_root(probe, ty, &root);
            let Some(atoms) = lemma_atoms(&sigma) else { continue };
            for phi in atoms {
                let c = CandidateConjunct { id: next_id, formula: phi.clone() };
                let Some(core) = instantiate(&c, &sigma) else { continue };
                let key = TinvRowKey {
                    ty: ty.def_path.clone(),
                    conjunct: next_id,
                    point: TypeInvariantPoint::Return,
                    site,
                    ordinal: u32::try_from(ordinal).unwrap_or(u32::MAX),
                    edge: None,
                };
                next_id = next_id.saturating_add(1);
                rows.push(RequestRow {
                    key: key.clone(),
                    ty: ti,
                    point: TinvPointRow {
                        point: TypeInvariantPoint::Return,
                        site,
                        row_point: usize::MAX,
                        root: root.clone(),
                        sigma_src: SigmaSource::Root,
                        state: TinvStateSpec::At,
                        failure: None,
                    },
                    sigma: sigma.clone(),
                    core: core.clone(),
                    edge_guard: None,
                });
                pending.push(Pending { key, param: root.local, phi, core });
            }
        }
    }
    if rows.is_empty() {
        return Vec::new();
    }
    let Some((probe, shape)) = probe_shape else { return Vec::new() };
    let request = TinvRowRequest::new(probe.def_path.clone(), request_types, rows);
    let walked = {
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(
            trust_types::verify_budget::current_deadline(),
            step_budget,
        );
        // The probe's hypothesis was emptied on purpose (`lemma_probe`): the generator
        // does not restate the parameters' type ranges into it.
        crate::generate::without_stated_param_ranges(|| tinv_check_rows(&probe, request))
    };
    let Ok(walked) = walked else { return Vec::new() };
    let mut a_rows: trust_types::fx::FxHashMap<u32, &(TinvRowKey, VerificationCondition)> =
        trust_types::fx::FxHashMap::with_capacity_and_hasher(pending.len(), Default::default());
    for pair in &walked {
        if pair.0.edge == Some(shape.a.0) {
            a_rows.entry(pair.0.conjunct).or_insert(pair);
        }
    }
    let mut out = Vec::new();
    for p in pending {
        // The `A` edge part only. An unsplit row (no `A` part) mints nothing.
        let Some((k, vc)) = a_rows.get(&p.key.conjunct).copied() else { continue };
        let a_key = TinvRowKey { edge: Some(shape.a.0), ..p.key };
        if *k != a_key {
            continue;
        }
        if judge(vc, oracle).is_some() {
            continue;
        }
        // The evidence is KEPT: a certificate whose rows consume this lemma carries it
        // (module doc, EVIDENCE).
        let Some(evidence) = certify(vc) else { continue };
        out.push((
            ArmLemma {
                callee: identity,
                function: func.def_path.clone(),
                ty: a_key.ty,
                param: p.param,
                phi: p.phi,
                core: Some(p.core),
                vc: Some(vc.clone()),
            },
            evidence,
        ));
    }
    out
}

/// Mint the lemmas of every eligible body of the run (module doc), in body order. A body
/// with no identity is never eligible, and an identity seen twice mints nothing for
/// either body (Houdini refuses the run on a duplicate anyway). At most one walk per body,
/// each under `step_budget`. The evidence vector is index-aligned with the lemmas.
pub(crate) fn mint_arm_lemmas<E>(
    types: &[&TinvType],
    bodies: &[TinvBody<'_>],
    env: &LemmaEnv<'_>,
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    step_budget: u64,
) -> (ArmLemmas, Vec<E>, Vec<TinvNote>) {
    let mut prepared_bodies = Vec::new();
    mint_arm_lemmas_with_prepared(
        types,
        bodies,
        &mut prepared_bodies,
        env,
        oracle,
        certify,
        step_budget,
    )
}

pub(crate) fn mint_arm_lemmas_with_prepared<'a, E>(
    types: &[&TinvType],
    bodies: &[TinvBody<'a>],
    prepared_bodies: &mut [Option<PreparedBody<'a>>],
    env: &LemmaEnv<'a>,
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    step_budget: u64,
) -> (ArmLemmas, Vec<E>, Vec<TinvNote>) {
    let mut seen: trust_types::fx::FxHashSet<CalleeIdentity> =
        trust_types::fx::FxHashSet::with_capacity_and_hasher(bodies.len(), Default::default());
    let mut dup: trust_types::fx::FxHashSet<CalleeIdentity> =
        trust_types::fx::FxHashSet::default();
    for b in bodies {
        if let Some(id) = b.identity
            && !seen.insert(id)
        {
            dup.insert(id);
        }
    }
    let mut lemmas = Vec::new();
    let mut evidence = Vec::new();
    for (bi, b) in bodies.iter().enumerate() {
        let Some(id) = b.identity else { continue };
        if dup.contains(&id) {
            continue;
        }
        let mut local_slot = None;
        let prep_slot = prepared_bodies.get_mut(bi).unwrap_or(&mut local_slot);
        for (l, e) in mint_body_with_prepared(
            b.func,
            b.facts,
            id,
            types,
            env,
            oracle,
            certify,
            step_budget,
            prep_slot,
        ) {
            lemmas.push(l);
            evidence.push(e);
        }
    }
    let notes = lemmas
        .iter()
        .map(|l: &ArmLemma| TinvNote {
            ty: l.ty.clone(),
            text: format!(
                "arm lemma (TINV-21): `{}` returns `Some` only when `{}` holds of its \
                 parameter `_{}` (kernel-certified; a caller's use is a trusted composition)",
                l.function,
                render(&l.phi, types.iter().find(|t| t.def_path == l.ty).copied()),
                l.param
            ),
        })
        .collect();
    (ArmLemmas { lemmas }, evidence, notes)
}

/// `phi` with its placeholders spelled by field name (`i < len(b)`), for notes only.
fn render(phi: &Formula, ty: Option<&TinvType>) -> String {
    let name = |i: usize| {
        ty.and_then(|t| t.fields.get(i)).map_or_else(|| format!("#{i}"), |(n, _)| n.clone())
    };
    let term = |f: &Formula| match super::as_field_var(f) {
        Some(FieldTerm::Value(i)) => name(i),
        Some(FieldTerm::Len(i)) => format!("len({})", name(i)),
        None => format!("{f:?}"),
    };
    match phi {
        Formula::Lt(a, b) => format!("{} < {}", term(a), term(b)),
        Formula::Le(a, b) => format!("{} <= {}", term(a), term(b)),
        other => format!("{other:?}"),
    }
}
