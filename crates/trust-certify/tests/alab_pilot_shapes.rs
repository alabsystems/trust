// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! MEASUREMENT for the ALab-derived battery rows `r34`/`r35` — aterm's
//! `constant_time_eq` length seed.
//!
//! # Why this file exists
//!
//! A `targo trust check` battery row needs a built compiler; this file does
//! not. It pins those rows' **Lean content** at crate level, where it is
//! cheap to run and where a change to the kernel, the elaborator or the E6
//! mint shows up as a named failure rather than as a colour change in the
//! battery. It drives the same public path the compiler drives —
//! [`CleanIslandSession::check`] for the island, `admit_program_functions` for
//! the E6 body mint, `admit_certified_island_definition` for the clause-local
//! admission, and `kernel_prove_ensures_by_defeq_in` /
//! `check_ensures_discharge_in` for the verdict — against hand-built extracted
//! IR for each fixture's Rust body.
//!
//! Every island declaration and every clause below is carried by the fixture
//! it names, so a fixture that drifts from its measurement is a test failure
//! here rather than a surprise in the battery. The constants are the
//! declarations only: a fixture's island additionally carries `--` comment
//! lines, so `fixtures_carry_the_measured_island_text` both counts what each
//! row is allowed to declare and re-checks the fixture's island **as written**,
//! comments included.
//!
//! What this does NOT measure: the compiletest/battery plumbing — MIR
//! extraction from real source, the `rustc_parse` island and contract-grammar
//! parses, the publication boundary, the `Gate:` line and the wire counts.
//! Those are what the four battery rows themselves measure, and each fixture
//! header quotes what its row printed. Both halves are needed: this file cannot
//! see the boundary, and the battery cannot tell you WHICH of the island, the
//! mint or the kernel moved when a row goes red.
//!
//! # Naming
//!
//! `pin_*` is a fact a fixture depends on. `neg_*` is a fact that must NOT
//! hold — the close negative twin, so that a later change which makes it hold
//! is caught here and not inside a green row. `boundary_*` records a measured
//! limit that the conversion guide quotes.

use trust_certify::clean_island::{
    CitationVerdict, CleanIslandSession, admit_certified_island_definition,
    kernel_prove_ensures_by_defeq_in,
};
use trust_spec_elab::{FacetTable, ProofClauseInputs};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// extracted-IR builders: the MIR the compiler hands the mint, spelled by hand
// ---------------------------------------------------------------------------

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn func(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    return_ty: Ty,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn f(a: T, b: T) -> bool { a <cmp> b }` — the comparison-to-bool shape.
fn cmp_bool_function(name: &str, cmp: BinOp, param_ty: Ty) -> VerifiableFunction {
    func(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: param_ty.clone(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: param_ty, name: Some("b".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::BinaryOp(
                    cmp,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
            )],
            terminator: Terminator::Return,
        }],
        2,
        Ty::Bool,
    )
}

/// `fn f(a: T, b: T) -> T { if a <cmp> b { <then> } else { <else> } }`, each arm
/// naming a PARAMETER local (1 or 2) — the O0 select diamond with a temp and a
/// join.
fn select_function(
    name: &str,
    cmp: BinOp,
    then_local: usize,
    else_local: usize,
    ty: Ty,
) -> VerifiableFunction {
    func(
        name,
        vec![
            LocalDecl { index: 0, ty: ty.clone(), name: None },
            LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            LocalDecl { index: 4, ty: ty.clone(), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    Place::local(3),
                    Rvalue::BinaryOp(
                        cmp,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(3)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            // TRUE edge (`otherwise`).
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(4),
                    Rvalue::Use(Operand::Copy(Place::local(then_local))),
                )],
                terminator: Terminator::Goto(BlockId(3)),
            },
            // FALSE edge (`targets[0]`).
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(
                    Place::local(4),
                    Rvalue::Use(Operand::Copy(Place::local(else_local))),
                )],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(4))))],
                terminator: Terminator::Return,
            },
        ],
        2,
        ty,
    )
}

/// `fn f(a: T) -> T { <n> }` — the one-parameter CONSTANT body. The lift's
/// uncited reach includes a constant; this is that row, which had no
/// measurement in tree before this file.
fn constant_function(name: &str, value: u128, ty: Ty) -> VerifiableFunction {
    let width = ty.int_width().expect("constant_function is for integer carriers");
    func(
        name,
        vec![
            LocalDecl { index: 0, ty: ty.clone(), name: None },
            LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::Use(Operand::Constant(ConstValue::Uint(value, width))),
            )],
            terminator: Terminator::Return,
        }],
        1,
        ty,
    )
}

// ---------------------------------------------------------------------------
// the harness: island -> mint -> clause-local admission -> verdict
// ---------------------------------------------------------------------------

struct Probe {
    session: CleanIslandSession,
    table: FacetTable,
}

fn check_island(island: &str) -> (CleanIslandSession, Vec<String>) {
    let mut session = CleanIslandSession::new();
    let outcome = session.check(island);
    let errors = outcome.errors.iter().map(|e| e.message.clone()).collect();
    (session, if outcome.is_rejected() { errors } else { Vec::new() })
}

/// Check `island`, mint `function`, admit each named island definition into a
/// clause-local table — the three steps a compilation takes before it asks the
/// kernel anything.
fn probe(island: &str, function: &VerifiableFunction, island_defs: &[&str]) -> Probe {
    let name = function.name.clone();
    let (mut session, errors) = check_island(island);
    assert!(errors.is_empty(), "island must check: {errors:?}");

    let structural = FacetTable::from_structural_facets([
        (format!("crate::{name}").as_str(), true, true, true, true),
        (name.as_str(), true, true, true, true),
    ]);
    let admissions = session.admit_program_functions(std::slice::from_ref(function), &structural);
    assert!(!admissions.is_empty(), "the body must mint an E6 admission: {name}");

    let mut table = structural.clone();
    for (path, admission) in admissions {
        // A clause names the function by its BARE spelling.
        let bare = path.rsplit("::").next().unwrap_or(&path).to_string();
        table.admit(&bare, admission);
    }
    let env = session.environment().expect("untainted session");
    for def in island_defs {
        admit_certified_island_definition(env, def, &mut table)
            .unwrap_or_else(|e| panic!("island definition `{def}` must admit: {e:?}"));
    }
    Probe { session, table }
}

impl Probe {
    /// The UNCITED lane: an `ensures` naming an island definition, closed by
    /// kernel definitional equality. `ProofLift` is the mode every user
    /// `ensures` is elaborated at (`trust_proof_clause_inputs`), so it is the
    /// mode used here whether or not the clause carries a cast.
    fn defeq(
        &self,
        clause: &str,
        params: &[(&str, &str)],
        name: &str,
        result_ty: &str,
    ) -> CitationVerdict {
        kernel_prove_ensures_by_defeq_in(
            self.session.environment().expect("untainted"),
            clause,
            params,
            name,
            &self.table,
            &ProofClauseInputs::proof_lift(Some(result_ty)),
        )
    }

    /// The CITED lane: `ensures … by <theorem>`.
    fn cited(
        &self,
        theorem: &str,
        clause: &str,
        params: &[(&str, &str)],
        name: &str,
    ) -> CitationVerdict {
        self.session.check_ensures_discharge_in(
            theorem,
            clause,
            params,
            name,
            &self.table,
            &ProofClauseInputs::proof_lift(Some("u64")),
        )
    }
}

fn certified(v: &CitationVerdict) -> bool {
    matches!(v, CitationVerdict::KernelStatementMatchCertified)
}

/// **A NEGATIVE MUST PIN THE REFUSAL KIND, not merely the absence of a green.**
/// `!certified(..)` is satisfied by [`CitationVerdict::ClauseOutsideFragment`]
/// (the clause never elaborated), [`CitationVerdict::TheoremNotFound`] and
/// [`CitationVerdict::SessionTainted`] just as much as by the kernel actually
/// declining the identity — and `emit_uncited_island_defeq_refusal` formats the
/// battery grader's `was not discharged by definitional equality` needle for
/// every one of them. So a `neg_*` written as `!certified` would keep passing
/// after a change that stopped the clause reaching the kernel at all, and would
/// report "the false model is still caught" when nothing was checked.
///
/// This asserts the one verdict class that means the KERNEL looked at the
/// obligation and refused it, and returns its detail so a caller can pin the
/// refusal further.
#[track_caller]
fn assert_kernel_refused(v: &CitationVerdict, what: &str) -> String {
    match v {
        CitationVerdict::StatementOrCertificationRejected { detail } => detail.clone(),
        other => panic!(
            "{what}: expected the kernel's own refusal \
             (`StatementOrCertificationRejected`); got {other:?}. \
             A non-kernel verdict here means the obligation never reached the kernel, \
             so this negative proves nothing."
        ),
    }
}

/// The UNCITED-lane form: the kernel built the lifted/plain identity and
/// `Eq.refl` did not check. This is the refusal the battery's `refused` rows
/// are graded on, and the one a `ClauseOutsideFragment` must never be mistaken
/// for.
#[track_caller]
fn assert_defeq_refused(v: &CitationVerdict, what: &str) {
    let detail = assert_kernel_refused(v, what);
    assert!(
        detail.contains("not definitionally equal"),
        "{what}: the kernel must refuse the IDENTITY itself, not something else: {detail}"
    );
}

// ===========================================================================
// r34 / r35 — aterm `constant_time_eq`
// (~/aterm/crates/aterm-gui/src/control_auth.rs:427)
// ===========================================================================

/// `tests/two-language-programs/r38_alab_aterm_ct_eq_seed/main.rs`, verbatim.
const ATERM_ISLAND: &str = "\
def len_eq_isl (la : UInt64) (lb : UInt64) : Bool := decide (la = lb)

def scan_len_isl (la : UInt64) (lb : UInt64) : UInt64 := if la < lb then lb else la

theorem scan_len_covers_left : forall (a : UInt64) (b : UInt64),
    Nat.le (UInt64.toNat a) (UInt64.toNat (if a < b then b else a)) :=
    fun a b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
            Nat.le (UInt64.toNat a) (UInt64.toNat (Decidable.casesOn
                (motive := fun _ => UInt64) d (fun _ => a) (fun _ => b))))
        (instDecidableUInt64Lt a b)
        (fun _ => @Nat.le.refl (UInt64.toNat a))
        (fun h => Nat.le_of_lt h)
";

/// `tests/two-language-programs/r39_alab_aterm_ct_eq_lossy_seed/main.rs`,
/// verbatim: `len_eq_isl` replaced by aterm's PRE-47cca4b seed decision,
/// everything else byte-identical.
const ATERM_LOSSY_ISLAND: &str = "\
def len_eq_isl (la : UInt64) (lb : UInt64) : Bool :=
    Nat.beq (Nat.lor (Nat.mod (Nat.xor (UInt64.toNat la) (UInt64.toNat lb)) 256)
                     (Nat.mod (Nat.div (Nat.xor (UInt64.toNat la) (UInt64.toNat lb)) 256) 256))
            0

def scan_len_isl (la : UInt64) (lb : UInt64) : UInt64 := if la < lb then lb else la

theorem scan_len_covers_left : forall (a : UInt64) (b : UInt64),
    Nat.le (UInt64.toNat a) (UInt64.toNat (if a < b then b else a)) :=
    fun a b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
            Nat.le (UInt64.toNat a) (UInt64.toNat (Decidable.casesOn
                (motive := fun _ => UInt64) d (fun _ => a) (fun _ => b))))
        (instDecidableUInt64Lt a b)
        (fun _ => @Nat.le.refl (UInt64.toNat a))
        (fun h => Nat.le_of_lt h)
";

const ATERM_SEED_CLAUSE: &str = "result == (a_len == b_len) && result == len_eq_isl(a_len, b_len)";
const ATERM_SEED_PARAMS: &[(&str, &str)] = &[("a_len", "u64"), ("b_len", "u64")];

/// r34 (1): the 47cca4b length seed's DECISION, uncited, closed by definitional
/// equality. This is the first battery use of `==` in the comparison-to-bool
/// lane — the in-tree `e9_comparison_bool_discharge.rs` covers `<=`/`>=` only —
/// and therefore the first measurement that an island writes it
/// `decide (la = lb)`.
#[test]
fn pin_r34_length_seed_decision_discharges_by_defeq() {
    let f = cmp_bool_function("lengths_agree", BinOp::Eq, Ty::u64());
    let p = probe(ATERM_ISLAND, &f, &["len_eq_isl"]);
    let verdict = p.defeq(ATERM_SEED_CLAUSE, ATERM_SEED_PARAMS, "lengths_agree", "bool");
    assert!(certified(&verdict), "r34's uncited clause must discharge; got {verdict:?}");
}

/// r34 (2): the comparator walks the LONGER input, cited. The theorem is a
/// TERM proof and that is forced — see `boundary_omega_declines_the_strict_arm`.
#[test]
fn pin_r34_scan_length_bound_discharges_by_citation() {
    let f = select_function("scan_len", BinOp::Lt, 2, 1, Ty::u64());
    let p = probe(ATERM_ISLAND, &f, &["scan_len_isl"]);
    let verdict = p.cited("scan_len_covers_left", "a_len <= result", ATERM_SEED_PARAMS, "scan_len");
    assert!(certified(&verdict), "r34's cited clause must discharge; got {verdict:?}");
}

/// r35's island must CHECK. If it did not, the row would be refused for the
/// wrong reason and its green would say nothing about the false model — the
/// pair-reading hazard r31/r32's headers already carry.
#[test]
fn pin_r35_lossy_seed_island_checks() {
    let (_, errors) = check_island(ATERM_LOSSY_ISLAND);
    assert!(errors.is_empty(), "r35's island must check: {errors:?}");
}

/// r35: aterm's own shipped bug as the model. The Rust body is the FIXED
/// comparator; the island is the seed 47cca4b replaced. Nothing may discharge.
#[test]
fn neg_r35_lossy_seed_does_not_discharge_the_fixed_body() {
    let f = cmp_bool_function("lengths_agree", BinOp::Eq, Ty::u64());
    let p = probe(ATERM_LOSSY_ISLAND, &f, &["len_eq_isl"]);
    let verdict = p.defeq(ATERM_SEED_CLAUSE, ATERM_SEED_PARAMS, "lengths_agree", "bool");
    assert_defeq_refused(
        &verdict,
        "the pre-47cca4b seed must not be credited against the fixed body",
    );
}

/// r35's honest half: the cited clause is untouched by the mutation and must
/// keep discharging, so the row's refusal is attributable to the false model
/// and not to collateral damage. This is the `cited != 0` half of the grader's
/// `refused` contract.
#[test]
fn pin_r35_cited_clause_survives_the_mutation() {
    let f = select_function("scan_len", BinOp::Lt, 2, 1, Ty::u64());
    let p = probe(ATERM_LOSSY_ISLAND, &f, &["scan_len_isl"]);
    let verdict = p.cited("scan_len_covers_left", "a_len <= result", ATERM_SEED_PARAMS, "scan_len");
    assert!(certified(&verdict), "the honest citation must survive; got {verdict:?}");
}

/// MUTATION CONTROL for `pin_r34_scan_length_bound_…`: the same theorem against
/// a MIN body. Without this the positive could be passing because the citation
/// lane credits anything.
#[test]
fn neg_r34_a_min_body_does_not_satisfy_the_scan_length_bound() {
    let f = select_function("scan_len", BinOp::Lt, 1, 2, Ty::u64());
    let p = probe(ATERM_ISLAND, &f, &["scan_len_isl"]);
    let verdict = p.cited("scan_len_covers_left", "a_len <= result", ATERM_SEED_PARAMS, "scan_len");
    assert_kernel_refused(&verdict, "a MIN body must not satisfy the max bound");
}

// ===========================================================================
// BOUNDARIES — measured limits the conversion guide quotes
// ===========================================================================

/// **`split <;> omega` closes the REFLEXIVE arm of a `UInt64` select and not
/// the STRICT one.** r31's `min2_isl a b <= a` splits into `a ≤ a` and
/// (`¬ a<b`) `b ≤ a`, both of which omega takes. Its mirror `… <= b` splits
/// into (`a<b`) `a ≤ b`, which it declines — and so does the max bound
/// `a <= max2 a b`. An explicit term proof through `Nat.le_of_lt` recovers
/// both, which is why r34 carries a term proof where r31 carried a tactic.
///
/// This is the single fact most likely to stop a conversion, because the
/// natural first attempt is r31's tactic and the failure is reported as an
/// island rejection with an `omega` internal reason, not as "state it the
/// other way round".
#[test]
fn boundary_omega_declines_the_strict_arm_of_a_uint64_select() {
    let min_le_left = "\
def m (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
theorem t (a : UInt64) (b : UInt64) : m a b <= a := by
  unfold m
  split <;> omega
";
    let min_le_right = "\
def m (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
theorem t (a : UInt64) (b : UInt64) : m a b <= b := by
  unfold m
  split <;> omega
";
    let max_ge_left_tactic = "\
def x (a : UInt64) (b : UInt64) : UInt64 := if a < b then b else a
theorem t (a : UInt64) (b : UInt64) : a <= x a b := by
  unfold x
  split <;> omega
";
    assert!(check_island(min_le_left).1.is_empty(), "r31's tactic shape must still check");
    let mirror = check_island(min_le_right).1;
    assert!(!mirror.is_empty(), "the MIRROR must still be declined; got a green");
    assert!(
        mirror.iter().any(|m| m.contains("omega")),
        "and it must be declined BY omega, not by something else: {mirror:?}"
    );
    assert!(!check_island(max_ge_left_tactic).1.is_empty(), "the max bound must be declined too");
    // The term spelling both fixtures use recovers it.
    assert!(check_island(ATERM_ISLAND).1.is_empty(), "the term proof must check");
}

/// **The lift's UNCITED reach is a projection, a constant, or a decision of
/// the carrier's own order.** Anything that branches or wraps is not
/// definitionally equal to its `Nat` reading, so a `Nat`-level model of a
/// select or an arithmetic body needs a CITED theorem, and so does a `Nat.beq`
/// decision — there is no uncited route to those.
///
/// The one decision that DOES close uncited is the one whose `Nat` predicate is
/// the carrier's own order over `toNat`: `decide (Nat.le a b)` for a machine
/// `a <= b`, `decide (Nat.lt a b)` for `a < b`. The prelude's unsigned order
/// instance unfolds to exactly that `Nat` order on the `toNat` images —
/// `clean_island.rs::machine_comparison_agrees_with_unsigned_nat_order_at_every_width`
/// proves it by `fun h => h` at every width and refuses the operand-reversed
/// agreement. So the positives below ship with their FALSE twins (operands
/// swapped; `le` against an `lt` body) refused in the same test: a kernel change
/// that made every decision match would turn this red, not leave it a vacuous
/// green. Each arm below is one measured row of the table the guide prints.
#[test]
fn boundary_the_nat_lift_closes_a_projection_and_nothing_that_branches() {
    // A SELECT under the lift: not definitional (the design's own
    // `neg_lifted_select_refinement_is_not_definitional`, re-measured here
    // through the whole discharge path).
    let island = "def cap_nat (c : Nat) (d : Nat) : Nat := if c < d then c else d";
    let f = select_function("sat_coeff", BinOp::Lt, 1, 2, Ty::u64());
    let p = probe(island, &f, &["cap_nat"]);
    let verdict = p.defeq(
        "(result as nat) == cap_nat(coeff as nat, degree as nat)",
        &[("coeff", "u64"), ("degree", "u64")],
        "sat_coeff",
        "u64",
    );
    assert_defeq_refused(&verdict, "a lifted select must not close");

    // A DECISION of the carrier's own order under the lift: after unfolding,
    // `decide (Nat.le a b)` over `toNat` IS the machine `a <= b` (the doc
    // comment above says why), so it closes with no theorem.
    let island = "def le_nat (a : Nat) (b : Nat) : Bool := decide (Nat.le a b)";
    let f = cmp_bool_function("within_degree", BinOp::Le, Ty::u64());
    let p = probe(island, &f, &["le_nat"]);
    let verdict = p.defeq(
        "result == le_nat(coeff as nat, degree as nat)",
        &[("coeff", "u64"), ("degree", "u64")],
        "within_degree",
        "bool",
    );
    assert!(
        certified(&verdict),
        "a lifted decision of the carrier's own order must close; got {verdict:?}"
    );
    // ITS TEETH: the operand-swapped twin is FALSE (it disagrees whenever
    // `coeff != degree`), and the kernel must refuse the identity itself.
    let verdict = p.defeq(
        "result == le_nat(degree as nat, coeff as nat)",
        &[("coeff", "u64"), ("degree", "u64")],
        "within_degree",
        "bool",
    );
    assert_defeq_refused(&verdict, "an operand-swapped lifted decision must not close");

    // The `<` mirror, and ITS teeth: `le` against an `lt` body is false at
    // `coeff == degree`, and must be refused.
    let island = "\
def le_nat (a : Nat) (b : Nat) : Bool := decide (Nat.le a b)
def lt_nat (a : Nat) (b : Nat) : Bool := decide (Nat.lt a b)";
    let f = cmp_bool_function("below_degree", BinOp::Lt, Ty::u64());
    let p = probe(island, &f, &["le_nat", "lt_nat"]);
    let verdict = p.defeq(
        "result == lt_nat(coeff as nat, degree as nat)",
        &[("coeff", "u64"), ("degree", "u64")],
        "below_degree",
        "bool",
    );
    assert!(
        certified(&verdict),
        "a lifted `<` decision of the carrier's own order must close; got {verdict:?}"
    );
    let verdict = p.defeq(
        "result == le_nat(coeff as nat, degree as nat)",
        &[("coeff", "u64"), ("degree", "u64")],
        "below_degree",
        "bool",
    );
    assert_defeq_refused(&verdict, "a `<=` model of a `<` body must not close");

    // `Nat.beq` — ct_eq.lean's OWN spelling of "the lengths agree" — is NOT the
    // carrier's decision and does not close, which is why r34 restates the
    // predicate at `UInt64` instead of citing the owner's file verbatim.
    let island = "def len_eq_nat (la : Nat) (lb : Nat) : Bool := Nat.beq la lb";
    let f = cmp_bool_function("lengths_agree", BinOp::Eq, Ty::u64());
    let p = probe(island, &f, &["len_eq_nat"]);
    let verdict = p.defeq(
        "result == len_eq_nat(a_len as nat, b_len as nat)",
        ATERM_SEED_PARAMS,
        "lengths_agree",
        "bool",
    );
    assert_defeq_refused(&verdict, "a lifted Nat.beq must not close");

    // THE REST OF THE POSITIVE HALF OF THE TABLE (the order decisions are
    // above), so that the reach is measured on both sides rather than
    // asserted. The projection arm is
    // `tests/ui/trust/nat_lift_defeq_discharge.rs` (`def first_nat (a : Nat)
    // (b : Nat) : Nat := a`); the CONSTANT arm had no measurement anywhere in
    // tree, so it is measured here.
    let island = "def c6 (x : Nat) : Nat := 6";
    let f = constant_function("six", 6, Ty::u64());
    let p = probe(island, &f, &["c6"]);
    let verdict = p.defeq("(result as nat) == c6(a as nat)", &[("a", "u64")], "six", "u64");
    assert!(certified(&verdict), "a lifted CONSTANT body must close; got {verdict:?}");
}

/// **THE ANTI-DRIFT CONTROL, and the reason the constants above are spelled
/// out in full rather than built.** Everything this file measures is measured
/// about the strings in THIS file. If a fixture is edited and this file is not,
/// the measurement silently stops being about the row it names — which is worse
/// than no measurement, because the row's header claims it is measured.
///
/// So every island declaration and every clause above is looked up in the
/// fixture that carries it. Comparison is line-by-line on the trimmed text, so
/// the indentation inside `clean { … }` is free and nothing else is.
#[test]
fn fixtures_carry_the_measured_island_text() {
    let rows: &[(&str, &[&str])] = &[
        (
            "r38_alab_aterm_ct_eq_seed",
            &[ATERM_ISLAND, ATERM_SEED_CLAUSE, "a_len <= result by scan_len_covers_left"],
        ),
        (
            "r39_alab_aterm_ct_eq_lossy_seed",
            &[ATERM_LOSSY_ISLAND, ATERM_SEED_CLAUSE, "a_len <= result by scan_len_covers_left"],
        ),
    ];
    let base =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/two-language-programs");
    for (row, texts) in rows {
        let path = base.join(row).join("main.rs");
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("fixture {} must exist: {e}", path.display()));
        // The header is prose ABOUT the row; only the program text counts.
        let program: String = source
            .lines()
            .filter(|l| !l.trim_start().starts_with("//!"))
            .collect::<Vec<_>>()
            .join("\n");
        for text in *texts {
            for line in text.lines().map(str::trim).filter(|l| !l.is_empty()) {
                // A clause line carries the `ensures` keyword in the fixture
                // and not in the constant, so the match is on containment of
                // the trimmed text — which still catches every edit to it.
                assert!(
                    program.lines().any(|l| l.trim() == line || l.trim().ends_with(line)),
                    "{row}/main.rs has drifted from its measurement: no line `{line}`"
                );
            }
        }

        // CONTAINMENT IS NOT ENOUGH. The loop above fires when a measured line
        // is edited or deleted and stays silent when the fixture GAINS one —
        // and gaining a second island `def`, or a second `ensures`, is exactly
        // the edit that breaks a twin's `defeq == 0` grading while every
        // measurement here still passes. So count what the row is allowed to
        // have.
        let island = fixture_island(&program, row);
        let defs = island.lines().filter(|l| l.trim_start().starts_with("def ")).count();
        let theorems = island.lines().filter(|l| l.trim_start().starts_with("theorem ")).count();
        let ensures = program.lines().filter(|l| l.trim_start().starts_with("ensures ")).count();
        assert_eq!(defs, 2, "{row}: the island must declare exactly the 2 measured `def`s");
        assert_eq!(theorems, 1, "{row}: the island must declare exactly the 1 measured `theorem`");
        assert_eq!(
            ensures, 2,
            "{row}: the row must carry exactly the 2 measured `ensures` clauses"
        );

        // AND THE ISLAND AS WRITTEN MUST CHECK. Everything else in this file
        // feeds the kernel the constants above, which carry no comments. The
        // fixture's island carries `--` comment lines that were never measured
        // — and `//` inside an island lexes and then fails to parse, which is
        // the trap that broke r31's first draft. Parse the fixture's own text.
        let (_, errors) = check_island(&island);
        assert!(errors.is_empty(), "{row}: the island AS WRITTEN must check: {errors:?}");
    }
}

/// The `clean { … }` block of a fixture's program text, brace-matched.
fn fixture_island(program: &str, row: &str) -> String {
    let start = program.find("clean {").unwrap_or_else(|| panic!("{row}: no `clean {{` block"));
    let body = &program[start + "clean {".len()..];
    let mut depth = 1usize;
    for (i, c) in body.char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return body[..i].to_string();
                }
            }
            _ => {}
        }
    }
    panic!("{row}: unbalanced `clean {{ … }}`")
}

/// **`usize` reaches the elaborator already resolved.** `a.len()` is `usize`,
/// so this is the spelling an aterm conversion actually has to write. The
/// elaborator itself refuses the bare name; the DISCHARGE lane never hands it
/// one, because `trust_fn_discharge_binder_types` resolves it to the target's
/// fixed width first (docs/TCB.md, `EnsuresCitationDischarge`). Both halves are
/// measured so the guide can say which component does what.
#[test]
fn boundary_usize_is_resolved_before_the_elaborator_sees_it() {
    let f = cmp_bool_function("lengths_agree", BinOp::Eq, Ty::u64());
    let p = probe(ATERM_ISLAND, &f, &["len_eq_isl"]);

    let raw = p.defeq(
        ATERM_SEED_CLAUSE,
        &[("a_len", "usize"), ("b_len", "usize")],
        "lengths_agree",
        "bool",
    );
    match &raw {
        CitationVerdict::ClauseOutsideFragment { reason } => assert!(
            reason.contains("unsupported clause variable type `usize`"),
            "the elaborator's own refusal must name the type: {reason}"
        ),
        other => panic!("the bare `usize` spelling must be refused; got {other:?}"),
    }

    let resolved = p.defeq(ATERM_SEED_CLAUSE, ATERM_SEED_PARAMS, "lengths_agree", "bool");
    assert!(
        certified(&resolved),
        "the 64-bit resolution the discharge lane performs must discharge; got {resolved:?}"
    );
}
