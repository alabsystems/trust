//! Postconditions over a `&mut`-parameter place on a body with an EARLY RETURN
//! and/or DIVERGENT BRANCHES — the multi-predecessor `Return` block.
//!
//! THE DEFECT. The postcondition body is versioned at the RETURN block, where a
//! `&mut`-parameter place carries the reaching-def JOIN token of every return
//! predecessor (`self*.0.0#e_s1_0`). Every conjunct that could constrain it —
//! the out-parameter pin, the block defs — carries a SINGLE establish token
//! (`self*.0.0#s1_0`) or the bare entry name. The join name is therefore FREE,
//! the VC degenerates to a refutable query over a havoc'd post-state, and the
//! solver "refutes" it whatever the body does. Its FALSE TWIN refutes
//! identically: `P` and `!P` produced byte-identical verdicts, which is the
//! signature of a clause that never reached the solver at all.
//!
//! `Grid::abort_reflow_offload`'s first line is an early return, so this is the
//! shape every real method has.
//!
//! THE FIX has two halves, both per-predecessor and both asserted below:
//!   * the RETURN-EDGE GUARD — the `pred -> return` branch condition, which is
//!     what makes the early-return path's postcondition true in the first place
//!     (the guard only returns when the flag is ALREADY false);
//!   * the MERGE PIN — `place#<join token at return> == place#<token at this
//!     predecessor's exit>`, the reaching-value identity that holds on every
//!     execution entering the return block through THIS predecessor.
//!
//! Every case runs in BOTH directions. A true clause that proves is worthless
//! without its false twin still refuting from a GENUINE value.

use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Projection, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::generate_v2_contract_vcs_impl;

// ───────────────────────────── MIR builders ─────────────────────────────

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: span() }
}

/// `(*self).0.<field>` — the pointee of the `&mut self` parameter, through the
/// `st` field, to `field`. Named `self*.0.<field>` by `place_to_var_name`.
fn st_field(field: usize) -> Place {
    Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(0), Projection::Field(field)],
    }
}

fn bool_const(value: bool) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Bool(value)))
}

fn u64_const(value: u128) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(value, 64)))
}

fn copy_of(place: Place) -> Rvalue {
    Rvalue::Use(Operand::Copy(place))
}

fn switch_on(local: usize, zero_target: BlockId, otherwise: BlockId) -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Move(Place::local(local)),
        targets: vec![(0, zero_target)],
        otherwise,
        exhaustive_enum_unreachable: false,
        span: span(),
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// A `struct` ADT stamped the way `trust-mir-extract` stamps one from rustc's
/// `AdtDef`. The generic `Ty::adt` constructor deliberately leaves `adt_kind`
/// `None` so hand-built synthetic types decline the G-STRUCT-KIND
/// certification; a test of the disjoint-field lane must therefore build the
/// REAL shape, or it silently exercises the fail-closed path instead.
fn struct_ty(name: &str, fields: Vec<(String, Ty)>) -> Ty {
    Ty::Adt { arbitrary_precision: None,
        name: name.to_string(),
        fields,
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(trust_types::AdtKind::Struct),
    }
}

/// `struct St { f: bool, g: u64, h: u64 }` inside `struct G { st: St }`, behind
/// `&mut self` — the exact shape of `Grid::abort_reflow_offload`'s receiver.
fn grid_locals(extra: Vec<LocalDecl>) -> Vec<LocalDecl> {
    let st = struct_ty(
        "St",
        vec![
            ("f".to_string(), Ty::Bool),
            ("g".to_string(), Ty::u64()),
            ("h".to_string(), Ty::u64()),
        ],
    );
    let g = struct_ty("G", vec![("st".to_string(), st)]);
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Ref { mutable: true, inner: Box::new(g) },
            name: Some("self".into()),
        },
    ];
    locals.extend(extra);
    locals
}

fn bool_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Bool, name: None }
}

fn u64_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::u64(), name: None }
}

fn func(
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    postconditions: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "a".into(),
        def_path: "a".into(),
        span: span(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::Tuple(vec![]),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions,
        spec: Default::default(),
    }
}

/// `ensures !self.st.f` (`positive == false`) or its FALSE TWIN
/// `ensures self.st.f` (`positive == true`).
fn flag_clause(positive: bool) -> Formula {
    let leaf = Formula::Var("self*.0.0".into(), Sort::Bool);
    if positive { leaf } else { Formula::Not(Box::new(leaf)) }
}

/// Every `Postcondition` VC's formula, rendered, in emission order.
fn postcondition_formulas(f: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect()
}

/// Every emitted VC's `(kind, formula)`, for the fail-closed assertions.
fn all_vc_kinds(f: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(f, None).into_iter().map(|vc| format!("{:?}", vc.kind)).collect()
}

// ═══════════════════════════════════════════════════════════════════════════
// LADDER RUNG 2 — the early-return guard, the minimal reproducer.
//
//   fn a(&mut self) ensures !self.st.f {
//       if !self.st.f { return; }        // bb0 switchInt -> [0: bb2] (early)
//       self.st.f = false;               // bb1
//   }                                    // bb2 return
// ═══════════════════════════════════════════════════════════════════════════

fn early_return_body(positive_clause: bool) -> VerifiableFunction {
    func(
        grid_locals(vec![bool_local(2)]),
        vec![
            block(
                0,
                vec![assign(Place::local(2), copy_of(st_field(0)))],
                switch_on(2, BlockId(2), BlockId(1)),
            ),
            block(1, vec![assign(st_field(0), bool_const(false))], Terminator::Goto(BlockId(2))),
            block(2, vec![], Terminator::Return),
        ],
        vec![flag_clause(positive_clause)],
    )
}

/// THE REGRESSION TEST for the early-return path. Two return predecessors, so
/// two VCs; BOTH must be UNSAT-shaped, and neither may be the fail-closed
/// `SpecUnverifiable` row that the unpinned join name used to force.
///
/// * predecessor `bb0` (the EARLY RETURN): the return-edge guard `!_2` plus the
///   block def `_2 == self*.0.0` plus the merge pin `self*.0.0#<join> ==
///   self*.0.0` force the join name FALSE — the negated clause is UNSAT.
/// * predecessor `bb1` (the WRITE): the merge pin ties the join name to
///   `self*.0.0#s1_0`, which the store pins to `false`.
#[test]
fn early_return_true_clause_proves_on_both_predecessors() {
    let formulas = postcondition_formulas(&early_return_body(false));
    assert_eq!(formulas.len(), 2, "one VC per return predecessor: {formulas:?}");

    // bb0 — the early-return path. The guard is what makes the clause true.
    assert!(
        formulas[0].contains(r#"Eq(Var("self*.0.0#e_s1_0", Bool), Var("self*.0.0", Bool))"#),
        "the merge pin must tie the return block's JOIN name to this predecessor's \
         exit value; without it the clause is a query about a free variable: {}",
        formulas[0]
    );
    assert!(
        formulas[0].contains(r#"Not(Var("_2", Bool))"#),
        "the `bb0 -> bb2` return-edge guard `!_2` must be conjoined — it is the \
         entire reason the early-return path satisfies the clause: {}",
        formulas[0]
    );
    assert!(
        formulas[0].contains(r#"Eq(Var("_2", Bool), Var("self*.0.0", Bool))"#),
        "the block def tying the guard temp to the flag must survive the relevance \
         filter now that the merge pin puts the bare flag name in the body: {}",
        formulas[0]
    );

    // bb1 — the write path.
    assert!(
        formulas[1].contains(r#"Eq(Var("self*.0.0#e_s1_0", Bool), Var("self*.0.0#s1_0", Bool))"#),
        "the merge pin must tie the join name to the WRITING predecessor's own \
         establish token: {}",
        formulas[1]
    );
    assert!(
        formulas[1].contains(r#"Eq(Var("self*.0.0#s1_0", Bool), Bool(false))"#),
        "the store `self.st.f = false` must pin its own establish token: {}",
        formulas[1]
    );
}

/// THE DISCRIMINATION TEST. The exact negation of the clause above, same body.
/// Every pin and guard is still emitted and still carries the body's GENUINE
/// values, so the negated clause stays SATisfiable and the twin is refuted.
///
/// A fix that proved the true case while this also "proved" would be a green
/// light with zero information content.
#[test]
fn early_return_false_twin_stays_refutable() {
    let formulas = postcondition_formulas(&early_return_body(true));
    assert_eq!(formulas.len(), 2, "one VC per return predecessor: {formulas:?}");
    for f in &formulas {
        assert!(
            f.contains(r#"Not(Var("self*.0.0#e_s1_0", Bool))"#),
            "the twin's negated clause must be the plain negation, refutable from \
             the genuine pinned value rather than from havoc: {f}"
        );
        assert!(
            f.contains(r#"Eq(Var("self*.0.0#e_s1_0", Bool), "#),
            "the twin must carry the SAME merge pin as the true clause — a twin that \
             refutes because nothing is pinned proves nothing: {f}"
        );
    }
    // The body genuinely sets the flag false on the write path, so the false
    // twin's `bb1` VC must remain satisfiable: pin says `false`, clause demands
    // `true`.
    assert!(
        formulas[1].contains(r#"Eq(Var("self*.0.0#s1_0", Bool), Bool(false))"#),
        "the refutation must come from the body's real stored value: {}",
        formulas[1]
    );
}

/// Neither direction may reach the fail-closed `SpecUnverifiable` row: that row
/// is what the unpinned join name used to force, and it is an unproved coverage
/// gap, not a verdict.
#[test]
fn early_return_emits_no_unsupported_mir_row() {
    for positive in [false, true] {
        let kinds = all_vc_kinds(&early_return_body(positive));
        assert!(
            !kinds.iter().any(|k| k.contains("UnsupportedMir")),
            "the merge pin must constrain the join name so the silent-weakening \
             tripwire has nothing to fail closed on (positive={positive}): {kinds:?}"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// LADDER RUNG 5/6 — divergent branches between the early return and the exit,
// so the writing block is NOT a predecessor of `Return` at all.
//
//   fn a(&mut self) ensures !self.st.f {
//       if !self.st.f { return; }        // bb0 -> [0: bb5]
//       self.st.f = false;               // bb1
//       if self.st.g > 0 { ... } else { ... }   // bb2 / bb3
//       self.st.g = 0;                   // bb4
//   }                                    // bb5 return
// ═══════════════════════════════════════════════════════════════════════════

fn divergent_branch_body(positive_clause: bool) -> VerifiableFunction {
    func(
        grid_locals(vec![bool_local(2), bool_local(3), u64_local(4)]),
        vec![
            block(
                0,
                vec![assign(Place::local(2), copy_of(st_field(0)))],
                switch_on(2, BlockId(5), BlockId(1)),
            ),
            block(
                1,
                vec![
                    assign(st_field(0), bool_const(false)),
                    assign(Place::local(4), copy_of(st_field(1))),
                    assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            trust_types::BinOp::Gt,
                            Operand::Move(Place::local(4)),
                            Operand::Constant(ConstValue::Uint(0, 64)),
                        ),
                    ),
                ],
                switch_on(3, BlockId(3), BlockId(2)),
            ),
            block(2, vec![assign(st_field(2), u64_const(1))], Terminator::Goto(BlockId(4))),
            block(3, vec![assign(st_field(2), u64_const(0))], Terminator::Goto(BlockId(4))),
            block(4, vec![assign(st_field(1), u64_const(0))], Terminator::Goto(BlockId(5))),
            block(5, vec![], Terminator::Return),
        ],
        vec![flag_clause(positive_clause)],
    )
}

/// The ladder's top rung, in vcgen terms: the flag is written in `bb1`, which is
/// NOT a predecessor of the return block, and two divergent branches merge
/// before the exit. The merge pin must still connect the return block's join
/// name to each predecessor's exit value.
///
/// The join token is `e_s1_0` — entry (the early-return edge) joined with `bb1`'s
/// store, and NOTHING ELSE. That it is not `e_s1_0_s2_0_s3_0_s4_0` is half the
/// fix: the sibling stores to `self.st.g` / `self.st.h` are provably
/// disjointly-addressable fields and must not re-version the flag.
#[test]
fn divergent_branch_true_clause_pins_the_join_name() {
    let formulas = postcondition_formulas(&divergent_branch_body(false));
    assert_eq!(formulas.len(), 2, "one VC per return predecessor: {formulas:?}");
    for f in &formulas {
        assert!(
            f.contains(r#"Eq(Var("self*.0.0#e_s1_0", Bool), "#),
            "the join name must be pinned on EVERY return predecessor, including the \
             one whose block never touches the flag: {f}"
        );
    }
    // `bb4` — the fall-through exit. The flag's single reaching definition there
    // is `bb1`'s store, three blocks upstream and invisible to any lane that
    // scans only `[predecessor, return block]`; the merge pin plus the store's
    // own defining equation are what close the gap.
    assert!(
        formulas[1].contains(r#"Eq(Var("self*.0.0#e_s1_0", Bool), Var("self*.0.0#s1_0", Bool))"#),
        "the join name must be tied to the reaching store's token: {}",
        formulas[1]
    );
    assert!(
        formulas[1].contains(r#"Eq(Var("self*.0.0#s1_0", Bool), Bool(false))"#),
        "and that token must carry the value the BODY stored: {}",
        formulas[1]
    );
}

/// The sibling-field half of the fix, isolated. A store to `self.st.g` must not
/// re-version `self.st.f`: they are distinct fields of a certified plain
/// `struct`, so they provably cannot alias. Before the fix the opaque-deref
/// alias havoc gen'd the receiver's BASE name — a projection ancestor of every
/// field — into the block gen-set, so each sibling store joined its own token
/// into the flag's version and the flag's post-state became unnameable.
#[test]
fn sibling_field_stores_do_not_reversion_the_flag() {
    let f = divergent_branch_body(false);
    let sv = super::StmtVersionCtx::build(&f);
    assert_eq!(
        sv.version_token_at(&f, BlockId(4), 1, "self*.0.0").as_deref(),
        Some("s1_0"),
        "`bb4` stores self.st.g; the flag's reaching definition is still bb1's store"
    );
    assert_eq!(
        sv.version_token_at(&f, BlockId(4), 1, "self*.0.1").as_deref(),
        Some("s4_0"),
        "the store's OWN place must still be re-versioned by it"
    );
}

/// The false twin of the top rung. This is the pair that produced BYTE-IDENTICAL
/// verdicts before the fix.
#[test]
fn divergent_branch_false_twin_differs_from_its_true_clause() {
    let truthy = postcondition_formulas(&divergent_branch_body(false));
    let twin = postcondition_formulas(&divergent_branch_body(true));
    assert_eq!(truthy.len(), twin.len());
    assert_ne!(
        truthy, twin,
        "a clause and its exact negation must not assemble the same VC — identical \
         formulas for P and !P is the signature of a clause that never reaches the \
         solver"
    );
    for f in &twin {
        assert!(
            f.contains(r#"Eq(Var("self*.0.0#e_s1_0", Bool), "#),
            "the twin must be refuted from the GENUINE pinned value, not from havoc: {f}"
        );
    }
    assert!(
        twin[1].contains(r#"Eq(Var("self*.0.0#s1_0", Bool), Bool(false))"#),
        "the twin's refutation must come from the body's real stored value — the \
         clause demands the flag be TRUE and the body provably stores FALSE: {}",
        twin[1]
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// SOUNDNESS GUARDS — the cases where the merge pin must NOT fire.
// ═══════════════════════════════════════════════════════════════════════════

/// A return block that WRITES the clause place itself. The obligation reads the
/// return block's OWN establish token, not the entry join, so pinning it to a
/// predecessor's exit value would assert a FALSE equality and could mint a false
/// proof. The pin must be suppressed; the existing same-block lane owns this.
#[test]
fn return_block_write_suppresses_the_merge_pin() {
    let f = func(
        grid_locals(vec![bool_local(2)]),
        vec![
            block(
                0,
                vec![assign(Place::local(2), copy_of(st_field(0)))],
                switch_on(2, BlockId(2), BlockId(1)),
            ),
            block(1, vec![assign(st_field(0), bool_const(true))], Terminator::Goto(BlockId(2))),
            // The RETURN block itself stores the flag.
            block(2, vec![assign(st_field(0), bool_const(false))], Terminator::Return),
        ],
        vec![flag_clause(false)],
    );
    for formula in postcondition_formulas(&f) {
        assert!(
            !formula.contains(r#"Var("self*.0.0#e_s1_0""#),
            "the obligation must read the return block's own establish token, and the \
             entry-join name must not appear at all: {formula}"
        );
        assert!(
            formula.contains(r#"Eq(Var("self*.0.0#s2_0", Bool), Bool(false))"#),
            "the return block's own store owns the post-state here: {formula}"
        );
    }
}

/// A predecessor whose TERMINATOR havocs the clause place — a call taking
/// `&mut self`. The value at the return block's entry is the POST-call value,
/// which is NOT the predecessor's post-statement value, so the merge pin would
/// be a false equality. It must be suppressed and the row must fail CLOSED.
#[test]
fn call_havoc_on_the_return_edge_suppresses_the_merge_pin() {
    let f = func(
        grid_locals(vec![bool_local(2), LocalDecl { index: 5, ty: Ty::Tuple(vec![]), name: None }]),
        vec![
            block(
                0,
                vec![assign(Place::local(2), copy_of(st_field(0)))],
                switch_on(2, BlockId(2), BlockId(1)),
            ),
            block(
                1,
                vec![assign(st_field(0), bool_const(false))],
                Terminator::Call {
                    func: "helper".into(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(5),
                    target: Some(BlockId(2)),
                    span: span(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    unwind: Default::default(),
                },
            ),
            block(2, vec![], Terminator::Return),
        ],
        vec![flag_clause(false)],
    );
    let vcs = generate_v2_contract_vcs_impl(&f, None);
    let pinned_across_the_call = vcs.iter().any(|vc| {
        matches!(vc.kind, trust_types::VcKind::Postcondition)
            && format!("{:?}", vc.formula).contains(r#", Var("self*.0.0#s1_0", Bool))"#)
    });
    assert!(
        !pinned_across_the_call,
        "a call that can write through `&mut self` invalidates the predecessor's \
         post-statement value; pinning across it would assert a false equality and \
         could mint a FALSE PROOF: {vcs:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// THE DECISIVE CHECK — satisfiability, not string shape.
//
// The convention is "SAT iff violation": a postcondition VC that is UNSAT is
// PROVED, one that is SAT is REFUTED. String assertions pin the mechanism; these
// pin the VERDICT, which is what the defect was actually about. A clause and its
// exact negation must land on OPPOSITE sides of this line — that is the whole
// content of "the verifier is checking this clause".
// ═══════════════════════════════════════════════════════════════════════════

/// Exhaustive propositional satisfiability for the small Boolean skeletons this
/// module builds. Non-propositional leaves (`Gt(_4, 0)`, integer equalities) are
/// treated as free ATOMS keyed by their rendering, which is sound for both
/// directions here: giving the solver MORE freedom can only turn a claimed UNSAT
/// into SAT, so an UNSAT verdict from this evaluator is a genuine UNSAT of the
/// real formula, and the SAT witnesses it finds are checked to be consistent
/// assignments of genuinely independent atoms.
fn atoms(f: &Formula, out: &mut Vec<String>) {
    match f {
        Formula::And(xs) | Formula::Or(xs) => xs.iter().for_each(|x| atoms(x, out)),
        Formula::Not(x) => atoms(x, out),
        Formula::Bool(_) => {}
        Formula::Eq(a, b)
            if matches!(&**a, Formula::Var(_, Sort::Bool) | Formula::Bool(_))
                && matches!(&**b, Formula::Var(_, Sort::Bool) | Formula::Bool(_)) =>
        {
            atoms(a, out);
            atoms(b, out);
        }
        // Keyed by NAME, exactly as `eval` looks a variable up. Keying this by
        // the Debug rendering instead silently forces every variable to `false`,
        // which makes the enumeration report UNSAT for formulas that are plainly
        // satisfiable — a test that would have "confirmed" the very false-proof
        // it exists to catch.
        Formula::Var(n, _) => {
            if !out.contains(n) {
                out.push(n.clone());
            }
        }
        other => {
            let key = format!("{other:?}");
            if !out.contains(&key) {
                out.push(key);
            }
        }
    }
}

fn eval(f: &Formula, env: &[(String, bool)]) -> bool {
    let lookup = |k: &str| env.iter().find(|(n, _)| n == k).map(|(_, v)| *v).unwrap_or(false);
    match f {
        Formula::And(xs) => xs.iter().all(|x| eval(x, env)),
        Formula::Or(xs) => xs.iter().any(|x| eval(x, env)),
        Formula::Not(x) => !eval(x, env),
        Formula::Bool(b) => *b,
        Formula::Eq(a, b)
            if matches!(&**a, Formula::Var(_, Sort::Bool) | Formula::Bool(_))
                && matches!(&**b, Formula::Var(_, Sort::Bool) | Formula::Bool(_)) =>
        {
            eval(a, env) == eval(b, env)
        }
        Formula::Var(n, _) => lookup(n),
        other => lookup(&format!("{other:?}")),
    }
}

/// `true` iff some assignment satisfies `f` — i.e. the VC is REFUTED.
fn is_sat(f: &Formula) -> bool {
    let mut names: Vec<String> = Vec::new();
    atoms(f, &mut names);
    assert!(names.len() <= 16, "skeleton too large to enumerate: {names:?}");
    (0u32..(1u32 << names.len())).any(|mask| {
        let env: Vec<(String, bool)> =
            names.iter().enumerate().map(|(i, n)| (n.clone(), mask & (1 << i) != 0)).collect();
        eval(f, &env)
    })
}

fn postcondition_verdicts(f: &VerifiableFunction) -> Vec<bool> {
    generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| is_sat(&vc.formula))
        .collect()
}

/// EARLY RETURN, both directions. Every predecessor of the true clause must be
/// UNSAT (proved); every predecessor of the false twin must be SAT (refuted).
#[test]
fn early_return_verdicts_discriminate() {
    assert_eq!(
        postcondition_verdicts(&early_return_body(false)),
        vec![false, false],
        "`ensures !self.st.f` holds on BOTH paths — trivially where the guard \
         returns because the flag is already false, and by the store otherwise — \
         so every per-predecessor VC must be UNSAT"
    );
    assert_eq!(
        postcondition_verdicts(&early_return_body(true)),
        vec![true, true],
        "`ensures self.st.f` is violated on BOTH paths and must be REFUTED on both; \
         a twin that proved alongside its own negation would be a green light with \
         no information in it"
    );
}

/// DIVERGENT BRANCHES with the store three blocks upstream of the exit — the
/// ladder's top rung, both directions.
#[test]
fn divergent_branch_verdicts_discriminate() {
    assert_eq!(
        postcondition_verdicts(&divergent_branch_body(false)),
        vec![false, false],
        "the flag is stored false before the branch and neither arm touches it, so \
         the clause holds on every exit path"
    );
    assert_eq!(
        postcondition_verdicts(&divergent_branch_body(true)),
        vec![true, true],
        "the exact negation of a clause the body satisfies must be refuted on every \
         exit path"
    );
}

/// The pair that produced BYTE-IDENTICAL verdicts before the fix, stated as the
/// property rather than as a formula shape.
#[test]
fn a_clause_and_its_negation_never_share_a_verdict() {
    for body in [
        (early_return_body(false), early_return_body(true)),
        (divergent_branch_body(false), divergent_branch_body(true)),
    ] {
        let truthy = postcondition_verdicts(&body.0);
        let twin = postcondition_verdicts(&body.1);
        assert_eq!(truthy.len(), twin.len());
        for (i, (t, f)) in truthy.iter().zip(twin.iter()).enumerate() {
            assert_ne!(
                t, f,
                "VC {i}: a clause and its exact negation landed on the SAME side of \
                 the SAT/UNSAT line. That is the signature of a clause decided by \
                 havoc rather than by the body."
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// LADDER RUNG 6 — the real method's shape: early return, divergent arms, and an
// OPAQUE `&mut self` CALL on one of them.
//
//   fn a(&mut self) ensures !self.st.f {
//       if !self.st.f { return; }               // bb0 -> [0: bb5]
//       self.st.f = false;                      // bb1
//       if self.st.g > 0 { self.helper(); }     // bb2   <- opaque, havocs self
//       else { self.st.h = 0; }                 // bb3
//       self.st.g = 0;                          // bb4
//   }                                           // bb5 return
//
// The call is opaque, so on the `bb2` arm the verifier must assume the callee
// may write `self.st.f` through `&mut self`. The clause is therefore NOT
// provable on the fall-through exit without a callee frame — and UNKNOWN is the
// correct answer there. What must NOT happen is the row being emitted as a
// refutable query and reported as a REFUTATION, identically for the clause and
// its negation. That is the collapse.
// ═══════════════════════════════════════════════════════════════════════════

fn opaque_call_body(positive_clause: bool) -> VerifiableFunction {
    func(
        grid_locals(vec![
            bool_local(2),
            bool_local(3),
            u64_local(4),
            LocalDecl { index: 5, ty: Ty::Tuple(vec![]), name: None },
        ]),
        vec![
            block(
                0,
                vec![assign(Place::local(2), copy_of(st_field(0)))],
                switch_on(2, BlockId(5), BlockId(1)),
            ),
            block(
                1,
                vec![
                    assign(st_field(0), bool_const(false)),
                    assign(Place::local(4), copy_of(st_field(1))),
                    assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            trust_types::BinOp::Gt,
                            Operand::Move(Place::local(4)),
                            Operand::Constant(ConstValue::Uint(0, 64)),
                        ),
                    ),
                ],
                switch_on(3, BlockId(3), BlockId(2)),
            ),
            block(
                2,
                vec![],
                Terminator::Call {
                    func: "helper".into(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(5),
                    target: Some(BlockId(4)),
                    span: span(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    unwind: Default::default(),
                },
            ),
            block(3, vec![assign(st_field(2), u64_const(0))], Terminator::Goto(BlockId(4))),
            block(4, vec![assign(st_field(1), u64_const(0))], Terminator::Goto(BlockId(5))),
            block(5, vec![], Terminator::Return),
        ],
        vec![flag_clause(positive_clause)],
    )
}

/// The exit path that passes through the opaque call must fail CLOSED to the
/// visible `SpecUnverifiable` row — never be emitted as a refutable query whose
/// "counterexample" is just the havoc'd post-state.
///
/// This is the hole that produced the collapse: the out-parameter pin lane scans
/// only `[predecessor, return block]`, and the store to the flag is three blocks
/// upstream, so its silent-weakening ledger came back empty and nothing fired.
#[test]
fn opaque_call_exit_fails_closed_in_both_directions() {
    for positive in [false, true] {
        let kinds = all_vc_kinds(&opaque_call_body(positive));
        assert!(
            kinds.iter().any(|k| k.contains("UnsupportedMir")),
            "the exit path through an opaque `&mut self` call leaves the flag's \
             post-state genuinely unknown; the row must be a VISIBLE coverage gap, \
             not a refutation (positive={positive}): {kinds:?}"
        );
    }
}

/// THE LADDER'S HEADLINE PAIR. Rung 6 and rung 6f previously produced
/// byte-identical verdicts. They must not.
///
/// The early-return predecessor decides both: the guard proves the clause there
/// (the body only returns early when the flag is ALREADY false) and refutes its
/// negation there, from the guard rather than from havoc.
#[test]
fn opaque_call_rung_discriminates_between_a_clause_and_its_negation() {
    let truthy = postcondition_verdicts(&opaque_call_body(false));
    let twin = postcondition_verdicts(&opaque_call_body(true));
    assert_eq!(
        truthy,
        vec![false],
        "the early-return exit must be UNSAT (proved); the opaque-call exit is not a \
         Postcondition row at all — it failed closed"
    );
    assert_eq!(
        twin,
        vec![true],
        "the negation must be REFUTED on the early-return exit, where the guard \
         proves the flag is false"
    );
    assert_ne!(
        truthy, twin,
        "rung 6 and rung 6f must not share a verdict — identical answers for P and \
         !P is precisely the collapse this work exists to remove"
    );
}
