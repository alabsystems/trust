//! `ensures` over a place written THROUGH a `&mut` parameter — the
//! out-parameter pin.
//!
//! `pub fn d(x: &mut u64) ensures *x == 0 { *x = 0; }` is the minimal shape.
//! Before the pin, the postcondition VC was the bare
//! `Not(Eq(Var("x*#s0_0"), Int(0)))`: the block-def extraction DID produce
//! `Eq(Var("x*"), Int(0))`, but `version_block_def_at_establish` could not stamp
//! it (it looks for the establish point of the `*`-stripped base `x`, and a
//! `&mut` PARAMETER is never assigned in-body), so the fact stayed BARE while
//! the obligation body was versioned to `x*#s0_0` — name-disjoint, hence pruned
//! as irrelevant. The VC became a query about a free variable, "refuted"
//! regardless of the body: the TRUE clause and its FALSE twin came back
//! identically Failed.
//!
//! These tests assert the EXACT formulas, because the whole defect was a
//! formula that looked plausible while binding nothing.

use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Projection, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::generate_v2_contract_vcs_impl;

fn u64_const(value: u128) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(value, 64)))
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `ensures <name> == <value>`, spelled the way the contract parser spells a
/// projection chain: `place_to_var_name` renders the pointee of a reference as a
/// POSTFIX star and each `Field(i)` as `.i`, so `*x` is `x*` and `self.n` (field
/// 0 of `&mut self`) is `self*.0`.
fn ensures_eq(name: &str, value: i128) -> Formula {
    Formula::Eq(Box::new(Formula::Var(name.into(), Sort::Int)), Box::new(Formula::Int(value)))
}

fn unit_ret() -> LocalDecl {
    LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: None }
}

fn mut_ref_param(inner: Ty, name: &str) -> LocalDecl {
    LocalDecl {
        index: 1,
        ty: Ty::Ref { mutable: true, inner: Box::new(inner) },
        name: Some(name.into()),
    }
}

fn build(
    locals: Vec<LocalDecl>,
    stmts: Vec<Statement>,
    postconditions: Vec<Formula>,
    return_ty: Ty,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "d".into(),
        def_path: "d".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions,
        spec: Default::default(),
    }
}

fn out_param_fn(
    locals: Vec<LocalDecl>,
    stmts: Vec<Statement>,
    postconditions: Vec<Formula>,
) -> VerifiableFunction {
    build(locals, stmts, postconditions, Ty::Tuple(vec![]))
}

fn struct_ty(name: &str, fields: Vec<(String, Ty)>) -> Ty {
    Ty::adt(name, fields)
}

/// The single Postcondition VC's formula, rendered.
fn postcondition_formula(f: &VerifiableFunction) -> String {
    let mut found: Vec<String> = generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect();
    assert_eq!(found.len(), 1, "expected exactly one Postcondition VC, got {found:?}");
    found.pop().unwrap()
}

// -------------------------------------------------------------------------
// `fn d(x: &mut u64) ensures *x == N { *x = 0; }`
// -------------------------------------------------------------------------

fn scalar_out_param(clause_value: i128) -> VerifiableFunction {
    out_param_fn(
        vec![unit_ret(), mut_ref_param(Ty::u64(), "x")],
        vec![assign(Place { local: 1, projections: vec![Projection::Deref] }, u64_const(0))],
        vec![ensures_eq("x*", clause_value)],
    )
}

/// TRUE clause. The pin `x*#s0_0 == 0` must be conjoined, making the VC UNSAT —
/// i.e. PROVED. Without the pin the formula is the bare negation and the
/// obligation is decided by havoc.
#[test]
fn scalar_out_param_true_clause_is_unsat() {
    assert_eq!(
        postcondition_formula(&scalar_out_param(0)),
        r#"And([Eq(Var("x*#s0_0", Int), Int(0)), Not(Eq(Var("x*#s0_0", Int), Int(0)))])"#,
        "the store `*x = 0` must pin the pointee under the SAME versioned name the \
         obligation body carries, so `P and not-P` is UNSAT and the clause proves"
    );
}

/// FALSE twin, same body. The pin is still emitted — and still carries the
/// BODY's value 0, never the clause's 1 — so `Not(x* == 1)` stays SATisfiable
/// and the clause is refuted. A fix that proved the true case without keeping
/// this refutable would be vacuous.
#[test]
fn scalar_out_param_false_twin_stays_sat() {
    assert_eq!(
        postcondition_formula(&scalar_out_param(1)),
        r#"And([Eq(Var("x*#s0_0", Int), Int(0)), Not(Eq(Var("x*#s0_0", Int), Int(1)))])"#,
        "the false twin must carry the GENUINE pin (value 0 from the body), so the \
         solver refutes it from the real stored value rather than from havoc"
    );
}

// -------------------------------------------------------------------------
// `impl S { fn d(&mut self) ensures self.n == N { self.n = 0; } }`
// -------------------------------------------------------------------------

fn field_out_param(clause_value: i128) -> VerifiableFunction {
    out_param_fn(
        vec![
            unit_ret(),
            mut_ref_param(struct_ty("S", vec![("n".into(), Ty::u64())]), "self"),
        ],
        vec![assign(
            Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
            u64_const(0),
        )],
        vec![ensures_eq("self*.0", clause_value)],
    )
}

/// THE TASK'S TARGET SHAPE: `ensures self.n == 0` on a body that sets it.
#[test]
fn self_field_true_clause_is_unsat() {
    assert_eq!(
        postcondition_formula(&field_out_param(0)),
        r#"And([Eq(Var("self*.0#s0_0", Int), Int(0)), Not(Eq(Var("self*.0#s0_0", Int), Int(0)))])"#,
        "`ensures self.n == 0` over `self.n = 0` must PROVE"
    );
}

/// THE REQUIRED OTHER HALF: `ensures self.n == 1` on the same body must FAIL.
#[test]
fn self_field_false_twin_stays_sat() {
    assert_eq!(
        postcondition_formula(&field_out_param(1)),
        r#"And([Eq(Var("self*.0#s0_0", Int), Int(0)), Not(Eq(Var("self*.0#s0_0", Int), Int(1)))])"#,
        "`ensures self.n == 1` over `self.n = 0` must stay REFUTABLE"
    );
}

// -------------------------------------------------------------------------
// NESTED: `ensures self.storage.flag == N` over `self.storage.flag = 0`
// -------------------------------------------------------------------------

fn nested_out_param(clause_value: i128) -> VerifiableFunction {
    let storage = struct_ty("Storage", vec![("flag".into(), Ty::u64())]);
    let outer = struct_ty("Grid", vec![("storage".into(), storage)]);
    out_param_fn(
        vec![unit_ret(), mut_ref_param(outer, "self")],
        vec![assign(
            Place {
                local: 1,
                projections: vec![Projection::Deref, Projection::Field(0), Projection::Field(0)],
            },
            u64_const(0),
        )],
        vec![ensures_eq("self*.0.0", clause_value)],
    )
}

/// Two-level projection (`self.storage.flag`) rides the same code path: the pin
/// keys on the whole place NAME, so depth costs nothing.
#[test]
fn nested_projection_true_clause_is_unsat() {
    assert_eq!(
        postcondition_formula(&nested_out_param(0)),
        r#"And([Eq(Var("self*.0.0#s0_0", Int), Int(0)), Not(Eq(Var("self*.0.0#s0_0", Int), Int(0)))])"#,
    );
}

#[test]
fn nested_projection_false_twin_stays_sat() {
    assert_eq!(
        postcondition_formula(&nested_out_param(1)),
        r#"And([Eq(Var("self*.0.0#s0_0", Int), Int(0)), Not(Eq(Var("self*.0.0#s0_0", Int), Int(1)))])"#,
    );
}

// -------------------------------------------------------------------------
// FAIL-CLOSED GATES
// -------------------------------------------------------------------------

/// A LATER store to the same place moves the obligation body's version token, so
/// the earlier statement's pin must NOT be emitted for it — and the pin that IS
/// emitted must be the LAST one. Pinning the stale value 7 while the body reads
/// the post-store version would be a FALSE FACT, and a false fact in an
/// antecedent is exactly how a false proof is minted.
#[test]
fn only_the_reaching_definition_is_pinned() {
    let f = out_param_fn(
        vec![unit_ret(), mut_ref_param(Ty::u64(), "x")],
        vec![
            assign(Place { local: 1, projections: vec![Projection::Deref] }, u64_const(7)),
            assign(Place { local: 1, projections: vec![Projection::Deref] }, u64_const(0)),
        ],
        vec![ensures_eq("x*", 0)],
    );
    let formula = postcondition_formula(&f);
    assert!(!formula.contains("Int(7)"), "the OVERWRITTEN value must never be pinned: {formula}");
    assert_eq!(
        formula,
        r#"And([Eq(Var("x*#s0_1", Int), Int(0)), Not(Eq(Var("x*#s0_1", Int), Int(0)))])"#,
        "only the reaching definition (statement 1) may pin, under statement 1's token"
    );
}

/// THE FALSE-PROOF THE LIVENESS GATE EXISTS TO STOP. Body is `*x = 7; *x = 0;`
/// and the clause is `ensures *x == 7` — plainly FALSE, the final value is 0.
/// If the stale statement-0 fact were pinned under the reaching-definition token
/// the VC would read `x*#s0_1 == 7 and not(x*#s0_1 == 7)` — UNSAT, a silent
/// FALSE PROVE. It must stay SATisfiable (refuted).
#[test]
fn stale_store_can_never_prove_a_false_clause() {
    let f = out_param_fn(
        vec![unit_ret(), mut_ref_param(Ty::u64(), "x")],
        vec![
            assign(Place { local: 1, projections: vec![Projection::Deref] }, u64_const(7)),
            assign(Place { local: 1, projections: vec![Projection::Deref] }, u64_const(0)),
        ],
        vec![ensures_eq("x*", 7)],
    );
    assert_eq!(
        postcondition_formula(&f),
        r#"And([Eq(Var("x*#s0_1", Int), Int(0)), Not(Eq(Var("x*#s0_1", Int), Int(7)))])"#,
        "`ensures *x == 7` over `*x = 7; *x = 0;` is FALSE and must stay refutable; \
         pinning the stale statement-0 value would make it vacuously UNSAT"
    );
}

/// A SHARED `&` parameter has no store to pin and must be left exactly as before.
#[test]
fn shared_ref_param_is_not_pinned() {
    let f = out_param_fn(
        vec![
            unit_ret(),
            LocalDecl {
                index: 1,
                ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u64()) },
                name: Some("x".into()),
            },
        ],
        vec![],
        vec![ensures_eq("x*", 0)],
    );
    assert_eq!(
        postcondition_formula(&f),
        r#"Not(Eq(Var("x*", Int), Int(0)))"#,
        "a shared reference has no out-parameter store; behaviour must be unchanged"
    );
}

/// A by-value parameter is not reachable through a `Deref`, so the hunt-6
/// entry-snapshot lane is untouched: no pin.
#[test]
fn by_value_param_is_never_pinned() {
    let f = build(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
        ],
        vec![assign(Place::local(1), u64_const(1))],
        vec![ensures_eq("a", 1)],
        Ty::u64(),
    );
    let formula = postcondition_formula(&f);
    assert!(
        !formula.starts_with(r#"And([Eq(Var("a"#),
        "a by-value reassigned parameter must keep the hunt-6 fail-closed shape: {formula}"
    );
}

/// A clause naming a place the body never stores to gets no pin — the pin is
/// minted from the BODY, never from the clause.
#[test]
fn unwritten_out_param_place_gets_no_pin() {
    let f = out_param_fn(
        vec![
            unit_ret(),
            mut_ref_param(struct_ty("S", vec![("n".into(), Ty::u64())]), "self"),
        ],
        vec![],
        vec![ensures_eq("self*.0", 0)],
    );
    assert_eq!(
        postcondition_formula(&f),
        r#"Not(Eq(Var("self*.0", Int), Int(0)))"#,
        "no store means no pin; the clause's own value must never become a fact"
    );
}

// =========================================================================
// P0 — THE MULTI-WRITE POST-STATE (2026-08-01)
//
// A body writing TWO OR MORE fields produced a VERIFIED FALSE COUNTEREXAMPLE
// against a postcondition it plainly satisfies. Measured, pre-fix:
//
//   self.n = 0; self.f = false;   ensures self.n == 0 && !self.f
//   smtlib=(and (= |self*.1#s0_1| false)
//               (not (and (= |self*.0#s0_1| 0) (not |self*.1#s0_1|))))
//                        ^^^^^^^^^^^^^^^ FREE — no conjunct constrains it
//   => 0 proved, 2 FAILED, counterexample: verified_counterexample = true
//
// Only the LAST write survived. `deref_store_havoc_names` is a whole-function
// list of BASE LOCAL names (a `&mut` parameter contributes the bare `self`), and
// `place_names_overlap` treats `*` as a projection separator — so
// `place_names_overlap("self", "self*.0")` is TRUE and the store `self.f = false`
// was reported by `stmt_writes_name` as a write of its own SIBLING `self*.0`.
// That moved `self*.0`'s version token from `s0_0` to `s0_1`, severing it from
// the exact-token pin in `with_out_param_pins`.
//
// These fixtures use a KIND-STAMPED struct, because the precision fix is gated on
// a positively-confirmed `AdtKind::Struct` (`Ty::adt` leaves `adt_kind: None`,
// which stays fail-closed — see `unkinded_adt_two_writes_stays_fail_closed`).
// =========================================================================

/// A struct `Ty::Adt` carrying the real rustc-derived kind, as
/// `trust-mir-extract::ty_convert` stamps it (`adt_kind: Some(Struct)` for a
/// struct, `Some(Union)` for a union).
fn kinded_adt(name: &str, fields: Vec<(String, Ty)>, kind: Option<trust_types::AdtKind>) -> Ty {
    match Ty::adt(name, fields) {
        Ty::Adt {
            name,
            fields,
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            ..
        } => Ty::Adt {
            name,
            fields,
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            adt_kind: kind,
        },
        other => other,
    }
}

fn bool_const(value: bool) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Bool(value)))
}

/// `S { n: u64, f: bool }` — the task's mixed-type shape.
fn mixed_struct(kind: Option<trust_types::AdtKind>) -> Ty {
    kinded_adt("S", vec![("n".into(), Ty::u64()), ("f".into(), Ty::Bool)], kind)
}

/// `fn d(&mut self) ensures <clause> { self.n = 0; self.f = false; }`
fn two_field_writes(kind: Option<trust_types::AdtKind>, clause: Formula) -> VerifiableFunction {
    out_param_fn(
        vec![unit_ret(), mut_ref_param(mixed_struct(kind), "self")],
        vec![
            assign(
                Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
                u64_const(0),
            ),
            assign(
                Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] },
                bool_const(false),
            ),
        ],
        vec![clause],
    )
}

fn struct_two_field_writes(clause: Formula) -> VerifiableFunction {
    two_field_writes(Some(trust_types::AdtKind::Struct), clause)
}

/// `self.n == <v> && !self.f`
fn mixed_clause(n: i128) -> Formula {
    Formula::And(vec![
        ensures_eq("self*.0", n),
        Formula::Not(Box::new(Formula::Var("self*.1".into(), Sort::Bool))),
    ])
}

/// Every VC kind the generator emits, for the fail-closed gates below.
fn vc_kind_names(f: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .map(|vc| match vc.kind {
            trust_types::VcKind::Postcondition => "Postcondition".to_string(),
            trust_types::VcKind::UnsupportedMir { kind, .. } => format!("UnsupportedMir/{kind}"),
            other => format!("{other:?}"),
        })
        .collect()
}

/// THE P0 ACCEPTANCE ROW — mixed types, clause naming BOTH fields.
///
/// Both writes must be pinned, each under the token its own read carries
/// (`self*.0#s0_0` from statement 0, `self*.1#s0_1` from statement 1). The
/// pre-fix formula constrained ONLY `self*.1`.
#[test]
fn two_field_writes_mixed_true_clause_is_unsat() {
    assert_eq!(
        postcondition_formula(&struct_two_field_writes(mixed_clause(0))),
        r#"And([Eq(Var("self*.1#s0_1", Bool), Bool(false)), And([Eq(Var("self*.0#s0_0", Int), Int(0)), Not(And([Eq(Var("self*.0#s0_0", Int), Int(0)), Not(Var("self*.1#s0_1", Bool))]))])])"#,
        "BOTH writes must be pinned, each under the token its OWN read carries \
         (`self*.0#s0_0` from statement 0, `self*.1#s0_1` from statement 1), so \
         `P and not-P` is UNSAT. Pre-fix, `self*.0` was stamped `#s0_1` by its \
         SIBLING's store and left completely unconstrained."
    );
}

/// THE LOAD-BEARING OTHER HALF. Same two-write body, FALSE clause
/// (`ensures self.n == 1 && !self.f`). Both pins are still emitted and both
/// still carry the BODY's values, so `Not(post)` stays SATisfiable. A fix that
/// bought the row above by making the lane vacuous would break here.
#[test]
fn two_field_writes_mixed_false_twin_stays_sat() {
    let formula = postcondition_formula(&struct_two_field_writes(mixed_clause(1)));
    assert_eq!(
        formula,
        r#"And([Eq(Var("self*.1#s0_1", Bool), Bool(false)), And([Eq(Var("self*.0#s0_0", Int), Int(0)), Not(And([Eq(Var("self*.0#s0_0", Int), Int(1)), Not(Var("self*.1#s0_1", Bool))]))])])"#,
        "the false twin must carry the GENUINE pins (body value 0, never the \
         clause's 1), so `self*.0#s0_0 == 0` together with `not(self*.0#s0_0 == 1)` \
         stays SATisfiable and the clause is refuted from the REAL stored value"
    );
    // The clause's own value may appear ONLY inside the negated postcondition,
    // never as a pin on the positive `And` spine — a pin minted from the clause
    // is exactly how a vacuous proof would be manufactured.
    assert!(
        !formula.contains(r#"Eq(Var("self*.0#s0_0", Int), Int(1))), Not"#),
        "the clause's value must never become a positive fact: {formula}"
    );
}

/// Two writes, clause naming ONLY the FIRST field — the row that isolates the
/// defect from the clause shape entirely (measured pre-fix as `0 proved,
/// 2 failed`, with the VC collapsing to the bare `(not (= |self*.0#s0_1| 0))`).
#[test]
fn two_field_writes_clause_naming_one_field_is_unsat() {
    let formula = postcondition_formula(&struct_two_field_writes(ensures_eq("self*.0", 0)));
    assert!(
        formula.contains(r#"Eq(Var("self*.0#s0_0", Int), Int(0))"#),
        "a clause naming only the first-written field must still be pinned: {formula}"
    );
}

/// SAME-FIELD overwrite is untouched: the liveness gate still keeps only the
/// REACHING definition, so a stale value can never be pinned. `self.n = 0;
/// self.n = 5;` with `ensures self.n == 0` must stay REFUTABLE — this is the
/// false-PROVE direction the precision fix must not open.
#[test]
fn same_field_overwrite_still_pins_only_the_reaching_store() {
    let f = out_param_fn(
        vec![unit_ret(), mut_ref_param(mixed_struct(Some(trust_types::AdtKind::Struct)), "self")],
        vec![
            assign(
                Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
                u64_const(0),
            ),
            assign(
                Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
                u64_const(5),
            ),
        ],
        vec![ensures_eq("self*.0", 0)],
    );
    let formula = postcondition_formula(&f);
    assert!(
        formula.contains(r#"Eq(Var("self*.0#s0_1", Int), Int(5))"#),
        "only the reaching store (value 5, statement 1) may pin: {formula}"
    );
    assert!(
        !formula.contains("Int(0), Int(0)") && !formula.contains(r#"#s0_0", Int), Int(0)"#),
        "pinning the OVERWRITTEN value 0 under the reaching token would silently \
         PROVE a false clause: {formula}"
    );
}

/// FAIL-CLOSED, UNION. A `union`'s fields OVERLAP at byte offset 0, so a store to
/// `self.f` genuinely CAN change `self.n`. The precision fix must decline
/// (G-STRUCT-KIND), leaving the whole-pointee havoc — and the new tripwire must
/// then refuse the row VISIBLY rather than emit a refutable query over the free
/// `self*.0`. This is the direct soundness witness for the fix.
#[test]
fn union_two_field_writes_stays_fail_closed() {
    let kinds = vc_kind_names(&two_field_writes(
        Some(trust_types::AdtKind::Union),
        ensures_eq("self*.0", 0),
    ));
    assert!(
        kinds.iter().any(|k| k.starts_with("UnsupportedMir/")),
        "a union field store must NOT get sibling-disjointness precision, and the \
         unpinned post-state must fail CLOSED to a visible row: {kinds:?}"
    );
    assert!(
        !kinds.iter().any(|k| k == "Postcondition"),
        "no refutable Postcondition row may survive over a free union post-state: {kinds:?}"
    );
}

/// FAIL-CLOSED, UN-MIGRATED ADT. `adt_kind: None` means the type never came from
/// a rustc `AdtDef` and its struct/union-ness is simply unknown. Same posture as
/// the union: decline, then fail closed.
#[test]
fn unkinded_adt_two_writes_stays_fail_closed() {
    let kinds = vc_kind_names(&two_field_writes(None, ensures_eq("self*.0", 0)));
    assert!(
        kinds.iter().any(|k| k.starts_with("UnsupportedMir/")),
        "an ADT of unconfirmed kind must stay fail-closed, never optimistically \
         assume sibling independence: {kinds:?}"
    );
}

/// THE TRIPWIRE'S OWN SCOPE. A clause naming a place the body NEVER writes is
/// GENUINELY refutable and must keep its refutation — the tripwire is keyed on
/// "the body stores to it", not "the clause mentions it". Guards against the
/// fix over-firing and turning true counterexamples into Unknown.
#[test]
fn tripwire_leaves_never_written_place_refutable() {
    let f = out_param_fn(
        vec![unit_ret(), mut_ref_param(mixed_struct(Some(trust_types::AdtKind::Struct)), "self")],
        vec![],
        vec![ensures_eq("self*.0", 0)],
    );
    assert_eq!(
        vc_kind_names(&f),
        vec!["Postcondition".to_string()],
        "an unwritten place must stay a real, refutable obligation"
    );
}
