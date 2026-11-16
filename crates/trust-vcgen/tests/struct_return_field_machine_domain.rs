//! REAL-ARTIFACT lane test: the RETURN RELATION for a postcondition over a
//! field of a STRUCT return.
//!
//! # What was measured, and where the gap was
//!
//! `proved_by_kind.postcond` was reported as 0 for `ay-proof-common`. It is not
//! 0 for every surface — MEASURED on sealed toolchain trust-e26541e3,
//! `-Ztrust-verify-level=2 -Ztrust-policy=advisory`:
//!
//! ```text
//! ensures ret.0 == x + 1   over  fn f(x: u32) -> (u32, u32) { (x + 1, x) }   PROVED
//! ensures ret.0 == x + 1   over  fn f(x: u32) -> Pair       { Pair(x + 1, x) }
//!     unsupported MIR `SpecUnverifiable`: unverifiable source specification
//!     (contract uses unmodeled fixed-width machine arithmetic)
//! ```
//!
//! Byte-identical clause, byte-identical arithmetic, the only difference being
//! `Ty::Tuple` versus `Ty::Adt` for the return local. The RELATION was never the
//! problem: `contract_vcs`'s return-aggregate pin already decomposes
//! `_0 = Literal(move _3)` (an `AggregateKind::Adt { variant: 0 }`) into
//! `_0.0 == _3` under exactly the `_0.i` name the contract surface mints. What
//! was missing was the field's declared WIDTH. An arithmetic-bearing `ensures`
//! may only be read in the Machine{w} lane (the mathematical-`Int` reading of
//! machine arithmetic is the confirmed `result + 1 > result` false-proof
//! vector), and admission there requires ONE shared declared `(width, signed)`
//! for every integer variable in the clause. `machine_int_ty_for_var` resolved
//! `<local>.<i>` for `Ty::Tuple` only, so `_0.0` on a struct had no domain, the
//! clause was inadmissible, and the row fell closed. The relation was in the VC
//! and nothing could consume it.
//!
//! # Why this is ay's case and not a synthetic one
//!
//! `ay-proof-common`'s `Literal` and `Variable` are single-`u32` tuple structs;
//! `Literal::positive/negative/negated` are the campaign's live postcondition
//! examples. Their authored clauses (`result.variable() == var`) are method
//! calls and stay refused for a vocabulary limit that belongs to the call lane.
//! The CALL-FREE statement of the same encoding — `result.0 == var.0 * 2` — is
//! what this file makes provable.
//!
//! # Fixtures
//!
//! Every fixture is the compiler's OWN extracted verification input, captured
//! verbatim from the sealed toolchain with
//!
//! ```text
//! trustc --crate-type=lib --edition=2024 --emit=metadata \
//!        -Ztrust-verify-level=2 -Ztrust-dump=mir:<dir> fx2.rs
//! ```
//!
//! and `fx2.rs` is reproduced in `tests/data/struct_return_field_domain.rs`.
//! These are not hand-built approximations of the MIR — they are the MIR.

use trust_types::{Formula, Ty, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");

fn load(name: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(format!("{FIXTURES}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The lowered-contract marker the compiler stamps on a contract body; a clause
/// swapped in below has to carry it or `contracts.rs` treats the text as a raw
/// unparseable spec closure.
const LOWERED: &str = "__trust_lowered_compiler_contract__:";

/// The same real MIR body with ONE clause replaced. The body, the locals, the
/// aggregate return and every guard stay byte-identical, so a difference in
/// outcome between two rows of the vacuity table below is a difference in the
/// PREDICATE and in nothing else.
///
/// The clause is replaced in ALL THREE carriers the extractor writes it to, not
/// only in `contracts`. Every capture in `tests/fixtures/` states its one clause
/// three ways: the authored text behind the lowered marker in `contracts`, that
/// text's parse in `postconditions`, and the bare text in `spec.ensures`
/// ([`assert_carriers_agree`] checks the fixture before anything is swapped, and
/// `with_clause_reproduces_the_compilers_own_capture` checks the rebuilt function
/// against the compiler's real extraction of a different clause).
///
/// WHY THIS IS NOT COSMETIC (2026-09-26). This helper used to swap `contracts`
/// alone, which builds a function no extraction produces: the swapped clause in
/// one carrier and the ORIGINAL clause `result.0 == var.0 * 2` — TRUE of this
/// body — still in the other two. That was invisible while every formula-only
/// arithmetic `ensures` was stripped unconditionally. `3539149e06` let a
/// Machine{w}-admissible one be CHECKED instead, so the stale true clause got a
/// `Postcondition` row of its own, which proved, and the verdict helpers below
/// credited that proof to the swapped clause: the table reported the false
/// clause `var.0 == var.0 * 2` as proved. MEASURED at `92e7829ca5`: the proved
/// row carried `source_contract_index: None` (it belongs to no authored clause),
/// the false clause's own row fell closed (`SelfReferentialDefinition`), and the
/// false clause proves through no carrier once the carriers agree
/// (`the_false_clauses_prove_through_no_carrier`). The verifier was right; the
/// harness asked it a question about one clause and read the answer for another.
fn with_clause(name: &str, clause: &str) -> VerifiableFunction {
    let mut func = load(name);
    assert_eq!(func.contracts.len(), 1, "fixture must carry exactly one clause");
    assert_carriers_agree(&func, name);
    func.contracts[0].body = format!("{LOWERED}{clause}");
    func.postconditions = vec![parse_clause(clause)];
    func.spec.ensures = vec![clause.to_string()];
    func
}

fn parse_clause(clause: &str) -> Formula {
    trust_types::parse_spec_expr(clause)
        .unwrap_or_else(|| panic!("clause `{clause}` must parse to a formula"))
}

/// The rule [`with_clause`] rebuilds by, read off the capture rather than
/// assumed: the fixture's one `Ensures` is stated identically in `contracts`
/// (marker + text), `postconditions` (the text's parse) and `spec.ensures` (the
/// text).
fn assert_carriers_agree(func: &VerifiableFunction, name: &str) {
    let text = func.contracts[0]
        .body
        .strip_prefix(LOWERED)
        .unwrap_or_else(|| panic!("fixture `{name}`'s clause must carry the lowered marker"));
    assert_eq!(
        func.postconditions,
        vec![parse_clause(text)],
        "fixture `{name}`: the formula carrier must be the parse of the authored clause"
    );
    assert_eq!(
        func.spec.ensures,
        vec![text.to_string()],
        "fixture `{name}`: the spec carrier must be the authored clause text"
    );
}

/// The clause identity a row carries: the index of the authored `contracts`
/// entry it was minted for, `None` for a row that belongs to no authored clause.
/// This is the same field the compiler requires before a solved row may
/// discharge a source-clause marker (`trust_verify.rs`: "Re-pointing a solved
/// row to another contract must not transfer proof").
fn source_index(vc: &trust_types::VerificationCondition) -> Option<usize> {
    vc.contract_metadata.as_ref().and_then(|metadata| metadata.source_contract_index)
}

/// Every `Postcondition` row, read by the verdict helpers below as THE verdict
/// of the fixture's one clause. So each row must actually BELONG to that clause:
/// a row minted for any other formula would have its verdict credited to the
/// clause under test, which is exactly how a proof of a true stale clause read as
/// a proof of a false one (see [`with_clause`]).
fn postcondition_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    let rows: Vec<_> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect();
    for vc in &rows {
        assert_eq!(
            source_index(vc),
            Some(0),
            "a Postcondition row not attributed to the clause under test would have its \
             verdict credited to that clause: {vc:?}"
        );
    }
    rows
}

/// The visible fail-closed rows: a clause that cannot be modelled must produce
/// one of these instead of a verdict.
fn unsupported_details(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "SpecUnverifiable" => Some(detail),
            _ => None,
        })
        .collect()
}

fn formula_contains(formula: &Formula, pred: &impl Fn(&Formula) -> bool) -> bool {
    pred(formula) || formula.children().into_iter().any(|child| formula_contains(child, pred))
}

fn strip_versions(formula: &Formula) -> Formula {
    formula.clone().map(&mut |node| match node {
        Formula::Var(name, sort) if name.contains('#') => {
            Formula::Var(name.split('#').next().unwrap_or(&name).to_string(), sort)
        }
        other => other,
    })
}

/// Whether the VC was emitted in the declared-width bitvector reading. A row
/// that reaches a solver in the mathematical-`Int` spelling of `u32` arithmetic
/// is the false-proof vector this lane must never produce.
fn is_declared_width_encoding(formula: &Formula) -> bool {
    formula_contains(formula, &|node| {
        matches!(
            node,
            Formula::BitVec { .. }
                | Formula::BvAdd(..)
                | Formula::BvSub(..)
                | Formula::BvMul(..)
                | Formula::BvShl(..)
                | Formula::BvLShr(..)
                | Formula::BvULe(..)
                | Formula::BvULt(..)
        )
    })
}

/// The outcome, from the same in-process ay backend the compiler routes to.
fn verdicts(vcs: &[trust_types::VerificationCondition]) -> Vec<VerificationResult> {
    let router = test_router::deterministic_test_router();
    vcs.iter()
        .map(|vc| {
            router
                .verify_all(std::slice::from_ref(vc))
                .into_iter()
                .next()
                .expect("one verdict per VC")
                .1
        })
        .collect()
}

fn all_proved(vcs: &[trust_types::VerificationCondition]) -> bool {
    !vcs.is_empty() && verdicts(vcs).iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
}

// ---------------------------------------------------------------------------
// 1. The obligation is PRODUCED, in the right encoding, and CONSTRAINS the
//    return field.
// ---------------------------------------------------------------------------

/// `fn positive(var: Variable) -> Literal { Literal(var.0 * 2) }`
/// `ensures ret.0 == var.0 * 2`
#[test]
fn struct_return_field_postcondition_is_emitted_and_pins_the_return_field() {
    let func = load("newtype_struct_return_positive");

    // The local this whole lane turns on: a single-`u32` tuple struct, kind
    // read off a real `AdtDef`. If a future extraction stops stamping the kind
    // the fix must decline, so pin the shape the fixture actually carries.
    let ret = &func.body.locals[0];
    assert!(
        matches!(
            &ret.ty,
            Ty::Adt { fields, adt_kind: Some(trust_types::AdtKind::Struct), .. }
                if fields.len() == 1
                    && matches!(fields[0].1, Ty::Int { width: 32, signed: false })
        ),
        "fixture's return local must be a single-u32 struct: {:?}",
        ret.ty
    );

    let posts = postcondition_vcs(&func);
    assert!(
        !posts.is_empty(),
        "the `ensures` must produce a Postcondition obligation, not a fail-closed row; \
         unsupported rows were: {:?}",
        unsupported_details(&func)
    );
    assert!(
        unsupported_details(&func).is_empty(),
        "no clause may fall closed once the struct field has a declared domain: {:?}",
        unsupported_details(&func)
    );

    for vc in &posts {
        // ENCODING: declared-width QF_BV, never the mathematical-Int reading.
        assert!(
            is_declared_width_encoding(&vc.formula),
            "an arithmetic-bearing `ensures` must be emitted in the declared-width \
             reading: {:?}",
            vc.formula
        );
        // The formula CONSTRAINS the return field: `_0.0` appears and is tied
        // to a body term. A free `_0.0` would make `Not(post)` satisfiable by
        // havoc — a refutable query about nothing.
        let formula = strip_versions(&vc.formula);
        assert!(
            formula_contains(&formula, &|node| node.var_name() == Some("_0.0")),
            "the postcondition must reason about the return field `_0.0`: {:?}",
            vc.formula
        );
        assert!(
            formula_contains(&formula, &|node| matches!(
                node,
                Formula::Eq(lhs, _) | Formula::Eq(_, lhs) if lhs.as_ref().var_name() == Some("_0.0")
            )),
            "the return field `_0.0` must be PINNED to the body's aggregate operand, \
             not left free: {:?}",
            vc.formula
        );
    }

    // OUTCOME.
    assert!(
        all_proved(&posts),
        "the exact encoding relation must be discharged; got {:?}",
        verdicts(&posts)
    );
}

// ---------------------------------------------------------------------------
// 2. MUTATION: the same clause, off by one, must NOT be proved.
// ---------------------------------------------------------------------------

/// Same body, clause `ensures ret.0 == var.0 * 2 + 1` — the NEGATIVE-literal
/// encoding. If this proved, the lane would be crediting a predicate the body
/// does not satisfy.
#[test]
fn the_off_by_one_encoding_mutant_is_refuted() {
    let func = load("newtype_struct_return_positive_mutant");
    let posts = postcondition_vcs(&func);
    assert!(
        !posts.is_empty(),
        "the mutant must still produce a real obligation (a refusal would not \
         discriminate): unsupported rows {:?}",
        unsupported_details(&func)
    );
    let outcomes = verdicts(&posts);
    assert!(
        outcomes.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
        "the mutant encoding must be REFUTED, not proved; got {outcomes:?}"
    );
    assert!(
        !outcomes.iter().all(|r| matches!(r, VerificationResult::Proved { .. })),
        "the mutant encoding must never be proved; got {outcomes:?}"
    );
}

// ---------------------------------------------------------------------------
// 3. VACUITY TABLE. Same MIR body, one clause swapped per row.
// ---------------------------------------------------------------------------

/// The mandatory vacuity table for anything this lane makes provable, run over
/// ONE real body so the only variable is the predicate.
///
/// Body: `fn positive(var: Variable) -> Literal { Literal(var.0 * 2) }`.
///
/// The row that decides whether this lane did real work is
/// `result.0 != var.0 * 2 + 1`: it is TRUE of every value the function can
/// return (`2v` and `2v+1` differ by one in every `u32`, so they are never
/// equal) and it is NOT a logical tautology (over a free `result.0` it is
/// falsifiable). It can only be discharged THROUGH the return relation.
/// `result.0 >= 0` is deliberately in the table as the row that looks like a
/// discriminator and is not: every `u32` bit pattern is unsigned-`>= 0`, so
/// `Not(P)` is UNSAT over a free result and the row says nothing about the
/// body.
#[test]
fn vacuity_table_over_one_real_body() {
    let rows: &[(&str, bool, &str)] = &[
        // clause, must_be_proved, why
        ("(result.0) == ((var.0) * (2))", true, "the exact encoding relation"),
        (
            "(result.0) != (((var.0) * (2)) + (1))",
            true,
            "TRUE of every returned value, NOT a logical tautology — THE DISCRIMINATOR",
        ),
        // --- tautologies: proved, and proved WITHOUT this lane as well ---
        ("(1) == (1)", true, "logical tautology"),
        ("(result.0) == (result.0)", true, "logical tautology"),
        ("(result.0) <= (result.0)", true, "logical tautology"),
        ("true", true, "boolean literal — see the note below, this differs end-to-end"),
        // --- true of the whole TYPE but body-independent: NOT a discriminator ---
        (
            "(result.0) >= (0)",
            true,
            "true of every u32, body-independent: `Not(P)` is UNSAT over a FREE result",
        ),
        // --- must not prove ---
        ("false", false, "contradiction"),
        ("(result.0) == (((var.0) * (2)) + (1))", false, "off-by-one mutant"),
        ("(var.0) == ((var.0) * (2))", false, "false of the function"),
        ("(result.0) == ((var.0) * (3))", false, "wrong coefficient"),
        ("(result.0) != ((var.0) * (2))", false, "the OTHER constructor's discriminator"),
    ];

    let mut report = String::new();
    let mut bad = Vec::new();
    for (clause, must_prove, why) in rows {
        let func = with_clause("newtype_struct_return_positive", clause);
        let posts = postcondition_vcs(&func);
        let unsupported = unsupported_details(&func);
        let proved = all_proved(&posts);
        report.push_str(&format!(
            "  {clause:<44} proved={proved:<5} rows={} refusals={} — {why}\n",
            posts.len(),
            unsupported.len()
        ));
        if proved != *must_prove {
            bad.push(format!("{clause} (expected proved={must_prove}, got {proved}) — {why}"));
        }
    }
    assert!(bad.is_empty(), "vacuity table disagreed:\n{report}\nrows: {bad:#?}");

    // The load-bearing shape check: THE PROVABLE SET IS NOT THE TAUTOLOGIES.
    // Four proved rows are tautologies, one (`result.0 >= 0`) is a body-
    // independent type-wide fact, and one — the discriminator — is neither and
    // is proved only through the return relation (see
    // `the_discriminator_needs_the_return_relation`). Five rows that are false,
    // or true only of a different constructor, do not prove. A widening whose
    // newly-provable set were the tautologies would flip the discriminator row
    // and fail here.
    //
    // ONE ROW DIFFERS END-TO-END AND IS RECORDED RATHER THAN HIDDEN. `true`
    // proves at THIS layer (generator + in-process ay router) but comes back
    // UNKNOWN from the compiler on the sealed toolchain, because the vacuity
    // gate that downgrades a definitively-false boolean skeleton
    // (`Not(Bool(true))`) sits above this one. `1 == 1` is opaque to that gate
    // — an arithmetic atom — and proves at BOTH layers, kernel-certified. So
    // the compiler's tautology filter is a boolean-literal filter, not a
    // validity filter, and this table is the layer where that shows.
    eprintln!("vacuity table over `positive(var) -> Literal {{ Literal(var.0 * 2) }}`:\n{report}");
}

/// The discriminator row is discharged THROUGH the return relation and not
/// around it. Deleting the aggregate return assignment — the one statement that
/// relates `_0.0` to the body's computation — must take the proof away. If it
/// survived, the row would be proving something about a free return value.
#[test]
fn the_discriminator_needs_the_return_relation() {
    let clause = "(result.0) != (((var.0) * (2)) + (1))";
    let with_relation = with_clause("newtype_struct_return_positive", clause);
    assert!(
        all_proved(&postcondition_vcs(&with_relation)),
        "control: the discriminator proves with the return relation present"
    );

    let mut without = with_relation;
    for block in &mut without.body.blocks {
        block.stmts.retain(|stmt| {
            !matches!(
                stmt,
                trust_types::Statement::Assign { place, rvalue: trust_types::Rvalue::Aggregate(..), .. }
                    if place.local == 0 && place.projections.is_empty()
            )
        });
    }
    let posts = postcondition_vcs(&without);
    assert!(
        !all_proved(&posts),
        "with the return aggregate deleted, `_0.0` is free and the discriminator must \
         stop proving; got {:?}",
        verdicts(&posts)
    );
}

// ---------------------------------------------------------------------------
// 4. WHAT STAYS REFUSED. Each of these is a decline, and each decline is the
//    correct outcome — the gate is load-bearing, not decoration.
// ---------------------------------------------------------------------------

/// A UNION's fields alias at offset 0, so `.0` and `.1` name the same bytes at
/// two different types and neither declared width is a sound domain for the
/// other. Rewriting the fixture's return kind to `Union` must take the verdict
/// away and restore the visible fail-closed row.
#[test]
fn union_return_field_has_no_domain() {
    assert_kind_declines(Some(trust_types::AdtKind::Union), "union");
}

/// An ENUM's field view is variant-dependent (`Ty::Adt`'s `fields` is the
/// union/struct view), so a positional name is ambiguous.
#[test]
fn enum_return_field_has_no_domain() {
    assert_kind_declines(Some(trust_types::AdtKind::Enum), "enum");
}

/// `adt_kind: None` is a hand-built or pre-W19-serialized `Ty::Adt` whose kind
/// was never read off a real `AdtDef`. Declining it is the same G-STRUCT-KIND
/// discipline the field-setter frame surface uses: never optimistically mint on
/// an un-migrated shape.
#[test]
fn unstamped_adt_kind_has_no_domain() {
    assert_kind_declines(None, "unstamped");
}

/// Rewrite the return type's ADT kind in BOTH places the extraction keeps it —
/// the local decl and `body.return_ty` — so the generator sees a coherent
/// function and declines for the KIND rather than for a shape mismatch.
fn assert_kind_declines(kind: Option<trust_types::AdtKind>, label: &str) {
    let mut func = load("newtype_struct_return_positive");
    let set = |ty: &mut Ty| {
        if let Ty::Adt { adt_kind, .. } = ty {
            *adt_kind = kind;
        } else {
            panic!("fixture's return local must be an Adt");
        }
    };
    set(&mut func.body.locals[0].ty);
    set(&mut func.body.return_ty);

    assert!(
        postcondition_vcs(&func).is_empty(),
        "a {label} return field must not yield a machine domain"
    );
    let details = unsupported_details(&func);
    assert!(
        details.iter().any(|d| d.contains("unmodeled fixed-width machine arithmetic")),
        "the {label} decline must keep its visible fail-closed row: {details:?}"
    );
}

/// A NESTED projection (`result.0.1`) is not a name this lane can resolve: the
/// callers split on the FIRST `.`, so `"0.1".parse::<usize>()` fails and the
/// whole clause keeps failing closed. Pinned so a future widening of the
/// projection surface cannot silently start resolving a chain whose MIR place
/// nobody checked.
#[test]
fn nested_projection_still_has_no_domain() {
    let func = with_clause("newtype_struct_return_positive", "(result.0.0) == ((var.0) * (2))");
    assert!(
        postcondition_vcs(&func).is_empty(),
        "a nested return projection must not be resolvable"
    );
}

/// A struct whose fields have DIFFERENT widths is the width-mixup vector: read
/// `.1`'s domain off `.0` and a 32-bit computation would be checked at 8 bits.
/// `Packed(pub u8, pub u32)` with `ensures ret.1 == x + 1` must therefore either
/// resolve `.1` at its OWN `u32` domain or decline — never silently borrow
/// `.0`'s `u8`. Here the sibling `.0` pin (`u8`) is conjoined into the same VC,
/// which puts the assembled formula outside the single declared width, so the
/// row falls closed with the honest per-VC diagnostic.
#[test]
fn mixed_width_struct_return_falls_closed_visibly() {
    let func = load("mixed_width_struct_return_second_field");
    let ret = &func.body.locals[0];
    assert!(
        matches!(
            &ret.ty,
            Ty::Adt { fields, .. }
                if matches!(fields[0].1, Ty::Int { width: 8, .. })
                    && matches!(fields[1].1, Ty::Int { width: 32, .. })
        ),
        "fixture must carry heterogeneous field widths: {:?}",
        ret.ty
    );
    let posts = postcondition_vcs(&func);
    let unsupported = unsupported_details(&func);
    assert!(
        posts.is_empty(),
        "a VC mixing an 8-bit sibling pin with a 32-bit clause must not be emitted \
         as a verdict-bearing row: {posts:#?}"
    );
    assert!(
        !unsupported.is_empty(),
        "the mixed-width row must be VISIBLY refused, never silently dropped"
    );
}

// ---------------------------------------------------------------------------
// 5. THE KERNEL DOOR. `promote_kernel_certifiable` and the bridge's certify
//    fallback call `trust_certify::certify_vc` on any undecided VC, and
//    `certify_vc` is FORMULA-driven, not kind-driven — so a new capability
//    reaches a CERTIFIED row with no second gate to catch a mistake. Measure
//    which of these rows the kernel actually certifies, rather than assuming.
// ---------------------------------------------------------------------------

/// MEASURED, with a control that this change does not touch.
///
/// `promote_kernel_certifiable` and the bridge's certify fallback call
/// `trust_certify::certify_vc` on any undecided VC, and `certify_vc` is
/// FORMULA-driven, not kind-driven — so a new capability reaches a CERTIFIED
/// row with no second gate. What this measures is which rows it actually takes:
///
/// ```text
///   tuple_ensures_duplicate         `ret.0 == ret.1`     proved 1  certified 1
///   tuple_return_field_arithmetic   `ret.0 == x + 1`     proved 1  certified 1   <- CONTROL
///   tuple_return_field_arithmetic   `ret.0 == x + 2`     proved 0  certified 0   <- CONTROL MUTANT
///   newtype_struct_return_positive  `ret.0 == var.0*2`   proved 1  certified 0
///   newtype_struct_return_positive  `ret.0 != var.0*2+1` proved 1  certified 0
///   newtype_struct_return_positive  `ret.0 == ret.0`     proved 1  certified 1
///   newtype_struct_return_positive  `1 == 1`             proved 1  certified 1
/// ```
///
/// THE DOOR MOVED, AND THIS IS WHERE THAT IS SAID (VCGEN-PERF-67-69-VERDICTS-1,
/// 2026-11-07). Until `de718fe643` the kernel certified only the Int-lane rows
/// (the tautologies) and none of the declared-width QF_BV rows, and this test
/// pinned the control at `certified 0`. `de718fe643` added
/// `trust_certify::bv_equality` (documented in `docs/TCB.md` by `ca243a06a2`):
/// each distinct well-sorted bitvector TERM becomes its own integer skolem, only
/// the original top-level equalities and disequalities are kept, and the
/// refutation the Clean kernel checks uses `Eq.refl`/`Eq.symm`/`Eq.trans` alone.
/// Any model of the VC maps to a model of that context (equal terms to equal
/// values), so the projection only weakens the goal; it interprets no arithmetic.
/// The control's violation is such a chain — `_0.0#s1_1 = _3 = _4.0#s0_1 =
/// bvadd(x, 1)` against `!(_0.0#s1_1 = bvadd(x, 1))` — so it now certifies, with
/// a certificate that replays against its own goal. That is a true formula
/// kernel-checked, not a false certification: the false clause over the same body
/// (`x + 2`) neither proves nor certifies, and a certified row the solver does
/// not prove fails this test.
///
/// This lane's struct-return rows do NOT certify: the newtype body pins `_4 =
/// var.0` and computes `bvmul(_4, 2)`, and closing `bvmul(_4, 2) = bvmul(var.0, 2)`
/// needs congruence, which the equality family deliberately does not have. So the
/// struct-return lane is in a certification class no stronger than the control's
/// — the property this test exists to keep — and every count is pinned exactly,
/// so a change that mints kernel authority for another declared-width row has to
/// come here and say so.
///
/// Under `-Ztrust-policy=certify` an ay `Proved` with no kernel token is reported
/// `Unknown`, so the exact struct relation still reads `Unknown` there while
/// `ensures result.0 == result.0` reads CERTIFIED. That is a real and
/// uncomfortable property of the Machine{w} lane and it is worth headlining.
#[test]
fn kernel_certification_matches_the_untouched_control() {
    let measure = |fixture: &str, clause: Option<&str>| -> (usize, usize, usize) {
        let func = match clause {
            Some(c) => with_clause(fixture, c),
            None => load(fixture),
        };
        let posts = postcondition_vcs(&func);
        let outcomes = verdicts(&posts);
        let mut certified = 0;
        for (vc, outcome) in posts.iter().zip(&outcomes) {
            let Some(evidence) = trust_certify::certify_vc(vc) else { continue };
            certified += 1;
            // A kernel certificate of a goal the solver does not discharge would
            // be a false certification (or a solver regression): either way, stop.
            assert!(
                matches!(outcome, VerificationResult::Proved { .. }),
                "{fixture} {clause:?}: kernel-certified but not proved: {outcome:?}"
            );
            assert!(
                trust_certify::replay_vc_evidence(vc, &evidence),
                "{fixture} {clause:?}: the certificate must replay against its own goal"
            );
        }
        let proved =
            outcomes.iter().filter(|r| matches!(r, VerificationResult::Proved { .. })).count();
        (posts.len(), proved, certified)
    };

    let control = measure("tuple_return_field_arithmetic_control", None);
    let control_mutant =
        measure("tuple_return_field_arithmetic_control", Some("(result.0) == ((x) + (2))"));
    let exact = measure("newtype_struct_return_positive", None);
    let disc =
        measure("newtype_struct_return_positive", Some("(result.0) != (((var.0) * (2)) + (1))"));
    let taut = measure("newtype_struct_return_positive", Some("(result.0) == (result.0)"));
    let mutant =
        measure("newtype_struct_return_positive", Some("(result.0) == (((var.0) * (2)) + (1))"));
    eprintln!(
        "kernel door (rows, proved, certified):\n  CONTROL tuple+arith {control:?}\n  \
         CONTROL mutant {control_mutant:?}\n  exact {exact:?}\n  discriminator {disc:?}\n  \
         tautology {taut:?}\n  mutant {mutant:?}"
    );

    for (label, row) in [("mutant", mutant), ("control mutant", control_mutant)] {
        assert!(row.0 > 0, "{label}: the false clause must still produce its row");
        assert_eq!(row.1, 0, "{label}: a false postcondition must never be proved");
        assert_eq!(row.2, 0, "{label}: a false postcondition must never be kernel-certified");
    }

    // The control is the pre-existing declared-width postcondition lane. Its
    // violation is a pure equality chain, which `bv_equality` certifies.
    assert_eq!(
        (control.1 > 0, control.2),
        (true, 1),
        "control: the declared-width equality chain proves and is kernel-certified"
    );
    // This change must never put its new rows in a STRONGER class than the
    // control, and the exact class is pinned so any move comes here.
    assert!(
        exact.2 <= control.2 && disc.2 <= control.2,
        "the struct-return lane must not certify beyond the untouched control: \
         {exact:?} {disc:?} vs {control:?}"
    );
    assert_eq!(
        (exact.2, disc.2),
        (0, 0),
        "measured: the struct-return rows need congruence under bvmul, which the \
         equality family does not have; a NEW kernel-certified class needs its own review"
    );
    assert!(exact.1 > 0 && disc.1 > 0, "both must still be proved: {exact:?} {disc:?}");

    // Recorded, not celebrated: the tautology IS kernel-certified, because it
    // carries no arithmetic and so never enters the declared-width lane at all.
    assert_eq!(taut.2, 1, "the tautology's Int-lane row is kernel-certified");
}

// ---------------------------------------------------------------------------
// 6. ATTRIBUTION. A clause reaches vcgen in three carriers, and since
//    `3539149e06` the FORMULA carrier is checked rather than stripped. These pin
//    that no false clause proves through any one of them, and that a proof of a
//    DIFFERENT clause riding in another carrier is never credited to it.
// ---------------------------------------------------------------------------

/// Every vacuity-table clause that must NOT prove, including the one that was
/// reported as proved on 2026-09-26 (`var.0 == var.0 * 2`).
const MUST_NOT_PROVE: &[&str] = &[
    "false",
    "(result.0) == (((var.0) * (2)) + (1))",
    "(var.0) == ((var.0) * (2))",
    "(result.0) == ((var.0) * (3))",
    "(result.0) != ((var.0) * (2))",
];

fn raw_postcondition_rows(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

/// [`with_clause`] rebuilds by the compiler's rule, not by a guess at it: its
/// rebuild of the MUTANT clause over the positive capture states exactly what
/// the compiler itself extracted for that clause
/// (`newtype_struct_return_positive_mutant`), in every carrier.
#[test]
fn with_clause_reproduces_the_compilers_own_capture() {
    let rebuilt =
        with_clause("newtype_struct_return_positive", "(result.0) == (((var.0) * (2)) + (1))");
    let captured = load("newtype_struct_return_positive_mutant");
    assert_carriers_agree(&captured, "newtype_struct_return_positive_mutant");
    let bodies = |f: &VerifiableFunction| {
        f.contracts.iter().map(|c| (c.kind, c.body.clone())).collect::<Vec<_>>()
    };
    assert_eq!(bodies(&rebuilt), bodies(&captured), "contracts carrier");
    assert_eq!(rebuilt.postconditions, captured.postconditions, "formula carrier");
    assert_eq!(rebuilt.spec.ensures, captured.spec.ensures, "spec carrier");
}

/// Each false clause, through every carrier configuration a real function can
/// arrive in: all three agreeing (what extraction writes), the FORMULA carrier
/// alone (the lane `3539149e06` opened: `inferred_return_check_vcs` and public
/// synthetic producers populate only `postconditions`), and the SOURCE carriers
/// alone. None may prove. The formula-only lane is the one to watch: it is
/// admitted through `machine_faithful_clause_admissible`, so its row must be the
/// declared-width reading and must refute (or fall closed) exactly as the
/// source-carried row does.
///
/// This is a PIN, not a born-red control, and it says so: on the real code it
/// passes, and the Int-reading defect it would most naturally guard against
/// should not flip these clauses, each being false over `Int` too (reasoned, not
/// measured). The born-red control
/// for the formula-only lane's Int reading is `3539149e06`'s own
/// `result + 1 > result` pin in `contracts.rs`; the born-red control for the
/// failure actually reported here is the attribution test below.
#[test]
fn the_false_clauses_prove_through_no_carrier() {
    let mut bad = Vec::new();
    for clause in MUST_NOT_PROVE {
        let coherent = with_clause("newtype_struct_return_positive", clause);
        let mut formula_only = coherent.clone();
        formula_only.contracts.clear();
        formula_only.spec.ensures.clear();
        let mut source_only = coherent.clone();
        source_only.postconditions.clear();
        for (carrier, func) in [
            ("all three", &coherent),
            ("formula only", &formula_only),
            ("source only", &source_only),
        ] {
            let rows = raw_postcondition_rows(func);
            if all_proved(&rows) {
                bad.push(format!("{clause} via {carrier}: {:?}", verdicts(&rows)));
            }
        }
    }
    assert!(bad.is_empty(), "a false postcondition was proved: {bad:#?}");
}

/// THE CONFIGURATION THAT WAS READ AS A FALSE PROOF, built on purpose: the false
/// clause in `contracts`, the ORIGINAL true clause (`result.0 == var.0 * 2`)
/// still in `postconditions` and `spec.ensures`. The true clause's row may
/// prove — it is true of this body — but its proof must never be ATTRIBUTED to
/// the false clause, and the false clause's own row must not prove.
///
/// Attribution is `source_contract_index`, the field the compiler requires
/// before a solved row may discharge a source-clause marker; nothing downstream
/// re-derives it, so a vcgen that credited this row to clause 0 would turn a
/// true proof into a verified FALSE contract. MEASURED both ways on 2026-09-26:
/// with `unique_source_contract_index_for_formula` planted to credit the sole
/// `Ensures` regardless of formula, this test FAILS on every clause below, while
/// every other test in this file (the rebuilt [`with_clause`] states one clause
/// in all carriers, so no second row exists) still passes; on the real code it
/// passes.
#[test]
fn a_true_clause_in_another_carrier_is_never_credited_to_a_false_one() {
    let mut bad = Vec::new();
    for clause in MUST_NOT_PROVE {
        let mut func = load("newtype_struct_return_positive");
        func.contracts[0].body = format!("{LOWERED}{clause}");
        let rows = raw_postcondition_rows(&func);
        let outcomes = verdicts(&rows);
        // NON-VACUITY: the stale true clause must actually be checked and proved
        // here, or this test is not exercising the conflation at all.
        assert!(
            outcomes.iter().any(|r| matches!(r, VerificationResult::Proved { .. })),
            "{clause}: the stale TRUE clause must still prove, or this test discriminates \
             nothing: {outcomes:?}"
        );
        for (vc, outcome) in rows.iter().zip(&outcomes) {
            if matches!(outcome, VerificationResult::Proved { .. }) && source_index(vc) == Some(0) {
                bad.push(format!("{clause}: a proved row is credited to it: {:?}", vc.formula));
            }
        }
    }
    assert!(bad.is_empty(), "a false postcondition was credited with a proof: {bad:#?}");
}
