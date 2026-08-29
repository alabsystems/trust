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

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");

fn load(name: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(format!("{FIXTURES}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The lowered-contract marker the compiler stamps on a contract body; a clause
/// swapped in below has to carry it or `contracts.rs` treats the text as a raw
/// unparseable spec closure.
const LOWERED: &str = "__trust_lowered_compiler_contract__:";

/// The same real MIR body with ONE clause replaced. The body, the locals, the
/// aggregate return and every guard stay byte-identical, so a difference in
/// outcome between two rows of the vacuity table below is a difference in the
/// PREDICATE and in nothing else.
fn with_clause(name: &str, clause: &str) -> VerifiableFunction {
    let mut func = load(name);
    assert_eq!(func.contracts.len(), 1, "fixture must carry exactly one clause");
    func.contracts[0].body = format!("{LOWERED}{clause}");
    func
}

fn postcondition_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

/// The visible fail-closed rows: a clause that cannot be modelled must produce
/// one of these instead of a verdict.
fn unsupported_details(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "SpecUnverifiable" => {
                Some(detail)
            }
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
    let router = trust_router::Router::deterministic_in_process_ay(30_000);
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
    !vcs.is_empty()
        && verdicts(vcs).iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
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
///   tuple_ensures_duplicate         `ret.0 == ret.1`   proved 1  certified 1
///   tuple_return_field_arithmetic   `ret.0 == x + 1`   proved 1  certified 0   <- CONTROL
///   newtype_struct_return_positive  `ret.0 == var.0*2` proved 1  certified 0
///   newtype_struct_return_positive  `ret.0 == ret.0`   proved 1  certified 1
///   newtype_struct_return_positive  `1 == 1`           proved 1  certified 1
/// ```
///
/// The kernel certifies the Int-lane rows — INCLUDING the tautologies — and
/// does NOT certify the declared-width QF_BV rows this lane produces. Under
/// `-Ztrust-policy=certify` an ay `Proved` with no kernel token is reported
/// `Unknown`, so every exact relation here would read `Unknown` there while
/// `ensures result.0 == result.0` would read CERTIFIED. That is a real and
/// uncomfortable property of the Machine{w} lane and it is worth headlining.
///
/// It is NOT introduced here. `tuple_return_field_arithmetic_control` is the
/// same shape on a TUPLE return, which proved on the sealed toolchain before
/// this change and is bit-for-bit unaffected by it; it is `certified 0` with
/// the change applied and `certified 0` with it reverted. This test pins that
/// equality, so a future change that starts minting kernel authority for
/// declared-width rows has to come here and say so.
#[test]
fn kernel_certification_matches_the_untouched_control() {
    let measure = |fixture: &str, clause: Option<&str>| -> (usize, usize, usize) {
        let func = match clause {
            Some(c) => with_clause(fixture, c),
            None => load(fixture),
        };
        let posts = postcondition_vcs(&func);
        let proved = verdicts(&posts)
            .iter()
            .filter(|r| matches!(r, VerificationResult::Proved { .. }))
            .count();
        let certified =
            posts.iter().filter(|vc| trust_certify::certify_vc(vc).is_some()).count();
        (posts.len(), proved, certified)
    };

    let control = measure("tuple_return_field_arithmetic_control", None);
    let exact = measure("newtype_struct_return_positive", None);
    let disc = measure("newtype_struct_return_positive", Some("(result.0) != (((var.0) * (2)) + (1))"));
    let taut = measure("newtype_struct_return_positive", Some("(result.0) == (result.0)"));
    let mutant = measure("newtype_struct_return_positive", Some("(result.0) == (((var.0) * (2)) + (1))"));
    eprintln!(
        "kernel door (rows, proved, certified):\n  CONTROL tuple+arith {control:?}\n  \
         exact {exact:?}\n  discriminator {disc:?}\n  tautology {taut:?}\n  mutant {mutant:?}"
    );

    assert_eq!(mutant.1, 0, "a false postcondition must never be proved");
    assert_eq!(mutant.2, 0, "a false postcondition must never be kernel-certified");

    // The control is the pre-existing declared-width postcondition lane. This
    // change must put its new rows in exactly the same certification class,
    // never a stronger one.
    assert_eq!(
        (control.1 > 0, control.2),
        (true, 0),
        "control: a declared-width postcondition proves and is NOT kernel-certified"
    );
    assert_eq!(
        (exact.2, disc.2),
        (control.2, control.2),
        "this lane's declared-width rows must certify exactly as the untouched control does; \
         a NEW kernel-certified class would need its own review"
    );
    assert!(exact.1 > 0 && disc.1 > 0, "both must still be proved: {exact:?} {disc:?}");

    // Recorded, not celebrated: the tautology IS kernel-certified, because it
    // carries no arithmetic and so never enters the declared-width lane at all.
    // Same before this change as after.
    assert_eq!(taut.2, 1, "the tautology's Int-lane row is kernel-certified");
}
