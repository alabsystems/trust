// Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the safety-VC adequacy certifier
// must read each VC's OWN emitted violation, at every kind, not the first hypothesis
// conjunct of the wrapped formula that happens to share its shape.
//
// `f1e45ccb0fe` fixed exactly one of the eight sites (`ShiftOverflow`), and fixed it by
// SHAPE alone — it matched the emitter's own construction but still searched the whole
// `vc.formula` for it. This module pins all eight. The mechanism is identical at every
// one: `vc.formula` is the violation WRAPPED in block definitions, dominating guards,
// the function's `preconditions` and its parameters' type bounds, and a scan of that
// whole tree reads a hypothesis. `emitted_obligation_body` inverts the wrapping;
// (`obligation_violation_leaf` then searched INSIDE the recovered body; round 6 DELETED
// it — see section 12 and `locate_violation`, which shape-matches the COLLAPSED body.)
//
// Every test here FAILS on the tree that precedes ITS OWN fix, verified by reverting and
// re-running — never by argument. Sections 0-5 fail on the pre-`f1e45ccb0fe`+region-fix
// tree (the whole-formula scan). Sections 6-7, and
// `no_site_certifies_through_a_negation_or_an_implication_hypothesis`, fail on the
// REGION-FIXED tree: they pin the four defects the adversarial re-review found still
// live in it — the mixed path-guard `Or`, the `Not` and `Implies` polarity lanes, and
// the assert binding that was not resolved through the MIR. The `shift-amount OOB` row
// of `site_hypotheses()` and section 8 fail on the ROUND-2 tree: they pin the eighth
// site's surviving whole-formula scan and the four widths read from the formula with no
// cross-check against the width the VC's own kind carries.
//
// Trust: SECTION 11 (2026-07-31, round 5) pins the three defects this lane had NO
// defence for — the negation SUBJECT, the dropped signed bounds disjunct, and the uadd
// vacuity side condition. Each of its three tests was falsified by reverting its own fix
// IN PLACE and re-running; the observed pre-fix mints are quoted in each test's doc.
//
// Trust: SECTION 12 (2026-07-31, round 6) pins the ROOT CAUSE all of the above kept
// re-opening: `is_core` must be applied to the COLLAPSED peeled body, never to a leaf
// found by descending it. trust-ir has done that lane-wide since round 5
// (`locate_violation`); mirsem did it only inside the unsigned-add arm, and the other six
// arms minted `Or([<that arm's own core>, Gt(decoy, 5)])`. Its four tests are falsified
// the same way, and the pre-fix mints are quoted per test.
//
// THE COST MEASUREMENTS quoted in `vc_faithful.rs` are taken by `mirsem_corpus_census`
// at the foot of this module — an `#[ignore]`d harness (it takes ~250 s) that walks every
// committed dump under `crates/trust-clean/fixtures` and ASSERTS the recorded tallies.
// PRE round-5, POST round-5 and POST round-6 are identical at `certs=635 fn_certified=286`
// over `safety=772`.

use super::*;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, UnOp, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

const LADDER: [&str; 2] = ["fixtures/census-2026-07-06", "fixtures/census-rung2-2026-07-07"];

/// Load a committed fixture. NO `Err(_) => return`: a rename must FAIL the test, never
/// silence it (the vacuous-test pattern `reports/2026-07-29-ladder-fixture-refreeze.md`
/// §0 records).
fn load(rel: &str) -> VerifiableFunction {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("fixture missing — {}: {e}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {rel}: {e}"))
}

fn ladder_fixtures() -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    for corpus in LADDER {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(corpus);
        let rd = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("ladder corpus missing — {}: {e}", dir.display()));
        for crate_dir in rd.flatten() {
            if !crate_dir.path().is_dir() {
                continue;
            }
            for f in std::fs::read_dir(crate_dir.path()).into_iter().flatten().flatten() {
                if f.path().extension().is_some_and(|e| e == "json") {
                    out.push(f.path());
                }
            }
        }
    }
    assert!(out.len() > 400, "the ladder corpus is 450 dumps, found {}", out.len());
    out.sort();
    out
}

fn var(n: &str) -> Formula {
    Formula::Var(n.into(), Sort::Int)
}

/// Trust: THE AUTHENTICATED-PATH TEST ADAPTER (2026-08-01, FIELD-REQUIRED). Every safety
/// arm now REQUIRES an authenticated obligation (the peel is deleted), so a hand-built VC
/// whose `formula` IS the emitter's raw violation body carries a record whose `body` is
/// exactly that formula and whose wrapper list is empty — `reconstruct_obligation(rec) ==
/// formula` holds trivially, so the arm reads `body` and behaves EXACTLY as the deleted
/// peel did on an unwrapped formula. This preserves each pinned property (a decoy body
/// still fails `is_core`; a bare core still certifies) while routing it through the field
/// authentication rather than the peel. Tests that pin a WRAPPED body (operand ranges as
/// `ConjoinFactsLast` — the uadd/umul vacuity tests) build their records explicitly.
fn authed_body(formula: &Formula) -> Option<trust_types::ObligationRecord> {
    Some(trust_types::ObligationRecord {
        body: formula.clone(),
        wrappers: vec![],
        subject: None,
        width: None,
    })
}

/// Trust: the test-side mirror of the production `vc_faithful::authenticated_record` (which
/// is private to the certifier): the emitter's obligation body for a VC, `Some(&body)` iff a
/// record is present AND reconstructs to `vc.formula` bit-for-bit — the same admission gate
/// the live certifier applies before it reads the body. This is the FAITHFUL replacement for
/// the deleted `emitted_obligation_body` peel at the sites that read the certified body: the
/// peel guessed the body out of the wrapped formula; this reads the authenticated field. On
/// this corpus the two agree exactly (measured 2026-08-01), which is why the substitution
/// preserves every assertion.
fn authenticated_obligation_body(vc: &VerificationCondition) -> Option<&Formula> {
    let rec = vc.obligation.as_ref()?;
    (reconstruct_obligation(rec) == vc.formula).then_some(&rec.body)
}

/// Trust: the test-side replacement for the deleted `#[cfg(test)]` `find_violation_leaf`
/// probe — does `f` contain a subterm matching `pred` anywhere? Used ONLY to assert a
/// fixture's own PREMISE (a hypothesis decoy is present in the wrapped formula; a recorded
/// body carries / does not carry a modeled leaf), never to drive the live certifier, which
/// reads the authenticated body directly and never searches the tree.
fn contains_leaf(f: &Formula, pred: &dyn Fn(&Formula) -> bool) -> bool {
    if pred(f) {
        return true;
    }
    match f {
        Formula::And(v) | Formula::Or(v) => v.iter().any(|x| contains_leaf(x, pred)),
        Formula::Not(a) => contains_leaf(a, pred),
        Formula::Implies(a, b) => contains_leaf(a, pred) || contains_leaf(b, pred),
        _ => false,
    }
}

/// The empty body a HAND-BUILT `VerificationCondition` is certified against. The
/// formula-driven routes never read it; the ASSERT-bound route does — and an empty body
/// binds no assert condition local, which is exactly the fail-closed answer for a VC
/// that was not produced from this MIR.
fn probe_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::probe".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Int { width: 32, signed: false },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn certified_kinds(func: &VerifiableFunction) -> Vec<SafetyVcKind> {
    trust_vcgen::generate_vcs(func)
        .iter()
        .filter(|vc| is_safety_vc_kind(&vc.kind))
        .filter_map(|vc| safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k))
        .collect()
}

// ---------------------------------------------------------------------------------
// 0. [REMOVED 2026-08-01] `obligation_body_agrees_with_the_shift_emitter_locator` was a
//    PURE PEEL-MECHANISM cross-check: it asserted the two deleted peel derivations
//    (`emitted_obligation_body` and the `emitted_shift_violation_pair_probe`) agree on the
//    ladder's shift VCs. Both peels are deleted (production authenticates a recorded
//    obligation instead), so there is nothing left to cross-check.
// ---------------------------------------------------------------------------------

// ---------------------------------------------------------------------------------
// 1. THE SITE-WIDE CONTRACT — an obligation with no modeled core is never certified.
// ---------------------------------------------------------------------------------

/// One row per certifying site: `(tag, the VC kind, a hypothesis spelled in THAT site's
/// own probe shape)`. Every row's hypothesis is something a wrapper legitimately puts in
/// `vc.formula` — a `#[requires]`, a dominating guard, a block definition, a parameter
/// type bound — and every one of them is a shape the site's leaf probe accepts. They are
/// the material a region-selection bug turns into a certificate.
fn site_hypotheses() -> Vec<(&'static str, VcKind, Formula)> {
    let u32t = || Ty::Int { width: 32, signed: false };
    let i32t = || Ty::Int { width: 32, signed: true };
    let sum = |a: &str, b: &str| Formula::Add(Box::new(var(a)), Box::new(var(b)));
    let prod = |a: &str, b: &str| Formula::Mul(Box::new(var(a)), Box::new(var(b)));
    let diff = |a: &str, b: &str| Formula::Sub(Box::new(var(a)), Box::new(var(b)));

    vec![
        (
            "bounds / IndexOutOfBounds",
            VcKind::IndexOutOfBounds,
            Formula::Ge(Box::new(var("i")), Box::new(Formula::Int(8))),
        ),
        (
            "bounds / SliceBoundsCheck",
            VcKind::SliceBoundsCheck,
            Formula::Ge(Box::new(var("i")), Box::new(var("n"))),
        ),
        (
            "div-by-zero",
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0))),
        ),
        (
            "rem-by-zero",
            VcKind::RemainderByZero,
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0))),
        ),
        (
            "unsigned-add overflow",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u32t(), u32t()) },
            Formula::Gt(Box::new(sum("p", "q")), Box::new(Formula::Int(255))),
        ),
        (
            "unsigned-sub underflow",
            VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (u32t(), u32t()) },
            Formula::Lt(Box::new(diff("p", "q")), Box::new(Formula::Int(0))),
        ),
        (
            "unsigned-mul overflow",
            VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (u32t(), u32t()) },
            Formula::Gt(Box::new(prod("p", "q")), Box::new(Formula::Int(4294967295))),
        ),
        (
            "signed add overflow",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (i32t(), i32t()) },
            Formula::Or(vec![
                Formula::Lt(Box::new(sum("p", "q")), Box::new(Formula::Int(-128))),
                Formula::Gt(Box::new(sum("p", "q")), Box::new(Formula::Int(127))),
            ]),
        ),
        (
            "negation overflow",
            VcKind::NegationOverflow { ty: i32t() },
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-128))),
        ),
        // Trust: lane A round-3 finding [1] (2026-07-29) — the EIGHTH site. It was
        // missing from this table, and it was the one site still running its locator
        // over the whole `vc.formula`, so neither of the two site-wide tests below
        // covered the only remaining forgery. Its probe shape is not a leaf: it is
        // `v2_shift_violation_formula`'s VERBATIM emitted pair
        // `And([input_range_constraint(n, u32), Ge(n, 32)])`, which is exactly what a
        // hypothesis conjunct would have to look like to be selected — and a
        // `#[requires]` may contain it, because it is an ordinary proposition.
        (
            "shift-amount OOB",
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: u32t(),
                shift_ty: u32t(),
            },
            Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(Box::new(Formula::Int(0)), Box::new(var("n"))),
                    Formula::Le(Box::new(var("n")), Box::new(Formula::Int(4294967295))),
                ]),
                Formula::Ge(Box::new(var("n")), Box::new(Formula::Int(32))),
            ]),
        ),
    ]
}

/// A safety VC whose own emitted violation is the fail-closed marker `Bool(true)` — a
/// shape the emitter really produces (`lib__check_ascii_printable`'s `SliceBoundsCheck`
/// obligation IS `Bool(true)`) — must be certified by NO site, whatever the wrapper
/// carries. Each row wraps that marker in exactly one hypothesis conjunct spelled in the
/// site's own probe shape, which is what the wrapper legitimately contains: a
/// `#[requires]`, a dominating guard, or a block definition.
///
/// This is the uniform statement of the defect. It is the load-bearing test for the
/// three payload-free kinds (`Bounds`, `DivByZero`, `RemByZero`), where a forged leaf is
/// invisible in the certificate's own value: the harm there is not a wrong width, it is
/// that an obligation nothing modeled was declared faithfully modeled.
///
/// PRE-FIX: every row certifies (the seven region-fixed sites on the pre-region tree;
/// the `shift-amount OOB` row on the round-2 tree, MEASURED -> `ShiftOob(W32, false)`).
/// POST-FIX: none do.
#[test]
fn no_site_certifies_an_obligation_whose_own_body_has_no_modeled_core() {
    let mut forged: Vec<String> = Vec::new();
    for (tag, kind, hypothesis) in site_hypotheses() {
        // The emitter's own fail-closed obligation marker, wrapped exactly the way every
        // conjoining wrapper wraps: hypotheses first, obligation LAST.
        let vc = VerificationCondition {
            kind,
            function: "crate::probe".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![hypothesis.clone(), Formula::Bool(true)]),
            contract_metadata: None,
            obligation: None,
        };
        if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&probe_func(), &vc) {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "kernel-checked adequacy certificates were minted for obligations whose own \
         violation is the fail-closed marker `Bool(true)`; the core was read off the \
         hypothesis conjunct: {forged:#?}"
    );
}

/// POLARITY (lane A findings [2] and [3]). The same rows, but the obligation is
/// wrapped in the two connectives that are NOT positive positions:
///
///   * `Not(And([hypothesis, Bool(true)]))` — the violation is the COMPLEMENT of what is
///     inside. `emitted_obligation_body` has no `Not` arm (correctly: no wrapper adds
///     one, so the `Not` IS part of the body), but the locator of the day
///     (`obligation_violation_leaf`, deleted in round 6) used to
///     descend THROUGH it and certify a leaf whose polarity is the opposite of the
///     obligation's. The assert route already refuses exactly this (`Not(Var c)` is not
///     admitted); the generic site did not.
///   * `Implies(hypothesis, Bool(true))` — the antecedent is a hypothesis in the most
///     literal sense. `alias_analysis::refine_vc_with_alias` (`:381`) builds this shape
///     over an arbitrary VC; it is `pub`, re-exported, and not currently called from
///     `generate_vcs` — so this row is the guard that wiring it in cannot open a
///     forgery lane.
///
/// PRE-FIX both wrappings certify (MEASURED: `Not(And([Ge(i,8), Bool(true)]))` and
/// `Implies(Ge(i,8), Bool(true))` each -> `Some(Bounds)`; and on the ROUND-2 tree, where
/// the seven region-fixed sites already declined, the `shift-amount OOB` row still
/// certified both wrappings -> `Some(ShiftOob(W32, false))`, because
/// `emitted_shift_violation` was the last locator in the file still descending through
/// `Not` and `Implies`). POST-FIX neither does, at any row.
#[test]
fn no_site_certifies_through_a_negation_or_an_implication_hypothesis() {
    let mut forged: Vec<String> = Vec::new();
    for (tag, kind, hypothesis) in site_hypotheses() {
        let wrappings: [(&str, Formula); 2] = [
            (
                "Not(And([hypothesis, body]))",
                Formula::Not(Box::new(Formula::And(vec![
                    hypothesis.clone(),
                    Formula::Bool(true),
                ]))),
            ),
            (
                "Implies(hypothesis, body)",
                Formula::Implies(Box::new(hypothesis.clone()), Box::new(Formula::Bool(true))),
            ),
        ];
        for (shape, formula) in wrappings {
            let vc = VerificationCondition {
                kind: kind.clone(),
                function: "crate::probe".into(),
                location: SourceSpan::default(),
                formula,
                contract_metadata: None,
                obligation: None,
            };
            if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&probe_func(), &vc) {
                forged.push(format!("{tag} / {shape} -> {k:?}"));
            }
        }
    }
    assert!(
        forged.is_empty(),
        "a core was certified from a NEGATED or IMPLIED position — the certificate \
         claims the complement of the obligation, or its hypothesis: {forged:#?}"
    );
}

// ---------------------------------------------------------------------------------
// 2. BOUNDS — the largest exposure, on unmodified library code with no hostile input.
// ---------------------------------------------------------------------------------

/// `byteorder`'s `read_u32`/`read_u64`/`write_u16` raise a `SliceBoundsCheck` whose OWN
/// violation is the container-length shape (`Gt(Int(4), buf__slice_len)`), which Lemma 3
/// does NOT model (`idx_oob len i` is `Ge(i, len)`).
///
/// These fixtures carry NO contract at all — `preconditions` is empty. The forged leaf is
/// `Ge(buf__slice_len, Int 0)`, the slice-LENGTH type invariant that
/// `type_ranges::conjoin_slice_len_bounds` conjoins ahead of the body onto every bounds
/// VC in the function (`type_ranges.rs:397`). The whole-tree scan selected it and
/// certified `idx_oob 0 buf__slice_len` — a kernel-checked claim that a length is out of
/// bounds of a length-0 collection, about a collection this VC does not mention. The
/// `byteorder` family alone accounts for 24 of the 28 bounds certificates the fix drops.
/// Nothing about it is user-controlled: an unannotated slice function is enough.
#[test]
fn a_slice_length_type_bound_can_never_supply_a_bounds_core() {
    for (name, contract_free) in [
        // `read_*` take only `&[u8]`: NO contract at all, so the forged leaf can only be
        // the slice-length type bound.
        ("<lib__BigEndian as lib__ByteOrder>__read_u32.json", true),
        ("<lib__LittleEndian as lib__ByteOrder>__read_u64.json", true),
        // `write_u16` also takes an integer `n`, so it additionally carries the
        // extractor's `Ge(n, 0)` parameter-domain precondition — the other `Ge`-spelled
        // hypothesis source. Both certify the same forged `idx_oob`.
        ("<lib__BigEndian as lib__ByteOrder>__write_u16.json", false),
    ] {
        let func = load(&format!("fixtures/census-2026-07-06/byteorder/{name}"));
        if contract_free {
            assert!(
                func.preconditions.is_empty(),
                "{name}: this row is evidence that NO contract is needed; it now has one"
            );
        }

        let vcs = trust_vcgen::generate_vcs(&func);
        let bounds: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
            })
            .collect();
        assert!(!bounds.is_empty(), "{name} must raise a bounds VC");
        let is_bounds_probe = |f: &Formula| {
            matches!(f, Formula::Ge(a, b)
                if formula_var_name(a).is_some()
                    && (formula_var_name(b).is_some() || matches!(&**b, Formula::Int(_))))
        };
        for vc in bounds {
            // The VC carries NO authenticated modeled `Ge(i, len)` core: either no record
            // (these container-length slice-range VCs record `obligation: None`) or a record
            // whose body is not the modeled shape. Read through the SAME admission gate the
            // live certifier uses (reconstruct-and-equate), never a peel of the formula.
            assert!(
                authenticated_obligation_body(vc).is_none_or(|b| !is_bounds_probe(b)),
                "{name}: this test needs a bounds VC OUTSIDE the modeled shape; got an \
                 authenticated modeled core {:?}",
                authenticated_obligation_body(vc)
            );
            // … but the WRAPPED formula still carries a `Ge`-shaped hypothesis (the
            // slice-length type bound) — the leaf the pre-authentication whole-formula scan
            // used to read. Asserted so the fixture drifting away from the collision this
            // test pins fails loudly rather than passing vacuously.
            assert!(
                contains_leaf(&vc.formula, &is_bounds_probe),
                "{name}: the wrapper no longer carries a `Ge`-shaped hypothesis, so the \
                 collision this test exists to pin is gone — re-derive it before \
                 weakening the assertion"
            );
            // … so the certifier must decline, not read one off the hypothesis side.
            assert_eq!(
                safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k),
                None,
                "{name}: a bounds adequacy certificate was minted for an obligation whose \
                 own violation has no modeled core — it was read off the slice-length \
                 type bound"
            );
        }
        // And the whole-function gate follows: these rows lose FULLY_FAITHFUL, which is
        // the honest verdict for a function whose bounds obligation nothing models.
        assert!(
            function_safety_vcs_faithful(&func).is_none(),
            "{name}: the function gate still passes on a forged bounds certificate"
        );
    }
}

// ---------------------------------------------------------------------------------
// 3. UNSIGNED ADD — a WIDTH forgery on unmodified real library code.
// ---------------------------------------------------------------------------------

/// `itoa`'s `<T as Sealed>::write` raises an 8-bit add-overflow VC whose OWN violation
/// is `Gt(_63 + 48, 255)`. The whole-tree scan reached the semantic assert-passed guard
/// `Gt(_43 + 2, 18446744073709551615)` first and minted `Overflow(U64)` — a
/// kernel-checked adequacy certificate that this obligation is a 64-bit addition
/// overflow. All eight `Sealed::write` rows in the ladder carry it, on the committed
/// dump, with no injected contract.
#[test]
fn an_unsigned_add_certifies_its_own_width_not_a_semantic_guard() {
    for ty in ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"] {
        let func = load(&format!(
            "fixtures/census-2026-07-06/itoa/lib__<impl lib__private__Sealed for {ty}>__write.json"
        ));
        let mut checked = 0usize;
        for vc in &trust_vcgen::generate_vcs(&func) {
            let VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (a, b) } = &vc.kind
            else {
                continue;
            };
            if !matches!(a, Ty::Int { signed: false, .. })
                || !matches!(b, Ty::Int { signed: false, .. })
            {
                continue;
            }
            // Read the emitter's authenticated obligation body (reconstruct-and-equate),
            // exactly as the live certifier does — not a peel of the wrapped formula.
            let body = authenticated_obligation_body(vc).expect("the itoa add VC records its \
                obligation, authenticating against `vc.formula`");
            // Only the rows whose own threshold is the u8 MAX are the mis-certified ones.
            let emits_u8 = contains_leaf(body, &|f| {
                matches!(f, Formula::Gt(_, r) if matches!(&**r, Formula::Int(255)))
            });
            if !emits_u8 {
                continue;
            }
            checked += 1;
            assert_eq!(
                safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k),
                Some(SafetyVcKind::Overflow(UWidth::W8)),
                "{ty}: this obligation's own threshold is 255 (u8); a W64 certificate is \
                 read off the `Gt(_43 + 2, u64::MAX)` semantic guard"
            );
        }
        assert!(checked >= 1, "{ty}: no u8-threshold add obligation found — the test\n             measures nothing");
    }
}

// ---------------------------------------------------------------------------------
// 4. The real-emitter hostile-contract exploits, where the certificate's own payload
//    makes the forgery visible.
// ---------------------------------------------------------------------------------

fn binop_func(name: &str, width: u32, signed: bool, op: BinOp) -> VerifiableFunction {
    let t = || Ty::Int { width, signed };
    VerifiableFunction {
        name: name.into(),
        def_path: format!("crate::{name}").into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: t(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: t(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn neg_func(width: u32) -> VerifiableFunction {
    named_neg_func("x", width)
}

/// `fn neg(<name>: i<width>) -> i<width> { -<name> }` — the MIR a hand-built negation
/// core is HONEST against.
///
/// Trust: THE PROBE MIR MUST NEGATE THE CERTIFIED VARIABLE (2026-07-31, round-5 defect
/// [1]). The negation arm now cross-checks the certified variable against the operands
/// this function's MIR actually negates, and reads the certified width from THAT
/// operand's type. `probe_func()` has no blocks at all, so every hand-built negation row
/// probed against it declines on the SUBJECT — which would silently turn the width and
/// wrapper controls below into vacuous "it declines" rows. They are re-pointed at this
/// function instead of being relaxed: the assertions are unchanged, the MIR they are
/// asserted against is now one where the row's own core is the honest obligation.
fn named_neg_func(name: &str, width: u32) -> VerifiableFunction {
    let t = || Ty::Int { width, signed: true };
    VerifiableFunction {
        name: "neg".into(),
        def_path: "crate::neg".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: t(), name: Some(name.into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// SIGNED ADD/SUB/MUL (Lemma 5). The certified `SWidth` is read from the located
/// `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])`'s literals, so a `#[requires]` spelling that
/// disjunction at a NARROWER width mints a certificate for a width the i32 obligation
/// does not contain.
#[test]
fn a_precondition_can_never_supply_the_certified_signed_width() {
    let base = binop_func("sadd", 32, true, BinOp::Add);
    let honest = certified_kinds(&base);
    assert!(
        honest.contains(&SafetyVcKind::SignedOverflow(SignedOp::Add, SWidth::W32)),
        "the bare i32 add must certify at W32, got {honest:?}"
    );

    let sum = |a: &str, b: &str| Formula::Add(Box::new(var(a)), Box::new(var(b)));
    for (tag, pre) in [
        (
            "the i8 out-of-range disjunction over the SAME operands",
            Formula::Or(vec![
                Formula::Lt(Box::new(sum("a", "b")), Box::new(Formula::Int(-128))),
                Formula::Gt(Box::new(sum("a", "b")), Box::new(Formula::Int(127))),
            ]),
        ),
        (
            "the i16 disjunction over operands the body never adds",
            Formula::Or(vec![
                Formula::Lt(Box::new(sum("p", "q")), Box::new(Formula::Int(-32768))),
                Formula::Gt(Box::new(sum("p", "q")), Box::new(Formula::Int(32767))),
            ]),
        ),
    ] {
        let mut hostile = base.clone();
        hostile.preconditions = vec![pre];
        let minted = certified_kinds(&hostile);
        assert_eq!(
            minted, honest,
            "{tag}: minted {minted:?} — a hypothesis conjunct was certified in place of \
             the emitted violation core"
        );
    }
}

/// UNSIGNED-MUL. A `var*var` mul is emitted as a BITVECTOR obligation that carries no
/// `Gt(Mul(a,b), MAX)` leaf at all, and MUST stay fail-closed (the `mul_*`/`sq_nonneg`
/// corpus's honest not-faithful). A `#[requires]` supplying that leaf minted
/// `UnsignedMulOverflow` for an obligation the bridge never inspected.
#[test]
fn a_precondition_can_never_certify_the_deferred_bitvector_mul() {
    let base = binop_func("umul", 32, false, BinOp::Mul);
    assert!(
        !certified_kinds(&base)
            .iter()
            .any(|k| matches!(k, SafetyVcKind::UnsignedMulOverflow(_))),
        "a bare `a * b` u32 mul is emitted in BITVECTOR form and must stay fail-closed"
    );

    let mut hostile = base.clone();
    hostile.preconditions = vec![Formula::Gt(
        Box::new(Formula::Mul(Box::new(var("a")), Box::new(var("b")))),
        Box::new(Formula::Int(4294967295)),
    )];
    assert!(
        !certified_kinds(&hostile)
            .iter()
            .any(|k| matches!(k, SafetyVcKind::UnsignedMulOverflow(_))),
        "a `#[requires] a * b > u32::MAX` minted an adequacy certificate for a bitvector \
         obligation whose own formula has no such leaf"
    );
}

/// NEGATION (Lemma 6). The old `find_violation_leaf_through_eq` descended into the
/// operands of EVERY `Eq` in the formula — every block definition and any `Eq`-shaped
/// precondition — and `swidth_of_signed_min` read the certified width off whatever it
/// found first. A `#[requires] y == -128` on an i32 negation mints
/// `NegationOverflow(W8)`: a claim that this obligation is an 8-bit negation overflow,
/// over a variable the body never negates.
#[test]
fn a_precondition_can_never_supply_the_certified_negation_width() {
    let base = neg_func(32);
    let honest = certified_kinds(&base);
    assert!(
        honest.contains(&SafetyVcKind::NegationOverflow(SWidth::W32)),
        "the bare i32 negation must certify at W32, got {honest:?}"
    );

    for (tag, pre) in [
        ("i8::MIN over an unrelated variable", (-128i128, "y")),
        ("i16::MIN over an unrelated variable", (-32768i128, "y")),
        ("i8::MIN over the negated variable itself", (-128i128, "x")),
    ]
    .map(|(t, (m, v))| (t, Formula::Eq(Box::new(var(v)), Box::new(Formula::Int(m)))))
    {
        let mut hostile = base.clone();
        hostile.preconditions = vec![pre];
        let minted = certified_kinds(&hostile);
        assert_eq!(
            minted, honest,
            "{tag}: minted {minted:?} — a precondition supplied the certified negation width"
        );
    }
}

/// The same for a BLOCK DEFINITION, which needs no contract at all — the widening the
/// old `find_violation_leaf_through_eq` specifically opened. Block definitions ARE
/// emitted as `Eq(local, rvalue)` equalities, so descending into `Eq` operands makes
/// every `let m: i8 = i8::MIN;` in the function a candidate negation core.
///
/// `combine_relevant_block_defs` prunes a definition that shares no variable with the
/// obligation, so the def must be made RELEVANT for the leak to reach the formula. Both
/// variants are pinned:
///
///   * IRRELEVANT (`let m: i8 = -128; -x`) — pruned before the scan sees it; this one
///     was never exploitable, and it passes on the pre-fix tree too.
///   * RELEVANT (`let m: i8 = -128; let w = m as i32; -(x + w)`) — `Eq(m, Int(-128))` is
///     transitively connected to the negated value and IS conjoined, ahead of the body.
///     The `Eq`-descending scan takes it and mints `NegationOverflow(W8)` for an i32
///     negation. This one FAILS on the pre-fix tree.
#[test]
fn a_block_definition_can_never_supply_the_certified_negation_width() {
    let i32t = || Ty::Int { width: 32, signed: true };
    let i8t = || Ty::Int { width: 8, signed: true };

    // (a) IRRELEVANT: `fn f(x: i32) -> i32 { let m: i8 = -128; -x }`
    let irrelevant = VerifiableFunction {
        name: "neg_with_min_literal".into(),
        def_path: "crate::neg_with_min_literal".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32t(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: i8t(), name: Some("m".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-128))),
                        span: Default::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: Default::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: i32t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // (b) RELEVANT: `fn g(x: i32) -> i32 { let m: i8 = -128; let w = m as i32;
    //                                      let y = x + w; -y }`
    let relevant = VerifiableFunction {
        name: "neg_with_relevant_min_literal".into(),
        def_path: "crate::neg_with_relevant_min_literal".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32t(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: i8t(), name: Some("m".into()) },
                LocalDecl { index: 3, ty: i32t(), name: Some("w".into()) },
                LocalDecl { index: 4, ty: i32t(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-128))),
                        span: Default::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(2)), i32t()),
                        span: Default::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: Default::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(4))),
                        span: Default::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: i32t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    for (tag, func) in [("irrelevant def", irrelevant), ("relevant def", relevant)] {
        let minted = certified_kinds(&func);
        assert!(
            !minted.contains(&SafetyVcKind::NegationOverflow(SWidth::W8)),
            "{tag}: a `let m: i8 = -128;` block definition supplied an i8 \
             negation-overflow certificate for an i32 negation: {minted:?}"
        );
    }
}

// ---------------------------------------------------------------------------------
// 5. The ASSERT-BOUND route is not a re-opened fallback.
// ---------------------------------------------------------------------------------

/// The `expected == false` assert shape (`abs`'s negation, `checked_div`'s division)
/// certifies through the block definition that BINDS its own condition local — and
/// through nothing else. A definition whose RHS is not a modeled core must decline even
/// when a perfectly-shaped hypothesis sits in the same formula.
#[test]
fn the_assert_bound_route_reads_only_its_own_condition_local() {
    let u32t = || Ty::Int { width: 32, signed: false };
    // `_3 = b < 1; assert(!_3, "divide by zero")` — the binding RHS is `Lt(b, 1)`, NOT
    // the modeled `Eq(b, 0)`, so the obligation is outside Lemma 4's fragment.
    let mut func = VerifiableFunction {
        name: "odd_div_assert".into(),
        def_path: "crate::odd_div_assert".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u32t(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: u32t(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: false,
                        msg: trust_types::AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: Default::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: u32t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    // A perfectly-shaped hypothesis in the same formula.
    func.preconditions = vec![Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0)))];

    for vc in &trust_vcgen::generate_vcs(&func) {
        if !matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero) {
            continue;
        }
        assert_eq!(
            safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k),
            None,
            "the assert's condition local is bound to `Lt(b, 1)`, not a modeled \
             div-by-zero core — the certificate was read off the `Eq(z, 0)` precondition"
        );
    }
}

// ---------------------------------------------------------------------------------
// 6. THE MIXED PATH-GUARD `Or` — lane A finding [1], the one forgery that survived the
//    first pass, and finding [5], the legitimate row the same defect was costing.
// ---------------------------------------------------------------------------------

/// Does `f` contain an `Or` with BOTH an `And` disjunct and a non-`And` one? That is the
/// shape `v2_formula_with_path_guards` emits for a block reached by one GUARDED and one
/// UNGUARDED path when the body is not itself an `And` (`generate/safety.rs:1079` pushes
/// the raw body for an empty guard list, `:1115` pushes `And([guards.., body..])`), and
/// it is what these two tests must actually be exercising. Asserted explicitly so a
/// change in the emitter turns them into failures rather than into vacuous passes.
fn contains_mixed_or(f: &Formula) -> bool {
    let here = matches!(f, Formula::Or(v)
        if v.iter().any(|d| matches!(d, Formula::And(_)))
            && v.iter().any(|d| !matches!(d, Formula::And(_))));
    here
        || match f {
            Formula::And(v) | Formula::Or(v) => v.iter().any(contains_mixed_or),
            Formula::Not(a) => contains_mixed_or(a),
            Formula::Implies(a, b) => contains_mixed_or(a) || contains_mixed_or(b),
            _ => false,
        }
}

/// A CFG whose successor block is reached by one guarded and one unguarded path. `bb0`'s
/// `Drop` has TWO unguarded successors (its target and its `Cleanup` unwind edge — both
/// are `unguarded_successors`, `trust-types/src/model.rs:6882`); the target then switches
/// on `stmt`'s result into `bb3`, while the cleanup edge reaches `bb3` by a bare `Goto`.
/// `bb3` carries `term`.
fn mixed_path_cfg(
    locals: Vec<LocalDecl>,
    arg_count: usize,
    return_ty: Ty,
    guard_stmt: Statement,
    guard_discr: usize,
    guard_value: u128,
    body: Vec<Statement>,
    term: Terminator,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "mixed_path".into(),
        def_path: "crate::mixed_path".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(3),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Cleanup(BlockId(2)),
                        span: Default::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![guard_stmt],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(guard_discr)),
                        targets: vec![(guard_value, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: Default::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: body, terminator: term },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// THE FORGERY (lane A finding [1]). `bb1` computes `_4 = i >= 8` and switches on it, so
/// the guarded path's term is `And([Ge(i,8), Not(_5)])`; the cleanup path is unguarded,
/// so its term is the RAW body `Not(_5)` — the `expected == true` `BoundsCheck` assert
/// failure, which carries NO modeled bounds core. The peel's old all-`And` test declined
/// to decompose that mixed `Or` and returned it WHOLE, so the leaf search read the
/// dominating guard and minted a kernel-checked `idx_oob 8 i`: an adequacy certificate
/// for a proposition this obligation does not contain.
///
/// Nothing here is hostile — no contract, no crafted formula, just a `Drop` with an
/// unwind edge and an `if i >= 8`. PRE-FIX: `Some(Bounds)`. POST-FIX: `None`.
#[test]
fn a_mixed_path_guard_or_can_never_supply_a_bounds_core() {
    let ut = || Ty::Int { width: 64, signed: false };
    let func = mixed_path_cfg(
        vec![
            LocalDecl { index: 0, ty: ut(), name: Some("_0".into()) },
            LocalDecl { index: 1, ty: ut(), name: Some("i".into()) },
            LocalDecl { index: 2, ty: ut(), name: Some("n".into()) },
            LocalDecl { index: 3, ty: ut(), name: Some("dr".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
            LocalDecl { index: 5, ty: Ty::Bool, name: None },
        ],
        3,
        ut(),
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Ge,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(8, 64)),
            ),
            span: Default::default(),
        },
        4,
        1,
        vec![],
        Terminator::Assert {
            cond: Operand::Copy(Place::local(5)),
            expected: true,
            msg: trust_types::AssertMessage::BoundsCheck,
            target: BlockId(5),
            unwind: trust_types::UnwindEdge::Unreachable,
            span: Default::default(),
        },
    );

    let mut seen = 0usize;
    for vc in &trust_vcgen::generate_vcs(&func) {
        if !matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck) {
            continue;
        }
        seen += 1;
        assert!(
            contains_mixed_or(&vc.formula),
            "this test exists to pin the MIXED path-guard `Or`; the emitter no longer \
             produces one for this CFG, so re-derive the shape before weakening it: {:?}",
            vc.formula
        );
        assert!(
            contains_leaf(&vc.formula, &|f| matches!(f, Formula::Ge(_, r)
                if matches!(&**r, Formula::Int(8)))),
            "the dominating guard `Ge(i, 8)` must still be IN the wrapped formula — it is \
             the leaf the pre-authentication whole-formula scan read"
        );
        assert_eq!(
            safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k),
            None,
            "a bounds adequacy certificate was minted from the DOMINATING GUARD of a \
             mixed path-guard `Or`; this obligation's own violation is the bare assert \
             failure `Not(_5)` and has no modeled core"
        );
    }
    assert_eq!(seen, 1, "the CFG must raise exactly one bounds VC");
}

/// THE LEGITIMATE ROW THE SAME DEFECT WAS COSTING (lane A finding [5]). Identical CFG,
/// but `bb3` really does divide, so the body IS the modeled core `Eq(b, 0)` and the
/// emitted formula is `Or([And([Eq(d,0), Eq(b,0)]), Eq(b,0)])`. The guard `Eq(d, 0)` is
/// spelled in the div site's own probe shape, so with the whole `Or` as the search
/// region the two collide, the singleton rule fires, and the row fails closed — an
/// honest verdict, but a lost capability, because the obligation's own core is right
/// there and identical on every path.
///
/// Decomposing the mixed `Or` dissolves it: both disjuncts peel to the SAME `Eq(b, 0)`,
/// they agree, and the row certifies. PRE-FIX: `None`. POST-FIX: `Some(DivByZero)`.
#[test]
fn a_mixed_path_guard_or_still_certifies_its_own_core() {
    let ut = || Ty::Int { width: 32, signed: false };
    let func = mixed_path_cfg(
        vec![
            LocalDecl { index: 0, ty: ut(), name: Some("_0".into()) },
            LocalDecl { index: 1, ty: ut(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: ut(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: ut(), name: Some("dr".into()) },
            LocalDecl { index: 4, ty: ut(), name: Some("d".into()) },
        ],
        3,
        ut(),
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: Default::default(),
        },
        4,
        0,
        vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: Default::default(),
        }],
        Terminator::Return,
    );

    let mut seen = 0usize;
    for vc in &trust_vcgen::generate_vcs(&func) {
        if !matches!(vc.kind, VcKind::DivisionByZero) {
            continue;
        }
        seen += 1;
        assert!(
            contains_mixed_or(&vc.formula),
            "this test exists to pin the MIXED path-guard `Or`: {:?}",
            vc.formula
        );
        assert_eq!(
            safety_vc_is_faithful_formula_aware(&func, vc).map(|(k, _)| k),
            Some(SafetyVcKind::DivByZero),
            "the obligation's own core `Eq(b, 0)` is present on BOTH paths of the mixed \
             `Or` and is the same formula on each; the row must certify, not fail closed \
             on a collision with the dominating guard"
        );
    }
    assert_eq!(seen, 1, "the CFG must raise exactly one div-by-zero VC");
}

// ---------------------------------------------------------------------------------
// 7. THE ASSERT-BOUND ROUTE IS RESOLVED THROUGH THE MIR — lane A finding [4].
// ---------------------------------------------------------------------------------

/// An `expected == false` `OverflowNeg` assert on local `_3`, with `def` controlling
/// whether the MIR actually BINDS `_3` (`_3 = (x == i32::MIN)`) and `pre` supplying an
/// optional contract.
fn assert_neg_func(def: bool, pre: Option<Formula>) -> VerifiableFunction {
    let i32t = || Ty::Int { width: 32, signed: true };
    let mut stmts = vec![];
    if def {
        stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(-2147483648)),
            ),
            span: Default::default(),
        });
    }
    VerifiableFunction {
        name: "assert_neg".into(),
        def_path: "crate::assert_neg".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32t(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: i32t(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: false,
                        msg: trust_types::AssertMessage::OverflowNeg,
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: Default::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: i32t(),
        },
        contracts: vec![],
        preconditions: pre.into_iter().collect(),
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The assert route's obligation body is the BARE condition local `Var(_3)`, and the core
/// is recovered from the equality that BINDS it. A name-matching scan of `vc.formula`
/// cannot tell that binding from an `Eq`-shaped PRECONDITION over the same name — once
/// `v2_formula_with_path_guards` flattens the wrapper they are the same tree in the same
/// position — and the singleton rule is no defense when the genuine definition is ABSENT.
///
/// So: with NO defining statement, a `#[requires] _3 == (y == -128)` minted
/// `NegationOverflow(W8)` for an **i32** negation, over a variable the body never negates
/// (PRE-FIX, MEASURED). POST-FIX the route requires the MIR to bind the assert's condition
/// local, and to bind it to exactly the comparison the located equality carries.
///
/// The honest twin is asserted in the same test: with the definition present, the row
/// still certifies at W32 — the fix removes the forgery, not the route.
#[test]
fn a_precondition_can_never_bind_an_assert_condition_local_the_mir_does_not_define() {
    let hostile_pre = || {
        Formula::Eq(
            Box::new(Formula::Var("_3".into(), Sort::Bool)),
            Box::new(Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-128)))),
        )
    };

    // (a) HONEST: the MIR binds `_3 = (x == i32::MIN)`; the route certifies at W32.
    let honest = assert_neg_func(true, None);
    assert!(
        certified_kinds(&honest).contains(&SafetyVcKind::NegationOverflow(SWidth::W32)),
        "the assert-bound route must still certify a genuinely-bound condition local — \
         got {:?}",
        certified_kinds(&honest)
    );

    // (b) HOSTILE: the same assert, but NOTHING in the MIR defines `_3`. The only
    //     equality naming it is the contract, and a contract is not a block definition.
    let forged = assert_neg_func(false, Some(hostile_pre()));
    let minted = certified_kinds(&forged);
    assert!(
        !minted.iter().any(|k| matches!(k, SafetyVcKind::NegationOverflow(_))),
        "a `#[requires] _3 == (y == -128)` supplied the certified negation core for an \
         assert whose condition local the MIR never binds: {minted:?}"
    );

    // (c) BOTH: the genuine definition AND the hostile contract. Two DIFFERENT bindings
    //     of the same local ⇒ ambiguity ⇒ fail closed (never the contract's width).
    let both = assert_neg_func(true, Some(hostile_pre()));
    assert!(
        !certified_kinds(&both).contains(&SafetyVcKind::NegationOverflow(SWidth::W8)),
        "the contract's i8 width was certified for an i32 negation: {:?}",
        certified_kinds(&both)
    );
}

// ---------------------------------------------------------------------------------
// 8. THE CERTIFIED WIDTH IS CROSS-CHECKED AGAINST THE VC'S OWN KIND — lane A round-3
//    finding [5].
// ---------------------------------------------------------------------------------

/// Four arms read the certified WIDTH out of a threshold literal in the formula. The
/// VC's `VcKind` carries that width INDEPENDENTLY (`operand_tys` / the negated `ty`), and
/// until this fix nothing compared them — so a formula whose threshold names a different
/// width than the kind minted a kernel-checked adequacy certificate for an arithmetic
/// operation of a width the obligation is not about. The shift arm has had exactly this
/// cross-check for SIGNEDNESS since `f1e45ccb0fe` (`vc_faithful.rs`, `signed_form !=
/// amount_signed`); these four had nothing.
///
/// Each row is an honest-shaped violation body — the emitter's own shape, in the
/// obligation's own position, so every region check introduced above passes it — carrying
/// a threshold from a DIFFERENT width than the kind. PRE-FIX all four certify (MEASURED,
/// in this order: `Overflow(W64)`, `UnsignedMulOverflow(W8)`, `SignedOverflow(Add, W8)`,
/// `NegationOverflow(W8)`). POST-FIX none do.
///
/// The unsigned-SUB arm is the CONTROL and is asserted positively: its width comes from
/// the kind already (`usub_underflow_vc_modeled`), the underflow bound is `0` at every
/// width, and it must keep certifying — otherwise this test would be measuring a blanket
/// decline rather than a width disagreement.
#[test]
fn the_certified_width_must_agree_with_the_vc_kinds_own_width() {
    let u8t = || Ty::Int { width: 8, signed: false };
    let u32t = || Ty::Int { width: 32, signed: false };
    let i32t = || Ty::Int { width: 32, signed: true };
    let sum = |a: &str, b: &str| Formula::Add(Box::new(var(a)), Box::new(var(b)));
    let prod = |a: &str, b: &str| Formula::Mul(Box::new(var(a)), Box::new(var(b)));
    let diff = |a: &str, b: &str| Formula::Sub(Box::new(var(a)), Box::new(var(b)));

    let mismatched: Vec<(&str, VcKind, Formula)> = vec![
        (
            "unsigned add: kind (u8,u8), formula threshold u64::MAX",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u8t(), u8t()) },
            Formula::Gt(Box::new(sum("a", "b")), Box::new(Formula::Int(18446744073709551615))),
        ),
        (
            "unsigned mul: kind (u32,u32), formula threshold u8::MAX",
            VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (u32t(), u32t()) },
            Formula::Gt(Box::new(prod("a", "b")), Box::new(Formula::Int(255))),
        ),
        (
            "signed add: kind (i32,i32), formula bounds i8::MIN/i8::MAX",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (i32t(), i32t()) },
            Formula::Or(vec![
                Formula::Lt(Box::new(sum("a", "b")), Box::new(Formula::Int(-128))),
                Formula::Gt(Box::new(sum("a", "b")), Box::new(Formula::Int(127))),
            ]),
        ),
        (
            "negation: kind i32, formula threshold i8::MIN",
            VcKind::NegationOverflow { ty: i32t() },
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-128))),
        ),
    ];

    let mut forged: Vec<String> = Vec::new();
    for (tag, kind, body) in mismatched {
        // Authenticated-path conversion: the record's `body` IS this honest-shaped violation
        // (no wrapper), so the arm reads it and the WIDTH cross-check runs exactly as it did
        // off the peeled body — `width: None` leaves the recorded-width check inert, so the
        // decline is the formula/kind width disagreement, not a missing record.
        let obligation = authed_body(&body);
        let vc = VerificationCondition {
            kind,
            function: "crate::probe".into(),
            location: SourceSpan::default(),
            formula: body,
            contract_metadata: None,
            obligation,
        };
        // The negation rows are probed against a MIR that really negates `y` at i32, so
        // the SUBJECT check (round-5 defect [1]) passes and the row keeps measuring the
        // WIDTH cross-check it is about rather than declining upstream of it.
        let func = if matches!(vc.kind, VcKind::NegationOverflow { .. }) {
            named_neg_func("y", 32)
        } else {
            probe_func()
        };
        if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&func, &vc) {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "a kernel-checked adequacy certificate was minted at a width the VC's own kind \
         contradicts: {forged:#?}"
    );

    // CONTROL: the same construction with the widths AGREEING must still certify, at
    // every one of the four arms — otherwise the check above is a blanket decline.
    let agreeing: Vec<(&str, VcKind, Formula, SafetyVcKind)> = vec![
        (
            "unsigned add: kind (u8,u8), formula threshold u8::MAX",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u8t(), u8t()) },
            Formula::Gt(Box::new(sum("a", "b")), Box::new(Formula::Int(255))),
            SafetyVcKind::Overflow(UWidth::W8),
        ),
        (
            "unsigned mul: kind (u32,u32), formula threshold u32::MAX",
            VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (u32t(), u32t()) },
            Formula::Gt(Box::new(prod("a", "b")), Box::new(Formula::Int(4294967295))),
            SafetyVcKind::UnsignedMulOverflow(UWidth::W32),
        ),
        (
            "signed add: kind (i32,i32), formula bounds i32::MIN/i32::MAX",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (i32t(), i32t()) },
            Formula::Or(vec![
                Formula::Lt(Box::new(sum("a", "b")), Box::new(Formula::Int(-2147483648))),
                Formula::Gt(Box::new(sum("a", "b")), Box::new(Formula::Int(2147483647))),
            ]),
            SafetyVcKind::SignedOverflow(SignedOp::Add, SWidth::W32),
        ),
        (
            "negation: kind i32, formula threshold i32::MIN",
            VcKind::NegationOverflow { ty: i32t() },
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-2147483648))),
            SafetyVcKind::NegationOverflow(SWidth::W32),
        ),
        (
            "CONTROL unsigned sub: width comes from the kind, threshold is 0",
            VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (u32t(), u32t()) },
            Formula::Lt(Box::new(diff("a", "b")), Box::new(Formula::Int(0))),
            SafetyVcKind::UnsignedSubUnderflow(UWidth::W32),
        ),
    ];
    for (tag, kind, body, want) in agreeing {
        let obligation = authed_body(&body);
        let vc = VerificationCondition {
            kind,
            function: "crate::probe".into(),
            location: SourceSpan::default(),
            formula: body,
            contract_metadata: None,
            obligation,
        };
        // See the note on the `mismatched` loop: the negation row is probed against a MIR
        // that negates `y` at i32, which is what makes this a POSITIVE control for the
        // width check rather than a subject decline.
        let func = if matches!(vc.kind, VcKind::NegationOverflow { .. }) {
            named_neg_func("y", 32)
        } else {
            probe_func()
        };
        assert_eq!(
            safety_vc_is_faithful_formula_aware(&func, &vc).map(|(k, _)| k),
            Some(want),
            "{tag}: the width cross-check must reject a DISAGREEMENT, not the arm"
        );
    }
}

/// The negation arm's ASSERT route reaches the same width the same way, and the MIR
/// confirmation `mir_assert_condition_core` does NOT close it: that chain checks the
/// assert's condition local is defined by the located COMPARISON, and nothing in it looks
/// at the width. A crafted `VerifiableFunction` whose MIR really does carry an
/// `expected == false` `OverflowNeg` assert on `_3` and the single defining statement
/// `_3 := (y == -128)` satisfies every structural requirement — and PRE-FIX minted
/// `NegationOverflow(W8)` for a VC whose kind is an **i32** negation (MEASURED).
///
/// The honest twin (`_3 := (x == i32::MIN)`) is asserted in the same test: it must still
/// certify at W32, so the fix removes the width forgery, not the assert route.
#[test]
fn the_assert_route_cannot_certify_a_width_the_vc_kind_contradicts() {
    let i32t = || Ty::Int { width: 32, signed: true };
    // `assert_neg_func(true, None)` binds `_3 = (x == i32::MIN)`; this variant binds it
    // to the NARROWER `-128` over an unrelated local, which is a genuine MIR statement
    // and therefore passes `mir_assert_condition_core`.
    let narrow = {
        let mut f = assert_neg_func(true, None);
        f.body.blocks[0].stmts = vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(-128)),
            ),
            span: Default::default(),
        }];
        f
    };
    let minted = certified_kinds(&narrow);
    assert!(
        !minted.contains(&SafetyVcKind::NegationOverflow(SWidth::W8)),
        "the assert route minted an i8 negation-overflow certificate for an i32 \
         negation — the MIR confirmation checks the comparison, not the WIDTH: {minted:?}"
    );

    // The honest twin still certifies.
    let honest = assert_neg_func(true, None);
    assert!(
        certified_kinds(&honest).contains(&SafetyVcKind::NegationOverflow(SWidth::W32)),
        "the width cross-check must reject a DISAGREEMENT, not the assert route: {:?}",
        certified_kinds(&honest)
    );
    let _ = i32t();
}

// ---------------------------------------------------------------------------------
// 9. THE ITE CASE-SPLIT PEEL (2026-07-30, round-4 defect [3]).
//
// `eliminate_term_ites` (`trust-vcgen/src/generate/entry.rs:603-604`) rewrites EVERY
// generated VC whose formula contains an `Ite`, safety VCs included. The `And`-last peel
// then fed the `Implies`-consequent peel, and the pair returned the LAST case-split arm's
// consequent WITH ITS GUARD STRIPPED — certifying one branch of a proposition that says
// both, and never reading the other.
// ---------------------------------------------------------------------------------

/// `fn f(a: u32) -> u32 { a <op> <symbolic Ite> }`, driven through the REAL emitter.
///
/// The divisor is an `Operand::Symbolic`, which is how a term-level `Ite` reaches a
/// safety VC: `v2_divisor_is_zero_formula` (`generate/block_defs.rs:244-255`) emits
/// `Eq(<the symbolic formula>, 0)` verbatim for a `Symbolic` divisor, and
/// `eliminate_term_ites` then lifts it. Per the round-4 verdict's scope limit this is
/// fixture/deserialization-reachable, not rustc-source-reachable — `trust-mir-extract`
/// only ever CONSUMES `Operand::Symbolic`.
fn symbolic_divisor_fn(op: BinOp, divisor: Formula) -> VerifiableFunction {
    let u32t = || Ty::Int { width: 32, signed: false };
    VerifiableFunction {
        name: "sym_div".into(),
        def_path: "crate::sym_div".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u32t(), name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Symbolic(divisor),
                    ),
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: u32t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn ite(cond: &str, then_v: &str, else_v: &str) -> Formula {
    Formula::Ite(
        Box::new(Formula::Var(cond.into(), Sort::Bool)),
        Box::new(var(then_v)),
        Box::new(var(else_v)),
    )
}

/// THE EMITTER-REACHABLE ROW. An `Ite` divisor makes the div/rem obligation
/// `(c → n1 = 0) ∧ (¬c → n2 = 0)` — a CASE SPLIT, whose truth is a statement about BOTH
/// branches. PRE-FIX the peel returned `Eq(n2, 0)`, i.e. the `¬c` arm with `¬c` thrown
/// away, and both lanes minted a kernel-checked `div_by_zero`/`rem_by_zero` adequacy
/// certificate for it. The `c` arm was never read.
///
/// Asserted here on the formula the REAL `trust_vcgen::generate_vcs` produces, both
/// operators, plus the ORDER-SWAP (`Ite(c, n2, n1)`, the same proposition with the arms
/// exchanged) — because the pre-fix selection was positional, a repair that reversed the
/// selection order rather than refusing would pass one and fail the other.
///
/// The HONEST CONTROL is in the same test: an `Ite`-free symbolic divisor still certifies.
#[test]
fn an_ite_divisor_case_split_is_certified_by_no_arm() {
    let mut forged: Vec<String> = Vec::new();
    let mut split_bodies = 0usize;
    for (op, want) in [(BinOp::Div, SafetyVcKind::DivByZero), (BinOp::Rem, SafetyVcKind::RemByZero)]
    {
        for arms in [("n1", "n2"), ("n2", "n1")] {
            let func = symbolic_divisor_fn(op, ite("c", arms.0, arms.1));
            for vc in &trust_vcgen::generate_vcs(&func) {
                if !matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero) {
                    continue;
                }
                // NOT VACUOUS: the emitter really does hand this site a case split whose
                // every conjunct is an `Implies`, with a modeled `Eq(var, 0)` core inside
                // each arm. If this stops holding the test measures nothing.
                let Formula::And(conjuncts) = &vc.formula else {
                    panic!("expected the lifted case split, got {:?}", vc.formula)
                };
                assert!(
                    conjuncts.len() == 2
                        && conjuncts.iter().all(|c| matches!(c, Formula::Implies(..))),
                    "expected `And([Implies(c,..), Implies(!c,..)])` from \
                     `eliminate_term_ites`, got {:?}",
                    vc.formula
                );
                assert!(
                    conjuncts.iter().all(|c| matches!(c, Formula::Implies(_, consequent)
                        if matches!(&**consequent, Formula::Eq(l, r)
                            if formula_var_name(l).is_some()
                                && matches!(&**r, Formula::Int(0))))),
                    "each arm must carry a MODELED div-by-zero core, or the decline \
                     below proves nothing: {:?}",
                    vc.formula
                );
                split_bodies += 1;
                if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&func, vc) {
                    forged.push(format!("{op:?} arms={arms:?} -> {k:?}"));
                }
            }
        }
        // HONEST CONTROL: the same lane, same route, with no `Ite` — must still certify,
        // so what the fix removes is the case-split peel and not the div/rem arm.
        let plain = symbolic_divisor_fn(op, var("d"));
        let certified: Vec<SafetyVcKind> = trust_vcgen::generate_vcs(&plain)
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
            .filter_map(|vc| safety_vc_is_faithful_formula_aware(&plain, vc).map(|(k, _)| k))
            .collect();
        assert!(
            certified.contains(&want),
            "an `Ite`-free symbolic divisor must still certify {want:?}: {certified:?}"
        );
    }
    assert_eq!(split_bodies, 4, "expected one case-split obligation per (op, arm order)");
    assert!(
        forged.is_empty(),
        "a kernel-checked div/rem-by-zero adequacy certificate was minted for a CASE \
         SPLIT `(c -> n1=0) AND (!c -> n2=0)` by taking one arm's consequent and \
         dropping its guard: {forged:#?}"
    );
}

/// One row per certifying site: `(tag, the VC kind, THAT KIND'S OWN honest violation
/// core)`. The mirror image of [`site_hypotheses`]: every core here is the proposition the
/// emitter really builds for that kind, at the width the kind carries, so each row DOES
/// certify when it sits where the obligation body sits. That makes the table usable as a
/// POSITIVE control — a position restriction is only honest if the position it keeps
/// still works.
fn site_cores() -> Vec<(&'static str, VcKind, Formula)> {
    let u32t = || Ty::Int { width: 32, signed: false };
    let i32t = || Ty::Int { width: 32, signed: true };
    let sum = |a: &str, b: &str| Formula::Add(Box::new(var(a)), Box::new(var(b)));
    let prod = |a: &str, b: &str| Formula::Mul(Box::new(var(a)), Box::new(var(b)));
    let diff = |a: &str, b: &str| Formula::Sub(Box::new(var(a)), Box::new(var(b)));

    vec![
        (
            "bounds / IndexOutOfBounds",
            VcKind::IndexOutOfBounds,
            Formula::Ge(Box::new(var("i")), Box::new(Formula::Int(8))),
        ),
        (
            "bounds / SliceBoundsCheck",
            VcKind::SliceBoundsCheck,
            Formula::Ge(Box::new(var("i")), Box::new(var("n"))),
        ),
        (
            "div-by-zero",
            VcKind::DivisionByZero,
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0))),
        ),
        (
            "rem-by-zero",
            VcKind::RemainderByZero,
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0))),
        ),
        (
            "unsigned-add overflow",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u32t(), u32t()) },
            Formula::Gt(Box::new(sum("p", "q")), Box::new(Formula::Int(4294967295))),
        ),
        (
            "unsigned-sub underflow",
            VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (u32t(), u32t()) },
            Formula::Lt(Box::new(diff("p", "q")), Box::new(Formula::Int(0))),
        ),
        (
            "unsigned-mul overflow",
            VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (u32t(), u32t()) },
            Formula::Gt(Box::new(prod("p", "q")), Box::new(Formula::Int(4294967295))),
        ),
        (
            "signed add overflow",
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (i32t(), i32t()) },
            Formula::Or(vec![
                Formula::Lt(Box::new(sum("p", "q")), Box::new(Formula::Int(-2147483648))),
                Formula::Gt(Box::new(sum("p", "q")), Box::new(Formula::Int(2147483647))),
            ]),
        ),
        (
            "negation overflow",
            VcKind::NegationOverflow { ty: i32t() },
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-2147483648))),
        ),
        (
            "shift-amount OOB",
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: u32t(), shift_ty: u32t() },
            Formula::Ge(Box::new(var("n")), Box::new(Formula::Int(32))),
        ),
    ]
}

/// THE `Implies` WRAPPER, AND ONLY THE WRAPPER. `emitted_obligation_body`'s `Implies` arm
/// exists for one producer: `alias_analysis::refine_vc_with_alias` assigns
/// `vc.formula = Implies(assumption, vc.formula)` (`trust-vcgen/src/alias_analysis.rs:379-384`,
/// the only `<vc>.formula = Formula::Implies(..)` in that crate). Nothing in the tree
/// CALLS it today — it is a public API with no pipeline caller (only the re-export at
/// `trust-vcgen/src/lib.rs:260` and its own two unit tests) — so the arm is unexercised on
/// the emitted path, and "the wrapper is the ROOT" holds for a caller that applies it
/// last, which is the only way it is used. At any INNER position an implication is a
/// case-split arm — that is what `generate/ite.rs` builds — and peeling it strips the
/// guard.
///
/// Both directions are pinned over [`site_cores`], because the fix is a POSITION
/// restriction and a position restriction is only honest if the position it keeps still
/// works:
///
///   * ROOT `Implies(assumption, core)` — must STILL certify (the wrapper inverse
///     survives; over-rejection here would be a real capability loss).
///   * INNER `And([Bool(true), Implies(guard, core)])` — must NOT certify. Note the
///     shape: it is the ordinary conjoining wrapper `And([hypothesis.., body])` with a
///     GUARDED body, and only ONE conjunct is an `Implies`, so a repair that refused only
///     an ALL-`Implies` `And` would still mint here. That is why both halves of the fix
///     are kept.
///   * CASE SPLIT `And([Implies(guard, Bool(true)), Implies(Not(guard), core)])` — must
///     NOT certify either. This is the shape `eliminate_term_ites` actually emits, and
///     the row that carries the site-wide claim "one fix closes the ITE peel at EVERY
///     arm": the round-4 verdict confirmed the mechanism only on the div/rem carrier and
///     listed shift / uadd / signed-add / negation / bounds as API-only, so those five
///     are pinned here rather than left to the argument that the same code path serves
///     them.
#[test]
fn an_implication_is_a_wrapper_only_at_the_outermost_position() {
    let assumption = || Formula::Var("__trust_alias_no_alias".into(), Sort::Bool);
    let mut forged: Vec<String> = Vec::new();
    for (tag, kind, core) in site_cores() {
        // Authenticated-path conversion: the record's `body` IS the given formula (bare core
        // or `Implies`-wrapped), so `is_core` is applied to it directly. A bare core
        // certifies; an `Implies`/case-split body fails `is_core` and declines — the same
        // verdict the peel's position restriction produced, now via the field authentication.
        let vc_at = |formula: Formula| {
            let obligation = authed_body(&formula);
            VerificationCondition {
                kind: kind.clone(),
                function: "crate::probe".into(),
                location: SourceSpan::default(),
                formula,
                contract_metadata: None,
                obligation,
            }
        };
        // The MIR each row's core is honest against. Only the NEGATION arm reads the
        // function at all (round-5 defect [1]: the certified variable must be one this
        // MIR negates, and the width comes from THAT operand's type), and its core here
        // is `Eq(y, i32::MIN)` — so that row is probed against `fn neg(y: i32) { -y }`.
        // Probing it against the block-less `probe_func()` would make every row below a
        // vacuous decline instead of a wrapper measurement.
        let func = || {
            if matches!(kind, VcKind::NegationOverflow { .. }) {
                named_neg_func("y", 32)
            } else {
                probe_func()
            }
        };
        // NOT VACUOUS: the bare core must certify, or neither row below says anything.
        assert!(
            safety_vc_is_faithful_formula_aware(&func(), &vc_at(core.clone())).is_some(),
            "{tag}: this row's core no longer certifies unwrapped, so the controls below \
             measure nothing — re-derive the core before weakening the test"
        );

        // ROOT wrapper — must now DECLINE. This assertion is INVERTED from what it
        // said before 2026-07-31, and the inversion is the fix, not a weakening:
        // it makes strictly fewer things certify.
        //
        // The peel this used to pin discarded the antecedent (`F::Implies(_, ..)`),
        // so round-6 recipe R17 minted at all ten rows with
        // `Implies(Not(Gt(__decoy,5)), core)` — the same proposition as the
        // `Or([core, decoy])` closed one commit earlier — and with
        // `Implies(Bool(false), core)`, an identically-true obligation.
        //
        // Nothing legitimate is lost: `refine_vc_with_alias` has no pipeline caller,
        // root `Implies` occurs 0 times over the corpus's 772 safety VCs, and the
        // `assumption()` used here was never even the producer's shape (it builds
        // `Not(Eq(Var(alias-loc, Int), ..))`, not a `Var(_, Bool)`).
        let root_hostiles: [(&str, Formula); 3] = [
            ("Implies(<alias assumption>, core)", assumption()),
            ("Implies(Bool(false), core)  [identically true]", Formula::Bool(false)),
            (
                "Implies(Not(Gt(__decoy,5)), core)  [== Or([core, decoy])]",
                Formula::Not(Box::new(Formula::Gt(
                    Box::new(Formula::Var("__decoy".into(), Sort::Int)),
                    Box::new(Formula::Int(5)),
                ))),
            ),
        ];
        for (shape, antecedent) in root_hostiles {
            let root = vc_at(Formula::Implies(Box::new(antecedent), Box::new(core.clone())));
            if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&func(), &root) {
                forged.push(format!("{tag} / ROOT {shape} -> {k:?}"));
            }
        }

        // INNER — a guarded arm sitting where the obligation body sits, and the full
        // ALL-`Implies` case split `eliminate_term_ites` really builds. Both must decline.
        let guard = || Formula::Var("c".into(), Sort::Bool);
        let inner_shapes: [(&str, Formula); 2] = [
            (
                "And([Bool(true), Implies(c, core)])",
                Formula::And(vec![
                    Formula::Bool(true),
                    Formula::Implies(Box::new(assumption()), Box::new(core.clone())),
                ]),
            ),
            (
                "And([Implies(c, Bool(true)), Implies(!c, core)])",
                Formula::And(vec![
                    Formula::Implies(Box::new(guard()), Box::new(Formula::Bool(true))),
                    Formula::Implies(
                        Box::new(Formula::Not(Box::new(guard()))),
                        Box::new(core.clone()),
                    ),
                ]),
            ),
        ];
        for (shape, formula) in inner_shapes {
            if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&func(), &vc_at(formula)) {
                forged.push(format!("{tag} / {shape} -> {k:?}"));
            }
        }
    }
    assert!(
        forged.is_empty(),
        "a certificate was minted from the CONSEQUENT of an INNER implication — the case \
         guard was stripped and the obligation's other arms were never read: {forged:#?}"
    );
}

// ---------------------------------------------------------------------------------
// 10. SIGNED MIXED-WIDTH `min(wa, wb)` (2026-07-30, round-4 defect [2]).
//
// `signed_overflow_vc_modeled` narrows a mixed-width kind to `min(wa, wb)`, which makes
// the `:1091` kind-vs-formula width cross-check satisfied BY CONSTRUCTION whenever the
// body is thresholded at the narrower width. The committed regression tests all use
// SAME-width kinds, where `min()` is the identity and the hole is invisible.
// ---------------------------------------------------------------------------------

/// A signed add-overflow VC: kind `(a_width, b_width)`, body
/// `Or([Lt(a+b, MIN_w), Gt(a+b, MAX_w)])` at width `w`, over the two given operands.
fn signed_add_vc(
    a_width: u32,
    b_width: u32,
    min: i128,
    max: i128,
    a_op: Formula,
    b_op: Formula,
) -> VerificationCondition {
    let sum = Formula::Add(Box::new(a_op), Box::new(b_op));
    let formula = Formula::Or(vec![
        Formula::Lt(Box::new(sum.clone()), Box::new(Formula::Int(min))),
        Formula::Gt(Box::new(sum), Box::new(Formula::Int(max))),
    ]);
    // Authenticated-path conversion: the record's `body` IS the `Or` out-of-range core, so
    // the arm reads it and the mixed-width narrowing check runs exactly as off the peel.
    let obligation = authed_body(&formula);
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: a_width, signed: true },
                Ty::Int { width: b_width, signed: true },
            ),
        },
        function: "crate::probe".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation,
    }
}

/// A mixed-width signed kind may only be narrowed to `min(wa, wb)` when the WIDER
/// position is the untyped integer CONSTANT that caused the width spread in the first
/// place.
///
/// WHY THE `min()` RULE EXISTS, and why it may not simply be deleted:
/// `generate::type_ranges::int_op_type` takes the operation's true `(width, signed)` from
/// a NON-CONSTANT operand, because `operand_ty` fabricates `i64` for a widthless
/// `ConstValue::Int` (`trust-vcgen/src/lib.rs:1237-1241`). So `100i8 + x` legitimately
/// emits an **i8**-thresholded body under a kind that reads `(i64, i8)`, and demanding
/// `wa == wb` would drop a real certificate. That is the round-3 caveat, and it is
/// re-asserted below as a positive control.
///
/// THE HOLE: `min()` then satisfies the width cross-check unconditionally in the
/// mixed-width case, so a kind of `(i64, i8)` with an i8-thresholded body and TWO BARE
/// `Var` operands minted `SignedOverflow(Add, W8)` — an 8-bit adequacy certificate for an
/// obligation over an operand the VC's own kind types as **i64**, whose overflow boundary
/// is −2⁶³/2⁶³−1, not −2⁷/2⁷−1 — so the certificate is about a strictly narrower
/// proposition than the obligation states.
/// Both position orders are pinned, since `operand_tys` is `(lhs_ty, rhs_ty)` and the
/// forgery does not care which side is wide.
///
/// COST, MEASURED over `crates/trust-clean/fixtures` (2326 functions, 772 safety VCs):
/// zero. 49 signed `ArithmeticOverflow` VCs carry differing kind widths; 41 locate a core
/// and in ALL 41 the wider position is an `F::Int` literal; the other 8 locate no core and
/// already declined. Certificates 635 and functions-certified 286 are unchanged.
#[test]
fn a_mixed_width_signed_kind_may_only_narrow_onto_a_literal() {
    const I8_MIN: i128 = -128;
    const I8_MAX: i128 = 127;
    let want = SafetyVcKind::SignedOverflow(SignedOp::Add, SWidth::W8);

    // POSITIVE CONTROL 1 — same-width `(i8, i8)`, two bare `Var`s. `min()` is the
    // identity here; this is the shape every committed test uses and it must keep
    // certifying.
    assert_eq!(
        safety_vc_is_faithful_formula_aware(
            &probe_func(),
            &signed_add_vc(8, 8, I8_MIN, I8_MAX, var("p"), var("q"))
        )
        .map(|(k, _)| k),
        Some(want.clone()),
        "the same-width signed add must still certify — the fix restricts NARROWING, not \
         the arm"
    );

    // POSITIVE CONTROL 2 — the shape `min()` exists for: `100i8 + x`, whose untyped
    // constant lhs fabricates `i64` in the kind and whose body is honestly i8-thresholded.
    // Both position orders.
    for (tag, wa, wb, a_op, b_op) in [
        ("(i64, i8) with the i64 position a literal", 64, 8, Formula::Int(100), var("q")),
        ("(i8, i64) with the i64 position a literal", 8, 64, var("p"), Formula::Int(100)),
    ] {
        assert_eq!(
            safety_vc_is_faithful_formula_aware(
                &probe_func(),
                &signed_add_vc(wa, wb, I8_MIN, I8_MAX, a_op, b_op)
            )
            .map(|(k, _)| k),
            Some(want.clone()),
            "{tag}: the round-3 `min()` caveat — an untyped integer constant operand \
             defaults to i64, and narrowing onto it is legitimate. This must not break."
        );
    }

    // THE FORGERY — the same mixed-width kinds with TWO BARE `Var` operands. Nothing
    // justifies the narrowing: neither operand is the constant `int_op_type` narrows for.
    let mut forged: Vec<String> = Vec::new();
    for (tag, wa, wb) in [("kind (i64, i8)", 64u32, 8u32), ("kind (i8, i64)", 8, 64)] {
        let vc = signed_add_vc(wa, wb, I8_MIN, I8_MAX, var("p"), var("q"));
        // NOT VACUOUS: the kind is still kind-modeled at W8 via `min()`, so the ONLY
        // thing that can decline it is the narrowing justification.
        assert_eq!(
            signed_overflow_vc_modeled(&vc.kind),
            Some((SignedOp::Add, SWidth::W8)),
            "{tag}: `min()` no longer narrows to W8, so this row measures nothing"
        );
        if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&probe_func(), &vc) {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "a kernel-checked 8-bit signed-overflow adequacy certificate was minted for a VC \
         whose own kind types an operand as i64; `min(wa, wb)` made the width \
         cross-check vacuous: {forged:#?}"
    );
}


// ---------------------------------------------------------------------------------
// 11. ROUND 5 (2026-07-31) — the three defects this lane had NO defence for.
//
// Round 4 repaired the trust-ir lane and left MirSem's copies of the same defects
// untouched, which is why they recurred: D1 (the negation SUBJECT) and D5/D6 (the uadd
// vacuity side condition) did not exist here in any form, and D4 (the dropped signed
// bounds disjunct) was closed there and open here. All three are now closed on both
// lanes, in the same shape.
// ---------------------------------------------------------------------------------

/// `assert_neg_func`, but the assert's TARGET block negates a DIFFERENT local than the
/// one the condition compares — `_3 = (x == i32::MIN)` guarding `-y`. `x_width` narrows
/// the compared local's own type without touching the literal.
///
/// This is a well-formed `VerifiableFunction` driven end-to-end through
/// `trust_vcgen::generate_vcs`: `v2_build_assert_negation_vc` reads its subject from
/// `v2_find_target_neg_operand` (the TARGET block's negation, i.e. `y`) while the
/// obligation body is the bare condition local `_3`, whose binding names `x`.
fn assert_neg_subject_mismatch_func(x_width: u32) -> VerifiableFunction {
    let mut f = assert_neg_func(true, None);
    f.body.locals[1].ty = Ty::Int { width: x_width, signed: true };
    // bb1 negates `y` (local 2), not the compared `x` (local 1).
    f.body.blocks[1].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(2))),
        span: Default::default(),
    }];
    f
}

/// D1/D8 — THE CERTIFIED SUBJECT. A `NegationOverflow` certificate names a variable; the
/// obligation is about the operand the MIR NEGATES. Nothing in this lane compared the
/// two, so a dominating `assert!(!(x == i32::MIN))` over a negation of an unrelated `y`
/// minted `NegationOverflow(W32)` about `x` — and `y`, the operand actually negated,
/// appears nowhere in the VC formula or in the certified proposition.
///
/// PRE-FIX, MEASURED by reverting the subject cross-check in place (2026-07-31):
///   * row (a) `assert!(!(x == i32::MIN))` over `-y`  -> `Some(NegationOverflow(W32))`
///   * row (b) the same with `x: i8`                  -> `Some(NegationOverflow(W32))`,
///     a 32-bit certificate about an i8: a type that can never hold −2³¹
///   * row (c) API, kind `i8` over a MIR that negates an `i32` -> `Some(NegationOverflow(W8))`
/// POST-FIX none of the three certifies, and the four positive controls still do.
///
/// Rows (a) and (b) are EMITTER-DRIVEN — `trust_vcgen::generate_vcs` on a well-formed
/// `VerifiableFunction`, no hand-built formula. Row (c) is API-level and is what pins the
/// second half of the fix: the width must come from `operand_ty` OF THE CERTIFIED
/// VARIABLE, not from `vc.kind`'s `ty`.
#[test]
fn a_negation_certificate_must_name_a_variable_the_mir_actually_negates() {
    // POSITIVE CONTROLS FIRST — the fix must remove the forgery, not the two routes.
    let raw = neg_func(32);
    assert!(
        certified_kinds(&raw).contains(&SafetyVcKind::NegationOverflow(SWidth::W32)),
        "the raw `-x` route must still certify at W32: {:?}",
        certified_kinds(&raw)
    );
    let asserted = assert_neg_func(true, None);
    assert!(
        certified_kinds(&asserted).contains(&SafetyVcKind::NegationOverflow(SWidth::W32)),
        "the assert-condition route must still certify at W32: {:?}",
        certified_kinds(&asserted)
    );
    for fixture in ["fixtures/real-corpus/negate.json", "fixtures/rustcmir_m2/abs_branch.json"] {
        let func = load(fixture);
        assert!(
            certified_kinds(&func).iter().any(|k| matches!(k, SafetyVcKind::NegationOverflow(_))),
            "{fixture}: a committed corpus negation row lost its certificate — the subject \
             check is supposed to cost nothing on real MIR: {:?}",
            certified_kinds(&func)
        );
    }

    let mut forged: Vec<String> = Vec::new();

    // (a)/(b) EMITTER-DRIVEN: the assert compares `x`, the MIR negates `y`.
    for (tag, x_width) in [("x: i32", 32u32), ("x: i8 — a 32-bit cert about an i8", 8)] {
        let func = assert_neg_subject_mismatch_func(x_width);
        // NOT VACUOUS: the emitter really does raise the negation obligation here.
        assert!(
            trust_vcgen::generate_vcs(&func)
                .iter()
                .any(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })),
            "{tag}: no NegationOverflow VC was emitted, so this row measures nothing"
        );
        for k in certified_kinds(&func) {
            if matches!(k, SafetyVcKind::NegationOverflow(_)) {
                forged.push(format!("({tag}) -> {k:?}"));
            }
        }
    }

    // (c) API: the certified variable IS negated, but at a width the certificate
    //     contradicts — the width must be read off the subject, not off `vc.kind`.
    let func = named_neg_func("y", 32);
    let vc = VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width: 8, signed: true } },
        function: "crate::neg".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-128))),
        contract_metadata: None,
        obligation: None,
    };
    // NOT VACUOUS: `vc.kind`'s own width check passes — W8 kind, W8 threshold — so the
    // ONLY thing that can decline this row is the subject's own type.
    assert_eq!(negation_vc_modeled(&vc.kind), Some(SWidth::W8));
    if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&func, &vc) {
        forged.push(format!("(kind i8 over a MIR that negates an i32) -> {k:?}"));
    }

    assert!(
        forged.is_empty(),
        "a kernel-checked negation-overflow certificate was minted about a variable this \
         function's MIR does not negate, or at a width that variable's own type \
         contradicts: {forged:#?}"
    );
}

/// `fn f(i: i64, len: i64) { assert!(i < len) }` — the SIGNED-index bounds assert, driven
/// through the real emitter. `v2_build_bounds_assert_vc` emits
/// `Or([Lt(i,0), Ge(i,len)])` for it (`generate/checked_vcs.rs:257-265`, taken whenever
/// the compared lhs `is_signed`); the unsigned twin emits the bare `Ge(i,len)`.
fn bounds_assert_func(signed: bool) -> VerifiableFunction {
    let t = || Ty::Int { width: 64, signed };
    VerifiableFunction {
        name: "idx".into(),
        def_path: "crate::idx".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: t(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: t(), name: Some("len".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: true,
                        msg: trust_types::AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: Default::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// D4 — THE DROPPED SIGNED DISJUNCT. For a signed index the emitted violation is
/// `Or([Lt(i,0), Ge(i,len)])`, and `idx_oob len i` models the `Ge` half ONLY.
/// The locator of the day (`obligation_violation_leaf`, deleted in round 6) descended
/// `Or`s, so it returned that half and
/// `SafetyVcKind::Bounds` was minted for an obligation strictly larger than the
/// certificate's own proposition — a false ADEQUACY statement (the direction is
/// over-refutation, so not a live safety hole) and a kind gap.
///
/// PRE-FIX, MEASURED by reverting the decline in place (2026-07-31): the emitter-driven
/// row certifies `Some(Bounds)` and so does the wrapped API row. POST-FIX neither does,
/// and the UNSIGNED twin — the same function with unsigned locals — still certifies,
/// so this is a signed-form decline and not a bounds-arm decline.
#[test]
fn a_signed_index_bounds_violation_is_certified_by_no_arm() {
    // POSITIVE CONTROL: the unsigned twin emits the bare `Ge(i, len)` and must certify.
    let unsigned = bounds_assert_func(false);
    assert!(
        certified_kinds(&unsigned).contains(&SafetyVcKind::Bounds),
        "the unsigned bounds assert must still certify: {:?}",
        certified_kinds(&unsigned)
    );

    // EMITTER-DRIVEN: the signed twin's own violation carries the `Lt(i,0)` disjunct.
    let signed = bounds_assert_func(true);
    let bodies: Vec<_> = trust_vcgen::generate_vcs(&signed)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .filter_map(|vc| authenticated_obligation_body(vc).cloned())
        .collect();
    // NOT VACUOUS: the shape this test is about must actually be what the emitter built.
    assert!(
        bodies.iter().any(|b| bounds_violation_shape(b).is_some_and(|(_, _, s)| s)),
        "the signed bounds assert did not emit the `Or([Lt(i,0), Ge(i,len)])` violation \
         this test is about, so it measures nothing: {bodies:#?}"
    );
    assert!(
        !certified_kinds(&signed).contains(&SafetyVcKind::Bounds),
        "a `Bounds` certificate was minted for a SIGNED-index obligation whose emitted \
         violation also states `i < 0`; the certificate's proposition is strictly \
         smaller than the VC's: {:?}",
        certified_kinds(&signed)
    );

    // API: the same violation, AUTHENTICATED — bare, and under an ordinary conjoining
    // wrapper (the emitter's `ConjoinFactsLast`). Each record reconstructs to its `formula`,
    // so the decline below is the bounds arm rejecting the SIGNED `Or` form
    // (`carries_signed_index_violation`), not the authentication failing for want of a record.
    let signed_or = || {
        Formula::Or(vec![
            Formula::Lt(Box::new(var("i")), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(var("i")), Box::new(var("n"))),
        ])
    };
    let api_recs = [
        (
            "bare",
            trust_types::ObligationRecord {
                body: signed_or(),
                wrappers: vec![],
                subject: None,
                width: None,
            },
        ),
        (
            "wrapped",
            trust_types::ObligationRecord {
                body: signed_or(),
                wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
                    facts: vec![Formula::Bool(true)],
                }],
                subject: None,
                width: None,
            },
        ),
    ];
    for (tag, rec) in api_recs {
        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "crate::probe".into(),
            location: SourceSpan::default(),
            formula: reconstruct_obligation(&rec),
            contract_metadata: None,
            obligation: Some(rec),
        };
        assert_eq!(
            safety_vc_is_faithful_formula_aware(&probe_func(), &vc).map(|(k, _)| k),
            None,
            "{tag}: the signed-index `Or` certified its `Ge` half alone"
        );
    }
}

/// D5/D6 — THE UADD VACUITY SIDE CONDITION, WHICH THIS LANE DID NOT HAVE.
///
/// The emitted unsigned-add violation is `Or([Lt(a+b,0), Gt(a+b,MAX)])` and
/// `uadd_overflows_uW` models the `Gt` half. Certifying it is sound only because the
/// emitter's own unsigned operand ranges make `Lt(a+b,0)` unsatisfiable — a fact this
/// lane never checked, at ANY uadd row, honest ones included.
///
/// The rows are the round-4 recipe and its two neighbours, in the shape
/// `v2_formula_with_path_guards` builds: one guarded path carrying the ranges and a
/// second path that does not. `a = −1, b = 0` refutes the certificate on that second
/// path. PRE-FIX (side condition reverted in place, 2026-07-31) all four mint
/// `Overflow(W8)`; POST-FIX none does, and both positive controls still certify.
#[test]
fn a_uadd_certificate_requires_its_discarded_disjunct_to_be_vacuous() {
    let sum = || Formula::Add(Box::new(var("a")), Box::new(var("b")));
    let oor = || {
        Formula::Or(vec![
            Formula::Lt(Box::new(sum()), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(sum()), Box::new(Formula::Int(255))),
        ])
    };
    let range = |v: &str| {
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var(v))),
            Formula::Le(Box::new(var(v)), Box::new(Formula::Int(255))),
        ])
    };
    let guard = |g: &str| Formula::Var(g.into(), Sort::Bool);
    let u8t = || Ty::Int { width: 8, signed: false };
    // Trust: AUTHENTICATED-PATH CONVERSION (2026-08-01). The vacuity of the discarded
    // `Lt(a+b, 0)` half is now checked against the RECORD's own `ConjoinFactsLast` facts
    // (the operand ranges the emitter demotes there), not against sibling conjuncts a peel
    // read out of the formula. So each row builds a record whose `body` is the two-disjunct
    // `oor` and whose facts are the given operand-range list; `formula` is the faithful
    // `reconstruct_obligation`. The multi-path negative controls of the peel era are gone
    // by construction: the ranges are the INNERMOST wrapper, shared across every path-guard
    // disjunct, so per-path range divergence cannot be recorded at all — the property is
    // "the record's facts pin both operands ≥ 0, or decline".
    let vc_with = |facts: Vec<Formula>, extra: Vec<trust_types::ObligationWrapper>| {
        let mut wrappers = vec![trust_types::ObligationWrapper::ConjoinFactsLast { facts }];
        wrappers.extend(extra);
        let rec = trust_types::ObligationRecord {
            body: oor(),
            wrappers,
            subject: None,
            width: None,
        };
        let formula = reconstruct_obligation(&rec);
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u8t(), u8t()) },
            function: "crate::probe".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: Some(rec),
        }
    };
    let minted = |facts: Vec<Formula>, extra: Vec<trust_types::ObligationWrapper>| {
        safety_vc_is_faithful_formula_aware(&probe_func(), &vc_with(facts, extra)).map(|(k, _)| k)
    };

    // POSITIVE CONTROL 1 — the emitter's own shape: both ranges recorded beside the body.
    assert_eq!(
        minted(vec![range("a"), range("b")], vec![]),
        Some(SafetyVcKind::Overflow(UWidth::W8)),
        "the emitter's own recorded `body = oor`, facts = both operand ranges must certify"
    );
    // POSITIVE CONTROL 2 — the multi-path split (a `PathGuardOr` wrapper OUTSIDE the shared
    // ranges); the ranges are innermost, so both paths carry them and the vacuity holds.
    assert_eq!(
        minted(
            vec![range("a"), range("b")],
            vec![trust_types::ObligationWrapper::PathGuardOr {
                paths: vec![
                    trust_types::PathGuardTerm::Guarded { guards: vec![guard("g1")] },
                    trust_types::PathGuardTerm::Guarded { guards: vec![guard("g2")] },
                ],
            }],
        ),
        Some(SafetyVcKind::Overflow(UWidth::W8)),
        "a recorded guard split over the SAME shared operand ranges must still certify"
    );

    let mut forged: Vec<String> = Vec::new();
    for (tag, facts) in [
        ("no range evidence at all", vec![Formula::Bool(true)]),
        ("only a's range recorded", vec![range("a")]),
        ("only b's range recorded", vec![range("b")]),
        ("ranges on terms that are not the operands", vec![range("p"), range("q")]),
    ] {
        if let Some(k) = minted(facts, vec![]) {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "a kernel-checked `uadd_overflows` certificate was minted for the `Gt` half of a \
         two-disjunct violation whose discarded `Lt(a+b, 0)` half is NOT provably \
         vacuous from the record's own facts — `a = −1, b = 0` satisfies the obligation \
         and refutes the certificate: {forged:#?}"
    );
}

// [REMOVED 2026-08-01] `the_bare_disjunct_of_a_mixed_or_is_examined_not_dropped` was a
// PURE PEEL-MECHANISM test: it exercised `emitted_obligation_body_located` /
// `emitted_obligation_body` directly (the sibling-less-occurrence bookkeeping of the
// wrapper-inverse, and its fail-closed on two paths peeling to different bodies). Both peels
// are deleted — production authenticates a recorded obligation by reconstruct-and-equate —
// so the behaviour this pinned no longer exists. The surviving mixed-`Or` decline property is
// pinned against the LIVE certifier by the migrated
// `trustir_safety_selection_tests::a_mixed_or_hides_an_occurrence_from_the_uadd_universal_and_must_decline`.

// ---------------------------------------------------------------------------------
// 12. ROUND 6 — `is_core` APPLIES TO THE COLLAPSED PEELED BODY, NEVER TO A LEAF FOUND
//     BY DESCENDING IT (F1), the assert route's own negation subject (F2), and the
//     one-sided `#` strip (F3).
//
// Round 5 landed the collapsed-body discipline lane-wide on trust-ir (`locate_violation`)
// but on mirsem only inside the unsigned-add arm. The other six arms handed their shape
// predicate to `obligation_violation_leaf`, which peeled to the body and then SEARCHED
// INSIDE it — so `Or([<that arm's own core>, Gt(decoy, 5)])`, an obligation strictly
// weaker than the core, located the core and certified it. These tests pin all seven arms
// and both routes.
// ---------------------------------------------------------------------------------

/// F1 — THE DISJOINED DECOY, AT EVERY ARM.
///
/// For each row of [`site_cores`], wrap that arm's OWN emitted core in
/// `Or([core, Gt(decoy, 5)])`. That formula's body — there is no `And` disjunct, so the
/// peel returns the whole `Or` — asserts `core ∨ decoy > 5`, which is strictly weaker
/// than `core`; a certificate for `core` is therefore a certificate for a proposition
/// the VC does not state. Every arm must decline.
///
/// PRE-FIX, MEASURED by reverting F1 in place (`locate_violation` back to the deleted
/// `obligation_violation_leaf` at the six arms) and re-running, 2026-07-31:
///
/// ```text
/// bounds / IndexOutOfBounds -> Bounds
/// bounds / SliceBoundsCheck -> Bounds
/// div-by-zero               -> DivByZero
/// rem-by-zero               -> RemByZero
/// unsigned-sub underflow    -> UnsignedSubUnderflow(W32)
/// unsigned-mul overflow     -> UnsignedMulOverflow(W32)
/// signed add overflow       -> SignedOverflow(Add, W32)
/// negation overflow         -> NegationOverflow(W32)
/// ```
///
/// Eight of the ten rows. The two that already declined are the CONTROLS this fix was
/// copied from and they are not weakened here: the unsigned-ADD arm was already a shape
/// match on the collapsed body (round-5 defects [5]/[6]), and the SHIFT arm has read
/// `shift_violation_shape` off the collapsed body since round 3.
///
/// This test drives the MIRSEM certifier only. What `trustir_safety.rs` returns on the
/// same ten recipes is NOT measured here and is not asserted here — that lane is owned and
/// repaired separately, and a parity checker is the thing that compares them.
///
/// NOT VACUOUS: each row's bare core is asserted to still certify first, so a blanket
/// decline cannot pass this test.
#[test]
fn a_disjoined_decoy_is_certified_by_no_arm() {
    let decoy = || Formula::Gt(Box::new(var("__decoy")), Box::new(Formula::Int(5)));
    let mut forged: Vec<String> = Vec::new();
    for (tag, kind, core) in site_cores() {
        let vc_at = |formula: Formula| {
            let obligation = authed_body(&formula);
            VerificationCondition {
                kind: kind.clone(),
                function: "crate::probe".into(),
                location: SourceSpan::default(),
                formula,
                contract_metadata: None,
                obligation,
            }
        };
        // Only the negation arm reads the MIR (the certified variable must be one this
        // function negates), and its core here is `Eq(y, i32::MIN)`.
        let func = || {
            if matches!(kind, VcKind::NegationOverflow { .. }) {
                named_neg_func("y", 32)
            } else {
                probe_func()
            }
        };
        assert!(
            safety_vc_is_faithful_formula_aware(&func(), &vc_at(core.clone())).is_some(),
            "{tag}: this row's core no longer certifies unwrapped, so the decoy below \
             measures nothing — re-derive the core before weakening the test"
        );
        let disjoined = Formula::Or(vec![core.clone(), decoy()]);
        if let Some((k, _)) = safety_vc_is_faithful_formula_aware(&func(), &vc_at(disjoined)) {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "a certificate was minted for a core found by DESCENDING the peeled body: the \
         obligation states `core ∨ decoy > 5` and the certificate states `core`, which is \
         strictly stronger — the VC does not entail what was certified: {forged:#?}"
    );
}

/// F1, the unsigned-MUL half — the ONE leaf-under-body population this lane still had.
///
/// The emitter's unsigned-mul violation is the two-disjunct
/// `Or([Lt(a*b, 0), Gt(a*b, MAX)])` and `umul_overflows_uW` models the `Gt` half, exactly
/// as at unsigned-add. Round 5 gave unsigned-add the vacuity side condition and recorded
/// the mul twin as unfixed; this pins the twin.
///
/// The rows are the unsigned-add test's rows with `Mul` for `Add`. PRE-FIX (F1 reverted
/// in place, 2026-07-31) all five mint `UnsignedMulOverflow(W8)`; POST-FIX none does, and
/// both positive controls still certify. `a = −1, b = 0` satisfies the discarded
/// `Lt(a*b, 0)` half on the evidence-free path and refutes the certificate there.
#[test]
fn a_umul_certificate_requires_its_discarded_disjunct_to_be_vacuous() {
    let prod = || Formula::Mul(Box::new(var("a")), Box::new(var("b")));
    let oor = || {
        Formula::Or(vec![
            Formula::Lt(Box::new(prod()), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(prod()), Box::new(Formula::Int(255))),
        ])
    };
    let range = |v: &str| {
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var(v))),
            Formula::Le(Box::new(var(v)), Box::new(Formula::Int(255))),
        ])
    };
    let guard = |g: &str| Formula::Var(g.into(), Sort::Bool);
    let u8t = || Ty::Int { width: 8, signed: false };
    // Trust: AUTHENTICATED-PATH CONVERSION (2026-08-01) — the unsigned-mul twin of the
    // uadd vacuity conversion. Vacuity is read off the record's own `ConjoinFactsLast`
    // facts; see [`a_uadd_certificate_requires_its_discarded_disjunct_to_be_vacuous`].
    let vc_with = |facts: Vec<Formula>, extra: Vec<trust_types::ObligationWrapper>| {
        let mut wrappers = vec![trust_types::ObligationWrapper::ConjoinFactsLast { facts }];
        wrappers.extend(extra);
        let rec = trust_types::ObligationRecord {
            body: oor(),
            wrappers,
            subject: None,
            width: None,
        };
        let formula = reconstruct_obligation(&rec);
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (u8t(), u8t()) },
            function: "crate::probe".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: Some(rec),
        }
    };
    let minted = |facts: Vec<Formula>, extra: Vec<trust_types::ObligationWrapper>| {
        safety_vc_is_faithful_formula_aware(&probe_func(), &vc_with(facts, extra)).map(|(k, _)| k)
    };

    // POSITIVE CONTROL 1 — the emitter's own shape: both ranges recorded beside the body.
    assert_eq!(
        minted(vec![range("a"), range("b")], vec![]),
        Some(SafetyVcKind::UnsignedMulOverflow(UWidth::W8)),
        "the emitter's own recorded `body = oor`, facts = both operand ranges must certify"
    );
    // POSITIVE CONTROL 2 — the multi-path split over the SAME shared ranges.
    assert_eq!(
        minted(
            vec![range("a"), range("b")],
            vec![trust_types::ObligationWrapper::PathGuardOr {
                paths: vec![
                    trust_types::PathGuardTerm::Guarded { guards: vec![guard("g1")] },
                    trust_types::PathGuardTerm::Guarded { guards: vec![guard("g2")] },
                ],
            }],
        ),
        Some(SafetyVcKind::UnsignedMulOverflow(UWidth::W8)),
        "a recorded guard split over the SAME shared operand ranges must still certify"
    );

    let mut forged: Vec<String> = Vec::new();
    for (tag, facts) in [
        ("no range evidence at all", vec![Formula::Bool(true)]),
        ("only a's range recorded", vec![range("a")]),
        ("only b's range recorded", vec![range("b")]),
        ("ranges on terms that are not the operands", vec![range("p"), range("q")]),
    ] {
        if let Some(k) = minted(facts, vec![]) {
            forged.push(format!("{tag} -> {k:?}"));
        }
    }
    assert!(
        forged.is_empty(),
        "a kernel-checked `umul_overflows` certificate was minted for the `Gt` half of a \
         two-disjunct violation whose discarded `Lt(a*b, 0)` half is NOT provably \
         vacuous: {forged:#?}"
    );
}

/// The certificates this function mints from VCs that take the ASSERT-CONDITION route —
/// the ones whose peeled obligation body is the bare boolean condition local. Selecting
/// them is what keeps the F2 test from being confounded by the raw-`Neg` VCs the same MIR
/// legitimately raises for every `Neg` statement in it.
fn assert_route_certificates(func: &VerifiableFunction) -> Vec<SafetyVcKind> {
    trust_vcgen::generate_vcs(func)
        .iter()
        .filter(|vc| is_safety_vc_kind(&vc.kind))
        .filter(|vc| {
            matches!(authenticated_obligation_body(vc), Some(Formula::Var(_, Sort::Bool)))
        })
        .filter_map(|vc| safety_vc_is_faithful_formula_aware(func, vc).map(|(k, _)| k))
        .collect()
}

/// `fn(x: i32, y: i32)` with an `expected == false` `OverflowNeg` assert on `_3`, bound in
/// the assert's own block by `_3 := (x == i32::MIN)`, whose TARGET block negates `y`
/// FIRST and `x` second.
///
/// That is precisely the gap between the two subject witnesses. `negation_subjects` is the
/// whole-body UNION, so it contains `x` and the union check passes. But the emitter's own
/// subject is `v2_find_target_neg_operand`'s FIRST `Neg` of the target block — `y` — and
/// `VcKind::NegationOverflow { ty }` is `operand_ty` of THAT operand. So the certificate
/// would be about `x` while the VC the emitter built is about `y`.
///
/// `first_neg == "y"` gives the hostile MIR; `first_neg == "x"` gives the honest twin,
/// where both witnesses name the same operand.
fn assert_neg_target_order_func(first_neg: &str) -> VerifiableFunction {
    let i32t = || Ty::Int { width: 32, signed: true };
    let neg_of = |local: usize, dest: usize| Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(local))),
        span: Default::default(),
    };
    // local 1 = `x`, local 2 = `y`.
    let target_stmts = if first_neg == "y" {
        vec![neg_of(2, 0), neg_of(1, 4)]
    } else {
        vec![neg_of(1, 0), neg_of(2, 4)]
    };
    VerifiableFunction {
        name: "assert_neg_order".into(),
        def_path: "crate::assert_neg_order".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32t(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32t(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: i32t(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: i32t(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(-2147483648)),
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: false,
                        msg: trust_types::AssertMessage::OverflowNeg,
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: Default::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: target_stmts, terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: i32t(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// F2 — THE ASSERT ROUTE GETS THE EMITTER'S OWN SUBJECT, LAYERED ON THE UNION.
///
/// Round 5 keyed the negation subject check on the whole-body UNION of every operand the
/// MIR negates, deliberately — the round-5 verdict records that keying it on the ROUTE is
/// what left the sibling lane's round-4 half API-reopenable (its defect [8]; that history
/// is cited, not re-measured here). But the union is a SUPERSET of what the assert producer
/// reads — `v2_find_target_neg_operand` takes the FIRST `Neg` of the assert's own TARGET
/// block — so a MIR that negates two different locals satisfies the union while the
/// certificate names the wrong one of them.
///
/// PRE-FIX, MEASURED by reverting the `CoreRoute::AssertCondition` gate in place and
/// re-running (2026-07-31): the hostile MIR mints `[NegationOverflow(W32)]` on the
/// assert-route VC — a certificate about `x` for a VC whose kind the emitter built from
/// `y`. POST-FIX that list is empty.
///
/// THE FIX LAYERS, IT DOES NOT REPLACE, and both halves are asserted:
///
///   * the honest twin (the target block negates `x` first) still certifies at W32, so
///     the assert route is not closed; and
///   * `assert_neg_func(true, None)`'s single-negation assert row still certifies, which
///     is the corpus-shaped case (7 of this lane's 12 negation certificates take this
///     route).
#[test]
fn the_assert_route_certifies_only_its_own_targets_negation() {
    // HONEST: the emitter's subject and the certified variable are the same operand.
    assert_eq!(
        assert_route_certificates(&assert_neg_target_order_func("x")),
        vec![SafetyVcKind::NegationOverflow(SWidth::W32)],
        "the assert route must still certify when its target block's FIRST negation IS \
         the variable the condition local compares"
    );
    assert_eq!(
        assert_route_certificates(&assert_neg_func(true, None)),
        vec![SafetyVcKind::NegationOverflow(SWidth::W32)],
        "the ordinary single-negation assert row must still certify"
    );

    // HOSTILE: the union still contains `x`, but the emitter's own subject is `y`.
    let hostile = assert_neg_target_order_func("y");
    assert!(
        negation_subject_ty(&hostile, "x").is_some(),
        "the whole-body union must still admit `x`, or this row would decline for the \
         round-5 reason instead of the round-6 one and measure nothing"
    );
    assert_eq!(
        assert_route_certificates(&hostile),
        Vec::<SafetyVcKind>::new(),
        "a negation certificate about `x` was minted for an assert whose own target block \
         negates `y` — the emitter built `VcKind::NegationOverflow {{ ty }}` from `y`"
    );
}

/// F3 — THE `#` STRIP WAS ONE-SIDED, AND THE MIR SIDE IS THE WRONG SIDE.
///
/// `negation_subject_ty` compared the caller's already-stripped FORMULA base name against
/// a MIR place name it stripped again. `place_to_var_name` closed exactly this
/// base/segment-boundary hazard for `.`/`[`/`*`/`@` (`trust-vcgen/src/lib.rs:4281`,
/// `PROJECTION_SEGMENT_LEAD`) and `#` is not in that set, so a MIR local literally named
/// `y#s3_0` authenticated a certificate about the formula variable `y` — two different
/// places, one name comparison.
///
/// PRE-FIX, MEASURED by restoring the `name.split('#').next()` strip in place and
/// re-running (2026-07-31): `Some(NegationOverflow(W32))`. POST-FIX: `None`.
///
/// The positive control is the same VC against a MIR whose local is spelled `y`: it must
/// still certify, so this is a name-boundary decline and not a blanket one.
#[test]
fn a_versioned_mir_local_name_can_never_authenticate_a_bare_negation_subject() {
    let formula = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-2147483648)));
    let vc = VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
        function: "crate::neg".into(),
        location: SourceSpan::default(),
        obligation: authed_body(&formula),
        formula,
        contract_metadata: None,
    };
    assert_eq!(
        safety_vc_is_faithful_formula_aware(&named_neg_func("y", 32), &vc).map(|(k, _)| k),
        Some(SafetyVcKind::NegationOverflow(SWidth::W32)),
        "the honest MIR — a local actually spelled `y` — must still certify"
    );
    assert_eq!(
        safety_vc_is_faithful_formula_aware(&named_neg_func("y#s3_0", 32), &vc).map(|(k, _)| k),
        None,
        "a MIR local named `y#s3_0` supplied the subject for a certificate about `y`: the \
         `#` version stamp is minted by `generate/path_defs.rs:859` onto FORMULA variables \
         and never by `place_to_var_name`, so stripping it on the MIR side merges two \
         distinct place names"
    );
}

// ---------------------------------------------------------------------------------
// 13. THE AUTHENTICATED-OBLIGATION FIELD (2026-07-31, the vertical-slice CONSUMER half).
//     The recorded `vc.obligation` REPLACES the wrapper peel for the div/rem and negation
//     arms — but only after `reconstruct_obligation(rec) == vc.formula` authenticates it
//     against the formula. A TRUTHFUL record certifies exactly as the peel does; a HOSTILE
//     record (the field claims one core, the formula asserts a DIFFERENT violable one) is
//     DECLINED by that equate, never certified and never silently ignored. Each test is
//     falsified by reverting the named check IN PLACE — the pre-fix mint is quoted.
// ---------------------------------------------------------------------------------

/// The emitter's own conjoining wrapper: hypotheses first, the violation body LAST — the
/// single shape `ObligationWrapper::ConjoinFactsLast` records and `reconstruct_obligation`
/// replays. A benign parameter-domain hypothesis stands in for the block-defs / guards /
/// preconditions the real emitter conjoins.
fn conjoin_hyp_last(body: Formula) -> (Formula, Formula) {
    let hyp = Formula::Ge(Box::new(var("p")), Box::new(Formula::Int(0)));
    (hyp.clone(), Formula::And(vec![hyp, body]))
}

/// TRUTHFUL RECORD CERTIFIES, HOSTILE RECORD DECLINES — div/rem (ARM 1, body-only) and
/// negation (ARM 2, body + subject + width).
///
/// For each arm three VCs share ONE `formula` (the emitter's `And([hyp, <real core>])`):
///   * `obligation: None`        — the legacy dumps; the peel certifies (the BASELINE).
///   * `obligation: Some(truthful)` — `body = <real core>`, wrappers reproduce `formula`;
///     `reconstruct_obligation == formula`, so it certifies IDENTICALLY to the peel.
///   * `obligation: Some(hostile)`  — `body = <a DIFFERENT is_core-valid predicate>`, so
///     `reconstruct_obligation(rec) != formula`. `select_obligation` returns `Decline` and
///     the arm fails closed. The negation hostile is the [10]-class WIDTH forgery: the
///     field claims `Eq(y, i8::MIN)` (width 8) while the formula asserts `Eq(y, i32::MIN)`
///     (width 32) — a benign narrow claim standing in front of a wide violation.
///
/// FALSIFICATION (constraint 4), verified by reverting IN PLACE:
///   * Relax `select_obligation`'s equate to `if true` (or route its `Decline` arm to the
///     peel): the hostile div VC then certifies `Some(DivByZero)` off the field's
///     `Eq(w, 0)` body, and the hostile negation VC certifies `Some(NegationOverflow(W32))`
///     off the peel's real `Eq(y, i32::MIN)` — the mint this test forbids.
#[test]
fn a_truthful_recorded_obligation_certifies_and_a_hostile_one_is_declined() {
    // ---- ARM 1: div-by-zero (body-only) --------------------------------------------
    let divisor = || var("z");
    let real_div_core = Formula::Eq(Box::new(divisor()), Box::new(Formula::Int(0)));
    let (div_hyp, div_formula) = conjoin_hyp_last(real_div_core.clone());
    let div_vc = |obligation: Option<trust_types::ObligationRecord>| VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::probe".into(),
        location: SourceSpan::default(),
        formula: div_formula.clone(),
        contract_metadata: None,
        obligation,
    };
    let div_truthful = trust_types::ObligationRecord {
        body: real_div_core.clone(),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![div_hyp.clone()],
        }],
        subject: None,
        width: None,
    };
    // The field claims a DIFFERENT divisor `w` — benign against `z`'s real violation.
    let div_hostile = trust_types::ObligationRecord {
        body: Formula::Eq(Box::new(var("w")), Box::new(Formula::Int(0))),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![div_hyp.clone()],
        }],
        subject: None,
        width: None,
    };

    // FIELD-REQUIRED (2026-08-01): the peel is deleted, so there is no `obligation: None`
    // baseline; a TRUTHFUL record is the ONLY thing that certifies, and it certifies to this
    // kind's own `SafetyVcKind`.
    assert_eq!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &div_vc(Some(div_truthful)))
            .map(|(k, _)| k),
        Some(SafetyVcKind::DivByZero),
        "a TRUTHFUL recorded obligation (reconstruct == formula) must certify DivByZero"
    );
    assert!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &div_vc(Some(div_hostile))).is_none(),
        "a HOSTILE recorded obligation (field says `Eq(w,0)`, formula asserts the violable \
         `Eq(z,0)`) reconstructs to a formula OTHER than `vc.formula`, so the authentication \
         must DECLINE; reverting the `reconstruct_obligation == vc.formula` equate mints \
         `Some(DivByZero)` off the field body"
    );

    // ---- ARM 2: negation overflow (body + subject + width) -------------------------
    let neg_func = || named_neg_func("y", 32);
    let real_neg_core =
        Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-2147483648)));
    let (neg_hyp, neg_formula) = conjoin_hyp_last(real_neg_core.clone());
    let neg_vc = |obligation: Option<trust_types::ObligationRecord>| VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
        function: "crate::neg".into(),
        location: SourceSpan::default(),
        formula: neg_formula.clone(),
        contract_metadata: None,
        obligation,
    };
    let neg_truthful = trust_types::ObligationRecord {
        body: real_neg_core.clone(),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![neg_hyp.clone()],
        }],
        subject: Some(var("y")),
        width: Some(32),
    };
    // The [10]-class WIDTH forgery: the field's body claims the i8 MIN threshold.
    let neg_hostile = trust_types::ObligationRecord {
        body: Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(-128))),
        wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
            facts: vec![neg_hyp.clone()],
        }],
        subject: Some(var("y")),
        width: Some(8),
    };

    assert_eq!(
        safety_vc_is_faithful_formula_aware(&neg_func(), &neg_vc(Some(neg_truthful)))
            .map(|(k, _)| k),
        Some(SafetyVcKind::NegationOverflow(SWidth::W32)),
        "a TRUTHFUL recorded negation obligation must certify NegationOverflow(W32)"
    );
    assert!(
        safety_vc_is_faithful_formula_aware(&neg_func(), &neg_vc(Some(neg_hostile))).is_none(),
        "a HOSTILE recorded negation obligation (field says the width-8 `Eq(y,-128)`, formula \
         asserts the width-32 `Eq(y,-2147483648)`) reconstructs to a DIFFERENT formula, so the \
         authentication must DECLINE; reverting the equate mints `Some(NegationOverflow(W32))` \
         off the peel's real core"
    );
}

/// A recorded obligation that FAILS to authenticate never falls back to the peel — the
/// fail-closed disposition constraint 3 mandates. Here the peel WOULD certify (the formula
/// carries a real, region-selected div-by-zero), yet a `Some(obligation)` whose `body`
/// disagrees with `formula` makes the arm DECLINE rather than silently ignore the field.
///
/// This is the precise hole a "fall back to the peel on any `Some`" design would leave: a
/// hostile fixture pairs a benign `obligation` with a violable `formula` and, if the field
/// were merely advisory, the peel would mint anyway. Falsified by changing
/// `ObligationSelection::Decline => return None` to fall through to the peel.
#[test]
fn an_unfaithful_recorded_obligation_declines_it_does_not_fall_back_to_the_peel() {
    let real_core = Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0)));
    let (hyp, formula) = conjoin_hyp_last(real_core);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "crate::probe".into(),
        location: SourceSpan::default(),
        formula: formula.clone(),
        contract_metadata: None,
        // A record whose wrappers do NOT reproduce `formula` (an EXTRA fact that is not in
        // the formula) — reconstruct != formula.
        obligation: Some(trust_types::ObligationRecord {
            body: Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0))),
            wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
                facts: vec![hyp, Formula::Ge(Box::new(var("q")), Box::new(Formula::Int(0)))],
            }],
            subject: None,
            width: None,
        }),
    };
    // CONTROL (field-required, 2026-08-01): the SAME formula with a TRUTHFUL record (body =
    // the real core, wrappers reproduce `formula` exactly) certifies — so the decline below
    // is the authentication rejecting the unfaithful record, not a formula nothing certifies.
    let truthful = VerificationCondition {
        obligation: Some(trust_types::ObligationRecord {
            body: Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(0))),
            wrappers: vec![trust_types::ObligationWrapper::ConjoinFactsLast {
                facts: vec![Formula::Ge(Box::new(var("p")), Box::new(Formula::Int(0)))],
            }],
            subject: None,
            width: None,
        }),
        ..vc.clone()
    };
    assert!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &truthful).is_some(),
        "control: a TRUTHFUL record (reconstruct == formula) must certify, else the test \
         proves nothing"
    );
    assert!(
        safety_vc_is_faithful_formula_aware(&probe_func(), &vc).is_none(),
        "a recorded-but-unfaithful obligation must DECLINE (reconstruct != formula), never \
         fall back to a peel; the peel is deleted, so the field is the only authority"
    );
}

// ---------------------------------------------------------------------------------
// [REMOVED 2026-08-01] `mirsem_corpus_census` was the `#[ignore]`d measurement harness. Its
// per-shape tallies (`emitted_obligation_body` bucketed by uadd/umul/bounds/negation shape)
// were computed with the now-deleted wrapper-inverse peel, so the harness cannot compile
// once the peel is gone. It never ran in the suite (`#[ignore]`), and the COST numbers it
// re-derived were peel-mechanism census figures, not live-certifier soundness assertions.
// ---------------------------------------------------------------------------------
