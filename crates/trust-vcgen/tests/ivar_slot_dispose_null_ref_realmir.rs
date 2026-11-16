// Real-MIR cover for the proof-loss class "typed CHC refutes its own encoding"
// (2026-10-02): aterm-objc `IvarSlot::<T>::dispose`.
//
//   pub struct IvarSlot<T> { initialized: bool, value: MaybeUninit<T> }
//   pub unsafe fn dispose(slot: *mut Self) {
//       let initialized = unsafe { (*slot).initialized };  // null check on `*slot`
//       if !initialized { return; }
//       unsafe {
//           (*slot).initialized = false;                    // null check on `*slot`
//           core::ptr::drop_in_place((*slot).value.as_mut_ptr()); // "null reference produced"
//       }
//   }
//
// The `&mut (*slot).value` borrow carries rustc's "null reference produced"
// assert. It is TRUE: the read of `(*slot).initialized` already passed the
// null-dereference check on the same `slot`, and `IvarSlot<T>` holds a `bool`,
// so it is never a ZST and that check fires on null.
//
// The seal (321aaeda7) "proved" the row, but vacuously: its formula read
// `initialized == slot*.0` and ALSO stated the later store as `slot*.0 == false`,
// so the branch taken (`initialized`) contradicted it — the P1 stale-read false
// proof 2aacba975d closed. Its clean-kernel certificate is that contradiction
// and nothing else: two hypotheses `p = 0` and `¬(p = 0)` over one abstracted
// proposition. Main's encoding is honest and SATISFIABLE, because it lacks
// three TRUE facts:
//
//  * F1 (fixed here): each check casts `slot` with `copy _1 as *const ()
//    (PtrToPtr)`, and `*mut IvarSlot<T>` failed the thin-pointer test (the
//    `MaybeUninit<T>` tail walked down to `T`'s `Unsupported` leaf), so no
//    `dest == slot` was emitted and every check addressed its own free integer.
//  * F2 (fixed here): the passed check is `!(addr == 0 && size_of::<IvarSlot<T>>()
//    != 0)`, and `size_of` lowered to an opaque symbol (the width-interned
//    `__trust_opaque_scalar_u64` when this was found; its own site or key since
//    OPAQUE-SCALAR-ID-1), which the model could set to 0.
//  * F3 (OPEN): the store `(*slot).initialized = false` rebinds the NAME `slot`
//    (`place_names_overlap` counts `slot*.0` as overlapping its ancestor `slot`:
//    `*` is a projection-segment lead like `.`),
//    so the checks after the store read `slot#s8_0`, a value unrelated to the
//    `slot#e` the read's check constrained. A store through `*slot` cannot change
//    `slot`; the frame fact is the remaining gap, and it lives in the versioning
//    relation behind the P1–P4 false proofs, so it is not taken here.
//
// Fixtures: `-Ztrust-dump=mir-only:<dir>` from the main stage2 compiler
// (d36c551fac), `--edition 2024 --crate-type lib`, ub-checks at their default
// (debug assertions on). Spans are rewritten to `src/lib.rs`.
//
//  * `value_ptr`: the read, the early return, then `(*slot).value.as_mut_ptr()`
//    with NO store between: F1 + F2 are enough and the row must be UNSAT (see
//    `is_unsat` for the ay certification gap that keeps it from `Proved`), and
//    it must be REFUTED again once the null check is not recognized.
//  * `null_ref`: `dispose` itself (above): still refuted (F3), and UNSAT once
//    `slot` is framed across the store.
//  * `zst_twin`: `Twin<T> { tag: PhantomData<fn() -> T>, value: MaybeUninit<T> }`
//    with the same reads; `T = ()` makes it a ZST, so the earlier check does NOT
//    establish `slot != null` and the row must stay REFUTED.
//  * `opaque_leak`: the `IvarSlot<T>` null check, then
//    `if const { size_of::<T>() } == 0 { panic!() }`. When this was found both
//    sizes (and the alignment check's `ALIGN`) were the SAME width-interned
//    symbol; F2 must not make the `T = ()` panic unreachable.
//
// Naming (merged 2026-10-08 onto OPAQUE-SCALAR-ID-1): the branch's per-pointer-local
// rename of the checks' constants (`__trust_ubcheck_{align,size}_of_l{p}`) is gone;
// every such constant is named by trust-types' one scheme, its MIR site or its
// extractor key (item + normalized generic arguments). `field_vs_whole`
// (`tests/fixtures/opaque_scalar_identity/`, the B' probe) pins why a per-LOCAL key
// was wrong: `CheckAlignment` follows projections, so one pointer local is checked
// against two different `align_of`s.
use trust_types::{
    AssertMessage, Formula, Sort, Terminator, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/ivar_slot_dispose_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// The row's query is UNSATISFIABLE by in-process ay: either a certified proof,
/// or ay's own UNSAT that its strict proof check withheld.
///
/// The second arm is an ay certification gap, not this encoding's: every
/// rustc null check asserts `is_ok = Not(should_throw)` with `expected: true`,
/// so the row's goal is `!is_ok` over a defined `is_ok == !should_throw`, and
/// ay solves the minimal `!(p == 0), g == (p == 0), n == !g, !n` in
/// preprocessing but rejects its own proof ("step t3 uses unverified trust
/// rule", 0 conflicts). When ay certifies that step this arm is unused.
fn is_unsat(result: &VerificationResult) -> bool {
    match result {
        VerificationResult::Proved { .. } => true,
        VerificationResult::Unknown { reason, .. } => {
            reason.contains("self-check-rejected") && reason.contains("unverified-trust-rule")
        }
        _ => false,
    }
}

fn is_refuted(result: &VerificationResult) -> bool {
    matches!(result, VerificationResult::Failed { .. })
}

/// The single "null reference produced" row (rustc's borrow-side null check).
fn null_reference_row(func: &VerifiableFunction) -> VerificationCondition {
    let rows: Vec<VerificationCondition> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message } if message.contains("null reference"))
        })
        .collect();
    assert_eq!(rows.len(), 1, "one null-reference row; got {rows:#?}");
    rows.into_iter().next().unwrap()
}

/// Every right-hand side `rhs` of an `Eq(Var(name), rhs)` conjunct of `formula`,
/// flattened through `And`.
fn defs_of<'a>(formula: &'a Formula, name: &str, out: &mut Vec<&'a Formula>) {
    match formula {
        Formula::And(parts) => parts.iter().for_each(|p| defs_of(p, name, out)),
        Formula::Eq(lhs, rhs) if lhs.var_name() == Some(name) => out.push(rhs),
        _ => {}
    }
}

/// The ZST-test temporaries (`z = Ne(size_of::<P>(), 0)`) of the
/// null-dereference checks, by local name.
fn zst_test_temps(func: &VerifiableFunction) -> Vec<String> {
    let mut temps = Vec::new();
    for block in &func.body.blocks {
        if !matches!(
            &block.terminator,
            Terminator::Assert { msg: AssertMessage::NullPointerDereference, .. }
        ) {
            continue;
        }
        for stmt in &block.stmts {
            if let trust_types::Statement::Assign {
                place,
                rvalue:
                    trust_types::Rvalue::BinaryOp(
                        trust_types::BinOp::Ne,
                        trust_types::Operand::Constant(trust_types::ConstValue::OpaqueScalar {
                            ..
                        }),
                        _,
                    ),
                ..
            } = stmt
            {
                temps.push(format!("_{}", place.local));
            }
        }
    }
    temps
}

/// The `copy _1 as *const () (PtrToPtr)` destinations of the pointer checks.
fn slot_casts(func: &VerifiableFunction) -> Vec<String> {
    let mut casts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let trust_types::Statement::Assign {
                place,
                rvalue:
                    trust_types::Rvalue::Cast(
                        trust_types::Operand::Copy(src),
                        trust_types::Ty::RawPtr { pointee, .. },
                    ),
                ..
            } = stmt
                && src.local == 1
                && src.projections.is_empty()
                && matches!(pointee.as_ref(), trust_types::Ty::Unit)
            {
                casts.push(format!("_{}", place.local));
            }
        }
    }
    casts
}

/// F2: each ZST test is the literal `true` in `vc`, and nothing else defines it.
fn assert_zst_tests_true(func: &VerifiableFunction, vc: &VerificationCondition) {
    let temps = zst_test_temps(func);
    assert!(!temps.is_empty(), "the fixture has a null-dereference check");
    for temp in &temps {
        let mut defs = Vec::new();
        defs_of(&vc.formula, temp, &mut defs);
        assert!(!defs.is_empty(), "{temp} must be defined in the row: {:?}", vc.formula);
        assert!(
            defs.iter().all(|rhs| matches!(rhs, Formula::Bool(true))),
            "{temp} (size_of::<IvarSlot<T>>() != 0) must be defined `true` and only `true`, \
             never through the shared opaque size symbol: {defs:?}"
        );
    }
}

/// F1: the names each `slot as *const ()` cast is defined as, per cast. A cast
/// may carry one definition per spelling of the same value (`slot#e` and the
/// entry-bucket `slot`, tied by `slot#e == slot`).
fn cast_targets(func: &VerifiableFunction, vc: &VerificationCondition) -> Vec<Vec<String>> {
    slot_casts(func)
        .iter()
        .map(|cast| {
            let mut defs = Vec::new();
            defs_of(&vc.formula, cast, &mut defs);
            assert!(!defs.is_empty(), "{cast} must be defined: {:?}", vc.formula);
            defs.iter()
                .map(|rhs| match rhs.var_name() {
                    Some(name) if name == "slot" || name.starts_with("slot#") => name.to_string(),
                    _ => panic!("{cast} must be defined as `slot`: {defs:?}"),
                })
                .collect()
        })
        .collect()
}

/// A spelling of `slot`'s ENTRY value.
fn is_entry_slot(name: &str) -> bool {
    name == "slot" || name == "slot#e"
}

/// Relabel every null-dereference assert so the ZST test is no longer recognized.
fn without_null_check_kind(mut func: VerifiableFunction) -> VerifiableFunction {
    for block in &mut func.body.blocks {
        if let Terminator::Assert { msg, .. } = &mut block.terminator
            && matches!(msg, AssertMessage::NullPointerDereference)
        {
            *msg = AssertMessage::MisalignedPointerDereference;
        }
    }
    func
}

#[test]
fn null_reference_after_a_passed_null_check_is_unsat() {
    let func = load("value_ptr");
    let vc = null_reference_row(&func);
    assert_zst_tests_true(&func, &vc);
    let targets = cast_targets(&func, &vc);
    assert_eq!(targets.len(), 4, "two alignment, one null, one borrow check: {targets:?}");
    assert!(
        targets.iter().flatten().all(|t| is_entry_slot(t)),
        "every check must address the one entry value of `slot`: {targets:?}"
    );
    let result = verdict(&vc);
    assert!(
        is_unsat(&result),
        "the read of `(*slot).initialized` passed the null check on a non-ZST pointee, so \
         `&mut (*slot).value` cannot be null; got {result:?}\nformula: {:?}",
        vc.formula
    );
}

#[test]
fn the_proof_comes_from_the_null_check_not_from_a_contradiction() {
    // With the null-dereference asserts relabeled (so the ZST test is no longer
    // recognized) the same row is NOT proved: the proof above rests on the
    // passed check, not on a contradictory path prefix as the seal's did.
    let func = without_null_check_kind(load("value_ptr"));
    let vc = null_reference_row(&func);
    let result = verdict(&vc);
    assert!(
        is_refuted(&result),
        "without the ZST test the passed check says only `slot != null OR size == 0`; \
         got {result:?}\nformula: {:?}",
        vc.formula
    );
}

#[test]
fn dispose_needs_only_the_pointer_frame_across_its_store() {
    let func = load("null_ref");
    let vc = null_reference_row(&func);
    assert_zst_tests_true(&func, &vc);
    let targets = cast_targets(&func, &vc);
    assert_eq!(targets.len(), 6, "three alignment, two null, one borrow check: {targets:?}");
    // Before the store every check addresses `slot#e`; after it, `slot` is
    // re-versioned (F3), so the two checks below the store address another name.
    let (pre, post): (Vec<&Vec<String>>, Vec<&Vec<String>>) =
        targets.iter().partition(|names| names.iter().all(|t| is_entry_slot(t)));
    assert_eq!(pre.len(), 4, "the read's and the store's checks: {targets:?}");
    assert_eq!(post.len(), 2, "the alignment and borrow checks after the store: {targets:?}");
    assert!(
        post.iter().all(|names| names.iter().all(|t| !is_entry_slot(t))),
        "after the store `slot` is re-versioned: {targets:?}"
    );

    // F3 tripwire: still refuted. If this stops refuting, check that F3 landed
    // (a store through `*slot` keeps `slot`) and turn this into a direct pin;
    // anything else proving it is a contradiction to find, as in the seal.
    let result = verdict(&vc);
    assert!(
        is_refuted(&result),
        "`dispose` still lacks the pointer frame across `(*slot).initialized = false`; \
         got {result:?}\nformula: {:?}",
        vc.formula
    );

    // With that frame (`slot` is never assigned and its address is never taken,
    // so every version of it IS its entry value) the row is UNSAT: F1 + F2 + F3
    // are the whole gap.
    let mut frame: Vec<Formula> = Vec::new();
    let mut seen = Vec::new();
    vc.formula.visit(&mut |node| {
        if let Formula::Var(name, _) = node
            && name.starts_with("slot#")
            && name != "slot#e"
            && !name.contains('*')
            && !seen.contains(name)
        {
            seen.push(name.clone());
        }
    });
    assert!(!seen.is_empty(), "the store must have re-versioned `slot`: {:?}", vc.formula);
    for name in &seen {
        frame.push(Formula::Eq(
            Box::new(Formula::Var(name.clone(), Sort::Int)),
            Box::new(Formula::Var("slot#e".to_string(), Sort::Int)),
        ));
    }
    let mut framed = vc.clone();
    frame.push(vc.formula.clone());
    framed.formula = Formula::And(frame);
    let result = verdict(&framed);
    assert!(
        is_unsat(&result),
        "with `slot` framed across the store ({seen:?}) the row must be UNSAT; got {result:?}"
    );
}

#[test]
fn a_possibly_zero_sized_pointee_keeps_the_row_open() {
    let func = load("zst_twin");
    let temps = zst_test_temps(&func);
    assert_eq!(temps.len(), 1, "one null-dereference check on `*slot`: {temps:?}");
    let vc = null_reference_row(&func);
    for temp in &temps {
        let mut defs = Vec::new();
        defs_of(&vc.formula, temp, &mut defs);
        assert!(
            defs.iter().all(|rhs| !matches!(rhs, Formula::Bool(true))),
            "`Twin<()>` is a ZST: {temp} must not be defined `true`: {defs:?}"
        );
    }
    let result = verdict(&vc);
    assert!(
        is_refuted(&result),
        "`Twin<()>` is a ZST, so a null `slot` passes the read's check and the borrow \
         panics; got {result:?}\nformula: {:?}",
        vc.formula
    );
}

#[test]
fn the_zst_test_does_not_constrain_the_shared_size_symbol() {
    let func = load("opaque_leak");
    let temps = zst_test_temps(&func);
    assert_eq!(temps.len(), 1, "one null-dereference check on `*slot`: {temps:?}");
    // `size_of::<T>() == 0` reaches `panic!` for `T = ()`: no row may prove it
    // unreachable. The check's ZST test shares the opaque symbol with that
    // `size_of::<T>()`; constraining the symbol would prove exactly that.
    let vcs = trust_vcgen::generate_vcs(&func);
    let panic_rows: Vec<&VerificationCondition> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic")))
        .collect();
    assert_eq!(panic_rows.len(), 1, "the `size_of::<T>() == 0` panic row: {vcs:#?}");
    for vc in panic_rows {
        for temp in &temps {
            let mut defs = Vec::new();
            defs_of(&vc.formula, temp, &mut defs);
            assert!(
                defs.iter().all(|rhs| matches!(rhs, Formula::Bool(true))),
                "{temp} is decided `true`, never through the opaque symbol: {defs:?}"
            );
        }
        let result = verdict(vc);
        assert!(
            !is_unsat(&result),
            "{:?}: the `T = ()` panic is reachable; got {result:?}\nformula: {:?}",
            vc.kind,
            vc.formula
        );
    }
}

/// The alignment-mask temporaries (`m = Sub(align_of::<P>(), 1)`) of the
/// misaligned-pointer checks, by local name.
fn alignment_mask_temps(func: &VerifiableFunction) -> Vec<String> {
    let mut temps = Vec::new();
    for block in &func.body.blocks {
        if !matches!(
            &block.terminator,
            Terminator::Assert { msg: AssertMessage::MisalignedPointerDereference, .. }
        ) {
            continue;
        }
        for stmt in &block.stmts {
            if let trust_types::Statement::Assign {
                place,
                rvalue:
                    trust_types::Rvalue::BinaryOp(
                        trust_types::BinOp::Sub,
                        trust_types::Operand::Constant(trust_types::ConstValue::OpaqueScalar {
                            ..
                        }),
                        _,
                    ),
                ..
            } = stmt
            {
                temps.push(format!("_{}", place.local));
            }
        }
    }
    temps
}

/// The conjuncts of `formula`, flattened through `And`.
fn conjuncts<'a>(formula: &'a Formula, out: &mut Vec<&'a Formula>) {
    match formula {
        Formula::And(parts) => parts.iter().for_each(|p| conjuncts(p, out)),
        other => out.push(other),
    }
}

fn mentions(formula: &Formula, name: &str) -> bool {
    let mut hit = false;
    formula.visit(&mut |node| {
        if let Formula::Var(v, _) = node
            && v == name
        {
            hit = true;
        }
    });
    hit
}

/// The B symbol (`ConstValue::opaque_scalar_smt_var_name`) of the opaque operand of
/// every statement `pick` selects, in body order. The body is placed on load, so a
/// legacy dump's operands carry their MIR sites.
fn opaque_operand_symbols(
    func: &VerifiableFunction,
    pick: impl Fn(&trust_types::Rvalue) -> bool,
) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let trust_types::Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if !pick(rvalue) {
                continue;
            }
            let trust_types::Rvalue::BinaryOp(_, lhs, _) = rvalue else { continue };
            if let trust_types::Operand::Constant(trust_types::ConstValue::OpaqueScalar {
                width,
                signed,
                origin,
            }) = lhs
            {
                out.push((
                    format!("_{}", place.local),
                    trust_types::ConstValue::opaque_scalar_smt_var_name(*width, *signed, origin),
                ));
            }
        }
    }
    out
}

fn is_sub(rv: &trust_types::Rvalue) -> bool {
    matches!(rv, trust_types::Rvalue::BinaryOp(trust_types::BinOp::Sub, ..))
}

fn is_eq(rv: &trust_types::Rvalue) -> bool {
    matches!(rv, trust_types::Rvalue::BinaryOp(trust_types::BinOp::Eq, ..))
}

/// Every opaque-scalar symbol a conjunct defining `temp` mentions, over every row.
fn symbols_defining(vcs: &[VerificationCondition], temp: &str) -> Vec<String> {
    let mut out = Vec::new();
    for vc in vcs {
        let mut parts = Vec::new();
        conjuncts(&vc.formula, &mut parts);
        for part in parts.into_iter().filter(|p| mentions(p, temp)) {
            part.visit(&mut |node| {
                if let Formula::Var(v, _) = node
                    && v.starts_with(trust_types::OPAQUE_SCALAR_SYMBOL_PREFIX)
                    && !out.contains(v)
                {
                    out.push(v.clone());
                }
            });
        }
    }
    out
}

/// Trust: 2026-10-02 (class-9 review, latent FALSE PROOF). rustc's alignment check
/// on `slot` tests `addr & (align_of::<IvarSlot<T>>() - 1) == 0`, and its `ALIGN`
/// was the width-interned `__trust_opaque_scalar_u64` — the very term the user's
/// `size_of::<T>()` rendered to. On the `T = ()` panic path that symbol is 0, so the
/// passed alignment check said `slot == 0 (mod 2^64)`, and with F1 + F2 the passed
/// null check says `slot != 0`: for any `slot` in `0..2^64` the reachable panic was
/// UNSAT (z3 on the dumped row: UNSAT once `0 <= slot < 2^64` is added; SAT with the
/// pre-F2 ZST test). The branch split the check constants off per pointer local;
/// since the merge onto OPAQUE-SCALAR-ID-1 each is its own site (this legacy dump has
/// no keys), which is the split this test pins: the mask is defined over the check's
/// own symbol, the user's `size_of::<T>()` over another, and the real execution
/// reaches the panic.
#[test]
fn a_reachable_zst_panic_stays_satisfiable_for_an_in_range_pointer() {
    let func = load("opaque_leak");
    let masks = alignment_mask_temps(&func);
    assert_eq!(masks.len(), 1, "one alignment check on `*slot`: {masks:?}");
    let align = opaque_operand_symbols(&func, is_sub);
    assert_eq!(align.len(), 1, "one `align_of::<IvarSlot<T>>() - 1`: {align:?}");
    let user = opaque_operand_symbols(&func, is_eq);
    assert_eq!(user.len(), 1, "one user `size_of::<T>() == 0`: {user:?}");
    let (align_sym, user_sym) = (&align[0].1, &user[0].1);
    assert_ne!(align_sym, user_sym, "the check's ALIGN and the user's size_of are two values");
    let vcs = trust_vcgen::generate_vcs(&func);
    let panic_rows: Vec<&VerificationCondition> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic")))
        .collect();
    assert_eq!(panic_rows.len(), 1, "the `size_of::<T>() == 0` panic row: {vcs:#?}");
    let vc = panic_rows[0];

    // Structure: the mask is defined over the alignment check's own symbol, never the
    // user's; the user's `_2 == (size_of == 0)` is over the user's. The mask's def is
    // the wrapping-`Sub` pair `Implies(.., Eq(_7, ..))`, so the conjuncts that mention
    // it are inspected whole.
    for mask in &masks {
        let mut parts = Vec::new();
        conjuncts(&vc.formula, &mut parts);
        let mask_parts: Vec<&&Formula> = parts.iter().filter(|p| mentions(p, mask)).collect();
        assert!(
            mask_parts.iter().any(|p| mentions(p, align_sym)),
            "{mask} = align_of::<IvarSlot<T>>() - 1 must be defined over the check's own \
             symbol {align_sym}: {:?}",
            vc.formula
        );
        assert!(
            mask_parts.iter().all(|p| !mentions(p, user_sym)),
            "{mask} = align_of::<IvarSlot<T>>() - 1 must not name the user's size_of: \
             {mask_parts:?}"
        );
    }
    let mut user_defs = Vec::new();
    defs_of(&vc.formula, "_2", &mut user_defs);
    assert!(
        !user_defs.is_empty() && user_defs.iter().all(|rhs| mentions(rhs, user_sym)),
        "the user's `size_of::<T>() == 0` is over its own symbol: {user_defs:?}"
    );

    // Semantics: `T = ()` (`size_of::<T>() == 0`) with `slot = 8` — non-null, in
    // range, aligned for `IvarSlot<()>`, whose alignment is 1 — is a real execution
    // reaching the panic. Pinned to it, the row must be REFUTED, never UNSAT. (With
    // one width-interned symbol the alignment check read `size_of - 1` as its mask,
    // so the pin made `8 & (2^64 - 1) == 0` a hypothesis: UNSAT.)
    let pin = |name: &str, value: i128| {
        Formula::Eq(
            Box::new(Formula::Var(name.to_string(), Sort::Int)),
            Box::new(Formula::Int(value)),
        )
    };
    let mut pins: Vec<Formula> = vec![pin(user_sym, 0), pin(align_sym, 1)];
    let mut seen: Vec<String> = Vec::new();
    vc.formula.visit(&mut |node| {
        if let Formula::Var(name, _) = node
            && (name == "slot" || name.starts_with("slot#"))
            && !name.contains('*')
            && !seen.contains(name)
        {
            seen.push(name.clone());
        }
    });
    assert!(!seen.is_empty(), "the row reads `slot`: {:?}", vc.formula);
    for name in &seen {
        pins.push(pin(name, 8));
    }
    let mut pinned = vc.clone();
    pins.push(vc.formula.clone());
    pinned.formula = Formula::And(pins);
    let result = verdict(&pinned);
    assert!(
        is_refuted(&result),
        "`slot = 8`, `size_of::<()>() = 0` reaches the panic ({seen:?}); got {result:?}\n\
         formula: {:?}",
        pinned.formula
    );
}

/// `if const { align_of::<T>() } == 1 { panic!(..) }` panics for `T = u8`: its
/// panic row exists and is neither proved nor kernel-certified.
fn assert_panic_row_open(vcs: &[VerificationCondition], what: &str) {
    let rows: Vec<&VerificationCondition> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic")))
        .collect();
    assert_eq!(rows.len(), 1, "{what}: the `align 1` panic row: {vcs:#?}");
    let result = verdict(rows[0]);
    assert!(
        !matches!(result, VerificationResult::Proved { .. }),
        "{what}: the `T = u8` panic is reachable; got {result:?}"
    );
    assert!(trust_certify::certify_vc(rows[0]).is_none(), "{what}: the panic row was certified");
}

/// `field_vs_whole` (the B' probe, `tests/fixtures/opaque_scalar_identity/rr_chc.rs`):
/// `&(*p).v` is checked against `align_of::<T>()` and the read `(*p).flag` against
/// `align_of::<S<T>>()` — ONE pointer local, two alignment values, because rustc's
/// `CheckAlignment` follows projections for a borrow. The branch's per-local key
/// (`__trust_ubcheck_align_of_l1`) named both alike.
fn field_vs_whole(level: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/opaque_scalar_identity/field_vs_whole_{level}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Legacy dumps carry no keys, so each check's `ALIGN` is its own MIR site: the two
/// masks of one pointer are defined over two symbols, and neither is the user's
/// `align_of::<T>()`.
#[test]
fn one_pointer_checked_against_two_alignments_keeps_two_symbols() {
    for level in ["o0", "o1d"] {
        let func = field_vs_whole(level);
        let masks = alignment_mask_temps(&func);
        assert_eq!(masks.len(), 2, "{level}: two alignment checks of `p`: {masks:?}");
        let vcs = trust_vcgen::generate_vcs(&func);
        let per_mask: Vec<Vec<String>> = masks.iter().map(|m| symbols_defining(&vcs, m)).collect();
        for (mask, syms) in masks.iter().zip(&per_mask) {
            assert_eq!(syms.len(), 1, "{level}: {mask} is defined over one ALIGN: {syms:?}");
        }
        assert_ne!(
            per_mask[0], per_mask[1],
            "{level}: align_of::<T>() and align_of::<S<T>>() are two values: {masks:?}"
        );
        assert_panic_row_open(&vcs, level);
    }
}

/// What the stage-built extractor emits instead: each `ALIGN` KEYED by its item and
/// normalized generic arguments (`opaque_scalar_const_key`). Simulated here on the
/// real body: `&(*p).v`'s check and the user's `align_of::<T>()` get the key of
/// `align_of::<T>`, the `(*p).flag` read's check the key of `align_of::<S<T>>`. One
/// pointer local, two keys, two symbols; one key, one symbol — the scheme keys by
/// (item, pointee type), never by local, and the panic stays reachable.
#[test]
fn keyed_alignments_share_by_pointee_type_never_by_local() {
    const ALIGN_T: &str = "core::mem::SizedTypeProperties::ALIGN@<T>";
    const ALIGN_ST: &str = "core::mem::SizedTypeProperties::ALIGN@<S<T>>";
    const SIZE_ST: &str = "core::mem::SizedTypeProperties::SIZE@<S<T>>";
    let mut func = field_vs_whole("o1d");
    // In body order: the borrow's alignment check (bb0, `Sub`), the null check's
    // `size_of::<S<T>>() != 0` (bb4, `Ne`), the read's alignment check (bb6, `Sub`),
    // the user's `align_of::<T>() == 1` (bb7, `Eq`).
    let keys = [ALIGN_T, SIZE_ST, ALIGN_ST, ALIGN_T];
    let ops = [
        trust_types::BinOp::Sub,
        trust_types::BinOp::Ne,
        trust_types::BinOp::Sub,
        trust_types::BinOp::Eq,
    ];
    let mut next = 0usize;
    for block in &mut func.body.blocks {
        for stmt in &mut block.stmts {
            if let trust_types::Statement::Assign {
                rvalue: trust_types::Rvalue::BinaryOp(op, lhs, _),
                ..
            } = stmt
                && let trust_types::Operand::Constant(
                    c @ trust_types::ConstValue::OpaqueScalar { .. },
                ) = lhs
                && next < keys.len()
            {
                assert_eq!(
                    *op, ops[next],
                    "operand {next} of field_vs_whole is not where expected"
                );
                *c = trust_types::ConstValue::opaque_scalar_const(64, false, keys[next].into());
                next += 1;
            }
        }
    }
    assert_eq!(next, 4, "four opaque `ALIGN`/`SIZE`/`align_of` operands in field_vs_whole");
    let masks = alignment_mask_temps(&func);
    assert_eq!(masks.len(), 2);
    let vcs = trust_vcgen::generate_vcs(&func);
    let per_mask: Vec<Vec<String>> = masks.iter().map(|m| symbols_defining(&vcs, m)).collect();
    let user = opaque_operand_symbols(&func, is_eq);
    assert_eq!(user.len(), 1, "the user's `align_of::<T>() == 1`: {user:?}");
    let sym = |key: &str| {
        trust_types::ConstValue::opaque_scalar_smt_var_name(
            64,
            false,
            &trust_types::OpaqueOrigin::Const { key: key.into() },
        )
    };
    assert_eq!(per_mask[0], vec![sym(ALIGN_T)], "the borrow's check is align_of::<T>()");
    assert_eq!(per_mask[1], vec![sym(ALIGN_ST)], "the read's check is align_of::<S<T>>()");
    assert_eq!(user[0].1, sym(ALIGN_T), "one key, one symbol: a TRUE equality");
    assert_panic_row_open(&vcs, "o1d keyed");
}
