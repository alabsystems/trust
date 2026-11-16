use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Sort, SourceSpan, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::build_semantic_guard_map;

/// `fn f(x: T) { _2 = callee(copy x) }` — one call, one successor block.
fn wrapping_neg_fn(ty: Ty, callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty, name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn successor_guards(func: &VerifiableFunction) -> Vec<Formula> {
    build_semantic_guard_map(func).get(&BlockId(1)).cloned().unwrap_or_default()
}

#[test]
fn signed_i128_wrapping_neg_gets_exact_ite_definition() {
    let func = wrapping_neg_fn(Ty::i128(), "core::num::<impl i128>::wrapping_neg");
    let x = || Box::new(Formula::Var("x".into(), Sort::Int));
    let min = || Box::new(Formula::Int(i128::MIN));
    let expected = Formula::Eq(
        Box::new(Formula::Var("n#s0_t".into(), Sort::Int)),
        Box::new(Formula::Ite(
            Box::new(Formula::Eq(x(), min())),
            min(),
            Box::new(Formula::Sub(Box::new(Formula::Int(0)), x())),
        )),
    );
    assert!(
        successor_guards(&func).contains(&expected),
        "signed wrapping_neg must pin dest == ite(x == MIN, MIN, -x) at FULL i128 width: {:?}",
        successor_guards(&func)
    );
}

#[test]
fn bare_ssa_variant_renames_versioned_call_dest_to_bare() {
    // The wrapping_neg guard names its subject `n#s0_t`; the SSA local `n`
    // (single call-dest write) makes the bare-renamed copy an identity —
    // this is what lets the fact bind a callsite ¬P[σ]'s bare `n`.
    let func = wrapping_neg_fn(Ty::i64(), "core::num::<impl i64>::wrapping_neg");
    let guards = successor_guards(&func);
    let versioned = guards
        .iter()
        .find(|g| format!("{g:?}").contains("n#s0_t"))
        .expect("wrapping_neg fact present");
    let variant = super::bare_ssa_guard_variant(&func, versioned)
        .expect("SSA call dest must yield a bare variant");
    let repr = format!("{variant:?}");
    assert!(
        repr.contains("\"n\"") && !repr.contains("n#"),
        "variant must be fully bare-renamed: {repr}"
    );
}

#[test]
fn unsigned_u128_wrapping_neg_fails_closed() {
    // 2^128 - x needs a modulus Formula::Int cannot represent — no fact.
    let func = wrapping_neg_fn(Ty::u128(), "core::num::<impl u128>::wrapping_neg");
    assert!(
        successor_guards(&func).iter().all(|f| !format!("{f:?}").contains("n#")),
        "u128 wrapping_neg must emit NO dest fact (fail-closed)"
    );
}

#[test]
fn user_defined_wrapping_neg_is_not_modeled() {
    let func = wrapping_neg_fn(Ty::i64(), "mymod::wrapping_neg");
    assert!(
        successor_guards(&func).iter().all(|f| !format!("{f:?}").contains("n#")),
        "a user wrapping_neg must NOT be modeled — false value-definition channel"
    );
}

/// `fn f() { _2 = callee(const K) }` — the operand is a width-LESS integer CONSTANT,
/// the shape whose width `operand_ty` has to guess from the VALUE.
fn wrapping_neg_const_fn(dest_ty: Ty, k: i128, callee: &str) -> VerifiableFunction {
    let mut func = wrapping_neg_fn(dest_ty, callee);
    func.body.arg_count = 0;
    let trust_types::Terminator::Call { args, .. } = &mut func.body.blocks[0].terminator else {
        unreachable!("fixture terminator is a Call")
    };
    *args = vec![Operand::Constant(trust_types::ConstValue::Int(k))];
    func
}

/// ADVERSARIAL (R5): `wrapping_neg`'s EXACT value model must decline when the receiver's
/// DECLARED width (callee path) disagrees with the operand's resolved width.
///
/// WITNESS — a live false proof before the agreement check:
///
/// ```ignore (illustrative)
/// const K: i128 = i64::MIN as i128;
/// let n = K.wrapping_neg();          // truly +2^63
/// ```
///
/// `operand_ty`'s `ConstValue::Int(v)` arm picks the width from the VALUE (`i64` when `v`
/// fits `i64`, else `i128`) because trust-types' `Int(i128)` carries no width. `i64::MIN`
/// fits `i64`, so an `i128` receiver resolved to width 64 and the model emitted
/// `ite(x == i64::MIN, i64::MIN, 0 - x)` — asserting the NEGATIVE `i64::MIN` where the
/// true `i128` result is the POSITIVE `+2^63`. Because this is an EXACT VALUE definition
/// (not an inequality, where the wider width would be the safe resolution), only exact
/// agreement is admissible.
///
/// A/B: this test FAILS on the unfixed recognizer.
#[test]
fn wrapping_neg_declines_when_the_path_width_disagrees_with_the_operand() {
    let func =
        wrapping_neg_const_fn(Ty::i128(), i64::MIN as i128, "core::num::<impl i128>::wrapping_neg");
    let guards = successor_guards(&func);
    assert!(
        guards.iter().all(|f| !format!("{f:?}").contains("n#")),
        "an i128 receiver whose width-less constant operand resolves to i64 must emit NO \
         wrapping_neg value fact — the i64 model asserts the NEGATIVE i64::MIN where the true \
         i128 result is +2^63: {guards:?}"
    );
}

/// Positive control: exact width agreement must still emit the fact, so the fix above
/// cannot "work" by disabling the model.
#[test]
fn wrapping_neg_still_models_a_width_agreeing_constant_receiver() {
    let func = wrapping_neg_const_fn(Ty::i64(), -5, "core::num::<impl i64>::wrapping_neg");
    let guards = successor_guards(&func);
    assert!(
        guards.iter().any(|f| format!("{f:?}").contains("n#")),
        "an i64 receiver with an i64-resolving constant must keep its exact model: {guards:?}"
    );
}
