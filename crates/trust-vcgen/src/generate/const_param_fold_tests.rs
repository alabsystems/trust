use trust_types::{CallableKind, ConstValue};

use super::*;

#[test]
fn const_param_equality_is_unknown_never_definitely_unequal() {
    // v2_const_eq_truth over a ConstParam must return None (verify BOTH
    // branches), NEVER Some(false) — else an equal `N == N` prunes the taken
    // branch and drops its safety obligations (a false PROVE).
    let n =
        ConstValue::ConstParam { index: 1, name: "N".to_string(), width: 64, signed: false };
    let m =
        ConstValue::ConstParam { index: 0, name: "M".to_string(), width: 64, signed: false };
    assert_eq!(v2_const_eq_truth(&n, &n), None, "N == N must be UNKNOWN, not Some(true/false)");
    assert_eq!(v2_const_eq_truth(&n, &m), None, "N == M must be UNKNOWN");
    assert_eq!(
        v2_const_eq_truth(&n, &ConstValue::Int(3)),
        None,
        "N == 3 must be UNKNOWN, not Some(false)"
    );
}

#[test]
fn callable_item_equality_is_unknown_and_identity_never_becomes_a_fact() {
    let first = ConstValue::CallableItem {
        def_path: "fixture::first".to_string(),
        kind: CallableKind::FnDef,
        def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
    };
    let same = first.clone();
    let second = ConstValue::CallableItem {
        def_path: "fixture::second".to_string(),
        kind: CallableKind::FnDef,
        def_path_hash: trust_types::CallableDefPathHash::new(1, 2),
    };
    assert_eq!(v2_const_eq_truth(&first, &same), None);
    assert_eq!(v2_const_eq_truth(&first, &second), None);
    assert_eq!(v2_const_eq_truth(&first, &ConstValue::Unit), None);
}

#[test]
fn const_param_divisor_is_satisfiably_zero_never_provably_nonzero() {
    // v2_divisor_is_zero_formula over a ConstParam divisor must emit the
    // SATISFIABLE `sym == 0`, NOT `Bool(false)` (provably nonzero = false
    // PROVE of `x / N`).
    use trust_types::{Operand, Sort, VerifiableBody, VerifiableFunction};
    let func = VerifiableFunction {
        name: "d".into(),
        def_path: "test::d".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let divisor = Operand::Constant(ConstValue::ConstParam {
        index: 1,
        name: "N".to_string(),
        width: 64,
        signed: false,
    });
    let f = v2_divisor_is_zero_formula(&func, &divisor);
    // Must reference the per-param symbol and be an Eq(..0), NOT Bool(false).
    match f {
        Formula::Eq(lhs, rhs) => {
            assert_eq!(*lhs, Formula::var("__trust_constparam_1_N", Sort::Int));
            assert_eq!(*rhs, Formula::Int(0));
        }
        other => {
            panic!("const-param divisor must yield a satisfiable `sym == 0`, got {other:?}")
        }
    }
}

#[test]
fn const_param_symbol_is_in_freshen_deny_list() {
    // INV-2: the per-param family must be freshened per occurrence on the R1 σ
    // callsite path, so it must be recognized as an aliasing opaque symbol.
    assert!(is_aliasing_opaque_symbol_name("__trust_constparam_1_N"));
    assert!(is_aliasing_opaque_symbol_name("__trust_constparam_0_M"));
    // INV-4: it must NOT be a `__slice_len` (no spurious where-fact).
    assert!(!"__trust_constparam_1_N".ends_with("__slice_len"));
}
