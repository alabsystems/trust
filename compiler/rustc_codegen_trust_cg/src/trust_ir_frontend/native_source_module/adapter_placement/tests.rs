use super::*;

#[test]
fn primitive_adapter_abi_stops_before_stack_float_wide_and_variadic_carriers() {
    let mut signature = FuncTy {
        params: vec![Ty::Ptr, Ty::I8, Ty::U16, Ty::I32, Ty::U64, Ty::Isize, Ty::Usize, Ty::Char],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    };
    let p = flat_placement(&signature).unwrap();
    assert_eq!(p.params[0], ParamPlace::Scalar(ScalarPlace::gpr(0, 64)));
    assert_eq!(p.params[1], ParamPlace::Scalar(ScalarPlace::gpr(1, 8)));
    assert_eq!(p.params[7], ParamPlace::Scalar(ScalarPlace::gpr(7, 32)));
    signature.params.push(Ty::U8);
    assert!(flat_placement(&signature).is_none(), "ninth argument must not guess a register");
    signature.params = vec![Ty::F64];
    assert!(flat_placement(&signature).is_none());
    signature.params = vec![Ty::U64];
    signature.returns = vec![Ty::U128];
    assert!(flat_placement(&signature).is_none());
    signature.returns = vec![];
    signature.is_vararg = true;
    assert!(flat_placement(&signature).is_none());
}
