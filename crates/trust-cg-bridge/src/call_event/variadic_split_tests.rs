// call_event/variadic_split_tests.rs — `check_placement` BLOCKS a variadic
// signature whose fixed/anonymous split is unknown, and grades every other
// signature exactly as before. The gate-level tests (a real object, a kernel
// twin) are `tests/call_event_gate.rs`'s `*_is_blocked`; these pin the
// placement check itself, which the gate's earlier pre-pass otherwise hides.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::value::{BlockId, FuncId, FuncTyId};
use trust_ir::{CallingConv, Function, Module, Ty as IrTy};

use super::{
    FnPlacement, Grade, ParamPlace, PlacementRefusal, ReturnPlace, ScalarPlace, Signature,
    check_placement,
};

/// Every convention trust-ir names. The match makes a new variant a compile
/// error here until it is listed.
const ALL_CONVS: [CallingConv; 12] = [
    CallingConv::C,
    CallingConv::Fast,
    CallingConv::Cold,
    CallingConv::Rust,
    CallingConv::Swift,
    CallingConv::CUnwind,
    CallingConv::SysV64,
    CallingConv::Win64,
    CallingConv::Aapcs,
    CallingConv::EfiApi,
    CallingConv::VectorCall,
    CallingConv::RustCold,
];

fn _every_convention_is_listed(conv: CallingConv) {
    match conv {
        CallingConv::C
        | CallingConv::Fast
        | CallingConv::Cold
        | CallingConv::Rust
        | CallingConv::Swift
        | CallingConv::CUnwind
        | CallingConv::SysV64
        | CallingConv::Win64
        | CallingConv::Aapcs
        | CallingConv::EfiApi
        | CallingConv::VectorCall
        | CallingConv::RustCold => {}
    }
}

fn is_rust_abi(conv: CallingConv) -> bool {
    matches!(conv, CallingConv::Rust | CallingConv::RustCold)
}

/// The conventions with a variadic form, listed here independently of the
/// gate's own `conv_has_variadic_form`: rustc's `ExternAbi::supports_varargs`
/// (`C`, `C-unwind`, `sysv64`, `win64`, `aapcs`, `efiapi`). fastcc and coldcc
/// do not support varargs (LLVM LangRef), and clang admits no variadic call
/// under swiftcall or vectorcall.
fn has_variadic_form(conv: CallingConv) -> bool {
    matches!(
        conv,
        CallingConv::C
            | CallingConv::CUnwind
            | CallingConv::SysV64
            | CallingConv::Win64
            | CallingConv::Aapcs
            | CallingConv::EfiApi
    )
}

/// `(u64 x fixed[, ...]) -> u64` and the all-register P of its fixed part.
fn sig_and_place(fixed: usize, vararg: bool) -> (Signature, FnPlacement) {
    let params = vec![IrTy::U64; fixed];
    let place = FnPlacement {
        params: (0..fixed).map(|r| ParamPlace::Scalar(ScalarPlace::gpr(r as u8, 64))).collect(),
        ret: ReturnPlace::Scalar(ScalarPlace::gpr(0, 64)),
    };
    ((params, vec![IrTy::U64], vararg), place)
}

#[test]
fn an_unknown_split_is_blocked_under_every_convention_and_both_roles() {
    let module = Module::new("variadic_split");
    for conv in ALL_CONVS {
        for is_definition in [false, true] {
            // No fixed parameter: unknown under EVERY convention.
            let (sig, place) = sig_and_place(0, true);
            let e = check_placement(&module, &sig, conv, &place, is_definition).unwrap_err();
            let PlacementRefusal::UnknownSplit(why) = &e else {
                panic!("{conv:?}: `(...)` was not blocked: {e:?}")
            };
            assert!(why.contains("no fixed parameter"), "{why}");
            let g = e.grade("`g`", |_| unreachable!("an unknown split is never Unknown"));
            assert_eq!(g.grade, Grade::Refuted, "{conv:?}");
            assert!(g.detail.starts_with("`g` is declared `(...)`"), "{}", g.detail);

            // A stated fixed prefix: unknown only under a convention with no
            // variadic form.
            let (sig, place) = sig_and_place(1, true);
            let e = check_placement(&module, &sig, conv, &place, is_definition).unwrap_err();
            if !has_variadic_form(conv) {
                let PlacementRefusal::UnknownSplit(why) = &e else {
                    panic!(
                        "{conv:?}: a variadic signature with no variadic form was not blocked: {e:?}"
                    )
                };
                let named = if is_rust_abi(conv) {
                    "the Rust ABI has no variadic form"
                } else {
                    "which has no variadic form"
                };
                assert!(why.contains(named), "{conv:?}: {why}");
                assert_eq!(e.grade("`g`", |e| e).grade, Grade::Refuted);
            } else {
                // Known split: graded as before, Unknown with the word "variadic".
                assert_eq!(e, PlacementRefusal::Unplaced("variadic".into()), "{conv:?}");
                let g = e.grade("`g`", |e| format!("does not place: {e}"));
                assert_eq!(
                    (g.grade, g.detail.as_str()),
                    (Grade::Unknown, "does not place: variadic")
                );
            }
        }
    }
}

#[test]
fn a_signature_that_is_not_variadic_is_checked_as_before() {
    let module = Module::new("variadic_split");
    for conv in ALL_CONVS {
        // P matches: placed, whatever the convention (the gate does not read it here).
        let (sig, place) = sig_and_place(2, false);
        assert_eq!(check_placement(&module, &sig, conv, &place, false), Ok(()), "{conv:?}");
        // No parameter at all is an ordinary nullary signature, not `(...)`.
        let (sig, place) = sig_and_place(0, false);
        assert_eq!(check_placement(&module, &sig, conv, &place, false), Ok(()), "{conv:?}");
        // A mismatch keeps its Unknown reason.
        let (sig, _) = sig_and_place(2, false);
        let (_, place1) = sig_and_place(1, false);
        assert_eq!(
            check_placement(&module, &sig, conv, &place1, false),
            Err(PlacementRefusal::Unplaced("2 parameter(s) but P places 1".into())),
            "{conv:?}"
        );
    }
}

/// The gate blocks AT LEAST every signature trust-cg's adapter refuses as an
/// unsigned variadic callee (OD-55), so the two cannot drift apart in the
/// direction that ships a guessed split; it also blocks `RustCold` and the
/// other conventions with no variadic form, which the adapter does not name.
#[test]
fn the_gate_blocks_every_signature_trust_cg_refuses_as_unsigned() {
    let module = Module::new("variadic_split");
    for conv in ALL_CONVS {
        for fixed in [0usize, 1, 2] {
            for vararg in [false, true] {
                let (sig, place) = sig_and_place(fixed, vararg);
                let mut callee =
                    Function::new(FuncId::new(0), "g", FuncTyId::new(0), BlockId::new(0));
                callee.calling_conv = conv;
                let func_ty = trust_ir::ty::FuncTy {
                    params: sig.0.clone(),
                    returns: sig.1.clone(),
                    is_vararg: vararg,
                    abi: None,
                };
                let refused = trust_cg_lower::reject_unsigned_variadic_callee(&callee, &func_ty);
                let blocked = matches!(
                    check_placement(&module, &sig, conv, &place, false),
                    Err(PlacementRefusal::UnknownSplit(_))
                );
                if refused.is_err() {
                    assert!(
                        blocked,
                        "{conv:?} fixed={fixed} vararg={vararg}: trust-cg refuses, the gate does not block"
                    );
                }
                // And nothing outside the named shapes is blocked.
                assert_eq!(
                    blocked,
                    vararg && (fixed == 0 || !has_variadic_form(conv)),
                    "{conv:?} fixed={fixed} vararg={vararg}"
                );
            }
        }
    }
}
