//! Native behavioral controls for widthless integer constants beside typed places.
//!
//! These use the existing bridge/object path and a C caller on Apple AArch64;
//! they establish observed code behavior, without granting proof authority.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::TrustCgCodegenBackend;
use trust_cg_bridge::lower_to_lir;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn int(value: i128) -> Operand {
    Operand::Constant(ConstValue::Int(value))
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn function(name: &str, types: Vec<Ty>, statements: Vec<Statement>) -> VerifiableFunction {
    let return_ty = types[0].clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: types
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: statements,
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn check_native(function: &VerifiableFunction, c_return: &str, c_argument: &str, checks: &str) {
    let lir = lower_to_lir(function).expect("behavioral fixture must lower");
    let object = TrustCgCodegenBackend::host()
        .emit_object(&[lir])
        .expect("behavioral fixture must emit a native object");
    let directory = tempfile::TempDir::new().expect("native fixture directory");
    let object_path = directory.path().join("fixture.o");
    let driver_path = directory.path().join("driver.c");
    let executable_path = directory.path().join("fixture");
    fs::write(&object_path, object).expect("write emitted object");
    fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\n#include <stdio.h>\n\
             extern {c_return} {}({c_argument});\n\
             int main(void) {{\n{checks}\nreturn 0;\n}}\n",
            function.name
        ),
    )
    .expect("write independent C caller");
    let linked = Command::new("cc")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&executable_path)
        .output()
        .expect("invoke native linker");
    assert!(
        linked.status.success(),
        "native link failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let ran = Command::new(&executable_path).output().expect("execute emitted machine code");
    assert!(
        ran.status.success(),
        "native behavioral mismatch ({}): {}{}",
        ran.status,
        String::from_utf8_lossy(&ran.stdout),
        String::from_utf8_lossy(&ran.stderr)
    );
}

#[test]
fn constant_shifted_i8_keeps_its_sign_with_different_count_widths() {
    for count_width in [32, 8, 16, 64] {
        let count_ty = Ty::Int { width: count_width, signed: false };
        let fixture = function(
            "shift_sign",
            vec![Ty::Bool, count_ty.clone(), count_ty, Ty::i8()],
            vec![
                assign(
                    2,
                    Rvalue::BinaryOp(
                        BinOp::BitAnd,
                        copy(1),
                        Operand::Constant(ConstValue::Uint(7, count_width)),
                    ),
                ),
                // The mask makes every input a valid shift at the i8 value width.
                assign(3, Rvalue::BinaryOp(BinOp::Shl, int(1), copy(2))),
                assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(3), int(0))),
            ],
        );
        // Independently specified truth table: 1_i8 << 7 is -128; the
        // other seven masked counts produce positive i8 values.
        check_native(
            &fixture,
            "uint64_t",
            &format!("uint{count_width}_t"),
            "for (unsigned count = 0; count < 256; ++count) {\n\
             unsigned expected = (count % 8 == 7);\n\
             uint64_t got = shift_sign(count);\n\
             if (got != expected) {\n\
             printf(\"count=%u got=%llu expected=%u\\n\", count, (unsigned long long)got, expected);\n\
             return 1; }}",
        );
    }
}

#[test]
fn constant_shifted_i32_keeps_its_sign_with_a_masked_u32_count() {
    let fixture = function(
        "shift_i32_sign",
        vec![Ty::Bool, Ty::u32(), Ty::u32(), Ty::i32()],
        vec![
            assign(
                2,
                Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    copy(1),
                    Operand::Constant(ConstValue::Uint(7, 32)),
                ),
            ),
            assign(3, Rvalue::BinaryOp(BinOp::Shl, int(1), copy(2))),
            assign(0, Rvalue::BinaryOp(BinOp::Lt, copy(3), int(0))),
        ],
    );
    // Every masked count is at most7, so the i32 result is positive,
    // including count7 where the corresponding i8 result is negative.
    check_native(
        &fixture,
        "uint64_t",
        "uint32_t",
        "for (unsigned count = 0; count < 256; ++count) {\n\
         uint64_t got = shift_i32_sign(count);\n\
         if (got != 0) {\n\
         printf(\"i32 count=%u got=%llu expected=0\\n\", count, (unsigned long long)got);\n\
         return 1; }}",
    );
}

#[test]
fn i32_subtraction_constants_still_match_the_place_in_both_orders() {
    for (name, lhs, rhs, expected) in [
        ("subtract_one", copy(1), int(1), [-101, -1, 0, 99]),
        ("subtract_from_one", int(1), copy(1), [101, 1, 0, -99]),
    ] {
        let fixture = function(
            name,
            vec![Ty::i32(), Ty::i32()],
            vec![assign(0, Rvalue::BinaryOp(BinOp::Sub, lhs, rhs))],
        );
        let checks = [-100, 0, 1, 100]
            .into_iter()
            .zip(expected)
            .map(|(input, expected)| format!("if ({name}({input}) != {expected}) return 1;\n"))
            .collect::<String>();
        check_native(&fixture, "int32_t", "int32_t", &checks);
    }
}

#[test]
fn checked_i8_shifts_retain_the_count_boundary() {
    for op in [BinOp::Shl, BinOp::Shr] {
        for count in [0, 7, 8, 255] {
            let fixture = function(
                "checked_shift_overflow",
                vec![Ty::Bool, Ty::i8(), Ty::Tuple(vec![Ty::i8(), Ty::Bool])],
                vec![
                    assign(2, Rvalue::CheckedBinaryOp(op, copy(1), int(count))),
                    assign(
                        0,
                        Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Field(1)],
                        })),
                    ),
                ],
            );
            let expected = u8::from(count >= 8);
            let checks = [-128, -1, 0, 127]
                .into_iter()
                .map(|input| {
                    format!("if (checked_shift_overflow({input}) != {expected}) return 1;\n")
                })
                .collect::<String>();
            check_native(&fixture, "uint64_t", "int8_t", &checks);
        }
    }
}

#[test]
fn checked_constant_shifted_i8_preserves_flag_and_valid_result_sign() {
    for op in [BinOp::Shl, BinOp::Shr] {
        for return_flag in [true, false] {
            let payload = Place { local: 2, projections: vec![Projection::Field(0)] };
            let observation = if return_flag {
                Rvalue::Use(Operand::Copy(Place {
                    local: 2,
                    projections: vec![Projection::Field(1)],
                }))
            } else {
                Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(payload), int(0))
            };
            let fixture = function(
                "checked_constant_shift",
                vec![Ty::Bool, Ty::u32(), Ty::Tuple(vec![Ty::i8(), Ty::Bool])],
                vec![
                    assign(2, Rvalue::CheckedBinaryOp(op, int(1), copy(1))),
                    assign(0, observation),
                ],
            );
            // Observe the flag at both sides of the count boundary. The sign
            // observation only consumes the payload for valid shift counts.
            let counts = if return_flag { vec![0, 7, 8, 31] } else { vec![0, 7] };
            let checks = counts
                .into_iter()
                .map(|count| {
                    let expected = if return_flag {
                        count >= 8
                    } else {
                        matches!(op, BinOp::Shl) && count == 7
                    };
                    format!(
                        "if (checked_constant_shift({count}) != {}) return 1;\n",
                        u8::from(expected)
                    )
                })
                .collect::<String>();
            check_native(&fixture, "uint64_t", "uint32_t", &checks);
        }
    }
}
