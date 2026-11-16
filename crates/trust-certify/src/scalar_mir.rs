//! A typed, raw-MIR-shaped scalar model and checked observation bridge.
//!
//! These are reified model inputs, not authenticated rustc `Body` values or
//! Rust-source refinement. No function/instance/caller/compiler authority can
//! be minted from them. The admitted capture has four always-live locals and
//! two blocks, before/after one overflow-assertion rewrite. General storage,
//! calls, memory, cleanup and move semantics are not claimed.
//!
//! The conclusion is a whole-execution, model-level full-observation bridge,
//! not a step-by-step Rust simulation. Before/after each take five raw steps;
//! the existing scalar spelling takes seven. Exact trace tags and the
//! before-only consumed-flag access marker remain in the proposition. Failed
//! assertions observe their unwind action; Rust's panic payload/runtime is not
//! modeled. The admitted theorem establishes that failure is unreachable.
//!
//! A non-call scalar Move reads data like Copy, as the current interpreter
//! does, but this model also enforces the documented no-reread discipline.
//! It does not resolve Rust's general move/deinitialization memory semantics.
//! No storage markers means all four locals are always-live; managed-storage
//! operations explicitly fault and cannot earn this certificate.
//!
//! `Use` retains its retag bit in the whole-body identity. The model's explicit
//! retag rule reconstructs only its closed pointer-free scalar values and is
//! kernel-proved observationally inert. This is not a rule for Rust pointers,
//! heap/provenance state, or a complete semantic projection of actual MIR.

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};

use crate::scalar_return::{ScalarType, ScalarValue};

mod model;
mod proof;
pub use proof::{
    ScalarMirBridgeCertificate, prove_successor_bridge, prove_successor_bridge_for_family,
};

pub mod actual_ir;
pub mod capture;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app<const N: usize>(name: &str, args: [Expr; N]) -> Expr {
    Expr::apps(c(name), args)
}
fn n(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, body)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, domain, body)
}
fn bool_(value: bool) -> Expr {
    c(if value { "Bool.true" } else { "Bool.false" })
}

/// Typed place in the bounded raw-MIR-shaped object language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarMirPlace {
    Local(u32),
    PairValue(u32),
    PairFlag(u32),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarMirOperand {
    Copy(ScalarMirPlace),
    Move(ScalarMirPlace),
    Constant(ScalarValue),
}
/// Explicit model bit corresponding to MIR's two `WithRetag` alternatives.
/// This type does not attest a compiler operand or supply Rust retag semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarMirRetag {
    No,
    Yes,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarMirRvalue {
    Use(ScalarMirOperand, ScalarMirRetag),
    WidenU8ToU16(ScalarMirOperand),
    CheckedAdd(ScalarMirOperand, ScalarMirOperand),
    Unsupported,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarMirStatement {
    Assign(u32, ScalarMirRvalue),
    StorageLive(u32),
    StorageDead(u32),
    Unsupported,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarMirUnwind {
    Continue,
    Unreachable,
    Terminate,
    Cleanup(u32),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarMirTerminator {
    AssertOverflowAdd {
        condition: ScalarMirOperand,
        expected: bool,
        target: u32,
        unwind: ScalarMirUnwind,
        left: ScalarMirOperand,
        right: ScalarMirOperand,
    },
    Goto(u32),
    Return,
    Unsupported,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarMirBlock {
    pub cleanup: bool,
    pub statements: Vec<ScalarMirStatement>,
    pub terminator: ScalarMirTerminator,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarMirAbi {
    Rust,
    Unsupported,
}
/// Caller-authored model data, never an authenticated compiler body or receipt.
/// Locals with storage markers are represented but refused by this bridge.
/// ABI/count and assertion diagnostic operands are bound by kernel whole-body
/// equalities, not by a modeled Rust calling convention or panic formatter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarMirBody {
    pub abi: ScalarMirAbi,
    pub argument_count: u32,
    pub locals: Vec<ScalarType>,
    pub blocks: Vec<ScalarMirBlock>,
}

/// Fixed model corresponding to the successor capture's scalar/CFG shape;
/// not a complete MIR encoding or a binding to the producing compiler/source.
/// The captured `Use` explicitly carries `Yes`; changing it to `No` changes the
/// fixed body even though the closed model proves equal observations. An actual
/// compiler adapter and the rest of a complete semantic projection are absent.
pub fn successor_before() -> ScalarMirBody {
    use ScalarMirOperand::{Constant, Copy, Move};
    use ScalarMirPlace::{Local, PairFlag, PairValue};
    use ScalarMirRvalue::{CheckedAdd, Use, WidenU8ToU16};
    let one = Constant(ScalarValue::U16(1));
    ScalarMirBody {
        abi: ScalarMirAbi::Rust,
        argument_count: 1,
        locals: vec![ScalarType::U16, ScalarType::U8, ScalarType::U16, ScalarType::CheckedU16],
        blocks: vec![
            ScalarMirBlock {
                cleanup: false,
                statements: vec![
                    ScalarMirStatement::Assign(2, WidenU8ToU16(Copy(Local(1)))),
                    ScalarMirStatement::Assign(3, CheckedAdd(Copy(Local(2)), one.clone())),
                ],
                terminator: ScalarMirTerminator::AssertOverflowAdd {
                    condition: Move(PairFlag(3)),
                    expected: false,
                    target: 1,
                    unwind: ScalarMirUnwind::Continue,
                    left: Copy(Local(2)),
                    right: one,
                },
            },
            ScalarMirBlock {
                cleanup: false,
                statements: vec![ScalarMirStatement::Assign(
                    0,
                    Use(Copy(PairValue(3)), ScalarMirRetag::Yes),
                )],
                terminator: ScalarMirTerminator::Return,
            },
        ],
    }
}
pub fn successor_after() -> ScalarMirBody {
    let mut body = successor_before();
    body.blocks[0].terminator = ScalarMirTerminator::Goto(1);
    body
}

/// Two exact model spellings, not alternative Rust ownership semantics.
/// The compiler spelling retains the observed return and diagnostic Moves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarMirSuccessorFamily {
    CopyFixture,
    CompilerMove,
}

impl ScalarMirSuccessorFamily {
    pub fn before(self) -> ScalarMirBody {
        let mut body = successor_before();
        if self == Self::CompilerMove {
            if let ScalarMirTerminator::AssertOverflowAdd { left, .. } =
                &mut body.blocks[0].terminator
            {
                // Bound in the full body, not evaluated on a successful assert.
                *left = ScalarMirOperand::Move(ScalarMirPlace::Local(2));
            }
            body.blocks[1].statements[0] = ScalarMirStatement::Assign(
                0,
                ScalarMirRvalue::Use(
                    ScalarMirOperand::Move(ScalarMirPlace::PairValue(3)),
                    ScalarMirRetag::Yes,
                ),
            );
        }
        body
    }

    pub fn after(self) -> ScalarMirBody {
        let mut body = self.before();
        body.blocks[0].terminator = ScalarMirTerminator::Goto(1);
        body
    }
}

fn type_term(ty: ScalarType) -> Expr {
    c(match ty {
        ScalarType::U8 => "SMTy.u8",
        ScalarType::U16 => "SMTy.u16",
        ScalarType::Bool => "SMTy.bool",
        ScalarType::CheckedU8 => "SMTy.pair8",
        ScalarType::CheckedU16 => "SMTy.pair16",
    })
}
fn value_term(value: ScalarValue) -> Expr {
    match value {
        ScalarValue::U8(value) => app("SMValue.u8", [app("UInt8.ofNat", [n(value.into())])]),
        ScalarValue::U16(value) => app("SMValue.u16", [app("UInt16.ofNat", [n(value.into())])]),
        ScalarValue::Bool(value) => app("SMValue.bool", [bool_(value)]),
        ScalarValue::CheckedU8(value, flag) => {
            app("SMValue.pair8", [app("UInt8.ofNat", [n(value.into())]), bool_(flag)])
        }
        ScalarValue::CheckedU16(value, flag) => {
            app("SMValue.pair16", [app("UInt16.ofNat", [n(value.into())]), bool_(flag)])
        }
    }
}
fn place_term(place: &ScalarMirPlace) -> Expr {
    let (local, field) = match place {
        ScalarMirPlace::Local(i) => (*i, 0),
        ScalarMirPlace::PairValue(i) => (*i, 1),
        ScalarMirPlace::PairFlag(i) => (*i, 2),
    };
    app("RMPlace.mk", [n(local.into()), n(field)])
}
fn operand_term(operand: &ScalarMirOperand) -> Expr {
    match operand {
        ScalarMirOperand::Copy(p) => app("RMOperand.copy", [place_term(p)]),
        ScalarMirOperand::Move(p) => app("RMOperand.move", [place_term(p)]),
        ScalarMirOperand::Constant(v) => app("RMOperand.constant", [value_term(*v)]),
    }
}
fn rvalue_term(rvalue: &ScalarMirRvalue) -> Expr {
    match rvalue {
        ScalarMirRvalue::Use(o, retag) => app(
            "RMRvalue.use",
            [
                operand_term(o),
                c(match retag {
                    ScalarMirRetag::No => "RMRetag.no",
                    ScalarMirRetag::Yes => "RMRetag.yes",
                }),
            ],
        ),
        ScalarMirRvalue::WidenU8ToU16(o) => app("RMRvalue.widen", [operand_term(o)]),
        ScalarMirRvalue::CheckedAdd(a, b) => {
            app("RMRvalue.checkedAdd", [operand_term(a), operand_term(b)])
        }
        ScalarMirRvalue::Unsupported => c("RMRvalue.unsupported"),
    }
}
fn statement_term(statement: &ScalarMirStatement) -> Expr {
    match statement {
        ScalarMirStatement::Assign(i, r) => {
            app("RMStatement.assign", [n((*i).into()), rvalue_term(r)])
        }
        ScalarMirStatement::StorageLive(i) => app("RMStatement.storageLive", [n((*i).into())]),
        ScalarMirStatement::StorageDead(i) => app("RMStatement.storageDead", [n((*i).into())]),
        ScalarMirStatement::Unsupported => c("RMStatement.unsupported"),
    }
}
fn unwind_term(unwind: &ScalarMirUnwind) -> Expr {
    match unwind {
        ScalarMirUnwind::Continue => c("RMUnwind.continue"),
        ScalarMirUnwind::Unreachable => c("RMUnwind.unreachable"),
        ScalarMirUnwind::Terminate => c("RMUnwind.terminate"),
        ScalarMirUnwind::Cleanup(i) => app("RMUnwind.cleanup", [n((*i).into())]),
    }
}
fn terminal_term(terminal: &ScalarMirTerminator) -> Expr {
    match terminal {
        ScalarMirTerminator::AssertOverflowAdd {
            condition,
            expected,
            target,
            unwind,
            left,
            right,
        } => app(
            "RMTerminator.assertOverflowAdd",
            [
                operand_term(condition),
                bool_(*expected),
                n((*target).into()),
                unwind_term(unwind),
                operand_term(left),
                operand_term(right),
            ],
        ),
        ScalarMirTerminator::Goto(i) => app("RMTerminator.goto", [n((*i).into())]),
        ScalarMirTerminator::Return => c("RMTerminator.ret"),
        ScalarMirTerminator::Unsupported => c("RMTerminator.unsupported"),
    }
}
fn body_term(body: &ScalarMirBody) -> Result<Expr, String> {
    if body.locals.len() > 16
        || body.blocks.len() > 8
        || body.blocks.iter().any(|b| b.statements.len() > 16)
    {
        return Err("MIR-shaped model exceeds encoding limits".into());
    }
    let types = body
        .locals
        .iter()
        .rev()
        .fold(c("RMTypes.nil"), |rest, ty| app("RMTypes.cons", [type_term(*ty), rest]));
    let blocks = body.blocks.iter().rev().fold(c("RMBlocks.nil"), |rest, block| {
        let code = block
            .statements
            .iter()
            .rev()
            .fold(app("RMCode.terminal", [terminal_term(&block.terminator)]), |rest, s| {
                app("RMCode.statement", [statement_term(s), rest])
            });
        app("RMBlocks.cons", [bool_(block.cleanup), code, rest])
    });
    Ok(app(
        "RMBody.mk",
        [
            c(match body.abi {
                ScalarMirAbi::Rust => "RMAbi.rust",
                ScalarMirAbi::Unsupported => "RMAbi.unsupported",
            }),
            n(body.argument_count.into()),
            types,
            blocks,
        ],
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn raw_mir_model_is_kernel_checked_and_axiom_free() {
        crate::checker_core::run_on_large_stack(|| {
            let env = model::environment().unwrap();
            TypeChecker::new(&env)
                .check_type(&body_term(&successor_before()).unwrap(), &c("RMBody"))
                .unwrap();
        })
        .expect("MIR model worker");
    }
}
