//! Actual instruction model with kernel-checked finite UInt8 exhaustion.
//! Fin/Nat/BitVec recursors and retained closure follow scalar_mir::proof;
//! no count of host executions is used as a completeness premise.

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{Declaration, Environment, Expr, Level, Name, TypeChecker};

use super::{Instruction, fixed_program, model};
use crate::scalar_mir::{app, bool_, c, lam, n, pi};
use crate::scalar_return::ScalarType;

const PROGRAM: &str = "ActualIrBridge.program";
const ACTUAL: &str = "ActualIrBridge.actual";
const EXPECTED: &str = "ActualIrBridge.expected";
const THEOREM: &str = "ActualIrBridge.universal";
const COUNT: usize = 3 + 1 + 257 + 1;
const MAX_TERM_BYTES: usize = 512 * 1024;
const MAX_CLOSURE_BYTES: usize = 8 * 1024 * 1024;

pub(super) struct Certificate {
    code: Vec<Instruction>,
    terms: Vec<Vec<u8>>,
}

impl Certificate {
    pub(super) fn replay(&self, code: &[Instruction]) -> Result<(), String> {
        if code != self.code
            || self.terms.len() != COUNT
            || trust_types::audit_ledger::cap_hit_if(
                self.terms.iter().any(|t| t.len() > MAX_TERM_BYTES),
                "crates/trust-certify/src/scalar_mir/actual_ir/proof.rs:MAX_TERM_BYTES",
            )
            || trust_types::audit_ledger::cap_hit_if(
                self.terms.iter().map(Vec::len).sum::<usize>() > MAX_CLOSURE_BYTES,
                "crates/trust-certify/src/scalar_mir/actual_ir/proof.rs:MAX_CLOSURE_BYTES",
            )
        {
            return Err("actual IR proof identity or bounded closure mismatch".into());
        }
        let code = code.to_vec();
        let terms = self.terms.clone();
        crate::checker_core::run_on_large_stack(move || check(&code, Some(&terms)).map(|_| ()))
            .ok_or("actual IR replay worker failed")?
    }
}

pub(super) fn prove(code: &[Instruction]) -> Result<Certificate, String> {
    if code.len() != 8 {
        return Err("actual IR instruction limit".into());
    }
    let code = code.to_vec();
    crate::checker_core::run_on_large_stack(move || {
        let terms = check(&code, None)?;
        Ok(Certificate { code, terms })
    })
    .ok_or("actual IR proof worker failed")?
}

struct Decl {
    name: String,
    ty: Expr,
    value: Expr,
    theorem: bool,
}
fn definition(name: &str, ty: Expr, value: Expr) -> Decl {
    Decl { name: name.into(), ty, value, theorem: false }
}
fn theorem(name: &str, ty: Expr, value: Expr) -> Decl {
    Decl { name: name.into(), ty, value, theorem: true }
}
fn poly<const N: usize>(name: &str, level: Level, args: [Expr; N]) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![level]), args)
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    poly("Eq", Level::succ(Level::zero()), [ty, a, b])
}
fn refl(ty: Expr, value: Expr) -> Expr {
    poly("Eq.refl", Level::succ(Level::zero()), [ty, value])
}
fn u16_(value: Expr) -> Expr {
    app("UInt16.ofNat", [value])
}
fn v16(value: Expr) -> Expr {
    app("SMValue.u16", [value])
}
fn v8(value: Expr) -> Expr {
    app("SMValue.u8", [value])
}
fn frame(typed: Vec<(ScalarType, Option<Expr>)>) -> Expr {
    typed.into_iter().rev().fold(c("SMFrame.nil"), |rest, (ty, value)| {
        let slot = value.map_or_else(|| c("SMSlot.uninitialized"), |v| app("SMSlot.value", [v]));
        app("SMFrame.cons", [crate::scalar_mir::type_term(ty), slot, rest])
    })
}

fn instruction_term(inst: &Instruction) -> Expr {
    let id = |value: u32| n(u64::from(value));
    match *inst {
        Instruction::Widen { result, operand } => {
            app("SIInstruction.widen", [id(result), id(operand)])
        }
        Instruction::U16 { result, value } => {
            app("SIInstruction.literal", [id(result), v16(u16_(n(u64::from(value))))])
        }
        Instruction::Bool { result, value } => {
            app("SIInstruction.literal", [id(result), app("SMValue.bool", [bool_(value)])])
        }
        Instruction::AddOverflow { result, flag, left, right } => {
            app("SIInstruction.overflow", [id(result), id(flag), id(left), id(right)])
        }
        Instruction::Select { result, condition, yes, no } => {
            app("SIInstruction.select", [id(result), id(condition), id(yes), id(no)])
        }
        Instruction::Assert(cond) => app("SIInstruction.assert", [id(cond)]),
        Instruction::Return(value) => app("SIInstruction.ret", [id(value)]),
    }
}
fn program_term(code: &[Instruction]) -> Expr {
    code.iter().rev().fold(c("SIProgram.nil"), |tail, inst| {
        app("SIProgram.cons", [instruction_term(inst), tail])
    })
}
fn ir_frame(values: [Option<Expr>; 8]) -> Expr {
    use crate::scalar_return::ScalarType::{Bool, U8, U16};
    frame([U8, U16, U16, U16, Bool, Bool, Bool, Bool].into_iter().zip(values).collect())
}
fn expected(input: Expr) -> Expr {
    let widened = u16_(app("UInt8.toNat", [input.clone()]));
    let result = u16_(app("Nat.add", [app("UInt8.toNat", [input.clone()]), n(1)]));
    let boolean = |b| app("SMValue.bool", [bool_(b)]);
    let frame = ir_frame([
        Some(v8(input)),
        Some(v16(widened)),
        Some(v16(u16_(n(1)))),
        Some(v16(result.clone())),
        Some(boolean(false)),
        Some(boolean(false)),
        Some(boolean(true)),
        Some(boolean(true)),
    ]);
    let trace = (0..8).fold(c("SMTrace.nil"), |tail, pc| app("SMTrace.cons", [n(pc), tail]));
    app("SMObservation.mk", [app("SMOutcome.returned", [v16(result)]), frame, trace])
}
fn definitions(code: &[Instruction]) -> Vec<Decl> {
    let input = Expr::bvar(0);
    let initial = app(
        "SIState.running",
        [
            n(0),
            c(PROGRAM),
            ir_frame([Some(v8(input.clone())), None, None, None, None, None, None, None]),
            c("SMTrace.nil"),
        ],
    );
    vec![
        definition(PROGRAM, c("SIProgram"), program_term(code)),
        definition(
            ACTUAL,
            pi(c("UInt8"), c("SMObservation")),
            lam(c("UInt8"), app("si_observe", [app("si_run", [n(8), initial])])),
        ),
        definition(EXPECTED, pi(c("UInt8"), c("SMObservation")), lam(c("UInt8"), expected(input))),
    ]
}
fn proposition(input: Expr) -> Expr {
    eq(c("SMObservation"), app(ACTUAL, [input.clone()]), app(EXPECTED, [input]))
}
fn refl_expected(input: Expr) -> Expr {
    refl(c("SMObservation"), app(EXPECTED, [input]))
}
fn from_fin(index: Expr) -> Expr {
    app("UInt8.ofBitVec", [app("BitVec.ofFin", [n(8), index])])
}
fn from_bound(value: Expr, bound: Expr) -> Expr {
    from_fin(app("Fin.mk", [n(256), value, bound]))
}
fn bound(value: Expr) -> Expr {
    app("Nat.lt", [value, n(256)])
}
fn shifted(tail: Expr, offset: u64) -> Expr {
    app("Nat.add", [tail, n(offset)])
}
fn clause_name(offset: u64) -> String {
    format!("ActualIrBridge.bound_{offset}")
}
fn clause_goal(offset: u64) -> Expr {
    pi(
        c("Nat"),
        pi(
            bound(shifted(Expr::bvar(0), offset)),
            proposition(from_bound(shifted(Expr::bvar(1), offset), Expr::bvar(0))),
        ),
    )
}
fn clause_proof(offset: u64) -> Expr {
    if offset == 256 {
        let mut proof = Expr::bvar(0);
        for remaining in (1..=256).rev() {
            proof = app(
                "Nat.le_of_succ_le_succ",
                [shifted(Expr::bvar(1), remaining), n(remaining - 1), proof],
            );
        }
        let contradiction = app("Nat.not_succ_le_zero", [Expr::bvar(1), proof]);
        let goal = proposition(from_bound(shifted(Expr::bvar(1), 256), Expr::bvar(0)));
        return lam(
            c("Nat"),
            lam(
                bound(shifted(Expr::bvar(0), 256)),
                poly("False.elim", Level::zero(), [goal, contradiction]),
            ),
        );
    }
    let motive = lam(
        c("Nat"),
        pi(
            bound(shifted(Expr::bvar(0), offset)),
            proposition(from_bound(shifted(Expr::bvar(1), offset), Expr::bvar(0))),
        ),
    );
    let zero = lam(bound(n(offset)), refl_expected(from_bound(n(offset), Expr::bvar(0))));
    let successor = lam(c("Nat"), app(&clause_name(offset + 1), [Expr::bvar(0)]));
    lam(c("Nat"), poly("Nat.casesOn", Level::zero(), [motive, Expr::bvar(0), zero, successor]))
}
fn universal_goal() -> Expr {
    pi(c("UInt8"), proposition(Expr::bvar(0)))
}
fn universal_proof() -> Expr {
    let fin_ty = app("Fin", [n(256)]);
    let bv_ty = app("BitVec", [n(8)]);
    let fin_motive = lam(fin_ty.clone(), proposition(from_fin(Expr::bvar(0))));
    let fin_minor = lam(
        c("Nat"),
        lam(bound(Expr::bvar(0)), app(&clause_name(0), [Expr::bvar(1), Expr::bvar(0)])),
    );
    let fin_proof =
        lam(fin_ty, poly("Fin.rec", Level::zero(), [n(256), fin_motive, fin_minor, Expr::bvar(0)]));
    let bv_motive = lam(bv_ty.clone(), proposition(app("UInt8.ofBitVec", [Expr::bvar(0)])));
    let bv_proof =
        lam(bv_ty, poly("BitVec.rec", Level::zero(), [n(8), bv_motive, fin_proof, Expr::bvar(0)]));
    let motive = lam(c("UInt8"), proposition(Expr::bvar(0)));
    lam(c("UInt8"), poly("UInt8.rec", Level::zero(), [motive, bv_proof, Expr::bvar(0)]))
}

fn declarations(code: &[Instruction]) -> Vec<Decl> {
    let mut result = definitions(code);
    let fixed = program_term(&fixed_program());
    result.push(theorem(
        "ActualIrBridge.bodyBinding",
        eq(c("SIProgram"), c(PROGRAM), fixed.clone()),
        refl(c("SIProgram"), fixed),
    ));
    result
        .extend((0..=256).rev().map(|i| theorem(&clause_name(i), clause_goal(i), clause_proof(i))));
    result.push(theorem(THEOREM, universal_goal(), universal_proof()));
    result
}

fn check(code: &[Instruction], retained: Option<&[Vec<u8>]>) -> Result<Vec<Vec<u8>>, String> {
    let declarations = declarations(code);
    if declarations.len() != COUNT || retained.is_some_and(|t| t.len() != COUNT) {
        return Err("incomplete actual IR proof closure".into());
    }
    let mut env = model::environment()?;
    let mut terms = Vec::new();
    let mut total_bytes = 0_usize;
    for (index, declaration) in declarations.iter().enumerate() {
        let encoded =
            serialize_term(&declaration.value).map_err(|e| format!("actual IR encode: {e:?}"))?;
        total_bytes =
            total_bytes.checked_add(encoded.len()).ok_or("actual IR byte count overflow")?;
        if trust_types::audit_ledger::cap_hit_if(
            encoded.len() > MAX_TERM_BYTES,
            "crates/trust-certify/src/scalar_mir/actual_ir/proof.rs:MAX_TERM_BYTES",
        ) || trust_types::audit_ledger::cap_hit_if(
            total_bytes > MAX_CLOSURE_BYTES,
            "crates/trust-certify/src/scalar_mir/actual_ir/proof.rs:MAX_CLOSURE_BYTES",
        ) {
            return Err("actual IR proof exceeds retained-byte limits".into());
        }
        if retained.is_some_and(|t| t[index] != encoded) {
            return Err("changed actual IR proof closure".into());
        }
        register(&mut env, declaration, &encoded)?;
        terms.push(encoded);
    }
    Ok(terms)
}

fn register(env: &mut Environment, expected: &Decl, bytes: &[u8]) -> Result<(), String> {
    let decoded =
        deserialize_term(bytes).map_err(|e| format!("{} decode: {e:?}", expected.name))?;
    let tc = TypeChecker::new(env);
    let _ = tc.infer_sort(&expected.ty).map_err(|e| format!("{} goal: {e:?}", expected.name))?;
    tc.check_type(&decoded, &expected.ty)
        .map_err(|e| format!("{} kernel proof: {e:?}", expected.name))?;
    drop(tc);
    let name = Name::from_string(&expected.name);
    let declaration = if expected.theorem {
        Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: expected.ty.clone(),
            value: decoded,
        }
    } else {
        Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: expected.ty.clone(),
            value: decoded,
            is_reducible: true,
        }
    };
    env.add_decl(declaration).map_err(|e| format!("{} registration: {e:?}", expected.name))?;
    if !env.axiom_deps(&name).is_some_and(|a| a.is_empty())
        || !env.foundational_axiom_deps(&name).is_some_and(|a| a.is_empty())
    {
        return Err(format!("{} axiom debt", expected.name));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn universal_actual_ir_model_constructs_and_replays() {
        let mut certificate = prove(&fixed_program()).unwrap();
        certificate.replay(&fixed_program()).unwrap();
        let last = certificate.terms.pop().unwrap();
        assert!(certificate.replay(&fixed_program()).is_err(), "missing universal term");
        certificate.terms.push(last);
        certificate.terms[0][0] ^= 1;
        assert!(certificate.replay(&fixed_program()).is_err(), "changed body term");
    }
    #[test]
    fn actual_ir_kernel_body_binding_refuses_changed_selector() {
        crate::checker_core::run_on_large_stack(|| {
            let mut code = fixed_program();
            code[5] = Instruction::Select { result: 7, condition: 4, yes: 6, no: 5 };
            let mut env = model::environment().unwrap();
            let decls = declarations(&code);
            for declaration in &decls[..3] {
                register(&mut env, declaration, &serialize_term(&declaration.value).unwrap())
                    .unwrap();
            }
            let error = register(&mut env, &decls[3], &serialize_term(&decls[3].value).unwrap())
                .unwrap_err();
            assert!(error.contains("bodyBinding kernel proof"), "{error}");
        })
        .unwrap();
    }
}
