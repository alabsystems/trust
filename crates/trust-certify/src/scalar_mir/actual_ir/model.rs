//! A closed operational model for the independently read instruction subset.
//! No instruction is erased: select/literal/assert/return each takes one step.

use clean_kernel::{ConstantKind, Environment, TypeChecker};

const SOURCE: &str = r#"
inductive SIInstruction : Type
| widen : Nat → Nat → SIInstruction
| literal : Nat → SMValue → SIInstruction
| overflow : Nat → Nat → Nat → Nat → SIInstruction
| select : Nat → Nat → Nat → Nat → SIInstruction
| assert : Nat → SIInstruction
| ret : Nat → SIInstruction

inductive SIProgram : Type
| nil : SIProgram
| cons : SIInstruction → SIProgram → SIProgram

inductive SIState : Type
| running : Nat → SIProgram → SMFrame → SMTrace → SIState
| halted : SMOutcome → SMFrame → SMTrace → SIState

def si_write (pc : Nat) (rest : SIProgram) (frame : SMFrame) (trace : SMTrace)
    (dst : Nat) (read : SMRead) : SIState :=
  match read with
  | SMRead.fault fault => SIState.halted (SMOutcome.fault fault) frame trace
  | SMRead.value value => match sm_write frame dst value with
    | SMWrite.fault fault => SIState.halted (SMOutcome.fault fault) frame trace
    | SMWrite.frame after => SIState.running (Nat.succ pc) rest after trace

def si_overflow_result (pc : Nat) (rest : SIProgram) (frame : SMFrame) (trace : SMTrace)
    (dst : Nat) (flag : Nat) (read : SMRead) : SIState :=
  match read with
  | SMRead.fault fault => SIState.halted (SMOutcome.fault fault) frame trace
  | SMRead.value value => match value with
    | SMValue.pair16 result overflow => match sm_write frame dst (SMValue.u16 result) with
      | SMWrite.fault fault => SIState.halted (SMOutcome.fault fault) frame trace
      | SMWrite.frame after => si_write pc rest after trace flag (SMRead.value (SMValue.bool overflow))
    | _ => SIState.halted (SMOutcome.fault SMFault.typeMismatch) frame trace

def si_select (frame : SMFrame) (condition : Nat) (yes : Nat) (no : Nat) : SMRead :=
  match sm_read frame condition with
  | SMRead.fault fault => SMRead.fault fault
  | SMRead.value value => match value with
    | SMValue.bool b => Bool.rec (fun _ => SMRead) (sm_read frame no) (sm_read frame yes) b
    | _ => SMRead.fault SMFault.typeMismatch

def si_assert (pc : Nat) (rest : SIProgram) (frame : SMFrame) (trace : SMTrace)
    (condition : Nat) : SIState :=
  match sm_read frame condition with
  | SMRead.fault fault => SIState.halted (SMOutcome.fault fault) frame trace
  | SMRead.value value => match value with
    | SMValue.bool b => Bool.rec (fun _ => SIState)
        (SIState.halted SMOutcome.panic frame trace)
        (SIState.running (Nat.succ pc) rest frame trace) b
    | _ => SIState.halted (SMOutcome.fault SMFault.typeMismatch) frame trace

def si_return (frame : SMFrame) (trace : SMTrace) (value : Nat) : SIState :=
  match sm_read frame value with
  | SMRead.fault fault => SIState.halted (SMOutcome.fault fault) frame trace
  | SMRead.value value => SIState.halted (SMOutcome.returned value) frame trace

def si_execute (pc : Nat) (rest : SIProgram) (frame : SMFrame) (trace : SMTrace)
    (instruction : SIInstruction) : SIState :=
  match instruction with
  | SIInstruction.widen dst src => si_write pc rest frame trace dst (sm_map_read sm_widen (sm_read frame src))
  | SIInstruction.literal dst value => si_write pc rest frame trace dst (SMRead.value value)
  | SIInstruction.overflow dst flag left right =>
      si_overflow_result pc rest frame trace dst flag (sm_add_reads Bool.true (sm_read frame left) (sm_read frame right))
  | SIInstruction.select dst condition yes no => si_write pc rest frame trace dst (si_select frame condition yes no)
  | SIInstruction.assert condition => si_assert pc rest frame trace condition
  | SIInstruction.ret value => si_return frame trace value

def si_step (state : SIState) : SIState :=
  match state with
  | SIState.halted outcome frame trace => state
  | SIState.running pc code frame trace => match code with
    | SIProgram.nil => SIState.halted (SMOutcome.fault SMFault.missingReturn) frame trace
    | SIProgram.cons instruction rest => si_execute pc rest frame (SMTrace.cons pc trace) instruction

def si_run (fuel : Nat) (initial : SIState) : SIState :=
  Nat.rec (fun _ => SIState) initial (fun _ previous => si_step previous) fuel

def si_observe (state : SIState) : SMObservation :=
  match state with
  | SIState.halted outcome frame trace => SMObservation.mk outcome frame trace
  | SIState.running pc code frame trace => SMObservation.mk SMOutcome.outOfFuel frame trace
"#;

pub(super) fn environment() -> Result<Environment, String> {
    use crate::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "TrustActualScalarIrModel".into(),
            path: "<fixed actual scalar IR model>".into(),
            source: format!("{}\n{SOURCE}", crate::scalar_return::SCALAR_MODEL_SOURCE),
        }],
        false,
    );
    let context = batch.accepted_context().ok_or_else(|| {
        format!("actual IR model registration: {:?}; {:?}", batch.errors(), batch.attempt())
    })?;
    let env = context.environment().clone();
    for name in context.owned_declarations() {
        let info = env.get_const(name).ok_or("actual IR model declaration disappeared")?;
        if info.kind == ConstantKind::Axiom
            || env.is_unsafe(name)
            || env.is_partial(name)
            || !env.axiom_deps(name).is_some_and(|a| a.is_empty())
            || !env.foundational_axiom_deps(name).is_some_and(|a| a.is_empty())
        {
            return Err(format!("actual IR model {name} has unchecked/axiom debt"));
        }
        if let Some(value) = &info.value {
            TypeChecker::new(&env)
                .check_type(value, &info.type_)
                .map_err(|e| format!("actual IR model {name} recheck: {e:?}"))?;
        }
    }
    Ok(env)
}
