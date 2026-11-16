//! A small, executable, kernel-checked scalar machine.
//!
//! This is a **model**, not an adapter for rustc MIR, a Rust-source refinement,
//! a call-result fact, or a compiler proof-authority token. In particular, a
//! successful model execution must never set `KernelCertified` or satisfy G4.
//! Connecting a real body to this syntax requires a separate checked refinement.
//!
//! The initial unsigned carriers are the kernel's actual finite `UInt8` and
//! `UInt16`, not unrestricted integers with a width label. Locals have declared
//! types and an explicit uninitialized state. Addition is either wrapping or
//! returns the wrapping value **and** overflow flag; panic happens only when an
//! executed assertion fails. A missing return, bad local, type error, unsupported
//! operation, and exhausted fuel are distinct outcomes. There is no memory/call
//! semantics: those operations explicitly fault, never behave as pure no-ops.
//!
//! The program is a finite instruction sequence, not an arbitrary MIR CFG.
//! Execution is defined in the kernel by structural recursion on fuel; its
//! trace records every attempted instruction index, newest first. Halted states
//! are absorbing. Tests check the complete observation (outcome, typed local
//! frame, and trace), not a host-language interpreter's answer.

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{ConstantKind, Environment, Expr, Level, Name, TypeChecker};

/// Version of the literal model below. This names semantics, not source fidelity.
pub const SCALAR_MODEL_VERSION: &str = "trust.scalar-execution-model/v1";

/// Complete model definition, elaborated and kernel-checked by [`ScalarExecutionModel`].
/// No imported file, solver verdict, assumed law, or external environment is accepted.
pub const SCALAR_MODEL_SOURCE: &str = r#"
inductive SMTy : Type
| u8 : SMTy
| u16 : SMTy
| bool : SMTy
| pair8 : SMTy
| pair16 : SMTy

inductive SMValue : Type
| u8 : UInt8 → SMValue
| u16 : UInt16 → SMValue
| bool : Bool → SMValue
| pair8 : UInt8 → Bool → SMValue
| pair16 : UInt16 → Bool → SMValue

def sm_type_tag (t : SMTy) : Nat :=
  match t with
  | SMTy.u8 => 0
  | SMTy.u16 => 1
  | SMTy.bool => 2
  | SMTy.pair8 => 3
  | SMTy.pair16 => 4

def sm_value_type (v : SMValue) : SMTy :=
  match v with
  | SMValue.u8 _ => SMTy.u8
  | SMValue.u16 _ => SMTy.u16
  | SMValue.bool _ => SMTy.bool
  | SMValue.pair8 _ _ => SMTy.pair8
  | SMValue.pair16 _ _ => SMTy.pair16

def sm_has_type (t : SMTy) (v : SMValue) : Bool :=
  Nat.beq (sm_type_tag t) (sm_type_tag (sm_value_type v))

inductive SMFault : Type
| uninitialized : SMFault
| badLocal : SMFault
| typeMismatch : SMFault
| unsupported : SMFault
| missingReturn : SMFault

inductive SMSlot : Type
| uninitialized : SMSlot
| value : SMValue → SMSlot

inductive SMFrame : Type
| nil : SMFrame
| cons : SMTy → SMSlot → SMFrame → SMFrame

inductive SMRead : Type
| value : SMValue → SMRead
| fault : SMFault → SMRead

inductive SMWrite : Type
| frame : SMFrame → SMWrite
| fault : SMFault → SMWrite

def sm_read_slot (t : SMTy) (s : SMSlot) : SMRead :=
  match s with
  | SMSlot.uninitialized => SMRead.fault SMFault.uninitialized
  | SMSlot.value v => @Bool.rec (fun _ => SMRead)
      (SMRead.fault SMFault.typeMismatch) (SMRead.value v) (sm_has_type t v)

def sm_read (frame : SMFrame) (index : Nat) : SMRead :=
  @SMFrame.rec (fun _ => Nat → SMRead)
    (fun _ => SMRead.fault SMFault.badLocal)
    (fun t s rest ih => fun i => @Nat.rec (fun _ => SMRead)
      (sm_read_slot t s) (fun n _ => ih n) i) frame index

def sm_prepend_write (t : SMTy) (s : SMSlot) (w : SMWrite) : SMWrite :=
  match w with
  | SMWrite.frame frame => SMWrite.frame (SMFrame.cons t s frame)
  | SMWrite.fault fault => SMWrite.fault fault

def sm_write (frame : SMFrame) (index : Nat) (value : SMValue) : SMWrite :=
  @SMFrame.rec (fun _ => Nat → SMValue → SMWrite)
    (fun _ _ => SMWrite.fault SMFault.badLocal)
    (fun t s rest ih => fun i v => @Nat.rec (fun _ => SMWrite)
      (@Bool.rec (fun _ => SMWrite) (SMWrite.fault SMFault.typeMismatch)
        (SMWrite.frame (SMFrame.cons t (SMSlot.value v) rest)) (sm_has_type t v))
      (fun n _ => sm_prepend_write t s (ih n v)) i) frame index value

def sm_widen (value : SMValue) : SMRead :=
  match value with
  | SMValue.u8 x => SMRead.value (SMValue.u16 (UInt16.ofNat (UInt8.toNat x)))
  | _ => SMRead.fault SMFault.typeMismatch

def sm_add8 (checked : Bool) (a : UInt8) (right : SMValue) : SMRead :=
  match right with
  | SMValue.u8 b => @Bool.rec (fun _ => SMRead)
      (SMRead.value (SMValue.u8 (UInt8.add a b)))
      (SMRead.value (SMValue.pair8 (UInt8.add a b)
        (Nat.ble 256 (Nat.add (UInt8.toNat a) (UInt8.toNat b))))) checked
  | _ => SMRead.fault SMFault.typeMismatch

def sm_add16 (checked : Bool) (a : UInt16) (right : SMValue) : SMRead :=
  match right with
  | SMValue.u16 b => @Bool.rec (fun _ => SMRead)
      (SMRead.value (SMValue.u16 (UInt16.add a b)))
      (SMRead.value (SMValue.pair16 (UInt16.add a b)
        (Nat.ble 65536 (Nat.add (UInt16.toNat a) (UInt16.toNat b))))) checked
  | _ => SMRead.fault SMFault.typeMismatch

def sm_add_values (checked : Bool) (left : SMValue) (right : SMValue) : SMRead :=
  match left with
  | SMValue.u8 a => sm_add8 checked a right
  | SMValue.u16 a => sm_add16 checked a right
  | _ => SMRead.fault SMFault.typeMismatch

def sm_add_right (checked : Bool) (left : SMValue) (right : SMRead) : SMRead :=
  match right with
  | SMRead.value b => sm_add_values checked left b
  | SMRead.fault fault => SMRead.fault fault

def sm_add_reads (checked : Bool) (left : SMRead) (right : SMRead) : SMRead :=
  match left with
  | SMRead.value a => sm_add_right checked a right
  | SMRead.fault fault => SMRead.fault fault

def sm_project_value (value : SMValue) : SMRead :=
  match value with
  | SMValue.pair8 v _ => SMRead.value (SMValue.u8 v)
  | SMValue.pair16 v _ => SMRead.value (SMValue.u16 v)
  | _ => SMRead.fault SMFault.typeMismatch

def sm_project_flag (value : SMValue) : SMRead :=
  match value with
  | SMValue.pair8 _ flag => SMRead.value (SMValue.bool flag)
  | SMValue.pair16 _ flag => SMRead.value (SMValue.bool flag)
  | _ => SMRead.fault SMFault.typeMismatch

def sm_map_read (f : SMValue → SMRead) (read : SMRead) : SMRead :=
  match read with
  | SMRead.value v => f v
  | SMRead.fault fault => SMRead.fault fault

inductive SMRvalue : Type
| literal : SMValue → SMRvalue
| copy : Nat → SMRvalue
| widen : Nat → SMRvalue
| add : Bool → Nat → Nat → SMRvalue
| valueField : Nat → SMRvalue
| flagField : Nat → SMRvalue
| unsupported : SMRvalue

def sm_eval_rvalue (frame : SMFrame) (r : SMRvalue) : SMRead :=
  match r with
  | SMRvalue.literal v => SMRead.value v
  | SMRvalue.copy i => sm_read frame i
  | SMRvalue.widen i => sm_map_read sm_widen (sm_read frame i)
  | SMRvalue.add checked a b => sm_add_reads checked (sm_read frame a) (sm_read frame b)
  | SMRvalue.valueField i => sm_map_read sm_project_value (sm_read frame i)
  | SMRvalue.flagField i => sm_map_read sm_project_flag (sm_read frame i)
  | SMRvalue.unsupported => SMRead.fault SMFault.unsupported

inductive SMInstruction : Type
| assign : Nat → SMRvalue → SMInstruction
| assert : Nat → Bool → SMInstruction
| ret : Nat → SMInstruction
| unsupported : SMInstruction

inductive SMProgram : Type
| nil : SMProgram
| cons : SMInstruction → SMProgram → SMProgram

inductive SMTrace : Type
| nil : SMTrace
| cons : Nat → SMTrace → SMTrace

inductive SMOutcome : Type
| returned : SMValue → SMOutcome
| panic : SMOutcome
| fault : SMFault → SMOutcome
| outOfFuel : SMOutcome

inductive SMState : Type
| running : Nat → SMProgram → SMFrame → SMTrace → SMState
| halted : SMOutcome → SMFrame → SMTrace → SMState

def sm_finish_write (pc : Nat) (rest : SMProgram) (before : SMFrame)
    (trace : SMTrace) (write : SMWrite) : SMState :=
  match write with
  | SMWrite.frame after => SMState.running pc rest after trace
  | SMWrite.fault fault => SMState.halted (SMOutcome.fault fault) before trace

def sm_assign (pc : Nat) (rest : SMProgram) (frame : SMFrame)
    (trace : SMTrace) (dst : Nat) (read : SMRead) : SMState :=
  match read with
  | SMRead.value v => sm_finish_write pc rest frame trace (sm_write frame dst v)
  | SMRead.fault fault => SMState.halted (SMOutcome.fault fault) frame trace

def sm_assert_value (pc : Nat) (rest : SMProgram) (frame : SMFrame)
    (trace : SMTrace) (expected : Bool) (value : SMValue) : SMState :=
  match value with
  | SMValue.bool actual => @Bool.rec (fun _ => SMState)
      (SMState.halted SMOutcome.panic frame trace)
      (SMState.running pc rest frame trace) (Bool.beq actual expected)
  | _ => SMState.halted (SMOutcome.fault SMFault.typeMismatch) frame trace

def sm_assert (pc : Nat) (rest : SMProgram) (frame : SMFrame)
    (trace : SMTrace) (expected : Bool) (read : SMRead) : SMState :=
  match read with
  | SMRead.value v => sm_assert_value pc rest frame trace expected v
  | SMRead.fault fault => SMState.halted (SMOutcome.fault fault) frame trace

def sm_return (frame : SMFrame) (trace : SMTrace) (read : SMRead) : SMState :=
  match read with
  | SMRead.value v => SMState.halted (SMOutcome.returned v) frame trace
  | SMRead.fault fault => SMState.halted (SMOutcome.fault fault) frame trace

def sm_instruction (pc : Nat) (rest : SMProgram) (frame : SMFrame)
    (trace : SMTrace) (instruction : SMInstruction) : SMState :=
  match instruction with
  | SMInstruction.assign dst r => sm_assign (Nat.succ pc) rest frame
      (SMTrace.cons pc trace) dst (sm_eval_rvalue frame r)
  | SMInstruction.assert i expected => sm_assert (Nat.succ pc) rest frame
      (SMTrace.cons pc trace) expected (sm_read frame i)
  | SMInstruction.ret i => sm_return frame (SMTrace.cons pc trace) (sm_read frame i)
  | SMInstruction.unsupported => SMState.halted (SMOutcome.fault SMFault.unsupported)
      frame (SMTrace.cons pc trace)

def sm_step_program (pc : Nat) (program : SMProgram) (frame : SMFrame)
    (trace : SMTrace) : SMState :=
  match program with
  | SMProgram.nil => SMState.halted (SMOutcome.fault SMFault.missingReturn) frame trace
  | SMProgram.cons instruction rest => sm_instruction pc rest frame trace instruction

def sm_step (state : SMState) : SMState :=
  match state with
  | SMState.running pc program frame trace => sm_step_program pc program frame trace
  | SMState.halted outcome frame trace => SMState.halted outcome frame trace

def sm_run (fuel : Nat) (initial : SMState) : SMState :=
  @Nat.rec (fun _ => SMState) initial (fun _ previous => sm_step previous) fuel

inductive SMObservation : Type
| mk : SMOutcome → SMFrame → SMTrace → SMObservation

def sm_observe (state : SMState) : SMObservation :=
  match state with
  | SMState.running _ _ frame trace => SMObservation.mk SMOutcome.outOfFuel frame trace
  | SMState.halted outcome frame trace => SMObservation.mk outcome frame trace
"#;

/// An initialized, independently kernel-checked model environment. This is not
/// an evidence token and has no conversion into compiler proof authority.
pub struct ScalarExecutionModel {
    environment: Environment,
}

impl ScalarExecutionModel {
    /// Elaborate the fixed model and reject any definition with axiom debt.
    pub fn new() -> Result<Self, String> {
        Self::from_source(SCALAR_MODEL_SOURCE)
    }

    fn from_source(source: &str) -> Result<Self, String> {
        use crate::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
        let batch = CheckedLeanSourceBatch::check(
            vec![LeanSourceInput {
                module: "TrustScalarExecutionModel".to_string(),
                path: "<fixed scalar execution model>".to_string(),
                source: source.to_string(),
            }],
            false,
        );
        let context = batch.accepted_context().ok_or_else(|| {
            format!(
                "scalar model failed kernel registration: {:?}; {:?}",
                batch.errors(),
                batch.attempt()
            )
        })?;
        let environment = context.environment().clone();
        // Recheck the actual eager before/after delta, including generated
        // declarations and helpers. A selected prefix or reported-name list
        // cannot hide an introduced axiom or a failed sibling.
        for name in context.owned_declarations() {
            let info = environment.get_const(name).ok_or("model declaration disappeared")?;
            if info.kind == ConstantKind::Axiom
                || environment.is_unsafe(name)
                || environment.is_partial(name)
                || !environment.axiom_deps(name).is_some_and(|deps| deps.is_empty())
                || !environment.foundational_axiom_deps(name).is_some_and(|deps| deps.is_empty())
            {
                return Err(format!("scalar model declaration {name} has unchecked/axiom debt"));
            }
            if let Some(value) = &info.value {
                TypeChecker::new(&environment)
                    .check_type(value, &info.type_)
                    .map_err(|error| format!("scalar model {name} recheck: {error:?}"))?;
            }
        }
        let arrow = |a, b| Expr::pi(clean_kernel::BinderInfo::Default, a, b);
        let required = [
            ("SMProgram", Expr::type_()),
            ("SMObservation", Expr::type_()),
            ("sm_run", arrow(constant("Nat"), arrow(constant("SMState"), constant("SMState")))),
            ("sm_observe", arrow(constant("SMState"), constant("SMObservation"))),
        ];
        for (name, expected_type) in required {
            let name = Name::from_string(name);
            if !context.owns_declaration(&name) {
                return Err(format!("scalar model is missing required declaration {name}"));
            }
            TypeChecker::new(&environment)
                .check_type(&Expr::const_(name.clone(), vec![]), &expected_type)
                .map_err(|error| format!("scalar model {name} has the wrong type: {error:?}"))?;
        }
        Ok(Self { environment })
    }

    /// Read-only access for constructing model propositions, not source claims.
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Check an exact whole model observation by kernel reduction, then check
    /// the serialized proof term again. This returns no certificate or authority
    /// token: it says nothing about a Rust function, instance, or caller state.
    pub fn check_execution(
        &self,
        program: &ScalarProgram,
        fuel: u32,
        expected: &ScalarObservation,
    ) -> Result<(), String> {
        // Bound the host encoder and kernel reduction request; a resource limit
        // is an error, never a modeled execution outcome or proof of termination.
        if program.instructions.len() > 256
            || program.locals.len() > 64
            || expected.locals.len() > 64
            || expected.trace.len() > 256
            || fuel > 512
            || expected.trace.iter().any(|index| *index > 256)
            || program.instructions.iter().any(|instruction| !indices_are_bounded(instruction))
        {
            return Err("scalar model request exceeds encoding/reduction limits".to_string());
        }
        let initial = call(
            "SMState.running",
            [
                Expr::nat_lit(0),
                program_term(&program.instructions),
                frame_term(&program.locals),
                constant("SMTrace.nil"),
            ],
        );
        let actual =
            call("sm_observe", [call("sm_run", [Expr::nat_lit(u64::from(fuel)), initial])]);
        let expected = observation_term(expected);
        let ty = constant("SMObservation");
        let universe = vec![Level::succ(Level::zero())];
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), universe.clone()),
            [ty.clone(), actual, expected.clone()],
        );
        let proof =
            Expr::apps(Expr::const_(Name::from_string("Eq.refl"), universe), [ty, expected]);
        let tc = TypeChecker::new(&self.environment);
        let _ = tc.infer_sort(&goal).map_err(|error| format!("ill-typed model goal: {error:?}"))?;
        tc.check_type(&proof, &goal)
            .map_err(|error| format!("model observation does not kernel-check: {error:?}"))?;
        let bytes =
            serialize_term(&proof).map_err(|error| format!("model proof encoding: {error:?}"))?;
        let decoded =
            deserialize_term(&bytes).map_err(|error| format!("model proof decoding: {error:?}"))?;
        tc.check_type(&decoded, &goal)
            .map_err(|error| format!("model proof roundtrip rejected: {error:?}"))?;
        Ok(())
    }
}

/// Declared local type in this unsigned two-width model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarType {
    U8,
    U16,
    Bool,
    CheckedU8,
    CheckedU16,
}

/// Finite, width-preserving literal values. No arbitrary Nat can masquerade as
/// an in-range input through this interface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarValue {
    U8(u8),
    U16(u16),
    Bool(bool),
    CheckedU8(u8, bool),
    CheckedU16(u16, bool),
}

/// A local keeps its declared type even while uninitialized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarLocal {
    pub ty: ScalarType,
    pub value: Option<ScalarValue>,
}

/// Object-language computations, not extracted rustc rvalues.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarRvalue {
    Literal(ScalarValue),
    Copy(u32),
    WidenU8ToU16(u32),
    Add { checked: bool, left: u32, right: u32 },
    CheckedValue(u32),
    CheckedFlag(u32),
    Unsupported,
}

/// Linear object-language instruction. Calls, memory, cleanup, branches and all
/// other unmodeled operations must remain `Unsupported`, never omitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarInstruction {
    Assign(u32, ScalarRvalue),
    Assert { local: u32, expected: bool },
    Return(u32),
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarProgram {
    pub locals: Vec<ScalarLocal>,
    pub instructions: Vec<ScalarInstruction>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarFault {
    Uninitialized,
    BadLocal,
    TypeMismatch,
    Unsupported,
    MissingReturn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarOutcome {
    Returned(ScalarValue),
    Panic,
    Fault(ScalarFault),
    OutOfFuel,
}

/// The entire observable result of a bounded model run. The trace is newest
/// first, contains attempted instruction indices (including a faulting one),
/// and is not a trace of external effects or a real Rust execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarObservation {
    pub outcome: ScalarOutcome,
    pub locals: Vec<ScalarLocal>,
    pub trace: Vec<u32>,
}

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn call<const N: usize>(name: &str, args: [Expr; N]) -> Expr {
    Expr::apps(constant(name), args)
}

fn bool_term(value: bool) -> Expr {
    constant(if value { "Bool.true" } else { "Bool.false" })
}

fn type_term(ty: ScalarType) -> Expr {
    constant(match ty {
        ScalarType::U8 => "SMTy.u8",
        ScalarType::U16 => "SMTy.u16",
        ScalarType::Bool => "SMTy.bool",
        ScalarType::CheckedU8 => "SMTy.pair8",
        ScalarType::CheckedU16 => "SMTy.pair16",
    })
}

fn value_term(value: ScalarValue) -> Expr {
    let uint = |ty: &str, n: u64| call(ty, [Expr::nat_lit(n)]);
    match value {
        ScalarValue::U8(n) => call("SMValue.u8", [uint("UInt8.ofNat", u64::from(n))]),
        ScalarValue::U16(n) => call("SMValue.u16", [uint("UInt16.ofNat", u64::from(n))]),
        ScalarValue::Bool(b) => call("SMValue.bool", [bool_term(b)]),
        ScalarValue::CheckedU8(n, b) => {
            call("SMValue.pair8", [uint("UInt8.ofNat", u64::from(n)), bool_term(b)])
        }
        ScalarValue::CheckedU16(n, b) => {
            call("SMValue.pair16", [uint("UInt16.ofNat", u64::from(n)), bool_term(b)])
        }
    }
}

fn frame_term(locals: &[ScalarLocal]) -> Expr {
    locals.iter().rev().fold(constant("SMFrame.nil"), |rest, local| {
        let slot = local.value.map_or_else(
            || constant("SMSlot.uninitialized"),
            |v| call("SMSlot.value", [value_term(v)]),
        );
        call("SMFrame.cons", [type_term(local.ty), slot, rest])
    })
}

fn rvalue_term(rvalue: &ScalarRvalue) -> Expr {
    let local = |n: u32| Expr::nat_lit(u64::from(n));
    match *rvalue {
        ScalarRvalue::Literal(v) => call("SMRvalue.literal", [value_term(v)]),
        ScalarRvalue::Copy(i) => call("SMRvalue.copy", [local(i)]),
        ScalarRvalue::WidenU8ToU16(i) => call("SMRvalue.widen", [local(i)]),
        ScalarRvalue::Add { checked, left, right } => {
            call("SMRvalue.add", [bool_term(checked), local(left), local(right)])
        }
        ScalarRvalue::CheckedValue(i) => call("SMRvalue.valueField", [local(i)]),
        ScalarRvalue::CheckedFlag(i) => call("SMRvalue.flagField", [local(i)]),
        ScalarRvalue::Unsupported => constant("SMRvalue.unsupported"),
    }
}

fn program_term(instructions: &[ScalarInstruction]) -> Expr {
    instructions.iter().rev().fold(constant("SMProgram.nil"), |rest, instruction| {
        let term = match instruction {
            ScalarInstruction::Assign(i, r) => {
                call("SMInstruction.assign", [Expr::nat_lit(u64::from(*i)), rvalue_term(r)])
            }
            ScalarInstruction::Assert { local, expected } => call(
                "SMInstruction.assert",
                [Expr::nat_lit(u64::from(*local)), bool_term(*expected)],
            ),
            ScalarInstruction::Return(i) => {
                call("SMInstruction.ret", [Expr::nat_lit(u64::from(*i))])
            }
            ScalarInstruction::Unsupported => constant("SMInstruction.unsupported"),
        };
        call("SMProgram.cons", [term, rest])
    })
}

fn indices_are_bounded(instruction: &ScalarInstruction) -> bool {
    let in_range = |index: u32| index <= 64;
    match instruction {
        ScalarInstruction::Assign(dst, rvalue) => {
            in_range(*dst)
                && match rvalue {
                    ScalarRvalue::Literal(_) | ScalarRvalue::Unsupported => true,
                    ScalarRvalue::Copy(i)
                    | ScalarRvalue::WidenU8ToU16(i)
                    | ScalarRvalue::CheckedValue(i)
                    | ScalarRvalue::CheckedFlag(i) => in_range(*i),
                    ScalarRvalue::Add { left, right, .. } => in_range(*left) && in_range(*right),
                }
        }
        ScalarInstruction::Assert { local, .. } | ScalarInstruction::Return(local) => {
            in_range(*local)
        }
        ScalarInstruction::Unsupported => true,
    }
}

fn observation_term(observation: &ScalarObservation) -> Expr {
    let outcome = match observation.outcome {
        ScalarOutcome::Returned(v) => call("SMOutcome.returned", [value_term(v)]),
        ScalarOutcome::Panic => constant("SMOutcome.panic"),
        ScalarOutcome::OutOfFuel => constant("SMOutcome.outOfFuel"),
        ScalarOutcome::Fault(fault) => call(
            "SMOutcome.fault",
            [constant(match fault {
                ScalarFault::Uninitialized => "SMFault.uninitialized",
                ScalarFault::BadLocal => "SMFault.badLocal",
                ScalarFault::TypeMismatch => "SMFault.typeMismatch",
                ScalarFault::Unsupported => "SMFault.unsupported",
                ScalarFault::MissingReturn => "SMFault.missingReturn",
            })],
        ),
    };
    let trace = observation.trace.iter().rev().fold(constant("SMTrace.nil"), |rest, i| {
        call("SMTrace.cons", [Expr::nat_lit(u64::from(*i)), rest])
    });
    call("SMObservation.mk", [outcome, frame_term(&observation.locals), trace])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn model() -> &'static ScalarExecutionModel {
        static MODEL: std::sync::OnceLock<ScalarExecutionModel> = std::sync::OnceLock::new();
        MODEL.get_or_init(|| ScalarExecutionModel::new().expect("axiom-free typed scalar model"))
    }

    fn local(ty: ScalarType, value: Option<ScalarValue>) -> ScalarLocal {
        ScalarLocal { ty, value }
    }

    fn widening_program(input: u8, addend: u16) -> (ScalarProgram, ScalarObservation) {
        use ScalarInstruction::{Assert, Assign, Return};
        use ScalarRvalue::{Add, CheckedFlag, CheckedValue, Literal, WidenU8ToU16};
        let locals = vec![
            local(ScalarType::U8, Some(ScalarValue::U8(input))),
            local(ScalarType::U16, None),
            local(ScalarType::U16, None),
            local(ScalarType::CheckedU16, None),
            local(ScalarType::Bool, None),
            local(ScalarType::U16, None),
        ];
        let program = ScalarProgram {
            locals: locals.clone(),
            instructions: vec![
                Assign(1, WidenU8ToU16(0)),
                Assign(2, Literal(ScalarValue::U16(addend))),
                Assign(3, Add { checked: true, left: 1, right: 2 }),
                Assign(4, CheckedFlag(3)),
                Assert { local: 4, expected: false },
                Assign(5, CheckedValue(3)),
                Return(5),
            ],
        };
        let (sum, overflow) = u16::from(input).overflowing_add(addend);
        let mut after = locals;
        after[1].value = Some(ScalarValue::U16(u16::from(input)));
        after[2].value = Some(ScalarValue::U16(addend));
        after[3].value = Some(ScalarValue::CheckedU16(sum, overflow));
        after[4].value = Some(ScalarValue::Bool(overflow));
        let outcome = if overflow {
            ScalarOutcome::Panic
        } else {
            after[5].value = Some(ScalarValue::U16(sum));
            ScalarOutcome::Returned(ScalarValue::U16(sum))
        };
        let trace = if overflow { vec![4, 3, 2, 1, 0] } else { vec![6, 5, 4, 3, 2, 1, 0] };
        (program, ScalarObservation { outcome, locals: after, trace })
    }

    fn fault_observation(
        program: &ScalarProgram,
        fault: ScalarFault,
        trace: Vec<u32>,
    ) -> ScalarObservation {
        ScalarObservation {
            outcome: ScalarOutcome::Fault(fault),
            locals: program.locals.clone(),
            trace,
        }
    }

    #[test]
    fn scalar_model_definitions_kernel_check_without_axioms() {
        let model = model();
        assert!(model.environment().get_const(&Name::from_string("sm_run")).is_some());
    }

    #[test]
    fn widening_255_plus_one_returns_256_with_exact_frame_and_trace() {
        let (program, expected) = widening_program(255, 1);
        assert_eq!(expected.outcome, ScalarOutcome::Returned(ScalarValue::U16(256)));
        model()
            .check_execution(&program, 7, &expected)
            .expect("kernel executes widening and checked add");
        model()
            .check_execution(&program, 10, &expected)
            .expect("return is absorbing, with no extra trace events");
    }

    #[test]
    fn different_widening_inputs_and_addends_execute_the_same_semantic_family() {
        // These are concrete controls, NOT a universal or exhaustive proof.
        for (input, addend) in [(0, 0), (1, 3), (127, 1000), (255, 65280)] {
            let (program, expected) = widening_program(input, addend);
            model().check_execution(&program, 7, &expected).expect("in-range family control");
        }
    }

    #[test]
    fn changed_addend_does_not_prove_the_old_return() {
        let (_, old) = widening_program(255, 1);
        let (changed, correct) = widening_program(255, 2);
        assert!(model().check_execution(&changed, 7, &old).is_err());
        model().check_execution(&changed, 7, &correct).expect("close positive twin returns 257");
    }

    #[test]
    fn overflowing_u16_checked_add_panics_and_never_executes_return() {
        let (program, expected) = widening_program(255, 65535);
        assert_eq!(expected.outcome, ScalarOutcome::Panic);
        model()
            .check_execution(&program, 7, &expected)
            .expect("actual width-16 overflow flag drives panic");
        let mut lie = expected.clone();
        lie.outcome = ScalarOutcome::Returned(ScalarValue::U16(254));
        assert!(model().check_execution(&program, 7, &lie).is_err());
    }

    #[test]
    fn u8_overflowing_add_keeps_both_wrapped_value_and_flag() {
        let program = ScalarProgram {
            locals: vec![
                local(ScalarType::U8, Some(ScalarValue::U8(255))),
                local(ScalarType::U8, Some(ScalarValue::U8(1))),
                local(ScalarType::CheckedU8, None),
            ],
            instructions: vec![
                ScalarInstruction::Assign(
                    2,
                    ScalarRvalue::Add { checked: true, left: 0, right: 1 },
                ),
                ScalarInstruction::Return(2),
            ],
        };
        let mut after = program.locals.clone();
        after[2].value = Some(ScalarValue::CheckedU8(0, true));
        let expected = ScalarObservation {
            outcome: ScalarOutcome::Returned(ScalarValue::CheckedU8(0, true)),
            locals: after,
            trace: vec![1, 0],
        };
        model()
            .check_execution(&program, 2, &expected)
            .expect("checked operation alone does not panic");
        let mut lie = expected.clone();
        lie.outcome = ScalarOutcome::Returned(ScalarValue::U16(256));
        assert!(model().check_execution(&program, 2, &lie).is_err());
    }

    #[test]
    fn u8_plain_add_wraps_without_inventing_an_assertion() {
        let program = ScalarProgram {
            locals: vec![
                local(ScalarType::U8, Some(ScalarValue::U8(255))),
                local(ScalarType::U8, Some(ScalarValue::U8(1))),
                local(ScalarType::U8, None),
            ],
            instructions: vec![
                ScalarInstruction::Assign(
                    2,
                    ScalarRvalue::Add { checked: false, left: 0, right: 1 },
                ),
                ScalarInstruction::Return(2),
            ],
        };
        let mut after = program.locals.clone();
        after[2].value = Some(ScalarValue::U8(0));
        model()
            .check_execution(
                &program,
                2,
                &ScalarObservation {
                    outcome: ScalarOutcome::Returned(ScalarValue::U8(0)),
                    locals: after,
                    trace: vec![1, 0],
                },
            )
            .expect("plain MIR-style addition wraps");
    }

    #[test]
    fn uninitialized_and_absent_locals_are_distinct_faults() {
        for (index, fault) in [(0, ScalarFault::Uninitialized), (1, ScalarFault::BadLocal)] {
            let program = ScalarProgram {
                locals: vec![local(ScalarType::U8, None)],
                instructions: vec![ScalarInstruction::Return(index)],
            };
            model()
                .check_execution(&program, 1, &fault_observation(&program, fault, vec![0]))
                .expect("read faults are explicit");
        }
    }

    #[test]
    fn incorrectly_typed_writes_leave_the_frame_unchanged() {
        let program = ScalarProgram {
            locals: vec![local(ScalarType::U16, None)],
            instructions: vec![ScalarInstruction::Assign(
                0,
                ScalarRvalue::Literal(ScalarValue::U8(1)),
            )],
        };
        model()
            .check_execution(
                &program,
                1,
                &fault_observation(&program, ScalarFault::TypeMismatch, vec![0]),
            )
            .expect("no implicit integer conversion on assignment");
    }

    #[test]
    fn ill_typed_initial_slot_is_rejected_when_read_not_reinterpreted() {
        let program = ScalarProgram {
            locals: vec![local(ScalarType::U8, Some(ScalarValue::U16(256)))],
            instructions: vec![ScalarInstruction::Return(0)],
        };
        model()
            .check_execution(
                &program,
                1,
                &fault_observation(&program, ScalarFault::TypeMismatch, vec![0]),
            )
            .expect("raw model frames cannot launder a width mismatch");
    }

    #[test]
    fn width_mismatch_and_invalid_projection_fault() {
        for rvalue in [
            ScalarRvalue::WidenU8ToU16(0),
            ScalarRvalue::CheckedValue(0),
            ScalarRvalue::CheckedFlag(0),
            ScalarRvalue::Add { checked: false, left: 0, right: 1 },
        ] {
            let program = ScalarProgram {
                locals: vec![
                    local(ScalarType::U16, Some(ScalarValue::U16(1))),
                    local(ScalarType::U8, Some(ScalarValue::U8(1))),
                ],
                instructions: vec![ScalarInstruction::Assign(0, rvalue)],
            };
            model()
                .check_execution(
                    &program,
                    1,
                    &fault_observation(&program, ScalarFault::TypeMismatch, vec![0]),
                )
                .expect("unsupported type combinations fault");
        }
    }

    #[test]
    fn unsupported_instruction_and_rvalue_are_never_skipped() {
        for instruction in [
            ScalarInstruction::Unsupported,
            ScalarInstruction::Assign(0, ScalarRvalue::Unsupported),
        ] {
            let program = ScalarProgram {
                locals: vec![local(ScalarType::U8, Some(ScalarValue::U8(1)))],
                instructions: vec![instruction, ScalarInstruction::Return(0)],
            };
            model()
                .check_execution(
                    &program,
                    2,
                    &fault_observation(&program, ScalarFault::Unsupported, vec![0]),
                )
                .expect("unmodeled operation stops execution");
        }
    }

    #[test]
    fn missing_return_is_not_success_or_out_of_fuel() {
        let program = ScalarProgram { locals: vec![], instructions: vec![] };
        model()
            .check_execution(
                &program,
                1,
                &fault_observation(&program, ScalarFault::MissingReturn, vec![]),
            )
            .expect("empty program is not a return");
    }

    #[test]
    fn fuel_exhaustion_preserves_exact_partial_state() {
        let (program, complete) = widening_program(255, 1);
        let mut after = program.locals.clone();
        after[1].value = Some(ScalarValue::U16(255));
        after[2].value = Some(ScalarValue::U16(1));
        let expected = ScalarObservation {
            outcome: ScalarOutcome::OutOfFuel,
            locals: after,
            trace: vec![1, 0],
        };
        model()
            .check_execution(&program, 2, &expected)
            .expect("fuel exhaustion isn't a return proof");
        assert!(model().check_execution(&program, 2, &complete).is_err());
    }

    #[test]
    fn changing_trace_or_nonreturned_local_breaks_the_kernel_judgment() {
        let (program, expected) = widening_program(255, 1);
        let mut bad_trace = expected.clone();
        bad_trace.trace.pop();
        assert!(model().check_execution(&program, 7, &bad_trace).is_err());
        let mut bad_frame = expected;
        bad_frame.locals[0].value = Some(ScalarValue::U8(0));
        assert!(model().check_execution(&program, 7, &bad_frame).is_err());
    }

    #[test]
    fn non_bool_assertion_is_a_type_fault_not_a_truthy_test() {
        let program = ScalarProgram {
            locals: vec![local(ScalarType::U8, Some(ScalarValue::U8(1)))],
            instructions: vec![ScalarInstruction::Assert { local: 0, expected: true }],
        };
        model()
            .check_execution(
                &program,
                1,
                &fault_observation(&program, ScalarFault::TypeMismatch, vec![0]),
            )
            .expect("integer one is not boolean true");
    }

    #[test]
    fn bounded_request_limit_is_an_error_not_a_model_verdict() {
        let (program, expected) = widening_program(255, 1);
        let error = model().check_execution(&program, 513, &expected).unwrap_err();
        assert!(error.contains("limits"), "{error}");
    }

    #[test]
    fn empty_or_truncated_model_cannot_construct_an_environment() {
        for source in ["", SCALAR_MODEL_SOURCE.split("def sm_observe").next().unwrap()] {
            let error =
                ScalarExecutionModel::from_source(source).err().expect("missing model must fail");
            assert!(error.contains("missing required declaration"), "{error}");
        }
    }

    #[test]
    fn key_model_declaration_requires_its_actual_expected_type() {
        let source = format!(
            "{}\ndef sm_observe (state : SMState) : Nat := 0\n",
            SCALAR_MODEL_SOURCE.split("def sm_observe").next().unwrap()
        );
        let error = ScalarExecutionModel::from_source(&source)
            .err()
            .expect("wrong observation type must fail");
        assert!(error.contains("sm_observe has the wrong type"), "{error}");
    }

    #[test]
    fn even_foundational_axioms_outside_a_selected_prefix_are_rejected() {
        let source = format!(
            "{SCALAR_MODEL_SOURCE}\ndef outsidePrefix (a b : Prop) (h : a ↔ b) : a = b := propext h\n"
        );
        let error =
            ScalarExecutionModel::from_source(&source).err().expect("model must remain axiom-free");
        assert!(error.contains("outsidePrefix has unchecked/axiom debt"), "{error}");
    }

    #[test]
    fn a_bare_natural_is_not_a_finite_uint_carrier() {
        let tc = TypeChecker::new(model().environment());
        tc.check_type(&value_term(ScalarValue::U8(255)), &constant("SMValue"))
            .expect("genuine finite literal");
        let forged = call("UInt8.ofBitVec", [Expr::nat_lit(256)]);
        assert!(tc.check_type(&forged, &constant("UInt8")).is_err());
    }

    #[test]
    fn huge_local_indices_are_resource_errors_not_long_kernel_recursions() {
        let program = ScalarProgram {
            locals: vec![],
            instructions: vec![ScalarInstruction::Return(u32::MAX)],
        };
        let expected = fault_observation(&program, ScalarFault::BadLocal, vec![0]);
        let error = model().check_execution(&program, 1, &expected).unwrap_err();
        assert!(error.contains("limits"), "{error}");
    }

    #[test]
    fn assertion_polarity_is_semantic_and_panic_is_absorbing() {
        let program = ScalarProgram {
            locals: vec![local(ScalarType::Bool, Some(ScalarValue::Bool(false)))],
            instructions: vec![
                ScalarInstruction::Assert { local: 0, expected: true },
                ScalarInstruction::Unsupported,
            ],
        };
        let expected = ScalarObservation {
            outcome: ScalarOutcome::Panic,
            locals: program.locals.clone(),
            trace: vec![0],
        };
        model()
            .check_execution(&program, 2, &expected)
            .expect("false versus expected true panics immediately");
        let changed = ScalarProgram {
            instructions: vec![
                ScalarInstruction::Assert { local: 0, expected: false },
                ScalarInstruction::Return(0),
            ],
            ..program
        };
        assert!(model().check_execution(&changed, 2, &expected).is_err());
        model()
            .check_execution(
                &changed,
                2,
                &ScalarObservation {
                    outcome: ScalarOutcome::Returned(ScalarValue::Bool(false)),
                    locals: changed.locals.clone(),
                    trace: vec![1, 0],
                },
            )
            .expect("opposite polarity has a genuine successful control");
    }

    #[test]
    fn u8_maximum_without_overflow_retains_a_false_flag() {
        let program = ScalarProgram {
            locals: vec![
                local(ScalarType::U8, Some(ScalarValue::U8(255))),
                local(ScalarType::U8, Some(ScalarValue::U8(0))),
                local(ScalarType::CheckedU8, None),
            ],
            instructions: vec![
                ScalarInstruction::Assign(
                    2,
                    ScalarRvalue::Add { checked: true, left: 0, right: 1 },
                ),
                ScalarInstruction::Return(2),
            ],
        };
        let mut after = program.locals.clone();
        after[2].value = Some(ScalarValue::CheckedU8(255, false));
        model()
            .check_execution(
                &program,
                2,
                &ScalarObservation {
                    outcome: ScalarOutcome::Returned(ScalarValue::CheckedU8(255, false)),
                    locals: after,
                    trace: vec![1, 0],
                },
            )
            .expect("maximum is in range, not overflow");
    }

    #[test]
    fn u16_exact_overflow_threshold_is_not_an_off_by_one() {
        for (input, expected_outcome) in
            [(0, ScalarOutcome::Returned(ScalarValue::U16(65535))), (1, ScalarOutcome::Panic)]
        {
            let (program, expected) = widening_program(input, 65535);
            assert_eq!(expected.outcome, expected_outcome);
            model()
                .check_execution(&program, 7, &expected)
                .expect("65535 is in range; 65536 overflows");
        }
    }

    #[test]
    fn zero_fuel_does_not_inspect_even_an_empty_program() {
        for instructions in [vec![], vec![ScalarInstruction::Unsupported]] {
            let program = ScalarProgram { locals: vec![], instructions };
            model()
                .check_execution(
                    &program,
                    0,
                    &ScalarObservation {
                        outcome: ScalarOutcome::OutOfFuel,
                        locals: vec![],
                        trace: vec![],
                    },
                )
                .expect("zero transitions means no outcome or trace invented");
        }
    }

    #[test]
    fn both_boolean_values_respect_both_assertion_polarities() {
        for actual in [false, true] {
            for expected in [false, true] {
                let program = ScalarProgram {
                    locals: vec![local(ScalarType::Bool, Some(ScalarValue::Bool(actual)))],
                    instructions: vec![
                        ScalarInstruction::Assert { local: 0, expected },
                        ScalarInstruction::Return(0),
                    ],
                };
                let (outcome, trace) = if actual == expected {
                    (ScalarOutcome::Returned(ScalarValue::Bool(actual)), vec![1, 0])
                } else {
                    (ScalarOutcome::Panic, vec![0])
                };
                model()
                    .check_execution(
                        &program,
                        2,
                        &ScalarObservation { outcome, locals: program.locals.clone(), trace },
                    )
                    .expect("complete boolean polarity control");
            }
        }
    }
}
