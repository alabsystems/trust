//! Fixed axiom-free raw-MIR-shaped semantics, not rustc's formal semantics.

use clean_kernel::ConstantKind;

use super::*;

// Place projection tags: 0 = whole local, 1 = pair value, 2 = pair flag.
// A place's local index is bound as `loc`, never `local`: `local` is a Lean
// 4.8.0 keyword, and Clean refuses a keyword wherever a name is bound (clean
// fd20888d5, 2026-09-27: "Lean keywords are never names").
// A Move reads like Copy (the current non-call interpreter behavior), while
// recording a conservative no-reread discipline. This does not settle Rust's
// general move/memory semantics or grant authority to a compiler snapshot.
pub(super) const SOURCE: &str = r#"
inductive RMPlace : Type
| mk : Nat → Nat → RMPlace
inductive RMPlaces : Type
| nil : RMPlaces
| cons : RMPlace → RMPlaces → RMPlaces
inductive RMOperand : Type
| copy : RMPlace → RMOperand
| move : RMPlace → RMOperand
| constant : SMValue → RMOperand
inductive RMRetag : Type
| no : RMRetag
| yes : RMRetag
inductive RMRvalue : Type
| use : RMOperand → RMRetag → RMRvalue
| widen : RMOperand → RMRvalue
| checkedAdd : RMOperand → RMOperand → RMRvalue
| unsupported : RMRvalue
inductive RMStatement : Type
| assign : Nat → RMRvalue → RMStatement
| storageLive : Nat → RMStatement
| storageDead : Nat → RMStatement
| unsupported : RMStatement
inductive RMUnwind : Type
| continue : RMUnwind
| unreachable : RMUnwind
| terminate : RMUnwind
| cleanup : Nat → RMUnwind
inductive RMTerminator : Type
| assertOverflowAdd : RMOperand → Bool → Nat → RMUnwind → RMOperand → RMOperand → RMTerminator
| goto : Nat → RMTerminator
| ret : RMTerminator
| unsupported : RMTerminator
inductive RMCode : Type
| statement : RMStatement → RMCode → RMCode
| terminal : RMTerminator → RMCode
inductive RMBlocks : Type
| nil : RMBlocks
| cons : Bool → RMCode → RMBlocks → RMBlocks
inductive RMTypes : Type
| nil : RMTypes
| cons : SMTy → RMTypes → RMTypes
inductive RMAbi : Type
| rust : RMAbi
| unsupported : RMAbi
inductive RMBody : Type
| mk : RMAbi → Nat → RMTypes → RMBlocks → RMBody
inductive RMFailure : Type
| scalar : SMFault → RMFailure
| moved : RMFailure
| badBlock : RMFailure
| badPc : RMFailure
| cleanup : RMFailure
| managedStorage : RMFailure
| unsupported : RMFailure
inductive RMRead : Type
| value : SMValue → RMPlaces → RMRead
| fault : RMFailure → RMPlaces → RMRead
inductive RMOutcome : Type
| returned : SMValue → RMOutcome
| unwind : RMUnwind → RMOutcome
| fault : RMFailure → RMOutcome
| outOfFuel : RMOutcome
inductive RMTrace : Type
| nil : RMTrace
| cons : Nat → Nat → Nat → RMTrace → RMTrace
inductive RMState : Type
| running : Nat → Nat → SMFrame → RMPlaces → RMTrace → RMState
| halted : RMOutcome → SMFrame → RMPlaces → RMTrace → RMState
inductive RMObservation : Type
| mk : RMOutcome → SMFrame → RMPlaces → RMTrace → RMObservation
inductive RMBridgeObservation : Type
| mk : RMObservation → RMObservation → SMObservation → RMBridgeObservation

def rm_overlap_fields (a : Nat) (b : Nat) : Bool :=
  Bool.rec (fun _ => Bool)
    (Bool.rec (fun _ => Bool) (Nat.beq a b) true (Nat.beq b 0)) true (Nat.beq a 0)
def rm_overlap (a : RMPlace) (b : RMPlace) : Bool :=
  match a with
  | RMPlace.mk ai af => match b with
    | RMPlace.mk bi bf => Bool.rec (fun _ => Bool) false (rm_overlap_fields af bf) (Nat.beq ai bi)
def rm_blocked (places : RMPlaces) (place : RMPlace) : Bool :=
  RMPlaces.rec (fun _ => Bool) false
    (fun previous rest ih => Bool.rec (fun _ => Bool) ih true (rm_overlap previous place)) places
def rm_project (field : Nat) (read : SMRead) : SMRead :=
  match field with
  | 0 => read
  | 1 => sm_map_read sm_project_value read
  | 2 => sm_map_read sm_project_flag read
  | _ => SMRead.fault SMFault.badLocal
def rm_read_place (frame : SMFrame) (place : RMPlace) : SMRead :=
  match place with
  | RMPlace.mk loc field => rm_project field (sm_read frame loc)
def rm_scalar_read (read : SMRead) (moves : RMPlaces) : RMRead :=
  match read with
  | SMRead.value value => RMRead.value value moves
  | SMRead.fault failure => RMRead.fault (RMFailure.scalar failure) moves
def rm_loaded (read : SMRead) (moves : RMPlaces) (place : RMPlace) (moving : Bool) : RMRead :=
  match read with
  | SMRead.value value => RMRead.value value
      (Bool.rec (fun _ => RMPlaces) moves (RMPlaces.cons place moves) moving)
  | SMRead.fault failure => RMRead.fault (RMFailure.scalar failure) moves
def rm_load (frame : SMFrame) (moves : RMPlaces) (place : RMPlace) (moving : Bool) : RMRead :=
  Bool.rec (fun _ => RMRead)
    (rm_loaded (rm_read_place frame place) moves place moving)
    (RMRead.fault RMFailure.moved moves) (rm_blocked moves place)
def rm_operand (frame : SMFrame) (moves : RMPlaces) (operand : RMOperand) : RMRead :=
  match operand with
  | RMOperand.copy place => rm_load frame moves place false
  | RMOperand.move place => rm_load frame moves place true
  | RMOperand.constant value => RMRead.value value moves

-- This is an explicit rule over SMValue's CLOSED pointer-free constructors,
-- not a Rust pointer/heap/provenance retag semantics or simulation theorem.
-- No catch-all case may silently admit a future reference-like carrier.
def rm_retag_value (value : SMValue) : SMValue :=
  match value with
  | SMValue.u8 x => SMValue.u8 x
  | SMValue.u16 x => SMValue.u16 x
  | SMValue.bool x => SMValue.bool x
  | SMValue.pair8 x flag => SMValue.pair8 x flag
  | SMValue.pair16 x flag => SMValue.pair16 x flag
theorem rm_retag_value_identity (value : SMValue) : rm_retag_value value = value :=
  match value with
  | SMValue.u8 x => rfl
  | SMValue.u16 x => rfl
  | SMValue.bool x => rfl
  | SMValue.pair8 x flag => rfl
  | SMValue.pair16 x flag => rfl
def rm_retag_read (read : RMRead) : RMRead :=
  match read with
  | RMRead.value value moves => RMRead.value (rm_retag_value value) moves
  | RMRead.fault failure moves => RMRead.fault failure moves
theorem rm_retag_read_identity (read : RMRead) : rm_retag_read read = read :=
  match read with
  | RMRead.value value moves => match value with
    | SMValue.u8 x => rfl
    | SMValue.u16 x => rfl
    | SMValue.bool x => rfl
    | SMValue.pair8 x flag => rfl
    | SMValue.pair16 x flag => rfl
  | RMRead.fault failure moves => rfl
def rm_use (retag : RMRetag) (read : RMRead) : RMRead :=
  match retag with
  | RMRetag.no => read
  | RMRetag.yes => rm_retag_read read
theorem rm_use_scalar_rule (retag : RMRetag) (read : RMRead) : rm_use retag read = read :=
  match retag with
  | RMRetag.no => rfl
  | RMRetag.yes => rm_retag_read_identity read

def rm_widen_read (read : RMRead) : RMRead :=
  match read with
  | RMRead.value value moves => rm_scalar_read (sm_widen value) moves
  | RMRead.fault failure moves => RMRead.fault failure moves
def rm_add_right (left : SMValue) (read : RMRead) : RMRead :=
  match read with
  | RMRead.value right moves => rm_scalar_read (sm_add_values true left right) moves
  | RMRead.fault failure moves => RMRead.fault failure moves
def rm_add_left (frame : SMFrame) (right : RMOperand) (read : RMRead) : RMRead :=
  match read with
  | RMRead.value left moves => rm_add_right left (rm_operand frame moves right)
  | RMRead.fault failure moves => RMRead.fault failure moves
def rm_rvalue (frame : SMFrame) (moves : RMPlaces) (rvalue : RMRvalue) : RMRead :=
  match rvalue with
  | RMRvalue.use operand retag => rm_use retag (rm_operand frame moves operand)
  | RMRvalue.widen operand => rm_widen_read (rm_operand frame moves operand)
  | RMRvalue.checkedAdd left right => rm_add_left frame right (rm_operand frame moves left)
  | RMRvalue.unsupported => RMRead.fault RMFailure.unsupported moves

def rm_forget_local (moves : RMPlaces) (destination : Nat) : RMPlaces :=
  RMPlaces.rec (fun _ => RMPlaces) RMPlaces.nil
    (fun place rest ih => match place with
      | RMPlace.mk loc field => Bool.rec (fun _ => RMPlaces)
          (RMPlaces.cons place ih) ih (Nat.beq loc destination)) moves
def rm_finish_write (bb : Nat) (pc : Nat) (before : SMFrame) (moves : RMPlaces)
    (trace : RMTrace) (destination : Nat) (write : SMWrite) : RMState :=
  match write with
  | SMWrite.frame after => RMState.running bb (Nat.succ pc) after (rm_forget_local moves destination) trace
  | SMWrite.fault failure => RMState.halted (RMOutcome.fault (RMFailure.scalar failure)) before moves trace
def rm_assign (bb : Nat) (pc : Nat) (frame : SMFrame) (trace : RMTrace)
    (destination : Nat) (read : RMRead) : RMState :=
  match read with
  | RMRead.value value moves => rm_finish_write bb pc frame moves trace destination (sm_write frame destination value)
  | RMRead.fault failure moves => RMState.halted (RMOutcome.fault failure) frame moves trace
def rm_statement (bb : Nat) (pc : Nat) (frame : SMFrame) (moves : RMPlaces)
    (trace : RMTrace) (statement : RMStatement) : RMState :=
  match statement with
  | RMStatement.assign destination rvalue => rm_assign bb pc frame
      (RMTrace.cons bb pc 0 trace) destination (rm_rvalue frame moves rvalue)
  | RMStatement.storageLive _ => RMState.halted (RMOutcome.fault RMFailure.managedStorage)
      frame moves (RMTrace.cons bb pc 4 trace)
  | RMStatement.storageDead _ => RMState.halted (RMOutcome.fault RMFailure.managedStorage)
      frame moves (RMTrace.cons bb pc 5 trace)
  | RMStatement.unsupported => RMState.halted (RMOutcome.fault RMFailure.unsupported)
      frame moves (RMTrace.cons bb pc 6 trace)
def rm_assert_bool (frame : SMFrame) (moves : RMPlaces) (trace : RMTrace)
    (expected : Bool) (target : Nat) (unwind : RMUnwind) (value : SMValue) : RMState :=
  match value with
  | SMValue.bool actual => Bool.rec (fun _ => RMState)
      (RMState.halted (RMOutcome.unwind unwind) frame moves trace)
      (RMState.running target 0 frame moves trace) (Bool.beq actual expected)
  | _ => RMState.halted (RMOutcome.fault (RMFailure.scalar SMFault.typeMismatch)) frame moves trace
def rm_assert_read (frame : SMFrame) (trace : RMTrace) (expected : Bool)
    (target : Nat) (unwind : RMUnwind) (read : RMRead) : RMState :=
  match read with
  | RMRead.value value moves => rm_assert_bool frame moves trace expected target unwind value
  | RMRead.fault failure moves => RMState.halted (RMOutcome.fault failure) frame moves trace
def rm_return (frame : SMFrame) (trace : RMTrace) (read : RMRead) : RMState :=
  match read with
  | RMRead.value value moves => RMState.halted (RMOutcome.returned value) frame moves trace
  | RMRead.fault failure moves => RMState.halted (RMOutcome.fault failure) frame moves trace
def rm_terminal (bb : Nat) (pc : Nat) (frame : SMFrame) (moves : RMPlaces)
    (trace : RMTrace) (terminal : RMTerminator) : RMState :=
  match terminal with
  | RMTerminator.assertOverflowAdd condition expected target unwind left right =>
      rm_assert_read frame (RMTrace.cons bb pc 3 trace) expected target unwind (rm_operand frame moves condition)
  | RMTerminator.goto target => RMState.running target 0 frame moves (RMTrace.cons bb pc 1 trace)
  | RMTerminator.ret => rm_return frame (RMTrace.cons bb pc 2 trace)
      (rm_operand frame moves (RMOperand.copy (RMPlace.mk 0 0)))
  | RMTerminator.unsupported => RMState.halted (RMOutcome.fault RMFailure.unsupported)
      frame moves (RMTrace.cons bb pc 6 trace)

def rm_code (bb : Nat) (pc : Nat) (frame : SMFrame) (moves : RMPlaces)
    (trace : RMTrace) (code : RMCode) (index : Nat) : RMState :=
  RMCode.rec (fun _ => Nat → RMState)
    (fun statement rest ih => fun i => Nat.rec (fun _ => RMState)
      (rm_statement bb pc frame moves trace statement) (fun n _ => ih n) i)
    (fun terminal => fun i => Nat.rec (fun _ => RMState)
      (rm_terminal bb pc frame moves trace terminal)
      (fun _ _ => RMState.halted (RMOutcome.fault RMFailure.badPc) frame moves trace) i) code index
def rm_block (bb : Nat) (pc : Nat) (frame : SMFrame) (moves : RMPlaces)
    (trace : RMTrace) (blocks : RMBlocks) : RMState :=
  RMBlocks.rec (fun _ => Nat → RMState)
    (fun _ => RMState.halted (RMOutcome.fault RMFailure.badBlock) frame moves trace)
    (fun cleanup code rest ih => fun index => Nat.rec (fun _ => RMState)
      (Bool.rec (fun _ => RMState) (rm_code bb pc frame moves trace code pc)
        (RMState.halted (RMOutcome.fault RMFailure.cleanup) frame moves trace) cleanup)
      (fun n _ => ih n) index) blocks bb
def rm_step (body : RMBody) (state : RMState) : RMState :=
  match state with
  | RMState.halted outcome frame moves trace => RMState.halted outcome frame moves trace
  | RMState.running bb pc frame moves trace => match body with
    | RMBody.mk abi arguments types blocks => rm_block bb pc frame moves trace blocks
def rm_run (fuel : Nat) (body : RMBody) (initial : RMState) : RMState :=
  Nat.rec (fun _ => RMState) initial (fun _ previous => rm_step body previous) fuel
def rm_observe (state : RMState) : RMObservation :=
  match state with
  | RMState.halted outcome frame moves trace => RMObservation.mk outcome frame moves trace
  | RMState.running bb pc frame moves trace => RMObservation.mk RMOutcome.outOfFuel frame moves trace
def rm_frame (types : RMTypes) (input : UInt8) : SMFrame :=
  RMTypes.rec (fun _ => Nat → SMFrame)
    (fun _ => SMFrame.nil)
    (fun ty rest ih => fun index => SMFrame.cons ty
      (Bool.rec (fun _ => SMSlot) SMSlot.uninitialized (SMSlot.value (SMValue.u8 input))
        (Nat.beq index 1)) (ih (Nat.succ index))) types 0
def rm_initial (body : RMBody) (input : UInt8) : RMState :=
  match body with
  | RMBody.mk abi arguments types blocks =>
      RMState.running 0 0 (rm_frame types input) RMPlaces.nil RMTrace.nil
"#;

pub(super) fn environment() -> Result<Environment, String> {
    use crate::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
    let source = format!("{}\n{SOURCE}", crate::scalar_return::SCALAR_MODEL_SOURCE);
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "TrustScalarMirModel".into(),
            path: "<fixed scalar MIR-shaped model>".into(),
            source,
        }],
        false,
    );
    let context = batch.accepted_context().ok_or_else(|| {
        format!("MIR model registration failed: {:?}; {:?}", batch.errors(), batch.attempt())
    })?;
    let env = context.environment().clone();
    for name in context.owned_declarations() {
        let info = env.get_const(name).ok_or("MIR model declaration disappeared")?;
        if info.kind == ConstantKind::Axiom
            || env.is_unsafe(name)
            || env.is_partial(name)
            || !env.axiom_deps(name).is_some_and(|a| a.is_empty())
            || !env.foundational_axiom_deps(name).is_some_and(|a| a.is_empty())
        {
            return Err(format!("MIR model {name} has unchecked/axiom debt"));
        }
        if let Some(value) = &info.value {
            TypeChecker::new(&env)
                .check_type(value, &info.type_)
                .map_err(|e| format!("MIR model {name} recheck: {e:?}"))?;
        }
    }
    for (name, ty) in [
        ("RMBody", Expr::type_()),
        ("RMRetag", Expr::type_()),
        ("RMRvalue.use", pi(c("RMOperand"), pi(c("RMRetag"), c("RMRvalue")))),
        ("rm_retag_value", pi(c("SMValue"), c("SMValue"))),
        ("rm_use", pi(c("RMRetag"), pi(c("RMRead"), c("RMRead")))),
        (
            "rm_use_scalar_rule",
            pi(
                c("RMRetag"),
                pi(
                    c("RMRead"),
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        [c("RMRead"), app("rm_use", [Expr::bvar(1), Expr::bvar(0)]), Expr::bvar(0)],
                    ),
                ),
            ),
        ),
        ("RMBridgeObservation", Expr::type_()),
        ("rm_run", pi(c("Nat"), pi(c("RMBody"), pi(c("RMState"), c("RMState"))))),
        ("rm_observe", pi(c("RMState"), c("RMObservation"))),
    ] {
        if !context.owns_declaration(&Name::from_string(name)) {
            return Err(format!("missing MIR model declaration {name}"));
        }
        TypeChecker::new(&env)
            .check_type(&c(name), &ty)
            .map_err(|e| format!("MIR model {name} type: {e:?}"))?;
    }
    Ok(env)
}
