/- Constructive execution of the actual pinned contextual evaluator. The
   closure escapes its maker's frame and is passed to another function before
   application. Logical environment fields are not physical capture bytes. -/
import ClosureU64
import TrustIr.Proofs.GenericCoroPrefixLayer

namespace ClosureU64
open TrustIr
open TrustIr.GenericCoro.Prefix
set_option maxRecDepth 1024

theorem multiplication_word (a x : UInt64) :
    semBinOpValues .Mul .U64 (word a) (word x) = .ok (word (a * x)) := by
  simp [semBinOpValues, semIntBinOp, word, UInt64.toNat_mul,
    Int.natCast_mul, Int.natCast_emod,
    Except.bind, Except.pure, Bind.bind, Pure.pure]

theorem addition_word (left right : UInt64) :
    semBinOpValues .Add .U64 (word left) (word right) =
      .ok (word (left + right)) := by
  simp [semBinOpValues, semIntBinOp, word, UInt64.toNat_add,
    Int.natCast_add, Int.natCast_emod,
    Except.bind, Except.pure, Bind.bind, Pure.pure]

/-- All fields outside the fresh logical SSA frame are arbitrary. -/
def entryState (world : MachineState) : MachineState :=
  { world with locals := ValueMap.empty, nextValueId := 0 }

def pairState (world : MachineState) (a b : UInt64) : MachineState :=
  { world with
    locals := (ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)
    nextValueId := 2 }

def makerState (world : MachineState) (a b : UInt64) : MachineState :=
  { world with
    locals := ((ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)).set
      (valueId 2) (closure a b)
    nextValueId := 3 }

def tripleState (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := ((ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)).set
      (valueId 2) (word x)
    nextValueId := 3 }

def productState (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := (((ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)).set
      (valueId 2) (word x)).set (valueId 3) (word (a * x))
    nextValueId := 4 }

def targetState (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := ((((ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)).set
      (valueId 2) (word x)).set (valueId 3) (word (a * x))).set
      (valueId 4) (word (a * x + b))
    nextValueId := 5 }

def callerState (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := ((((ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)).set
      (valueId 2) (word x)).set (valueId 3) (closure a b)).set
      (valueId 4) (word (ClosureSource.useAffine a b x))
    nextValueId := 5 }

def callerPartial (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := (((ValueMap.empty.set (valueId 0) (word a)).set (valueId 1) (word b)).set
      (valueId 2) (word x)).set (valueId 3) (closure a b)
    nextValueId := 4 }

def applicationEntry (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := (ValueMap.empty.set (valueId 0) (closure a b)).set (valueId 1) (word x)
    nextValueId := 2 }

def applicationState (world : MachineState) (a b x : UInt64) : MachineState :=
  { world with
    locals := ((ValueMap.empty.set (valueId 0) (closure a b)).set (valueId 1) (word x)).set
      (valueId 2) (word (a * x + b))
    nextValueId := 3 }

@[simp] theorem word_not_poison (value : UInt64) : (word value).isPoison = false := rfl

@[simp] theorem closure_not_poison (a b : UInt64) : (closure a b).isPoison = false := rfl

@[simp] theorem word_reject_partial (value : UInt64) (operation : String) :
    Sem.rejectPartial (word value) operation = (pure () : Sem Unit) := rfl

@[simp] theorem set_twice (locals : ValueMap) (id : ValueId) (value : Value) :
    (locals.set id value).set id value = locals.set id value := by
  funext key
  by_cases same : key == id <;> simp [ValueMap.set, same]

theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (world : MachineState) :
    Sem.run (StateT.bind action next) world =
      Except.bind (Sem.run action world) (fun pair => Sem.run (next pair.1) pair.2) := rfl

theorem run_pure {α : Type} (value : α) (world : MachineState) :
    Sem.run (StateT.pure value : Sem α) world = .ok (value, world) := rfl

theorem run_get (world : MachineState) : Sem.run Sem.getState world = .ok (world, world) := rfl

theorem run_set (before after : MachineState) :
    Sem.run (Sem.setState after) before = .ok ((), after) := rfl

theorem lookup_pair_first (world : MachineState) (a b : UInt64) :
    Sem.run (Sem.lookupValue (valueId 0)) (pairState world a b) =
      .ok (word a, pairState world a b) := rfl

theorem lookup_pair_second (world : MachineState) (a b : UInt64) :
    Sem.run (Sem.lookupValue (valueId 1)) (pairState world a b) =
      .ok (word b, pairState world a b) := rfl

theorem lookup_pair_all (world : MachineState) (a b : UInt64) :
    Sem.run ([valueId 0, valueId 1].mapM Sem.lookupValue) (pairState world a b) =
      .ok ([word a, word b], pairState world a b) := rfl

theorem fresh_closure (world : MachineState) (a b : UInt64) :
    Sem.run (Sem.bindFresh (closure a b)) (pairState world a b) =
      .ok (valueId 2, makerState world a b) := rfl

def finishConstruction (checked : Except SemError Value) : Sem InstrResult := do
  let value ← match checked with
    | .ok value => pure value
    | .error error => throw error
  let id ← Sem.bindFresh value
  pure (.value (some id))

theorem construction_action (ctx : EvalContext) (cid : ClosureTyId) (code : FuncId)
    (captures : List ValueId) :
    stepInstWithContext ctx (.MakeClosure cid code captures) =
      StateT.bind (captures.mapM Sem.lookupValue)
        (fun values => finishConstruction (makeClosureValue ctx cid code values)) := by
  rw [stepInstWithContext_makeClosure]
  rfl

theorem lookup_pair_then (next : List Value → Sem InstrResult)
    (world : MachineState) (a b : UInt64) :
    Sem.run (StateT.bind ([valueId 0, valueId 1].mapM Sem.lookupValue) next)
      (pairState world a b) = Sem.run (next [word a, word b]) (pairState world a b) := by
  rw [run_bind, lookup_pair_all]
  rfl

theorem finish_construction_run (checked : Except SemError Value)
    (world : MachineState) (a b : UInt64) :
    Sem.run (finishConstruction checked) (pairState world a b) =
      match checked with
      | .ok value => .ok (.value (some (valueId 2)),
          { pairState world a b with
            locals := (pairState world a b).locals.set (valueId 2) value
            nextValueId := 3 })
      | .error error => .error error := by
  cases checked <;> rfl

theorem maker_parameters (world : MachineState) (a b : UInt64) :
    Sem.run (bindBlockParamsChecked [(valueId 0, .U64), (valueId 1, .U64)]
      [word a, word b]) (entryState world) = .ok ((), pairState world a b) := by
  simp [bindBlockParamsChecked, checkSSACharValues, checkSSACharValue, bindBlockParams,
    Sem.run, Sem.getState, Sem.setState, entryState, pairState, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem maker_constructs (depth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run (stepInstWithContext (context depth)
      (.MakeClosure nominal targetId [valueId 0, valueId 1])) (pairState world a b) =
      .ok (.value (some (valueId 2)), makerState world a b) := by
  rw [construction_action, lookup_pair_then, finish_construction_run,
    construction_exact depth a b]
  rfl

theorem maker_result_bound (depth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run ((context depth).bindInstructionResults
      (.MakeClosure nominal targetId [valueId 0, valueId 1])
      (.value (some (valueId 2))) [valueId 2]) (makerState world a b) =
      .ok ((), makerState world a b) := by
  simp [EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, ssaInstructionResultTypes, ssaResultSourceType,
    localResultTypes, checkSSACharValues, checkSSACharValue,
    bindInstrResultDests, bindResultDests,
    Sem.run, Sem.getState, Sem.setState, Sem.lookupValue,
    MachineState.lookupValue, makerState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure] <;> rfl

theorem maker_body_step (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b : UInt64) :
    Sem.run (evalBodyStep recurse (context depth) callDepth .abort
      (.MakeClosure nominal targetId [valueId 0, valueId 1], [valueId 2]))
      (pairState world a b) = .ok (.yield (), makerState world a b) := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, maker_constructs]
  dsimp only [Except.bind]
  rw [run_bind, maker_result_bound]
  rfl

theorem maker_returns (depth callDepth : Nat) (world : MachineState) (a b : UInt64) :
    Sem.run (stepTermWithContext (context depth) callDepth maker.cfg
      (.Return [valueId 2]) .abort) (makerState world a b) =
      .ok (.terminator (.Ret [closure a b]), makerState world a b) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    makerState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

def makerBlock : BasicBlock :=
  { params := [(valueId 0, .U64), (valueId 1, .U64)]
    body := [.MakeClosure nominal targetId [valueId 0, valueId 1]]
    bodyResultDests := [[valueId 2]]
    terminator := .Return [valueId 2] }

theorem maker_block_lookup : maker.cfg ⟨0⟩ = some makerBlock := rfl

theorem maker_block_resolved (depth : Nat) :
    (context depth).resolveBlock makerBlock = makerBlock := rfl

theorem run_single_body {α : Type} (body : α → Unit → Sem (ForInStep Unit))
    (row : α) (before after : MachineState)
    (computed : Sem.run (body row ()) before = .ok (.yield (), after)) :
    Sem.run (forIn [row] () body) before = .ok ((), after) := by
  rw [List.forIn_cons]
  simp only [bind]
  rw [run_bind, computed]
  rfl

theorem maker_body_loop (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b : UInt64) :
    Sem.run (evalBody recurse (context depth) callDepth .abort
      [(.MakeClosure nominal targetId [valueId 0, valueId 1], [valueId 2])])
      (pairState world a b) = .ok ((), makerState world a b) := by
  unfold evalBody
  exact run_single_body _ _ _ _ (maker_body_step recurse depth callDepth world a b)

theorem run_returning_layer (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (cfg : CFG) (pc : BlockId) (block : BasicBlock) (args values : List Value)
    (before bound bodyAfter after : MachineState)
    (found : cfg pc = some block)
    (resolved : ctx.resolveBlock block = block)
    (parameters : Sem.run (bindBlockParamsChecked block.params args) before = .ok ((), bound))
    (body : Sem.run (evalBody recurse ctx callDepth .abort
      (bodyInstsWithResultDests block.body block.bodyResultDests)) bound = .ok ((), bodyAfter))
    (returned : Sem.run (stepTermWithContext ctx callDepth cfg block.terminator .abort)
      bodyAfter = .ok (.terminator (.Ret values), after)) :
    Sem.run (evalLayer recurse ctx callDepth cfg pc args .abort) before = .ok (values, after) := by
  unfold evalLayer
  rw [found]
  simp only [resolved, bind]
  rw [run_bind, parameters]
  dsimp only [Except.bind]
  rw [run_bind, body]
  dsimp only [Except.bind]
  rw [run_bind, returned]
  rfl

/-- The original evaluator completes construction and return with explicit
    sufficient fuel, preserving every field outside the fresh SSA frame. -/
theorem maker_body_evaluates (depth callDepth : Nat) (world : MachineState)
    (a b : UInt64) :
    Sem.run (stepNWithContext (context depth) 2 callDepth maker.cfg ⟨0⟩ [word a, word b])
      (entryState world) = .ok ([closure a b], makerState world a b) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := makerBlock) (bound := pairState world a b)
    (bodyAfter := makerState world a b)
  · exact maker_block_lookup
  · exact maker_block_resolved depth
  · exact maker_parameters world a b
  · exact maker_body_loop _ depth callDepth world a b
  · exact maker_returns depth callDepth world a b


theorem maker_body_evaluates_with_fuel (fuel depth callDepth : Nat) (world : MachineState)
    (a b : UInt64) :
    Sem.run (stepNWithContext (context depth) (fuel + 1) callDepth maker.cfg ⟨0⟩ [word a, word b])
      (entryState world) = .ok ([closure a b], makerState world a b) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := makerBlock) (bound := pairState world a b)
    (bodyAfter := makerState world a b)
  · exact maker_block_lookup
  · exact maker_block_resolved depth
  · exact maker_parameters world a b
  · exact maker_body_loop _ depth callDepth world a b
  · exact maker_returns depth callDepth world a b


theorem lookup_triple_first (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.lookupValue (valueId 0)) (tripleState world a b x) =
      .ok (word a, tripleState world a b x) := rfl

theorem lookup_triple_argument (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.lookupValue (valueId 2)) (tripleState world a b x) =
      .ok (word x, tripleState world a b x) := rfl

theorem fresh_product (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.bindFresh (word (a * x))) (tripleState world a b x) =
      .ok (valueId 3, productState world a b x) := rfl

def finishArithmetic (checked : Except SemError Value) : Sem ValueId :=
  match checked with
  | .ok value => Sem.bindFresh value
  | .error error => throw error

theorem deterministic_arithmetic_action (op : BinOp) (ty : Ty) (left right : ValueId) :
    semBinOpDeterministic op ty left right = (do
      let lhs ← Sem.lookupValue left
      let rhs ← Sem.lookupValue right
      Sem.rejectPartial lhs "BinOp"
      Sem.rejectPartial rhs "BinOp"
      finishArithmetic (semBinOpValues op ty lhs rhs)) := rfl

theorem binary_instruction_action (ctx : EvalContext) (op : BinOp) (left right : ValueId) :
    stepInstWithContext ctx (.BinOp op .U64 left right) =
      StateT.bind (semBinOp op .U64 left right)
        (fun id => StateT.pure (.value (some id))) := rfl

theorem multiplication_runs (world : MachineState) (a b x : UInt64) :
    Sem.run (semBinOp .Mul .U64 (valueId 0) (valueId 2)) (tripleState world a b x) =
      .ok (valueId 3, productState world a b x) := by
  change Sem.run (semBinOpDeterministic .Mul .U64 (valueId 0) (valueId 2)) _ = _
  rw [deterministic_arithmetic_action]
  simp only [bind]
  rw [run_bind, lookup_triple_first]
  dsimp only [Except.bind]
  rw [run_bind, lookup_triple_argument]
  dsimp only [Except.bind]
  rw [word_reject_partial]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [word_reject_partial]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [multiplication_word]
  exact fresh_product world a b x

theorem target_multiply_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepInstWithContext (context depth)
      (.BinOp .Mul .U64 (valueId 0) (valueId 2))) (tripleState world a b x) =
      .ok (.value (some (valueId 3)), productState world a b x) := by
  rw [binary_instruction_action, run_bind, multiplication_runs]
  rfl

theorem lookup_product (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.lookupValue (valueId 3)) (productState world a b x) =
      .ok (word (a * x), productState world a b x) := rfl

theorem lookup_offset (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.lookupValue (valueId 1)) (productState world a b x) =
      .ok (word b, productState world a b x) := rfl

theorem fresh_sum (world : MachineState) (a b x : UInt64) :
    Sem.run (Sem.bindFresh (word (a * x + b))) (productState world a b x) =
      .ok (valueId 4, targetState world a b x) := rfl

theorem addition_runs (world : MachineState) (a b x : UInt64) :
    Sem.run (semBinOp .Add .U64 (valueId 3) (valueId 1)) (productState world a b x) =
      .ok (valueId 4, targetState world a b x) := by
  change Sem.run (semBinOpDeterministic .Add .U64 (valueId 3) (valueId 1)) _ = _
  rw [deterministic_arithmetic_action]
  simp only [bind]
  rw [run_bind, lookup_product]
  dsimp only [Except.bind]
  rw [run_bind, lookup_offset]
  dsimp only [Except.bind]
  rw [word_reject_partial]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [word_reject_partial]
  simp only [pure]
  rw [run_bind, run_pure]
  dsimp only [Except.bind]
  rw [addition_word]
  exact fresh_sum world a b x

theorem target_add_step (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepInstWithContext (context depth)
      (.BinOp .Add .U64 (valueId 3) (valueId 1))) (productState world a b x) =
      .ok (.value (some (valueId 4)), targetState world a b x) := by
  rw [binary_instruction_action, run_bind, addition_runs]
  rfl

theorem target_multiply_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((context depth).bindInstructionResults
      (.BinOp .Mul .U64 (valueId 0) (valueId 2))
      (.value (some (valueId 3))) [valueId 3]) (productState world a b x) =
      .ok ((), productState world a b x) := by
  simp [EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, ssaInstructionResultTypes, ssaResultSourceType,
    localResultTypes, checkSSACharValues, checkSSACharValue,
    bindInstrResultDests, bindResultDests,
    Sem.run, Sem.getState, Sem.setState, Sem.lookupValue,
    MachineState.lookupValue, productState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure] <;> rfl

theorem target_add_bound (depth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run ((context depth).bindInstructionResults
      (.BinOp .Add .U64 (valueId 3) (valueId 1))
      (.value (some (valueId 4))) [valueId 4]) (targetState world a b x) =
      .ok ((), targetState world a b x) := by
  simp [EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, ssaInstructionResultTypes, ssaResultSourceType,
    localResultTypes, checkSSACharValues, checkSSACharValue,
    bindInstrResultDests, bindResultDests,
    Sem.run, Sem.getState, Sem.setState, Sem.lookupValue,
    MachineState.lookupValue, targetState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure] <;> rfl

theorem target_multiply_body_step (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep recurse (context depth) callDepth .abort
      (.BinOp .Mul .U64 (valueId 0) (valueId 2), [valueId 3])) (tripleState world a b x) =
      .ok (.yield (), productState world a b x) := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, target_multiply_step]
  dsimp only [Except.bind]
  rw [run_bind, target_multiply_bound]
  rfl

theorem target_add_body_step (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBodyStep recurse (context depth) callDepth .abort
      (.BinOp .Add .U64 (valueId 3) (valueId 1), [valueId 4])) (productState world a b x) =
      .ok (.yield (), targetState world a b x) := by
  unfold evalBodyStep
  simp only [bind]
  rw [run_bind, target_add_step]
  dsimp only [Except.bind]
  rw [run_bind, target_add_bound]
  rfl

theorem run_body_cons {α : Type} (body : α → Unit → Sem (ForInStep Unit))
    (row : α) (rows : List α) (before middle after : MachineState)
    (head : Sem.run (body row ()) before = .ok (.yield (), middle))
    (tail : Sem.run (forIn rows () body) middle = .ok ((), after)) :
    Sem.run (forIn (row :: rows) () body) before = .ok ((), after) := by
  rw [List.forIn_cons]
  simp only [bind]
  rw [run_bind, head]
  dsimp only [Except.bind]
  exact tail

def targetBlock : BasicBlock :=
  { params := [(valueId 0, .U64), (valueId 1, .U64), (valueId 2, .U64)]
    body := [.BinOp .Mul .U64 (valueId 0) (valueId 2),
      .BinOp .Add .U64 (valueId 3) (valueId 1)]
    bodyResultDests := [[valueId 3], [valueId 4]]
    terminator := .Return [valueId 4] }

theorem target_block_lookup : target.cfg ⟨0⟩ = some targetBlock := rfl

theorem target_block_resolved (depth : Nat) :
    (context depth).resolveBlock targetBlock = targetBlock := rfl

theorem target_parameters (world : MachineState) (a b x : UInt64) :
    Sem.run (bindBlockParamsChecked targetBlock.params [word a, word b, word x])
      (entryState world) = .ok ((), tripleState world a b x) := by
  simp [targetBlock, bindBlockParamsChecked, checkSSACharValues, checkSSACharValue,
    bindBlockParams, Sem.run, Sem.getState, Sem.setState, entryState, tripleState, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

theorem target_body_loop (recurse : Recurse) (depth callDepth : Nat)
    (world : MachineState) (a b x : UInt64) :
    Sem.run (evalBody recurse (context depth) callDepth .abort
      (bodyInstsWithResultDests targetBlock.body targetBlock.bodyResultDests))
      (tripleState world a b x) = .ok ((), targetState world a b x) := by
  unfold evalBody
  apply run_body_cons (middle := productState world a b x)
  · exact target_multiply_body_step recurse depth callDepth world a b x
  · exact run_single_body _ _ _ _ (target_add_body_step recurse depth callDepth world a b x)

theorem target_returns (depth callDepth : Nat) (world : MachineState) (a b x : UInt64) :
    Sem.run (stepTermWithContext (context depth) callDepth target.cfg
      (.Return [valueId 4]) .abort) (targetState world a b x) =
      .ok (.terminator (.Ret [word (a * x + b)]), targetState world a b x) := by
  simp [stepTermWithContext, closureTermWithContext, stepInst, semReturn,
    Sem.run, Sem.lookupValue, Sem.getState, MachineState.lookupValue,
    targetState, ValueMap.get, ValueMap.set, valueId,
    StateT.run, StateT.bind, StateT.get, StateT.pure,
    Except.bind, Except.pure, bind, pure, Bind.bind, Pure.pure]

/-- One block suffices for the actual selected lifted target, for all full-range
    captures and arguments, without changing any surrounding state field. -/
theorem target_body_evaluates (depth callDepth : Nat) (world : MachineState)
    (a b x : UInt64) :
    Sem.run (stepNWithContext (context depth) 1 callDepth target.cfg ⟨0⟩
      [word a, word b, word x]) (entryState world) =
      .ok ([word (a * x + b)], targetState world a b x) := by
  rw [stepNWithContext_succ_layer]
  apply run_returning_layer (block := targetBlock) (bound := tripleState world a b x)
    (bodyAfter := targetState world a b x)
  · exact target_block_lookup
  · exact target_block_resolved depth
  · exact target_parameters world a b x
  · exact target_body_loop _ depth callDepth world a b x
  · exact target_returns depth callDepth world a b x

theorem run_failing_layer (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (cfg : CFG) (pc : BlockId) (block : BasicBlock) (args : List Value)
    (before bound : MachineState) (error : SemError)
    (found : cfg pc = some block)
    (resolved : ctx.resolveBlock block = block)
    (parameters : Sem.run (bindBlockParamsChecked block.params args) before = .ok ((), bound))
    (body : Sem.run (evalBody recurse ctx callDepth .abort
      (bodyInstsWithResultDests block.body block.bodyResultDests)) bound = .error error) :
    Sem.run (evalLayer recurse ctx callDepth cfg pc args .abort) before = .error error := by
  unfold evalLayer
  rw [found]
  simp only [resolved, bind]
  rw [run_bind, parameters]
  dsimp only [Except.bind]
  rw [run_bind, body]
  rfl

theorem run_body_head_failure {α : Type} (body : α → Unit → Sem (ForInStep Unit))
    (row : α) (rows : List α) (before : MachineState) (error : SemError)
    (head : Sem.run (body row ()) before = .error error) :
    Sem.run (forIn (row :: rows) () body) before = .error error := by
  rw [List.forIn_cons]
  simp only [bind]
  rw [run_bind, head]
  rfl

theorem run_body_tail_failure {α : Type} (body : α → Unit → Sem (ForInStep Unit))
    (row : α) (rows : List α) (before middle : MachineState) (error : SemError)
    (head : Sem.run (body row ()) before = .ok (.yield (), middle))
    (tail : Sem.run (forIn rows () body) middle = .error error) :
    Sem.run (forIn (row :: rows) () body) before = .error error := by
  rw [List.forIn_cons]
  simp only [bind]
  rw [run_bind, head]
  dsimp only [Except.bind]
  exact tail


end ClosureU64
