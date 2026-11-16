/- Fresh retained-value replay. No source proof producer/tactic is re-run here.
   This is SAME Lean kernel evidence; independent Clean recheck is separate. -/
import Lean
import MiniRustU64RetainedClaims
import MiniRustAllocate8Audit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`MiniRustU64Function, `MiniRustU64Execution, `MiniRustU64Return,
    `MiniRustU64Step, `MiniRustU64Entry, `MiniRustU64Call, `MiniRustU64AllocatedCall,
    `MiniRustU64Run, `MiniRustU64Correspondence, `MiniRustU64Availability,
    `MiniRustU64Controls, `MiniRustU64AvailabilityControls, `MiniRustU64RetainedClaims, `MiniRustAllocate8Safety,
    `MiniRustAllocate8Room, `MiniRustAllocate8Audit]
  let prefixes : Array Name := #[`MiniRustU64Function, `MiniRustU64Execution, `MiniRustU64Return,
    `MiniRustU64Step, `MiniRustU64Entry, `MiniRustU64Call, `MiniRustU64AllocatedCall,
    `MiniRustU64Run, `MiniRustU64Correspondence, `MiniRustU64Availability,
    `MiniRustU64Controls, `MiniRustU64AvailabilityControls, `MiniRustU64RetainedClaims, `MiniRustAllocate8Safety]
  let base ← liftIO <| importModules #[{module := `SemRMemory}, {module := `U64Addition}] {} 0
  let mut targets : Std.HashMap Name ConstantInfo := {}
  let mut theorems := 0
  let mut sourceNames : Array Name := #[]
  let mut implementations : Array Name := #[]
  for (name, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[idx.toNat]!
      if modules.contains module && (prefixes.any (·.isPrefixOf name) ||
          name.toString.startsWith s!"_private.{module}.") then
        if ci.isUnsafe || ci.isPartial then
          -- Lean emits a separate partial executable implementation for a
          -- regular recursive definition. It is NOT logical proof evidence.
          -- Require its actual safe parent/type, census it, and later reject
          -- ANY unsafe/partial constant in the logical dependency closure.
          let some parent := Compiler.isUnsafeRecName? name |
            throwError "unclassified unsafe/partial source declaration {name}"
          let some (.defnInfo logical) := env.find? parent |
            throwError "generated implementation has no actual logical parent {name}"
          let logicalInfo := ConstantInfo.defnInfo logical
          if logicalInfo.isUnsafe || logicalInfo.isPartial then
            throwError "implementation parent is not safe {parent}"
          let .defnInfo executable := ci | throwError "unexpected implementation kind {name}"
          unless executable.type == logical.type && executable.levelParams == logical.levelParams do
            throwError "implementation parent/type mismatch {name}"
          implementations := implementations.push name
          continue
        if let .axiomInfo _ := ci then throwError "new source axiom {name}"
        if ci.type.hasFVar || ci.type.hasLooseBVars then throwError "open source type {name}"
        if (base.find? name).isSome then throwError "new source root already in replay base {name}"
        if let .thmInfo _ := ci then
          theorems := theorems + 1
          for axiomName in (← collectAxioms name) do
            unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
              throwError "nonstandard axiom {axiomName} at {name}"
        targets := targets.insert name ci
        sourceNames := sourceNames.push name
  let required : Array Name := #[`MiniRustU64Call.actual_create, `MiniRustU64Call.create_frame_plan,
    `MiniRustU64AllocatedCall.call_tree_exact, `MiniRustU64Correspondence.full_tree_exact,
    `MiniRustU64Correspondence.original_function_correspondence,
    `MiniRustU64Correspondence.original_canonical_no_bad,
    `MiniRustU64Correspondence.original_model_no_error,
    `MiniRustU64Availability.full_function_available,
    `MiniRustU64AvailabilityControls.concrete_full64_available,
    `MiniRustU64AvailabilityControls.actual_maximum_input_wrap,
    `MiniRustU64AvailabilityControls.invalid_scheduler_refuses,
    `MiniRustU64Controls.valid_wrong_module_counterexample,
    `MiniRustU64Controls.deleted_private_allocation_refuses,
    `MiniRustU64Controls.wrong_continuation_refuses,
    `MiniRustU64RetainedClaims.original_blob_zero, `MiniRustU64RetainedClaims.complete_zero]
  for name in required do
    let some (.thmInfo _) := targets[name]? | throwError "required original theorem absent {name}"
  let mut pending := targets.toArray.map Prod.fst
  let mut visited : Std.HashSet Name := {}
  let mut budget := 100000
  while !pending.isEmpty do
    if budget == 0 then throwError "replay dependency bound"
    budget := budget - 1
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    let some ci := env.find? name | throwError "missing actual source declaration {name}"
    for dep in ci.getUsedConstantsAsSet do
      if (base.find? dep).isSome then continue
      let some value := env.find? dep | throwError "missing actual dependency {dep}"
      if value.isUnsafe || value.isPartial then throwError "unsafe/partial dependency {dep}"
      if let .axiomInfo _ := value then throwError "new dependency axiom {dep}"
      targets := targets.insert dep value
      pending := pending.push dep
  let checked ← liftIO <| Environment.replay targets base
  for (name, _) in targets do
    unless (checked.toKernelEnv.find? name).isSome do throwError "fresh kernel skipped {name}"
  let key := `MiniRustU64Correspondence.original_function_correspondence
  let some (.thmInfo original) := targets[key]? | throwError "original proof absent"
  let wrongProof := targets.insert key (.thmInfo {original with value := mkConst ``True.intro})
  let blobKey := `MiniRustU64RetainedClaims.original_blob_zero
  let some (.thmInfo blobProof) := targets[blobKey]? | throwError "retained original blob claim absent"
  let wrongSubject := targets.insert blobKey
    (.thmInfo {blobProof with type := mkConst `MiniRustU64RetainedClaims.WrongBlobClaim})
  let endpointKey := `MiniRustU64RetainedClaims.complete_zero
  let some (.thmInfo endpointProof) := targets[endpointKey]? | throwError "retained actual execution claim absent"
  let wrongWorld := targets.insert endpointKey
    (.thmInfo {endpointProof with type := mkConst `MiniRustU64RetainedClaims.DroppedZeroClaim})
  let wrongScalar := targets.insert endpointKey
    (.thmInfo {endpointProof with type := mkConst `MiniRustU64RetainedClaims.WrongScalarZeroClaim})
  for (label, mutation) in #[ ("proof", wrongProof), ("valid-wrong-module-closed", wrongSubject),
      ("deleted-private-world-closed", wrongWorld), ("wrong-result-closed", wrongScalar) ] do
    let failure ← liftIO do
      try
        let _ ← Environment.replay mutation base
        pure none
      catch error => pure (some error.toString)
    let some message := failure | throwError "fresh kernel accepted altered {label}"
    unless (message.toLower.splitOn "type mismatch").length > 1 do
      throwError "altered {label} refused for an unexpected reason: {message}"
    logInfo m!"MINIRUST_FUNCTION_MUTANT {label} actual-TypeMismatch-refused"
  logInfo m!"MINIRUST_FUNCTION_IMPLEMENTATIONS excluded-from-logic={implementations.size} actual-names={implementations}; no unsafe/partial logical dependency admitted"
  logInfo m!"MINIRUST_FUNCTION_REPLAY source-declarations={sourceNames.size} theorems={theorems} closure={targets.size} required={required.size} missing=0 new-axioms=0 replay-calls-producer=0; SAME Lean kernel, independent Clean remains separate"
