/- Hostile endpoint controls for the actual function observation. -/
import MiniRustU64Correspondence
noncomputable section
namespace MiniRustU64Controls
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Run
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Concrete model data: the entry/body domains contain real inhabitants. -/
def base : MR_Machine :=
  { prog := ⟨[(⟨0⟩, MiniRustU64Function.function 7)], ⟨0⟩, [], [], []⟩
    mem := ⟨⟨[], ()⟩, []⟩, intptrcast := ⟨[]⟩, threads := [], active_thread := 0
    synchronized_threads := [], locks := [], global_ptrs := [], fn_ptrs := []
    vtable_ptrs := [], stdout := (), stderr := () }

def caller : MR_StackFrame :=
  frame 0 (ptr 0 8) (ptr 1 16) .BottomOfStack 0

theorem full64_wrap_boundary :
    ((modulus 64 - 1) + 7) % modulus 64 = 6 := by decide

theorem exit_allocation_population (model : MR_Machine) (parent : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value input : Nat) :
    (exitState model parent next before after callerAddr retAddr argAddr value input).mem.memory.allocations.length =
      before.length + after.length + 3 := by
  simp [exitState, single, retiredCells, callerWorld, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A semantically different endpoint deletes the second private allocation. -/
def droppedArgument (model : MR_Machine) (parent : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value input : Nat) : MR_Machine :=
  single model [(parent.set_next_block next).set_next_stmt 0]
    ⟨⟨callerWorld before after callerAddr (u64bytes value) ++
      [(slot (Int.ofNat retAddr) (u64bytes value)).set_live false], ()⟩,
      [⟨.Load, .None, Int.ofNat retAddr, 8⟩, ⟨.Store, .None, Int.ofNat callerAddr, 8⟩]⟩

theorem deleted_private_allocation_refuses (model : MR_Machine) (parent : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value input : Nat) :
    ¬ ReturnObservation model parent next before after callerAddr retAddr argAddr input
      (.ret [.int .u64 value])
      (.ok (), droppedArgument model parent next before after callerAddr retAddr argAddr value input) := by
  intro h
  change droppedArgument model parent next before after callerAddr retAddr argAddr value input =
    exitState model parent next before after callerAddr retAddr argAddr value input at h
  have size := congrArg (fun machine => machine.mem.memory.allocations.length) h
  dsimp only at size
  rw [exit_allocation_population] at size
  simp only [droppedArgument, single, callerWorld, List.length_append, List.length_cons, List.length_nil] at size
  omega

/-- A different caller continuation is not the same function-boundary result. -/
theorem wrong_continuation_refuses (model : MR_Machine) (parent : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation)
    (callerAddr retAddr argAddr value input : Nat) :
    ¬ ReturnObservation model parent next before after callerAddr retAddr argAddr input
      (.ret [.int .u64 value])
      (.ok (), exitState model parent ⟨next.f0 + 1⟩ before after callerAddr retAddr argAddr value input) := by
  intro h
  change exitState model parent ⟨next.f0 + 1⟩ before after callerAddr retAddr argAddr value input =
    exitState model parent next before after callerAddr retAddr argAddr value input at h
  have targets := congrArg (fun machine => machine.threads.map
    (fun thread => thread.stack.map (fun frame => frame.next_block.f0))) h
  simp only [exitState, single, List.map_cons, List.map_nil,
    MR_StackFrame.set_next_block, MR_StackFrame.set_next_stmt, List.cons.injEq, and_true] at targets
  omega

/-- Hostile byte mutation ONLY: the original constant's low literal byte.
    It is not relabeled as a new compiler-produced artifact. -/
def wrongBytes : List Nat := SemRU64Addition.originalBytes.set 184 8

theorem wrong_bytes_decode : decode wrongBytes = .ok (SemRU64Addition.module 8) := rfl

theorem wrong_blob_return (input depth : Nat) (inputValid : input < modulus 64) :
    runBlob wrongBytes 0 [.int .u64 input] 3 depth =
      .ok (.ret [.int .u64 ((input + 8) % modulus 64)]) := by
  simp only [runBlob, wrong_bytes_decode, runFunction,
    SemRU64Addition.start_exact 8 input depth inputValid]
  rw [SemRU64Addition.run_exact 8 input depth Mem.empty inputValid]

/-- Both complete modules decode and run. Their different result is a real
    countermodel, not merely a failed proof search or unsupported encoding. -/
theorem valid_wrong_module_counterexample :
    runBlob wrongBytes 0 [.int .u64 0] 3 0 ≠
      runBlob SemRU64Addition.originalBytes 0 [.int .u64 0] 3 0 := by
  rw [wrong_blob_return 0 0 (by decide)]
  have original : runBlob SemRU64Addition.originalBytes 0 [.int .u64 0] 3 0 =
      .ok (.ret [.int .u64 7]) := by
    simp only [runBlob, SemRU64Addition.original_decodes]
    exact congrArg Except.ok (SemRU64Addition.original_return 0 0 (by decide))
  rw [original]
  intro impossible
  cases impossible

/-- A separate expected SUBJECT for retained-proof rejection controls. -/
def WrongObservation (input depth : Nat) (model : MR_Machine) (parent : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte)
    (result : SRes MR_TerminationInfo Unit × MR_Machine) : Prop :=
  match runBlob wrongBytes 0 [.int .u64 input] 3 depth with
  | .error _ => False
  | .ok irResult => MiniRustU64Correspondence.FunctionObservation model parent next before after callerAddr
      input callerBytes irResult result

end MiniRustU64Controls
