/- Copyright 2026 Andrew Yates. Apache-2.0.
   Canonical SemR execution of the retained two-input core callee.
   No Rust-source, physical ABI, compiler admission or emitted-byte claim. -/
import SemR
namespace SemRWord64Pair
open SemR
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def originalBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 6, 4, 99, 111, 114, 101, 18, 97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109, 97, 99, 111, 115, 120, 44, 47, 114, 117, 115, 116, 99, 47, 116, 114, 117, 115, 116, 45, 100, 101, 118, 47, 108, 105, 98, 114, 97, 114, 121, 47, 99, 111, 114, 101, 47, 115, 114, 99, 47, 110, 117, 109, 47, 109, 111, 100, 46, 114, 115, 48, 95, 82, 78, 118, 77, 115, 55, 95, 78, 116, 67, 115, 49, 120, 116, 50, 114, 101, 103, 114, 114, 85, 69, 95, 52, 99, 111, 114, 101, 51, 110, 117, 109, 121, 49, 50, 119, 114, 97, 112, 112, 105, 110, 103, 95, 97, 100, 100, 4, 115, 101, 108, 102, 3, 114, 104, 115, 0, 1, 2, 8, 8, 1, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 0, 2, 0, 8, 1, 8, 2, 0, 0, 8, 0, 1, 1, 2, 0, 1, 0, 179, 10, 4, 0, 0, 20, 1, 2, 0, 0, 1, 0, 179, 10, 4, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 1, 2, 0, 4, 1, 5, 0, 0, 0, 0, 1, 1, 8, 0, 0, 2, 1, 2, 0, 0, 0, 0]
def signature : FuncTy := ⟨[.int .u64, .int .u64], [.int .u64], false⟩
def body : Block :=
  ⟨0, [(0, .int .u64), (1, .int .u64)],
    [⟨.binop .add (.int .u64) 0 1, [2]⟩, ⟨.ret [2], []⟩]⟩
def function : Func :=
  { id := 0, ty := 0, entry := 0, blocks := [body], name := [95, 82, 78, 118, 77, 115, 55, 95, 78, 116, 67, 115, 49, 120, 116, 50, 114, 101, 103, 114, 114, 85, 69, 95, 52, 99, 111, 114, 101, 51, 110, 117, 109, 121, 49, 50, 119, 114, 97, 112, 112, 105, 110, 103, 95, 97, 100, 100] }
def module : Module :=
  { funcTys := [signature], enums := [], functions := [function],
    target := some ⟨[97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109, 97, 99, 111, 115, 120], 8, false, none, 2⟩ }

/-- Complete unchanged producer encoding, reduced by the canonical decoder. -/
theorem original_decodes : decode originalBytes = .ok module := rfl

def initial (left right depth : Nat) (memory : Mem) : Core :=
  { fn := function, sig := signature, block := body, pc := 0,
    env := [(1, .int .u64 right), (0, .int .u64 left)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := memory }

private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl

theorem start_exact (left right depth : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    start module 0 [.int .u64 left, .int .u64 right] depth =
      .ok (initial left right depth Mem.empty) := by
  simp [start, module, function, signature, body, initial, checkSig, bindParams,
    expectTy, Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.executableTarget,
    findBlock, nth?, rejectPoison, ok_bind, leftValid, rightValid] <;> rfl

def afterAddition (left right depth : Nat) (memory : Mem) : Core :=
  { fn := function, sig := signature, block := body, pc := 1,
    env := [(2, .int .u64 ((left + right) % modulus 64)),
      (1, .int .u64 right), (0, .int .u64 left)],
    depth := depth, stack := [], openFrames := [], nextFrame := 0, mem := memory }

/-- The complete next state preserves arbitrary memory, stack and frame state;
    this statement does not project execution down to returned arithmetic. -/
theorem addition_step (left right depth : Nat) (memory : Mem)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    stepCore module (initial left right depth memory) =
      .cont (afterAddition left right depth memory) := by
  simp [stepCore, execNode, initial, afterAddition, body, module, function, signature,
    nth?, binopStep, evalBinop, intBin, liftOp, pure_ok, ok_bind,
    getV, lookupEnv, expectTy, rejectPoison, expectInt, isBoolTy,
    Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.pointerBits,
    bindResults, next, ofR, leftValid, rightValid]

theorem return_step (left right depth : Nat) (memory : Mem) :
    stepCore module (afterAddition left right depth memory) =
      .done (.ret [.int .u64 ((left + right) % modulus 64)]) := by
  simp [stepCore, execNode, afterAddition, initial, body, module, function, signature,
    nth?, getV, getVs, lookupEnv, expectTy, rejectPoison,
    Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.pointerBits,
    ofR, retStep, returnTo, checkSig, pure_ok, ok_bind,
    Nat.mod_lt _ (by decide : 0 < modulus 64)]

/-- Both inputs range over all U64 values; depth and initial memory are arbitrary.
    No successful execution or preselected result is assumed. -/
theorem run_exact (left right depth : Nat) (memory : Mem)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    run module 2 (initial left right depth memory) =
      .ret [.int .u64 ((left + right) % modulus 64)] := by
  simp [run, stepCore, execNode, initial, body, module, function, signature,
    nth?, binopStep, evalBinop, intBin, liftOp, pure_ok, ok_bind,
    getV, getVs, lookupEnv, expectTy, rejectPoison, expectInt, isBoolTy,
    Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.pointerBits,
    bindResults, next, ofR, retStep, returnTo, checkSig, leftValid, rightValid,
    Nat.mod_lt _ (by decide : 0 < modulus 64)]

theorem original_returns (left right depth : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    runBlob originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
      .ok (.ret [.int .u64 ((left + right) % modulus 64)]) := by
  simp only [runBlob, original_decodes, runFunction,
    start_exact left right depth leftValid rightValid]
  exact congrArg Except.ok (run_exact left right depth Mem.empty leftValid rightValid)

/-- The canonical relational theorem excludes bad finite prefixes of this run.
    This is IR semantics, not Rust source NoUB or a physical entry theorem. -/
theorem no_body_violation (left right depth : Nat) (memory : Mem)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    ¬ BodyViolation module (initial left right depth memory) :=
  returned_excludes_body_violation module (initial left right depth memory) 2
    [.int .u64 ((left + right) % modulus 64)]
    (run_exact left right depth memory leftValid rightValid)

/-- False subjects for independent replay of the unchanged positive proofs. -/
def WrongDecode : Prop := decode (originalBytes ++ [0]) = .ok module
def WrongResult : Prop := ∀ left right depth : Nat,
  left < modulus 64 → right < modulus 64 →
  runBlob originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
    .ok (.ret [.int .u64 ((left + left) % modulus 64)])
def WrongFuel : Prop := ∀ left right depth : Nat,
  left < modulus 64 → right < modulus 64 →
  runBlob originalBytes 0 [.int .u64 left, .int .u64 right] 0 depth =
    .ok (.ret [.int .u64 ((left + right) % modulus 64)])
def MissingInputValidity : Prop := ∀ left right depth : Nat,
  runBlob originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
    .ok (.ret [.int .u64 ((left + right) % modulus 64)])

#print axioms original_decodes
#print axioms start_exact
#print axioms addition_step
#print axioms return_step
#print axioms run_exact
#print axioms original_returns
#print axioms no_body_violation
end SemRWord64Pair
