/- Canonical execution of the unchanged caller after explicit callee linking.
   No source authentication, ABI or compiler admission claim. -/
import SourceWord64Call
namespace PairCallerOperational
open SemR
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
def originalBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 7, 16, 115, 111, 117, 114, 99, 101, 95, 99, 108, 97, 105, 109, 95, 100, 101, 112, 18, 97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109, 97, 99, 111, 115, 120, 93, 47, 85, 115, 101, 114, 115, 47, 97, 121, 97, 116, 101, 115, 47, 116, 114, 117, 115, 116, 45, 108, 101, 97, 110, 45, 102, 49, 47, 99, 114, 97, 116, 101, 115, 47, 116, 114, 117, 115, 116, 45, 116, 104, 105, 114, 45, 108, 111, 119, 101, 114, 47, 112, 114, 111, 98, 101, 115, 47, 115, 111, 117, 114, 99, 101, 95, 119, 111, 114, 100, 54, 52, 95, 109, 101, 116, 97, 100, 97, 116, 97, 47, 112, 114, 111, 100, 117, 99, 101, 114, 46, 114, 115, 41, 95, 82, 78, 118, 67, 115, 106, 55, 116, 109, 80, 73, 106, 109, 53, 109, 99, 95, 49, 54, 115, 111, 117, 114, 99, 101, 95, 99, 108, 97, 105, 109, 95, 100, 101, 112, 52, 112, 97, 105, 114, 1, 120, 1, 121, 48, 95, 82, 78, 118, 77, 115, 55, 95, 78, 116, 67, 115, 49, 120, 116, 50, 114, 101, 103, 114, 114, 85, 69, 95, 52, 99, 111, 114, 101, 51, 110, 117, 109, 121, 49, 50, 119, 114, 97, 112, 112, 105, 110, 103, 95, 97, 100, 100, 0, 1, 2, 8, 8, 1, 8, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 1, 0, 2, 0, 8, 1, 8, 2, 18, 1, 2, 0, 1, 1, 2, 0, 1, 0, 12, 6, 0, 0, 20, 1, 2, 0, 0, 1, 0, 13, 1, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 1, 2, 0, 4, 1, 5, 0, 0, 1, 6, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 8, 0, 0, 2, 1, 2, 0, 0, 0, 0]
def callerName : List Nat := [95, 82, 78, 118, 67, 115, 106, 55, 116, 109, 80, 73, 106, 109, 53, 109, 99, 95, 49, 54, 115, 111, 117, 114, 99, 101, 95, 99, 108, 97, 105, 109, 95, 100, 101, 112, 52, 112, 97, 105, 114]
def callerBlock : Block := ⟨0, [(0, .int .u64), (1, .int .u64)],
  [⟨.call 1 [0, 1], [2]⟩, ⟨.ret [2], []⟩]⟩
def caller : Func := { id := 0, ty := 0, entry := 0, blocks := [callerBlock], name := callerName }
def declaration : Func := { SemRWord64Pair.function with id := 1, blocks := [] }
def original : Module := { SemRWord64Pair.module with functions := [caller, declaration] }

theorem original_decodes : decode originalBytes = .ok original := rfl

/-- Only the callee's module-local function id changes. Its blocks, SSA,
    signature and symbol remain the exact retained callee's contents. -/
def relocated : Func := { SemRWord64Pair.function with id := 1 }
def linked : Module := { original with functions := [caller, relocated] }
theorem caller_unchanged : linked.functions.head? = original.functions.head? := rfl
theorem callee_blocks_unchanged : relocated.blocks = SemRWord64Pair.function.blocks := rfl

private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl

theorem linked_returns (left right depth : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    runFunction linked 0 [.int .u64 left, .int .u64 right] 4 (depth + 1) =
      .ret [.int .u64 ((left + right) % modulus 64)] := by
  simp [runFunction, start, run, stepCore, execNode, linked, original,
    caller, callerBlock, callerName, relocated, SemRWord64Pair.module,
    SemRWord64Pair.function, SemRWord64Pair.body, SemRWord64Pair.signature,
    checkSig, bindParams, expectTy, rejectPoison, Val.ty, Ty.beq,
    IntTy.code, IntTy.bits, Module.executableTarget, Module.pointerBits,
    findBlock, nth?, getV, getVs, lookupEnv, callStep, callOn, callFn, callSig, callSigned, enterFn, suspend,
    binopStep, evalBinop, intBin, expectInt, isBoolTy, liftOp, bindResults, next, ofR,
    retStep, returnTo, pure_ok, ok_bind, leftValid, rightValid,
    Nat.mod_lt _ (by decide : 0 < modulus 64)]

theorem zero_depth_refused (left right : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    runFunction linked 0 [.int .u64 left, .int .u64 right] 4 0 = .outOfFuel := by
  simp [runFunction, start, run, stepCore, execNode, linked, original,
    caller, callerBlock, callerName, relocated, declaration, SemRWord64Pair.module,
    SemRWord64Pair.function, SemRWord64Pair.body, SemRWord64Pair.signature,
    checkSig, bindParams, expectTy, rejectPoison, Val.ty, Ty.beq,
    IntTy.code, IntTy.bits, Module.executableTarget, Module.pointerBits,
    findBlock, nth?, getV, getVs, lookupEnv, callStep, callOn,
    callFn, callSig, callSigned, enterFn, suspend, unsupR,
    pure_ok, ok_bind, ofR, leftValid, rightValid]

theorem missing_body_refused (left right depth : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    runFunction original 0 [.int .u64 left, .int .u64 right] 4 (depth + 1) =
      .unsupported "interprocedural_call" := by
  simp [runFunction, start, run, stepCore, execNode, linked, original,
    caller, callerBlock, callerName, relocated, declaration, SemRWord64Pair.module,
    SemRWord64Pair.function, SemRWord64Pair.body, SemRWord64Pair.signature,
    checkSig, bindParams, expectTy, rejectPoison, Val.ty, Ty.beq,
    IntTy.code, IntTy.bits, Module.executableTarget, Module.pointerBits,
    findBlock, nth?, getV, getVs, lookupEnv, callStep, callOn,
    callFn, callSig, callSigned, enterFn, suspend, unsupR,
    pure_ok, ok_bind, ofR, leftValid, rightValid]

theorem call_claim_matches_linked (left right depth : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    SourceWord64Call.evaluateThrough SourceWord64RecordOriginal.original
      SourceWord64Call.caller [left, right] = some ((left + right) % modulus 64) ∧
    runFunction linked 0 [.int .u64 left, .int .u64 right] 4 (depth + 1) =
      .ret [.int .u64 ((left + right) % modulus 64)] :=
  ⟨SourceWord64Call.caller_evaluates left right leftValid rightValid,
    linked_returns left right depth leftValid rightValid⟩

#print axioms original_decodes
#print axioms caller_unchanged
#print axioms callee_blocks_unchanged
#print axioms linked_returns
#print axioms zero_depth_refused
#print axioms missing_body_refused
#print axioms call_claim_matches_linked
end PairCallerOperational
