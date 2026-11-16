/- Copyright 2026 Andrew Yates. Apache-2.0.
   Canonical decoded U64 Const/Add/Return profile. No source/ABI/license theorem. -/
import U64Addition
namespace SemRU64ScalarProfile
open SemR
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

structure View where
  literal : Nat
  name : List Nat
  target : Option TargetInfo
  blobs : List (List Nat × List Nat)

def function (view : View) : Func :=
  { SemRU64Addition.function view.literal with name := view.name }
def module (view : View) : Module :=
  { funcTys := [SemRU64Addition.signature], enums := [],
    functions := [function view], target := view.target, blobs := view.blobs }

/-- An exact typed classifier over the REAL canonical decoder result. It
    retains the actual name and full target; every ID and operand is checked. -/
def classify : Module → Option View
  | ⟨[⟨[.int .u64], [.int .u64], false⟩], [],
      [⟨0, 0, 0, [⟨0, [(0, .int .u64)],
        [⟨.const (.int .u64) (.int literal), [1]⟩,
         ⟨.binop .add (.int .u64) 0 1, [2]⟩,
         ⟨.ret [2], []⟩]⟩], name⟩], target, [], [], blobs⟩ =>
      some ⟨literal, name, target, blobs⟩
  | _ => none

theorem classify_exact (m : Module) (view : View) (matched : classify m = some view) :
    m = module view := by
  unfold classify at matched
  split at matched <;> cases matched <;> rfl

/-- Actual decoding, complete typed shape and executable target are mandatory.
    A proof is kernel reduction of this definition, never a Rust boolean flag. -/
def accepts (bytes : List Nat) (literal : Nat) : Bool :=
  match decode bytes with
  | .error _ => false
  | .ok m =>
    match classify m with
    | none => false
    | some view => (view.literal == literal) && m.executableTarget

def Decodes (bytes : List Nat) (literal : Nat) : Prop := accepts bytes literal = true

theorem decode_profile (bytes : List Nat) (literal : Nat)
    (checked : accepts bytes literal = true) : Decodes bytes literal := checked

theorem decoded_module (bytes : List Nat) (literal : Nat) (checked : Decodes bytes literal) :
    ∃ view : View, decode bytes = .ok (module view) ∧ view.literal = literal ∧
      (module view).executableTarget = true := by
  cases decoded : decode bytes with
  | error failure => simp [Decodes, accepts, decoded] at checked
  | ok m =>
    cases extracted : classify m with
    | none => simp [Decodes, accepts, decoded, extracted] at checked
    | some view =>
      have parts : (view.literal == literal) && m.executableTarget = true := by
        simpa [Decodes, accepts, decoded, extracted] using checked
      have both : (view.literal == literal) = true ∧ m.executableTarget = true := by
        simpa using parts
      have exactModule := classify_exact m view extracted
      exact ⟨view, by simpa only [exactModule] using decoded,
        (by simpa using both.1), by simpa only [exactModule] using both.2⟩

def initial (view : View) (input depth : Nat) (memory : Mem) : Core :=
  { fn := function view, sig := SemRU64Addition.signature,
    block := SemRU64Addition.body view.literal, pc := 0,
    env := [(0, .int .u64 input)], depth := depth, stack := [],
    openFrames := [], nextFrame := 0, mem := memory }

private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl

theorem start_exact (view : View) (input depth : Nat)
    (targetAccepted : (module view).executableTarget = true)
    (inputValid : input < modulus 64) :
    start (module view) 0 [.int .u64 input] depth =
      .ok (initial view input depth Mem.empty) := by
  simp only [module, function, SemRU64Addition.function, SemRU64Addition.signature,
    SemRU64Addition.body] at targetAccepted
  simp [start, targetAccepted, module, function, SemRU64Addition.function,
    SemRU64Addition.signature, SemRU64Addition.body, initial, checkSig,
    bindParams, expectTy, Val.ty, Ty.beq, IntTy.code, IntTy.bits,
    findBlock, nth?, rejectPoison, ok_bind, inputValid] <;> rfl

theorem run_exact (view : View) (input depth : Nat) (memory : Mem)
    (inputValid : input < modulus 64) :
    run (module view) 3 (initial view input depth memory) =
      .ret [.int .u64 ((input + view.literal) % modulus 64)] := by
  simp [run, stepCore, execNode, initial, module, function,
    SemRU64Addition.body, SemRU64Addition.function, SemRU64Addition.signature,
    nth?, constStep, constVal, binopStep, evalBinop, intBin, liftOp, pure_ok,
    ok_bind, getV, getVs, lookupEnv, expectTy, rejectPoison, expectInt, isBoolTy,
    Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.pointerBits,
    bindResults, next, ofR, retStep, returnTo, checkSig, inputValid,
    Nat.mod_lt _ (by decide : 0 < modulus 64)]

def Returns (bytes : List Nat) (literal : Nat) : Prop :=
  ∀ input depth : Nat, input < modulus 64 →
    runBlob bytes 0 [.int .u64 input] 3 depth =
      .ok (.ret [.int .u64 ((input + literal) % modulus 64)])

def NoBad (bytes : List Nat) : Prop :=
  ∀ m : Module, decode bytes = .ok m →
    ∀ (input depth : Nat) (initialState : Core), input < modulus 64 →
      start m 0 [.int .u64 input] depth = .ok initialState →
      ¬ BodyViolation m initialState

theorem returns (bytes : List Nat) (literal : Nat) (checked : Decodes bytes literal) :
    Returns bytes literal := by
  obtain ⟨view, decoded, sameLiteral, accepted⟩ := decoded_module bytes literal checked
  intro input depth valid
  simp only [runBlob, decoded, runFunction, start_exact view input depth accepted valid]
  exact congrArg Except.ok (by simpa only [sameLiteral] using run_exact view input depth Mem.empty valid)

theorem no_bad (bytes : List Nat) (literal : Nat) (checked : Decodes bytes literal) :
    NoBad bytes := by
  obtain ⟨view, decoded, sameLiteral, accepted⟩ := decoded_module bytes literal checked
  intro m actual input depth state valid started
  rw [decoded] at actual
  cases actual
  rw [start_exact view input depth accepted valid] at started
  cases started
  exact returned_excludes_body_violation (module view)
    (initial view input depth Mem.empty) 3
    [.int .u64 ((input + view.literal) % modulus 64)]
    (run_exact view input depth Mem.empty valid)

/-- This scalar body never reads the retained blob table. Keeping the table in
    the exact module view does not restrict which unreferenced data it carries. -/
theorem run_blob_table_independent (view : View) (blobs : List (List Nat × List Nat))
    (input depth : Nat) (memory : Mem) (valid : input < modulus 64) :
    run (module { view with blobs := blobs }) 3
        (initial { view with blobs := blobs } input depth memory) =
      run (module view) 3 (initial view input depth memory) := by
  rw [run_exact _ _ _ _ valid, run_exact _ _ _ _ valid]

end SemRU64ScalarProfile
