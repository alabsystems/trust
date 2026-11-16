/- Full-domain mathematical UInt64/raw-word bridge for the actual canonical
   evaluator context. These are the imported model's UInt64 operations, not a
   qualification of a captured Clean Prelude, physical carrier or machine ABI. -/
import CanonicalClosurePublic

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

def wordModulus : Nat := 2 ^ 64
def rawWord (value : Nat) : Value := .int 64 (Int.ofNat value)

theorem uint64_ofNat_toNat (value : UInt64) : UInt64.ofNat value.toNat = value :=
  UInt64.ofNat_toNat

theorem uint64_toNat_ofNat (value : Nat) :
    (UInt64.ofNat value).toNat = value % wordModulus := UInt64.toNat_ofNat

theorem uint64_toNat_bound (value : UInt64) : value.toNat < wordModulus :=
  value.toNat_lt_size

theorem uint64_toNat_ofNat_bounded (value : Nat) (bounded : value < wordModulus) :
    (UInt64.ofNat value).toNat = value := by
  rw [uint64_toNat_ofNat, Nat.mod_eq_of_lt bounded]

theorem word_ofNat_mod (value : Nat) :
    word (UInt64.ofNat value) = rawWord (value % wordModulus) := by
  unfold word rawWord
  rw [uint64_toNat_ofNat]

theorem word_ofNat_bounded (value : Nat) (bounded : value < wordModulus) :
    word (UInt64.ofNat value) = rawWord value := by
  rw [word_ofNat_mod, Nat.mod_eq_of_lt bounded]

/-- Every bounded raw operand has an explicit source preimage and an exact
    inverse observation. Coverage is not restricted to a chosen source subset. -/
theorem every_bounded_raw_word (value : Nat) (bounded : value < wordModulus) :
    ∃ source : UInt64, word source = rawWord value ∧ source.toNat = value :=
  ⟨UInt64.ofNat value, word_ofNat_bounded value bounded,
    uint64_toNat_ofNat_bounded value bounded⟩

theorem every_bounded_raw_int (value : Int) (nonnegative : 0 ≤ value)
    (bounded : value < Int.ofNat wordModulus) :
    ∃ source : UInt64, word source = .int 64 value := by
  cases value with
  | ofNat value =>
    exact ⟨UInt64.ofNat value, word_ofNat_bounded value (Int.ofNat_lt.mp bounded)⟩
  | negSucc value => omega

theorem word_injective : Function.Injective word := by
  intro first second same
  have decoded := congrArg (fun value : Value => match value with
    | .int _ raw => raw.toNat | _ => 0) same
  change first.toNat = second.toNat at decoded
  exact UInt64.toNat_inj.mp decoded

theorem rawWord_injective : Function.Injective rawWord := by
  intro first second same
  have decoded := congrArg (fun value : Value => match value with
    | .int _ raw => raw.toNat | _ => 0) same
  exact decoded

theorem word_roundtrip (value : UInt64) : rawWord value.toNat = word value := rfl

theorem raw_word_bijection (value : Nat) (bounded : value < wordModulus) :
    (UInt64.ofNat value).toNat = value ∧
    (∀ source : UInt64, source.toNat = value → source = UInt64.ofNat value) := by
  refine ⟨uint64_toNat_ofNat_bounded value bounded, ?_⟩
  intro source observed
  rw [← observed]
  exact (uint64_ofNat_toNat source).symm

/-- Wrapping arithmetic is related for all natural operands, including values
    beyond the carrier; boundedness is only needed to retain raw inputs exactly. -/
theorem affine_ofNat_toNat (a b x : Nat) :
    ((UInt64.ofNat a) * (UInt64.ofNat x) + (UInt64.ofNat b)).toNat =
      (a * x + b) % wordModulus := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, uint64_toNat_ofNat]
  change (a % wordModulus * (x % wordModulus) % wordModulus + b % wordModulus) % wordModulus =
    (a * x + b) % wordModulus
  rw [← Nat.mul_mod a x wordModulus]
  exact (Nat.add_mod (a * x) b wordModulus).symm

theorem affine_ofNat_word (a b x : Nat) :
    word ((UInt64.ofNat a) * (UInt64.ofNat x) + (UInt64.ofNat b)) =
      rawWord ((a * x + b) % wordModulus) := by
  unfold word rawWord
  rw [affine_ofNat_toNat]

theorem raw_result_bounded (a b x : Nat) :
    (a * x + b) % wordModulus < wordModulus :=
  Nat.mod_lt _ (by decide)

def rawCallerState (world : MachineState) (a b x : Nat) : MachineState :=
  callerState world (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat x)

/-- The actual public canonical evaluator consumes every bounded triple of
    raw64 operands and constructs its normal result. No returning run is assumed. -/
theorem raw_caller_evaluates (depth : Nat) (world : MachineState) (a b x : Nat)
    (aBound : a < wordModulus) (bBound : b < wordModulus) (xBound : x < wordModulus) :
    Sem.run (evalFunctionInContext (context depth) callerId [rawWord a, rawWord b, rawWord x] 3 .abort)
      (entryState world) =
      .ok ([rawWord ((a * x + b) % wordModulus)], rawCallerState world a b x) := by
  have inputs : [word (UInt64.ofNat a), word (UInt64.ofNat b), word (UInt64.ofNat x)] =
      [rawWord a, rawWord b, rawWord x] := by
    rw [word_ofNat_bounded a aBound, word_ofNat_bounded b bBound, word_ofNat_bounded x xBound]
  calc
    _ = Sem.run (evalFunctionInContext (context depth) callerId
        [word (UInt64.ofNat a), word (UInt64.ofNat b), word (UInt64.ofNat x)] 3 .abort)
        (entryState world) := congrArg (fun values =>
          Sem.run (evalFunctionInContext (context depth) callerId values 3 .abort)
            (entryState world)) inputs.symm
    _ = .ok ([word ((UInt64.ofNat a) * (UInt64.ofNat x) + (UInt64.ofNat b))],
        rawCallerState world a b x) :=
      caller_evaluates depth world (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat x)
    _ = _ := congrArg (fun value => Except.ok ([value], rawCallerState world a b x))
      (affine_ofNat_word a b x)

theorem raw_caller_world_restored (world : MachineState) (a b x : Nat) :
    { rawCallerState world a b x with locals := world.locals, nextValueId := world.nextValueId } =
      world := rfl

/-- Equivalently, every nonnegative bounded Int carrier triple is covered;
    no restriction to values previously chosen from UInt64 is imposed. -/
theorem raw_int_caller_evaluates (depth : Nat) (world : MachineState) (a b x : Int)
    (aNonneg : 0 ≤ a) (bNonneg : 0 ≤ b) (xNonneg : 0 ≤ x)
    (aBound : a < Int.ofNat wordModulus) (bBound : b < Int.ofNat wordModulus)
    (xBound : x < Int.ofNat wordModulus) :
    Sem.run (evalFunctionInContext (context depth) callerId [.int 64 a, .int 64 b, .int 64 x] 3 .abort)
      (entryState world) =
      .ok ([.int 64 ((a * x + b) % Int.ofNat wordModulus)],
        rawCallerState world a.toNat b.toNat x.toNat) := by
  cases a with
  | negSucc a => omega
  | ofNat a =>
    cases b with
    | negSucc b => omega
    | ofNat b =>
      cases x with
      | negSucc x => omega
      | ofNat x =>
        have result := raw_caller_evaluates depth world a b x
          (Int.ofNat_lt.mp aBound) (Int.ofNat_lt.mp bBound) (Int.ofNat_lt.mp xBound)
        have converted : Int.ofNat ((a * x + b) % wordModulus) =
            (Int.ofNat a * Int.ofNat x + Int.ofNat b) % Int.ofNat wordModulus := by
          simp [Int.natCast_emod, Int.natCast_add, Int.natCast_mul]
        exact result.trans (congrArg (fun value : Int =>
          Except.ok ([Value.int 64 value], rawCallerState world a b x)) converted)

#print axioms every_bounded_raw_word
#print axioms word_injective
#print axioms affine_ofNat_toNat
#print axioms raw_caller_evaluates
#print axioms raw_int_caller_evaluates
end CanonicalClosure
