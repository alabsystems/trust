-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderTyping

/-! Value rules for the supported model int32/unsigned-int32/_Bool profile.
These are scalar-value rules, not a C evaluation relation or evidence for the
actual target, an atomic intrinsic, an external call, or an ownership right.
They make integer promotion and modulo conversion explicit before attaching
parsed source and stateful execution. Unsupported scalar families refuse. -/
namespace C11ScalarValues
open C11HeaderTyping
inductive Value where
  | signed (value : Int)
  | unsigned (value : Nat)
  | boolean (value : Bool)
  deriving DecidableEq, BEq, Repr

def typeOf : Value → CType
  | .signed _ => .cInt
  | .unsigned _ => .cUInt
  | .boolean _ => .cBool

def valid : Value → Bool
  | .signed value => decide (-2147483648 ≤ value ∧ value < 2147483648)
  | .unsigned value => value < 4294967296
  | .boolean _ => true

def truth : Value → Bool
  | .signed value => value != 0
  | .unsigned value => value != 0
  | .boolean value => value

def intResult (result : Bool) : Value := .signed (if result then 1 else 0)

/-- N1570 6.3.1.3 reduction modulo one more than maximum unsigned value,
including negative int values. Input validity is checked before conversion. -/
def convert (target : CType) (value : Value) : Option Value := do
  if !valid value then none else
    if typeOf value == target then some value else
      match value, target with
      | .signed value, .cUInt => some (.unsigned (value % 4294967296).toNat)
      | .signed value, .cBool => some (.boolean (value != 0))
      | .unsigned value, .cBool => some (.boolean (value != 0))
      | .boolean value, .cInt => some (intResult value)
      | _, _ => none

/-- Comparison operands use the same commonInteger and conversion rules as
source typing. The result is C int 0/1, not an assumed _Bool runtime value. -/
def compareValues (operation : Binary) (left right : Value) : Option Value := do
  if !valid left || !valid right then none else
    match operation with
    | .logicalAnd => some (intResult (truth left && truth right))
    | _ => do
        let common ← commonInteger (typeOf left) (typeOf right)
        let left ← convert common left
        let right ← convert common right
        let compare (left right : Int) : Bool := match operation with
          | .ge => decide (left ≥ right)
          | .lt => decide (left < right)
          | .ne => left != right
          | .logicalAnd => false
        match left, right with
        | .signed left, .signed right => some (intResult (compare left right))
        | .unsigned left, .unsigned right => some (intResult (compare left right))
        | _, _ => none

/-- Every accepted conversion has the requested C type; producer type advice
cannot change the returned value family. This is scalar typing only. -/
theorem convert_type (target : CType) (value result : Value)
    (accepted : convert target value = some result) : typeOf result = target := by
  unfold convert at accepted
  split at accepted
  next => simp_all
  next =>
    split at accepted
    next equal =>
      have same : typeOf value = target := eq_of_beq equal
      simp_all
    next =>
      cases value <;> cases target <;> simp_all [typeOf, intResult]
      all_goals subst result; rfl

theorem int_result_valid (result : Bool) : valid (intResult result) = true := by
  cases result <;> rfl

theorem unsigned_modulo_valid (value : Int) :
    valid (.unsigned (value % 4294967296).toNat) = true := by
  have lower : 0 ≤ value % 4294967296 := Int.emod_nonneg value (by decide)
  have upper : value % 4294967296 < 4294967296 := Int.emod_lt_of_pos value (by decide)
  have bounded : (value % 4294967296).toNat < 4294967296 := (Int.toNat_lt lower).mpr upper
  exact decide_eq_true bounded

theorem negative_one_becomes_unsigned_max :
    convert .cUInt (.signed (-1)) = some (.unsigned 4294967295) := by rfl

theorem mixed_comparison_converts_before_compare :
    compareValues .lt (.signed (-1)) (.unsigned 1) = some (.signed 0) := by rfl

theorem comparison_result_is_int :
    compareValues .ge (.unsigned 5) (.signed 1) = some (.signed 1) := by rfl

theorem bool_return_conversion : convert .cBool (.signed 1) = some (.boolean true) := by rfl

theorem invalid_signed_value_refused : convert .cUInt (.signed 2147483648) = none := by rfl

theorem invalid_unsigned_value_refused :
    compareValues .ge (.unsigned 4294967296) (.signed 0) = none := by rfl

theorem unknown_pointer_conversion_refused :
    convert (.pointer .cUInt) (.unsigned 1) = none := by rfl

end C11ScalarValues
