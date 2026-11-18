-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderAST

/-! C scalar typing/elaboration for the captured 32-bit-int/uint32_t target.
This handles the REAL C types omitted by the normalized AST: int literals,
comparison/logical results of type int, unsigned conversion of 0/1 operands,
and the final conversion to _Bool. Target widths and source typedef/macro/
field/intrinsic binding are NOT inferred from an annotation or familiar name.
The checker below consumes a declaration environment; constructing that
complete environment from the actual TU remains a separate obligation. -/
namespace C11HeaderTyping
open C11HeaderAST
inductive CType where
  | cInt | cUInt | cBool | cUChar | cUShort | unit
  | record (tag : String)
  | pointer (type : CType)
  | atomic (type : CType)
  | flexibleArray (type : CType)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr
inductive Binary where
  | ge | lt | ne | logicalAnd
  deriving DecidableEq, BEq, Repr
inductive Raw where
  | variable (name : String)
  | decimal (value : Nat)
  | unsigned (value : Nat)
  | call (name : String) (arguments : List Raw)
  | binary (operation : Binary) (left right : Raw)
  | logicalNot (operand : Raw)
  | boolCast (operand : Raw)
  | uintCast (operand : Raw)
  | pointerMember (base : Raw) (field : String)
  | member (base : Raw) (field : String)
  | addressOf (operand : Raw)
  deriving Repr
structure Signature where
  parameters : List CType
  result : CType
  deriving DecidableEq, BEq, Repr
structure Target where
  intBits : Nat
  unsignedIntBits : Nat
  deriving DecidableEq, BEq, Repr
/-- A MODEL profile, not a certificate that the actual compiler target has
these widths. Actual target/configuration binding is an independent obligation. -/
def int32Target : Target := { intBits := 32, unsignedIntBits := 32 }
structure Environment where
  target : Option Target := none
  variables : List (String × CType) := []
  functions : List (String × Signature) := []
  records : List (String × List (String × CType)) := []
  deriving Repr
inductive Conversion where
  | identity | intToUInt | intToBool | uintToBool | boolToInt
  | lvalueToRValue | functionToPointerDecay
  deriving DecidableEq, BEq, Repr

def scalar : CType → Bool
  | .cInt | .cUInt | .cBool => true
  | _ => false

def conversion (source target : CType) : Option Conversion :=
  if source == target then some .identity else
  match source, target with
  | .cInt, .cUInt => some .intToUInt
  | .cInt, .cBool => some .intToBool
  | .cUInt, .cBool => some .uintToBool
  | .cBool, .cInt => some .boolToInt
  | _, _ => none

/-- Declarative conversion relation for the supported C scalar rules;
this is not an assumption about a producer's annotations. -/
def AllowedConversion (source target : CType) (cast : Conversion) : Prop :=
  (source = target ∧ cast = .identity) ∨
  (source = .cInt ∧ target = .cUInt ∧ cast = .intToUInt) ∨
  (source = .cInt ∧ target = .cBool ∧ cast = .intToBool) ∨
  (source = .cUInt ∧ target = .cBool ∧ cast = .uintToBool) ∨
  (source = .cBool ∧ target = .cInt ∧ cast = .boolToInt)

theorem conversion_sound (source target : CType) (cast : Conversion)
    (accepted : conversion source target = some cast) : AllowedConversion source target cast := by
  unfold conversion at accepted
  split at accepted
  next equal =>
    have equality : source = target := eq_of_beq equal
    subst target
    cases accepted
    exact Or.inl ⟨rfl, rfl⟩
  next different =>
    cases source <;> cases target <;> simp_all [AllowedConversion]

/-- Equal rank int/unsigned-int uses unsigned int (N1570 6.3.1.8).
_Bool undergoes integer promotion before the usual arithmetic conversions. -/
def commonInteger (left right : CType) : Option CType :=
  let promote := fun t => if t == .cBool then CType.cInt else t
  match promote left, promote right with
  | .cInt, .cInt => some .cInt
  | .cInt, .cUInt | .cUInt, .cInt | .cUInt, .cUInt => some .cUInt
  | _, _ => none

/-- Only the parameter/result families needed by this slice are supported.
In particular void is never a parameter/value argument; aggregates, arrays and
atomic-by-value calls require their own C typing/elaboration rules. -/
def supportedParameter : CType → Bool
  | .cInt | .cUInt | .cBool | .cUChar | .cUShort | .pointer _ => true
  | _ => false

def supportedSignature (signature : Signature) : Bool :=
  signature.parameters.all supportedParameter &&
    (signature.result == .unit || supportedParameter signature.result)

/-- Fuel is a total parser/checker bound, not permission to trust advice.
No type annotation is present in Raw; all call/variable types come from lookup.
Unknown or ambiguous declarations refuse. Duplicate names never select first. -/
def uniqueLookup [BEq α] (name : String) (entries : List (String × α)) : Option α :=
  match entries.filter (fun entry => entry.1 == name) with
  | [(_, value)] => some value
  | _ => none

/-- The reported conversions are part of the elaboration output, not discarded
producer annotations. This records the REAL int/uint/_Bool conversion path. -/
structure Elaboration where
  type : CType
  conversions : List Conversion := []
  lvalue : Bool := false
  deriving DecidableEq, BEq, Repr

private def asRValue (expression : Elaboration) : Elaboration :=
  if expression.lvalue then
    { expression with lvalue := false, conversions := expression.conversions ++ [.lvalueToRValue] }
  else expression

private def infer32 : Nat → Environment → Raw → Option Elaboration
  | 0, _, _ => none
  | fuel + 1, env, expression =>
    match expression with
    | .variable name => do return { type := ← uniqueLookup name env.variables, lvalue := true }
    | .decimal value =>
        if value < 2147483648 then some { type := .cInt } else none
    | .unsigned value =>
        if value < 4294967296 then some { type := .cUInt } else none
    | .call name arguments => do
        let signature ← uniqueLookup name env.functions
        if !supportedSignature signature then none else do
          let arguments ← arguments.mapM (fun argument => do return asRValue (← infer32 fuel env argument))
          if arguments.length != signature.parameters.length then none else do
            let conversions ← (arguments.zip signature.parameters).mapM (fun (argument, parameter) =>
              conversion argument.type parameter)
            return { type := signature.result, conversions := [.functionToPointerDecay] ++ arguments.flatMap (·.conversions) ++ conversions }
    | .binary operation left right => do
        let left := asRValue (← infer32 fuel env left)
        let right := asRValue (← infer32 fuel env right)
        match operation with
        | .logicalAnd =>
            if scalar left.type && scalar right.type then
              return { type := .cInt, conversions := left.conversions ++ right.conversions }
            else none
        | _ => do
            let common ← commonInteger left.type right.type
            let leftConversion ← conversion left.type common
            let rightConversion ← conversion right.type common
            return { type := .cInt, conversions := left.conversions ++ right.conversions ++ [leftConversion, rightConversion] }
    | .logicalNot operand => do
        let operand := asRValue (← infer32 fuel env operand)
        if scalar operand.type then return { type := .cInt, conversions := operand.conversions }
        else none
    | .boolCast operand => do
        let operand := asRValue (← infer32 fuel env operand)
        let cast ← conversion operand.type .cBool
        return { type := .cBool, conversions := operand.conversions ++ [cast] }
    | .uintCast operand => do
        let operand := asRValue (← infer32 fuel env operand)
        let cast ← conversion operand.type .cUInt
        return { type := .cUInt, conversions := operand.conversions ++ [cast] }

    | .pointerMember base field => do
        let base := asRValue (← infer32 fuel env base)
        let .pointer (.record tag) := base.type | none
        let fields ← uniqueLookup tag env.records
        let type ← uniqueLookup field fields
        return { type := type, conversions := base.conversions, lvalue := true }
    | .member base field => do
        let base ← infer32 fuel env base
        let .record tag := base.type | none
        let fields ← uniqueLookup tag env.records
        let type ← uniqueLookup field fields
        return { type := type, conversions := base.conversions, lvalue := base.lvalue }
    | .addressOf operand => do
        let operand ← infer32 fuel env operand
        if operand.lvalue then return { type := .pointer operand.type, conversions := operand.conversions }
        else none

/-- Unknown or unsupported target profiles refuse, rather than silently
assuming the producer's int/uint annotations establish 32-bit C semantics. -/
def infer (fuel : Nat) (environment : Environment) (expression : Raw) : Option Elaboration :=
  if environment.target == some int32Target then infer32 fuel environment expression else none

/-- The atomic builtin meaning does NOT follow from this ordinary signature.
This generic test environment exercises types only. Its declarations still need
actual complete source binding; no runtime interpretation is attached here. -/
def typedData : Environment :=
  { target := some int32Target, variables := [("header", .pointer (.atomic .cUInt)), ("limit", .cUInt)],
    functions := [("load", { parameters := [.pointer (.atomic .cUInt)], result := .cUInt }),
      ("rmw", { parameters := [.pointer (.atomic .cUInt), .cUInt], result := .cUInt })] }

theorem literal_one_is_int : infer 4 typedData (.decimal 1) = some { type := .cInt } := by rfl

theorem rmw_argument_records_unsigned_conversion :
    infer 4 typedData (.call "rmw" [.variable "header", .decimal 1]) =
      some { type := .cUInt, conversions := [.functionToPointerDecay, .lvalueToRValue, .identity, .intToUInt] } := by rfl

theorem comparison_zero_records_unsigned_conversion :
    infer 8 typedData (.binary .ne (.call "rmw" [.variable "header", .decimal 1]) (.decimal 0)) =
      some { type := .cInt, conversions := [.functionToPointerDecay, .lvalueToRValue, .identity, .intToUInt, .identity, .intToUInt] } := by rfl

theorem return_false_records_bool_conversion :
    infer 4 typedData (.boolCast (.decimal 0)) =
      some { type := .cBool, conversions := [.intToBool] } := by rfl

theorem unknown_callee_refused : infer 4 { target := some int32Target } (.call "load" []) = none := by rfl

theorem duplicate_declaration_refused :
    infer 4 { target := some int32Target, functions := [("load", { parameters := [], result := .cUInt }),
      ("load", { parameters := [], result := .cUInt })] } (.call "load" []) = none := by rfl

theorem wrong_arity_refused : infer 4 typedData (.call "rmw" [.variable "header"]) = none := by rfl

theorem pointer_as_integer_refused :
    infer 4 typedData (.binary .ge (.variable "header") (.decimal 0)) = none := by rfl

theorem too_wide_unsigned_refused : infer 4 typedData (.unsigned 4294967296) = none := by rfl

theorem absent_target_refused : infer 4 {} (.decimal 1) = none := by rfl

theorem incompatible_target_refused :
    infer 4 { target := some { intBits := 16, unsignedIntBits := 16 } } (.decimal 1) = none := by rfl

theorem void_parameter_advice_refused :
    infer 8 { target := some int32Target, functions :=
      [("g", { parameters := [], result := .unit }),
       ("f", { parameters := [.unit], result := .cInt })] }
      (.call "f" [.call "g" []]) = none := by rfl

#print axioms comparison_zero_records_unsigned_conversion
#print axioms duplicate_declaration_refused
end C11HeaderTyping
