/- Copyright 2026 Andrew Yates. Apache-2.0.
   Total structural projection of captured typed source into the SAME view.
   No emitter, source authority, Rust DefId assumption or source-grade promotion.
-/
import MirCaptureJson
import MirHelperReturn
namespace TrustMirCaptureView
open TrustMirCaptureJson TrustMirBoolAssignment TrustMirNominalSwitch TrustMirHelperReturn
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def field (j : J) (key : String) : Option J := match j with
  | .obj fs => (fs.find? (fun p => p.1 == key)).map Prod.snd
  | _ => none
def keys (j : J) (expected : List String) : Bool := match j with
  | .obj fs => fs.length == expected.length && expected.all (fun k => (field j k).isSome)
  | _ => false
def nat (j : J) : Option Nat := match j with
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none
def str (j : J) : Option String := match j with | .str s => some s | _ => none
def boolean (j : J) : Option Bool := match j with | .bool b => some b | _ => none
def array (j : J) : Option (List J) := match j with | .arr xs => some xs | _ => none
def isNull (j : J) : Bool := match j with | .null => true | _ => false

def span (j : J) : Bool :=
  keys j ["file","line_start","col_start","line_end","col_end"] &&
    ((field j "file").bind str).isSome &&
    ["line_start","col_start","line_end","col_end"].all (fun k => ((field j k).bind nat).isSome)

def projectPlace (j : J) : Option Place := do
  if !keys j ["local","projections"] then none else pure ()
  let id ← field j "local" >>= nat
  let ps ← field j "projections" >>= array
  if !ps.isEmpty then none else pure ()
  pure ⟨id,[]⟩
def projectOperand (j : J) : Option Operand := do
  match j with
  | .obj [(kind,value)] =>
    if kind == "Copy" then return .copy (← projectPlace value)
    else if kind == "Constant" then
      match value with
      | .obj [(tag,.bool b)] => if tag == "Bool" then some (.constantBool b) else none
      | _ => none
    else none
  | _ => none
def projectRvalue (j : J) : Option Rvalue := do
  match j with
  | .obj [(kind,value)] =>
    if kind == "Use" then return .use (← projectOperand value)
    else if kind == "Discriminant" then return .discriminant (← projectPlace value)
    else none
  | _ => none
def projectStatement (j : J) : Option Statement := do
  match j with
  | .obj [(kind,value)] =>
    if kind != "Assign" || !keys value ["place","rvalue","span"] then none else pure ()
    if !span (← field value "span") then none else pure ()
    return .assign (← field value "place" >>= projectPlace) (← field value "rvalue" >>= projectRvalue)
  | _ => none
def projectTarget (j : J) : Option (Nat × Nat) := do
  match j with | .arr [a,b] => return (← nat a, ← nat b) | _ => none
def projectTerminator (j : J) : Option Terminator := do
  match j with
  | .str "Return" => some .return
  | .obj [(kind,value)] =>
    if kind == "Goto" then return .goto (← nat value)
    else if kind == "SwitchInt" then
      if !keys value ["discr","targets","otherwise","exhaustive_enum_unreachable","span"] then none else pure ()
      if (← field value "exhaustive_enum_unreachable" >>= boolean) then none else pure ()
      if !span (← field value "span") then none else pure ()
      let cases ← (← field value "targets" >>= array).mapM projectTarget
      return .switchInt (← field value "discr" >>= projectOperand) cases (← field value "otherwise" >>= nat)
    else none
  | _ => none

inductive Scalar where | bool | i64 deriving DecidableEq
structure Variant where
  name : String
  discriminant : Int
  fields : List (String × Scalar)
  deriving DecidableEq
structure Nominal where
  name : String
  fields : List (String × Scalar)
  variants : List Variant
  discIndexSafe : Bool
  deriving DecidableEq
inductive Ty where | bool | i64 | nominal (decl : Nominal) deriving DecidableEq
structure Local where
  index : Nat
  name : Option String
  ty : Ty
  deriving DecidableEq
structure Block where
  id : Nat
  statements : List Statement
  terminator : Terminator
  deriving DecidableEq
structure Body where
  arguments : Nat
  result : Ty
  locals : List Local
  blocks : List Block
  deriving DecidableEq
structure Capture where
  ownerName : String
  defPath : String
  body : Body

def projectScalar (j : J) : Option Scalar := do
  match j with
  | .str "Bool" => some .bool
  | .obj [(kind,v)] =>
    if kind != "Int" || !keys v ["width","signed"] then none else pure ()
    if (← field v "width" >>= nat) != 64 || !(← field v "signed" >>= boolean) then none else pure ()
    pure .i64
  | _ => none
def projectField (j : J) : Option (String × Scalar) := do
  match j with | .arr [a,b] => return (← str a, ← projectScalar b) | _ => none
def projectVariant (j : J) : Option Variant := do
  if !keys j ["name","discriminant","fields"] then none else pure ()
  let .int d ← field j "discriminant" | none
  return ⟨← field j "name" >>= str, d, ← (← field j "fields" >>= array).mapM projectField⟩
def projectTy (j : J) : Option Ty := do
  if let some scalar := projectScalar j then
    return match scalar with | .bool => .bool | .i64 => .i64
  match j with
  | .obj [(kind,v)] =>
    if kind != "Adt" || !keys v ["name","fields","variants","disc_index_safe","faithful_enum_repr","layout","enum_layout","adt_kind"] then none else pure ()
    for k in ["faithful_enum_repr","layout","enum_layout"] do
      if !isNull (← field v k) then none else pure ()
    if (← field v "adt_kind" >>= str) != "Enum" then none else pure ()
    return .nominal ⟨← field v "name" >>= str,
      ← (← field v "fields" >>= array).mapM projectField,
      ← (← field v "variants" >>= array).mapM projectVariant,
      ← field v "disc_index_safe" >>= boolean⟩
  | _ => none
def projectLocal (j : J) : Option Local := do
  if !keys j ["index","ty","name"] then none else pure ()
  let n ← field j "index" >>= nat
  let nameValue ← field j "name"
  let name : Option String ← match nameValue with
    | .null => some none
    | .str text => some (some text)
    | _ => none
  return ⟨n,name,← field j "ty" >>= projectTy⟩
def projectBlock (j : J) : Option Block := do
  if !keys j ["id","stmts","terminator"] then none else pure ()
  return ⟨← field j "id" >>= nat, ← (← field j "stmts" >>= array).mapM projectStatement,
    ← field j "terminator" >>= projectTerminator⟩
def projectBody (j : J) : Option Body := do
  if !keys j ["locals","blocks","arg_count","return_ty"] then none else pure ()
  return ⟨← field j "arg_count" >>= nat, ← field j "return_ty" >>= projectTy,
    ← (← field j "locals" >>= array).mapM projectLocal, ← (← field j "blocks" >>= array).mapM projectBlock⟩
def projectCapture (j : J) : Option Capture := do
  if !keys j ["name","def_path","span","body","contracts","preconditions","postconditions","spec"] then none else pure ()
  if !span (← field j "span") then none else pure ()
  -- These SPEC carriers remain in full Rust source identity. They are NEVER
  -- assumptions of body execution, nor do we infer source-clause validity.
  let _ ← field j "contracts" >>= array
  let _ ← field j "preconditions" >>= array
  let _ ← field j "postconditions" >>= array
  let _ ← field j "spec"
  return ⟨← field j "name" >>= str, ← field j "def_path" >>= str, ← field j "body" >>= projectBody⟩

def expectedNominal : Nominal :=
  ⟨originalNominalName,[("__tag",.i64)], TrustMirNominalSwitch.variants.map (fun v => ⟨v.name,v.discriminant,[]⟩),true⟩
def expectedBody (b : Bool) : Body :=
  ⟨1,.bool,[⟨0,none,.bool⟩,⟨1,some "kind",.nominal expectedNominal⟩,⟨2,none,.bool⟩,⟨3,none,.i64⟩],
   [⟨0,[sourceStatement],sourceTerminator⟩] ++
   ((constants b).zipIdx.map (fun (v,i) => ⟨i+1,[.assign ⟨2,[]⟩ (.use (.constantBool v))],.goto 10⟩)) ++
   [⟨10,[copyToReturn],.return⟩]⟩

/-- A checked structural equality, not a source grade or nominal identity key. -/
structure CheckedView (capture : Capture) where
  bodyFlag : Bool
  bodyEq : capture.body = expectedBody bodyFlag

def checkView (capture : Capture) : Option (CheckedView capture) :=
  if h : capture.body = expectedBody true then some ⟨true,h⟩
  else if h : capture.body = expectedBody false then some ⟨false,h⟩ else none

theorem checked_body_exact (capture : Capture) (checked : CheckedView capture) :
    capture.body = expectedBody checked.bodyFlag := checked.bodyEq
end TrustMirCaptureView
