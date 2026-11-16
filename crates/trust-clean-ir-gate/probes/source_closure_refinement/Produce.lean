/- Untrusted proposal producer.  Importing this module is never proof or
   permission.  Proof modules import the generated quotation and the original
   source instead; the actual original constants occur in their own goals. -/
import Lean
import Original

open Lean Elab Command

namespace UntrustedClosureProposal

/- These readers only propose code.  No Boolean or successful reader result
   crosses the proof boundary as source faithfulness or carrier evidence. -/
def strip : Expr → Expr
  | .mdata _ e => strip e
  | e => e

def lambdas : Expr → List Name × Expr
  | .lam name _ body _ =>
    let (names, result) := lambdas body
    (name :: names, result)
  | .mdata _ body => lambdas body
  | body => ([], body)

def vid (n : Nat) : String := s!"(ClosureU64.valueId {n})"

def nats (values : List Nat) : String :=
  "[" ++ String.intercalate ", " (values.map vid) ++ "]"

def value (locals : List Nat) (e : Expr) : Except String Nat :=
  match strip e with
  | .bvar i => match locals[i]? with
    | some value => .ok value
    | none => .error s!"unbound source variable {i}"
  | _ => .error "proposal grammar requires a source variable here"

structure Code where
  instructions : List String := []
  destinations : List Nat := []
  next : Nat

def emit (code : Code) (inst : String) : Code × Nat :=
  ({ instructions := code.instructions ++ [inst]
     destinations := code.destinations ++ [code.next]
     next := code.next + 1 }, code.next)

/-- Translate the genuine arithmetic tree, rather than choosing a body because
    a declaration happens to have an affine-sounding name. -/
partial def arithmetic (locals : List Nat) (e : Expr) (code : Code) :
    Except String (Code × Nat) := do
  let e := strip e
  if let .bvar _ := e then return (code, ← value locals e)
  let args := e.getAppArgs.toList
  let .const op _ := e.getAppFn | throw "nonconstant arithmetic head"
  let operation ← if op == ``HAdd.hAdd then pure "Add"
    else if op == ``HMul.hMul then pure "Mul"
    else throw s!"unsupported arithmetic head {op}"
  let [left, right] := args.drop (args.length - 2) | throw "arithmetic argument count"
  let (code, a) ← arithmetic locals left code
  let (code, b) ← arithmetic locals right code
  return emit code s!".BinOp .{operation} .U64 {vid a} {vid b}"

def call (e : Expr) : Except String (Name × List Expr) := do
  let e := strip e
  let .const name _ := e.getAppFn | throw "expected named source call"
  return (name, e.getAppArgs.toList)

partial def outerUses (depth : Nat) (e : Expr) : List Nat :=
  match strip e with
  | .bvar i => if depth ≤ i then [i - depth] else []
  | .app f a => outerUses depth f ++ outerUses depth a
  | .lam _ _ body _ => outerUses (depth + 1) body
  | .letE _ _ v body _ => outerUses depth v ++ outerUses (depth + 1) body
  | _ => []

def functionText (name : String) (params returns : String) (code : Code)
    (result : Nat) : String :=
  s!"def {name} : EvalFunction := ClosureU64.function {params} {returns}\n" ++
  "  [" ++ String.intercalate ",\n   " code.instructions ++ "]\n  [" ++
  String.intercalate ", " (code.destinations.map fun n => "[" ++ vid n ++ "]") ++
  s!"] {vid result}\n\n"

def definition (env : Environment) (name : Name) : Except String Expr := do
  let some (.defnInfo ci) := env.find? name | throw s!"not an original definition: {name}"
  return ci.value

def produce (env : Environment) (entry : Name) : Except String String := do
  let some sourceModule := env.getModuleIdxFor? entry | throw "missing original module"
  let owned := env.constants.toList.filter fun (name, ci) =>
    env.getModuleIdxFor? name == some sourceModule && ci.isDefinition
  let (entryParams, entryBody) := lambdas (← definition env entry)
  let .letE _ _ makerCall applyCall _ := strip entryBody | throw "entry must retain a let-bound function"
  let (makerName, makerArgs) ← call makerCall
  let (applyName, applyArgs) ← call applyCall
  let originalNames := [entry, makerName, applyName]
  if owned.length != originalNames.length ||
      !(owned.all fun (name, _) => originalNames.contains name) ||
      originalNames.eraseDups.length != originalNames.length then
    throw "complete original module is not exactly the supported three distinct definitions"
  let (makerParams, makerBody) := lambdas (← definition env makerName)
  let stage := makerArgs.length
  if stage != 2 || makerParams.length != stage + 1 || entryParams.length != 3 then
    throw "proposal grammar requires two captured parameters and one apparent parameter"
  let captureOuter := (outerUses 0 makerBody).filter (· > 0)
  let captureOrder := (captureOuter.map fun i => makerParams.length - 1 - i).eraseDups.mergeSort (· ≤ ·)
  if captureOrder != [0, 1] then throw "proposal needs both live captures in source order"
  let (targetCode, targetResult) ← arithmetic [2, 1, 0] makerBody {next := makerParams.length}
  let (applyParams, applyBody) := lambdas (← definition env applyName)
  let .app f x := strip applyBody | throw "application helper is not dynamic application"
  if applyParams.length != 2 then throw "dynamic application helper arity"
  let f ← value [1, 0] f
  let x ← value [1, 0] x
  let (applyCode, applyResult) := emit {next := 2}
    s!".CallIndirect {vid f} (⟨0⟩ : FuncTyId) {nats [x]} .Rust"
  let entryLocals := (List.range entryParams.length).reverse
  let makerValues ← makerArgs.mapM (value entryLocals)
  let (callerCode, held) := emit {next := entryParams.length}
    s!".Call (⟨1⟩ : FuncId) {nats makerValues}"
  let applyValues ← applyArgs.mapM (value (held :: entryLocals))
  let (callerCode, callerResult) := emit callerCode
    s!".Call (⟨2⟩ : FuncId) {nats applyValues}"
  let (makerCode, makerResult) := emit {next := stage}
    s!".MakeClosure (⟨0⟩ : ClosureTyId) (⟨3⟩ : FuncId) {nats captureOrder}"
  let header := "/- GENERATED UNTRUSTED PROPOSAL from Original's actual kernel definitions.\n" ++
    "   This quotation supplies no source, runtime, ABI or object permission. -/\n" ++
    "import Original\nimport ClosureU64\nnamespace SourceProposal\nopen TrustIr\n\n"
  let roster := "def originalRoster : List (String × FuncId) :=\n  [" ++
    String.intercalate ", " (originalNames.zipIdx |>.map fun (n, i) => s!"(\"{n}\", ⟨{i}⟩)") ++ "]\n" ++
    s!"def liftedRoster : List (String × FuncId) := [(\"{makerName}.__closure_target\", ⟨3⟩)]\n\n"
  return header ++ roster ++
    functionText "target" "[.U64, .U64, .U64]" "[.U64]" targetCode targetResult ++
    functionText "maker" "[.U64, .U64]" "[.Closure ⟨0⟩]" makerCode makerResult ++
    functionText "application" "[.Closure ⟨0⟩, .U64]" "[.U64]" applyCode applyResult ++
    functionText "caller" "[.U64, .U64, .U64]" "[.U64]" callerCode callerResult ++
    "def context (depth : Nat) : EvalContext :=\n  { EvalContext.empty with\n" ++
    "    maxCallDepth := depth + 3\n    functions := fun id =>\n" ++
    "      if id == (⟨0⟩ : FuncId) then some caller\n" ++
    "      else if id == (⟨1⟩ : FuncId) then some maker\n" ++
    "      else if id == (⟨2⟩ : FuncId) then some application\n" ++
    "      else if id == (⟨3⟩ : FuncId) then some target else none\n" ++
    "    funcTys := fun id => if id == (⟨0⟩ : FuncTyId) then\n" ++
    "      some {params := [.U64], returns := [.U64], isVararg := false} else none\n" ++
    "    closures := fun id => if id == (⟨0⟩ : ClosureTyId) then\n" ++
    "      some {func := ⟨0⟩, captures := [.U64, .U64]} else none }\n\nend SourceProposal\n"

end UntrustedClosureProposal

run_cmd do
  let env ← getEnv
  let proposal ← match UntrustedClosureProposal.produce env ``EscapingOriginal.useAffine with
    | .ok text => pure text
    | .error error => throwError "untrusted proposal generation refused: {error}"
  liftIO <| IO.FS.writeFile "Proposal.lean" proposal
  logInfo "wrote untrusted Proposal.lean from all three original kernel definitions and the lifted body"
