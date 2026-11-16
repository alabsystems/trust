/-
Untrusted independent declaration-type DATA producer.  It reads the genuine Lean
4.30 environment, rather than any Clean replay or observation report.  The wire
projection is explicitly tied to Clean248's public Expr/Name/Level serde and the
standard bincode2 configuration used by the maintained serialize_term.  Comparing
these independently produced bytes grants no proof, reference, environment pin,
compiler verdict or source/machine equivalence.

Do not import this module into the fixed production base.  Compile it separately
only after the original source-bound VF5Check module has been built. This is a
candidate wire projection with the maintained canonical-codec budget and selected
metadata guards; it is NOT generic .olean-reader domain equivalence. Other reader
caps (names/strings/lists/levels/BVar) are not established by these fixes. Actual
seven-target use still requires successful real importer/replay of the SAME
source/world-bound package and exact per-target byte comparison.
-/
import VF5Check
import Lean

open Lean

namespace VF5ExpectedTypesData

private def maxBytes : Nat := 64 * 1024 * 1024
private def maxNodes : Nat := 2_000_000
private def maxDepth : Nat := 4096
private def u64Limit : Nat := 2^64
private structure EncodeState where
  output : ByteArray := {}
  nodes : Nat := 0
  nodeLimit : Nat := maxNodes
  depthLimit : Nat := maxDepth

private abbrev EncodeM := StateT EncodeState (Except String)

-- fuel4096 is structural depth1. Recursive calls consume fuel; these explicit
-- depth/count charges match proof_codec::StructuralBudget, including non-Expr
-- nodes. Test-only small limits exercise the SAME production enter function.
private def enter (fuel count : Nat) : EncodeM Unit := do
  let state ← get
  let depth := maxDepth + 1 - fuel
  if depth > state.depthLimit then throw "independent structural depth bound"
  let nodes := state.nodes + count
  if nodes > state.nodeLimit then throw "independent structural node bound"
  set { state with nodes := nodes }

private def emit (b : Nat) : EncodeM Unit := do
  if b >= 256 then throw "independent byte out of range"
  let state ← get
  if state.output.size >= maxBytes then throw "independent type producer byte bound"
  set { state with output := state.output.push (UInt8.ofNat b) }

private def emitLE (n width : Nat) : EncodeM Unit := do
  for i in [0:width] do
    emit ((n / 256^i) % 256)

-- Standard bincode2 unsigned variable integer representation. All enum tags
-- below are the frozen Clean248 public serde declaration indices.
private def uvar (n : Nat) : EncodeM Unit := do
  if n < 251 then emit n
  else if n < 2^16 then do emit 251; emitLE n 2
  else if n < 2^32 then do emit 252; emitLE n 4
  else if n < u64Limit then do emit 253; emitLE n 8
  else throw "independent u64 value out of range"

private def text (s : String) : EncodeM Unit := do
  let bytes := s.toUTF8
  uvar bytes.size
  let state ← get
  if state.output.size + bytes.size > maxBytes then throw "independent type producer byte bound"
  set { state with output := state.output ++ bytes }

private def name : Nat → Name → EncodeM Unit
  | 0, _ => throw "independent name depth bound"
  | fuel + 1, .anonymous => do enter (fuel + 1) 1; uvar 0
  | fuel + 1, .str p s => do enter (fuel + 1) 1; uvar 1; name fuel p; text s
  | fuel + 1, .num p n => do enter (fuel + 1) 1; uvar 2; name fuel p; uvar n

private def level : Nat → Level → EncodeM Unit
  | 0, _ => throw "independent level depth bound"
  | fuel + 1, .zero => do enter (fuel + 1) 1; uvar 0
  | fuel + 1, .succ a => do enter (fuel + 1) 1; uvar 1; level fuel a
  | fuel + 1, .max a b => do enter (fuel + 1) 1; uvar 2; level fuel a; level fuel b
  | fuel + 1, .imax a b => do enter (fuel + 1) 1; uvar 3; level fuel a; level fuel b
  | fuel + 1, .param n => do enter (fuel + 1) 1; uvar 4; name fuel n
  | _ + 1, .mvar _ => throw "metavariable in independent declaration universe"

private def binder (bi : BinderInfo) : EncodeM Unit := do
  uvar (match bi with
    | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3)
  -- Clean's maintained Lean importer constructs BinderData::from(info), with
  -- Multiplicity::Many (tag2). No resource-use proof is inferred here.
  uvar 2

private def natLiteral (fuel n : Nat) : EncodeM Unit := do
  if n < u64Limit then
    uvar 0
    uvar n
  else
    let mut limbs : Array Nat := #[]
    let mut remaining := n
    while remaining > 0 do
      if limbs.size >= maxBytes / 8 then throw "independent natural literal byte bound"
      -- Charge each limb at Literal depth+1 BEFORE its allocation. This is
      -- the same aggregate count as StructuralBudget::validate_literal.
      enter (fuel - 1) 1
      limbs := limbs.push (remaining % u64Limit)
      remaining := remaining / u64Limit
    uvar 1
    uvar limbs.size
    for limb in limbs do uvar limb

private def dataValue (fuel : Nat) (value : DataValue) : EncodeM Unit := do
  match value with
  | .ofBool b => uvar 0; emit (if b then 1 else 0)
  | .ofNat n => uvar 1; uvar n
  | .ofString s => uvar 2; text s
  | .ofName n => uvar 3; name fuel n
  -- Clean stores these as opaque carried metadata. The independent producer
  -- refuses rather than inventing a textual/raw-pointer payload or dropping it.
  | .ofInt _ => throw "opaque integer metadata in independent declaration type"
  | .ofSyntax _ => throw "opaque syntax metadata in independent declaration type"

private def rootComponent : Name → Option String
  | .anonymous => none
  | .str .anonymous s => some s
  | .str parent _ => rootComponent parent
  | .num parent _ => rootComponent parent

private def expr : Nat → Expr → EncodeM Unit
  | 0, _ => throw "independent expression depth bound"
  | fuel + 1, .bvar n => do
    enter (fuel + 1) 1
    if n >= 2^32 then throw "bound variable index overflow"
    uvar 0
    uvar n
  | _ + 1, .fvar _ => throw "free variable in independent declaration type"
  | _ + 1, .mvar _ => throw "metavariable in independent declaration type"
  | fuel + 1, .sort u => do enter (fuel + 1) 1; uvar 2; level fuel u
  | fuel + 1, .const n us => do
    enter (fuel + 1) 1; uvar 3; name fuel n; uvar us.length
    for u in us do level fuel u
  | fuel + 1, .app f a => do enter (fuel + 1) 1; uvar 4; expr fuel f; expr fuel a
  | fuel + 1, .lam _ ty body bi => do
    enter (fuel + 1) 1; uvar 5; binder bi; expr fuel ty; expr fuel body
  | fuel + 1, .forallE _ ty body bi => do
    enter (fuel + 1) 1; uvar 6; binder bi; expr fuel ty; expr fuel body
  | fuel + 1, .letE n ty value body nondep => do
    enter (fuel + 1) 1; uvar 7; name fuel n; expr fuel ty; expr fuel value; expr fuel body
    emit (if nondep then 1 else 0)
  | fuel + 1, .lit (.natVal n) => do
    enter (fuel + 1) 1; enter fuel 1
    uvar 8; uvar 0; natLiteral fuel n
  | fuel + 1, .lit (.strVal s) => do
    enter (fuel + 1) 1; enter fuel 1
    uvar 8; uvar 1; text s
  | fuel + 1, .proj n index value => do
    enter (fuel + 1) 1
    if index >= 2^32 then throw "projection index overflow"
    uvar 9
    name fuel n
    uvar index
    expr fuel value
  | fuel + 1, .mdata data value => do
    enter (fuel + 1) 1
    if data.entries.length > 4096 then throw "Lean metadata has more than 4096 entries"
    uvar 10; uvar data.entries.length
    for (key, item) in data.entries do
      -- The importer rejects this structural root BEFORE value conversion.
      if rootComponent key == some "_clean_lean_mdata" then
        throw "Lean metadata key is in the reserved carriage namespace"
      enter fuel 1
      name (fuel - 1) key
      dataValue (fuel - 1) item
    expr fuel value

private def encodedWith (state : EncodeState) (e : Expr) : Except String ByteArray := do
  let (_, state) ← (expr maxDepth e).run state
  return state.output

private def encoded (e : Expr) : Except String ByteArray :=
  encodedWith {} e

private def checkBytes (label : String) (actual : ByteArray) (wanted : Array Nat) : Except String Unit := do
  unless actual.data.map (fun b => b.toNat) == wanted do
    throw s!"independent encoding regression: {label}; actual={reprStr (actual.data.map (fun b => b.toNat))}; wanted={reprStr wanted}"

-- These are codec/projection controls only, not seven-target kernel proofs.
private def controls : Except String Unit := do
  for (n, wanted) in [
      (250, #[250]), (251, #[251, 251, 0]),
      (65535, #[251, 255, 255]), (65536, #[252, 0, 0, 1, 0]),
      (2^32, #[253, 0, 0, 0, 0, 1, 0, 0, 0]),
      (2^64-1, #[253, 255, 255, 255, 255, 255, 255, 255, 255])] do
    let (_, state) ← (uvar n).run {}
    checkBytes "standard unsigned variable integer boundaries" state.output wanted
  checkBytes "bound variable zero emits both tag and index" (← encoded (.bvar 0)) #[0, 0]
  checkBytes "bound variable varint index is emitted" (← encoded (.bvar 251)) #[0, 251, 251, 0]
  checkBytes "projection zero emits structure, index and inner expression"
    (← encoded (.proj .anonymous 0 (.sort .zero))) #[9, 0, 0, 2, 0]
  checkBytes "sort expression tag" (← encoded (.sort .zero)) #[2, 0]
  checkBytes "explicit universe binder projection"
    (← encoded (.forallE `x (.sort .zero) (.bvar 0) .implicit)) #[6, 1, 2, 2, 0, 0, 0]
  let (_, alphaState) ← (name maxDepth (.str .anonymous "α")).run {}
  let alpha := alphaState.output
  checkBytes "structural name and UTF8 byte length" alpha #[1, 0, 2, 206, 177]
  let (_, numericState) ← (name maxDepth (.num .anonymous 7)).run {}
  let numeric := numericState.output
  let (_, stringState) ← (name maxDepth (.str .anonymous "7")).run {}
  let string := stringState.output
  if numeric == string then throw "numeric/string name components collapsed"
  let letA ← encoded (.letE `a (.sort .zero) (.sort .zero) (.bvar 0) false)
  let letB ← encoded (.letE `b (.sort .zero) (.sort .zero) (.bvar 0) false)
  if letA == letB then throw "let-bound names were discarded"
  checkBytes "large natural limbs are retained" (← encoded (.lit (.natVal (2^64)))) #[8, 0, 1, 2, 0, 1]
  let metadata : KVMap := ⟨[(`testFlag, .ofBool true)]⟩
  let withMetadata ← encoded (.mdata metadata (.sort .zero))
  if withMetadata == (← encoded (.sort .zero)) then throw "metadata was erased"
  let opaqueMetadata : KVMap := ⟨[(`opaque, .ofInt 1)]⟩
  match encoded (.mdata opaqueMetadata (.sort .zero)) with
  | .error _ => pure ()
  | .ok _ => throw "opaque metadata was invented or silently omitted"

private def mustRefuse (label : String) (result : Except String ByteArray) : Except String Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw s!"independent boundary regression: {label}"

private def boundaryControls : Except String Unit := do
  -- Expr1 +Literal1: tiny limits expose the original missing-literal charge.
  let small : Expr := .lit (.natVal 0)
  mustRefuse "literal node is distinct from Expr" (encodedWith { nodeLimit := 1 } small)
  let _ ← encodedWith { nodeLimit := 2 } small
  mustRefuse "literal depth is Expr depth plus one" (encodedWith { depthLimit := 1 } small)
  let _ ← encodedWith { depthLimit := 2 } small
  -- Two limbs only: Expr1 +Literal1 +limbs2, with limbs at depth3.
  let big : Expr := .lit (.natVal (2^64))
  mustRefuse "each BigNat limb is charged" (encodedWith { nodeLimit := 3 } big)
  let _ ← encodedWith { nodeLimit := 4 } big
  mustRefuse "BigNat limbs have their own depth" (encodedWith { depthLimit := 2 } big)
  let _ ← encodedWith { depthLimit := 3 } big
  -- One entry +two-component key: Expr1,entry1,key2,inner Expr1/Level1.
  let key : Name := .str .anonymous "ordinary"
  let md : Expr := .mdata ⟨[(key, .ofBool true)]⟩ (.sort .zero)
  mustRefuse "metadata entry/key node population" (encodedWith { nodeLimit := 5 } md)
  let _ ← encodedWith { nodeLimit := 6 } md
  mustRefuse "metadata key depth is Expr depth plus two" (encodedWith { depthLimit := 3 } md)
  let _ ← encodedWith { depthLimit := 4 } md
  let nameValue : Expr := .mdata ⟨[(.anonymous, .ofName key)]⟩ (.sort .zero)
  mustRefuse "metadata value-Name depth is Expr depth plus two" (encodedWith { depthLimit := 3 } nameValue)
  let _ ← encodedWith { depthLimit := 4 } nameValue
  -- The structural FIRST component matters, rather than a display substring.
  let reserved : Name := .str .anonymous "_clean_lean_mdata"
  for k in [reserved, .str reserved "child", .num reserved 7] do
    mustRefuse "reserved metadata root" (encoded (.mdata ⟨[(k, .ofBool true)]⟩ (.sort .zero)))
  for k in [.str key "_clean_lean_mdata", .str (.num .anonymous 7) "_clean_lean_mdata",
      .str .anonymous "_clean_lean_mdata_neighbor"] do
    let _ ← encoded (.mdata ⟨[(k, .ofBool true)]⟩ (.sort .zero))
  -- 4096 is the maintained importer cap, not a new workload/proof policy.
  let atCap : KVMap := ⟨List.replicate 4096 (.anonymous, .ofBool true)⟩
  let _ ← encoded (.mdata atCap (.sort .zero))
  let pastCap : KVMap := ⟨List.replicate 4097 (.anonymous, .ofBool true)⟩
  mustRefuse "metadata entry 4097" (encoded (.mdata pastCap (.sort .zero)))

private def nameJson : Name → Json
  | .anonymous => .str "Anon"
  | .str p s => Json.mkObj [("Str", .arr #[nameJson p, .str s])]
  | .num p n => Json.mkObj [("Num", .arr #[nameJson p, toJson n])]

private def targets : Array Name := #[
  ``VF5.RowProved, ``VF5.row_of, ``VF5.checkBlob, ``VF5.rowShape,
  ``VF5.vc_sound_F1, ``VF5.compose_F1, ``VF5.rootsSafe_of]

-- The raw bytes are retained; an ordinary SHA256 shell can form the expected
-- DATA book from them. This producer never reads or copies a measured digest.
private def observe (env : Environment) : Except String Json := do
  controls
  boundaryControls
  let mut rows := #[]
  for target in targets do
    let some info := env.find? target | throw s!"missing original declaration {target}"
    if info.name != target then throw "independent declaration name mismatch"
    let (_, state) ← (expr maxDepth info.type).run {}
    let bytes := state.output
    let nodes := state.nodes
    rows := rows.push <| Json.mkObj [
      ("name", nameJson info.name),
      ("level_params", .arr <| info.levelParams.toArray.map nameJson),
      ("canonical_type_bytes", .arr <| bytes.data.map (fun b => toJson b.toNat)),
      ("observed_nodes", toJson nodes)]
  return Json.mkObj [
    ("kind", .str "vf5-independent-lean-target-types-v2"),
    ("projection_scope", .str "candidate wire/codecbudget +metadata guards; not generic importer-domain equivalence"),
    ("clean_revision", .str "24861300fea40294bb485bb630eb216756dc558d"),
    ("lean_world", .str "v4.30.0-rc2"),
    ("target_type_codec", .str "clean_auto::bridge::ay_contract::serialize_term/bincode2-standard"),
    ("production_admission", .bool false),
    ("producer_control_families", .arr #[.str "original-nine-codec-projection-families",
      .str "literal-node-and-depth", .str "two-limb-node-and-depth",
      .str "metadata-entry-and-name-depth", .str "reserved-structural-root", .str "metadata-4096-entry-boundary", .str "bvar-and-projection-wire-emission"]),
    ("target_types", .arr rows)]

open Lean Elab Command in
run_cmd do
  match observe (← getEnv) with
  | .error error => throwError "independent VF5 type observation refused: {error}"
  | .ok value => liftIO <| IO.println ("VF5_INDEPENDENT_TYPE_BYTES=" ++ value.compress)

end VF5ExpectedTypesData
