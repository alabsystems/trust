-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderDeclarations
import C11HeaderLiterals
import C11ActualDeclarationData
import C11DeclarationCuts
namespace C11ActualDeclarations
open C11HeaderDeclarations C11HeaderTyping C11ActualDeclarationData
theorem uint8_declaration : parseComplete 32 uint8_t_0 =
    some (.alias "uint8_t" (.builtin .cUChar)) := by rfl

theorem uint16_declaration : parseComplete 32 uint16_t_0 =
    some (.alias "uint16_t" (.builtin .cUShort)) := by rfl

theorem uint32_declaration : parseComplete 32 uint32_t_0 =
    some (.alias "uint32_t" (.builtin .cUInt)) := by rfl

theorem header_complete_declaration : parseComplete 32 clean_obj_header_0 =
    some (.recordAlias "clean_obj_header" "clean_obj_header" [
      { name := "ref_count", type := .atomic (.named "uint32_t") },
      { name := "tag", type := .named "uint8_t" },
      { name := "kind", type := .named "uint8_t" },
      { name := "num_objs", type := .named "uint8_t" },
      { name := "scalar_sz", type := .named "uint8_t" }]) := by
  unfold parseComplete
  rw [C11DeclarationCuts.clean_obj_header_source_lex]
  rfl

theorem object_complete_declaration : parseComplete 32 clean_obj_0 =
    some (.recordAlias "clean_obj" "clean_obj" [
      { name := "header", type := .named "clean_obj_header" },
      { name := "fields", type := .flexibleArray (.pointer (.record "clean_obj")) }]) := by
  unfold parseComplete
  rw [C11DeclarationCuts.clean_obj_source_lex]
  rfl

def installSources (sources : List String) : Option Bindings :=
  sources.foldlM (fun bindings source => do
    let declaration ← parseComplete 32 source
    install 32 bindings declaration) {}

def declarationBindings : Option Bindings :=
  installSources [uint8_t_0, uint16_t_0, uint32_t_0, clean_obj_header_0, clean_obj_0]

theorem actual_header_address_type :
    declarationBindings.bind (fun bindings => bindAtomicMember bindings "clean_obj" "header" "ref_count") =
      some (.pointer (.atomic .cUInt)) := by
  simp only [declarationBindings, installSources, List.foldlM_cons, List.foldlM_nil, uint8_declaration, uint16_declaration, uint32_declaration, header_complete_declaration, object_complete_declaration]
  rfl

/-- Both preprocessor alternatives remain visible. No first-definition or
producer-selected-branch fallback can create a binding. -/
theorem unresolved_bool_branches_refused : installSources [bool_0, bool_1] = none := by rfl

theorem actual_atomic_alias_is_only_tokens :
    parseComplete 32 atomic_load_explicit_0 =
      some (.objectMacro "atomic_load_explicit" ["__c11_atomic_load"]) := by rfl

/-- The function-like fence macro cannot masquerade as an object-like alias. -/
theorem function_macro_requires_new_parser : parseComplete 32 atomic_thread_fence_0 = none := by rfl

theorem actual_bool_expansion :
    (installSources [bool_0]).bind (fun bindings => expandObjects 16 bindings ["bool"]) =
      some ["_Bool"] := by rfl

theorem alias_gives_no_callee_type :
    infer 8 { target := some int32Target } (.call "__c11_atomic_load" []) = none := by rfl

theorem duplicate_record_binding_refused :
    installSources [uint8_t_0, uint32_t_0, clean_obj_header_0, clean_obj_header_0] = none := by
  simp only [declarationBindings, installSources, List.foldlM_cons, List.foldlM_nil, uint8_declaration, uint16_declaration, uint32_declaration, header_complete_declaration, object_complete_declaration]
  rfl

theorem two_directives_not_one_macro :
    parseComplete 32 "#define x y\n#undef x\n" = none := by rfl

/-- Derive the constant from its actual complete definition, not its name or
Clang's numeric annotation. Active-TU/conditional binding remains unproved. -/
def literalFromSource (source name : String) : Option Raw := do
  let bindings ← installSources [source]
  let [token] ← expandObjects 16 bindings [name] | none
  C11HeaderLiterals.parse int32Target token

theorem drop_cutoff_from_definition : literalFromSource CLEAN_RC_STICKY_DROP_0 "CLEAN_RC_STICKY_DROP" =
    some (.unsigned 3758096384) := by rfl

theorem increment_cutoff_from_definition : literalFromSource CLEAN_RC_STICKY_0 "CLEAN_RC_STICKY" =
    some (.unsigned 4026531840) := by rfl

theorem false_branch_fragment_conversion :
    (literalFromSource false_0 "false").bind (fun expression =>
      infer 4 { target := some int32Target } (.boolCast expression)) =
    some { type := .cBool, conversions := [.intToBool] } := by rfl

/-- Type the actual &(o->header.ref_count) form using only the derived
nominal declarations. This establishes no pointer value, offset or permission.
The complete active-TU/macro/parameter binding and target widths still remain
separate; no producer annotation supplies a hidden atomic operation meaning. -/
def memberEnvironment : Option Environment := do
  let bindings ← declarationBindings
  let parameter ← resolve 32 bindings (.pointer (.named "clean_obj"))
  return { target := some int32Target, variables := [("o", parameter)], records := bindings.records }

def memberExpression : Raw := .addressOf
  (.member (.pointerMember (.variable "o") "header") "ref_count")

theorem derived_member_expression_type :
    memberEnvironment.bind (fun environment => infer 16 environment memberExpression) =
    some { type := .pointer (.atomic .cUInt), conversions := [.lvalueToRValue] } := by
  simp only [memberEnvironment, declarationBindings, installSources, List.foldlM_cons, List.foldlM_nil,
    uint8_declaration, uint16_declaration, uint32_declaration, header_complete_declaration, object_complete_declaration]
  rfl

theorem missing_member_refused :
    memberEnvironment.bind (fun environment => infer 16 environment
      (.addressOf (.member (.pointerMember (.variable "o") "header") "absent"))) = none := by
  simp only [memberEnvironment, declarationBindings, installSources, List.foldlM_cons, List.foldlM_nil,
    uint8_declaration, uint16_declaration, uint32_declaration, header_complete_declaration, object_complete_declaration]
  rfl

theorem rvalue_address_refused :
    infer 4 { target := some int32Target } (.addressOf (.decimal 1)) = none := by rfl

#print axioms actual_header_address_type
#print axioms unresolved_bool_branches_refused
end C11ActualDeclarations
