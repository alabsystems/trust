-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderDeclarations
import C11ActualDeclarationData

/-! A supported, one-parameter function-like macro source checker/expander.
This handles the ACTUAL fence definition, with source adjacency checked before
its parameter list. It is not a full preprocessor: conditional/include/undef
order, recursive argument prescan, #/##/variadics and general invocations still
require checked support. A resulting builtin-looking identifier is ONLY TOKENS,
never a C11 intrinsic/semantic permission or a source-owned declaration. -/
namespace C11FunctionMacros
open C11HeaderDeclarations
structure Definition where
  name : String
  parameter : String
  body : List String
  deriving DecidableEq, BEq, Repr
private def starts : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: tail, b :: rest => a == b && starts tail rest
private def identifier (name : String) : Bool :=
  C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) []

/-- Reserved preprocessing operators cannot be rebound in this supported
slice, through either function-like or object-like definitions. -/
private def reservedOperator (name : String) : Bool :=
  name == "_Pragma" || name == "__VA_ARGS__"

/-- Physical adjacency matters: f(x) defines a function-like macro, but f (x)
does not. The supported directive spelling is exact and conservative. -/
def parse (source : String) : Option Definition := do
  if (source.toList.filter (· == '\n')).length != 1 then none else
  let tokens ← C11DeclarationLexer.tokenize source
  if tokens.getLast? != some "\n" then none else
  match tokens.dropLast with
  | "#" :: "define" :: name :: "(" :: parameter :: ")" :: body =>
      if identifier name && identifier parameter && !reservedOperator name && !reservedOperator parameter &&
          starts ("#define " ++ name ++ "(").toList source.toList && !body.isEmpty &&
          !body.contains "#" && !body.contains "##" && !body.contains "__VA_ARGS__" && !body.contains "_Pragma"
      then some { name := name, parameter := parameter, body := body } else none
  | _ => none

/-- One-token identifier arguments only; nested and multi-argument forms
refuse instead of guessing argument boundaries or evaluating source effects. -/
def substitute (definition : Definition) (invocation : List String) : Option (List String) :=
  match invocation with
  | [name, "(", argument, ")"] =>
      if name == definition.name && identifier argument then
        some (definition.body.flatMap (fun token => if token == definition.parameter then [argument] else [token]))
      else none
  | _ => none

/-- Even if two bodies are equal, ambiguous definition custody refuses.
No first-match fallback silently chooses an active conditional branch. -/
def expand (sources : List String) (invocation : List String) : Option (List String) := do
  let definitions ← sources.mapM parse
  let some name := invocation.head? | none
  let [definition] := definitions.filter (fun definition => definition.name == name) | none
  substitute definition invocation

/-- Supported-context expansion includes object argument prescan and result
rescan. Unknown context completeness remains an actual-TU obligation. Nested
function-like dependencies refuse; they are not silently assumed unbound.
A same-name object/function macro collision refuses across the shared namespace. -/
def expandSupported (fuel : Nat) (objects : Bindings) (sources : List String)
    (invocation : List String) : Option (List String) := do
  let definitions ← sources.mapM parse
  if objects.macros.any (fun object => reservedOperator object.1) ||
      definitions.any (fun definition => reservedOperator definition.name) ||
      definitions.any (fun definition => objects.macros.any (fun object => object.1 == definition.name))
  then none else do
    let [name, "(", argument, ")"] := invocation | none
    let [definition] := definitions.filter (fun definition => definition.name == name) | none
    let [argument] ← expandObjects fuel objects [argument] | none
    let body ← substitute definition [name, "(", argument, ")"]
    let result ← expandObjects fuel objects body
    if result.contains "_Pragma" || result.contains "__VA_ARGS__" ||
        definitions.any (fun definition => result.contains definition.name) then none else some result

theorem actual_fence_definition : parse C11ActualDeclarationData.atomic_thread_fence_0 =
    some { name := "atomic_thread_fence", parameter := "order", body := ["__c11_atomic_thread_fence", "(", "order", ")"] } := by rfl

theorem captured_fence_substitution :
    expand [C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "memory_order_acquire", ")"] =
    some ["__c11_atomic_thread_fence", "(", "memory_order_acquire", ")"] := by rfl

theorem whitespace_is_not_function_adjacency :
    parse "#define f (x) x\n" = none := by rfl

theorem duplicate_definition_refused :
    expand [C11ActualDeclarationData.atomic_thread_fence_0, C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "memory_order_acquire", ")"] = none := by rfl

theorem wrong_call_arity_refused :
    expand [C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "memory_order_acquire", ",", "memory_order_relaxed", ")"] = none := by rfl

theorem two_source_directives_refused : parse "#define f(x) x\n#undef f\n" = none := by rfl

theorem unsupported_stringizing_refused : parse "#define f(x) #x\n" = none := by rfl

/-- Substitution can duplicate source tokens; no purity/evaluation-order fact
is silently inferred from successful macro expansion. -/
theorem duplicated_parameter_remains_visible :
    expand ["#define f(x) g(x,x)\n"] ["f", "(", "argument", ")"] =
      some ["g", "(", "argument", ",", "argument", ")"] := by rfl

/-- Ordinary type lookup is still absent after obtaining a builtin-looking
name: the target intrinsic semantic owner has NOT been supplied. -/
theorem expanded_name_is_not_an_intrinsic_license :
    C11HeaderTyping.infer 8 { target := some C11HeaderTyping.int32Target }
      (.call "__c11_atomic_thread_fence" []) = none := by rfl

theorem supported_empty_object_context :
    expandSupported 32 {} [C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "memory_order_acquire", ")"] =
    some ["__c11_atomic_thread_fence", "(", "memory_order_acquire", ")"] := by rfl

/-- A builtin-looking target can itself be replaced in the supplied context;
no immutable intrinsic-name assumption can override real preprocessing. -/
theorem builtin_looking_name_rescanned :
    expandSupported 32 { macros := [("__c11_atomic_thread_fence", ["changed_target"])] }
      [C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "memory_order_acquire", ")"] =
    some ["changed_target", "(", "memory_order_acquire", ")"] := by rfl

theorem argument_object_macro_prescanned :
    expandSupported 32 { macros := [("chosen_order", ["memory_order_acquire"])] }
      [C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "chosen_order", ")"] =
    some ["__c11_atomic_thread_fence", "(", "memory_order_acquire", ")"] := by rfl

theorem cross_macro_namespace_collision_refused :
    expandSupported 32 { macros := [("atomic_thread_fence", ["changed"])] }
      [C11ActualDeclarationData.atomic_thread_fence_0]
      ["atomic_thread_fence", "(", "memory_order_acquire", ")"] = none := by rfl

theorem nested_function_dependency_refused :
    expandSupported 32 {} ["#define f(x) g(x)\n", "#define g(y) h(y)\n"]
      ["f", "(", "argument", ")"] = none := by rfl

theorem unsupported_varargs_token_refused : parse "#define f(x) __VA_ARGS__\n" = none := by rfl

theorem unsupported_pragma_effect_refused : parse "#define f(x) _Pragma(x)\n" = none := by rfl

/-- Unsupported preprocessing effects can be introduced by an argument or
its expansion, not just spelled directly in the definition body. -/
theorem indirect_pragma_argument_refused :
    expandSupported 32 {} ["#define f(x) x\n"] ["f", "(", "_Pragma", ")"] = none := by rfl

theorem indirect_pragma_object_expansion_refused :
    expandSupported 32 { macros := [("argument", ["_Pragma"])] }
      ["#define f(x) x\n"] ["f", "(", "argument", ")"] = none := by rfl

theorem reserved_operator_cannot_be_macro_masked :
    expandSupported 32 { macros := [("_Pragma", ["changed"])] }
      ["#define f(x) x\n"] ["f", "(", "_Pragma", ")"] = none := by rfl

theorem reserved_function_name_refused :
    parse "#define _Pragma(x) replacement\n" = none := by rfl

theorem reserved_operator_cannot_be_function_masked :
    expandSupported 32 {} ["#define _Pragma(x) replacement\n"]
      ["_Pragma", "(", "argument", ")"] = none := by rfl

theorem unused_reserved_function_context_refused :
    expandSupported 32 {}
      [C11ActualDeclarationData.atomic_thread_fence_0, "#define _Pragma(x) replacement\n"]
      ["atomic_thread_fence", "(", "memory_order_acquire", ")"] = none := by rfl

#print axioms actual_fence_definition
#print axioms captured_fence_substitution
end C11FunctionMacros
