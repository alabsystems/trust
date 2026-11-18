-- Copyright 2026 Andrew Yates | Apache-2.0
import C11ActualDeclarations

/-! Source/annotation hostility controls. Actual complete declaration tokens,
not a record name or proposed type, determine nominal field bindings. These
remain fragment facts; no full active-TU/builtin/source-execution right follows. -/
namespace C11DeclarationControls
open C11HeaderTyping C11HeaderDeclarations C11ActualDeclarationData C11ActualDeclarations

def withHeaderTokens (tokens : List String) : Option Bindings := do
  let bindings ← installSources [uint8_t_0, uint16_t_0, uint32_t_0]
  let declaration ← parseDeclaration 32 (tokens.filter (· != "\n"))
  let bindings ← install 32 bindings declaration
  let object ← parseComplete 32 clean_obj_0
  install 32 bindings object

def strippedAtomic : List String :=
  C11DeclarationCuts.clean_obj_header_tokens.filter (· != "_Atomic")

theorem omitted_atomic_is_not_original_tokens :
    (strippedAtomic == C11DeclarationCuts.clean_obj_header_tokens) = false := by rfl

/-- Forged proposed atomics cannot come from the same record/field names if
the complete declaration actually lacks the _Atomic qualifier. -/
theorem omitted_atomic_binding_refused :
    (withHeaderTokens strippedAtomic).bind
      (fun bindings => bindAtomicMember bindings "clean_obj" "header" "ref_count") = none := by
  simp only [withHeaderTokens, installSources, List.foldlM_cons, List.foldlM_nil,
    uint8_declaration, uint16_declaration, uint32_declaration, object_complete_declaration]
  rfl

theorem duplicate_field_source_refused :
    parseComplete 32 "typedef struct R { unsigned int x; unsigned int x; } R;" = none := by rfl

theorem void_field_source_refused :
    installSources ["typedef struct R { void x; } R;"] = none := by rfl

theorem nonfinal_flexible_field_refused :
    installSources ["typedef struct R { unsigned int x[]; unsigned int y; } R;"] = none := by rfl

theorem only_flexible_field_refused :
    installSources ["typedef struct R { unsigned int x[]; } R;"] = none := by rfl

theorem keyword_alias_refused :
    parseComplete 32 "typedef unsigned int if;" = none := by rfl

theorem multiline_macro_refused :
    parseComplete 32 "#define x /*\n*/ y\n" = none := by rfl

theorem function_macro_not_object_alias :
    parseComplete 32 "#define f(x) x\n" = none := by rfl

/-- Changed actual replacement text changes the derived value despite the
same original macro name. No threshold is inferred from that name. -/
theorem changed_threshold_not_name_bound :
    literalFromSource "#define CLEAN_RC_STICKY_DROP 0x0000002Au\n" "CLEAN_RC_STICKY_DROP" =
      some (.unsigned 42) := by rfl

#print axioms omitted_atomic_binding_refused
#print axioms changed_threshold_not_name_bound
end C11DeclarationControls
