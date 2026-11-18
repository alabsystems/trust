-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderAST

/-! A total complete-token shape checker for the two supported fragments.
Names are proposed DATA and checked as identifiers, never a semantic whitelist.
Success builds a typed intrinsic-role PROPOSAL: actual macro/type/field/builtin
resolution still requires checked TU binding. In particular it grants no source
meaning from the spelling atomic_load_explicit or clean_is_scalar. -/
namespace C11HeaderParser
open C11HeaderAST

def keywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do", "double",
   "else", "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long",
   "register", "restrict", "return", "short", "signed", "sizeof", "static", "struct",
   "switch", "typedef", "union", "unsigned", "void", "volatile", "while", "_Alignas",
   "_Alignof", "_Atomic", "_Bool", "_Complex", "_Generic", "_Imaginary", "_Noreturn",
   "_Static_assert", "_Thread_local"]
def identifier (name : String) : Bool :=
  C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) [] &&
    !keywords.contains name
def namesValid (p : CAtomicDropSyntax.Proposal) : Bool :=
  identifier p.functionName && identifier p.argument && identifier p.thresholdMacro

def parseDrop (names : CAtomicDropSyntax.Proposal) (input : List String) :
    Option (Stmt .boolean) :=
  if namesValid names && decide (input = functionTokens "bool" names (drop names.thresholdMacro))
  then some (drop names.thresholdMacro) else none

def parseIncrement (names : CAtomicDropSyntax.Proposal) (input : List String) :
    Option (Stmt .unit) :=
  if namesValid names && decide (input = functionTokens "void" names (increment names.thresholdMacro))
  then some (increment names.thresholdMacro) else none

/-- Parser success retains the COMPLETE rendering equality, not a prefix match.
This theorem establishes syntax only; the intrinsic-role proposal is not TU typing. -/
theorem parse_drop_complete (p : CAtomicDropSyntax.Proposal) (input : List String)
    (success : (parseDrop p input).isSome = true) :
    input = functionTokens "bool" p (drop p.thresholdMacro) := by
  unfold parseDrop at success
  split at success
  next h => exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  next => contradiction

theorem parse_increment_complete (p : CAtomicDropSyntax.Proposal) (input : List String)
    (success : (parseIncrement p input).isSome = true) :
    input = functionTokens "void" p (increment p.thresholdMacro) := by
  unfold parseIncrement at success
  split at success
  next h => exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  next => contradiction

theorem actual_drop_parses :
    parseDrop CAtomicDropSource.proposal (CAtomicDropSyntax.tokens CAtomicDropSource.proposal) =
      some (drop CAtomicDropSource.proposal.thresholdMacro) := by rfl

theorem actual_increment_parses :
    parseIncrement CAtomicIncrementSource.proposal (CAtomicIncrementSyntax.tokens CAtomicIncrementSource.proposal) =
      some (increment CAtomicIncrementSource.proposal.thresholdMacro) := by rfl

/-- Full original source bytes, complete ordinary-token witness AND checked AST
shape are retained together; neither conjunct asserts macro/TU meaning. -/
theorem actual_drop_source_and_parse :
    C11OrdinaryTokens.Lexes CAtomicDropSource.actualSource
      (CAtomicDropSyntax.tokens CAtomicDropSource.proposal) ∧
    parseDrop CAtomicDropSource.proposal (CAtomicDropSyntax.tokens CAtomicDropSource.proposal) =
      some (drop CAtomicDropSource.proposal.thresholdMacro) :=
  ⟨C11ActualTokens.drop_actual_lexes, actual_drop_parses⟩

theorem actual_increment_source_and_parse :
    C11OrdinaryTokens.Lexes CAtomicIncrementSource.actualSource
      (CAtomicIncrementSyntax.tokens CAtomicIncrementSource.proposal) ∧
    parseIncrement CAtomicIncrementSource.proposal (CAtomicIncrementSyntax.tokens CAtomicIncrementSource.proposal) =
      some (increment CAtomicIncrementSource.proposal.thresholdMacro) :=
  ⟨C11ActualTokens.increment_actual_lexes, actual_increment_parses⟩

theorem appended_statement_refused :
    parseDrop CAtomicDropSource.proposal
      (CAtomicDropSyntax.tokens CAtomicDropSource.proposal ++ ["return", "true", ";"]) = none := by rfl

theorem arithmetic_operator_mutant_refused :
    parseDrop CAtomicDropSource.proposal
      ((CAtomicDropSyntax.tokens CAtomicDropSource.proposal).map
        (fun token => if token == "atomic_fetch_sub_explicit" then "atomic_fetch_add_explicit" else token)) = none := by rfl

theorem wrong_return_type_refused :
    parseDrop CAtomicDropSource.proposal
      (functionTokens "void" CAtomicDropSource.proposal (drop CAtomicDropSource.proposal.thresholdMacro)) = none := by rfl

theorem malformed_identifier_refused :
    namesValid { functionName := "drop", argument := "x+y", thresholdMacro := "limit" } = false := by rfl

/-- Preprocessing identifiers are not automatically legal declarator names. -/
theorem keyword_declarator_refused :
    namesValid { functionName := "if", argument := "o", thresholdMacro := "limit" } = false := by rfl

#print axioms actual_drop_source_and_parse
#print axioms arithmetic_operator_mutant_refused
end C11HeaderParser
