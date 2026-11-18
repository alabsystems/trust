-- Copyright 2026 Andrew Yates | Apache-2.0
import CAtomicDropSyntax

/-! Complete actual clean_inc fragment shape only. Scalar tagging, macro/type
binding and C11 semantics remain separate. No numeric count supplies rights. -/
namespace CAtomicIncrementSyntax
open CAtomicDropSyntax

def tokens (p : Proposal) : List String :=
  ["static", "inline", "void", p.functionName, "(", "clean_obj", "*", p.argument,
   ")", "{", "if", "(", "!", "clean_is_scalar", "(", p.argument, ")", "&&",
   "atomic_load_explicit", "(", "&", p.argument, "->", "header", ".", "ref_count",
   ",", "memory_order_relaxed", ")", "<", p.thresholdMacro, ")", "{",
   "atomic_fetch_add_explicit", "(", "&", p.argument, "->", "header", ".", "ref_count",
   ",", "1", ",", "memory_order_relaxed", ")", ";", "}", "}"]

def check (source : List UInt8) (proposal : Proposal) : Bool :=
  decide (tokenize source = some (tokens proposal))

theorem check_sound (source : List UInt8) (proposal : Proposal)
    (accepted : check source proposal = true) :
    tokenize source = some (tokens proposal) := of_decide_eq_true accepted

#print axioms check_sound
end CAtomicIncrementSyntax
