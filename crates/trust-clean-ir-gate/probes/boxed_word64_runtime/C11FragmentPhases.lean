-- Copyright 2026 Andrew Yates | Apache-2.0
import CAtomicDropSyntax

/-!
Mechanical trigraph replacement and single-pass line splicing for already
mapped LF byte fragments: WG14 N1570 §§5.1.1.2, 5.2.1.1,
https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf .
This is not a complete C preprocessor or an operational C11 model. Character-set
mapping, whole-file constraints, include/macro processing, typing and execution
remain open. In particular fragments need not themselves be whole source files.
-/
namespace C11FragmentPhases
open CAtomicDropSyntax

private def trigraph (b : UInt8) : Option UInt8 :=
  if b == 61 then some 35       -- ??= -> #
  else if b == 47 then some 92  -- ??/ -> backslash
  else if b == 39 then some 94  -- ??' -> ^
  else if b == 40 then some 91  -- ??( -> [
  else if b == 41 then some 93  -- ??) -> ]
  else if b == 33 then some 124 -- ??! -> |
  else if b == 60 then some 123 -- ??< -> {
  else if b == 62 then some 125 -- ??> -> }
  else if b == 45 then some 126 -- ??- -> ~
  else none

def replaceTrigraphs : List UInt8 → List UInt8
  | [] => []
  | [a] => [a]
  | [a, b] => [a, b]
  | a :: b :: c :: rest =>
    if a == 63 && b == 63 then
      match trigraph c with
      | some replacement => replacement :: replaceTrigraphs rest
      | none => a :: replaceTrigraphs (b :: c :: rest)
    else a :: replaceTrigraphs (b :: c :: rest)
termination_by bytes => bytes.length
decreasing_by all_goals simp_wf <;> omega

/-- Single-pass: an emitted backslash is NOT reconsidered against an output
newline. Only adjacency in the incoming physical line is eligible. -/
def spliceLines : List UInt8 → List UInt8
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    if a == 92 && b == 10 then spliceLines rest
    else a :: spliceLines (b :: rest)
termination_by bytes => bytes.length
decreasing_by all_goals simp_wf <;> omega

def mechanical12 (bytes : List UInt8) : List UInt8 :=
  spliceLines (replaceTrigraphs bytes)

/-- The checker deliberately rejects all inputs requiring these phase/profile
transformations, rather than claiming an unchecked raw-source equivalence. -/
def unsupported (b : UInt8) : Bool :=
  b == 92 || b == 63 || !(b == 9 || b == 10 || (32 ≤ b.toNat && b.toNat ≤ 126))
inductive Safe : List UInt8 → Prop where
  | nil : Safe []
  | cons {b : UInt8} {tail : List UInt8} :
      unsupported b = false → Safe tail → Safe (b :: tail)

theorem step_only_safe (s t : State) (b : UInt8) (accepted : step s b = some t) :
    unsupported b = false := by
  by_cases bad : unsupported b = true
  · have blocked : step s b = none := by
      unfold unsupported at bad
      unfold step
      rw [bad]
      rfl
    rw [blocked] at accepted
    cases accepted
  · exact Bool.eq_false_iff.mpr bad

theorem feed_none (bytes : List UInt8) : feed none bytes = none := by
  induction bytes with
  | nil => rfl
  | cons a tail ih => exact ih

theorem feed_only_safe (bytes : List UInt8) (s t : State)
    (accepted : feed (some s) bytes = some t) : Safe bytes := by
  induction bytes generalizing s with
  | nil => exact .nil
  | cons a tail ih =>
    change feed (step s a) tail = some t at accepted
    cases transition : step s a with
    | none =>
      rw [transition, feed_none] at accepted
      cases accepted
    | some next =>
      rw [transition] at accepted
      exact .cons (step_only_safe s next a transition) (ih next accepted)

theorem safe_no_question (b : UInt8) (safe : unsupported b = false) : b ≠ 63 := by
  intro equal
  subst b
  simp [unsupported] at safe

theorem safe_no_backslash (b : UInt8) (safe : unsupported b = false) : b ≠ 92 := by
  intro equal
  subst b
  simp [unsupported] at safe

theorem safe_trigraph_identity (bytes : List UInt8) (safe : Safe bytes) :
    replaceTrigraphs bytes = bytes := by
  induction safe with
  | nil => simp [replaceTrigraphs, spliceLines]
  | @cons b tail head rest ih =>
    cases tail with
    | nil => simp [replaceTrigraphs, spliceLines]
    | cons c tail =>
      cases tail with
      | nil => simp [replaceTrigraphs, spliceLines]
      | cons d more => simp [replaceTrigraphs, safe_no_question b head, ih]

theorem safe_splice_identity (bytes : List UInt8) (safe : Safe bytes) :
    spliceLines bytes = bytes := by
  induction safe with
  | nil => simp [replaceTrigraphs, spliceLines]
  | @cons b tail head rest ih =>
    cases tail with
    | nil => simp [replaceTrigraphs, spliceLines]
    | cons c more => simp [spliceLines, safe_no_backslash b head, ih]

theorem safe_phases_identity (bytes : List UInt8) (safe : Safe bytes) :
    mechanical12 bytes = bytes := by
  rw [mechanical12, safe_trigraph_identity bytes safe, safe_splice_identity bytes safe]

/-- Derived from actual total lexer success, not an assumed successful C run.
No macro/type/full-file/ABI/execution claim is made. -/
theorem tokenized_phases_identity (bytes : List UInt8) (tokens : List String)
    (accepted : tokenize bytes = some tokens) : mechanical12 bytes = bytes := by
  unfold tokenize at accepted
  cases scanned : feed (some initial) bytes with
  | none => simp [scanned] at accepted
  | some final => exact safe_phases_identity bytes (feed_only_safe bytes initial final scanned)

/-- Removing one physical splice must not manufacture another eligible splice. -/
theorem splice_does_not_rescan_output : spliceLines [92, 92, 10, 10] = [92, 10] := by simp [spliceLines]

theorem trigraph_precedes_splicing : mechanical12 [63, 63, 47, 10, 120] = [120] := by simp [mechanical12, replaceTrigraphs, trigraph, spliceLines]

theorem all_nine_trigraphs : replaceTrigraphs
    [63,63,61,32,63,63,47,32,63,63,39,32,63,63,40,32,63,63,41,32,
     63,63,33,32,63,63,60,32,63,63,62,32,63,63,45] =
    [35,32,92,32,94,32,91,32,93,32,124,32,123,32,125,32,126] := by
  simp [replaceTrigraphs, trigraph]

#print axioms tokenized_phases_identity
#print axioms splice_does_not_rescan_output
#print axioms all_nine_trigraphs
end C11FragmentPhases
