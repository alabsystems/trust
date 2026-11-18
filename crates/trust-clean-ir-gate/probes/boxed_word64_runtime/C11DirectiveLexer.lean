-- Copyright 2026 Andrew Yates | Apache-2.0
import C11DeclarationLexer

/-! Supported directive-condition punctuation layered on the checked character
lexer. Comments/newlines/identifiers retain the base rules; !/!=, < / <=,
> / >= and && get maximal-munch tokens only OUTSIDE comments. Other C/CPP
operator/extension families remain unsupported. No type/target/TU permission. -/
namespace C11DirectiveLexer
inductive Pending where
  | none | amp | bang | less | greater
  deriving DecidableEq, BEq, Repr
structure State where
  base : C11DeclarationLexer.State := C11DeclarationLexer.initial
  pending : Pending := .none
  deriving DecidableEq, BEq, Repr

def initial : State := {}
private def emit (base : C11DeclarationLexer.State) (token : String) : C11DeclarationLexer.State :=
  { mode := .normal, word := [], reversed := token :: base.reversed }
private def operator (char : Char) : Pending :=
  if char == '&' then .amp else if char == '!' then .bang
  else if char == '<' then .less else if char == '>' then .greater else .none
private def start (base : C11DeclarationLexer.State) (char : Char) : Option State :=
  let pending := operator char
  if pending != .none && (base.mode == .normal || base.mode == .word) then
    let base := if base.mode == .word then emit base (String.ofList base.word.reverse) else base
    some { base := base, pending := pending }
  else do return { base := ← C11DeclarationLexer.step base char }

def step (state : State) (char : Char) : Option State :=
  if char == '\\' || char == '?' || char == '\r' || char == '\x00' then none else
  match state.pending with
  | .none => start state.base char
  | .amp => if char == '&' then some { base := emit state.base "&&" } else none
  | .bang => if char == '=' then some { base := emit state.base "!=" } else start (emit state.base "!") char
  | .less => if char == '<' then none else if char == '=' then some { base := emit state.base "<=" } else start (emit state.base "<") char
  | .greater => if char == '>' then none else if char == '=' then some { base := emit state.base ">=" } else start (emit state.base ">") char

def finish (state : State) : Option (List String) :=
  match state.pending with
  | .none => C11DeclarationLexer.finish state.base
  | .amp => none
  | .bang => C11DeclarationLexer.finish (emit state.base "!")
  | .less => C11DeclarationLexer.finish (emit state.base "<")
  | .greater => C11DeclarationLexer.finish (emit state.base ">")

def feed (state : Option State) (chars : List Char) : Option State :=
  chars.foldl (fun state char => state.bind (fun state => step state char)) state

def tokenizeCharacters (source : List Char) : Option (List String) :=
  (feed (some initial) source).bind finish

def tokenize (source : String) : Option (List String) := tokenizeCharacters source.toList

theorem feed_append (state : Option State) (a b : List Char) :
    feed state (a ++ b) = feed (feed state a) b := by exact List.foldl_append

def tokenizeChunks (chunks : List (List Char)) : Option (List String) :=
  (chunks.foldl feed (some initial)).bind finish

theorem feed_chunks (chunks : List (List Char)) (state : Option State) :
    chunks.foldl feed state = feed state chunks.flatten := by
  induction chunks generalizing state with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldl_cons, List.flatten_cons]
    rw [ih, feed_append]

theorem chunks_exact (chunks : List (List Char)) :
    tokenizeChunks chunks = tokenizeCharacters chunks.flatten := by
  unfold tokenizeChunks tokenizeCharacters
  rw [feed_chunks]

theorem actual_condition_punctuation : tokenize "#if defined(x) && x >= 201112L\n" =
    some ["#", "if", "defined", "(", "x", ")", "&&", "x", ">=", "201112L", "\n"] := by rfl

theorem comment_operators_not_executed : tokenize "/* ! && >= */ x\n" = some ["x", "\n"] := by rfl

theorem missing_second_amp_refused : tokenize "#if x & y\n" = none := by rfl

theorem malformed_operator_not_split : tokenize "#if x &&& y\n" = none := by rfl

theorem unsupported_splice_before_comments : tokenize "/* \\\n */ x\n" = none := by rfl
theorem unsupported_shift_not_split : tokenize "#if x >> y\n" = none := by rfl
end C11DirectiveLexer
