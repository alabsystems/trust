-- Copyright 2026 Andrew Yates | Apache-2.0
import Init

/-! Streaming declaration-fragment lexer on decoded source characters.
Source encoding/character mapping is a separate input relation. Unsupported
backslash/trigraph/CR/NUL features refuse BEFORE comments. Unicode is allowed
inside comments only. Physical newlines remain explicit; macro parsing also
requires one physical line. Unsupported compound punctuators never split into
shorter accepted tokens. Generic chunk equations permit small checked cuts. -/
namespace C11DeclarationLexer
inductive Mode where
  | normal | word | slash | line | block | star | hash | equal | asterisk
  deriving DecidableEq, BEq, Repr
structure State where
  mode : Mode := .normal
  word : List Char := []
  reversed : List String := []
  deriving DecidableEq, BEq, Repr

def initial : State := {}
private def letter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def wordChar (c : Char) : Bool := letter c || digit c
private def space (c : Char) : Bool := c == ' ' || c == '\t' || c == '\x0b' || c == '\x0c'
private def emit (state : State) (token : String) : State :=
  { mode := .normal, word := [], reversed := token :: state.reversed }
private def normal (state : State) (c : Char) : Option State :=
  if space c then some state
  else if c == '\n' then some (emit state "\n")
  else if wordChar c then some { state with mode := .word, word := [c] }
  else if c == '/' then some { state with mode := .slash }
  else if c == '#' then some { state with mode := .hash }
  else if c == '=' then some { state with mode := .equal }
  else if c == '*' then some { state with mode := .asterisk }
  else if [ '{', '}', '[', ']', '(', ')', ';', ',' ].contains c
    then some (emit state (String.singleton c))
  else none

def step (state : State) (c : Char) : Option State :=
  if c == '\\' || c == '?' || c == '\r' || c == '\x00' then none else
  match state.mode with
  | .normal => normal state c
  | .word => if wordChar c then some { state with word := c :: state.word }
      else normal (emit state (String.ofList state.word.reverse)) c
  | .slash => if c == '/' then some { state with mode := .line }
      else if c == '*' then some { state with mode := .block } else none
  | .line => if c == '\n' then some (emit state "\n") else some state
  | .block => if c == '*' then some { state with mode := .star }
      else if c == '\n' then some { (emit state "\n") with mode := .block } else some state
  | .star => if c == '/' then some { state with mode := .normal }
      else if c == '*' then some state
      else if c == '\n' then some { (emit state "\n") with mode := .block }
      else some { state with mode := .block }
  | .hash => if c == '#' then none else normal (emit state "#") c
  | .equal => if c == '=' then none else normal (emit state "=") c
  | .asterisk => if c == '=' || c == '/' then none else normal (emit state "*") c

def finish (state : State) : Option (List String) :=
  match state.mode with
  | .normal | .line => some state.reversed.reverse
  | .word => some ((emit state (String.ofList state.word.reverse)).reversed.reverse)
  | .hash => some ((emit state "#").reversed.reverse)
  | .equal => some ((emit state "=").reversed.reverse)
  | .asterisk => some ((emit state "*").reversed.reverse)
  | _ => none

def feed (state : Option State) (chars : List Char) : Option State :=
  chars.foldl (fun state char => state.bind (fun state => step state char)) state

def tokenizeCharacters (source : List Char) : Option (List String) :=
  (feed (some initial) source).bind finish

def tokenize (source : String) : Option (List String) := tokenizeCharacters source.toList

def tokenizeChunks (chunks : List (List Char)) : Option (List String) :=
  (chunks.foldl feed (some initial)).bind finish

theorem feed_append (state : Option State) (a b : List Char) :
    feed state (a ++ b) = feed (feed state a) b := by exact List.foldl_append

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

theorem newline_not_erased : tokenize "#define x y\n#undef x\n" =
    some ["#", "define", "x", "y", "\n", "#", "undef", "x", "\n"] := by rfl

theorem unterminated_comment_refused : tokenize "typedef int X; /*" = none := by rfl

theorem line_splice_in_comment_refused : tokenize "// \\\n typedef int X;" = none := by rfl

theorem unicode_in_comment_only : tokenize "typedef /* — */ int X;" =
    some ["typedef", "int", "X", ";"] := by rfl

theorem unicode_identifier_refused : tokenize "typedef int —;" = none := by rfl

theorem compound_punctuator_not_split : tokenize "#define x a##b\n" = none := by rfl
end C11DeclarationLexer
