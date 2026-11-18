-- Copyright 2026 Andrew Yates | Apache-2.0
import Init

/-! Conservative source fence for the current physical-line directive processor.
A block-comment newline inside a directive cannot terminate that directive and
leak replacement tokens as ordinary C. Refuse that unsupported logical-line
case before the declaration lexer. Multiline comment prefixes remain supported.
# away from logical beginning-of-line also refuses: a comment newline must not
manufacture a new directive. This does not implement full C translation phases. -/
namespace C11DirectiveLines
inductive Mode where
  | normal | slash | line | block | star
  deriving DecidableEq, BEq, Repr
structure State where
  mode : Mode := .normal
  beginning : Bool := true
  directive : Bool := false
  deriving DecidableEq, BEq, Repr

def initial : State := {}
private def white (char : Char) : Bool := char == ' ' || char == '\t' || char == '\x0b' || char == '\x0c'

def step (state : State) (char : Char) : Option State :=
  if char == '\\' || char == '?' || char == '\r' || char == '\x00' then none else
  match state.mode with
  | .normal =>
      if char == '\n' then some initial
      else if white char then some state
      else if char == '/' then some { state with mode := .slash }
      else if char == '#' then
        if state.beginning then some { state with beginning := false, directive := true } else none
      else some { state with beginning := false }
  | .slash =>
      if char == '*' then some { state with mode := .block }
      else if char == '/' then some { state with mode := .line } else none
  | .line => if char == '\n' then some initial else some state
  | .block =>
      if char == '\n' && state.directive then none
      else if char == '*' then some { state with mode := .star } else some state
  | .star =>
      if char == '\n' && state.directive then none
      else if char == '/' then some { state with mode := .normal }
      else if char == '*' then some state else some { state with mode := .block }

def feed (state : Option State) (chars : List Char) : Option State :=
  chars.foldl (fun state char => state.bind (fun state => step state char)) state

def finish : Option State → Bool
  | none => false
  | some state => state.mode == .normal || state.mode == .line

def supportedCharacters (chars : List Char) : Bool := finish (feed (some initial) chars)
def supported (source : String) : Bool := supportedCharacters source.toList

def supportedChunks (chunks : List (List Char)) : Bool := finish (chunks.foldl feed (some initial))

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
    supportedChunks chunks = supportedCharacters chunks.flatten := by
  unfold supportedChunks supportedCharacters
  rw [feed_chunks]

theorem directive_comment_newline_refused : supported "#define X /*\n*/ replacement\n" = false := by rfl

theorem ordinary_multiline_prefix_supported : supported "/* license\n prefix */\n#ifndef X\n#endif\n" = true := by rfl

theorem comment_cannot_manufacture_directive : supported "ordinary /*\n*/ #define X 1\n" = false := by rfl

theorem single_line_directive_comment_supported : supported "#define X /* comment */ replacement\n" = true := by rfl
end C11DirectiveLines
