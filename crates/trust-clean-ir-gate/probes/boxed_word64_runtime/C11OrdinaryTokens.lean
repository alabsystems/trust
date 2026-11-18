-- Copyright 2026 Andrew Yates | Apache-2.0
import Init

/-!
Restricted ordinary-fragment preprocessing-token grammar, corresponding to
WG14 N1570 §§6.4, 6.4.2.1, 6.4.6, 6.4.8. It handles ASCII identifiers, the
actual literals 0/1 and punctuators, with maximal munch. Directive/header-name
contexts, comments, strings, other numbers and encodings are unsupported here;
this is not a whole-TU parser/typechecker or a C11 execution relation.
-/
namespace C11OrdinaryTokens

def bytes (text : String) : List UInt8 := text.toUTF8.data.toList
private def letter (b : UInt8) : Bool :=
  (97 ≤ b.toNat && b.toNat ≤ 122) || (65 ≤ b.toNat && b.toNat ≤ 90) || b == 95
private def digit (b : UInt8) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57
private def identifierRest (b : UInt8) : Bool := letter b || digit b

def white (b : UInt8) : Bool := b == 9 || b == 10 || b == 32

def punctuators : List (List UInt8) :=
  ["[", "]", "(", ")", "{", "}", ".", "->", "++", "--", "&", "*", "+", "-", "~", "!",
   "/", "%", "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "^", "|", "&&", "||",
   "?", ":", ";", "...", "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|=",
   ",", "#", "##", "<:", ":>", "<%", "%>", "%:", "%:%:"].map bytes

private def isPrefix : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefix as bs

inductive Kind where
  | identifier | integer01 | punctuator
  deriving DecidableEq, Repr

/-- Every longer punctuation alternative is checked, not just the intended
operator. Dot-number and comment openers also take precedence over punctuation. -/
def valid (kind : Kind) (token rest : List UInt8) : Bool :=
  match kind with
  | .identifier => match token with
    | [] => false
    | a :: tail => letter a && tail.all identifierRest &&
        (match rest with | [] => true | b :: _ => !identifierRest b)
  | .integer01 => (token == [48] || token == [49]) &&
      (match rest with | [] => true | b :: _ => !(identifierRest b || b == 46))
  | .punctuator => punctuators.contains token &&
      -- Ordinary function fragments do not establish directive/header contexts.
      !(token == [35] || token == [35,35] || token == [37,58] || token == [37,58,37,58]) &&
      punctuators.all (fun other => decide (other.length ≤ token.length) ||
        !isPrefix other (token ++ rest)) &&
      !(token == [46] && (match rest with | b :: _ => digit b | [] => false)) &&
      !(token == [47] && (match rest with | b :: _ => b == 47 || b == 42 | [] => false))

/-- This is an independent, complete-consumption grammar judgment. The token
kind/boundary conditions are checked separately from the streaming lexer. -/
inductive Lexes : List UInt8 → List String → Prop where
  | done : Lexes [] []
  | whitespace (space rest : List UInt8) (tokens : List String) :
      space.all white = true → Lexes rest tokens → Lexes (space ++ rest) tokens
  | token (kind : Kind) (text : String) (rest : List UInt8) (tokens : List String) :
      valid kind (bytes text) rest = true → Lexes rest tokens →
      Lexes (bytes text ++ rest) (text :: tokens)

/-- A short identifier prefix cannot split a longer identifier. -/
theorem no_identifier_prefix_split : valid .identifier (bytes "atomic") (bytes "_load") = false := by decide
/-- The preprocessing-number maximal-munch rule also prevents 1 + Ex splitting. -/
theorem no_number_prefix_split : valid .integer01 (bytes "1") (bytes "Ex") = false := by decide
/-- A > token cannot hide the second character of >=. -/
theorem no_short_punctuator_split : valid .punctuator (bytes ">") (bytes "= x") = false := by decide
/-- This grammar does not misclassify a comment opener as division. -/
theorem no_comment_as_division : valid .punctuator (bytes "/") (bytes "*x*/") = false := by decide
/-- Nor may a . token split a preprocessing number starting with a dot. -/
theorem no_dot_number_split : valid .punctuator (bytes ".") (bytes "1") = false := by decide

#print axioms no_short_punctuator_split
#print axioms no_comment_as_division
end C11OrdinaryTokens
