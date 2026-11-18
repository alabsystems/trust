-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderDeclarations

/-! Source-parsed preprocessing condition slice: defined, decimal signed-intmax
constants (optionally L/LL), !, && and comparisons. No caller Boolean selects a
branch. All macro references are resolved BEFORE evaluation, even on a false
&& arm; unsupported expansion/function syntax never hides behind short circuit.
This is not a full preprocessor or proof of actual target/predefined context.
Nonnegative values below 2^63 need no signed/unsigned mixing or overflow rule.
Other literal/operator/extension families refuse rather than guess. -/
namespace C11PPConditions
open C11HeaderDeclarations
inductive Comparison where
  | lt | le | gt | ge | ne
  deriving DecidableEq, BEq, Repr
inductive Expr where
  | number (value : Nat)
  | defined (name : String)
  | identifier (name : String)
  | not (operand : Expr)
  | and (left right : Expr)
  | compare (operation : Comparison) (left right : Expr)
  deriving DecidableEq, BEq, Repr
private def identifier (token : String) : Bool :=
  token != "_Pragma" && token != "__VA_ARGS__" &&
    C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes token) []

def number (token : String) : Option Nat := do
  let chars := token.toList
  let chars := match chars.reverse with
    | 'L' :: 'L' :: rest | 'l' :: 'l' :: rest => rest.reverse
    | 'L' :: rest | 'l' :: rest => rest.reverse
    | _ => chars
  if chars.isEmpty || (chars.length > 1 && chars.head? == some '0') then none else
    chars.foldlM (fun value char =>
      if '0' ≤ char && char ≤ '9' then
        let value := value * 10 + char.toNat - '0'.toNat
        if value < 9223372036854775808 then some value else none
      else none) 0

private inductive Task where
  | atom
  | expression (minimum : Nat)
  | continuation (minimum : Nat) (left : Expr)

private def binary : String → Option (Nat × Option Comparison)
  | "&&" => some (1, none)
  | "<" => some (3, some .lt)
  | "<=" => some (3, some .le)
  | ">" => some (3, some .gt)
  | ">=" => some (3, some .ge)
  | "!=" => some (2, some .ne)
  | _ => none

/-- One explicit descending fuel recursion avoids a mutually recursive parser
whose compiled equation machinery obscures the bounded parsing cost. -/
private def parseTask : Nat → Task → List String → Option (Expr × List String)
  | 0, _, _ => none
  | fuel + 1, task, tokens => match task with
    | .atom => match tokens with
      | "!" :: rest => do
          let (value, rest) ← parseTask fuel .atom rest
          return (.not value, rest)
      | "(" :: rest => do
          let (value, rest) ← parseTask fuel (.expression 1) rest
          let ")" :: rest := rest | none
          return (value, rest)
      | "defined" :: "(" :: name :: ")" :: rest =>
          if identifier name then some (.defined name, rest) else none
      | "defined" :: name :: rest =>
          if identifier name then some (.defined name, rest) else none
      | "defined" :: _ => none
      | token :: rest => match number token with
          | some value => some (.number value, rest)
          | none => if identifier token then some (.identifier token, rest) else none
      | [] => none
    | .expression minimum => do
        let (left, rest) ← parseTask fuel .atom tokens
        parseTask fuel (.continuation minimum left) rest
    | .continuation minimum left =>
        match tokens with
        | token :: rest => match binary token with
          | some (precedence, operation) =>
              if precedence < minimum then some (left, tokens) else do
                let (right, rest) ← parseTask fuel (.expression (precedence + 1)) rest
                let result := match operation with
                  | none => Expr.and left right
                  | some operation => Expr.compare operation left right
                parseTask fuel (.continuation minimum result) rest
          | none => some (left, tokens)
        | [] => some (left, [])

def parseTokens (tokens : List String) : Option Expr := do
  let (expression, rest) ← parseTask 64 (.expression 1) tokens
  if rest.isEmpty then some expression else none

def parse (source : String) : Option Expr := do
  let tokens ← CAtomicDropSyntax.tokenize source.toUTF8.data.toList
  parseTokens tokens

/-- Defined values are unique and scalar, not arbitrary type/meaning advice.
Complex replacement expressions and cycles refuse instead of inserting hidden
parentheses or changing source precedence. Undefined identifiers become 0. -/
def identifierValue : Nat → Bindings → String → Option Nat
  | 0, _, _ => none
  | fuel + 1, context, name =>
    match context.macros.filter (fun entry => entry.1 == name) with
    | [] => some 0
    | [(_, [token])] => match number token with
        | some value => some value
        | none => if identifier token && token != "defined" then identifierValue fuel context token else none
    | _ => none

inductive Resolved where
  | number (value : Nat)
  | not (operand : Resolved)
  | and (left right : Resolved)
  | compare (operation : Comparison) (left right : Resolved)
  deriving DecidableEq, BEq, Repr

def resolve (context : Bindings) : Expr → Option Resolved
  | .number value => some (.number value)
  | .defined name =>
      if (context.macros.filter (fun entry => entry.1 == name)).length > 1 then none
      else some (.number (if context.macros.any (fun entry => entry.1 == name) then 1 else 0))
  | .identifier name => do return .number (← identifierValue 64 context name)
  | .not operand => do return .not (← resolve context operand)
  | .and left right => do
      let left ← resolve context left
      let right ← resolve context right
      return .and left right
  | .compare operation left right => do return .compare operation (← resolve context left) (← resolve context right)

def evaluate : Resolved → Nat
  | .number value => value
  | .not value => if evaluate value == 0 then 1 else 0
  | .and left right => if evaluate left == 0 then 0 else if evaluate right == 0 then 0 else 1
  | .compare operation left right =>
      let left := evaluate left; let right := evaluate right
      let result : Bool := match operation with
        | .lt => decide (left < right) | .le => decide (left ≤ right) | .gt => decide (left > right)
        | .ge => decide (left ≥ right) | .ne => left != right
      if result then 1 else 0

def decideSource (context : Bindings) (source : String) : Option Bool := do
  let expression ← parse source
  let expression ← resolve context expression
  return evaluate expression != 0

end C11PPConditions
