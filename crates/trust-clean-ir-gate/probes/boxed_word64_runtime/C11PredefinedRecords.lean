-- Copyright 2026 Andrew Yates | Apache-2.0
import C11PPConditions

/-! Complete-line DATA reader for a captured -dM macro inventory. Every line
is consumed and all replacement bytes retained, including unimplemented ones.
Some frontend builtin operators can be defined without appearing in -dM.
Consequently absence below is ONLY inventory absence, not actual-world
undefinedness. A separate complete frontend/dialect association is required.
This is not a preprocessor/parser for arbitrary macro definitions, nor evidence
that a tool's claimed predefined environment/target is authentic. Object-body
meaning is checked lazily by the supported condition reader, not inferred from
its name. Function-like bodies remain opaque and cannot become object values. -/
namespace C11PredefinedRecords
structure Record where
  name : String
  functionLike : Bool
  tail : String
  deriving DecidableEq, BEq, Repr

private def word (char : Char) : Bool :=
  char == '_' || ('a' ≤ char && char ≤ 'z') || ('A' ≤ char && char ≤ 'Z') || ('0' ≤ char && char ≤ '9')
private def identifier (name : String) : Bool :=
  name != "_Pragma" && name != "__VA_ARGS__" &&
    C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) []

/-- Exactly the physical-line observation format, not arbitrary C directives.
The complete tail is DATA; no function parameter/body semantics is granted. -/
def parseLine (line : String) : Option Record := do
  let chars := line.toList
  let '#' :: 'd' :: 'e' :: 'f' :: 'i' :: 'n' :: 'e' :: ' ' :: rest := chars | none
  let name := String.ofList (rest.takeWhile word)
  let tail := rest.dropWhile word
  if !identifier name || tail.contains '\n' || tail.contains '\r' || tail.contains '\x00' then none else
    match tail with
    | [] => some { name := name, functionLike := false, tail := "" }
    | '(' :: _ => some { name := name, functionLike := true, tail := String.ofList tail }
    | ' ' :: rest => some { name := name, functionLike := false, tail := String.ofList rest }
    | _ => none

/-- The captured inventory's strict ASCII ordering gives an adjacent checked
uniqueness rule without trusting a producer's map or silently sorting input. -/
def before : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then before as bs else a.toNat < b.toNat

def insert (records : List Record) (line : String) : Option (List Record) := do
  let record ← parseLine line
  match records with
  | previous :: _ =>
      if before previous.name.toList record.name.toList then some (record :: records) else none
  | [] => some [record]

structure Scan where
  pending : List Char := []
  reversed : List Record := []
  deriving Repr

def scanStep (state : Scan) (char : Char) : Option Scan :=
  if char == '\n' then do
    let records ← insert state.reversed (String.ofList state.pending.reverse)
    return { pending := [], reversed := records }
  else some { state with pending := char :: state.pending }

def feed (state : Option Scan) (chars : List Char) : Option Scan :=
  chars.foldl (fun state char => state.bind (fun state => scanStep state char)) state

def finish (state : Option Scan) : Option (List Record) := do
  let state ← state
  if state.pending.isEmpty then some state.reversed.reverse else none

/-- Physical lines are consumed in full, including the final LF. Blank,
unknown, duplicate or noncanonical-order records refuse, never disappear. -/
def parse (source : String) : Option (List Record) := finish (feed (some {}) source.toList)

def parseChunks (chunks : List (List Char)) : Option (List Record) :=
  finish (chunks.foldl feed (some {}))

theorem feed_append (state : Option Scan) (a b : List Char) :
    feed state (a ++ b) = feed (feed state a) b := by exact List.foldl_append

theorem feed_chunks (chunks : List (List Char)) (state : Option Scan) :
    chunks.foldl feed state = feed state chunks.flatten := by
  induction chunks generalizing state with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldl_cons, List.flatten_cons]
    rw [ih, feed_append]

theorem chunks_exact (chunks : List (List Char)) :
    parseChunks chunks = finish (feed (some {}) chunks.flatten) := by
  unfold parseChunks
  rw [feed_chunks]

def lookup (records : List Record) (name : String) : Option (Option Record) :=
  match records.filter (fun record => record.name == name) with
  | [] => some none
  | [record] => some (some record)
  | _ => none

/-- A bare function-macro identifier is not invoked and becomes 0 in #if.
A reached object replacement must be exactly one supported scalar/alias token;
unsupported strings/operators/recursive replacement still refuse. -/
def value : Nat → List Record → String → Option Nat
  | 0, _, _ => none
  | fuel + 1, records, name => do
    if !identifier name || name == "defined" then none else
      match ← lookup records name with
      | none => some 0
      | some record =>
        if record.functionLike then some 0 else do
          let [token] ← CAtomicDropSyntax.tokenize record.tail.toUTF8.data.toList | none
          match C11PPConditions.number token with
          | some result => some result
          | none => value fuel records token

def resolve (records : List Record) : C11PPConditions.Expr → Option C11PPConditions.Resolved
  | .number n => some (.number n)
  | .defined name => do
      let record ← lookup records name
      return .number (if record.isSome then 1 else 0)
  | .identifier name => do return .number (← value 64 records name)
  | .not operand => do return .not (← resolve records operand)
  | .and left right => do return .and (← resolve records left) (← resolve records right)
  | .compare operation left right => do return .compare operation (← resolve records left) (← resolve records right)

def decideCaptured (source condition : String) : Option Bool := do
  let records ← parse source
  let expression ← C11PPConditions.parse condition
  let resolved ← resolve records expression
  return C11PPConditions.evaluate resolved != 0

theorem version_lookup_from_complete_records :
    decideCaptured "#define __STDC_VERSION__ 201112L\n#define unused unsupported + body\n"
      "defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L" = some true := by rfl

theorem omitted_final_newline_refused : parse "#define x 1" = none := by rfl

theorem duplicate_record_refused : parse "#define x 1\n#define x 2\n" = none := by rfl

theorem noncanonical_order_refused : parse "#define z 1\n#define a 2\n" = none := by rfl

theorem nonrecord_cannot_be_ignored : parse "#define x 1\nnot a record\n" = none := by rfl

theorem unused_tail_retained :
    parseLine "#define unused unsupported + body" =
      some { name := "unused", functionLike := false, tail := "unsupported + body" } := by rfl

theorem reached_unsupported_tail_refused :
    decideCaptured "#define x unsupported + body\n" "x" = none := by rfl

theorem function_macro_not_object_value :
    decideCaptured "#define f(x) 1\n" "f" = some false := by rfl

theorem function_presence_is_not_value_truth :
    decideCaptured "#define f(x) 1\n" "defined(f)" = some true := by rfl
end C11PredefinedRecords
