-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderTyping
import C11HeaderParser
import C11DeclarationLexer

/-! Complete-token C declaration/macro parsing and nominal field binding.
These functions derive types/aliases from typeSyntax, not producer type annotations.
They do not certify include/conditional/undef order or a complete actual TU.
Primitive C target widths and compiler-builtin meanings remain separate owners.
In particular an object-like macro naming __c11_atomic_load is only an alias,
NOT an intrinsic-semantics license. -/
namespace C11HeaderDeclarations
open C11HeaderTyping
inductive TypeSyntax where
  | builtin (type : CType)
  | named (name : String)
  | record (tag : String)
  | pointer (base : TypeSyntax)
  | atomic (base : TypeSyntax)
  | flexibleArray (base : TypeSyntax)
  deriving DecidableEq, BEq, Repr
structure Field where
  name : String
  type : TypeSyntax
  deriving DecidableEq, BEq, Repr
inductive Declaration where
  | alias (name : String) (type : TypeSyntax)
  | recordAlias (tag alias : String) (fields : List Field)
  | objectMacro (name : String) (replacement : List String)
  deriving DecidableEq, BEq, Repr

/-- No unknown declaration is accepted by treating its first word as a type. -/
def parseBase : Nat → List String → Option (TypeSyntax × List String)
  | 0, _ => none
  | fuel + 1, input =>
    match input with
    | "unsigned" :: "int" :: rest => some (.builtin .cUInt, rest)
    | "unsigned" :: "char" :: rest => some (.builtin .cUChar, rest)
    | "unsigned" :: "short" :: rest => some (.builtin .cUShort, rest)
    | "int" :: rest => some (.builtin .cInt, rest)
    | "_Bool" :: rest => some (.builtin .cBool, rest)
    | "void" :: rest => some (.builtin .unit, rest)
    | "struct" :: tag :: rest =>
        if C11HeaderParser.identifier tag then some (.record tag, rest) else none
    | "_Atomic" :: rest => do
        let (base, rest) ← parseBase fuel rest
        return (.atomic base, rest)
    | name :: rest =>
        if C11HeaderParser.identifier name then some (.named name, rest) else none
    | [] => none

def parsePointers : Nat → TypeSyntax → List String → Option (TypeSyntax × List String)
  | 0, _, _ => none
  | fuel + 1, base, "*" :: rest => parsePointers fuel (.pointer base) rest
  | _ + 1, base, rest => some (base, rest)

def parseType (fuel : Nat) (input : List String) : Option (TypeSyntax × List String) := do
  let (base, rest) ← parseBase fuel input
  parsePointers fuel base rest

def parseFields : Nat → List String → Option (List Field × List String)
  | 0, _ => none
  | _ + 1, "}" :: rest => some ([], rest)
  | fuel + 1, input => do
      let (base, rest) ← parseType (fuel + 1) input
      let name :: rest := rest | none
      if !C11HeaderParser.identifier name then none else do
        let (type, rest) ← match rest with
          | "[" :: "]" :: ";" :: rest => some (.flexibleArray base, rest)
          | ";" :: rest => some (base, rest)
          | _ => none
        let (tail, rest) ← parseFields fuel rest
        if tail.any (fun field => field.name == name) then none
        else return ({ name := name, type := type } :: tail, rest)

def parseDeclaration (fuel : Nat) (tokens : List String) : Option Declaration := do
  match tokens with
  | "typedef" :: "struct" :: tag :: "{" :: rest =>
      if !C11HeaderParser.identifier tag then none else do
        let (fields, rest) ← parseFields fuel rest
        let [alias, ";"] := rest | none
        if C11HeaderParser.identifier alias && !fields.isEmpty then some (.recordAlias tag alias fields) else none
  | "typedef" :: rest =>
      let (type, rest) ← parseType fuel rest
      let [alias, ";"] := rest | none
      if C11HeaderParser.identifier alias then some (.alias alias type) else none
  | "#" :: "define" :: name :: replacement =>
      if C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) [] && !replacement.isEmpty && replacement.head? != some "("
      then some (.objectMacro name replacement) else none
  | _ => none

/-- Newline retention is mandatory for directives: a second directive or a
continued/redefined macro cannot be swallowed as replacement advice. -/
def parseComplete (fuel : Nat) (source : String) : Option Declaration := do
  let tokens ← C11DeclarationLexer.tokenize source
  if tokens.head? == some "#" then
    if tokens.getLast? != some "\n" || (source.toList.filter (· == '\n')).length != 1 then none else
      let tokens := tokens.dropLast
      if tokens.contains "\n" then none else parseDeclaration fuel tokens
  else parseDeclaration fuel (tokens.filter (· != "\n"))

structure Bindings where
  aliases : List (String × CType) := []
  records : List (String × List (String × CType)) := []
  macros : List (String × List String) := []
  deriving Repr

def resolve : Nat → Bindings → TypeSyntax → Option CType
  | 0, _, _ => none
  | fuel + 1, bindings, typeSyntax =>
    match typeSyntax with
    | .builtin type =>
        if type == .cInt || type == .cUInt || type == .cBool || type == .cUChar || type == .cUShort || type == .unit
        then some type else none
    | .named name => uniqueLookup name bindings.aliases
    | .record tag => do
        let _ ← uniqueLookup tag bindings.records
        return .record tag
    | .pointer (.record tag) =>
        -- A pointer to an incomplete self-record is legal C, not a body/type grant.
        some (.pointer (.record tag))
    | .pointer base => do return .pointer (← resolve fuel bindings base)
    | .atomic base => do
        let base ← resolve fuel bindings base
        if base == .cInt || base == .cUInt || base == .cUChar || base == .cUShort || base == .cBool
        then some (.atomic base) else none
    | .flexibleArray base => do return .flexibleArray (← resolve fuel bindings base)

/-- C11 flexible members must be last, with at least one other named member.
Void and records containing flexible members cannot be embedded as fields. -/
def embeddable (bindings : Bindings) : CType → Bool
  | .unit | .flexibleArray _ => false
  | .record tag => match uniqueLookup tag bindings.records with
      | none => false
      | some fields => !fields.any (fun field => match field.2 with | .flexibleArray _ => true | _ => false)
  | _ => true

def fieldsValid (bindings : Bindings) (fields : List (String × CType)) : Bool :=
  !fields.isEmpty && fields.zipIdx.all (fun (field, index) =>
    C11HeaderParser.identifier field.1 && match field.2 with
    | .flexibleArray base => index + 1 == fields.length && 0 < index && embeddable bindings base
    | type => embeddable bindings type)

def install (fuel : Nat) (bindings : Bindings) (declaration : Declaration) : Option Bindings := do
  match declaration with
  | .alias name typeSyntax =>
      if !C11HeaderParser.identifier name || bindings.aliases.any (fun item => item.1 == name) then none else do
        let type ← resolve fuel bindings typeSyntax
        return { bindings with aliases := bindings.aliases ++ [(name, type)] }
  | .objectMacro name replacement =>
      if !C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) [] || replacement.isEmpty || replacement.head? == some "(" || bindings.macros.any (fun item => item.1 == name) then none
      else return { bindings with macros := bindings.macros ++ [(name, replacement)] }
  | .recordAlias tag alias fields =>
      if !C11HeaderParser.identifier tag || !C11HeaderParser.identifier alias || bindings.records.any (fun item => item.1 == tag) ||
          bindings.aliases.any (fun item => item.1 == alias) then none else do
        let resolved ← fields.mapM (fun field => do return (field.name, ← resolve fuel bindings field.type))
        if !fieldsValid bindings resolved || (resolved.map (·.1)).eraseDups.length != resolved.length then none else
        return { bindings with records := bindings.records ++ [(tag, resolved)], aliases := bindings.aliases ++ [(alias, .record tag)] }

def fieldType (bindings : Bindings) (record field : String) : Option CType := do
  let fields ← uniqueLookup record bindings.records
  uniqueLookup field fields

/-- Restricted object-like macro expansion. Unsupported #/##, ambiguous
bindings and recursive/fuel-exhausted advice refuse. No builtin is interpreted
by spelling; an alias target remains an ordinary token. -/
def expandObjects : Nat → Bindings → List String → Option (List String)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | fuel + 1, bindings, token :: tail => do
      if token == "#" || token == "##" then none else do
        let head ← match bindings.macros.filter (fun item => item.1 == token) with
          | [] => some [token]
          | [(_, replacement)] => expandObjects fuel bindings replacement
          | _ => none
        let tail ← expandObjects fuel bindings tail
        return head ++ tail

/-- Source member lookup derives a nominal atomic-pointer type only; there is
no byte offset, object-layout, builtin-role or ownership inference here. -/
def bindAtomicMember (bindings : Bindings) (objectAlias outer inner : String) : Option CType := do
  let .record objectTag ← uniqueLookup objectAlias bindings.aliases | none
  let .record headerTag ← fieldType bindings objectTag outer | none
  let .atomic .cUInt ← fieldType bindings headerTag inner | none
  return .pointer (.atomic .cUInt)

/-- An alias to a builtin-looking token never installs a function signature or
an execution role. Ordinary source aliases cannot certify intrinsic meaning. -/
theorem macro_only_stores_tokens (bindings : Bindings) (name : String) (body : List String)
    (validName : C11OrdinaryTokens.valid .identifier (C11OrdinaryTokens.bytes name) [] = true)
    (nonempty : body.isEmpty = false) (notFunction : (body.head? == some "(") = false)
    (fresh : bindings.macros.any (fun item => item.1 == name) = false) :
    install fuel bindings (.objectMacro name body) =
      some { bindings with macros := bindings.macros ++ [(name, body)] } := by
  simp [install, fresh, validName, nonempty, notFunction]
end C11HeaderDeclarations
