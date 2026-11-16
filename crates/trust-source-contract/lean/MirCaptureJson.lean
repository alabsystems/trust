/- Copyright 2026 Andrew Yates. Apache-2.0.
   Total bounded reader of the existing capture JSON integer/string fragment.
   No partial Json.parse, native_decide, external decoder or source authority.
-/
namespace TrustMirCaptureJson
set_option maxRecDepth 10000
inductive J where
  | null
  | bool (value : Bool)
  | int (value : Int)
  | str (value : String)
  | arr (values : List J)
  | obj (fields : List (String × J))
abbrev Parsed := Except String (J × List Char)

def white (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'
def ws : List Char → List Char
  | [] => []
  | c::rest => if white c then ws rest else c::rest

def stringCore : Nat → List Char → List Char → Except String (String × List Char)
  | 0, _, _ => .error "string work bound"
  | _+1, [], _ => .error "unterminated string"
  | fuel+1, c::rest, acc =>
    if c == '"' then .ok (String.ofList acc.reverse,rest)
    else if c == '\\' then
      match rest with
      | [] => .error "unterminated escape"
      | e::tail =>
        let decoded := if e == '"' then some '"' else if e == '\\' then some '\\'
          else if e == '/' then some '/' else if e == 'n' then some '\n'
          else if e == 'r' then some '\r' else if e == 't' then some '\t'
          else if e == 'b' then some (Char.ofNat 8) else if e == 'f' then some (Char.ofNat 12)
          else none
        match decoded with
        | none => .error "unsupported or invalid string escape"
        | some d => stringCore fuel tail (d::acc)
    else if c.toNat < 32 then .error "unescaped control character"
    else stringCore fuel rest (c::acc)

def string (xs : List Char) : Except String (String × List Char) :=
  match xs with
  | '"'::rest => stringCore 4097 rest []
  | _ => .error "expected string"
def digit (c : Char) : Bool := decide ('0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat)
def digits : Nat → List Char → Nat → Except String (Nat × List Char)
  | 0, _, _ => .error "integer work bound"
  | fuel+1, c::rest, n => if digit c then digits fuel rest (10*n+c.toNat-'0'.toNat) else .ok (n,c::rest)
  | _+1, [], n => .ok (n,[])
def number (negative : Bool) (xs : List Char) : Parsed := do
  let (n,rest) ← match xs with
    | [] => .error "missing integer"
    | c::tail =>
      if !digit c then .error "expected integer"
      else if c == '0' then
        match tail with
        | d::_ => if digit d then .error "leading zero" else .ok (0,tail)
        | [] => .ok (0,[])
      else digits 128 tail (c.toNat-'0'.toNat)
  match rest with
  | '.'::_ | 'e'::_ | 'E'::_ => .error "unsupported non-integer number"
  | _ => .ok (.int (if negative then -(n:Int) else (n:Int)),rest)

inductive Frame where
  | array (values : List J) (first : Bool)
  | objectValue (key : String) (fields : List (String × J))
inductive Task where
  | value
  | key (fields : List (String × J)) (first : Bool)
  | completed (value : J)

/-- One structural recursion, with explicit syntax stack. Unlike a mutually
    recursive parser pack this does not expand unused fuel branches in proofs. -/
def loop : Nat → List Char → List Frame → Task → Except String J
  | 0, _, _, _ => .error "JSON work bound"
  | fuel+1, input, stack, task => do
    let xs := ws input
    match task with
    | .value =>
      match xs with
      | [] => throw "missing JSON value"
      | ']'::rest =>
        match stack with
        | .array [] true :: tail => loop fuel rest tail (.completed (.arr []))
        | _ => throw "unexpected array end"
      | '['::rest =>
        if 128 ≤ stack.length then throw "JSON depth bound"
        loop fuel rest (.array [] true :: stack) .value
      | '{'::rest =>
        if 128 ≤ stack.length then throw "JSON depth bound"
        loop fuel rest stack (.key [] true)
      | 'n'::'u'::'l'::'l'::rest => loop fuel rest stack (.completed .null)
      | 't'::'r'::'u'::'e'::rest => loop fuel rest stack (.completed (.bool true))
      | 'f'::'a'::'l'::'s'::'e'::rest => loop fuel rest stack (.completed (.bool false))
      | '"'::_ => do let (v,rest) ← string xs; loop fuel rest stack (.completed (.str v))
      | '-'::rest => do let (v,tail) ← number true rest; loop fuel tail stack (.completed v)
      | c::_ =>
        if !digit c then throw "invalid JSON token"
        let (v,rest) ← number false xs
        loop fuel rest stack (.completed v)
    | .key fields first =>
      match xs with
      | '}'::rest =>
        if first then loop fuel rest stack (.completed (.obj [])) else throw "trailing object comma"
      | _ =>
        if 256 ≤ fields.length then throw "object field bound"
        let (key,rest) ← string xs
        if 256 < key.length then throw "object key bound"
        if fields.any (fun p => p.1 == key) then throw "duplicate object key"
        let tail ← match ws rest with
          | ':'::tail => pure tail
          | _ => throw "expected object colon"
        loop fuel tail (.objectValue key fields :: stack) .value
    | .completed v =>
      match stack with
      | [] => if xs.isEmpty then pure v else throw "trailing JSON bytes"
      | .array acc _ :: parent =>
        match xs with
        | ','::rest => loop fuel rest (.array (v::acc) false :: parent) .value
        | ']'::rest => loop fuel rest parent (.completed (.arr (v::acc).reverse))
        | _ => throw "expected array comma/end"
      | .objectValue key fields :: parent =>
        match xs with
        | ','::rest => loop fuel rest parent (.key ((key,v)::fields) false)
        | '}'::rest => loop fuel rest parent (.completed (.obj ((key,v)::fields).reverse))
        | _ => throw "expected object comma/end"

def parseChars (input : List Char) : Except String J := do
  if 65536 < input.length then throw "capture character bound"
  loop (4*input.length+1) input [] .value

def parse (input : String) : Except String J := do
  if 65536 < input.length then throw "capture character bound"
  parseChars input.toList

example : parse "{\"a\":1,\"a\":2}" = .error "duplicate object key" := rfl
example : parse "[0,]" = .error "unexpected array end" := rfl
example : parse "01" = .error "leading zero" := rfl
example : parse "1e2" = .error "unsupported non-integer number" := rfl
example : parse "truex" = .error "trailing JSON bytes" := rfl
example : parse "{\"\\/\":0,\"/\":1}" = .error "duplicate object key" := rfl
example : loop 0 [] [] .value = .error "JSON work bound" := rfl
example : loop 1 ['['] (List.replicate 128 (.array [] true)) .value = .error "JSON depth bound" := rfl
example : stringCore 0 [] [] = .error "string work bound" := rfl
example : digits 0 [] 0 = .error "integer work bound" := rfl
end TrustMirCaptureJson
