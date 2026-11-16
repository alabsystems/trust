-- SpecrPrelude.lean — HAND-AUTHORED runtime for the specr → Clean translator, v2
-- (RM1 of Trust docs/plans/2026-10-15-proven-core.md; v1 was the K8 probe's,
-- reports/2026-09-17-phase0-k8-specr/translator/SpecrPrelude.lean).
--
-- This file plays the role libspecr plays for specr-transpile: it gives
-- MiniRust's meta-language (specr lang) its primitive types and operations.
-- It is NOT generated and it is NOT part of the byte-compared output; it is
-- reviewed Clean source, and every definition below is exercised by the
-- conformance runs. Each operation cites the libspecr 0.1.41 function it
-- mirrors (the version MiniRust e8666821 pins in `mini`).
--
-- v2: `SOut` is a free monad. Its two choice nodes are the non-determinism of
-- specr, left unresolved in the generated code; both choose by an index:
--   pick k      demonic choice: `k j` continues with the distribution's j-th
--               candidate (libspecr `pick`; `SPick.choose` decodes the index)
--   predict k   angelic prediction: `k i` continues with the predicted type's
--               i-th candidate (libspecr `predict`; `SPredict.choose`)
-- An index past the candidates, or a candidate that fails its predicate,
-- continues as `reject`: that resolution is not a behaviour. An executable run
-- is one interpretation of the tree by an oracle: `SOut.runOracle (δ, π)` for
-- any oracle, and `SOut.runLeast`, K8's deterministic one (the least candidate
-- that passes its predicate). The relational semantics of `SOut` itself, and
-- core_wf / run_sound / run_ub / run_adequate for it, are TrustSem's (Clean
-- crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/trust_sem/TrustSem.lean),
-- which imports a byte-identical copy of this file and of the generated slice
-- (`regen.py check` compares the copies in the pinned first-party/clean).
--
-- The leaves of `SOut`:
--   ok a        normal result
--   panic m     a specr `panic!`/`unwrap`/`assert!`/index failure — a spec bug
--   fuel        a recursion or loop exceeded its fuel (observable, never silent)
--   refused w   the translator refused the construct `w`; reaching it is a result
--   nobehavior  an interpretation found no candidate among the first `bound` ones
--   reject      the candidate a choice node offered fails its predicate
-- specr's own `Result`/`Option`/`NdResult` values are ordinary data inside `ok`.
-- Nothing here is an axiom, a `sorry`, or an opaque constant.

/-- libspecr `IntDistribution` -/
structure SIntDistribution where
  start : Int
  «end» : Int
  divisor : Int

inductive SOut (α : Type) where
  | ok (a : α)
  | panic (msg : String)
  | fuel
  | refused (what : String)
  | nobehavior
  | reject
  | pick (k : Nat → SOut α)
  | predict (k : Nat → SOut α)

-- Recursion over `SOut` is written with its recursor `SOut.rec`: Clean's
-- elaborator (Clean cd92bac82) refuses a structurally recursive `match` through
-- a function-typed recursive argument (`k c`), and accepts the recursor.
def SOut.bind {α β : Type} (x : SOut α) (f : α → SOut β) : SOut β :=
  @SOut.rec α (fun _ => SOut β)
    (fun a => f a)
    (fun m => SOut.panic m)
    SOut.fuel
    (fun w => SOut.refused w)
    SOut.nobehavior
    SOut.reject
    (fun _ ih => SOut.pick ih)
    (fun _ ih => SOut.predict ih)
    x

/-- The interpretation by an oracle `(δ, π)` (TrustSem's `run` is this, step by
step): each oracle answers from the choices taken so far, oldest first. `δ`
names a `pick`'s candidate by its index and `π` a prediction's. A `reject` leaf
is a resolution that is not a behaviour. -/
def SOut.runOracle {α : Type} (δ π : List Nat → Nat) (x : SOut α) : SOut α :=
  @SOut.rec α (fun _ => (List Nat → Nat) → (List Nat → Nat) → SOut α)
    (fun a _ _ => SOut.ok a)
    (fun m _ _ => SOut.panic m)
    (fun _ _ => SOut.fuel)
    (fun w _ _ => SOut.refused w)
    (fun _ _ => SOut.nobehavior)
    (fun _ _ => SOut.reject)
    (fun _ ih dl pl => ih (dl []) (fun h => dl (dl [] :: h)) (fun h => pl (dl [] :: h)))
    (fun _ ih dl pl => ih (pl []) (fun h => dl (pl [] :: h)) (fun h => pl (pl [] :: h)))
    x δ π

/-- specr `Result<T, E>` (std) and `NdResult<T>` (the non-determinism is resolved
by the oracle, so both are the same data). -/
inductive SRes (ε α : Type) where
  | ok (a : α)
  | err (e : ε)

inductive SOrdering where
  | less
  | equal
  | greater

-- libspecr enums (signedness.rs, mutability.rs, endianness.rs). The translator
-- registers them as ADTs for typing and patterns and does not re-emit them.
inductive MR_Signedness where
  | Signed
  | Unsigned

inductive MR_Mutability where
  | Mutable
  | Immutable

inductive MR_Endianness where
  | LittleEndian
  | BigEndian

def MR_Signedness.beq (a b : MR_Signedness) : Bool :=
  match a with
  | MR_Signedness.Signed => (match b with | MR_Signedness.Signed => true | _ => false)
  | MR_Signedness.Unsigned => (match b with | MR_Signedness.Unsigned => true | _ => false)

def MR_Mutability.beq (a b : MR_Mutability) : Bool :=
  match a with
  | MR_Mutability.Mutable => (match b with | MR_Mutability.Mutable => true | _ => false)
  | MR_Mutability.Immutable => (match b with | MR_Mutability.Immutable => true | _ => false)

def MR_Endianness.beq (a b : MR_Endianness) : Bool :=
  match a with
  | MR_Endianness.LittleEndian => (match b with | MR_Endianness.LittleEndian => true | _ => false)
  | MR_Endianness.BigEndian => (match b with | MR_Endianness.BigEndian => true | _ => false)

def MR_Signedness.debugName (a : MR_Signedness) : String :=
  match a with | MR_Signedness.Signed => "Signed" | MR_Signedness.Unsigned => "Unsigned"

def MR_Mutability.debugName (a : MR_Mutability) : String :=
  match a with | MR_Mutability.Mutable => "Mutable" | MR_Mutability.Immutable => "Immutable"

def MR_Endianness.debugName (a : MR_Endianness) : String :=
  match a with | MR_Endianness.LittleEndian => "LittleEndian" | MR_Endianness.BigEndian => "BigEndian"

-- ---------------------------------------------------------------- Bool / String
def SBool.beq (a b : Bool) : Bool :=
  match a with
  | true => b
  | false => match b with | true => false | false => true

def SBool.not (a : Bool) : Bool := match a with | true => false | false => true
def SBool.and (a b : Bool) : Bool := match a with | true => b | false => false
def SBool.or (a b : Bool) : Bool := match a with | true => true | false => b
def SBool.xor (a b : Bool) : Bool := match a with | true => SBool.not b | false => b
def SBool.cmp (a b : Bool) : SOrdering :=
  match a with
  | false => (match b with | false => SOrdering.equal | true => SOrdering.less)
  | true => (match b with | false => SOrdering.greater | true => SOrdering.equal)

def SString.beq (a b : String) : Bool := decide (a = b)

def SOrdering.beq (a b : SOrdering) : Bool :=
  match a with
  | SOrdering.less => (match b with | SOrdering.less => true | _ => false)
  | SOrdering.equal => (match b with | SOrdering.equal => true | _ => false)
  | SOrdering.greater => (match b with | SOrdering.greater => true | _ => false)

-- std::cmp::Ordering methods
def SOrdering.is_lt (o : SOrdering) : Bool := match o with | SOrdering.less => true | _ => false
def SOrdering.is_gt (o : SOrdering) : Bool := match o with | SOrdering.greater => true | _ => false
def SOrdering.is_eq (o : SOrdering) : Bool := match o with | SOrdering.equal => true | _ => false
def SOrdering.is_le (o : SOrdering) : Bool := SBool.not (SOrdering.is_gt o)
def SOrdering.is_ge (o : SOrdering) : Bool := SBool.not (SOrdering.is_lt o)
def SOrdering.is_ne (o : SOrdering) : Bool := SBool.not (SOrdering.is_eq o)
def SOrdering.then (o p : SOrdering) : SOrdering := match o with | SOrdering.equal => p | _ => o

-- ---------------------------------------------------------------- Int
-- All integer types of specr (Int, u8, usize, ...) and libspecr Size/Align are
-- carried as Lean `Int`; the translator keeps them apart for method dispatch.

def SInt.beq (a b : Int) : Bool := decide (a = b)
def SInt.blt (a b : Int) : Bool := decide (a < b)
def SInt.ble (a b : Int) : Bool := decide (a ≤ b)
def SInt.cmp (a b : Int) : SOrdering :=
  match SInt.blt a b with
  | true => SOrdering.less
  | false => (match SInt.beq a b with | true => SOrdering.equal | false => SOrdering.greater)
def SInt.min (a b : Int) : Int := match SInt.ble a b with | true => a | false => b
def SInt.max (a b : Int) : Int := match SInt.ble a b with | true => b | false => a

/-- magnitude as Nat -/
def SInt.abs (a : Int) : Nat :=
  match a with
  | Int.ofNat n => n
  | Int.negSucc n => n + 1

def SInt.isNeg (a : Int) : Bool :=
  match a with
  | Int.ofNat _ => false
  | Int.negSucc _ => true

def SInt.ofSignedNat (neg : Bool) (n : Nat) : Int :=
  match neg with
  | false => Int.ofNat n
  | true => -(Int.ofNat n)

/-- num-bigint `/` on BigInt: truncating division; panics on a zero divisor. -/
def SInt.div (a b : Int) : SOut Int :=
  match SInt.beq b 0 with
  | true => SOut.panic "attempt to divide by zero"
  | false => SOut.ok (SInt.ofSignedNat (SBool.xor (SInt.isNeg a) (SInt.isNeg b)) (SInt.abs a / SInt.abs b))

/-- num-bigint `%` on BigInt: remainder takes the sign of the dividend; panics on zero. -/
def SInt.rem (a b : Int) : SOut Int :=
  match SInt.beq b 0 with
  | true => SOut.panic "attempt to calculate the remainder with a divisor of zero"
  | false => SOut.ok (SInt.ofSignedNat (SInt.isNeg a) (SInt.abs a % SInt.abs b))

/-- libspecr `Int::rem_euclid` -/
def SInt.rem_euclid (a b : Int) : SOut Int :=
  SOut.bind (SInt.rem a b) (fun r =>
    match SInt.blt r 0 with
    | true => SOut.ok (r + Int.ofNat (SInt.abs b))
    | false => SOut.ok r)

/-- libspecr `Int::div_ceil` (num_integer::Integer::div_ceil: rounds toward +∞) -/
def SInt.div_ceil (a b : Int) : SOut Int :=
  SOut.bind (SInt.div a b) (fun q =>
    SOut.bind (SInt.rem a b) (fun r =>
      match SInt.beq r 0 with
      | true => SOut.ok q
      | false =>
        -- the exact quotient is positive iff a and b have the same sign
        match SBool.xor (SInt.isNeg a) (SInt.isNeg b) with
        | false => SOut.ok (q + 1)
        | true => SOut.ok q))

/-- libspecr `Int::next_multiple_of` -/
def SInt.next_multiple_of (a b : Int) : SOut Int :=
  SOut.bind (SInt.div_ceil a b) (fun q => SOut.ok (q * b))

def SNat.pow2 (n : Nat) : Nat := Nat.pow 2 n

/-- two's-complement bitwise operations on unbounded integers (num-bigint) -/
def SInt.bnot (a : Int) : Int := -a - 1

def SInt.band (a b : Int) : Int :=
  match a with
  | Int.ofNat x =>
    (match b with
     | Int.ofNat y => Int.ofNat (Nat.land x y)
     | Int.negSucc ny => Int.ofNat (x - Nat.land x ny))
  | Int.negSucc nx =>
    (match b with
     | Int.ofNat y => Int.ofNat (y - Nat.land y nx)
     | Int.negSucc ny => Int.negSucc (Nat.lor nx ny))

def SInt.bor (a b : Int) : Int :=
  match a with
  | Int.ofNat x =>
    (match b with
     | Int.ofNat y => Int.ofNat (Nat.lor x y)
     | Int.negSucc ny => Int.negSucc (ny - Nat.land ny x))
  | Int.negSucc nx =>
    (match b with
     | Int.ofNat y => Int.negSucc (nx - Nat.land nx y)
     | Int.negSucc ny => Int.negSucc (Nat.land nx ny))

def SInt.bxor (a b : Int) : Int :=
  match a with
  | Int.ofNat x =>
    (match b with
     | Int.ofNat y => Int.ofNat (Nat.xor x y)
     | Int.negSucc ny => Int.negSucc (Nat.xor x ny))
  | Int.negSucc nx =>
    (match b with
     | Int.ofNat y => Int.negSucc (Nat.xor nx y)
     | Int.negSucc ny => Int.ofNat (Nat.xor nx ny))

/-- libspecr `Int << Int`: the shift amount goes through `to_u128().unwrap()`. -/
def SInt.shl (a n : Int) : SOut Int :=
  match n with
  | Int.negSucc _ => SOut.panic "called `Option::unwrap()` on a `None` value (shift amount)"
  | Int.ofNat k => SOut.ok (a * Int.ofNat (SNat.pow2 k))

/-- libspecr `Int >> Int`: num-bigint shifts negative values toward −∞.
`Nat.shiftRight` is an AXIOM in Clean's environment (measured 2026-09-17 with
`clean export-cert`), so the shift is written as division by a power of two,
which is a definition. -/
def SNat.shr (x k : Nat) : Nat := x / SNat.pow2 k

def SInt.shr (a n : Int) : SOut Int :=
  match n with
  | Int.negSucc _ => SOut.panic "called `Option::unwrap()` on a `None` value (shift amount)"
  | Int.ofNat k =>
    match a with
    | Int.ofNat x => SOut.ok (Int.ofNat (SNat.shr x k))
    | Int.negSucc nx => SOut.ok (Int.negSucc (SNat.shr nx k))

/-- libspecr `Int::pow`: exponent through `to_u32().unwrap()`. -/
def SInt.pow (a n : Int) : SOut Int :=
  match n with
  | Int.negSucc _ => SOut.panic "called `Option::unwrap()` on a `None` value (exponent)"
  | Int.ofNat k =>
    match a with
    | Int.ofNat x => SOut.ok (Int.ofNat (Nat.pow x k))
    | Int.negSucc nx => SOut.ok (SInt.ofSignedNat (decide (k % 2 = 1)) (Nat.pow (nx + 1) k))

/-- libspecr `Int::is_power_of_two` -/
def SNat.isPow2Aux : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, n =>
    match n with
    | 0 => false
    | 1 => true
    | m => (match decide (m % 2 = 0) with
            | true => SNat.isPow2Aux fuel (m / 2)
            | false => false)

def SInt.is_power_of_two (a : Int) : Bool :=
  match a with
  | Int.ofNat n => SNat.isPow2Aux (n + 1) n
  | Int.negSucc _ => false

/-- libspecr `Int::bring_in_bounds` (panics on size zero) -/
def SInt.bring_in_bounds (a : Int) (signed : MR_Signedness) (sizeBytes : Int) : SOut Int :=
  match SInt.beq sizeBytes 0 with
  | true => SOut.panic "Int::modulo received invalid size zero!"
  | false =>
    SOut.bind (SInt.pow 2 (sizeBytes * 8)) (fun m =>
      SOut.bind (SInt.rem_euclid a m) (fun r =>
        match signed with
        | MR_Signedness.Unsigned => SOut.ok r
        | MR_Signedness.Signed =>
          SOut.bind (SInt.div m 2) (fun h =>
            match SInt.ble h r with
            | true => SOut.ok (r - m)
            | false => SOut.ok r)))

/-- libspecr `Int::in_bounds` -/
def SInt.in_bounds (a : Int) (signed : MR_Signedness) (sizeBytes : Int) : SOut Bool :=
  SOut.bind (SInt.bring_in_bounds a signed sizeBytes) (fun b => SOut.ok (SInt.beq a b))

-- decimal rendering (Display for Int)
def SNat.digitChar (d : Nat) : Char := Char.ofNat (48 + d)

def SNat.toDigits : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    match decide (n < 10) with
    | true => SNat.digitChar n :: acc
    | false => SNat.toDigits fuel (n / 10) (SNat.digitChar (n % 10) :: acc)

def SInt.toString (a : Int) : String :=
  match a with
  | Int.ofNat n => String.mk (SNat.toDigits (n + 1) n [])
  | Int.negSucc n => String.mk ('-' :: SNat.toDigits (n + 2) (n + 1) [])

def SBool.toString (b : Bool) : String := match b with | true => "true" | false => "false"

-- ---------------------------------------------------------------- Size / Align (libspecr size.rs, align.rs)
def SSize.from_bytes (b : Int) : Option Int := match SInt.blt b 0 with | true => none | false => some b
def SSize.from_bytes_const (b : Int) : Int := b
def SSize.from_bits (bits : Int) : SOut (Option Int) :=
  SOut.bind (SInt.rem bits 8) (fun r =>
    match SInt.beq r 0 with
    | false => SOut.ok none
    | true => match SInt.blt bits 0 with
      | true => SOut.ok none
      | false => SOut.bind (SInt.div bits 8) (fun q => SOut.ok (some q)))
def SSize.from_bits_const (bits : Int) : SOut (Option Int) := SSize.from_bits bits
def SSize.bits (s : Int) : Int := s * 8
def SSize.is_zero (s : Int) : Bool := SInt.beq s 0
/-- `Size + Size` goes through `Size::from_bytes(..).unwrap()` -/
def SSize.add (a b : Int) : SOut Int :=
  match SSize.from_bytes (a + b) with
  | some s => SOut.ok s
  | none => SOut.panic "called `Option::unwrap()` on a `None` value (Size + Size)"
def SSize.mul (a b : Int) : SOut Int :=
  match SSize.from_bytes (a * b) with
  | some s => SOut.ok s
  | none => SOut.panic "called `Option::unwrap()` on a `None` value (Size * Int)"
def SSize.align_to (s a : Int) : SOut Int :=
  SOut.bind (SInt.next_multiple_of s a) (fun m =>
    match SSize.from_bytes m with
    | some r => SOut.ok r
    | none => SOut.panic "called `Option::unwrap()` on a `None` value (align_to)")

def SAlign.from_bytes (b : Int) : Option Int := match SInt.is_power_of_two b with | true => some b | false => none
def SAlign.from_bits (bits : Int) : SOut (Option Int) :=
  SOut.bind (SInt.rem bits 8) (fun r =>
    match SInt.beq r 0 with
    | false => SOut.ok none
    | true => SOut.bind (SInt.div bits 8) (fun q => SOut.ok (SAlign.from_bytes q)))
def SAlign.from_bits_const (bits : Int) : SOut (Option Int) := SAlign.from_bits bits
def SAlign.from_bytes_const (b : Int) : Option Int := SAlign.from_bytes b
/-- `addr % align == 0`; an Align is a power of two, so the divisor is nonzero -/
def SAlign.is_aligned (a addr : Int) : SOut Bool :=
  SOut.bind (SInt.rem addr a) (fun r => SOut.ok (SInt.beq r 0))

-- ---------------------------------------------------------------- Option
def SOption.beq {α : Type} (eq : α → α → Bool) (a b : Option α) : Bool :=
  match a with
  | none => (match b with | none => true | some _ => false)
  | some x => (match b with | none => false | some y => eq x y)

def SOption.beqM {α : Type} (eq : α → α → SOut Bool) (a b : Option α) : SOut Bool :=
  match a with
  | none => (match b with | none => SOut.ok true | some _ => SOut.ok false)
  | some x => (match b with | none => SOut.ok false | some y => eq x y)

def SOption.unwrap {α : Type} (a : Option α) : SOut α :=
  match a with
  | some x => SOut.ok x
  | none => SOut.panic "called `Option::unwrap()` on a `None` value"

def SOption.expect {α : Type} (a : Option α) (msg : String) : SOut α :=
  match a with
  | some x => SOut.ok x
  | none => SOut.panic msg

def SOption.is_some {α : Type} (a : Option α) : Bool := match a with | some _ => true | none => false
def SOption.is_none {α : Type} (a : Option α) : Bool := match a with | some _ => false | none => true
def SOption.unwrap_or {α : Type} (a : Option α) (d : α) : α := match a with | some x => x | none => d

def SOption.mapS {α β σ : Type} (a : Option α) (f : α → σ → SOut (β × σ)) (s : σ) : SOut (Option β × σ) :=
  match a with
  | none => SOut.ok (none, s)
  | some x => SOut.bind (f x s) (fun p => match p with | (y, s2) => SOut.ok (some y, s2))

def SOption.mapOrS {α β σ : Type} (a : Option α) (d : β) (f : α → σ → SOut (β × σ)) (s : σ) : SOut (β × σ) :=
  match a with
  | none => SOut.ok (d, s)
  | some x => f x s

-- ---------------------------------------------------------------- Result
def SRes.beq {ε α : Type} (ee : ε → ε → Bool) (ea : α → α → Bool) (a b : SRes ε α) : Bool :=
  match a with
  | SRes.ok x => (match b with | SRes.ok y => ea x y | SRes.err _ => false)
  | SRes.err x => (match b with | SRes.err y => ee x y | SRes.ok _ => false)

def SRes.beqM {ε α : Type} (ee : ε → ε → SOut Bool) (ea : α → α → SOut Bool) (a b : SRes ε α) : SOut Bool :=
  match a with
  | SRes.ok x => (match b with | SRes.ok y => ea x y | SRes.err _ => SOut.ok false)
  | SRes.err x => (match b with | SRes.err y => ee x y | SRes.ok _ => SOut.ok false)

def SRes.unwrap {ε α : Type} (a : SRes ε α) : SOut α :=
  match a with
  | SRes.ok x => SOut.ok x
  | SRes.err _ => SOut.panic "called `Result::unwrap()` on an `Err` value"

def SRes.expect {ε α : Type} (a : SRes ε α) (msg : String) : SOut α :=
  match a with
  | SRes.ok x => SOut.ok x
  | SRes.err _ => SOut.panic msg

def SRes.is_ok {ε α : Type} (a : SRes ε α) : Bool := match a with | SRes.ok _ => true | SRes.err _ => false
def SRes.is_err {ε α : Type} (a : SRes ε α) : Bool := match a with | SRes.ok _ => false | SRes.err _ => true

-- ---------------------------------------------------------------- List (libspecr list/func.rs)
def SList.beq {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => SBool.and (eq x y) (SList.beq eq xs ys)
  | _, _ => false

def SList.beqM {α : Type} (eq : α → α → SOut Bool) : List α → List α → SOut Bool
  | [], [] => SOut.ok true
  | x :: xs, y :: ys => SOut.bind (eq x y) (fun e => match e with
      | true => SList.beqM eq xs ys
      | false => SOut.ok false)
  | _, _ => SOut.ok false

def SList.lenNat {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => SList.lenNat xs + 1

def SList.len {α : Type} (l : List α) : Int := Int.ofNat (SList.lenNat l)
def SList.is_empty {α : Type} (l : List α) : Bool := match l with | [] => true | _ => false
def SList.first {α : Type} (l : List α) : Option α := match l with | [] => none | x :: _ => some x

def SList.last {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => SList.last xs

def SList.getNat {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => SList.getNat xs n

/-- `List::get`: the index goes through `try_to_usize().expect(..)` -/
def SList.get {α : Type} (l : List α) (i : Int) : SOut (Option α) :=
  match i with
  | Int.ofNat n => SOut.ok (SList.getNat l n)
  | Int.negSucc _ => SOut.panic "List::get: index out of range of `usize`!"

/-- `list[i]` = `index_at` = `get(i).unwrap()` -/
def SList.index_at {α : Type} (l : List α) (i : Int) : SOut α :=
  SOut.bind (SList.get l i) SOption.unwrap

def SList.setNat {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => match SList.setNat xs n v with
    | some ys => some (x :: ys)
    | none => none

def SList.set {α : Type} (l : List α) (i : Int) (v : α) : SOut (List α) :=
  match i with
  | Int.negSucc _ => SOut.panic "List::mutate_at: index out of range of `usize`!"
  | Int.ofNat n => match SList.setNat l n v with
    | some r => SOut.ok r
    | none => SOut.panic "index out of bounds (List::set)"

def SList.appendL {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: SList.appendL xs ys

def SList.push {α : Type} (l : List α) (v : α) : List α := SList.appendL l [v]

def SList.dropLast {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | x :: xs => x :: SList.dropLast xs

/-- `pop`: returns the popped element and the new list -/
def SList.pop {α : Type} (l : List α) : (Option α × List α) := (SList.last l, SList.dropLast l)

def SList.reverseAux {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => SList.reverseAux xs (x :: acc)
def SList.reverse {α : Type} (l : List α) : List α := SList.reverseAux l []

def SList.dropNat {α : Type} : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, _ :: xs => SList.dropNat n xs

def SList.takeNat {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs => x :: SList.takeNat n xs

/-- `subslice_with_length(start, length)`: im::Vector::slice panics out of range -/
def SList.subslice_with_length {α : Type} (l : List α) (start len : Int) : SOut (List α) :=
  match start with
  | Int.negSucc _ => SOut.panic "List::subslice_with_length: `start` out of range of `usize`!"
  | Int.ofNat s => match len with
    | Int.negSucc _ => SOut.panic "List::subslice_with_length: `length` out of range of `usize`!"
    | Int.ofNat n =>
      match decide (s + n ≤ SList.lenNat l) with
      | true => SOut.ok (SList.takeNat n (SList.dropNat s l))
      | false => SOut.panic "Vector::slice: index out of bounds"

/-- `write_subslice_at_index(start, src)` -/
def SList.write_subslice_at_index {α : Type} (l : List α) (start : Int) (src : List α) : SOut (List α) :=
  match SInt.blt (SList.len l) (start + SList.len src) with
  | true => SOut.panic "`write_subslice_at_index`: trying to write out of range!"
  | false => match start with
    | Int.negSucc _ => SOut.panic "List::subslice_with_length: `start` out of range of `usize`!"
    | Int.ofNat s => SOut.ok (SList.appendL (SList.takeNat s l)
        (SList.appendL src (SList.dropNat (s + SList.lenNat src) l)))

def SList.repeatNat {α : Type} (x : α) : Nat → List α
  | 0 => []
  | n + 1 => x :: SList.repeatNat x n

/-- `list![x; n]` = `List::from_elem(x, n)` -/
def SList.from_elem {α : Type} (x : α) (n : Int) : SOut (List α) :=
  match n with
  | Int.ofNat k => SOut.ok (SList.repeatNat x k)
  | Int.negSucc _ => SOut.panic "invalid number of elements in List::from_elem"

def SList.zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: SList.zip xs ys
  | _, _ => []

def SList.enumerateFrom {α : Type} (i : Int) : List α → List (Int × α)
  | [] => []
  | x :: xs => (i, x) :: SList.enumerateFrom (i + 1) xs
def SList.enumerate {α : Type} (l : List α) : List (Int × α) := SList.enumerateFrom 0 l

/-- `(a..b)` as the list of its elements -/
def SList.rangeNat (a : Int) : Nat → List Int
  | 0 => []
  | n + 1 => a :: SList.rangeNat (a + 1) n
def SList.range (a b : Int) : List Int :=
  match SInt.blt a b with
  | true => SList.rangeNat a (SInt.abs (b - a))
  | false => []

-- state-threading, fallible higher-order functions. Every closure the
-- translator emits has the shape `args → σ → SOut (result × σ)`.
def SList.mapS {α β σ : Type} (xs : List α) (f : α → σ → SOut (β × σ)) (s : σ) : SOut (List β × σ) :=
  match xs with
  | [] => SOut.ok ([], s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (b, s2) => SOut.bind (SList.mapS rest f s2) (fun q => match q with
      | (bs, s3) => SOut.ok (b :: bs, s3)))

def SList.flatMapS {α β σ : Type} (xs : List α) (f : α → σ → SOut (List β × σ)) (s : σ) : SOut (List β × σ) :=
  match xs with
  | [] => SOut.ok ([], s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (b, s2) => SOut.bind (SList.flatMapS rest f s2) (fun q => match q with
      | (bs, s3) => SOut.ok (SList.appendL b bs, s3)))

def SList.mapWithIdxAux {α β σ : Type} (i : Int) (xs : List α) (f : Int → α → σ → SOut (β × σ)) (s : σ) : SOut (List β × σ) :=
  match xs with
  | [] => SOut.ok ([], s)
  | x :: rest => SOut.bind (f i x s) (fun p => match p with
    | (b, s2) => SOut.bind (SList.mapWithIdxAux (i + 1) rest f s2) (fun q => match q with
      | (bs, s3) => SOut.ok (b :: bs, s3)))
def SList.mapWithIdxS {α β σ : Type} (xs : List α) (f : Int → α → σ → SOut (β × σ)) (s : σ) : SOut (List β × σ) :=
  SList.mapWithIdxAux 0 xs f s

def SList.foldWithIdxAux {α A σ : Type} (i : Int) (xs : List α) (acc : A) (f : A → Int → α → σ → SOut (A × σ)) (s : σ) : SOut (A × σ) :=
  match xs with
  | [] => SOut.ok (acc, s)
  | x :: rest => SOut.bind (f acc i x s) (fun p => match p with
    | (a2, s2) => SList.foldWithIdxAux (i + 1) rest a2 f s2)
def SList.foldWithIdxS {α A σ : Type} (xs : List α) (acc : A) (f : A → Int → α → σ → SOut (A × σ)) (s : σ) : SOut (A × σ) :=
  SList.foldWithIdxAux 0 xs acc f s

def SList.foldS {α A σ : Type} (xs : List α) (acc : A) (f : A → α → σ → SOut (A × σ)) (s : σ) : SOut (A × σ) :=
  match xs with
  | [] => SOut.ok (acc, s)
  | x :: rest => SOut.bind (f acc x s) (fun p => match p with
    | (a2, s2) => SList.foldS rest a2 f s2)

def SList.anyS {α σ : Type} (xs : List α) (f : α → σ → SOut (Bool × σ)) (s : σ) : SOut (Bool × σ) :=
  match xs with
  | [] => SOut.ok (false, s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (b, s2) => match b with
      | true => SOut.ok (true, s2)
      | false => SList.anyS rest f s2)

def SList.allS {α σ : Type} (xs : List α) (f : α → σ → SOut (Bool × σ)) (s : σ) : SOut (Bool × σ) :=
  match xs with
  | [] => SOut.ok (true, s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (b, s2) => match b with
      | false => SOut.ok (false, s2)
      | true => SList.allS rest f s2)

def SList.findS {α σ : Type} (xs : List α) (f : α → σ → SOut (Bool × σ)) (s : σ) : SOut (Option α × σ) :=
  match xs with
  | [] => SOut.ok (none, s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (b, s2) => match b with
      | true => SOut.ok (some x, s2)
      | false => SList.findS rest f s2)

def SList.findMapS {α β σ : Type} (xs : List α) (f : α → σ → SOut (Option β × σ)) (s : σ) : SOut (Option β × σ) :=
  match xs with
  | [] => SOut.ok (none, s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (o, s2) => match o with
      | some y => SOut.ok (some y, s2)
      | none => SList.findMapS rest f s2)

/-- `try_map` with a `Result`/`NdResult`-returning closure: stops at the first error -/
def SList.tryMapResS {α β ε σ : Type} (xs : List α) (f : α → σ → SOut (SRes ε β × σ)) (s : σ) : SOut (SRes ε (List β) × σ) :=
  match xs with
  | [] => SOut.ok (SRes.ok [], s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (r, s2) => match r with
      | SRes.err e => SOut.ok (SRes.err e, s2)
      | SRes.ok b => SOut.bind (SList.tryMapResS rest f s2) (fun q => match q with
        | (rs, s3) => match rs with
          | SRes.err e => SOut.ok (SRes.err e, s3)
          | SRes.ok bs => SOut.ok (SRes.ok (b :: bs), s3)))

/-- `try_map` with an `Option`-returning closure -/
def SList.tryMapOptS {α β σ : Type} (xs : List α) (f : α → σ → SOut (Option β × σ)) (s : σ) : SOut (Option (List β) × σ) :=
  match xs with
  | [] => SOut.ok (some [], s)
  | x :: rest => SOut.bind (f x s) (fun p => match p with
    | (r, s2) => match r with
      | none => SOut.ok (none, s2)
      | some b => SOut.bind (SList.tryMapOptS rest f s2) (fun q => match q with
        | (rs, s3) => match rs with
          | none => SOut.ok (none, s3)
          | some bs => SOut.ok (some (b :: bs), s3)))

/-- `mutate_at(i, f)` / `try_mutate_at(i, f)`: `f` gets the element by `&mut` -/
def SList.mutateAtNat {α O σ : Type} (l : List α) (n : Nat) (f : α → σ → SOut (O × α × σ)) (s : σ) : SOut (O × List α × σ) :=
  match l with
  | [] => SOut.panic "index out of bounds (List::mutate_at)"
  | x :: xs => match n with
    | 0 => SOut.bind (f x s) (fun p => match p with
      | (o, x2, s2) => SOut.ok (o, x2 :: xs, s2))
    | k + 1 => SOut.bind (SList.mutateAtNat xs k f s) (fun p => match p with
      | (o, xs2, s2) => SOut.ok (o, x :: xs2, s2))

def SList.mutateAtS {α O σ : Type} (l : List α) (i : Int) (f : α → σ → SOut (O × α × σ)) (s : σ) : SOut (O × List α × σ) :=
  match i with
  | Int.negSucc _ => SOut.panic "List::mutate_at: index out of range of `usize`!"
  | Int.ofNat n => SList.mutateAtNat l n f s

/-- `sort_by_key` with an integer-like key (`Size`/`Int`); stable like `slice::sort_by_key` -/
def SList.insertKeyed {α : Type} (x : Int × α) : List (Int × α) → List (Int × α)
  | [] => [x]
  | y :: ys => match x with
    | (kx, _) => match y with
      | (ky, _) => match SInt.blt kx ky with
        | true => x :: y :: ys
        | false => y :: SList.insertKeyed x ys

def SList.sortKeyed {α : Type} : List (Int × α) → List (Int × α) → List (Int × α)
  | acc, [] => acc
  | acc, x :: rest => SList.sortKeyed (SList.insertKeyed x acc) rest

def SList.snds {α : Type} : List (Int × α) → List α
  | [] => []
  | (_, x) :: rest => x :: SList.snds rest

def SList.sortByIntKeyS {α σ : Type} (xs : List α) (key : α → σ → SOut (Int × σ)) (s : σ) : SOut (List α × σ) :=
  SOut.bind (SList.mapS xs (fun (x : α) (st : σ) => SOut.bind (key x st) (fun p => match p with
      | (k, st2) => SOut.ok ((k, x), st2))) s) (fun q => match q with
    | (keyed, s2) => SOut.ok (SList.snds (SList.sortKeyed [] keyed), s2))

-- ---------------------------------------------------------------- Endianness (libspecr endianness.rs)
/-- libspecr `Endianness::decode(signed, bytes)`: the most significant byte is
read at its signedness, then `out = (out << 8) | b` for the rest. -/
def SEndian.foldBytes : Int → List Int → Int
  | acc, [] => acc
  | acc, b :: rest => SEndian.foldBytes (acc * 256 + b) rest

def SEndian.decode (e : MR_Endianness) (signed : MR_Signedness) (bytes : List Int) : SOut Int :=
  let be := (match e with | MR_Endianness.LittleEndian => SList.reverse bytes | MR_Endianness.BigEndian => bytes)
  match be with
  | [] => SOut.panic "called `Option::unwrap()` on a `None` value (Endianness::decode of no bytes)"
  | b0 :: rest =>
    let first := (match signed with
      | MR_Signedness.Unsigned => b0
      | MR_Signedness.Signed => (match SInt.ble 128 b0 with | true => b0 - 256 | false => b0))
    SOut.ok (SEndian.foldBytes first rest)

/-- libspecr `Endianness::encode(signed, size, int)`: `None` when out of bounds;
otherwise the size-byte two's-complement representation. -/
def SEndian.leBytes (v : Int) : Nat → SOut (List Int)
  | 0 => SOut.ok []
  | n + 1 => SOut.bind (SInt.rem_euclid v 256) (fun b =>
      SOut.bind (SInt.shr v 8) (fun v2 =>
        SOut.bind (SEndian.leBytes v2 n) (fun rest => SOut.ok (b :: rest))))

def SEndian.encode (e : MR_Endianness) (signed : MR_Signedness) (sizeBytes : Int) (i : Int) : SOut (Option (List Int)) :=
  SOut.bind (SInt.in_bounds i signed sizeBytes) (fun ok =>
    match ok with
    | false => SOut.ok none
    | true =>
      SOut.bind (SInt.pow 2 (sizeBytes * 8)) (fun m =>
        let v := (match SInt.blt i 0 with | true => i + m | false => i)
        SOut.bind (SEndian.leBytes v (SInt.abs sizeBytes)) (fun le =>
          match e with
          | MR_Endianness.LittleEndian => SOut.ok (some le)
          | MR_Endianness.BigEndian => SOut.ok (some (SList.reverse le)))))

-- ---------------------------------------------------------------- Map / Set (libspecr map, set; im::HashMap / im::HashSet)
-- A map is an association list with unique keys; iteration order is insertion
-- order (libspecr's HashMap order is unspecified). Equality is extensional.
def SMap.getL {K V : Type} (eq : K → K → Bool) : List (K × V) → K → Option V
  | [], _ => none
  | (k, v) :: rest, key => match eq k key with
    | true => some v
    | false => SMap.getL eq rest key

def SMap.get {K V : Type} (eq : K → K → Bool) (m : List (K × V)) (k : K) : Option V := SMap.getL eq m k

def SMap.index_at {K V : Type} (eq : K → K → Bool) (m : List (K × V)) (k : K) : SOut V :=
  SOption.unwrap (SMap.get eq m k)

def SMap.contains_key {K V : Type} (eq : K → K → Bool) (m : List (K × V)) (k : K) : Bool :=
  SOption.is_some (SMap.get eq m k)

def SMap.replaceL {K V : Type} (eq : K → K → Bool) : List (K × V) → K → V → List (K × V)
  | [], _, _ => []
  | (k, v) :: rest, key, nv => match eq k key with
    | true => (k, nv) :: rest
    | false => (k, v) :: SMap.replaceL eq rest key nv

/-- `insert`: returns the previous value -/
def SMap.insert {K V : Type} (eq : K → K → Bool) (m : List (K × V)) (k : K) (v : V) : (Option V × List (K × V)) :=
  match SMap.get eq m k with
  | some old => (some old, SMap.replaceL eq m k v)
  | none => (none, SList.push m (k, v))

def SMap.removeL {K V : Type} (eq : K → K → Bool) : List (K × V) → K → List (K × V)
  | [], _ => []
  | (k, v) :: rest, key => match eq k key with
    | true => rest
    | false => (k, v) :: SMap.removeL eq rest key

def SMap.remove {K V : Type} (eq : K → K → Bool) (m : List (K × V)) (k : K) : (Option V × List (K × V)) :=
  (SMap.get eq m k, SMap.removeL eq m k)

def SMap.try_insert {K V : Type} (eq : K → K → Bool) (m : List (K × V)) (k : K) (v : V) : (SRes Unit Unit × List (K × V)) :=
  match SMap.contains_key eq m k with
  | true => (SRes.err (), m)
  | false => (SRes.ok (), SList.push m (k, v))

def SMap.keys {K V : Type} : List (K × V) → List K
  | [] => []
  | (k, _) :: rest => k :: SMap.keys rest

def SMap.values {K V : Type} : List (K × V) → List V
  | [] => []
  | (_, v) :: rest => v :: SMap.values rest

def SMap.subsetL {K V : Type} (keq : K → K → Bool) (veq : V → V → Bool) (big : List (K × V)) : List (K × V) → Bool
  | [] => true
  | (k, v) :: rest => match SMap.get keq big k with
    | none => false
    | some w => SBool.and (veq v w) (SMap.subsetL keq veq big rest)

def SMap.beq {K V : Type} (keq : K → K → Bool) (veq : V → V → Bool) (a b : List (K × V)) : Bool :=
  SBool.and (SInt.beq (SList.len a) (SList.len b)) (SMap.subsetL keq veq b a)

def SMap.subsetLM {K V : Type} (keq : K → K → Bool) (veq : V → V → SOut Bool) (big : List (K × V)) : List (K × V) → SOut Bool
  | [] => SOut.ok true
  | (k, v) :: rest => match SMap.get keq big k with
    | none => SOut.ok false
    | some w => SOut.bind (veq v w) (fun e => match e with
      | true => SMap.subsetLM keq veq big rest
      | false => SOut.ok false)

def SMap.beqM {K V : Type} (keq : K → K → Bool) (veq : V → V → SOut Bool) (a b : List (K × V)) : SOut Bool :=
  match SInt.beq (SList.len a) (SList.len b) with
  | false => SOut.ok false
  | true => SMap.subsetLM keq veq b a

def SSet.contains {T : Type} (eq : T → T → Bool) : List T → T → Bool
  | [], _ => false
  | x :: rest, y => match eq x y with
    | true => true
    | false => SSet.contains eq rest y

def SSet.insert {T : Type} (eq : T → T → Bool) (s : List T) (x : T) : List T :=
  match SSet.contains eq s x with
  | true => s
  | false => SList.push s x

def SSet.try_insert {T : Type} (eq : T → T → Bool) (s : List T) (x : T) : (SRes Unit Unit × List T) :=
  match SSet.contains eq s x with
  | true => (SRes.err (), s)
  | false => (SRes.ok (), SList.push s x)

def SSet.removeL {T : Type} (eq : T → T → Bool) : List T → T → List T
  | [], _ => []
  | x :: rest, y => match eq x y with
    | true => rest
    | false => x :: SSet.removeL eq rest y

def SSet.ofList {T : Type} (eq : T → T → Bool) : List T → List T → List T
  | acc, [] => acc
  | acc, x :: rest => SSet.ofList eq (SSet.insert eq acc x) rest

def SSet.subsetL {T : Type} (eq : T → T → Bool) (big : List T) : List T → Bool
  | [] => true
  | x :: rest => SBool.and (SSet.contains eq big x) (SSet.subsetL eq big rest)

def SSet.beq {T : Type} (eq : T → T → Bool) (a b : List T) : Bool :=
  SBool.and (SInt.beq (SList.len a) (SList.len b)) (SSet.subsetL eq b a)

-- ---------------------------------------------------------------- derived Debug (`{:?}`)
-- The pieces Rust's `#[derive(Debug)]` renders for the library types; the
-- per-ADT walk is generated. libspecr prints `Size`/`Align` as `Size(N bytes)`
-- (size.rs, align.rs) and `Int` through `Display` (int/ops.rs).
def SDebug.size (n : Int) : String := "Size(" ++ SInt.toString n ++ " bytes)"
def SDebug.align (n : Int) : String := "Align(" ++ SInt.toString n ++ " bytes)"
def SDebug.name (n : Nat) : String := "Name(" ++ SInt.toString (Int.ofNat n) ++ ")"
def SDebug.str (s : String) : String := "\"" ++ s ++ "\""
def SDebug.ordering (o : SOrdering) : String :=
  match o with
  | SOrdering.less => "Less"
  | SOrdering.equal => "Equal"
  | SOrdering.greater => "Greater"

def SDebug.option {α : Type} (f : α → SOut String) (o : Option α) : SOut String :=
  match o with
  | none => SOut.ok "None"
  | some x => SOut.bind (α := String) (β := String) (f x) (fun (s : String) => SOut.ok ("Some(" ++ s ++ ")"))

def SDebug.listAux {α : Type} (f : α → SOut String) (first : Bool) (acc : String) : List α → SOut String
  | [] => SOut.ok (acc ++ "]")
  | x :: rest => SOut.bind (α := String) (β := String) (f x) (fun (s : String) =>
      SDebug.listAux f false (acc ++ (match first with | true => s | false => ", " ++ s)) rest)

def SDebug.list {α : Type} (f : α → SOut String) (l : List α) : SOut String :=
  SDebug.listAux f true "[" l

def MR_Signedness.debugStr (_fuel : Nat) (a : MR_Signedness) : SOut String := SOut.ok (MR_Signedness.debugName a)
def MR_Mutability.debugStr (_fuel : Nat) (a : MR_Mutability) : SOut String := SOut.ok (MR_Mutability.debugName a)
def MR_Endianness.debugStr (_fuel : Nat) (a : MR_Endianness) : SOut String := SOut.ok (MR_Endianness.debugName a)

-- ---------------------------------------------------------------- control flow
inductive SCtl (σ ρ : Type) where
  | next (s : σ)
  | brk (s : σ)
  | ret (r : ρ)

/-- `for x in xs { body }` -/
def SLoop.forS {α σ ρ : Type} (xs : List α) (s : σ) (body : α → σ → SOut (SCtl σ ρ)) : SOut (SCtl σ ρ) :=
  match xs with
  | [] => SOut.ok (SCtl.next s)
  | x :: rest => SOut.bind (body x s) (fun c => match c with
    | SCtl.next s2 => SLoop.forS rest s2 body
    | SCtl.brk s2 => SOut.ok (SCtl.brk s2)
    | SCtl.ret r => SOut.ok (SCtl.ret r))

/-- `while cond { body }` / `while let`: `body` returns `brk` when the condition fails -/
def SLoop.whileS {σ ρ : Type} (fuel : Nat) (s : σ) (body : σ → SOut (SCtl σ ρ)) : SOut (SCtl σ ρ) :=
  match fuel with
  | 0 => SOut.fuel
  | fuel + 1 => SOut.bind (body s) (fun c => match c with
    | SCtl.next s2 => SLoop.whileS fuel s2 body
    | SCtl.brk s2 => SOut.ok (SCtl.brk s2)
    | SCtl.ret r => SOut.ok (SCtl.ret r))

-- ---------------------------------------------------------------- non-determinism
/-- libspecr `pick(IntDistribution, pred)`: a demonic choice node. The candidates of
the distribution are its start rounded up to a multiple of the divisor, then each
further multiple below `end`; index `j` names the j-th. Every candidate that
satisfies `pred` is a legitimate behaviour; an index past the end, or a candidate
that fails `pred`, continues as `reject`. Nothing is resolved here. -/
def SPick.choose {σ : Type} (d : SIntDistribution) (pred : Int → σ → SOut (Bool × σ)) (s : σ) : SOut (Int × σ) :=
  SOut.bind (SInt.div_ceil d.start d.divisor) (fun q =>
    SOut.pick (fun j => match SInt.blt ((q + Int.ofNat j) * d.divisor) d.«end» with
      | false => SOut.reject
      | true => SOut.bind (pred ((q + Int.ofNat j) * d.divisor) s) (fun p => match p with
        | (b, s2) => match b with
          | true => SOut.ok ((q + Int.ofNat j) * d.divisor, s2)
          | false => SOut.reject)))

/-- libspecr `predict(pred)`: an angelic prediction node over the candidates
`dec 0, dec 1, …` of the predicted type (`dec i = none` past a finite domain). -/
def SPredict.choose {β σ : Type} (dec : Nat → Option β) (pred : β → σ → SOut (Bool × σ)) (s : σ) : SOut (β × σ) :=
  SOut.predict (fun i => match dec i with
    | none => SOut.reject
    | some v => SOut.bind (pred v s) (fun p => match p with
      | (b, s2) => match b with
        | true => SOut.ok (v, s2)
        | false => SOut.reject))

/-- The least-candidate search K8's oracle performs at a choice node: the first
index `i, i+1, …` whose interpreted branch `r i` is not `reject`, among the first
`bound`. -/
def SOut.searchNat {α : Type} (bound : Nat) (i : Nat) (r : Nat → SOut α) : SOut α :=
  match bound with
  | 0 => SOut.nobehavior
  | bound + 1 =>
    match r i with
    | SOut.reject => SOut.searchNat bound (i + 1) r
    | x => x

/-- K8's deterministic interpretation: every `pick` and every `predict` takes the
least candidate that passes its predicate, among the first `bound`. It is one
oracle, not the angelic semantics: a prediction it makes may lead to UB that
another prediction avoids. -/
def SOut.runLeast {α : Type} (bound : Nat) (x : SOut α) : SOut α :=
  @SOut.rec α (fun _ => SOut α)
    (fun a => SOut.ok a)
    (fun m => SOut.panic m)
    SOut.fuel
    (fun w => SOut.refused w)
    SOut.nobehavior
    SOut.reject
    (fun _ ih => SOut.searchNat bound 0 ih)
    (fun _ ih => SOut.searchNat bound 0 ih)
    x
