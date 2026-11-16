-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Model.Syntax: the executable presentation's syntax (Beyond-TLA design
-- 10-executable-semantics.md, "Syntax", 10:121-170): QKind, PrimOp, the mutual Expr/Act,
-- the Boolean connectives as encoding definitions, term size, and de Bruijn shifting,
-- substitution and instantiation. Clean source, served to ty by crates/trust-model-prelude
-- and kernel-checked by crates/trust-spec-temporal. Lane row B1A-12.
--
-- Verbatim: QKind (10:127-128) and Expr/Act (10:130-161) have the design's names and
-- constructor order; the statement pins of B1A-26b enforce it. The design writes the two
-- inductives one after the other; Clean takes them as one `mutual` block (B1A-02a,
-- capabilities/mutual_expr_act.lean).
--
-- Cost discipline (TASK-STATE 4.8): control is raw recursors with explicit motives, never
-- `match`, `if` or `&&`.

namespace Trust
namespace Model

-- Quantifier kinds (10:127-128): \E, \A, CHOOSE, {x \in S : P}, {e : x \in S},
-- [x \in S |-> e].
inductive QKind where
  | qEx | qAll | qChoose | qFilter | qMap | qFn

-- ---- PrimOp (B1A-D10) ----
--
-- One constructor per value-semantic row of the K2 catalog current at this row's start:
-- contract K2 version 2, amendment 4 (`CONTRACT_VERSION = 2`, `CONTRACT_AMENDMENT = 4`),
-- ty crates/tla-model-ir/src/ops.rs `OPS` (:476-603) at ty 874e62f03b. A value-semantic row
-- is a row of class `Value`; its constructor is the row's mnemonic in camelCase
-- (`set.big_union` is `setBigUnion`), in `OPS` order, so PrimOp maps 1:1 by name onto the
-- K2 value rows (design 10:166). A row's attributes (ops attr.rs `op_attrs`) are the
-- constructor's arguments, never operands: `field` and `fields` are token ranks (the
-- `Value.str` rank of the field name; `fields` in source order), `index` is 1-based. The
-- additions TLC needs and K2 lacks follow the K2 rows. Eight value rows are excluded as
-- L4-only representation, iterator or fused rows: each is a second form of a construct
-- another row or an Expr form already covers, so admitting it would give two alpha-distinct
-- Specs for one TLA+ construct (README D-B, B1A-D10). The additions and the exclusions are
-- filed for m30 in ty reports/perf/2026-10-09-beyond-tla-b1a/K2-REQUESTS-B1A.md R2 and R3.
-- The design's names in 10:113 and 10:675 (`PrimOp.eq`, `PrimOp.lt`, `op .eq`) are the
-- rows `value.eq` and `int.lt`: `valueEq` and `intLt`.
--
-- The table below is parsed by trust-model-prelude's unit test
-- `tests::primop_table_mirrors_k2`: every line `-- | <constructor> | <K2 row> |` names one
-- constructor (in declaration order) and its row, `B1a addition (K2 request)`, and every
-- line `-- | - | <K2 row>: excluded L4-only (<reason>) |` an excluded value row.
--
-- | intAdd | int.add |
-- | intSub | int.sub |
-- | intMul | int.mul |
-- | intDiv | int.div |
-- | intMod | int.mod |
-- | intNeg | int.neg |
-- | intLt | int.lt |
-- | intLe | int.le |
-- | - | int.eq: excluded L4-only (value.eq covers it) |
-- | - | enum.eq: excluded L4-only (a universe-index compare; value.eq covers it) |
-- | - | enum.lt: excluded L4-only (a universe-index compare; TLC's order is tlcLt) |
-- | recGet | rec.get |
-- | recWith | rec.with |
-- | funcApply | func.apply |
-- | funcExcept | func.except |
-- | funcDomain | func.domain |
-- | setIn | set.in |
-- | setInsert | set.insert |
-- | setUnion | set.union |
-- | setDiff | set.diff |
-- | setCard | set.card |
-- | setSubseteq | set.subseteq |
-- | - | set.iter: excluded L4-only (an iterator; Expr.quant and Act.ex/fa/primeIn cover it) |
-- | seqLen | seq.len |
-- | seqIndex | seq.index |
-- | seqAppend | seq.append |
-- | seqHead | seq.head |
-- | seqTail | seq.tail |
-- | seqSubseq | seq.subseq |
-- | valueEq | value.eq |
-- | valueNe | value.ne |
-- | - | value.eq_func_except: excluded L4-only (fused; value.eq over func.except covers it) |
-- | - | value.eq_record_new: excluded L4-only (fused; value.eq over rec.new covers it) |
-- | setEnum | set.enum |
-- | setRange | set.range |
-- | setIntersect | set.intersect |
-- | setBigUnion | set.big_union |
-- | setPowerset | set.powerset |
-- | setProduct | set.product |
-- | setIsFinite | set.is_finite |
-- | funcSet | func.set |
-- | recNew | rec.new |
-- | recSetOf | rec.set_of |
-- | tupleNew | tuple.new |
-- | tupleGet | tuple.get |
-- | - | seq.new: excluded L4-only (another representation; tuple.new covers it) |
-- | seqConcat | seq.concat |
-- | seqSet | seq.set |
-- | seqRemoveAt | seq.remove_at |
-- | valueAsBool | value.as_bool |
-- | - | func.tabulate: excluded L4-only (a cursor's element; Expr.quant qFn covers it) |
-- | intPow | B1a addition (K2 request) |
-- | intGt | B1a addition (K2 request) |
-- | intGe | B1a addition (K2 request) |
-- | natSuccU | B1a addition (K2 request) |
-- | natSatU | B1a addition (K2 request) |
-- | assert | B1a addition (K2 request) |
--
-- The other K2 rows are not value rows (classes State, Boundary, Control, Iteration and
-- Constant) and have no PrimOp: rep.load and rep.store are Expr.cur/nxt and the item
-- machine's assignments; box, unbox and top.call are L4's value-word boundary; gen.* are
-- Act; raise is Fail; loop.* are Expr.quant; pool.load is Expr.pool.
--
-- Additions (design 10:166 and the construct coverage table): `intPow` is `a ^ b`
-- (Naturals' `^`), `intGt` and `intGe` are `a > b` and `a >= b` (K2 has only int.lt and
-- int.le, and TLC evaluates `a > b` with its own operand order), `natSuccU [a]` and
-- `natSatU [a, cap]` are the unbounded natural-number ops of 10:166 (B1A-D12), and `assert`
-- is TLC's `Assert(P, msg)` (10:679, `Fail.assertFailed`).
inductive PrimOp where
  | intAdd | intSub | intMul | intDiv | intMod | intNeg | intLt | intLe
  | recGet (field : Nat)
  | recWith (field : Nat)
  | funcApply | funcExcept | funcDomain
  | setIn | setInsert | setUnion | setDiff | setCard | setSubseteq
  | seqLen | seqIndex | seqAppend | seqHead | seqTail | seqSubseq
  | valueEq | valueNe
  | setEnum | setRange | setIntersect | setBigUnion | setPowerset | setProduct | setIsFinite
  | funcSet
  | recNew (fields : List Nat)
  | recSetOf (fields : List Nat)
  | tupleNew
  | tupleGet (index : Nat)
  | seqConcat | seqSet | seqRemoveAt
  | valueAsBool
  | intPow | intGt | intGe | natSuccU | natSatU | assert

-- ---- Expr and Act (10:130-161), verbatim ----
--
-- De Bruijn convention (B1A-D15): `bvar 0` is the innermost binder. A list of n binders
-- (Expr.quant's domains, Act.ex/fa's domains, a definition's n parameters) binds its k-th
-- binder (from 0, in source order) as `bvar (n-1-k)` in its body, so the last binder is
-- innermost; a binder list's domains are read outside it (TLC's ContextEnumerator
-- evaluates every domain first). `Expr.letLazy e b` and `Act.letA e a` bind one variable
-- (`bvar 0` in b or a; e is read outside it). No other constructor binds.
--
-- The block's recursors take one motive per type of the block plus one per distinct nested
-- instantiation of a block type, in the order Clean discovers them (B1A-D70; measured by
-- model_prelude_kernel::syntax_recursor_motives): Expr, Act, List Expr,
-- List (Expr × Expr), Option Expr, List Act, List (Expr × Act), Option Act,
-- List (Nat × Act), Expr × Expr, Expr × Act, Nat × Act (twelve).
mutual
inductive Expr where
  | lit     : Value → Expr
  | cur     : Nat → Expr
  | nxt     : Nat → Expr
  | bvar    : Nat → Expr
  | pool    : Nat → Expr
  | op      : PrimOp → List Expr → Expr
  | ite     : Expr → Expr → Expr → Expr
  | caseOf  : List (Expr × Expr) → Option Expr → Expr
  | letLazy : Expr → Expr → Expr
  | quant   : QKind → List Expr → Expr → Expr
  | app     : Nat → List Expr → Expr
  | enabled : Act → Expr
inductive Act where
  | conj      : List Act → Act
  | disj      : List Act → Act
  | pred      : Expr → Act
  | prime     : Nat → Expr → Act
  | primeIn   : Nat → Expr → Act
  | unchanged : Expr → Act
  | changed   : Expr → Act
  | ex        : List Expr → Act → Act
  | fa        : List Expr → Act → Act
  | ite       : Expr → Act → Act → Act
  | caseOf    : List (Expr × Act) → Option Act → Act
  | letA      : Expr → Act → Act
  | call      : Nat → List Expr → Act
  | pchoice   : List (Nat × Act) → Act
end

-- ---- The Boolean connectives: encoding definitions (B1A-D11) ----
--
-- TLA+'s connectives are not PrimOps: each is an Expr built from `ite`, `value.as_bool` and
-- `value.eq`, so a TLC short-circuit is the `ite` that skips a branch. Probe.lean's DSL
-- reuses them and B2's front end must produce them. Each follows TLC 94d0c50's
-- Tool.evalApplImpl (read with `javap -c`, opcodes lnot 27, land 36, lor 37, implies 38,
-- equiv 39):
--   ~a       eval a; not a Boolean: error; else its negation.
--   a /\ b   eval a; not a Boolean: error; FALSE: FALSE (b unread); else eval b, not a
--            Boolean: error, else b.
--   a \/ b   eval a; not a Boolean: error; TRUE: TRUE (b unread); else b as for /\.
--   a => b   eval a; not a Boolean: error; FALSE: TRUE (b unread); else b as for /\.
--   a <=> b  eval a, THEN eval b, then either one not a Boolean: error; else a = b.
-- `Expr.ite`'s condition check is the "not a Boolean" error (TLC's IF; class typeErr) and
-- `value.as_bool` is the second operand's (K2 v2.1, Q-K2-14: "any other value raises
-- type_error"). `<=>` is not short-circuit: TLC evaluates both operands before checking
-- either, so a non-Boolean a whose b raises gives b's error. `Expr.equiv_` reproduces that
-- order without duplicating a or b in the term: it binds the tuple <<a, b>> lazily (LET is
-- substitution, 10:168), reads each component with `seq.head`/`seq.tail` (TLC's Head
-- returns the tuple's element as evaluated, Sequences.Head; a tuple is a sequence, 10:85),
-- checks each with `value.as_bool`, and compares them with `value.eq`, whose receiver is
-- the left operand (B1A-D87). Reading <<a, b>> twice evaluates a and b twice, with the same
-- result: evaluation is a function.
def Expr.and_ (a b : Expr) : Expr :=
  Expr.ite a (Expr.op PrimOp.valueAsBool [b]) (Expr.lit (Value.bool false))

def Expr.or_ (a b : Expr) : Expr :=
  Expr.ite a (Expr.lit (Value.bool true)) (Expr.op PrimOp.valueAsBool [b])

def Expr.not_ (a : Expr) : Expr :=
  Expr.ite a (Expr.lit (Value.bool false)) (Expr.lit (Value.bool true))

def Expr.implies_ (a b : Expr) : Expr :=
  Expr.ite a (Expr.op PrimOp.valueAsBool [b]) (Expr.lit (Value.bool true))

def Expr.equiv_ (a b : Expr) : Expr :=
  Expr.letLazy (Expr.op PrimOp.tupleNew [a, b])
    (Expr.op PrimOp.valueEq
      [Expr.op PrimOp.valueAsBool [Expr.op PrimOp.seqHead [Expr.bvar 0]],
        Expr.op PrimOp.valueAsBool
          [Expr.op PrimOp.seqHead [Expr.op PrimOp.seqTail [Expr.bvar 0]]]])

-- ---- Size, shifting, substitution, instantiation (B1A-D15) ----
--
-- Every function below is a structural recursion through the block's recursor (all twelve
-- motives, B1A-D70): total by construction, so none needs fuel and none can run out
-- (B1A-D89). Act's versions go through `Expr.enabled`, whose recursor case is the Act's
-- own, so each traversal is written once.

-- `Expr.size e`: one per constructor, plus the sizes of the parts (a literal is 1; a list,
-- an option and a pair add their elements' sizes).
def Expr.size (e : Expr) : Nat :=
  @Expr.rec
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    -- Expr
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ s => Nat.succ s)
    (fun _ _ _ sc st se => Nat.succ (Nat.add sc (Nat.add st se)))
    (fun _ _ sa sd => Nat.succ (Nat.add sa sd))
    (fun _ _ se sb => Nat.succ (Nat.add se sb))
    (fun _ _ _ sd sb => Nat.succ (Nat.add sd sb))
    (fun _ _ s => Nat.succ s)
    (fun _ s => Nat.succ s)
    -- Act
    (fun _ s => Nat.succ s) (fun _ s => Nat.succ s) (fun _ s => Nat.succ s)
    (fun _ _ s => Nat.succ s) (fun _ _ s => Nat.succ s)
    (fun _ s => Nat.succ s) (fun _ s => Nat.succ s)
    (fun _ _ sd sa => Nat.succ (Nat.add sd sa))
    (fun _ _ sd sa => Nat.succ (Nat.add sd sa))
    (fun _ _ _ sc st se => Nat.succ (Nat.add sc (Nat.add st se)))
    (fun _ _ sa sd => Nat.succ (Nat.add sa sd))
    (fun _ _ se sa => Nat.succ (Nat.add se sa))
    (fun _ _ s => Nat.succ s)
    (fun _ s => Nat.succ s)
    -- List Expr, List (Expr × Expr), Option Expr, List Act, List (Expr × Act), Option Act,
    -- List (Nat × Act)
    0 (fun _ _ sh st => Nat.add sh st)
    0 (fun _ _ sh st => Nat.add sh st)
    0 (fun _ s => s)
    0 (fun _ _ sh st => Nat.add sh st)
    0 (fun _ _ sh st => Nat.add sh st)
    0 (fun _ s => s)
    0 (fun _ _ sh st => Nat.add sh st)
    -- Expr × Expr, Expr × Act, Nat × Act
    (fun _ _ sa sb => Nat.add sa sb)
    (fun _ _ sa sb => Nat.add sa sb)
    (fun _ _ sa => sa)
    e

-- `Act.size a`: as `Expr.size` (`Expr.enabled a` adds exactly one).
def Act.size (a : Act) : Nat := Nat.pred (Expr.size (Expr.enabled a))

-- `Expr.mapVar f e k`: e with every `bvar j` that sits under k' binders of e replaced by
-- `f (k + k') j`, so `f` sees the number of binders around the variable (k at the root)
-- and decides whether j is local (below that number) or free. Every other constructor is
-- rebuilt unchanged.
def Expr.mapVar (f : Nat → Nat → Expr) (e : Expr) : Nat → Expr :=
  @Expr.rec
    (fun _ => Nat → Expr) (fun _ => Nat → Act) (fun _ => Nat → List Expr)
    (fun _ => Nat → List (Prod Expr Expr)) (fun _ => Nat → Option Expr)
    (fun _ => Nat → List Act) (fun _ => Nat → List (Prod Expr Act))
    (fun _ => Nat → Option Act) (fun _ => Nat → List (Prod Nat Act))
    (fun _ => Nat → Prod Expr Expr) (fun _ => Nat → Prod Expr Act)
    (fun _ => Nat → Prod Nat Act)
    -- Expr
    (fun v _ => Expr.lit v)
    (fun n _ => Expr.cur n)
    (fun n _ => Expr.nxt n)
    (fun j k => f k j)
    (fun n _ => Expr.pool n)
    (fun o _ rs k => Expr.op o (rs k))
    (fun _ _ _ rc rt re k => Expr.ite (rc k) (rt k) (re k))
    (fun _ _ rs rd k => Expr.caseOf (rs k) (rd k))
    (fun _ _ re rb k => Expr.letLazy (re k) (rb (Nat.succ k)))
    (fun q ds _ rds rb k => Expr.quant q (rds k) (rb (Nat.add k (List.length ds))))
    (fun i _ rs k => Expr.app i (rs k))
    (fun _ ra k => Expr.enabled (ra k))
    -- Act
    (fun _ rs k => Act.conj (rs k))
    (fun _ rs k => Act.disj (rs k))
    (fun _ re k => Act.pred (re k))
    (fun n _ re k => Act.prime n (re k))
    (fun n _ re k => Act.primeIn n (re k))
    (fun _ re k => Act.unchanged (re k))
    (fun _ re k => Act.changed (re k))
    (fun ds _ rds ra k => Act.ex (rds k) (ra (Nat.add k (List.length ds))))
    (fun ds _ rds ra k => Act.fa (rds k) (ra (Nat.add k (List.length ds))))
    (fun _ _ _ rc rt re k => Act.ite (rc k) (rt k) (re k))
    (fun _ _ rs rd k => Act.caseOf (rs k) (rd k))
    (fun _ _ re ra k => Act.letA (re k) (ra (Nat.succ k)))
    (fun i _ rs k => Act.call i (rs k))
    (fun _ rs k => Act.pchoice (rs k))
    -- List Expr
    (fun _ => List.nil) (fun _ _ rh rt k => List.cons (rh k) (rt k))
    -- List (Expr × Expr)
    (fun _ => List.nil) (fun _ _ rh rt k => List.cons (rh k) (rt k))
    -- Option Expr
    (fun _ => Option.none) (fun _ rx k => Option.some (rx k))
    -- List Act
    (fun _ => List.nil) (fun _ _ rh rt k => List.cons (rh k) (rt k))
    -- List (Expr × Act)
    (fun _ => List.nil) (fun _ _ rh rt k => List.cons (rh k) (rt k))
    -- Option Act
    (fun _ => Option.none) (fun _ rx k => Option.some (rx k))
    -- List (Nat × Act)
    (fun _ => List.nil) (fun _ _ rh rt k => List.cons (rh k) (rt k))
    -- Expr × Expr, Expr × Act, Nat × Act
    (fun _ _ ra rb k => Prod.mk (ra k) (rb k))
    (fun _ _ ra rb k => Prod.mk (ra k) (rb k))
    (fun n _ ra k => Prod.mk n (ra k))
    e

-- `Expr.enabledArg e`: the Act of `Expr.enabled a`; `Act.conj []` for any other Expr (never
-- read: `Act.mapVar` applies it to an `Expr.enabled` only).
def Expr.enabledArg (e : Expr) : Act :=
  @Expr.casesOn
    (fun _ => Act) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    e
    (fun _ => Act.conj []) (fun _ => Act.conj []) (fun _ => Act.conj [])
    (fun _ => Act.conj []) (fun _ => Act.conj []) (fun _ _ => Act.conj [])
    (fun _ _ _ => Act.conj []) (fun _ _ => Act.conj []) (fun _ _ => Act.conj [])
    (fun _ _ _ => Act.conj []) (fun _ _ => Act.conj []) (fun a => a)
    -- the other eleven types' minors: unused
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)

-- `Act.mapVar f a k`: `Expr.mapVar` on an Act.
def Act.mapVar (f : Nat → Nat → Expr) (a : Act) (k : Nat) : Act :=
  Expr.enabledArg (Expr.mapVar f (Expr.enabled a) k)

-- `shiftVar c d k j`: a variable j under k binders: local or below the cutoff c (j < c + k)
-- stays, any other is raised by d.
def shiftVar (c d : Nat) (k j : Nat) : Expr :=
  @Bool.rec (fun _ => Expr) (Expr.bvar (Nat.add j d)) (Expr.bvar j) (Nat.blt j (Nat.add c k))

-- `Expr.shift c d e` (10:168, `def-expr-shift`): every free variable of e at or above c
-- raised by d. `Expr.shift 0 k a` moves a term a from its own scope to a place k binders
-- deeper, which is what substitution does with an actual under every binder it crosses.
def Expr.shift (c d : Nat) (e : Expr) : Expr :=
  Expr.mapVar (shiftVar c d) e 0

-- `revOnto xs acc`: xs reversed, then acc.
def revOnto (xs acc : List Expr) : List Expr :=
  @List.rec Expr (fun _ => List Expr → List Expr)
    (fun acc => acc)
    (fun x _ go acc => go (List.cons x acc))
    xs acc

-- `pickArg k rs i`: the term for the free variable i (counted from the innermost
-- substituted one) under k binders, where rs are the actuals LAST FIRST: the i-th of rs
-- moved k binders deeper, or, past the actuals, the variable lowered by their number.
def pickArg (k : Nat) (rs : List Expr) : Nat → Expr :=
  @List.rec Expr (fun _ => Nat → Expr)
    (fun i => Expr.bvar (Nat.add k i))
    (fun a _ go i => @Nat.rec (fun _ => Expr) (Expr.shift 0 k a) (fun i' _ => go i') i)
    rs

-- `substVar args k j`: a variable j under k binders: local (j < k) stays; else it is the
-- actual of parameter n-1-(j-k) (n = the number of args, B1A-D15), or, past them, a free
-- variable of the enclosing scope, lowered by n.
def substVar (args : List Expr) (k j : Nat) : Expr :=
  @Bool.rec (fun _ => Expr)
    (pickArg k (revOnto args []) (Nat.sub j k))
    (Expr.bvar j)
    (Nat.blt j k)

-- `Expr.subst args e` (10:168, `def-expr-subst`): e with its n outermost free variables
-- replaced by the actuals args (parameter k of n is `bvar (n-1-k)`, B1A-D15), each shifted
-- under every binder it crosses (capture-avoiding by construction, 10:675), and every other
-- free variable lowered by n. An n-ary definition body applied to n by-name actuals is
-- `Expr.subst actuals body`; `Expr.letLazy e b` is `Expr.subst [e] b`.
def Expr.subst (args : List Expr) (e : Expr) : Expr :=
  Expr.mapVar (substVar args) e 0

-- `Act.subst args a`: `Expr.subst` on an Act (an action definition applied by name,
-- `Act.call`; `Act.letA e a` is `Act.subst [e] a`).
def Act.subst (args : List Expr) (a : Act) : Act :=
  Act.mapVar (substVar args) a 0

-- `Act.inst x a` (10:168, `def-act-inst`): a's leading binders instantiated with the values
-- x (binder k of n is `bvar (n-1-k)`), as `FairEntry.angle` (10:357) instantiates a fairness
-- entry's action with one tuple of its binder values.
def Act.inst (x : List Value) (a : Act) : Act :=
  Act.subst (List.map Expr.lit x) a

end Model
end Trust
