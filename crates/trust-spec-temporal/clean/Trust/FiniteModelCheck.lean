-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- An executable finite-model checker with a kernel-checked soundness theorem.
-- `checkScalarRows` is an ordinary Bool program the kernel evaluates by
-- reduction; `scalarSafetyOfCheck` proves that `true` implies the exact
-- `ScalarModel.safetyClaim` of FiniteModel.lean (it discharges the three
-- premises of `scalarSafetyClaimOfRows`).  `reachRows` is an untrusted
-- budgeted breadth-first search.  Soundness never depends on it, and `false`
-- proves nothing.  An island proves a model safe through either door:
--
--   theorem safe : ScalarModel.safetyClaim M := proveSafe M 64 rfl
--   theorem safe : ScalarModel.safetyClaim M := checkSafety M 64 rfl
--
-- and the kernel runs the search AND the check while it compiles the island.
-- `checkSafety` takes `checkScalarRows M (reachRows M 64) = true`, so a
-- rejection shows only `false`.  `proveSafe` takes `safetyVerdict M 64 =
-- CheckVerdict.ok` (section 6).  It runs the same trusted check in the
-- search's own index, so it costs no more, and its rejection prints WHY.
-- Prefer it.
--
-- A PROGRESS claim (the goal holds again and again on every fair run) has its
-- own two doors: `lassoVerdict` confirms a counterexample (section 8), and
--
--   theorem live : ScalarProgress.claim P := progressOfCheck P cert rfl
--
-- proves the claim from a certificate of levels, under weak and strong
-- fairness (section 9).
--
-- FUEL IS A STATE BUDGET (section 4).  Either door is designed to accept M
-- when M is in the grammar, has at most `fuel` reachable states, and satisfies
-- its invariants on every one of them.  Only soundness is a theorem; that
-- completeness is the design, not proved.  Fuel is not a depth: a model with N
-- states needs fuel >= N, whatever its BFS diameter.  Search work is linear
-- in the budget even on an infinite model, and extra fuel on a finite model
-- is free.
--
-- Grammar (everything else compiles to `none`, and the check DECLINES):
--   @nat     int, var (a declared variable), constRef (every same-named
--            constant agrees), add, sub;
--   @bool    gt, le, eq, neq (nat operands); or, and, iff (bool operands);
--            bool literals;
--   @either  ite (a bool condition; branches at the sort asked for).
--   Declined: forallIn, fnAccess, except, comprehension; two updates of one
--   variable in one action; same-named constants that disagree.  Updates of
--   undeclared names are ignored, exactly as `ActionHolds` ignores them.
--
-- READING A REJECTED ISLAND (messages as clean 0.9.0 prints them):
--   * `proveSafe`: "expected ...safetyVerdict M n = ...CheckVerdict.ok, got"
--     then one of:
--       "const mismatch: ...CheckVerdict.budgetExhausted vs ...ok": more
--         than n reachable states; raise fuel;
--       "cannot unify ...: ...CheckVerdict.invariantFails (List.cons Nat
--         (Nat.succ 0) (List.cons Nat 0 (List.nil Nat))) 0 vs ...ok":
--         reachable row [1, 0] breaks invariant #0; the MODEL is wrong;
--       "const mismatch: ...CheckVerdict.unsupported vs ...ok": the model
--         leaves the grammar.
--   * `checkSafety`: "... = true, got const mismatch: Bool.false vs
--     Bool.true".  The check ran and answered false, for one of the three
--     reasons above.  Switch the door to `proveSafe` to see which.
--   * `progressOfCheck`: "... progressCheck P cert = true, got const
--     mismatch: Bool.false vs Bool.true".  The check ran and answered false:
--     the certificate is wrong for the claim, or the claim leaves the grammar
--     (section 9 lists what the check asks of a certificate).
--   * a mismatch that shows a STUCK term, such as "rigid head/arity
--     mismatch: CheckVerdict.rec vs ...safetyVerdict" (or "Bool.rec vs
--     ...checkScalarRows", "Bool.rec vs ...progressCheck"): the elaborator
--     stopped before an answer.  Clean caps the elaborator's evaluation
--     behind one `rfl` at 10M kernel ticks.
--     Nothing was decided: shrink the model, or the fuel on an infinite one.
--     Measured: Lockstep with 8193 states stops at 10,000,761 ticks after
--     102 s (so did the previous checker).
--   * "Kernel check failed ... got Bool.false = Bool.false": the elaborator
--     agreed, but the kernel's top-level lazy-delta loop gave up (see the
--     cost discipline).  The doors are built so that this does not happen;
--     state claims through them, not through internal definitions such as
--     `checkCompiled` or `searchCompiled`.
-- Capacity, measured on clean 0.9.0 (`peak_decl_ticks`, CPU on a loaded host;
-- `proveSafe` / `checkSafety`; the previous checker in brackets):
--   * Lockstep, 2 variables, 2 actions: 1025 states 0.84M / 0.96M ticks
--     (13 s) [0.87M]; 4097 states 5.55M / 5.70M (54 / 59 s) [7.09M, 67 s];
--     6145 states 8.79M (80 s); 8193 states stop at the cap.  With
--     `--max-cache-entries 0`: 4097 states 3.97M / 4.49M, and 8193 pass at
--     7.89M (86 s, 3.0 GB).  A passing claim can report more than 10M,
--     because the kernel re-checks what the elaborator evaluated;
--   * 3-D cube, 3 variables, 4 actions: 512 states 0.53M / 0.59M (12 s);
--     4096 states 7.77M / 7.75M (97 / 105 s) [8.50M, 126 s].
--   Instructions retired, model-only file subtracted, Lockstep: 1025 states
--   78.5 / 82.8 G [100.8]; 4097 states 426 / 445 G [555].  Past about 2k
--   states the default memo cache (100k entries) cannot hold one evaluation,
--   and the claim is evaluated twice.  `--max-cache-entries 0` then saves
--   14% of the instructions and 21-28% of the ticks (4097 states), at about
--   0.4 MB per state.
--
-- Kernel-cost discipline (measured):
--   * names are resolved ONCE (`compileModel`); the per-row loop sees only
--     positions (`CExpr.slot`), literals and Nat.beq/Nat.ble -- no String;
--   * everything the search and the check HOLD is a value.  Rows, hashes,
--     budgets, index trees, the row list's spine and the compiled model are
--     produced in continuation-passing style (`forceNat`, `forceRow`,
--     `lookupInsertK`, `insertK`, `takeTreeK`, `forceSpine`, `forceCM`).  The
--     kernel is lazy, so without this each BFS row is a term DAG over its
--     predecessors (about 2^depth paths), the index is a chain of insert
--     thunks, and the check re-reads the search term.  All of that is cheap
--     only while the memo cache (default 100k entries, sliding window) keeps
--     it.  Measured consequences: a thrash cliff past about 1000 states, the
--     whole search re-run once its cached result was evicted, and
--     exponential printing or defeq of verdict rows.  A row list handed to
--     `checkScalarRows` keeps its entries as given: literal rows and the
--     search's rows are values;
--   * the check never re-inserts what the search inserted.  `proveSafe`
--     checks in the search's final tree, and its rows are that tree's rows.
--     `checkScalarRows` lays out rows that ascend in walk order (`reachRows`
--     returns them so) as a balanced tree in one pass with no comparison
--     (`indexK`); only other lists are inserted row by row.  Measured at
--     1025 states: the insertion rebuild was 18 G of a 45 G check; the
--     balanced layout is 4 G, and the shared tree 0;
--   * every door (`checkScalarRows`, `reachRows`, `safetyVerdict`,
--     `explainCheck`) is a recursor over its computation, an identity, so
--     the kernel reduces the whole computation as a MAJOR PREMISE, with full
--     whnf.  The kernel's top-level definitional-equality check instead runs
--     a lazy-delta loop capped at about 10 000 unfoldings.  At top level,
--     each continuation step whose head is a definition would spend one;
--   * inside the loops, control is raw recursors (List.rec / Bool.rec /
--     Option.rec / Nat.rec / RIndex.rec), never `&&`/`||`/`if` or match-defs.
--     The tree-walk step is written out inline at each use, not called as
--     the `steer` definition: measured, that cuts ticks by about a fifth;
--   * membership is a hash-steered search tree whose ONLY proof-carrying
--     answer is `rowEq`; hash, order and tree shape are untrusted steering.

namespace Trust
namespace Temporal
namespace FiniteModel

-- ===== 1. positional compiled form and its evaluator =====

inductive CExpr where
  | lit : Nat → CExpr
  | slot : Nat → CExpr
  | add : CExpr → CExpr → CExpr
  | sub : CExpr → CExpr → CExpr
  | gt : CExpr → CExpr → CExpr
  | le : CExpr → CExpr → CExpr
  | eq : CExpr → CExpr → CExpr
  | ite : CExpr → CExpr → CExpr → CExpr
  | neq : CExpr → CExpr → CExpr
  | bor : CExpr → CExpr → CExpr
  | band : CExpr → CExpr → CExpr
  | biff : CExpr → CExpr → CExpr
  | blit : Bool → CExpr

inductive Srt where
  | nat
  | bool

def slotAt (row : List Nat) : Nat → Nat :=
  @List.rec Nat (fun _ => Nat → Nat) (fun _ => 0)
    (fun v _ ih i => @Nat.rec (fun _ => Nat) v (fun j _ => ih j) i) row

def iffB (a b : Bool) : Bool :=
  @Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) true false b) b a

def evalV (row : List Nat) (c : CExpr) : Value :=
  @CExpr.rec (fun _ => Value)
    (fun n => Value.nat n)
    (fun i => Value.nat (slotAt row i))
    (fun _ _ a b => Value.nat (valueNatProjection a + valueNatProjection b))
    (fun _ _ a b => Value.nat (valueNatProjection a - valueNatProjection b))
    (fun _ _ a b => Value.bool
      (@Bool.rec (fun _ => Bool) true false
        (Nat.ble (valueNatProjection a) (valueNatProjection b))))
    (fun _ _ a b => Value.bool (Nat.ble (valueNatProjection a) (valueNatProjection b)))
    (fun _ _ a b => Value.bool (Nat.beq (valueNatProjection a) (valueNatProjection b)))
    (fun _ _ _ c t e => @Bool.rec (fun _ => Value) e t (valueBoolProjection c))
    (fun _ _ a b => Value.bool
      (@Bool.rec (fun _ => Bool) true false
        (Nat.beq (valueNatProjection a) (valueNatProjection b))))
    (fun _ _ a b => Value.bool (valueBoolProjection a || valueBoolProjection b))
    (fun _ _ a b => Value.bool (valueBoolProjection a && valueBoolProjection b))
    (fun _ _ a b => Value.bool (iffB (valueBoolProjection a) (valueBoolProjection b)))
    (fun t => Value.bool t)
    c

def evalN (row : List Nat) (c : CExpr) : Nat := valueNatProjection (evalV row c)
def evalB (row : List Nat) (c : CExpr) : Bool := valueBoolProjection (evalV row c)


-- ===== 2. compile: the only phase that compares names =====

def lookupSlot (vars : List StateVar) (name : String) : Option Nat :=
  @List.rec StateVar (fun _ => Option Nat) none
    (fun v _ ih =>
      @Bool.rec (fun _ => Option Nat)
        (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i)) ih)
        (some 0)
        (decide (v.name = name)))
    vars

-- First value bound to `name`, and every same-named constant agrees with it.
def firstConst (consts : List Constant) (name : String) : Option Nat :=
  @List.rec Constant (fun _ => Option Nat) none
    (fun c _ ih => @Bool.rec (fun _ => Option Nat) ih (some c.value) (decide (c.name = name)))
    consts

def constsAgree (consts : List Constant) (name : String) (value : Nat) : Bool :=
  @List.rec Constant (fun _ => Bool) true
    (fun c _ ih =>
      @Bool.rec (fun _ => Bool) ih
        (@Bool.rec (fun _ => Bool) false ih (Nat.beq c.value value))
        (decide (c.name = name)))
    consts

def constOf (consts : List Constant) (name : String) : Option Nat :=
  @Option.rec Nat (fun _ => Option Nat) none
    (fun v => @Bool.rec (fun _ => Option Nat) none (some v) (constsAgree consts name v))
    (firstConst consts name)

def bind2 (o1 o2 : Option CExpr) (k : CExpr → CExpr → CExpr) : Option CExpr :=
  @Option.rec CExpr (fun _ => Option CExpr) none
    (fun a => @Option.rec CExpr (fun _ => Option CExpr) none (fun b => some (k a b)) o2) o1

def bind3 (o1 o2 o3 : Option CExpr) (k : CExpr → CExpr → CExpr → CExpr) : Option CExpr :=
  @Option.rec CExpr (fun _ => Option CExpr) none
    (fun a => bind2 o2 o3 (k a)) o1

def compileS (vars : List StateVar) (consts : List Constant) (e : ScalarExpr) :
    Srt → Option CExpr :=
  @ScalarExpr.rec (fun _ => Srt → Option CExpr)
    (fun n s => @Srt.rec (fun _ => Option CExpr) (some (CExpr.lit n)) none s)
    (fun name s => @Srt.rec (fun _ => Option CExpr)
      (@Option.rec Nat (fun _ => Option CExpr) none (fun i => some (CExpr.slot i))
        (lookupSlot vars name)) none s)
    (fun name s => @Srt.rec (fun _ => Option CExpr)
      (@Option.rec Nat (fun _ => Option CExpr) none (fun v => some (CExpr.lit v))
        (constOf consts name)) none s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) (bind2 (l Srt.nat) (r Srt.nat) CExpr.add) none s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) (bind2 (l Srt.nat) (r Srt.nat) CExpr.sub) none s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.nat) (r Srt.nat) CExpr.gt) s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.nat) (r Srt.nat) CExpr.le) s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.nat) (r Srt.nat) CExpr.eq) s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.nat) (r Srt.nat) CExpr.neq) s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.bool) (r Srt.bool) CExpr.bor) s)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.bool) (r Srt.bool) CExpr.band) s)
    (fun _ _ _ c t f s => bind3 (c Srt.bool) (t s) (f s) CExpr.ite)
    (fun _ _ l r s => @Srt.rec (fun _ => Option CExpr) none (bind2 (l Srt.bool) (r Srt.bool) CExpr.biff) s)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ => none)
    (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun b s => @Srt.rec (fun _ => Option CExpr) none (some (CExpr.blit b)) s)
    e

def cTrue : CExpr := CExpr.le (CExpr.lit 0) (CExpr.lit 0)

def compileGuard (vars : List StateVar) (consts : List Constant) (g : Guard) : Option CExpr :=
  @Guard.rec (fun _ => Option CExpr) (some cTrue)
    (fun e => compileS vars consts e Srt.bool) g

inductive Found where
  | none
  | one : ScalarExpr → Found
  | dup

def findU (us : List Update) (name : String) : Found :=
  @List.rec Update (fun _ => Found) Found.none
    (fun u _ ih =>
      @Bool.rec (fun _ => Found) ih
        (@Found.rec (fun _ => Found) (Found.one u.value) (fun _ => Found.dup) Found.dup ih)
        (decide (u.var = name)))
    us

def consOpt (x : Option CExpr) (o : Option (List (Option CExpr))) : Option (List (Option CExpr)) :=
  @Option.rec (List (Option CExpr)) (fun _ => Option (List (Option CExpr))) none
    (fun xs => some (x :: xs)) o

def compileUpds (vars : List StateVar) (consts : List Constant) (us : List Update)
    (vs : List StateVar) : Option (List (Option CExpr)) :=
  @List.rec StateVar (fun _ => Option (List (Option CExpr))) (some [])
    (fun v _ ih =>
      @Found.rec (fun _ => Option (List (Option CExpr)))
        (consOpt none ih)
        (fun e => @Option.rec CExpr (fun _ => Option (List (Option CExpr))) none
            (fun c => consOpt (some c) ih) (compileS vars consts e Srt.nat))
        none
        (findU us v.name))
    vs

structure CAction where
  guard : CExpr
  upd : List (Option CExpr)

def compileAction (vars : List StateVar) (consts : List Constant) (a : Action) : Option CAction :=
  @Option.rec CExpr (fun _ => Option CAction) none
    (fun g => @Option.rec (List (Option CExpr)) (fun _ => Option CAction) none
      (fun u => some (CAction.mk g u)) (compileUpds vars consts a.updates vars))
    (compileGuard vars consts a.guard)

def mapOpt {α β : Type} (f : α → Option β) (xs : List α) : Option (List β) :=
  @List.rec α (fun _ => Option (List β)) (some [])
    (fun x _ ih => @Option.rec β (fun _ => Option (List β)) none
      (fun y => @Option.rec (List β) (fun _ => Option (List β)) none
        (fun ys => some (y :: ys)) ih) (f x))
    xs

structure CModel where
  init : List Nat
  actions : List CAction
  invs : List CExpr

def initRow (vars : List StateVar) : List Nat :=
  @List.rec StateVar (fun _ => List Nat) [] (fun v _ ih => v.init :: ih) vars

def compileModel (model : ScalarModel) : Option CModel :=
  @Option.rec (List CAction) (fun _ => Option CModel) none
    (fun acts => @Option.rec (List CExpr) (fun _ => Option CModel) none
      (fun invs => some (CModel.mk (initRow model.variables) acts invs))
      (mapOpt (fun inv : Invariant => compileS model.variables model.constants inv.value Srt.bool)
        model.invariants))
    (mapOpt (compileAction model.variables model.constants) model.actions)


-- ===== 3. the hot loop =====

def rowEq (a : List Nat) : List Nat → Bool :=
  @List.rec Nat (fun _ => List Nat → Bool)
    (fun b => @List.rec Nat (fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => @List.rec Nat (fun _ => Bool) false
      (fun y ys _ => @Bool.rec (fun _ => Bool) false (ih ys) (Nat.beq x y)) b)
    a


-- Hash-ordered search tree over rows.  Only `rowEq` answers carry proof
-- weight; the hash and the order merely steer the walk.
inductive RIndex where
  | leaf
  | node : RIndex → Nat → List Nat → RIndex → RIndex

-- Steering hash.  Each coordinate enters through the Weyl multiplier
-- 2654435761 (about p / golden ratio), and the result is cubed mod p, which is
-- a bijection because 3 does not divide p - 1.  The tree is unbalanced and
-- filled in search order, so related rows such as [0], [1], [2], ... must get
-- unrelated keys.  An earlier hash was linear in a lone coordinate, and on
-- one-variable models it turned the tree into a list and the check into
-- O(n^2).  Proofs never look inside this function.
def rowHash (row : List Nat) : Nat :=
  (fun h => Nat.mod (h * Nat.mod (h * h) 4294967291) 4294967291)
    (@List.rec Nat (fun _ => Nat) 7
      (fun v _ ih => Nat.mod (ih * 1000003 + v * 2654435761 + 1) 4294967291) row)

-- lexicographic row order (only used for steering among equal hashes)
def rowLt (a : List Nat) : List Nat → Bool :=
  @List.rec Nat (fun _ => List Nat → Bool)
    (fun b => @List.rec Nat (fun _ => Bool) false (fun _ _ _ => true) b)
    (fun x _ ih b => @List.rec Nat (fun _ => Bool) false
      (fun y ys _ => @Bool.rec (fun _ => Bool)
          (Nat.blt x y)
          (ih ys) (Nat.beq x y)) b)
    a

-- One step of every walk.  Go left if h < h', right if h' < h; on equal
-- hashes stop `here` if the rows are equal, else go by row order.  The usual
-- case costs one Nat.blt to go left and two to go right.  Every walk below
-- spells this step out inline; measured, that costs about a fifth fewer ticks
-- than calling `steer`.  The proofs state facts about `steer`, and the kernel
-- unfolds it to match the inline copies.  They use only `steerSel`: `here` is
-- chosen only when `rowEq r r'` holds.
def steer {β : Type} (goL here goR : β) (h : Nat) (r : List Nat) (h' : Nat) (r' : List Nat) : β :=
  @Bool.rec (fun _ => β)
    (@Bool.rec (fun _ => β)
      (@Bool.rec (fun _ => β) (@Bool.rec (fun _ => β) goR goL (rowLt r r')) here (rowEq r r'))
      goR (Nat.blt h' h))
    goL (Nat.blt h h')

def indexMemH (h : Nat) (r : List Nat) (t : RIndex) : Bool :=
  @RIndex.rec (fun _ => Bool) false
    (fun _ h' r' _ ihl ihr =>
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool)
          (@Bool.rec (fun _ => Bool) (@Bool.rec (fun _ => Bool) ihr ihl (rowLt r r')) true (rowEq r r'))
          ihr (Nat.blt h' h))
        ihl (Nat.blt h h'))
    t

def indexMem (r : List Nat) (t : RIndex) : Bool := indexMemH (rowHash r) r t

def indexInsertH (h : Nat) (r : List Nat) (t : RIndex) : RIndex :=
  @RIndex.rec (fun _ => RIndex) (RIndex.node RIndex.leaf h r RIndex.leaf)
    (fun l h' r' rr ihl ihr =>
      @Bool.rec (fun _ => RIndex)
        (@Bool.rec (fun _ => RIndex)
          (@Bool.rec (fun _ => RIndex) (@Bool.rec (fun _ => RIndex) (RIndex.node l h' r' ihr) (RIndex.node ihl h' r' rr) (rowLt r r')) (RIndex.node l h' r' rr) (rowEq r r'))
          (RIndex.node l h' r' ihr) (Nat.blt h' h))
        (RIndex.node ihl h' r' rr) (Nat.blt h h'))
    t

-- the insertion-built index: `indexK`'s fallback (proofs reason about this)
def buildIndex (rows : List (List Nat)) : RIndex :=
  @List.rec (List Nat) (fun _ => RIndex) RIndex.leaf
    (fun r _ ih => indexInsertH (rowHash r) r ih) rows

-- Value forcing, in continuation-passing style.  The kernel is lazy: a row
-- that one step computes from the previous one stays a term that mentions the
-- previous row (twice, in `succRow row upd row`).  After k steps it is a DAG
-- with about 2^k paths, and its cost depends on the memo cache.  `forceNat`
-- makes the kernel reduce a number to a literal before the continuation runs,
-- and the continuation receives `Nat.succ <literal>`, a closed constant-size
-- term.  So every row, hash, budget and tree the search or the check holds is
-- a VALUE, independent of the memo cache, and the verdict rows print small.
-- `forceNatEq`, `forceRowEq`, `insertKEq` and `buildIndexKEq` prove that each
-- forced form equals the plain one.
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  @Nat.rec (fun _ => α) (k 0) (fun p _ => k (Nat.succ p)) n

def forceRow {α : Type} (row : List Nat) : (List Nat → α) → α :=
  @List.rec Nat (fun _ => (List Nat → α) → α) (fun k => k [])
    (fun v _ ih k => forceNat v (fun v' => ih (fun vs' => k (v' :: vs')))) row

-- The row list's spine as a value.  The check reads its rows twice (index,
-- then rows), and `rows` is usually the search term itself, which a cache
-- eviction in between would make the kernel run again.  The entries are kept
-- as given, not rebuilt: the search's rows are values already, and keeping
-- the very terms the search evaluated lets the memo cache serve the check's
-- guard and successor work (measured: 3% fewer instructions than rebuilding
-- each row).  Literal rows are values too.
def forceSpine {α : Type} (rows : List (List Nat)) : (List (List Nat) → α) → α :=
  @List.rec (List Nat) (fun _ => (List (List Nat) → α) → α) (fun k => k [])
    (fun r _ ih k => ih (fun rs => k (r :: rs))) rows

-- the compiled model as a value: the per-row loop reads guards, updates and
-- invariants millions of times, and must not depend on the memo cache
-- keeping the compiler's thunks
def forceBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  @Bool.rec (fun _ => α) (k false) (k true) b

def forceCExpr {α : Type} (c : CExpr) : (CExpr → α) → α :=
  @CExpr.rec (fun _ => (CExpr → α) → α)
    (fun n k => forceNat n (fun n' => k (CExpr.lit n')))
    (fun i k => forceNat i (fun i' => k (CExpr.slot i')))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.add a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.sub a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.gt a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.le a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.eq a b))))
    (fun _ _ _ fc ft fe k => fc (fun c => ft (fun t => fe (fun e => k (CExpr.ite c t e)))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.neq a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.bor a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.band a b))))
    (fun _ _ fa fb k => fa (fun a => fb (fun b => k (CExpr.biff a b))))
    (fun t k => forceBool t (fun t' => k (CExpr.blit t')))
    c

def forceList {α β : Type} (f : β → (β → α) → α) (xs : List β) : (List β → α) → α :=
  @List.rec β (fun _ => (List β → α) → α) (fun k => k [])
    (fun x _ ih k => f x (fun x' => ih (fun xs' => k (x' :: xs')))) xs

def forceUpd {α : Type} (u : Option CExpr) (k : Option CExpr → α) : α :=
  @Option.rec CExpr (fun _ => α) (k none) (fun c => forceCExpr c (fun c' => k (some c'))) u

def forceAction {α : Type} (ca : CAction) (k : CAction → α) : α :=
  @CAction.rec (fun _ => α)
    (fun g u => forceCExpr g (fun g' => forceList forceUpd u (fun u' => k (CAction.mk g' u'))))
    ca

def forceCM {α : Type} (cm : CModel) (k : CModel → α) : α :=
  @CModel.rec (fun _ => α)
    (fun i acts invs => forceRow i (fun i' => forceList forceAction acts (fun acts' =>
      forceList forceCExpr invs (fun invs' => k (CModel.mk i' acts' invs')))))
    cm

-- `indexInsertH`, rebuilding the walked path as a value
def insertK {α : Type} (h : Nat) (r : List Nat) (t : RIndex) : (RIndex → α) → α :=
  @RIndex.rec (fun _ => (RIndex → α) → α)
    (fun k => k (RIndex.node RIndex.leaf h r RIndex.leaf))
    (fun l h' r' rr ihl ihr k =>
      @Bool.rec (fun _ => α)
        (@Bool.rec (fun _ => α)
          (@Bool.rec (fun _ => α) (@Bool.rec (fun _ => α) (ihr (fun rr' => k (RIndex.node l h' r' rr'))) (ihl (fun l' => k (RIndex.node l' h' r' rr))) (rowLt r r')) (k (RIndex.node l h' r' rr)) (rowEq r r'))
          (ihr (fun rr' => k (RIndex.node l h' r' rr'))) (Nat.blt h' h))
        (ihl (fun l' => k (RIndex.node l' h' r' rr))) (Nat.blt h h'))
    t

-- `buildIndex`, as a value tree
def buildIndexK {α : Type} (rows : List (List Nat)) : (RIndex → α) → α :=
  @List.rec (List Nat) (fun _ => (RIndex → α) → α) (fun k => k RIndex.leaf)
    (fun r _ ih k => ih (fun t => forceNat (rowHash r) (fun h => insertK h r t k))) rows

-- membership with the probe row and its hash forced once
def memK (t : RIndex) (s : List Nat) : Bool :=
  forceRow s (fun s' => forceNat (rowHash s') (fun h => indexMemH h s' t))

-- The rows of an index in walk order (left, node, right).  The search hands
-- the check its rows in this order, so the check can rebuild the index
-- without one comparison (`indexK`).
def treeRowsAcc (t : RIndex) : List (List Nat) → List (List Nat) :=
  @RIndex.rec (fun _ => List (List Nat) → List (List Nat)) (fun acc => acc)
    (fun _ _ r _ ihl ihr acc => ihl (r :: ihr acc)) t

-- `rows` strictly ascend in walk order after (h0, r0): steering only
def ascAfter (rows : List (List Nat)) : Nat → List Nat → Bool :=
  @List.rec (List Nat) (fun _ => Nat → List Nat → Bool) (fun _ _ => true)
    (fun r _ ih h0 r0 => forceNat (rowHash r) (fun h =>
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool) false
          (@Bool.rec (fun _ => Bool) false (ih h r) (rowLt r0 r)) (Nat.beq h0 h))
        (ih h r) (Nat.blt h0 h)))
    rows

-- A tree of depth at most `d` over the next rows of `xs`, in list order; the
-- continuation gets the tree and the rows left over.
def takeTreeK {α : Type} (d : Nat) :
    List (List Nat) → (RIndex → List (List Nat) → α) → α :=
  @Nat.rec (fun _ => List (List Nat) → (RIndex → List (List Nat) → α) → α)
    (fun xs k => k RIndex.leaf xs)
    (fun _ ih xs k => ih xs (fun l xs1 =>
      @List.rec (List Nat) (fun _ => α) (k l [])
        (fun x xs2 _ => ih xs2 (fun r xs3 =>
          forceNat (rowHash x) (fun h => k (RIndex.node l h x r) xs3)))
        xs1))
    d

-- `t` has depth `d`; the next row and a depth-`d` tree after it make a tree
-- of depth d + 1.  Each round eats at least one row of `fuel`, so `fuel =
-- rows` never runs out (about log2 n rounds).
def growK {α : Type} (fuel : List (List Nat)) :
    RIndex → Nat → List (List Nat) → (RIndex → α) → α :=
  @List.rec (List Nat) (fun _ => RIndex → Nat → List (List Nat) → (RIndex → α) → α)
    (fun t _ _ k => k t)
    (fun _ _ ih t d xs k =>
      @List.rec (List Nat) (fun _ => α) (k t)
        (fun x xs' _ => takeTreeK d xs' (fun r xs'' =>
          forceNat (rowHash x) (fun h => ih (RIndex.node t h x r) (Nat.succ d) xs'' k)))
        xs)
    fuel

-- The check's index over `rows`.  Rows that ascend in walk order (the
-- search's, `reachRows`) are laid out as a balanced tree in one pass, with
-- no comparison; any other list is inserted row by row (`buildIndexK`).
-- Either way the proofs need only that every row in the tree is in `rows`.
def indexK {α : Type} (rows : List (List Nat)) (k : RIndex → α) : α :=
  @List.rec (List Nat) (fun _ => α) (k RIndex.leaf)
    (fun r rest _ => forceNat (rowHash r) (fun h =>
      @Bool.rec (fun _ => α) (buildIndexK rows k) (growK rows RIndex.leaf 0 rows k)
        (ascAfter rest h r)))
    rows

def succRow (full : List Nat) (upd : List (Option CExpr)) : List Nat → List Nat :=
  @List.rec (Option CExpr) (fun _ => List Nat → List Nat) (fun _ => [])
    (fun u _ ih row => @List.rec Nat (fun _ => List Nat) []
      (fun v vs _ => (@Option.rec CExpr (fun _ => Nat) v (fun c => evalN full c) u) :: ih vs) row)
    upd

def allB {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  @List.rec α (fun _ => Bool) true
    (fun x _ prev => @Bool.rec (fun _ => Bool) false prev (p x)) xs


def actionOk (t : RIndex) (row : List Nat) (ca : CAction) : Bool :=
  @Bool.rec (fun _ => Bool) true (memK t (succRow row ca.upd row)) (evalB row ca.guard)

def rowOk (cm : CModel) (t : RIndex) (row : List Nat) : Bool :=
  @Bool.rec (fun _ => Bool) false (allB (fun ci => evalB row ci) cm.invs)
    (allB (actionOk t row) cm.actions)

def checkIndexed (cm : CModel) (rows : List (List Nat)) (t : RIndex) : Bool :=
  @Bool.rec (fun _ => Bool) false (allB (rowOk cm t) rows) (memK t cm.init)

def checkCompiled (cm : CModel) (rows : List (List Nat)) : Bool :=
  forceSpine rows (fun rs => indexK rs (checkIndexed cm rs))

def checkCore (model : ScalarModel) (rows : List (List Nat)) : Bool :=
  @Option.rec CModel (fun _ => Bool) false (fun cm => forceCM cm (fun cm' => checkCompiled cm' rows))
    (compileModel model)

-- The door is `Bool.rec false true core`, an identity, so the whole check
-- is a recursor MAJOR PREMISE, which the kernel reduces with full whnf.  The
-- kernel's top-level definitional-equality check instead goes through a
-- lazy-delta loop capped at about 10 000 unfoldings, and every CPS step whose
-- head is a definition (`forceNat`, `insertK`, ...) would spend one.  Measured:
-- without the wrapper, a 4096-row check passed the elaborator, then failed
-- in the kernel with `Bool.false = Bool.false`.
def checkScalarRows (model : ScalarModel) (rows : List (List Nat)) : Bool :=
  @Bool.rec (fun _ => Bool) false true (checkCore model rows)


-- ===== 4. untrusted budgeted breadth-first search =====
--
-- FUEL IS A STATE BUDGET.  `reachRows model fuel` collects at most `fuel`
-- rows.  A model with at most `fuel` reachable states (so its BFS diameter is
-- below `fuel`) is explored completely.  If the search finds a new row once
-- the budget is spent, it stops and returns what it holds; that list is not
-- closed, so the check answers false.  Hence
--   proveSafe M fuel rfl (or checkSafety M fuel rfl)  is accepted  iff  M is
--   in the grammar, has at most `fuel` reachable states, and satisfies its
--   invariants on all of them.
-- Search and check work is linear in the budget whatever the model.  On an
-- infinite or unexpectedly large model, a large `fuel` therefore costs time
-- in proportion, and then stops.  It never runs away.  Extra fuel on a finite
-- model is free.  Choose fuel = the expected state count, with headroom;
-- `safetyVerdict` reports `budgetExhausted` when it was too small.

-- The search's answer.  `done t all`: the rows are closed under the actions;
-- `t` indexes them and `all` lists them newest first (BFS order, which the
-- diagnostics use).  `exhausted all`: cut off by the budget.
inductive Search where
  | done : RIndex → List (List Nat) → Search
  | exhausted : List (List Nat) → Search

-- a closed search hands over its rows in walk order (`treeRowsAcc`), so the
-- check lays its index out in one pass (`indexK`)
def searchRowsOf (s : Search) : List (List Nat) :=
  @Search.rec (fun _ => List (List Nat)) (fun t _ => treeRowsAcc t []) (fun rows => rows) s

-- one walk: `found` if `r` is present, else the continuation gets the tree
-- with `r` added
def lookupInsertK {α : Type} (h : Nat) (r : List Nat) (t : RIndex) (found : α) :
    (RIndex → α) → α :=
  @RIndex.rec (fun _ => (RIndex → α) → α)
    (fun k => k (RIndex.node RIndex.leaf h r RIndex.leaf))
    (fun l h' r' rr ihl ihr k =>
      @Bool.rec (fun _ => α)
        (@Bool.rec (fun _ => α)
          (@Bool.rec (fun _ => α) (@Bool.rec (fun _ => α) (ihr (fun rr' => k (RIndex.node l h' r' rr'))) (ihl (fun l' => k (RIndex.node l' h' r' rr))) (rowLt r r')) found (rowEq r r'))
          (ihr (fun rr' => k (RIndex.node l h' r' rr'))) (Nat.blt h' h))
        (ihl (fun l' => k (RIndex.node l' h' r' rr))) (Nat.blt h h'))
    t

-- search state, threaded through continuations:
--   seen (index of every row so far), fresh (next frontier),
--   all (every row so far, newest first), budget (rows still allowed)
def visitK (k : RIndex → List (List Nat) → List (List Nat) → Nat → Search)
    (c : List Nat) (seen : RIndex) (fresh all : List (List Nat)) (budget : Nat) : Search :=
  forceRow c (fun c' =>
    forceNat (rowHash c') (fun h =>
      lookupInsertK h c' seen (k seen fresh all budget)
        (fun seen' =>
          @Nat.rec (fun _ => Search) (Search.exhausted all)
            (fun b _ => k seen' (c' :: fresh) (c' :: all) b)
            budget)))

def collectK (k : RIndex → List (List Nat) → List (List Nat) → Nat → Search)
    (cands : List (List Nat)) : RIndex → List (List Nat) → List (List Nat) → Nat → Search :=
  @List.rec (List Nat) (fun _ => RIndex → List (List Nat) → List (List Nat) → Nat → Search)
    k (fun c _ ih => visitK ih c) cands

def succsOf (cm : CModel) (row : List Nat) : List (List Nat) :=
  @List.rec CAction (fun _ => List (List Nat)) []
    (fun ca _ ih => @Bool.rec (fun _ => List (List Nat)) ih (succRow row ca.upd row :: ih)
      (evalB row ca.guard))
    cm.actions

def expandK (cm : CModel) (k : RIndex → List (List Nat) → List (List Nat) → Nat → Search)
    (frontier : List (List Nat)) : RIndex → List (List Nat) → List (List Nat) → Nat → Search :=
  @List.rec (List Nat) (fun _ => RIndex → List (List Nat) → List (List Nat) → Nat → Search)
    k (fun r _ ih => collectK ih (succsOf cm r)) frontier

-- at most `layers` BFS layers (the budget already bounds them; this is the
-- structural measure)
def layersK (cm : CModel) (layers : Nat) :
    RIndex → List (List Nat) → List (List Nat) → Nat → Search :=
  @Nat.rec (fun _ => RIndex → List (List Nat) → List (List Nat) → Nat → Search)
    (fun seen frontier all _ =>
      @List.rec (List Nat) (fun _ => Search) (Search.done seen all)
        (fun _ _ _ => Search.exhausted all) frontier)
    (fun _ ih seen frontier all budget =>
      @List.rec (List Nat) (fun _ => Search) (Search.done seen all)
        (fun _ _ _ => expandK cm ih frontier seen [] all budget)
        frontier)
    layers

def searchCompiled (cm : CModel) (fuel : Nat) : Search :=
  @Nat.rec (fun _ => Search) (Search.exhausted [])
    (fun b _ => forceRow cm.init (fun i => forceNat (rowHash i) (fun h =>
      layersK cm fuel (RIndex.node RIndex.leaf h i RIndex.leaf) [i] [i] b)))
    fuel

def searchOf (model : ScalarModel) (fuel : Nat) : Search :=
  @Option.rec CModel (fun _ => Search) (Search.exhausted [])
    (fun cm => forceCM cm (fun cm' => searchCompiled cm' fuel)) (compileModel model)

-- (a recursor over the search, for the same reason as `checkScalarRows`)
def reachRows (model : ScalarModel) (fuel : Nat) : List (List Nat) :=
  searchRowsOf (searchOf model fuel)

-- ===== 5. soundness =====

theorem boolRecAnd (a b : Bool)
    (h : @Bool.rec (fun _ => Bool) false b a = true) : a = true ∧ b = true :=
  @Bool.rec (fun a => @Bool.rec (fun _ => Bool) false b a = true → a = true ∧ b = true)
    (fun k => Bool.noConfusion k) (fun k => ⟨rfl, k⟩) a h

theorem boolRecImp (a b : Bool)
    (h : @Bool.rec (fun _ => Bool) true b a = true) (ha : a = true) : b = true :=
  @Bool.rec (fun a => @Bool.rec (fun _ => Bool) true b a = true → a = true → b = true)
    (fun _ k => Bool.noConfusion k) (fun k _ => k) a h ha

theorem natBeqSound (a b : Nat) (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true a b h

theorem rowEqSound (a : List Nat) : ∀ b : List Nat, rowEq a b = true → a = b :=
  @List.rec Nat (fun a => ∀ b : List Nat, rowEq a b = true → a = b)
    (fun b => @List.rec Nat (fun b => rowEq [] b = true → [] = b)
        (fun _ => rfl)
        (fun _ _ _ h => Bool.noConfusion h) b)
    (fun x xs ih b => @List.rec Nat (fun b => rowEq (x :: xs) b = true → x :: xs = b)
        (fun h => Bool.noConfusion h)
        (fun y ys _ h =>
          (fun both =>
            Eq.trans
              (congrArg (fun z => z :: xs) (natBeqSound x y both.1))
              (congrArg (fun zs => y :: zs) (ih ys both.2)))
          (boolRecAnd (Nat.beq x y) (rowEq xs ys) h))
        b)
    a

theorem allBSound {α : Type} (p : α → Bool) (xs : List α)
    (h : allB p xs = true) : ∀ x : α, Member x xs → p x = true :=
  fun x member =>
    @Member.rec α x
      (fun list _ => allB p list = true → p x = true)
      (fun tail k => (boolRecAnd (p x) (allB p tail) k).1)
      (fun hd tail _ ih k => ih (boolRecAnd (p hd) (allB p tail) k).2)
      xs member h

theorem optionRecSome {α : Type} (o : Option α) (f : α → Bool)
    (h : @Option.rec α (fun _ => Bool) false f o = true) :
    ∃ x : α, o = some x ∧ f x = true :=
  @Option.rec α
    (fun o => @Option.rec α (fun _ => Bool) false f o = true →
      ∃ x : α, o = some x ∧ f x = true)
    (fun k => Bool.noConfusion k)
    (fun x k => ⟨x, rfl, k⟩)
    o h

theorem boolRecId (b : Bool) : @Bool.rec (fun _ => Bool) false true b = b :=
  @Bool.rec (fun b => @Bool.rec (fun _ => Bool) false true b = b) rfl rfl b

theorem compiledOfCheck (model : ScalarModel) (rows : List (List Nat))
    (h : checkScalarRows model rows = true) :
    ∃ cm : CModel, compileModel model = some cm ∧
      forceCM cm (fun cm' => checkCompiled cm' rows) = true :=
  optionRecSome (compileModel model) (fun cm => forceCM cm (fun cm' => checkCompiled cm' rows))
    (Eq.trans (Eq.symm (boolRecId (checkCore model rows))) h)
theorem boolCases (b : Bool) : b = true ∨ b = false :=
  @Bool.rec (fun b => b = true ∨ b = false) (Or.inr rfl) (Or.inl rfl) b

theorem someInj {α : Type} {a b : α} (h : some a = some b) : a = b :=
  congrArg (fun o => @Option.rec α (fun _ => α) a (fun x => x) o) h

theorem noneNeSome {α : Type} {a : α} (h : (none : Option α) = some a) : False :=
  Bool.noConfusion (congrArg (fun o => @Option.rec α (fun _ => Bool) false (fun _ => true) o) h)

theorem optionMapSome {α β : Type} (o : Option α) (f : α → β) (c : β)
    (h : @Option.rec α (fun _ => Option β) none (fun a => some (f a)) o = some c) :
    ∃ a : α, o = some a ∧ f a = c :=
  @Option.rec α
    (fun o => @Option.rec α (fun _ => Option β) none (fun a => some (f a)) o = some c →
      ∃ a : α, o = some a ∧ f a = c)
    (fun k => False.elim (noneNeSome k))
    (fun a k => ⟨a, rfl, someInj k⟩)
    o h

theorem bind2Some (o1 o2 : Option CExpr) (k : CExpr → CExpr → CExpr) (c : CExpr)
    (h : bind2 o1 o2 k = some c) :
    ∃ a : CExpr, ∃ b : CExpr, o1 = some a ∧ o2 = some b ∧ k a b = c :=
  @Option.rec CExpr
    (fun o1 => bind2 o1 o2 k = some c →
      ∃ a : CExpr, ∃ b : CExpr, o1 = some a ∧ o2 = some b ∧ k a b = c)
    (fun h1 => False.elim (noneNeSome h1))
    (fun a h1 =>
      @Option.rec CExpr
        (fun o2 => bind2 (some a) o2 k = some c →
          ∃ a' : CExpr, ∃ b : CExpr, some a = some a' ∧ o2 = some b ∧ k a' b = c)
        (fun h2 => False.elim (noneNeSome h2))
        (fun b h2 => ⟨a, b, rfl, rfl, someInj h2⟩)
        o2 h1)
    o1 h

theorem bind3Some (o1 o2 o3 : Option CExpr) (k : CExpr → CExpr → CExpr → CExpr) (c : CExpr)
    (h : bind3 o1 o2 o3 k = some c) :
    ∃ a : CExpr, ∃ b : CExpr, ∃ d : CExpr,
      o1 = some a ∧ o2 = some b ∧ o3 = some d ∧ k a b d = c :=
  @Option.rec CExpr
    (fun o1 => bind3 o1 o2 o3 k = some c →
      ∃ a : CExpr, ∃ b : CExpr, ∃ d : CExpr,
        o1 = some a ∧ o2 = some b ∧ o3 = some d ∧ k a b d = c)
    (fun h1 => False.elim (noneNeSome h1))
    (fun a h1 =>
      Exists.elim (bind2Some o2 o3 (k a) c h1) (fun b rest =>
        Exists.elim rest (fun d facts =>
          ⟨a, b, d, rfl, facts.1, facts.2.1, facts.2.2⟩)))
    o1 h

theorem notLeLt (a b : Nat) (h : ¬ Nat.le a b) : Nat.lt b a :=
  @Nat.rec (fun a => ∀ b : Nat, ¬ Nat.le a b → Nat.lt b a)
    (fun b h => False.elim (h (Nat.zero_le b)))
    (fun a ih b h =>
      @Nat.rec (fun b => ¬ Nat.le (Nat.succ a) b → Nat.lt b (Nat.succ a))
        (fun _ => Nat.succ_le_succ (Nat.zero_le a))
        (fun b _ h' => Nat.succ_le_succ (ih b (fun k => h' (Nat.succ_le_succ k))))
        b h)
    a b h

theorem bleTrueLe (a b : Nat) (h : Nat.ble a b = true) : Nat.le a b :=
  Nat.le_of_ble_eq_true a b h

theorem bleFalseLt (a b : Nat) (h : Nat.ble a b = false) : Nat.lt b a :=
  notLeLt a b (fun k => Bool.noConfusion (Eq.trans (Eq.symm h) (Nat.ble_eq_true_of_le a b k)))

theorem beqFalseNe (a b : Nat) (h : Nat.beq a b = false) : ¬ (a = b) :=
  fun e => Bool.noConfusion (Eq.trans (Eq.symm h)
    (Eq.mpr (congrArg (fun z => Nat.beq a z = true) (Eq.symm e)) (Nat.beq_refl a)))

-- Value view chosen by the compiled sort.
def sortView (s : Srt) (v : Value) : Value :=
  @Srt.rec (fun _ => Value)
    (Value.nat (valueNatProjection v))
    (Value.bool (valueBoolProjection v)) s

def Good (m : Model) (st : State) (row : List Nat) (s : Srt)
    (e : ScalarExpr) (c : CExpr) : Prop :=
  ExactScalarEvaluation m st e (sortView s (evalV row c))
def InTree (r : List Nat) (t : RIndex) : Prop :=
  @RIndex.rec (fun _ => Prop) False (fun _ _ r' _ il ir => il ∨ r = r' ∨ ir) t

theorem boolRecSelP {β : Type} (P : β → Prop) (x y : β) (b : Bool)
    (hx : b = false → P x) (hy : b = true → P y) : P (@Bool.rec (fun _ => β) x y b) :=
  @Bool.rec (fun c => (c = false → P x) → (c = true → P y) → P (@Bool.rec (fun _ => β) x y c))
    (fun f _ => f rfl) (fun _ t => t rfl) b hx hy

-- the only fact the proofs need about the walk
theorem steerSel {β : Type} (P : β → Prop) (goL here goR : β) (h : Nat) (r : List Nat)
    (h' : Nat) (r' : List Nat)
    (hL : P goL) (hR : P goR) (hH : rowEq r r' = true → P here) :
    P (steer goL here goR h r h' r') :=
  boolRecSelP P _ goL (Nat.blt h h')
    (fun _ => boolRecSelP P _ goR (Nat.blt h' h)
      (fun _ => boolRecSelP P (@Bool.rec (fun _ => β) goR goL (rowLt r r')) here (rowEq r r')
        (fun _ => boolRecSelP P goR goL (rowLt r r') (fun _ => hR) (fun _ => hL))
        hH)
      (fun _ => hR))
    (fun _ => hL)

theorem indexMemSound (h : Nat) (r : List Nat) (t : RIndex) :
    indexMemH h r t = true → InTree r t :=
  @RIndex.rec (fun t => indexMemH h r t = true → InTree r t)
    (fun k => Bool.noConfusion k)
    (fun l h' r' rr ihl ihr =>
      steerSel (fun b => b = true → InTree r (RIndex.node l h' r' rr))
        (indexMemH h r l) true (indexMemH h r rr) h r h' r'
        (fun k => Or.inl (ihl k))
        (fun k => Or.inr (Or.inr (ihr k)))
        (fun e _ => Or.inr (Or.inl (rowEqSound r r' e))))
    t

theorem insertSound (x : List Nat) (h0 : Nat) (r0 : List Nat) (t : RIndex) :
    InTree x (indexInsertH h0 r0 t) → x = r0 ∨ InTree x t :=
  @RIndex.rec (fun t => InTree x (indexInsertH h0 r0 t) → x = r0 ∨ InTree x t)
    (fun k => Or.inl (Or.elim k (fun f => (False.elim f : x = r0))
      (fun k2 => Or.elim k2 (fun e => e) (fun f => (False.elim f : x = r0)))))
    (fun l h' r' rr ihl ihr =>
      steerSel (fun s => InTree x s → x = r0 ∨ InTree x (RIndex.node l h' r' rr))
        (RIndex.node (indexInsertH h0 r0 l) h' r' rr) (RIndex.node l h' r' rr)
        (RIndex.node l h' r' (indexInsertH h0 r0 rr)) h0 r0 h' r'
        (fun k => Or.elim k
          (fun inL => Or.elim (ihl inL) (fun e => Or.inl e) (fun old => Or.inr (Or.inl old)))
          (fun rest => Or.inr (Or.inr rest)))
        (fun k => Or.elim k
          (fun inL => Or.inr (Or.inl inL))
          (fun rest => Or.elim rest
            (fun e => Or.inr (Or.inr (Or.inl e)))
            (fun inR => Or.elim (ihr inR) (fun e => Or.inl e)
              (fun old => Or.inr (Or.inr (Or.inr old))))))
        (fun _ k => Or.inr k))
    t

theorem buildSound (x : List Nat) (rows : List (List Nat)) :
    InTree x (buildIndex rows) → Member x rows :=
  @List.rec (List Nat) (fun rows => InTree x (buildIndex rows) → Member x rows)
    (fun k => False.elim k)
    (fun r rest ih k =>
      Or.elim (insertSound x (rowHash r) r (buildIndex rest) k)
        (fun e => Eq.mpr (congrArg (fun z => Member z (r :: rest)) e) (Member.head rest))
        (fun old => Member.tail r rest (ih old)))
    rows

-- the forced (value) forms equal the plain forms
theorem forceNatEq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n :=
  @Nat.rec (fun n => forceNat n k = k n) rfl (fun _ _ => rfl) n

theorem forceRowEq {α : Type} (row : List Nat) : ∀ k : List Nat → α, forceRow row k = k row :=
  @List.rec Nat (fun row => ∀ k : List Nat → α, forceRow row k = k row)
    (fun _ => rfl)
    (fun v vs ih k => Eq.trans (forceNatEq v (fun v' => forceRow vs (fun vs' => k (v' :: vs'))))
      (ih (fun vs' => k (v :: vs'))))
    row

theorem forceSpineEq {α : Type} (rows : List (List Nat)) :
    ∀ k : List (List Nat) → α, forceSpine rows k = k rows :=
  @List.rec (List Nat) (fun rows => ∀ k : List (List Nat) → α, forceSpine rows k = k rows)
    (fun _ => rfl)
    (fun r rest ih k => ih (fun rs => k (r :: rs)))
    rows

theorem forceBoolEq {α : Type} (b : Bool) (k : Bool → α) : forceBool b k = k b :=
  @Bool.rec (fun b => forceBool b k = k b) rfl rfl b

theorem forceCExprEq {α : Type} (c : CExpr) : ∀ k : CExpr → α, forceCExpr c k = k c :=
  @CExpr.rec (fun c => ∀ k : CExpr → α, forceCExpr c k = k c)
    (fun n k => forceNatEq n (fun n' => k (CExpr.lit n')))
    (fun i k => forceNatEq i (fun i' => k (CExpr.slot i')))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.add a' b'))))
      (ib (fun b' => k (CExpr.add a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.sub a' b'))))
      (ib (fun b' => k (CExpr.sub a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.gt a' b'))))
      (ib (fun b' => k (CExpr.gt a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.le a' b'))))
      (ib (fun b' => k (CExpr.le a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.eq a' b'))))
      (ib (fun b' => k (CExpr.eq a b'))))
    (fun c t e ic it ie k =>
      Eq.trans (ic (fun c' => forceCExpr t (fun t' => forceCExpr e (fun e' => k (CExpr.ite c' t' e')))))
        (Eq.trans (it (fun t' => forceCExpr e (fun e' => k (CExpr.ite c t' e'))))
          (ie (fun e' => k (CExpr.ite c t e')))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.neq a' b'))))
      (ib (fun b' => k (CExpr.neq a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.bor a' b'))))
      (ib (fun b' => k (CExpr.bor a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.band a' b'))))
      (ib (fun b' => k (CExpr.band a b'))))
    (fun a b ia ib k => Eq.trans (ia (fun a' => forceCExpr b (fun b' => k (CExpr.biff a' b'))))
      (ib (fun b' => k (CExpr.biff a b'))))
    (fun t k => forceBoolEq t (fun t' => k (CExpr.blit t')))
    c

theorem forceListEq {α β : Type} (f : β → (β → α) → α) (hf : ∀ (x : β) (k : β → α), f x k = k x)
    (xs : List β) : ∀ k : List β → α, forceList f xs k = k xs :=
  @List.rec β (fun xs => ∀ k : List β → α, forceList f xs k = k xs)
    (fun _ => rfl)
    (fun x rest ih k => Eq.trans (hf x (fun x' => forceList f rest (fun xs' => k (x' :: xs'))))
      (ih (fun xs' => k (x :: xs'))))
    xs

theorem forceUpdEq {α : Type} (u : Option CExpr) (k : Option CExpr → α) : forceUpd u k = k u :=
  @Option.rec CExpr (fun u => forceUpd u k = k u) rfl
    (fun c => forceCExprEq c (fun c' => k (some c'))) u

theorem forceActionEq {α : Type} (ca : CAction) (k : CAction → α) : forceAction ca k = k ca :=
  @CAction.rec (fun ca => forceAction ca k = k ca)
    (fun g u => Eq.trans (forceCExprEq g (fun g' => forceList forceUpd u (fun u' => k (CAction.mk g' u'))))
      (forceListEq forceUpd forceUpdEq u (fun u' => k (CAction.mk g u'))))
    ca

theorem forceCMEq {α : Type} (cm : CModel) (k : CModel → α) : forceCM cm k = k cm :=
  @CModel.rec (fun cm => forceCM cm k = k cm)
    (fun i acts invs =>
      Eq.trans (forceRowEq i (fun i' => forceList forceAction acts (fun acts' =>
          forceList forceCExpr invs (fun invs' => k (CModel.mk i' acts' invs')))))
        (Eq.trans (forceListEq forceAction forceActionEq acts (fun acts' =>
            forceList forceCExpr invs (fun invs' => k (CModel.mk i acts' invs'))))
          (forceListEq forceCExpr (fun c k' => forceCExprEq c k') invs
            (fun invs' => k (CModel.mk i acts invs')))))
    cm

theorem boolRecPush {β γ : Type} (k : β → γ) (x y : β) (b : Bool) :
    @Bool.rec (fun _ => γ) (k x) (k y) b = k (@Bool.rec (fun _ => β) x y b) :=
  @Bool.rec (fun b => @Bool.rec (fun _ => γ) (k x) (k y) b = k (@Bool.rec (fun _ => β) x y b))
    rfl rfl b

theorem steerPush {β γ : Type} (k : β → γ) (a b c : β) (h : Nat) (r : List Nat) (h' : Nat)
    (r' : List Nat) : steer (k a) (k b) (k c) h r h' r' = k (steer a b c h r h' r') :=
  Eq.trans
    (congrArg (fun z => @Bool.rec (fun _ => γ) (@Bool.rec (fun _ => γ)
        (@Bool.rec (fun _ => γ) z (k b) (rowEq r r')) (k c) (Nat.blt h' h)) (k a) (Nat.blt h h'))
      (boolRecPush k c a (rowLt r r')))
    (Eq.trans
      (congrArg (fun z => @Bool.rec (fun _ => γ) (@Bool.rec (fun _ => γ) z (k c) (Nat.blt h' h))
          (k a) (Nat.blt h h'))
        (boolRecPush k (@Bool.rec (fun _ => β) c a (rowLt r r')) b (rowEq r r')))
      (Eq.trans
        (congrArg (fun z => @Bool.rec (fun _ => γ) z (k a) (Nat.blt h h'))
          (boolRecPush k (@Bool.rec (fun _ => β) (@Bool.rec (fun _ => β) c a (rowLt r r')) b (rowEq r r'))
            c (Nat.blt h' h)))
        (boolRecPush k (@Bool.rec (fun _ => β)
            (@Bool.rec (fun _ => β) (@Bool.rec (fun _ => β) c a (rowLt r r')) b (rowEq r r'))
            c (Nat.blt h' h))
          a (Nat.blt h h'))))

theorem insertKEq {α : Type} (h : Nat) (r : List Nat) (t : RIndex) :
    ∀ k : RIndex → α, insertK h r t k = k (indexInsertH h r t) :=
  @RIndex.rec (fun t => ∀ k : RIndex → α, insertK h r t k = k (indexInsertH h r t))
    (fun _ => rfl)
    (fun l h' r' rr ihl ihr k =>
      Eq.trans
        (congrArg (fun z => steer z (k (RIndex.node l h' r' rr))
            (insertK h r rr (fun rr' => k (RIndex.node l h' r' rr'))) h r h' r')
          (ihl (fun l' => k (RIndex.node l' h' r' rr))))
        (Eq.trans
          (congrArg (fun z => steer (k (RIndex.node (indexInsertH h r l) h' r' rr))
              (k (RIndex.node l h' r' rr)) z h r h' r')
            (ihr (fun rr' => k (RIndex.node l h' r' rr'))))
          (steerPush k (RIndex.node (indexInsertH h r l) h' r' rr) (RIndex.node l h' r' rr)
            (RIndex.node l h' r' (indexInsertH h r rr)) h r h' r')))
    t

theorem buildIndexKEq {α : Type} (rows : List (List Nat)) :
    ∀ k : RIndex → α, buildIndexK rows k = k (buildIndex rows) :=
  @List.rec (List Nat) (fun rows => ∀ k : RIndex → α, buildIndexK rows k = k (buildIndex rows))
    (fun _ => rfl)
    (fun r rest ih k =>
      Eq.trans (ih (fun t => forceNat (rowHash r) (fun h => insertK h r t k)))
        (Eq.trans (forceNatEq (rowHash r) (fun h => insertK h r (buildIndex rest) k))
          (insertKEq (rowHash r) r (buildIndex rest) k)))
    rows

theorem memKEq (t : RIndex) (s : List Nat) : memK t s = indexMem s t :=
  Eq.trans (forceRowEq s (fun s' => forceNat (rowHash s') (fun h => indexMemH h s' t)))
    (forceNatEq (rowHash s) (fun h => indexMemH h s t))

-- every row of the index is a row of the list: what `memK` answers carry
theorem memKCover (t : RIndex) (rows : List (List Nat))
    (cover : ∀ x : List Nat, InTree x t → Member x rows) :
    ∀ r : List Nat, memK t r = true → Member r rows :=
  fun r h => cover r (indexMemSound (rowHash r) r t (Eq.trans (Eq.symm (memKEq t r)) h))

theorem takeTreeSound {α : Type} (P : α → Prop) (d : Nat) :
    ∀ (xs : List (List Nat)) (k : RIndex → List (List Nat) → α),
      (∀ (t : RIndex) (rest : List (List Nat)),
        (∀ y : List Nat, InTree y t ∨ Member y rest → Member y xs) → P (k t rest)) →
      P (takeTreeK d xs k) :=
  @Nat.rec
    (fun d => ∀ (xs : List (List Nat)) (k : RIndex → List (List Nat) → α),
      (∀ (t : RIndex) (rest : List (List Nat)),
        (∀ y : List Nat, InTree y t ∨ Member y rest → Member y xs) → P (k t rest)) →
      P (takeTreeK d xs k))
    (fun xs k hk => hk RIndex.leaf xs (fun y o => Or.elim o (fun f => False.elim f) (fun m => m)))
    (fun d ih xs k hk =>
      ih xs
        (fun l xs1 => @List.rec (List Nat) (fun _ => α) (k l [])
          (fun x xs2 _ => takeTreeK d xs2 (fun r xs3 =>
            forceNat (rowHash x) (fun h => k (RIndex.node l h x r) xs3)))
          xs1)
        (fun l xs1 cover1 =>
          @List.rec (List Nat)
            (fun xs1 => (∀ y : List Nat, InTree y l ∨ Member y xs1 → Member y xs) →
              P (@List.rec (List Nat) (fun _ => α) (k l [])
                (fun x xs2 _ => takeTreeK d xs2 (fun r xs3 =>
                  forceNat (rowHash x) (fun h => k (RIndex.node l h x r) xs3)))
                xs1))
            (fun c1 => hk l [] c1)
            (fun x xs2 _ c1 =>
              ih xs2
                (fun r xs3 => forceNat (rowHash x) (fun h => k (RIndex.node l h x r) xs3))
                (fun r xs3 cover2 =>
                  Eq.mpr (congrArg P (forceNatEq (rowHash x) (fun h => k (RIndex.node l h x r) xs3)))
                    (hk (RIndex.node l (rowHash x) x r) xs3 (fun y o =>
                      Or.elim o
                        (fun inT => Or.elim inT
                          (fun inL => c1 y (Or.inl inL))
                          (fun rest => Or.elim rest
                            (fun e => c1 y (Or.inr (Eq.mpr (congrArg (fun z => Member z (x :: xs2)) e)
                              (Member.head xs2))))
                            (fun inR => c1 y (Or.inr (Member.tail x xs2 (cover2 y (Or.inl inR)))))))
                        (fun m => c1 y (Or.inr (Member.tail x xs2 (cover2 y (Or.inr m)))))))))
            xs1 cover1))
    d

theorem growSound {α : Type} (P : α → Prop) (rows : List (List Nat)) (k : RIndex → α)
    (hk : ∀ t : RIndex, (∀ x : List Nat, InTree x t → Member x rows) → P (k t))
    (fuel : List (List Nat)) :
    ∀ (t : RIndex) (d : Nat) (xs : List (List Nat)),
      (∀ y : List Nat, InTree y t ∨ Member y xs → Member y rows) →
      P (growK fuel t d xs k) :=
  @List.rec (List Nat)
    (fun fuel => ∀ (t : RIndex) (d : Nat) (xs : List (List Nat)),
      (∀ y : List Nat, InTree y t ∨ Member y xs → Member y rows) →
      P (growK fuel t d xs k))
    (fun t d xs cover => hk t (fun y i => cover y (Or.inl i)))
    (fun _ fuel' ih t d xs =>
      @List.rec (List Nat)
        (fun xs => (∀ y : List Nat, InTree y t ∨ Member y xs → Member y rows) →
          P (@List.rec (List Nat) (fun _ => α) (k t)
            (fun x xs' _ => takeTreeK d xs' (fun r xs'' =>
              forceNat (rowHash x) (fun h => growK fuel' (RIndex.node t h x r) (Nat.succ d) xs'' k)))
            xs))
        (fun cover => hk t (fun y i => cover y (Or.inl i)))
        (fun x xs' _ cover =>
          takeTreeSound P d xs'
            (fun r xs'' => forceNat (rowHash x)
              (fun h => growK fuel' (RIndex.node t h x r) (Nat.succ d) xs'' k))
            (fun r xs'' cover2 =>
              Eq.mpr (congrArg P (forceNatEq (rowHash x)
                  (fun h => growK fuel' (RIndex.node t h x r) (Nat.succ d) xs'' k)))
                (ih (RIndex.node t (rowHash x) x r) (Nat.succ d) xs''
                  (fun y o => Or.elim o
                    (fun inT => Or.elim inT
                      (fun inL => cover y (Or.inl inL))
                      (fun rest => Or.elim rest
                        (fun e => cover y (Or.inr (Eq.mpr (congrArg (fun z => Member z (x :: xs')) e)
                          (Member.head xs'))))
                        (fun inR => cover y (Or.inr (Member.tail x xs' (cover2 y (Or.inl inR)))))))
                    (fun m => cover y (Or.inr (Member.tail x xs' (cover2 y (Or.inr m)))))))))
        xs)
    fuel

-- whichever way `indexK` builds its tree, every row in it is a row of the list
theorem indexKSound {α : Type} (P : α → Prop) (rows : List (List Nat)) (k : RIndex → α)
    (hk : ∀ t : RIndex, (∀ x : List Nat, InTree x t → Member x rows) → P (k t)) :
    P (indexK rows k) :=
  @List.rec (List Nat)
    (fun rows => (∀ t : RIndex, (∀ x : List Nat, InTree x t → Member x rows) → P (k t)) →
      P (indexK rows k))
    (fun hk0 => hk0 RIndex.leaf (fun x f => False.elim f))
    (fun r rest _ hk1 =>
      Eq.mpr (congrArg P (forceNatEq (rowHash r) (fun h =>
          @Bool.rec (fun _ => α) (buildIndexK (r :: rest) k)
            (growK (r :: rest) RIndex.leaf 0 (r :: rest) k) (ascAfter rest h r))))
        (boolRecSelP P (buildIndexK (r :: rest) k) (growK (r :: rest) RIndex.leaf 0 (r :: rest) k)
          (ascAfter rest (rowHash r) r)
          (fun _ => Eq.mpr (congrArg P (buildIndexKEq (r :: rest) k))
            (hk1 (buildIndex (r :: rest)) (fun x i => buildSound x (r :: rest) i)))
          (fun _ => growSound P (r :: rest) k hk1 (r :: rest) RIndex.leaf 0 (r :: rest)
            (fun y o => Or.elim o (fun f => False.elim f) (fun m => m)))))
    rows hk

theorem checkCompiledSound (cm : CModel) (rows : List (List Nat))
    (h : checkCompiled cm rows = true) :
    ∃ t : RIndex, (∀ x : List Nat, InTree x t → Member x rows) ∧ checkIndexed cm rows t = true :=
  indexKSound
    (fun b => b = true →
      ∃ t : RIndex, (∀ x : List Nat, InTree x t → Member x rows) ∧ checkIndexed cm rows t = true)
    rows (checkIndexed cm rows)
    (fun t cover hb => ⟨t, cover, hb⟩)
    (Eq.trans (Eq.symm (forceSpineEq rows (fun rs => indexK rs (checkIndexed cm rs)))) h)

theorem lsNil (st : State) (name : String) (row : List Nat) (i : Nat)
    (h : lookupSlot [] name = some i) : False := noneNeSome h

theorem lsTrue (v : StateVar) (rest : List StateVar) (name : String) (i : Nat)
    (hd : decide (v.name = name) = true) (h : lookupSlot (v :: rest) name = some i) : 0 = i :=
  someInj (Eq.trans
    (congrArg (fun b => @Bool.rec (fun _ => Option Nat)
      (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i))
        (lookupSlot rest name))
      (some 0) b) (Eq.symm hd)) h)

theorem lsFalse (v : StateVar) (rest : List StateVar) (name : String) (i : Nat)
    (hd : decide (v.name = name) = false) (h : lookupSlot (v :: rest) name = some i) :
    ∃ j : Nat, lookupSlot rest name = some j ∧ Nat.succ j = i :=
  optionMapSome (lookupSlot rest name) Nat.succ i
    (Eq.trans
      (congrArg (fun b => @Bool.rec (fun _ => Option Nat)
        (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i))
          (lookupSlot rest name))
        (some 0) b) (Eq.symm hd)) h)

theorem lsName (v : StateVar) (name : String)
    (hd : decide (v.name = name) = true) : v.name = name := of_decide_eq_true hd

def SlotFacts (st : State) (name : String) (vs : List StateVar) (row : List Nat) (i : Nat) : Prop :=
  (∃ entry : StateVar, Member entry vs ∧ entry.name = name) ∧ st.scalar name = slotAt row i

theorem lsHit (st : State) (name : String) (v : StateVar) (rest : List StateVar)
    (value : Nat) (tail : List Nat) (i : Nat)
    (coord : st.scalar v.name = value)
    (hd : decide (v.name = name) = true) (h : lookupSlot (v :: rest) name = some i) :
    SlotFacts st name (v :: rest) (value :: tail) i :=
  And.intro
    (@Exists.intro StateVar (fun entry => Member entry (v :: rest) ∧ entry.name = name) v
      (And.intro (Member.head rest) (lsName v name hd)))
    (Eq.mpr
      (congrArg (fun j => st.scalar name = slotAt (value :: tail) j)
        (Eq.symm (lsTrue v rest name i hd h)))
      (Eq.trans (congrArg st.scalar (Eq.symm (lsName v name hd))) coord))

theorem lsMiss (st : State) (name : String) (v : StateVar) (rest : List StateVar)
    (value : Nat) (tail : List Nat) (i : Nat)
    (ih : ∀ j : Nat, lookupSlot rest name = some j → SlotFacts st name rest tail j)
    (hd : decide (v.name = name) = false) (h : lookupSlot (v :: rest) name = some i) :
    SlotFacts st name (v :: rest) (value :: tail) i :=
  Exists.elim (lsFalse v rest name i hd h)
    (fun j facts =>
      And.intro
        (Exists.elim (ih j facts.1).1 (fun entry ef =>
            Exists.intro entry (And.intro (Member.tail v rest ef.1) ef.2)))
        (Eq.mpr (congrArg (fun k => st.scalar name = slotAt (value :: tail) k)
            (Eq.symm facts.2))
          (ih j facts.1).2))

theorem lookupSlotSound (st : State) (name : String) (vs : List StateVar) :
    ∀ (row : List Nat) (i : Nat),
      ScalarCoordinatesDenote st vs row → lookupSlot vs name = some i →
      SlotFacts st name vs row i :=
  @List.rec StateVar
    (fun vs => ∀ (row : List Nat) (i : Nat),
      ScalarCoordinatesDenote st vs row → lookupSlot vs name = some i →
      SlotFacts st name vs row i)
    (fun row i _ h => False.elim (lsNil st name row i h))
    (fun v rest ih row =>
      @List.rec Nat
        (fun row => ∀ i : Nat,
          ScalarCoordinatesDenote st (v :: rest) row → lookupSlot (v :: rest) name = some i →
          SlotFacts st name (v :: rest) row i)
        (fun i denote _ => False.elim denote)
        (fun value tail _ i denote h =>
          Or.elim (boolCases (decide (v.name = name)))
            (fun hd => lsHit st name v rest value tail i denote.1 hd h)
            (fun hd => lsMiss st name v rest value tail i
               (fun j found => ih tail j denote.2 found) hd h))
        row)
    vs
theorem optionBindSome {α β : Type} (o : Option α) (g : α → Option β) (w : β)
    (h : @Option.rec α (fun _ => Option β) none g o = some w) :
    ∃ a : α, o = some a ∧ g a = some w :=
  @Option.rec α
    (fun o => @Option.rec α (fun _ => Option β) none g o = some w →
      ∃ a : α, o = some a ∧ g a = some w)
    (fun k => False.elim (noneNeSome k))
    (fun a k => ⟨a, rfl, k⟩)
    o h

def ConstFound (consts : List Constant) (name : String) (v : Nat) : Prop :=
  ∃ entry : Constant, Member entry consts ∧ entry.name = name ∧ entry.value = v

theorem firstConstSound (name : String) (consts : List Constant) :
    ∀ v : Nat, firstConst consts name = some v → ConstFound consts name v :=
  @List.rec Constant
    (fun consts => ∀ v : Nat, firstConst consts name = some v → ConstFound consts name v)
    (fun v h => False.elim (noneNeSome h))
    (fun c rest ih v h =>
      Or.elim (boolCases (decide (c.name = name)))
        (fun hd =>
          @Exists.intro Constant
            (fun entry => Member entry (c :: rest) ∧ entry.name = name ∧ entry.value = v) c
            (And.intro (Member.head rest)
              (And.intro (of_decide_eq_true hd)
                (someInj (Eq.trans
                  (congrArg (fun b => @Bool.rec (fun _ => Option Nat)
                    (firstConst rest name) (some c.value) b) (Eq.symm hd)) h)))))
        (fun hd =>
          Exists.elim
            (ih v (Eq.trans
              (congrArg (fun b => @Bool.rec (fun _ => Option Nat)
                (firstConst rest name) (some c.value) b) (Eq.symm hd)) h))
            (fun entry facts =>
              @Exists.intro Constant
                (fun entry => Member entry (c :: rest) ∧ entry.name = name ∧ entry.value = v) entry
                (And.intro (Member.tail c rest facts.1) facts.2))))
    consts

theorem constsAgreeSound (name : String) (v : Nat) (consts : List Constant) :
    constsAgree consts name v = true →
    Every (fun entry : Constant => entry.name = name → entry.value = v) consts :=
  @List.rec Constant
    (fun consts => constsAgree consts name v = true →
      Every (fun entry : Constant => entry.name = name → entry.value = v) consts)
    (fun _ => True.intro)
    (fun c rest ih h =>
      Or.elim (boolCases (decide (c.name = name)))
        (fun hd =>
          (fun both =>
            And.intro (fun _ => natBeqSound c.value v both.1) (ih both.2))
          (boolRecAnd (Nat.beq c.value v) (constsAgree rest name v)
            (Eq.trans
              (congrArg (fun b => @Bool.rec (fun _ => Bool) (constsAgree rest name v)
                (@Bool.rec (fun _ => Bool) false (constsAgree rest name v) (Nat.beq c.value v)) b)
                (Eq.symm hd)) h)))
        (fun hd =>
          And.intro (fun hn => False.elim (of_decide_eq_false hd hn))
            (ih (Eq.trans
              (congrArg (fun b => @Bool.rec (fun _ => Bool) (constsAgree rest name v)
                (@Bool.rec (fun _ => Bool) false (constsAgree rest name v) (Nat.beq c.value v)) b)
                (Eq.symm hd)) h))))
    consts

theorem constOfSound (model : ScalarModel) (name : String) (w : Nat)
    (h : constOf model.constants name = some w) :
    ConstantValue model.asModel name w ∧
      (∀ other : Nat, ConstantValue model.asModel name other → other = w) :=
  Exists.elim (optionBindSome (firstConst model.constants name)
      (fun v => @Bool.rec (fun _ => Option Nat) none (some v) (constsAgree model.constants name v)) w h)
    (fun v facts =>
      Or.elim (boolCases (constsAgree model.constants name v))
        (fun ha =>
          (fun same : v = w =>
            (fun found : ConstFound model.constants name w =>
              (fun every : Every (fun entry : Constant => entry.name = name → entry.value = w) model.constants =>
                And.intro found
                  (uniqueConstantValueOfEvery model.asModel name w every))
              (Eq.mpr (congrArg (fun z => Every (fun entry : Constant => entry.name = name → entry.value = z) model.constants) (Eq.symm same))
                (constsAgreeSound name v model.constants ha)))
            (Eq.mpr (congrArg (fun z => ConstFound model.constants name z) (Eq.symm same))
              (firstConstSound name model.constants v facts.1)))
          (someInj (Eq.trans
            (congrArg (fun b => @Bool.rec (fun _ => Option Nat) none (some v) b) (Eq.symm ha))
            facts.2)))
        (fun ha => False.elim (noneNeSome (Eq.trans
            (congrArg (fun b => @Bool.rec (fun _ => Option Nat) none (some v) b) (Eq.symm ha))
            facts.2))))
-- The compiled-evaluation invariant for one expression.
def CompileGood (model : ScalarModel) (st : State) (row : List Nat) (e : ScalarExpr) : Prop :=
  ∀ (s : Srt) (c : CExpr), compileS model.variables model.constants e s = some c →
    Good model.asModel st row s e c

theorem goodTransport (m : Model) (st : State) (row : List Nat) (s : Srt)
    (e : ScalarExpr) (c c' : CExpr) (same : c = c') (good : Good m st row s e c) :
    Good m st row s e c' :=
  Eq.mpr (congrArg (fun z => Good m st row s e z) (Eq.symm same)) good

theorem caseInt (model : ScalarModel) (st : State) (row : List Nat) (n : Nat) :
    CompileGood model st row (ScalarExpr.int n) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.int n) s = some c →
        Good model.asModel st row s (ScalarExpr.int n) c)
      (fun c h => goodTransport model.asModel st row Srt.nat (ScalarExpr.int n)
        (CExpr.lit n) c (someInj h) (exactScalarInt model.asModel st n))
      (fun c h => False.elim (noneNeSome h))
      s

theorem caseVar (model : ScalarModel) (st : State) (row : List Nat)
    (denote : ScalarCoordinatesDenote st model.variables row) (name : String) :
    CompileGood model st row (ScalarExpr.var name) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.var name) s = some c →
        Good model.asModel st row s (ScalarExpr.var name) c)
      (fun c h =>
        Exists.elim (optionMapSome (lookupSlot model.variables name) CExpr.slot c h)
          (fun i facts =>
            goodTransport model.asModel st row Srt.nat (ScalarExpr.var name)
              (CExpr.slot i) c facts.2
              (exactScalarVar model.asModel st name (slotAt row i)
                (lookupSlotSound st name model.variables row i denote facts.1).1
                (lookupSlotSound st name model.variables row i denote facts.1).2
                (scalarModelNoFunctionRange model name))))
      (fun c h => False.elim (noneNeSome h))
      s

theorem caseConst (model : ScalarModel) (st : State) (row : List Nat) (name : String) :
    CompileGood model st row (ScalarExpr.constRef name) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.constRef name) s = some c →
        Good model.asModel st row s (ScalarExpr.constRef name) c)
      (fun c h =>
        Exists.elim (optionMapSome (constOf model.constants name) CExpr.lit c h)
          (fun v facts =>
            goodTransport model.asModel st row Srt.nat (ScalarExpr.constRef name)
              (CExpr.lit v) c facts.2
              (exactScalarConst model.asModel st name v
                (constOfSound model name v facts.1).1
                (constOfSound model name v facts.1).2)))
      (fun c h => False.elim (noneNeSome h))
      s

theorem caseAdd (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.add l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.add l r) s = some c →
        Good model.asModel st row s (ScalarExpr.add l r) c)
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.nat)
            (compileS model.variables model.constants r Srt.nat) CExpr.add c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.nat (ScalarExpr.add l r)
              (CExpr.add a b) c facts.2.2
              (exactScalarAdd model.asModel st l r (evalN row a) (evalN row b)
                (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)))))
      (fun c h => False.elim (noneNeSome h))
      s

theorem caseSub (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.sub l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.sub l r) s = some c →
        Good model.asModel st row s (ScalarExpr.sub l r) c)
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.nat)
            (compileS model.variables model.constants r Srt.nat) CExpr.sub c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.nat (ScalarExpr.sub l r)
              (CExpr.sub a b) c facts.2.2
              (exactScalarSub model.asModel st l r (evalN row a) (evalN row b)
                (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)))))
      (fun c h => False.elim (noneNeSome h))
      s

-- Bool-sorted comparison results, rewritten along the computed Bool.
theorem exactBoolTransport (m : Model) (st : State) (e : ScalarExpr)
    (f : Bool → Bool) (b b' : Bool) (same : b = b')
    (exact : ExactScalarEvaluation m st e (Value.bool (f b'))) :
    ExactScalarEvaluation m st e (Value.bool (f b)) :=
  Eq.mpr (congrArg (fun z => ExactScalarEvaluation m st e (Value.bool (f z))) same) exact

theorem caseGt (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.gt l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.gt l r) s = some c →
        Good model.asModel st row s (ScalarExpr.gt l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.nat)
            (compileS model.variables model.constants r Srt.nat) CExpr.gt c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.gt l r)
              (CExpr.gt a b) c facts.2.2
              (Or.elim (boolCases (Nat.ble (evalN row a) (evalN row b)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.gt l r)
                  (fun z => @Bool.rec (fun _ => Bool) true false z) _ true hb
                  (exactScalarGtFalse model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (bleTrueLe (evalN row a) (evalN row b) hb)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.gt l r)
                  (fun z => @Bool.rec (fun _ => Bool) true false z) _ false hb
                  (exactScalarGtTrue model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (bleFalseLt (evalN row a) (evalN row b) hb)))))))
      s

theorem caseLe (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.le l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.le l r) s = some c →
        Good model.asModel st row s (ScalarExpr.le l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.nat)
            (compileS model.variables model.constants r Srt.nat) CExpr.le c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.le l r)
              (CExpr.le a b) c facts.2.2
              (Or.elim (boolCases (Nat.ble (evalN row a) (evalN row b)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.le l r)
                  (fun z => z) _ true hb
                  (exactScalarLeTrue model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (bleTrueLe (evalN row a) (evalN row b) hb)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.le l r)
                  (fun z => z) _ false hb
                  (exactScalarLeFalse model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (bleFalseLt (evalN row a) (evalN row b) hb)))))))
      s

theorem caseEq (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.eq l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.eq l r) s = some c →
        Good model.asModel st row s (ScalarExpr.eq l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.nat)
            (compileS model.variables model.constants r Srt.nat) CExpr.eq c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.eq l r)
              (CExpr.eq a b) c facts.2.2
              (Or.elim (boolCases (Nat.beq (evalN row a) (evalN row b)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.eq l r)
                  (fun z => z) _ true hb
                  (exactScalarEqTrue model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (natBeqSound (evalN row a) (evalN row b) hb)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.eq l r)
                  (fun z => z) _ false hb
                  (exactScalarEqFalse model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (beqFalseNe (evalN row a) (evalN row b) hb)))))))
      s

theorem caseIte (model : ScalarModel) (st : State) (row : List Nat) (cnd t f : ScalarExpr)
    (ihc : CompileGood model st row cnd) (iht : CompileGood model st row t)
    (ihf : CompileGood model st row f) :
    CompileGood model st row (ScalarExpr.ite cnd t f) :=
  fun s c h =>
    Exists.elim (bind3Some (compileS model.variables model.constants cnd Srt.bool)
        (compileS model.variables model.constants t s)
        (compileS model.variables model.constants f s) CExpr.ite c h)
      (fun cc rest => Exists.elim rest (fun ct rest2 => Exists.elim rest2 (fun cf facts =>
        goodTransport model.asModel st row s (ScalarExpr.ite cnd t f)
          (CExpr.ite cc ct cf) c facts.2.2.2
          (Or.elim (boolCases (evalB row cc))
            (fun hb =>
              Eq.mpr
                (congrArg (fun z => ExactScalarEvaluation model.asModel st (ScalarExpr.ite cnd t f)
                  (sortView s (@Bool.rec (fun _ => Value) (evalV row cf) (evalV row ct) z))) hb)
                (exactScalarIteTrue model.asModel st cnd t f (sortView s (evalV row ct))
                  (exactBoolTransport model.asModel st cnd (fun z => z) true (evalB row cc)
                    (Eq.symm hb) (ihc Srt.bool cc facts.1))
                  (iht s ct facts.2.1)))
            (fun hb =>
              Eq.mpr
                (congrArg (fun z => ExactScalarEvaluation model.asModel st (ScalarExpr.ite cnd t f)
                  (sortView s (@Bool.rec (fun _ => Value) (evalV row cf) (evalV row ct) z))) hb)
                (exactScalarIteFalse model.asModel st cnd t f (sortView s (evalV row cf))
                  (exactBoolTransport model.asModel st cnd (fun z => z) false (evalB row cc)
                    (Eq.symm hb) (ihc Srt.bool cc facts.1))
                  (ihf s cf facts.2.2.1)))))))

-- ===== Boolean glue: neq / or / and / iff / bool literal =====
def GlueEvaluationView (model : Model) (locals : List (String × Nat))
    (state : State) (expression : ScalarExpr) (value : Value) : Prop :=
  match expression with
  | ScalarExpr.neq left right =>
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        (¬ (leftValue = rightValue)) ∧ value = Value.bool true) ∨
      (∃ leftValue : Nat, ∃ rightValue : Nat,
        Evaluates model locals state left (Value.nat leftValue) ∧
        Evaluates model locals state right (Value.nat rightValue) ∧
        leftValue = rightValue ∧ value = Value.bool false)
  | ScalarExpr.or left right =>
      (Evaluates model locals state left (Value.bool false) ∧
        Evaluates model locals state right (Value.bool false) ∧
        value = Value.bool false) ∨
      (∃ rightValue : Bool,
        Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool rightValue) ∧
        value = Value.bool true) ∨
      (Evaluates model locals state left (Value.bool false) ∧
        Evaluates model locals state right (Value.bool true) ∧
        value = Value.bool true)
  | ScalarExpr.and left right =>
      (Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool true) ∧
        value = Value.bool true) ∨
      (∃ rightValue : Bool,
        Evaluates model locals state left (Value.bool false) ∧
        Evaluates model locals state right (Value.bool rightValue) ∧
        value = Value.bool false) ∨
      (Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool false) ∧
        value = Value.bool false)
  | ScalarExpr.iff left right =>
      (∃ truth : Bool,
        Evaluates model locals state left (Value.bool truth) ∧
        Evaluates model locals state right (Value.bool truth) ∧
        value = Value.bool true) ∨
      (Evaluates model locals state left (Value.bool false) ∧
        Evaluates model locals state right (Value.bool true) ∧
        value = Value.bool false) ∨
      (Evaluates model locals state left (Value.bool true) ∧
        Evaluates model locals state right (Value.bool false) ∧
        value = Value.bool false)
  | ScalarExpr.bool truth => value = Value.bool truth
  | _ => True

theorem glueEvaluationViewOfEvaluates
    (model : Model) (locals : List (String × Nat)) (state : State)
    (expression : ScalarExpr) (value : Value)
    (evaluation : Evaluates model locals state expression value) :
    GlueEvaluationView model locals state expression value :=
  @Evaluates.rec model
    (fun locals state expression value _ =>
      GlueEvaluationView model locals state expression value)
    (fun _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ leftValue rightValue leftProof rightProof different _ _ =>
      Or.inl ⟨leftValue, rightValue, leftProof, rightProof, different, rfl⟩)
    (fun _ _ leftValue rightValue leftProof rightProof same _ _ =>
      Or.inr ⟨leftValue, rightValue, leftProof, rightProof, same, rfl⟩)
    (fun _ _ leftProof rightProof _ _ =>
      Or.inl ⟨leftProof, rightProof, rfl⟩)
    (fun _ _ rightValue leftProof rightProof _ _ =>
      Or.inr (Or.inl ⟨rightValue, leftProof, rightProof, rfl⟩))
    (fun _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inr ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ leftProof rightProof _ _ =>
      Or.inl ⟨leftProof, rightProof, rfl⟩)
    (fun _ _ rightValue leftProof rightProof _ _ =>
      Or.inr (Or.inl ⟨rightValue, leftProof, rightProof, rfl⟩))
    (fun _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inr ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ truth leftProof rightProof _ _ =>
      Or.inl ⟨truth, leftProof, rightProof, rfl⟩)
    (fun _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inl ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ leftProof rightProof _ _ =>
      Or.inr (Or.inr ⟨leftProof, rightProof, rfl⟩))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ => rfl)
    locals state expression value evaluation

theorem boolPinned (model : Model) (state : State) (e : ScalarExpr) (a b : Bool)
    (exact : ExactScalarEvaluation model state e (Value.bool a))
    (other : Evaluates model [] state e (Value.bool b)) : b = a :=
  congrArg valueBoolProjection (exact.unique (Value.bool b) other)

theorem natPinned (model : Model) (state : State) (e : ScalarExpr) (a b : Nat)
    (exact : ExactScalarEvaluation model state e (Value.nat a))
    (other : Evaluates model [] state e (Value.nat b)) : b = a :=
  congrArg valueNatProjection (exact.unique (Value.nat b) other)

theorem exactScalarOr (model : Model) (state : State)
    (left right : ScalarExpr) (a b : Bool)
    (leftExact : ExactScalarEvaluation model state left (Value.bool a))
    (rightExact : ExactScalarEvaluation model state right (Value.bool b)) :
    ExactScalarEvaluation model state (ScalarExpr.or left right)
      (Value.bool (a || b)) :=
  { derives :=
      @Bool.rec
        (fun a => Evaluates model [] state left (Value.bool a) →
          Evaluates model [] state (ScalarExpr.or left right) (Value.bool (a || b)))
        (fun lp =>
          @Bool.rec
            (fun b => Evaluates model [] state right (Value.bool b) →
              Evaluates model [] state (ScalarExpr.or left right)
                (Value.bool (false || b)))
            (fun rp => Evaluates.orFalse left right lp rp)
            (fun rp => Evaluates.orRight left right lp rp)
            b rightExact.derives)
        (fun lp => Evaluates.orLeft left right b lp rightExact.derives)
        a leftExact.derives
    unique := fun other evaluation =>
      Or.elim
        (glueEvaluationViewOfEvaluates model [] state
          (ScalarExpr.or left right) other evaluation)
        (fun bothFalse =>
          Eq.trans bothFalse.2.2
            (congrArg Value.bool
              (Eq.trans (congrArg (fun z => z || false)
                  (boolPinned model state left a false leftExact bothFalse.1))
                (congrArg (fun z => a || z)
                  (boolPinned model state right b false rightExact bothFalse.2.1)))))
        (fun rest =>
          Or.elim rest
            (fun leftTrue =>
              Exists.elim leftTrue (fun _ facts =>
                Eq.trans facts.2.2
                  (congrArg Value.bool
                    (congrArg (fun z => z || b)
                      (boolPinned model state left a true leftExact facts.1)))))
            (fun rightTrue =>
              Eq.trans rightTrue.2.2
                (congrArg Value.bool
                  (Eq.trans
                    (congrArg (fun z => false || z)
                      (boolPinned model state right b true rightExact rightTrue.2.1))
                    (congrArg (fun z => z || b)
                      (boolPinned model state left a false leftExact rightTrue.1)))))) }

theorem exactScalarAnd (model : Model) (state : State)
    (left right : ScalarExpr) (a b : Bool)
    (leftExact : ExactScalarEvaluation model state left (Value.bool a))
    (rightExact : ExactScalarEvaluation model state right (Value.bool b)) :
    ExactScalarEvaluation model state (ScalarExpr.and left right)
      (Value.bool (a && b)) :=
  { derives :=
      @Bool.rec
        (fun a => Evaluates model [] state left (Value.bool a) →
          Evaluates model [] state (ScalarExpr.and left right) (Value.bool (a && b)))
        (fun lp => Evaluates.andLeftFalse left right b lp rightExact.derives)
        (fun lp =>
          @Bool.rec
            (fun b => Evaluates model [] state right (Value.bool b) →
              Evaluates model [] state (ScalarExpr.and left right)
                (Value.bool (true && b)))
            (fun rp => Evaluates.andRightFalse left right lp rp)
            (fun rp => Evaluates.andTrue left right lp rp)
            b rightExact.derives)
        a leftExact.derives
    unique := fun other evaluation =>
      Or.elim
        (glueEvaluationViewOfEvaluates model [] state
          (ScalarExpr.and left right) other evaluation)
        (fun bothTrue =>
          Eq.trans bothTrue.2.2
            (congrArg Value.bool
              (Eq.trans (congrArg (fun z => z && true)
                  (boolPinned model state left a true leftExact bothTrue.1))
                (congrArg (fun z => a && z)
                  (boolPinned model state right b true rightExact bothTrue.2.1)))))
        (fun rest =>
          Or.elim rest
            (fun leftFalse =>
              Exists.elim leftFalse (fun _ facts =>
                Eq.trans facts.2.2
                  (congrArg Value.bool
                    (congrArg (fun z => z && b)
                      (boolPinned model state left a false leftExact facts.1)))))
            (fun rightFalse =>
              Eq.trans rightFalse.2.2
                (congrArg Value.bool
                  (Eq.trans
                    (congrArg (fun z => true && z)
                      (boolPinned model state right b false rightExact rightFalse.2.1))
                    (congrArg (fun z => z && b)
                      (boolPinned model state left a true leftExact rightFalse.1)))))) }

theorem iffBSelf (t : Bool) : iffB t t = true :=
  @Bool.rec (fun t => iffB t t = true) rfl rfl t

theorem exactScalarIff (model : Model) (state : State)
    (left right : ScalarExpr) (a b : Bool)
    (leftExact : ExactScalarEvaluation model state left (Value.bool a))
    (rightExact : ExactScalarEvaluation model state right (Value.bool b)) :
    ExactScalarEvaluation model state (ScalarExpr.iff left right)
      (Value.bool (iffB a b)) :=
  { derives :=
      @Bool.rec
        (fun a => Evaluates model [] state left (Value.bool a) →
          Evaluates model [] state (ScalarExpr.iff left right) (Value.bool (iffB a b)))
        (fun lp =>
          @Bool.rec
            (fun b => Evaluates model [] state right (Value.bool b) →
              Evaluates model [] state (ScalarExpr.iff left right)
                (Value.bool (iffB false b)))
            (fun rp => Evaluates.iffTrue left right false lp rp)
            (fun rp => Evaluates.iffFalseTrue left right lp rp)
            b rightExact.derives)
        (fun lp =>
          @Bool.rec
            (fun b => Evaluates model [] state right (Value.bool b) →
              Evaluates model [] state (ScalarExpr.iff left right)
                (Value.bool (iffB true b)))
            (fun rp => Evaluates.iffTrueFalse left right lp rp)
            (fun rp => Evaluates.iffTrue left right true lp rp)
            b rightExact.derives)
        a leftExact.derives
    unique := fun other evaluation =>
      Or.elim
        (glueEvaluationViewOfEvaluates model [] state
          (ScalarExpr.iff left right) other evaluation)
        (fun same =>
          Exists.elim same (fun t facts =>
            Eq.trans facts.2.2
              (congrArg Value.bool
                (Eq.trans (Eq.symm (iffBSelf t))
                  (Eq.trans
                    (congrArg (fun z => iffB z t)
                      (boolPinned model state left a t leftExact facts.1))
                    (congrArg (fun z => iffB a z)
                      (boolPinned model state right b t rightExact facts.2.1)))))))
        (fun rest =>
          Or.elim rest
            (fun ft =>
              Eq.trans ft.2.2
                (congrArg Value.bool
                  (Eq.trans
                    (congrArg (fun z => iffB z true)
                      (boolPinned model state left a false leftExact ft.1))
                    (congrArg (fun z => iffB a z)
                      (boolPinned model state right b true rightExact ft.2.1)))))
            (fun tf =>
              Eq.trans tf.2.2
                (congrArg Value.bool
                  (Eq.trans
                    (congrArg (fun z => iffB z false)
                      (boolPinned model state left a true leftExact tf.1))
                    (congrArg (fun z => iffB a z)
                      (boolPinned model state right b false rightExact tf.2.1)))))) }

theorem exactNeqTrue (model : Model) (state : State) (left right : ScalarExpr) (x y : Nat)
    (leftExact : ExactScalarEvaluation model state left (Value.nat x))
    (rightExact : ExactScalarEvaluation model state right (Value.nat y))
    (different : ¬ (x = y)) :
    ExactScalarEvaluation model state (ScalarExpr.neq left right) (Value.bool true) :=
  { derives := Evaluates.neqTrue left right x y leftExact.derives rightExact.derives different
    unique := fun other evaluation =>
      Or.elim
        (glueEvaluationViewOfEvaluates model [] state
          (ScalarExpr.neq left right) other evaluation)
        (fun t => Exists.elim t (fun _ r1 => Exists.elim r1 (fun _ facts => facts.2.2.2)))
        (fun f => Exists.elim f (fun lv r1 => Exists.elim r1 (fun rv facts =>
          False.elim (different
            (Eq.trans (Eq.symm (natPinned model state left x lv leftExact facts.1))
              (Eq.trans facts.2.2.1 (natPinned model state right y rv rightExact facts.2.1))))))) }

theorem exactNeqFalse (model : Model) (state : State) (left right : ScalarExpr) (x y : Nat)
    (leftExact : ExactScalarEvaluation model state left (Value.nat x))
    (rightExact : ExactScalarEvaluation model state right (Value.nat y))
    (same : x = y) :
    ExactScalarEvaluation model state (ScalarExpr.neq left right) (Value.bool false) :=
  { derives := Evaluates.neqFalse left right x y leftExact.derives rightExact.derives same
    unique := fun other evaluation =>
      Or.elim
        (glueEvaluationViewOfEvaluates model [] state
          (ScalarExpr.neq left right) other evaluation)
        (fun t => Exists.elim t (fun lv r1 => Exists.elim r1 (fun rv facts =>
          False.elim (facts.2.2.1
            (Eq.trans (natPinned model state left x lv leftExact facts.1)
              (Eq.trans same (Eq.symm (natPinned model state right y rv rightExact facts.2.1))))))))
        (fun f => Exists.elim f (fun _ r1 => Exists.elim r1 (fun _ facts => facts.2.2.2))) }

theorem exactBoolLit (model : Model) (state : State) (truth : Bool) :
    ExactScalarEvaluation model state (ScalarExpr.bool truth) (Value.bool truth) :=
  { derives := Evaluates.bool truth
    unique := fun other evaluation =>
      glueEvaluationViewOfEvaluates model [] state (ScalarExpr.bool truth) other evaluation }

theorem caseNeq (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.neq l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.neq l r) s = some c →
        Good model.asModel st row s (ScalarExpr.neq l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.nat)
            (compileS model.variables model.constants r Srt.nat) CExpr.neq c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.neq l r)
              (CExpr.neq a b) c facts.2.2
              (Or.elim (boolCases (Nat.beq (evalN row a) (evalN row b)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.neq l r)
                  (fun z => @Bool.rec (fun _ => Bool) true false z) _ true hb
                  (exactNeqFalse model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (natBeqSound (evalN row a) (evalN row b) hb)))
                (fun hb => exactBoolTransport model.asModel st (ScalarExpr.neq l r)
                  (fun z => @Bool.rec (fun _ => Bool) true false z) _ false hb
                  (exactNeqTrue model.asModel st l r (evalN row a) (evalN row b)
                    (ihl Srt.nat a facts.1) (ihr Srt.nat b facts.2.1)
                    (beqFalseNe (evalN row a) (evalN row b) hb)))))))
      s

theorem caseOr (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.or l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.or l r) s = some c →
        Good model.asModel st row s (ScalarExpr.or l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.bool)
            (compileS model.variables model.constants r Srt.bool) CExpr.bor c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.or l r)
              (CExpr.bor a b) c facts.2.2
              (exactScalarOr model.asModel st l r (evalB row a) (evalB row b)
                (ihl Srt.bool a facts.1) (ihr Srt.bool b facts.2.1)))))
      s

theorem caseAnd (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.and l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.and l r) s = some c →
        Good model.asModel st row s (ScalarExpr.and l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.bool)
            (compileS model.variables model.constants r Srt.bool) CExpr.band c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.and l r)
              (CExpr.band a b) c facts.2.2
              (exactScalarAnd model.asModel st l r (evalB row a) (evalB row b)
                (ihl Srt.bool a facts.1) (ihr Srt.bool b facts.2.1)))))
      s

theorem caseIff (model : ScalarModel) (st : State) (row : List Nat) (l r : ScalarExpr)
    (ihl : CompileGood model st row l) (ihr : CompileGood model st row r) :
    CompileGood model st row (ScalarExpr.iff l r) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.iff l r) s = some c →
        Good model.asModel st row s (ScalarExpr.iff l r) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h =>
        Exists.elim (bind2Some (compileS model.variables model.constants l Srt.bool)
            (compileS model.variables model.constants r Srt.bool) CExpr.biff c h)
          (fun a rest => Exists.elim rest (fun b facts =>
            goodTransport model.asModel st row Srt.bool (ScalarExpr.iff l r)
              (CExpr.biff a b) c facts.2.2
              (exactScalarIff model.asModel st l r (evalB row a) (evalB row b)
                (ihl Srt.bool a facts.1) (ihr Srt.bool b facts.2.1)))))
      s

theorem caseBool (model : ScalarModel) (st : State) (row : List Nat) (t : Bool) :
    CompileGood model st row (ScalarExpr.bool t) :=
  fun s =>
    @Srt.rec
      (fun s => ∀ c : CExpr,
        compileS model.variables model.constants (ScalarExpr.bool t) s = some c →
        Good model.asModel st row s (ScalarExpr.bool t) c)
      (fun c h => False.elim (noneNeSome h))
      (fun c h => goodTransport model.asModel st row Srt.bool (ScalarExpr.bool t)
        (CExpr.blit t) c (someInj h) (exactBoolLit model.asModel st t))
      s

theorem compileExact (model : ScalarModel) (st : State) (row : List Nat)
    (denote : ScalarCoordinatesDenote st model.variables row) (e : ScalarExpr) :
    CompileGood model st row e :=
  @ScalarExpr.rec (fun e => CompileGood model st row e)
    (fun n => caseInt model st row n)
    (fun name => caseVar model st row denote name)
    (fun name => caseConst model st row name)
    (fun l r ihl ihr => caseAdd model st row l r ihl ihr)
    (fun l r ihl ihr => caseSub model st row l r ihl ihr)
    (fun l r ihl ihr => caseGt model st row l r ihl ihr)
    (fun l r ihl ihr => caseLe model st row l r ihl ihr)
    (fun l r ihl ihr => caseEq model st row l r ihl ihr)
    (fun l r ihl ihr => caseNeq model st row l r ihl ihr)
    (fun l r ihl ihr => caseOr model st row l r ihl ihr)
    (fun l r ihl ihr => caseAnd model st row l r ihl ihr)
    (fun cnd t f ihc iht ihf => caseIte model st row cnd t f ihc iht ihf)
    (fun l r ihl ihr => caseIff model st row l r ihl ihr)
    (fun _ _ _ _ _ _ _ _ _ h => False.elim (noneNeSome h))
    (fun _ _ _ _ _ h => False.elim (noneNeSome h))
    (fun _ _ _ _ _ _ _ h => False.elim (noneNeSome h))
    (fun _ _ _ _ _ _ _ _ _ h => False.elim (noneNeSome h))
    (fun t => caseBool model st row t)
    e
theorem everyImp {α : Type} (p q : α → Prop) (imp : ∀ x : α, p x → q x) (xs : List α) :
    Every p xs → Every q xs :=
  @List.rec α (fun xs => Every p xs → Every q xs)
    (fun _ => True.intro)
    (fun x _ ih all => And.intro (imp x all.1) (ih all.2))
    xs

def foundIsNone (f : Found) : Bool := @Found.rec (fun _ => Bool) true (fun _ => false) false f

theorem foundCases (f : Found) :
    f = Found.none ∨ (∃ e : ScalarExpr, f = Found.one e) ∨ f = Found.dup :=
  @Found.rec (fun f => f = Found.none ∨ (∃ e : ScalarExpr, f = Found.one e) ∨ f = Found.dup)
    (Or.inl rfl) (fun e => Or.inr (Or.inl ⟨e, rfl⟩)) (Or.inr (Or.inr rfl)) f

theorem oneInj {a b : ScalarExpr} (h : Found.one a = Found.one b) : a = b :=
  congrArg (fun f => @Found.rec (fun _ => ScalarExpr) a (fun x => x) a f) h

-- the "head matches" step of findU never yields Found.none
theorem findStepNotNone (v : ScalarExpr) (f : Found)
    (h : @Found.rec (fun _ => Found) (Found.one v) (fun _ => Found.dup) Found.dup f = Found.none) :
    False :=
  @Found.rec
    (fun f => @Found.rec (fun _ => Found) (Found.one v) (fun _ => Found.dup) Found.dup f = Found.none → False)
    (fun k => Bool.noConfusion (congrArg foundIsNone k))
    (fun _ k => Bool.noConfusion (congrArg foundIsNone k))
    (fun k => Bool.noConfusion (congrArg foundIsNone k))
    f h

-- the "head matches" step yields Found.one e only from an empty tail
theorem findStepOne (v e : ScalarExpr) (f : Found)
    (h : @Found.rec (fun _ => Found) (Found.one v) (fun _ => Found.dup) Found.dup f = Found.one e) :
    f = Found.none ∧ v = e :=
  @Found.rec
    (fun f => @Found.rec (fun _ => Found) (Found.one v) (fun _ => Found.dup) Found.dup f = Found.one e →
      f = Found.none ∧ v = e)
    (fun k => ⟨rfl, oneInj k⟩)
    (fun _ k => False.elim (Bool.noConfusion (congrArg
      (fun g => @Found.rec (fun _ => Bool) false (fun _ => false) true g) k)))
    (fun k => False.elim (Bool.noConfusion (congrArg
      (fun g => @Found.rec (fun _ => Bool) false (fun _ => false) true g) k)))
    f h

theorem findUStep (u : Update) (rest : List Update) (name : String) (b : Bool)
    (hd : decide (u.var = name) = b) :
    findU (u :: rest) name =
      @Bool.rec (fun _ => Found) (findU rest name)
        (@Found.rec (fun _ => Found) (Found.one u.value) (fun _ => Found.dup) Found.dup (findU rest name)) b :=
  congrArg (fun z => @Bool.rec (fun _ => Found) (findU rest name)
    (@Found.rec (fun _ => Found) (Found.one u.value) (fun _ => Found.dup) Found.dup (findU rest name)) z) hd

theorem findUNone (name : String) (us : List Update) :
    findU us name = Found.none → Every (fun u : Update => ¬ (u.var = name)) us :=
  @List.rec Update
    (fun us => findU us name = Found.none → Every (fun u : Update => ¬ (u.var = name)) us)
    (fun _ => True.intro)
    (fun u rest ih h =>
      Or.elim (boolCases (decide (u.var = name)))
        (fun hd => False.elim (findStepNotNone u.value (findU rest name)
          (Eq.trans (Eq.symm (findUStep u rest name true hd)) h)))
        (fun hd => And.intro (of_decide_eq_false hd)
          (ih (Eq.trans (Eq.symm (findUStep u rest name false hd)) h))))
    us

theorem findUHitStep (u : Update) (rest : List Update) (name : String) (e : ScalarExpr)
    (step : findU rest name = Found.none ∧ u.value = e) (same : u.var = name) :
    (Every (fun w : Update => w.var = name → w.value = e) (u :: rest) ∧ ∃ w : Update, Member w (u :: rest) ∧ w.var = name) :=
  And.intro
    (And.intro (fun _ : u.var = name => step.2)
      (everyImp (fun w : Update => ¬ (w.var = name))
        (fun w : Update => w.var = name → w.value = e)
        (fun w nw same' => False.elim (nw same')) rest
        (findUNone name rest step.1)))
    (@Exists.intro Update (fun w => Member w (u :: rest) ∧ w.var = name) u
      (And.intro (Member.head rest) same))

theorem findUMissStep (u : Update) (rest : List Update) (name : String) (e : ScalarExpr)
    (inner : (Every (fun w : Update => w.var = name → w.value = e) rest ∧ ∃ w : Update, Member w rest ∧ w.var = name)) (differ : ¬ (u.var = name)) :
    (Every (fun w : Update => w.var = name → w.value = e) (u :: rest) ∧ ∃ w : Update, Member w (u :: rest) ∧ w.var = name) :=
  And.intro
    (And.intro (fun same : u.var = name => (False.elim (differ same) : u.value = e)) inner.1)
    (Exists.elim inner.2 (fun w facts =>
      @Exists.intro Update (fun w => Member w (u :: rest) ∧ w.var = name) w
        (And.intro (Member.tail u rest facts.1) facts.2)))

theorem findUOne (name : String) (e : ScalarExpr) (us : List Update) :
    findU us name = Found.one e → (Every (fun w : Update => w.var = name → w.value = e) us ∧ ∃ w : Update, Member w us ∧ w.var = name) :=
  @List.rec Update
    (fun us => findU us name = Found.one e → (Every (fun w : Update => w.var = name → w.value = e) us ∧ ∃ w : Update, Member w us ∧ w.var = name))
    (fun h => False.elim (Bool.noConfusion (congrArg foundIsNone h)))
    (fun u rest ih h =>
      Or.elim (boolCases (decide (u.var = name)))
        (fun hd => findUHitStep u rest name e
          (findStepOne u.value e (findU rest name)
            (Eq.trans (Eq.symm (findUStep u rest name true hd)) h))
          (of_decide_eq_true hd))
        (fun hd => findUMissStep u rest name e
          (ih (Eq.trans (Eq.symm (findUStep u rest name false hd)) h))
          (of_decide_eq_false hd)))
    us
theorem memberConsInv {α : Type} {x hd : α} {tl : List α} (m : Member x (hd :: tl)) :
    x = hd ∨ Member x tl :=
  @Member.rec α x
    (fun list _ => @List.rec α (fun _ => Prop) True (fun h t _ => x = h ∨ Member x t) list)
    (fun tail => Or.inl rfl)
    (fun h tail mt _ => Or.inr mt)
    (hd :: tl) m

theorem mapOptMember {α β : Type} (f : α → Option β) (xs : List α) :
    ∀ ys : List β, mapOpt f xs = some ys →
      ∀ x : α, Member x xs → ∃ y : β, Member y ys ∧ f x = some y :=
  @List.rec α
    (fun xs => ∀ ys : List β, mapOpt f xs = some ys →
      ∀ x : α, Member x xs → ∃ y : β, Member y ys ∧ f x = some y)
    (fun ys _ x mem => False.elim (memberNilFalse mem))
    (fun x0 rest ih ys h x mem =>
      Exists.elim (optionBindSome (f x0)
          (fun y => @Option.rec (List β) (fun _ => Option (List β)) none
            (fun ys => some (y :: ys)) (mapOpt f rest)) ys h)
        (fun y0 f1 =>
          Exists.elim (optionMapSome (mapOpt f rest) (fun ys' => y0 :: ys') ys f1.2)
            (fun ys' f2 =>
              Eq.mpr
                (congrArg (fun zs => ∃ y : β, Member y zs ∧ f x = some y) (Eq.symm f2.2))
                (Or.elim (memberConsInv mem)
                  (fun same =>
                    @Exists.intro β (fun y => Member y (y0 :: ys') ∧ f x = some y) y0
                      (And.intro (Member.head ys')
                        (Eq.trans (congrArg f same) f1.1)))
                  (fun later =>
                    Exists.elim (ih ys' f2.1 x later) (fun y f3 =>
                      @Exists.intro β (fun y => Member y (y0 :: ys') ∧ f x = some y) y
                        (And.intro (Member.tail y0 ys' f3.1) f3.2)))))))
    xs

theorem compileActionSound (vars : List StateVar) (consts : List Constant)
    (a : Action) (ca : CAction) (h : compileAction vars consts a = some ca) :
    compileGuard vars consts a.guard = some ca.guard ∧
      compileUpds vars consts a.updates vars = some ca.upd :=
  Exists.elim (optionBindSome (compileGuard vars consts a.guard)
      (fun g => @Option.rec (List (Option CExpr)) (fun _ => Option CAction) none
        (fun u => some (CAction.mk g u)) (compileUpds vars consts a.updates vars)) ca h)
    (fun g f1 =>
      Exists.elim (optionMapSome (compileUpds vars consts a.updates vars)
          (fun u => CAction.mk g u) ca f1.2)
        (fun u f2 =>
          And.intro
            (Eq.trans f1.1 (congrArg some (congrArg CAction.guard f2.2)))
            (Eq.trans f2.1 (congrArg some (congrArg CAction.upd f2.2)))))

theorem compileModelSound (model : ScalarModel) (cm : CModel)
    (h : compileModel model = some cm) :
    cm.init = initRow model.variables ∧
    mapOpt (compileAction model.variables model.constants) model.actions = some cm.actions ∧
    mapOpt (fun inv : Invariant => compileS model.variables model.constants inv.value Srt.bool)
      model.invariants = some cm.invs :=
  Exists.elim (optionBindSome
      (mapOpt (compileAction model.variables model.constants) model.actions)
      (fun acts => @Option.rec (List CExpr) (fun _ => Option CModel) none
        (fun invs => some (CModel.mk (initRow model.variables) acts invs))
        (mapOpt (fun inv : Invariant => compileS model.variables model.constants inv.value Srt.bool)
          model.invariants)) cm h)
    (fun acts f1 =>
      Exists.elim (optionMapSome
          (mapOpt (fun inv : Invariant => compileS model.variables model.constants inv.value Srt.bool)
            model.invariants)
          (fun invs => CModel.mk (initRow model.variables) acts invs) cm f1.2)
        (fun invs f2 =>
          And.intro (Eq.symm (congrArg CModel.init f2.2))
            (And.intro (Eq.trans f1.1 (congrArg some (congrArg CModel.actions f2.2)))
              (Eq.trans f2.1 (congrArg some (congrArg CModel.invs f2.2))))))

theorem guardSound (model : ScalarModel) (st : State) (row : List Nat)
    (denote : ScalarCoordinatesDenote st model.variables row) (g : Guard) (cg : CExpr)
    (h : compileGuard model.variables model.constants g = some cg)
    (holds : GuardHolds model.asModel st g) : evalB row cg = true :=
  @Guard.rec
    (fun g => compileGuard model.variables model.constants g = some cg →
      GuardHolds model.asModel st g → evalB row cg = true)
    (fun k _ => Eq.mpr (congrArg (fun z => evalB row z = true) (Eq.symm (someInj k))) rfl)
    (fun e k ev => Eq.symm (congrArg valueBoolProjection
      ((compileExact model st row denote e Srt.bool cg k).unique (Value.bool true) ev)))
    g h holds

theorem initDenotes (model : ScalarModel) (st : State) (init : Initial model.asModel st)
    (vs : List StateVar) :
    (∀ entry : StateVar, Member entry vs → Member entry model.variables) →
    ScalarCoordinatesDenote st vs (initRow vs) :=
  @List.rec StateVar
    (fun vs => (∀ entry : StateVar, Member entry vs → Member entry model.variables) →
      ScalarCoordinatesDenote st vs (initRow vs))
    (fun _ => True.intro)
    (fun v rest ih sub =>
      And.intro (init.2.1 v (sub v (Member.head rest)))
        (ih (fun entry m => sub entry (Member.tail v rest m))))
    vs

theorem compileUpdsStep (vars : List StateVar) (consts : List Constant) (us : List Update)
    (v : StateVar) (rest : List StateVar) (f : Found) (hf : findU us v.name = f) :
    compileUpds vars consts us (v :: rest) =
      @Found.rec (fun _ => Option (List (Option CExpr)))
        (consOpt none (compileUpds vars consts us rest))
        (fun e => @Option.rec CExpr (fun _ => Option (List (Option CExpr))) none
            (fun c => consOpt (some c) (compileUpds vars consts us rest))
            (compileS vars consts e Srt.nat))
        none f :=
  congrArg (fun z => @Found.rec (fun _ => Option (List (Option CExpr)))
        (consOpt none (compileUpds vars consts us rest))
        (fun e => @Option.rec CExpr (fun _ => Option (List (Option CExpr))) none
            (fun c => consOpt (some c) (compileUpds vars consts us rest))
            (compileS vars consts e Srt.nat))
        none z) hf

theorem succUnchanged (model : ScalarModel) (a : Action) (before after : State)
    (row : List Nat) (v : StateVar) (rest : List StateVar) (value : Nat) (tail upd' : List Nat)
    (vmem : Member v model.variables) (coord : before.scalar v.name = value)
    (none_ : findU a.updates v.name = Found.none)
    (holds : ActionHolds model.asModel a before after) :
    after.scalar v.name = value :=
  scalarCoordinateOfUnchangedAction model.asModel a before after v value vmem coord
    (findUNone v.name a.updates none_) holds

theorem succUpdated (model : ScalarModel) (a : Action) (before after : State)
    (row : List Nat) (denote : ScalarCoordinatesDenote before model.variables row)
    (v : StateVar) (e : ScalarExpr) (c : CExpr)
    (vmem : Member v model.variables)
    (one : findU a.updates v.name = Found.one e)
    (hc : compileS model.variables model.constants e Srt.nat = some c)
    (holds : ActionHolds model.asModel a before after) :
    after.scalar v.name = evalN row c :=
  scalarCoordinateOfUpdatedAction model.asModel a before after v (evalN row c) vmem
    (everyImp (fun w : Update => w.var = v.name → w.value = e)
      (fun w : Update => w.var = v.name →
        Evaluates model.asModel [] before w.value (Value.nat (after.scalar v.name)) →
        after.scalar v.name = evalN row c)
      (fun w imp same ev =>
        congrArg valueNatProjection
          ((compileExact model before row denote e Srt.nat c hc).unique
            (Value.nat (after.scalar v.name))
            (Eq.mp (congrArg (fun z => Evaluates model.asModel [] before z
                (Value.nat (after.scalar v.name))) (imp same)) ev)))
      a.updates (findUOne v.name e a.updates one).1)
    (findUOne v.name e a.updates one).2 holds
def SuccGoal (model : ScalarModel) (a : Action) (before after : State) (row : List Nat)
    (vs : List StateVar) : Prop :=
  (∀ entry : StateVar, Member entry vs → Member entry model.variables) →
  ∀ (tail : List Nat) (upd : List (Option CExpr)),
    ScalarCoordinatesDenote before vs tail →
    compileUpds model.variables model.constants a.updates vs = some upd →
    ScalarCoordinatesDenote after vs (succRow row upd tail)

theorem succConsNone (model : ScalarModel) (a : Action) (before after : State) (row : List Nat)
    (v : StateVar) (rest : List StateVar) (ih : SuccGoal model a before after row rest)
    (sub : ∀ entry : StateVar, Member entry (v :: rest) → Member entry model.variables)
    (value : Nat) (tail : List Nat) (upd : List (Option CExpr))
    (dBefore : ScalarCoordinatesDenote before (v :: rest) (value :: tail))
    (hf : findU a.updates v.name = Found.none)
    (h : compileUpds model.variables model.constants a.updates (v :: rest) = some upd)
    (holds : ActionHolds model.asModel a before after) :
    ScalarCoordinatesDenote after (v :: rest) (succRow row upd (value :: tail)) :=
  Exists.elim (optionMapSome (compileUpds model.variables model.constants a.updates rest)
      (fun xs => none :: xs) upd
      (Eq.trans (Eq.symm (compileUpdsStep model.variables model.constants a.updates v rest
        Found.none hf)) h))
    (fun upd' f =>
      Eq.mpr (congrArg (fun z => ScalarCoordinatesDenote after (v :: rest) (succRow row z (value :: tail)))
          (Eq.symm f.2))
        (And.intro
          (succUnchanged model a before after row v rest value tail [] (sub v (Member.head rest))
            dBefore.1 hf holds)
          (ih (fun entry m => sub entry (Member.tail v rest m)) tail upd' dBefore.2 f.1)))

theorem succConsOne (model : ScalarModel) (a : Action) (before after : State) (row : List Nat)
    (denote : ScalarCoordinatesDenote before model.variables row)
    (v : StateVar) (rest : List StateVar) (ih : SuccGoal model a before after row rest)
    (sub : ∀ entry : StateVar, Member entry (v :: rest) → Member entry model.variables)
    (value : Nat) (tail : List Nat) (upd : List (Option CExpr))
    (dBefore : ScalarCoordinatesDenote before (v :: rest) (value :: tail))
    (e : ScalarExpr) (hf : findU a.updates v.name = Found.one e)
    (h : compileUpds model.variables model.constants a.updates (v :: rest) = some upd)
    (holds : ActionHolds model.asModel a before after) :
    ScalarCoordinatesDenote after (v :: rest) (succRow row upd (value :: tail)) :=
  Exists.elim (optionBindSome (compileS model.variables model.constants e Srt.nat)
      (fun c => consOpt (some c) (compileUpds model.variables model.constants a.updates rest)) upd
      (Eq.trans (Eq.symm (compileUpdsStep model.variables model.constants a.updates v rest
        (Found.one e) hf)) h))
    (fun c f1 =>
      Exists.elim (optionMapSome (compileUpds model.variables model.constants a.updates rest)
          (fun xs => some c :: xs) upd f1.2)
        (fun upd' f2 =>
          Eq.mpr (congrArg (fun z => ScalarCoordinatesDenote after (v :: rest) (succRow row z (value :: tail)))
              (Eq.symm f2.2))
            (And.intro
              (succUpdated model a before after row denote v e c (sub v (Member.head rest)) hf f1.1 holds)
              (ih (fun entry m => sub entry (Member.tail v rest m)) tail upd' dBefore.2 f2.1))))

theorem succDenotes (model : ScalarModel) (a : Action) (before after : State) (row : List Nat)
    (denote : ScalarCoordinatesDenote before model.variables row)
    (holds : ActionHolds model.asModel a before after) (vs : List StateVar) :
    SuccGoal model a before after row vs :=
  @List.rec StateVar (fun vs => SuccGoal model a before after row vs)
    (fun _ tail upd _ h =>
      Eq.mpr (congrArg (fun z => ScalarCoordinatesDenote after [] (succRow row z tail))
          (Eq.symm (someInj h)))
        True.intro)
    (fun v rest ih sub tail =>
      @List.rec Nat
        (fun tail => ∀ upd : List (Option CExpr),
          ScalarCoordinatesDenote before (v :: rest) tail →
          compileUpds model.variables model.constants a.updates (v :: rest) = some upd →
          ScalarCoordinatesDenote after (v :: rest) (succRow row upd tail))
        (fun upd dBefore _ => False.elim dBefore)
        (fun value tail' _ upd dBefore h =>
          Or.elim (foundCases (findU a.updates v.name))
            (fun hf => succConsNone model a before after row v rest ih sub value tail' upd
              dBefore hf h holds)
            (fun rest2 => Or.elim rest2
              (fun one => Exists.elim one (fun e hf =>
                succConsOne model a before after row denote v rest ih sub value tail' upd
                  dBefore e hf h holds))
              (fun hf => False.elim (noneNeSome
                (Eq.trans (Eq.symm (compileUpdsStep model.variables model.constants a.updates
                  v rest Found.dup hf)) h)))))
        tail)
    vs


-- ===== the three premises of scalarSafetyClaimOfRows, over any index =====
-- `htree`: every row the index `t` answers for is in `rows`
theorem initiationOfCheck (model : ScalarModel) (rows : List (List Nat)) (t : RIndex) (cm : CModel)
    (htree : ∀ r : List Nat, memK t r = true → Member r rows)
    (hinit : cm.init = initRow model.variables) (hmem : memK t cm.init = true) :
    ∀ st : State, Initial model.asModel st → ScalarRowsStrengthening model rows st :=
  fun st init =>
    @Exists.intro (List Nat) (fun r => Member r rows ∧ ScalarRowDenotes model r st)
      (initRow model.variables)
      (And.intro
        (Eq.mpr (congrArg (fun z => Member z rows) (Eq.symm hinit)) (htree cm.init hmem))
        (And.intro init.1 (initDenotes model st init model.variables (fun entry m => m))))

theorem rowOkParts (cm : CModel) (t : RIndex) (row : List Nat)
    (h : rowOk cm t row = true) :
    allB (actionOk t row) cm.actions = true ∧ allB (fun ci => evalB row ci) cm.invs = true :=
  boolRecAnd (allB (actionOk t row) cm.actions) (allB (fun ci => evalB row ci) cm.invs) h

theorem preservationOfCheck (model : ScalarModel) (rows : List (List Nat)) (t : RIndex) (cm : CModel)
    (hinvs : mapOpt (fun inv : Invariant => compileS model.variables model.constants inv.value Srt.bool)
      model.invariants = some cm.invs)
    (hall : allB (rowOk cm t) rows = true) :
    ∀ st : State, ScalarRowsStrengthening model rows st → AllInvariantsHold model.asModel st :=
  fun st strong inv mem =>
    Exists.elim strong (fun row f =>
      Exists.elim (mapOptMember
          (fun inv : Invariant => compileS model.variables model.constants inv.value Srt.bool)
          model.invariants cm.invs hinvs inv mem)
        (fun ci g =>
          Eq.mp
            (congrArg (fun z => Evaluates model.asModel [] st inv.value (Value.bool z))
              (allBSound (fun ci => evalB row ci) cm.invs
                (rowOkParts cm t row (allBSound (rowOk cm t) rows hall row f.1)).2 ci g.1))
            (compileExact model st row f.2.2 inv.value Srt.bool ci g.2).derives))

theorem consecutionOfCheck (model : ScalarModel) (rows : List (List Nat)) (t : RIndex) (cm : CModel)
    (htree : ∀ r : List Nat, memK t r = true → Member r rows)
    (hacts : mapOpt (compileAction model.variables model.constants) model.actions = some cm.actions)
    (hall : allB (rowOk cm t) rows = true) :
    ∀ before after : State,
      ScalarRowsStrengthening model rows before →
      Next model.asModel before after →
      ScalarRowsStrengthening model rows after :=
  fun before after strong next =>
    Exists.elim strong (fun row f =>
      Exists.elim next (fun a g =>
        Exists.elim (mapOptMember (compileAction model.variables model.constants)
            model.actions cm.actions hacts a g.1)
          (fun ca k =>
            @Exists.intro (List Nat) (fun r => Member r rows ∧ ScalarRowDenotes model r after)
              (succRow row ca.upd row)
              (And.intro
                (htree (succRow row ca.upd row)
                  (boolRecImp (evalB row ca.guard) (memK t (succRow row ca.upd row))
                    (allBSound (actionOk t row) cm.actions
                      (rowOkParts cm t row (allBSound (rowOk cm t) rows hall row f.1)).1
                      ca k.1)
                    (guardSound model before row f.2.2 a.guard ca.guard
                      (compileActionSound model.variables model.constants a ca k.2).1 g.2.1)))
                (And.intro g.2.2.1
                  (succDenotes model a before after row f.2.2 g.2 model.variables
                    (fun entry m => m) row ca.upd f.2.2
                    (compileActionSound model.variables model.constants a ca k.2).2))))))

-- one indexed check that answered true proves the model safe
theorem indexedSafety (model : ScalarModel) (cm : CModel) (hc : compileModel model = some cm)
    (rows : List (List Nat)) (t : RIndex) (cover : ∀ x : List Nat, InTree x t → Member x rows)
    (h : checkIndexed cm rows t = true) : ScalarModel.safetyClaim model :=
  (fun parts : memK t cm.init = true ∧ allB (rowOk cm t) rows = true =>
    scalarSafetyClaimOfRows model rows
      (initiationOfCheck model rows t cm (memKCover t rows cover)
        (compileModelSound model cm hc).1 parts.1)
      (consecutionOfCheck model rows t cm (memKCover t rows cover)
        (compileModelSound model cm hc).2.1 parts.2)
      (preservationOfCheck model rows t cm (compileModelSound model cm hc).2.2 parts.2))
  (boolRecAnd (memK t cm.init) (allB (rowOk cm t) rows) h)

-- ===== soundness and the front door =====
theorem scalarSafetyOfCheck (model : ScalarModel) (rows : List (List Nat))
    (h : checkScalarRows model rows = true) : ScalarModel.safetyClaim model :=
  Exists.elim (compiledOfCheck model rows h) (fun cm facts =>
    Exists.elim (checkCompiledSound cm rows
        (Eq.trans (Eq.symm (forceCMEq cm (fun cm' => checkCompiled cm' rows))) facts.2))
      (fun t parts => indexedSafety model cm facts.1 rows t parts.1 parts.2))

-- The Bool front door.  `fuel` is the state budget (section 4): accepted iff
-- the model is in the grammar, has at most `fuel` reachable states, and is
-- safe.  On a rejection it cannot say which; `proveSafe` (section 6) can.
--   theorem safe : ScalarModel.safetyClaim M := checkSafety M 64 rfl
theorem checkSafety (model : ScalarModel) (fuel : Nat)
    (h : checkScalarRows model (reachRows model fuel) = true) : ScalarModel.safetyClaim model :=
  scalarSafetyOfCheck model (reachRows model fuel) h


-- ===== 6. the verdict door: a rejection that says why =====
--
-- `proveSafe M fuel rfl` proves what `checkSafety M fuel rfl` proves, at no
-- more cost (it checks in the search's own tree: 1-4% fewer instructions,
-- measured), but its hypothesis is `safetyVerdict M fuel = CheckVerdict.ok`,
-- so a rejected island prints the actual verdict (clean 0.9.0 spells 1 as
-- `Nat.succ 0`):
--   unsupported         the model leaves the grammar (header);
--   invariantFails r i  reachable row r breaks invariant #i, shallowest r
--                       first, even when the budget also ran out;
--   budgetExhausted     more than `fuel` reachable states and no violation
--                       among the rows held: raise fuel;
--   ok                  accepted.
-- `ok` is TRUSTED: it is answered only when the trusted check, run on the
-- closed search, says true, and `proveSafe` turns it into the safety claim.
-- Every other answer is an UNTRUSTED explanation that never reads `ok`
-- (`CheckVerdict.notOk`).  The explanation reuses the search and
-- the index the check already built, so a rejection costs at most one more
-- pass over the rows.  Two other untrusted cases name a broken certificate,
-- and arise from `explainCheck` on hand-written rows: initMissing r, and
-- successorMissing r i s (action #i takes row r to row s, which is missing).
--
-- Verdicts compare as terms or as a Bool, both linear in the rows:
--   example : safetyVerdict M 64 = CheckVerdict.invariantFails [1, 0] 0 := rfl
--   example : CheckVerdict.beq (safetyVerdict M 64) CheckVerdict.budgetExhausted = true := rfl
-- Verdict rows are values (section 3), so they print and compare small.
inductive CheckVerdict where
  | ok
  | unsupported
  | budgetExhausted
  | initMissing : List Nat → CheckVerdict
  | invariantFails : List Nat → Nat → CheckVerdict
  | successorMissing : List Nat → Nat → List Nat → CheckVerdict

def CheckVerdict.beq (a b : CheckVerdict) : Bool :=
  @CheckVerdict.rec (fun _ => Bool)
    (@CheckVerdict.rec (fun _ => Bool) true false false
      (fun _ => false) (fun _ _ => false) (fun _ _ _ => false) b)
    (@CheckVerdict.rec (fun _ => Bool) false true false
      (fun _ => false) (fun _ _ => false) (fun _ _ _ => false) b)
    (@CheckVerdict.rec (fun _ => Bool) false false true
      (fun _ => false) (fun _ _ => false) (fun _ _ _ => false) b)
    (fun r => @CheckVerdict.rec (fun _ => Bool) false false false
      (fun r' => rowEq r r') (fun _ _ => false) (fun _ _ _ => false) b)
    (fun r i => @CheckVerdict.rec (fun _ => Bool) false false false
      (fun _ => false)
      (fun r' i' => @Bool.rec (fun _ => Bool) false (Nat.beq i i') (rowEq r r'))
      (fun _ _ _ => false) b)
    (fun r i s => @CheckVerdict.rec (fun _ => Bool) false false false
      (fun _ => false) (fun _ _ => false)
      (fun r' i' s' => @Bool.rec (fun _ => Bool) false
        (@Bool.rec (fun _ => Bool) false (rowEq s s') (Nat.beq i i')) (rowEq r r'))
      b)
    a

def CheckVerdict.isOk (v : CheckVerdict) : Bool :=
  @CheckVerdict.rec (fun _ => Bool) true false false
    (fun _ => false) (fun _ _ => false) (fun _ _ _ => false) v

-- an untrusted explanation, kept away from `ok` (an `ok` reads `unsupported`)
def CheckVerdict.notOk (v : CheckVerdict) : CheckVerdict :=
  @CheckVerdict.rec (fun _ => CheckVerdict) CheckVerdict.unsupported CheckVerdict.unsupported
    CheckVerdict.budgetExhausted (fun r => CheckVerdict.initMissing r)
    (fun r i => CheckVerdict.invariantFails r i) (fun r i s => CheckVerdict.successorMissing r i s) v

-- identity on verdicts: a door's computation becomes a recursor major
-- premise (full whnf), as for `checkScalarRows`
def verdictId (v : CheckVerdict) : CheckVerdict :=
  @CheckVerdict.rec (fun _ => CheckVerdict) CheckVerdict.ok CheckVerdict.unsupported
    CheckVerdict.budgetExhausted (fun r => CheckVerdict.initMissing r)
    (fun r i => CheckVerdict.invariantFails r i) (fun r i s => CheckVerdict.successorMissing r i s) v

-- first `some` of `f i x` over `xs`, with `i` the (forced) position
def firstSomeIdx {α β : Type} (f : Nat → α → Option β) (xs : List α) : Option β :=
  (@List.rec α (fun _ => Nat → Option β) (fun _ => none)
    (fun x _ ih i => @Option.rec β (fun _ => Option β) (forceNat (Nat.succ i) ih) (fun b => some b) (f i x))
    xs) 0

def firstRow (f : List Nat → Option CheckVerdict) (rows : List (List Nat)) : Option CheckVerdict :=
  @List.rec (List Nat) (fun _ => Option CheckVerdict) none
    (fun r _ ih => @Option.rec CheckVerdict (fun _ => Option CheckVerdict) ih (fun v => some v) (f r))
    rows

-- the search lists rows newest first; diagnostics scan oldest (shallowest) first
def revRows (rows : List (List Nat)) : List (List Nat) :=
  (@List.rec (List Nat) (fun _ => List (List Nat) → List (List Nat)) (fun acc => acc)
    (fun r _ ih acc => ih (r :: acc)) rows) []

def invVerdict (cm : CModel) (row : List Nat) : Option CheckVerdict :=
  firstSomeIdx (fun (i : Nat) (ci : CExpr) =>
      @Bool.rec (fun _ => Option CheckVerdict) (some (CheckVerdict.invariantFails row i)) none
        (evalB row ci))
    cm.invs

def succVerdict (cm : CModel) (t : RIndex) (row : List Nat) : Option CheckVerdict :=
  firstSomeIdx (fun (i : Nat) (ca : CAction) =>
      @Bool.rec (fun _ => Option CheckVerdict) none
        (forceRow (succRow row ca.upd row) (fun s => forceNat (rowHash s) (fun h =>
          @Bool.rec (fun _ => Option CheckVerdict) (some (CheckVerdict.successorMissing row i s)) none
            (indexMemH h s t))))
        (evalB row ca.guard))
    cm.actions

-- why `checkIndexed cm rows t` answers as it does, scanning `scan` (the
-- same rows, in the order to report them); `ok` iff it says true
def explainIndexed (cm : CModel) (scan : List (List Nat)) (t : RIndex) : CheckVerdict :=
  @Bool.rec (fun _ => CheckVerdict)
    (forceRow cm.init (fun i => CheckVerdict.initMissing i))
    (@Option.rec CheckVerdict (fun _ => CheckVerdict) CheckVerdict.ok (fun v => v)
      (firstRow (fun r => @Option.rec CheckVerdict (fun _ => Option CheckVerdict)
          (succVerdict cm t r) (fun v => some v) (invVerdict cm r))
        scan))
    (memK t cm.init)

-- `ok` exactly when the trusted check says true; else the explanation
def verdictIndexed (cm : CModel) (rows scan : List (List Nat)) (t : RIndex) : CheckVerdict :=
  @Bool.rec (fun _ => CheckVerdict) (CheckVerdict.notOk (explainIndexed cm scan t))
    CheckVerdict.ok (checkIndexed cm rows t)

-- a cut-off search: the first invariant failure among the rows held, or
-- `budgetExhausted`; never `ok`
def exhaustedVerdict (cm : CModel) (all : List (List Nat)) : CheckVerdict :=
  @Option.rec CheckVerdict (fun _ => CheckVerdict) CheckVerdict.budgetExhausted (fun v => v)
    (firstRow (invVerdict cm) (revRows all))

-- One search.  A closed one is checked in its own index: the rows are the
-- tree's rows (`treeRowsAcc t []`, what `reachRows` returns) and membership
-- is answered by the tree itself, so nothing is rebuilt; it is explained in
-- BFS order.
def verdictCompiled (cm : CModel) (s : Search) : CheckVerdict :=
  @Search.rec (fun _ => CheckVerdict)
    (fun t all => verdictIndexed cm (treeRowsAcc t []) (revRows all) t)
    (fun all => CheckVerdict.notOk (exhaustedVerdict cm all))
    s

-- the verdict door's hypothesis: see the head of this section
def safetyVerdict (model : ScalarModel) (fuel : Nat) : CheckVerdict :=
  verdictId (@Option.rec CModel (fun _ => CheckVerdict) CheckVerdict.unsupported
    (fun cm0 => forceCM cm0 (fun cm => verdictCompiled cm (searchCompiled cm fuel)))
    (compileModel model))

-- why `checkScalarRows model rows` answers as it does (`ok` iff true),
-- scanning `rows` in their given order; untrusted
def explainCheck (model : ScalarModel) (rows : List (List Nat)) : CheckVerdict :=
  verdictId (@Option.rec CModel (fun _ => CheckVerdict) CheckVerdict.unsupported
    (fun cm0 => forceCM cm0 (fun cm => forceSpine rows (fun rs => indexK rs (explainIndexed cm rs))))
    (compileModel model))

theorem verdictIdEq (v : CheckVerdict) : verdictId v = v :=
  @CheckVerdict.rec (fun v => verdictId v = v) rfl rfl rfl
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) v

theorem isOkNotOk (v : CheckVerdict) : CheckVerdict.isOk (CheckVerdict.notOk v) = false :=
  @CheckVerdict.rec (fun v => CheckVerdict.isOk (CheckVerdict.notOk v) = false) rfl rfl rfl
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) v

theorem notOkNeOk (v : CheckVerdict) (h : CheckVerdict.notOk v = CheckVerdict.ok) : False :=
  Bool.noConfusion (Eq.trans (Eq.symm (isOkNotOk v)) (congrArg CheckVerdict.isOk h))

theorem unsupportedNeOk (h : CheckVerdict.unsupported = CheckVerdict.ok) : False :=
  Bool.noConfusion (congrArg CheckVerdict.isOk h)

theorem optionRecOk {α : Type} (o : Option α) (f : α → CheckVerdict)
    (h : @Option.rec α (fun _ => CheckVerdict) CheckVerdict.unsupported f o = CheckVerdict.ok) :
    ∃ x : α, o = some x ∧ f x = CheckVerdict.ok :=
  @Option.rec α
    (fun o => @Option.rec α (fun _ => CheckVerdict) CheckVerdict.unsupported f o = CheckVerdict.ok →
      ∃ x : α, o = some x ∧ f x = CheckVerdict.ok)
    (fun k => False.elim (unsupportedNeOk k))
    (fun x k => ⟨x, rfl, k⟩)
    o h

theorem verdictIndexedOk (cm : CModel) (rows scan : List (List Nat)) (t : RIndex)
    (h : verdictIndexed cm rows scan t = CheckVerdict.ok) : checkIndexed cm rows t = true :=
  @Bool.rec
    (fun b => @Bool.rec (fun _ => CheckVerdict) (CheckVerdict.notOk (explainIndexed cm scan t))
        CheckVerdict.ok b = CheckVerdict.ok → b = true)
    (fun hf => False.elim (notOkNeOk (explainIndexed cm scan t) hf))
    (fun _ => rfl)
    (checkIndexed cm rows t) h

-- every row of a tree is among its walk-order rows
theorem treeMember (r : List Nat) (t : RIndex) :
    ∀ acc : List (List Nat), (InTree r t ∨ Member r acc) → Member r (treeRowsAcc t acc) :=
  @RIndex.rec
    (fun t => ∀ acc : List (List Nat), (InTree r t ∨ Member r acc) → Member r (treeRowsAcc t acc))
    (fun acc k => Or.elim k (fun f => False.elim f) (fun m => m))
    (fun l h' r' rr ihl ihr acc k =>
      ihl (r' :: treeRowsAcc rr acc)
        (Or.elim k
          (fun inT => Or.elim inT
            (fun inL => Or.inl inL)
            (fun rest => Or.elim rest
              (fun e => Or.inr (Eq.mpr (congrArg (fun z => Member z (r' :: treeRowsAcc rr acc)) e)
                (Member.head (treeRowsAcc rr acc))))
              (fun inR => Or.inr (Member.tail r' (treeRowsAcc rr acc) (ihr acc (Or.inl inR))))))
          (fun m => Or.inr (Member.tail r' (treeRowsAcc rr acc) (ihr acc (Or.inr m))))))
    t

theorem verdictCompiledSound (model : ScalarModel) (cm : CModel) (hc : compileModel model = some cm)
    (s : Search) (h : verdictCompiled cm s = CheckVerdict.ok) : ScalarModel.safetyClaim model :=
  @Search.rec (fun s => verdictCompiled cm s = CheckVerdict.ok → ScalarModel.safetyClaim model)
    (fun t all k =>
      indexedSafety model cm hc (treeRowsAcc t []) t (fun x i => treeMember x t [] (Or.inl i))
        (verdictIndexedOk cm (treeRowsAcc t []) (revRows all) t k))
    (fun all k => False.elim (notOkNeOk (exhaustedVerdict cm all) k))
    s h

-- The verdict front door: the same claim and cost as `checkSafety`, and a
-- rejection prints the verdict.
--   theorem safe : ScalarModel.safetyClaim M := proveSafe M 64 rfl
theorem proveSafe (model : ScalarModel) (fuel : Nat)
    (h : safetyVerdict model fuel = CheckVerdict.ok) : ScalarModel.safetyClaim model :=
  Exists.elim (optionRecOk (compileModel model)
      (fun cm0 => forceCM cm0 (fun cm => verdictCompiled cm (searchCompiled cm fuel)))
      (Eq.trans (Eq.symm (verdictIdEq (@Option.rec CModel (fun _ => CheckVerdict)
          CheckVerdict.unsupported
          (fun cm0 => forceCM cm0 (fun cm => verdictCompiled cm (searchCompiled cm fuel)))
          (compileModel model)))) h))
    (fun cm facts => verdictCompiledSound model cm facts.1 (searchCompiled cm fuel)
      (Eq.trans (Eq.symm (forceCMEq cm (fun cm' => verdictCompiled cm' (searchCompiled cm' fuel))))
        facts.2))


-- 7. Replaying a run (untrusted; for diagnostics).  A caller that explains an
-- `invariantFails` verdict with a run (the compiler, under its error) hands
-- the action positions back here and compares every row, so a printed step is
-- one THIS checker takes: the guard is true in the row it is taken from, and
-- the next row is the checker's own successor.

def countB {α : Type} (p : α → Bool) (xs : List α) : Nat :=
  @List.rec α (fun _ => Nat) 0
    (fun x _ n => @Bool.rec (fun _ => Nat) n (Nat.succ n) (p x)) xs

-- every variable name is declared once.  A model that repeats one has NO
-- initial state when the two initial values differ, so it has no run, and
-- nothing here may confirm a run of it.
def distinctVars (vars : List StateVar) : Bool :=
  @List.rec StateVar (fun _ => Bool) true
    (fun v _ prev => @Bool.rec (fun _ => Bool) false prev
      (Nat.beq (countB (fun (w : StateVar) => decide (w.name = v.name)) vars) 1))
    vars

-- `compileModel`, for the confirmations of sections 7 and 8
def compileDistinct (model : ScalarModel) : Option CModel :=
  @Bool.rec (fun _ => Option CModel) none (compileModel model) (distinctVars model.variables)

def nthAction (acts : List CAction) : Nat → Option CAction :=
  @List.rec CAction (fun _ => Nat → Option CAction) (fun _ => none)
    (fun a _ ih i => @Nat.rec (fun _ => Option CAction) (some a) (fun j _ => ih j) i) acts

-- the rows after each step of `steps` (action positions) from `row`; `none`
-- when a position names no action or its guard is false in the row it is
-- taken from
def replayCompiled (cm : CModel) (steps : List Nat) : List Nat → Option (List (List Nat)) :=
  @List.rec Nat (fun _ => List Nat → Option (List (List Nat))) (fun _ => some [])
    (fun i _ ih row =>
      @Option.rec CAction (fun _ => Option (List (List Nat))) none
        (fun ca => @Bool.rec (fun _ => Option (List (List Nat))) none
          (forceRow (succRow row ca.upd row) (fun s =>
            @Option.rec (List (List Nat)) (fun _ => Option (List (List Nat))) none
              (fun rest => some (s :: rest)) (ih s)))
          (evalB row ca.guard))
        (nthAction cm.actions i))
    steps

-- the initial row followed by the rows of `replayCompiled`
def replayRun (model : ScalarModel) (steps : List Nat) : Option (List (List Nat)) :=
  @Option.rec CModel (fun _ => Option (List (List Nat))) none
    (fun cm => forceRow cm.init (fun i =>
      @Option.rec (List (List Nat)) (fun _ => Option (List (List Nat))) none
        (fun rest => some (i :: rest)) (replayCompiled cm steps i)))
    (compileDistinct model)

-- what the invariants say at `row`: `some (invariantFails row i)` for the first
-- invariant that is false there, `none` when every invariant holds (or the
-- model is outside the grammar).  With `replayRun` this lets a caller confirm
-- a violation found by ITS OWN search, however large the model: the kernel
-- replays the run and evaluates the invariant at its last row, and never
-- searches.
def rowVerdict (model : ScalarModel) (row : List Nat) : Option CheckVerdict :=
  @Option.rec CModel (fun _ => Option CheckVerdict) none
    (fun cm => forceRow row (fun r => invVerdict cm r))
    (compileDistinct model)


-- ===== 8. Progress: confirming a fair run that leaves the goal for good =====
--
-- A PROGRESS CLAIM says the goal holds again and again on every fair run of
-- the model (`[]<> goal`), under weak fairness of the actions `weak` and
-- strong fairness of `strong`.  Fairness is about steps that CHANGE the state
-- (`Trust.Temporal.NonStuttering`): a run may stutter forever, and an action
-- is "enabled" when its guard holds and its step moves the row.
--
-- Section 9 PROVES a claim.  Here `lassoVerdict` only CONFIRMS a counterexample
-- a caller found by its own search: a stem from the initial row, then a loop
-- the run repeats forever.  It answers `some true` exactly when, by this
-- checker's own guards and successors,
--   * the stem and the loop are steps of the machine, each loop step moves
--     the row, and the loop returns to the row it starts at;
--   * the goal is false at every row of the loop;
--   * every weakly fair action is taken on the loop or cannot move some row
--     of it (so it is not continuously enabled);
--   * every strongly fair action is taken on the loop or cannot move any row
--     of it (so it is not enabled infinitely often).
-- An EMPTY loop is the run that stutters at the stem's last row forever.
-- `none`: the claim is outside the grammar, the model repeats a variable name,
-- a fair name is carried by no action or by more than one, or a step is not
-- one the machine takes.

structure ScalarProgress where
  model : ScalarModel
  goal : ScalarExpr
  weak : List String
  strong : List String

def firstActionSlot (acts : List Action) (name : String) : Option Nat :=
  @List.rec Action (fun _ => Option Nat) none
    (fun a _ ih =>
      @Bool.rec (fun _ => Option Nat)
        (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i)) ih)
        (some 0)
        (decide (a.name = name)))
    acts

-- the position of THE action named `name`: `none` when no action or more than
-- one carries the name (fairness of a name two actions share is ambiguous)
def actionSlot (acts : List Action) (name : String) : Option Nat :=
  @Bool.rec (fun _ => Option Nat) none (firstActionSlot acts name)
    (Nat.beq (countB (fun (a : Action) => decide (a.name = name)) acts) 1)

def notB (b : Bool) : Bool := @Bool.rec (fun _ => Bool) true false b
def andB (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) false b a
def orB (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) b true a

def anyB {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  @List.rec α (fun _ => Bool) false (fun x _ prev => orB (p x) prev) xs

def natMem (n : Nat) (xs : List Nat) : Bool := anyB (fun m => Nat.beq n m) xs

-- whether the action can change `row`: its guard holds and its step moves it
def movesRow (row : List Nat) (ca : CAction) : Bool :=
  andB (evalB row ca.guard) (notB (rowEq (succRow row ca.upd row) row))

def movesAt (cm : CModel) (slot : Nat) (row : List Nat) : Bool :=
  @Option.rec CAction (fun _ => Bool) false (fun ca => movesRow row ca) (nthAction cm.actions slot)

-- `replayCompiled`, with every step required to move the row
def replayMoving (cm : CModel) (steps : List Nat) : List Nat → Option (List (List Nat)) :=
  @List.rec Nat (fun _ => List Nat → Option (List (List Nat))) (fun _ => some [])
    (fun i _ ih row =>
      @Option.rec CAction (fun _ => Option (List (List Nat))) none
        (fun ca => @Bool.rec (fun _ => Option (List (List Nat))) none
          (forceRow (succRow row ca.upd row) (fun s =>
            @Option.rec (List (List Nat)) (fun _ => Option (List (List Nat))) none
              (fun rest => some (s :: rest)) (ih s)))
          (movesRow row ca))
        (nthAction cm.actions i))
    steps

def lastRow (first : List Nat) (rows : List (List Nat)) : List Nat :=
  (@List.rec (List Nat) (fun _ => List Nat → List Nat) (fun acc => acc)
    (fun r _ ih _ => ih r) rows) first

def lassoCompiled (cm : CModel) (goal : CExpr) (weak strong stem cycle : List Nat) : Option Bool :=
  @Option.rec (List (List Nat)) (fun _ => Option Bool) none
    (fun stemRows => forceRow (lastRow cm.init stemRows) (fun entry =>
      @Option.rec (List (List Nat)) (fun _ => Option Bool) none
        (fun loopRows =>
          some (andB (rowEq (lastRow entry loopRows) entry)
            (andB (allB (fun row => notB (evalB row goal)) (entry :: loopRows))
              (andB
                (allB (fun slot => orB (natMem slot cycle)
                    (anyB (fun row => notB (movesAt cm slot row)) (entry :: loopRows))) weak)
                (allB (fun slot => orB (natMem slot cycle)
                    (allB (fun row => notB (movesAt cm slot row)) (entry :: loopRows))) strong)))))
        (replayMoving cm cycle entry)))
    (replayCompiled cm stem cm.init)

def lassoVerdict (claim : ScalarProgress) (stem cycle : List Nat) : Option Bool :=
  @Option.rec CModel (fun _ => Option Bool) none
    (fun cm => @Option.rec CExpr (fun _ => Option Bool) none
      (fun goal => @Option.rec (List Nat) (fun _ => Option Bool) none
        (fun weak => @Option.rec (List Nat) (fun _ => Option Bool) none
          (fun strong => lassoCompiled cm goal weak strong stem cycle)
          (mapOpt (actionSlot claim.model.actions) claim.strong))
        (mapOpt (actionSlot claim.model.actions) claim.weak))
      (compileS claim.model.variables claim.model.constants claim.goal Srt.bool))
    (compileDistinct claim.model)


-- ===== 9. Progress: proving a claim from a certificate of levels =====
--
-- Section 8 confirms that a progress claim is FALSE.  This section proves one
-- TRUE.  `ScalarProgress.claim p` is the temporal statement itself: on every
-- run of the model's state machine that is weakly fair to each action named
-- in `p.weak` and strongly fair to each action named in `p.strong`, the goal
-- holds again and again.  An island proves it with
--
--   theorem live : ScalarProgress.claim P := progressOfCheck P cert rfl
--
-- and the kernel runs `progressCheck P cert` while it compiles the island.
-- Name the claim (`P`), never `_`: clean 0.9.0 elaborates `rfl` against
-- `progressCheck ?p cert = true` before it reads the theorem's type.
--
-- THE CERTIFICATE lists every reachable row with its LEVELS, outermost
-- first: (rank, helper) pairs, the helper an action position.  A claim that
-- weak fairness carries needs one level per non-goal row; each strongly fair
-- helper a row waits on adds one.  The caller finds the certificate by its
-- own search and it has no authority.  `progressCheck p cert` answers true
-- exactly when, by this checker's own compilation, guards and successors
-- (`compileDistinct`, `evalB`, `succRow`, `rowEq`, `actionSlot`, `movesRow`):
--   * the model compiles with distinct variable names, the goal compiles, and
--     every name in `p.weak` and in `p.strong` is carried by exactly one
--     action;
--   * the initial row is a certificate row;
--   * every action whose guard holds at a certificate row takes it to a
--     certificate row (so every reachable row is in the certificate);
--   * at a certificate row where the goal is FALSE, with levels L:
--       - L is not empty; every level but the last names a strongly fair
--         action that cannot move the row (`innerOk`), and the last names a
--         fair action that moves it (`lastOk`);
--       - the last helper's step reaches a goal row, a row whose levels lie
--         below L (where they first differ, its rank is lower: `lexDownB`),
--         or a row that agrees with L down to a level above the last whose
--         helper can move it (`wakesB`);
--       - every step does one of those or keeps every level of L (`prefixB`).
-- The levels of a successor are those of the FIRST entry whose row equals
-- it.  Every entry is checked, one that an earlier entry shadows too.
--
-- THE RULE AND THE CHECK.  `progressRule` is the rule above read literally:
-- every lookup is a linear scan for the first entry (`certFind`).  That is
-- quadratic in the rows, so nothing runs it.  `progressCheck` makes the same
-- passes over an index of the certificate (`PIndex`, a trie on the rows'
-- hashes), so its work grows as n log n.  `progressCheckRule` (9g) proves
-- `progressCheck p cert = progressRule p cert` for every claim and every
-- certificate: "exactly when" is a theorem, duplicate rows and colliding
-- hashes included.  Soundness is proved once, about the rule
-- (`progressOfRule`, 9f).
--
-- WHY THAT PROVES THE CLAIM (`levelsProgress`, 9a).  Every state of a run
-- denotes a certificate row.  Take a run that never reaches the goal from
-- some point on.  No step raises its first level, so the level settles at
-- some (k, h).  If h can move the state again and again, fairness takes one
-- of its steps (a row whose last level is h has h enabled; a row that keeps
-- h above its last level names h strongly fair), and that step leaves
-- (k, h).  So eventually h never can, every row then has a second level,
-- and the second level settles the same way, and so on.  Levels are finitely
-- long, so some helper's step is taken: the run reaches the goal.
--
-- LIMITS.  Fairness comes from the claim: a certificate cannot add any.
-- `false` proves nothing; `lassoVerdict` (section 8) confirms a
-- counterexample.
-- THE CAP is clean's, not the rule's: it stops the evaluation behind one
-- `rfl` (the header's READING A REJECTED ISLAND).  Past it a VALID
-- certificate fails too, and only the message tells the two failures apart:
--   * rejected: "expected ...progressCheck P cert = true, got const mismatch:
--     Bool.false vs Bool.true".  The check ran and answered false;
--   * over the cap: "... got rigid head/arity mismatch: Bool.rec vs
--     ...progressCheck", with 10.0M ticks reported.  A stuck term: nothing
--     was decided.
-- Measured on clean 0.9.0 (`peak_decl_ticks` and wall time of the claim
-- alone, the certificate in literals of 25 rows, one level per non-goal row):
--   * one variable, one action: 1001 rows 0.83M (6 s), 4001 rows 3.68M
--     (25 s), 8001 rows 7.61M (52 s); 10501 rows stop at the cap;
--   * the harness protocol's shape, 9 variables and 11 actions: 973 rows
--     1.97M (18 s), 1933 rows 3.99M (38 s), 3853 rows 8.09M (78 s); 4813
--     rows stop at the cap.
--   Levels cost about 7% more than the (rank, helper) rows of the rule this
--   one replaced, which passed 10501 rows (9.66M) and 4813 (9.62M).  The
--   rest of this paragraph was measured on those rows.
--   The order of the entries does not matter (1001 rows in ascending or
--   descending hash order: 0.77M, as in any other order).
--   About 60% of a passing claim's ticks are the elaborator's evaluation and
--   40% the kernel's re-check (`set_option maxHeartbeats 1` stops the
--   re-check at once: 5.80M of 9.66M at 10501 rows, 5.77M of 9.62M at 4813).
--   `set_option maxHeartbeats 2000000` still passes both of those, and
--   `--max-cache-entries 0` passes 11001 rows (9.19M) and 5053 (9.77M).
--   The linear-scan check this index replaced stopped near 975 and 1050 rows
--   (971 rows 10.0M, 84 s; 973 rows 8.92M, 144 s).  On the harness shape the
--   safety door now stops first: `proveSafe` takes 5.85M ticks at 1933
--   states and stops at the cap at 3853.
--   Rows that share a HASH share a tip of the index, and a tip is scanned as
--   the rule scans, so a model whose rows collide by construction pays the
--   square again: 801 rows of one hash cost 7.00M (401 rows 1.89M).
--   `rowHash` is linear before its last step: [0] and [4294967291] collide,
--   and so do [1000003, 0] and [0, 1].
--
-- WRITING A LARGE CERTIFICATE.  clean 0.9.0 refuses a list literal of 2001
-- entries ("maximum macro expansion depth exceeded") and a `++` chain nested
-- deeper than 128, and it elaborates a long literal in more than linear time
-- (1933 rows of 9 numbers: 13 s in literals of 25 rows, 40 s of 100, 167 s of
-- 400).  Emit short literals, each its own definition, and chain them with
-- definitions: `tailJ := partJ ++ tail(J+1)`.

-- the relation of the action(s) named `name`
def NamedAction (model : Model) (name : String) (s t : State) : Prop :=
  ∃ a : Action, Member a model.actions ∧ a.name = name ∧ ActionHolds model a s t

-- the goal holds in state `s`
def GoalHolds (model : Model) (goal : ScalarExpr) (s : State) : Prop :=
  Evaluates model [] s goal (Value.bool true)

-- THE CLAIM: on every run that is weakly fair to every action named in `weak`
-- and strongly fair to every action named in `strong`, the goal holds again
-- and again
def ScalarProgress.claim (p : ScalarProgress) : Prop :=
  ∀ b : _root_.Trust.Temporal.Behavior State,
    _root_.Trust.Temporal.Runs (StateMachine p.model.asModel) b →
    (∀ name : String, Member name p.weak →
      _root_.Trust.Temporal.WeakFair (NamedAction p.model.asModel name) b) →
    (∀ name : String, Member name p.strong →
      _root_.Trust.Temporal.StrongFair (NamedAction p.model.asModel name) b) →
    _root_.Trust.Temporal.Always (_root_.Trust.Temporal.Eventually
      (_root_.Trust.Temporal.Lift (GoalHolds p.model.asModel p.goal))) b

-- one level of a certificate row: a rank and a helper (an action position)
structure ProgressLevel where
  rank : Nat
  helper : Nat

-- one row of a certificate: a reachable row and its levels, outermost first
structure ProgressRow where
  row : List Nat
  levels : List ProgressLevel

-- THE RULE's lookup: the FIRST certificate entry whose row equals `t` (a
-- linear scan; the check runs `pfindK`, which answers the same, 9g)
def certFind (cert : List ProgressRow) (t : List Nat) : Option ProgressRow :=
  @List.rec ProgressRow (fun _ => Option ProgressRow) none
    (fun e _ ih => @Bool.rec (fun _ => Option ProgressRow) ih (some e) (rowEq e.row t)) cert

def lvEq (a b : ProgressLevel) : Bool := andB (Nat.beq a.rank b.rank) (Nat.beq a.helper b.helper)

-- `E` lies strictly below `L`: at the first level where they differ, `E`'s rank
-- is lower (the cheap test: a weak certificate has one level per row)
def lexDownB (E : List ProgressLevel) : List ProgressLevel → Bool :=
  @List.rec ProgressLevel (fun _ => List ProgressLevel → Bool) (fun _ => false)
    (fun e _ ih L => @List.rec ProgressLevel (fun _ => Bool) false
      (fun l ls _ => orB (Nat.blt e.rank l.rank) (andB (lvEq e l) (ih ls))) L) E

-- `L` is a prefix of `E`: the step keeps every level of `L`
def prefixB (L : List ProgressLevel) : List ProgressLevel → Bool :=
  @List.rec ProgressLevel (fun _ => List ProgressLevel → Bool) (fun _ => true)
    (fun l _ ih E => @List.rec ProgressLevel (fun _ => Bool) false
      (fun e es _ => andB (lvEq e l) (ih es)) E) L

-- `E` agrees with `L` down to a level of `L` whose helper can move `t`: the
-- step wakes a helper that was asleep
def wakesB (cm : CModel) (t : List Nat) (E : List ProgressLevel) : List ProgressLevel → Bool :=
  @List.rec ProgressLevel (fun _ => List ProgressLevel → Bool) (fun _ => false)
    (fun e _ ih L => @List.rec ProgressLevel (fun _ => Bool) false
      (fun l ls _ => andB (lvEq e l) (orB (movesAt cm l.helper t) (ih ls))) L) E

def dropLastL (L : List ProgressLevel) : List ProgressLevel :=
  @List.rec ProgressLevel (fun _ => List ProgressLevel) []
    (fun l ls ih => @List.rec ProgressLevel (fun _ => List ProgressLevel) [] (fun _ _ _ => l :: ih) ls) L

-- The successor of `ca` from `row` has an entry, and `ok` accepts it.  `find`
-- is the lookup: `certFind cert` states the rule, `pfindK` runs it.
def succIn (find : List Nat → Option ProgressRow) (ok : List Nat → ProgressRow → Bool)
    (row : List Nat) (ca : CAction) : Bool :=
  forceRow (succRow row ca.upd row) (fun t =>
    @Option.rec ProgressRow (fun _ => Bool) false (fun e => ok t e) (find t))

-- ... when the guard of `ca` holds at `row`
def stepOk (find : List Nat → Option ProgressRow) (ok : List Nat → ProgressRow → Bool)
    (row : List Nat) (ca : CAction) : Bool :=
  @Bool.rec (fun _ => Bool) true (succIn find ok row ca) (evalB row ca.guard)

-- where the last helper's step from a row with levels `L` may go: below `L`,
-- to the goal, or to a row that wakes a helper of a level above the last
def helperStepB (cm : CModel) (g : CExpr) (L : List ProgressLevel) (t : List Nat)
    (e : ProgressRow) : Bool :=
  orB (lexDownB e.levels L) (orB (evalB t g) (wakesB cm t e.levels (dropLastL L)))

-- where any step may go: as the helper's, or keeping every level of `L`
def anyStepB (cm : CModel) (g : CExpr) (L : List ProgressLevel) (t : List Nat)
    (e : ProgressRow) : Bool :=
  orB (lexDownB e.levels L)
    (orB (prefixB L e.levels) (orB (evalB t g) (wakesB cm t e.levels L)))

-- a level above the last: its helper is strongly fair and cannot move the row
def innerOk (cm : CModel) (strong : List Nat) (row : List Nat) (l : ProgressLevel) : Bool :=
  andB (natMem l.helper strong) (notB (movesAt cm l.helper row))

-- the last level: its helper is fair, moves the row, and its step goes where
-- `helperStepB` allows
def lastOk (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (row : List Nat) (L : List ProgressLevel)
    (l : ProgressLevel) : Bool :=
  andB (orB (natMem l.helper weak) (natMem l.helper strong))
    (@Option.rec CAction (fun _ => Bool) false
      (fun ca => andB (movesRow row ca) (succIn find (helperStepB cm g L) row ca))
      (nthAction cm.actions l.helper))

-- the levels after `prev`, in order: inner levels, then the last
def levelsWalk (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (row : List Nat) (L : List ProgressLevel)
    (ls : List ProgressLevel) : ProgressLevel → Bool :=
  @List.rec ProgressLevel (fun _ => ProgressLevel → Bool)
    (fun prev => lastOk cm g weak strong find row L prev)
    (fun x _ ih prev => andB (innerOk cm strong row prev) (ih x)) ls

-- a row's levels: at least one, every one in order
def levelsOk (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (row : List Nat) (L : List ProgressLevel) : Bool :=
  @List.rec ProgressLevel (fun _ => Bool) false
    (fun l ls _ => levelsWalk cm g weak strong find row L ls l) L

-- one certificate entry: closure only at a goal row; at any other row its
-- levels, and no step that leaves them except downwards or by waking a helper
def entryOk (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (r : ProgressRow) : Bool :=
  @Bool.rec (fun _ => Bool)
    (andB (levelsOk cm g weak strong find r.row r.levels)
      (allB (stepOk find (anyStepB cm g r.levels) r.row) cm.actions))
    (allB (stepOk find (fun (_ : List Nat) (_ : ProgressRow) => true) r.row) cm.actions)
    (evalB r.row g)

-- the initial row is a certificate row, and every entry is in order
def progressRows (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (cert : List ProgressRow) : Bool :=
  andB (@Option.rec ProgressRow (fun _ => Bool) false (fun _ => true) (find cm.init))
    (allB (entryOk cm g weak strong find) cert)

-- names are resolved once, and the compiled model, goal and fair positions
-- are values before the loop reads them (the cost discipline of the header)
def progressWith (p : ScalarProgress) (body : CModel → CExpr → List Nat → List Nat → Bool) : Bool :=
  @Option.rec CModel (fun _ => Bool) false
    (fun cm0 => @Option.rec CExpr (fun _ => Bool) false
      (fun g0 => @Option.rec (List Nat) (fun _ => Bool) false
        (fun weak0 => @Option.rec (List Nat) (fun _ => Bool) false
          (fun strong0 => forceCM cm0 (fun cm => forceCExpr g0 (fun g => forceRow weak0 (fun weak =>
            forceRow strong0 (fun strong => body cm g weak strong)))))
          (mapOpt (actionSlot p.model.actions) p.strong))
        (mapOpt (actionSlot p.model.actions) p.weak))
      (compileS p.model.variables p.model.constants p.goal Srt.bool))
    (compileDistinct p.model)

-- THE RULE as the header states it, every lookup a linear scan.  Quadratic,
-- so nothing runs it: `progressCheck` answers the same (`progressCheckRule`).
def progressRule (p : ScalarProgress) (cert : List ProgressRow) : Bool :=
  progressWith p (fun cm g weak strong => progressRows cm g weak strong (certFind cert) cert)

-- The check's index: a trie over the certificate entries.  A fork goes four
-- ways by the next two bits of the row's hash; a tip holds the entries that
-- took one path, in certificate order.  The SHAPE depends on the hashes
-- alone, not on the order of the entries (a search tree filled in hash order
-- would be a list: `reachRows` returns its rows so).  The hash only steers;
-- the only answer is an entry of the tip whose row `rowEq` matched.
inductive PIndex where
  | tip : List ProgressRow → PIndex
  | fork : PIndex → PIndex → PIndex → PIndex → PIndex

-- one of four, by `m` = 0, 1, 2, more (proofs state facts about `pick4`; the
-- walks spell it out inline)
def pick4 {β : Type} (c0 c1 c2 c3 : β) (m : Nat) : β :=
  @Nat.rec (fun _ => β) c0
    (fun m1 _ => @Nat.rec (fun _ => β) c1
      (fun m2 _ => @Nat.rec (fun _ => β) c2 (fun _ _ => c3) m2) m1)
    m

-- the first entry for row `r` on the path of hash `h`
def pfindH (r : List Nat) (t : PIndex) : Nat → Option ProgressRow :=
  @PIndex.rec (fun _ => Nat → Option ProgressRow)
    (fun bucket _ => certFind bucket r)
    (fun _ _ _ _ i0 i1 i2 i3 h =>
      forceNat (Nat.div h 4) (fun q =>
        @Nat.rec (fun _ => Option ProgressRow) (i0 q)
          (fun m1 _ => @Nat.rec (fun _ => Option ProgressRow) (i1 q)
            (fun m2 _ => @Nat.rec (fun _ => Option ProgressRow) (i2 q) (fun _ _ => i3 q) m2) m1)
          (Nat.mod h 4)))
    t

-- the check's lookup (every row it asks about is a value already)
def pfindK (t : PIndex) (r : List Nat) : Option ProgressRow :=
  forceNat (rowHash r) (fun h => pfindH r t h)

-- Insert entry `e` on the path of hash `h`, at the FRONT of its tip.  The
-- index is built from the last entry to the first, so every tip keeps the
-- certificate's order and the first entry of a row is the one found.
def pinsertH (e : ProgressRow) (t : PIndex) : Nat → PIndex :=
  @PIndex.rec (fun _ => Nat → PIndex)
    (fun bucket _ => PIndex.tip (e :: bucket))
    (fun a b c d i0 i1 i2 i3 h =>
      pick4 (PIndex.fork (i0 (Nat.div h 4)) b c d) (PIndex.fork a (i1 (Nat.div h 4)) c d)
        (PIndex.fork a b (i2 (Nat.div h 4)) d) (PIndex.fork a b c (i3 (Nat.div h 4))) (Nat.mod h 4))
    t

-- `pinsertH`, rebuilding the walked path as a value
def pinsertK {α : Type} (e : ProgressRow) (t : PIndex) : Nat → (PIndex → α) → α :=
  @PIndex.rec (fun _ => Nat → (PIndex → α) → α)
    (fun bucket _ k => k (PIndex.tip (e :: bucket)))
    (fun a b c d i0 i1 i2 i3 h k =>
      forceNat (Nat.div h 4) (fun q =>
        @Nat.rec (fun _ => α) (i0 q (fun x => k (PIndex.fork x b c d)))
          (fun m1 _ => @Nat.rec (fun _ => α) (i1 q (fun x => k (PIndex.fork a x c d)))
            (fun m2 _ => @Nat.rec (fun _ => α) (i2 q (fun x => k (PIndex.fork a b x d)))
              (fun _ _ => i3 q (fun x => k (PIndex.fork a b c x))) m2) m1)
          (Nat.mod h 4)))
    t

-- the empty index of depth `d`: 4^d tips, all one shared term
def pempty (d : Nat) : PIndex :=
  @Nat.rec (fun _ => PIndex) (PIndex.tip []) (fun _ t => PIndex.fork t t t t) d

def pemptyK {α : Type} (d : Nat) : (PIndex → α) → α :=
  @Nat.rec (fun _ => (PIndex → α) → α) (fun k => k (PIndex.tip []))
    (fun _ ih k => ih (fun t => k (PIndex.fork t t t t))) d

def pbuild (cert : List ProgressRow) (t0 : PIndex) : PIndex :=
  @List.rec ProgressRow (fun _ => PIndex) t0
    (fun e _ ih => pinsertH e ih (rowHash e.row)) cert

-- `pbuild`, as a value
def pbuildK {α : Type} (cert : List ProgressRow) (t0 : PIndex) : (PIndex → α) → α :=
  @List.rec ProgressRow (fun _ => (PIndex → α) → α) (fun k => k t0)
    (fun e _ ih k => ih (fun t => forceNat (rowHash e.row) (fun h => pinsertK e t h k))) cert

-- the certificate's spine as a value (it is read three times: length, index,
-- entries); the entries are kept as given
def forceEntries {α : Type} (cert : List ProgressRow) : (List ProgressRow → α) → α :=
  @List.rec ProgressRow (fun _ => (List ProgressRow → α) → α) (fun k => k [])
    (fun e _ ih k => ih (fun es => k (e :: es))) cert

-- the number of entries (after `acc`), as a value
def lengthK {α : Type} (cert : List ProgressRow) : Nat → (Nat → α) → α :=
  @List.rec ProgressRow (fun _ => Nat → (Nat → α) → α) (fun n k => k n)
    (fun _ _ ih n k => forceNat (Nat.succ n) (fun n' => ih n' k)) cert

-- The depth for `n` entries: the least d with 2 * 4^d >= n, so a tip holds
-- between one half and two entries on average.  Steering only: any depth
-- gives the same answers.
def pdepth (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat) (fun _ d => d)
    (fun _ ih cap d =>
      @Bool.rec (fun _ => Nat) d (ih (Nat.mul cap 4) (Nat.succ d)) (Nat.blt cap n))
    32 2 0

def progressIndexed (cm : CModel) (g : CExpr) (weak strong : List Nat) (cert : List ProgressRow) : Bool :=
  forceEntries cert (fun es => lengthK es 0 (fun n => forceNat (pdepth n) (fun d =>
    pemptyK d (fun t0 => pbuildK es t0 (fun t => progressRows cm g weak strong (pfindK t) es)))))

-- THE CHECK (a recursor over its computation, as every door of this module)
def progressCheck (p : ScalarProgress) (cert : List ProgressRow) : Bool :=
  @Bool.rec (fun _ => Bool) false true
    (progressWith p (fun cm g weak strong => progressIndexed cm g weak strong cert))

-- ===== 9a. the temporal layer: nested levels under weak and strong fairness =====

theorem orBCases (a b : Bool) (h : orB a b = true) : a = true ∨ b = true :=
  @Bool.rec (fun a => orB a b = true → a = true ∨ b = true)
    (fun k => Or.inr k) (fun _ => Or.inl rfl) a h

theorem bltLt (a b : Nat) (h : Nat.blt a b = true) : Nat.lt a b :=
  Nat.le_of_ble_eq_true (Nat.succ a) b h

theorem natStrong (P : Nat → Prop)
    (step : ∀ k : Nat, (∀ j : Nat, Nat.lt j k → P j) → P k) : ∀ k : Nat, P k :=
  fun k => step k
    (@Nat.rec (fun k => ∀ j : Nat, Nat.lt j k → P j)
      (fun j h => False.elim (Nat.not_succ_le_zero j h))
      (fun k ih j h =>
        Or.elim (Nat.lt_or_eq_of_le j k (Nat.le_of_succ_le_succ j k h))
          (fun lt => ih j lt)
          (fun e => Eq.mpr (congrArg P e) (step k ih)))
      k)

theorem runInvariant {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ) (I : σ → Prop)
    (b : _root_.Trust.Temporal.Behavior σ) (runs : _root_.Trust.Temporal.Runs M b)
    (init : ∀ s : σ, M.init s → I s)
    (step : ∀ s t : σ, I s → M.next s t → I t) : ∀ n : Nat, I (b n) :=
  fun n => @Nat.rec (fun n => I (b n)) (init (b 0) runs.1)
    (fun n prev => Or.elim (runs.2 n)
      (fun st => step (b n) (b (Nat.succ n)) prev st)
      (fun stutter => Eq.mpr (congrArg I stutter) prev))
    n

def catL (P L : List ProgressLevel) : List ProgressLevel :=
  @List.rec ProgressLevel (fun _ => List ProgressLevel) L (fun x _ ih => x :: ih) P

def lenL (L : List ProgressLevel) : Nat :=
  @List.rec ProgressLevel (fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

-- `E` agrees with `L` down to a level of `L` whose helper `en` holds
def Wakes (en : Nat → Prop) (E : List ProgressLevel) : List ProgressLevel → Prop :=
  @List.rec ProgressLevel (fun _ => List ProgressLevel → Prop) (fun _ => False)
    (fun e _ ih L => @List.rec ProgressLevel (fun _ => Prop) False
      (fun l ls _ => lvEq e l = true ∧ (en l.helper ∨ ih ls)) L) E

-- every level but the last is `inner`, the last is `last`; an empty list is not a shape
def LevelsShape (inner last : ProgressLevel → Prop) (L : List ProgressLevel) : Prop :=
  @List.rec ProgressLevel (fun _ => Prop) False
    (fun l ls ih => @List.rec ProgressLevel (fun _ => Prop) (last l) (fun _ _ _ => inner l ∧ ih) ls) L

def LastIs (l0 : ProgressLevel) (L : List ProgressLevel) : Prop :=
  @List.rec ProgressLevel (fun _ => Prop) False
    (fun l ls ih => @List.rec ProgressLevel (fun _ => Prop) (l = l0) (fun _ _ _ => ih) ls) L

def AllL (q : ProgressLevel → Prop) (L : List ProgressLevel) : Prop :=
  @List.rec ProgressLevel (fun _ => Prop) True (fun x _ ih => q x ∧ ih) L

def AnyL (q : ProgressLevel → Prop) (L : List ProgressLevel) : Prop :=
  @List.rec ProgressLevel (fun _ => Prop) False (fun x _ ih => q x ∨ ih) L

-- ----- list facts -----

theorem lvEta (e : ProgressLevel) : ProgressLevel.mk e.rank e.helper = e :=
  @ProgressLevel.rec (fun e => ProgressLevel.mk e.rank e.helper = e) (fun r h => rfl) e

theorem lvEqSound (e l : ProgressLevel) (h : lvEq e l = true) : e = l :=
  (fun both =>
    Eq.trans (Eq.symm (lvEta e))
      (Eq.trans (congrArg (fun r => ProgressLevel.mk r e.helper) (natBeqSound e.rank l.rank both.1))
        (Eq.trans (congrArg (fun hh => ProgressLevel.mk l.rank hh) (natBeqSound e.helper l.helper both.2))
          (lvEta l))))
  (boolRecAnd (Nat.beq e.rank l.rank) (Nat.beq e.helper l.helper) h)

theorem natBeqRefl (n : Nat) : Nat.beq n n = true :=
  @Nat.rec (fun n => Nat.beq n n = true) rfl (fun _ ih => ih) n

theorem lvEqRefl (l : ProgressLevel) : lvEq l l = true :=
  Eq.trans (congrArg (fun z => andB z (Nat.beq l.helper l.helper)) (natBeqRefl l.rank))
    (natBeqRefl l.helper)

theorem bltSelf (n : Nat) (h : Nat.blt n n = true) : False := Nat.lt_irrefl n (bltLt n n h)

theorem catNil (P : List ProgressLevel) : catL P [] = P :=
  @List.rec ProgressLevel (fun P => catL P [] = P) rfl
    (fun x P' ih => congrArg (fun z => x :: z) ih) P

theorem catAssoc (l : ProgressLevel) (rest P : List ProgressLevel) :
    catL P (l :: rest) = catL (catL P [l]) rest :=
  @List.rec ProgressLevel (fun P => catL P (l :: rest) = catL (catL P [l]) rest) rfl
    (fun x P' ih => congrArg (fun z => x :: z) ih) P

theorem lenCat (X P : List ProgressLevel) : lenL (catL P X) = lenL P + lenL X :=
  @List.rec ProgressLevel (fun P => lenL (catL P X) = lenL P + lenL X)
    (Eq.symm (Nat.zero_add (lenL X)))
    (fun x P' ih => Eq.trans (congrArg Nat.succ ih) (Eq.symm (Nat.succ_add (lenL P') (lenL X)))) P

theorem lexDownCat (E L P : List ProgressLevel) :
    lexDownB (catL P E) (catL P L) = true → lexDownB E L = true :=
  @List.rec ProgressLevel
    (fun P => lexDownB (catL P E) (catL P L) = true → lexDownB E L = true)
    (fun h => h)
    (fun x P' ih h =>
      Or.elim (orBCases (Nat.blt x.rank x.rank) (andB (lvEq x x) (lexDownB (catL P' E) (catL P' L))) h)
        (fun lt => False.elim (bltSelf x.rank lt))
        (fun rest => ih (boolRecAnd (lvEq x x) (lexDownB (catL P' E) (catL P' L)) rest).2))
    P

theorem prefixCat (L E P : List ProgressLevel) :
    prefixB (catL P L) (catL P E) = true → prefixB L E = true :=
  @List.rec ProgressLevel
    (fun P => prefixB (catL P L) (catL P E) = true → prefixB L E = true)
    (fun h => h)
    (fun x P' ih h => ih (boolRecAnd (lvEq x x) (prefixB (catL P' L) (catL P' E)) h).2)
    P

theorem wakesCat (en : Nat → Prop) (E L P : List ProgressLevel) :
    Wakes en (catL P E) (catL P L) → AnyL (fun x => en x.helper) P ∨ Wakes en E L :=
  @List.rec ProgressLevel
    (fun P => Wakes en (catL P E) (catL P L) → AnyL (fun x => en x.helper) P ∨ Wakes en E L)
    (fun h => Or.inr h)
    (fun x P' ih h =>
      Or.elim h.2
        (fun here => Or.inl (Or.inl here))
        (fun deeper => Or.elim (ih deeper)
          (fun any => Or.inl (Or.inr any))
          (fun w => Or.inr w)))
    P

theorem anyAllFalse (q : ProgressLevel → Prop) (P : List ProgressLevel) :
    AnyL q P → AllL (fun x => ¬ q x) P → False :=
  @List.rec ProgressLevel (fun P => AnyL q P → AllL (fun x => ¬ q x) P → False)
    (fun any _ => any)
    (fun x P' ih any all => Or.elim any (fun here => all.1 here) (fun there => ih there all.2))
    P

theorem allCatSingle (q : ProgressLevel → Prop) (l : ProgressLevel) (P : List ProgressLevel)
    (hP : AllL q P) (hl : q l) : AllL q (catL P [l]) :=
  @List.rec ProgressLevel (fun P => AllL q P → AllL q (catL P [l]))
    (fun _ => ⟨hl, True.intro⟩)
    (fun x P' ih all => ⟨all.1, ih all.2⟩)
    P hP

theorem lexDownNil (E : List ProgressLevel) : lexDownB E [] = false :=
  @List.rec ProgressLevel (fun E => lexDownB E [] = false) rfl (fun _ _ _ => rfl) E

theorem lastIsCat (l : ProgressLevel) (P : List ProgressLevel) : LastIs l (catL P [l]) :=
  @List.rec ProgressLevel (fun P => LastIs l (catL P [l])) rfl
    (fun x P' ih => @List.rec ProgressLevel
      (fun P' => LastIs l (catL P' [l]) → LastIs l (catL (x :: P') [l]))
      (fun h => h)
      (fun _ _ _ h => h) P' ih)
    P

theorem nilNeCons (r : ProgressLevel) (rs : List ProgressLevel)
    (e : ([] : List ProgressLevel) = r :: rs) : False :=
  Eq.mp (congrArg (fun z => @List.rec ProgressLevel (fun _ => Prop) True (fun _ _ _ => False) z) e)
    True.intro

theorem dropLastCat (l : ProgressLevel) (P : List ProgressLevel) : dropLastL (catL P [l]) = P :=
  @List.rec ProgressLevel (fun P => dropLastL (catL P [l]) = P) rfl
    (fun x P' ih => @List.rec ProgressLevel
      (fun P' => dropLastL (catL P' [l]) = P' → dropLastL (catL (x :: P') [l]) = x :: P')
      (fun h => congrArg (fun z => x :: z) h)
      (fun _ _ _ h => congrArg (fun z => x :: z) h) P' ih)
    P

-- a shape whose levels are all disabled is impossible: its last level is enabled
theorem shapeNotAllOff (inner last : ProgressLevel → Prop) (en : ProgressLevel → Prop)
    (lastEn : ∀ l : ProgressLevel, last l → en l) (P : List ProgressLevel) :
    LevelsShape inner last P → AllL (fun x => ¬ en x) P → False :=
  @List.rec ProgressLevel (fun P => LevelsShape inner last P → AllL (fun x => ¬ en x) P → False)
    (fun shape _ => shape)
    (fun x P' ih => @List.rec ProgressLevel
      (fun P' => (LevelsShape inner last P' → AllL (fun x => ¬ en x) P' → False) →
        LevelsShape inner last (x :: P') → AllL (fun x => ¬ en x) (x :: P') → False)
      (fun _ shape all => all.1 (lastEn x shape))
      (fun y ys _ ih' shape all => ih' shape.2 all.2) P' ih)
    P

-- the shape at a list `P ++ l :: rest`: with nothing after `l`, `l` is last; otherwise inner
theorem shapeAt (inner last : ProgressLevel → Prop) (l : ProgressLevel) (rest P : List ProgressLevel) :
    LevelsShape inner last (catL P (l :: rest)) →
      (rest = [] → last l) ∧ (∀ (r : ProgressLevel) (rs : List ProgressLevel), rest = r :: rs → inner l) :=
  @List.rec ProgressLevel
    (fun P => LevelsShape inner last (catL P (l :: rest)) →
      (rest = [] → last l) ∧ (∀ (r : ProgressLevel) (rs : List ProgressLevel), rest = r :: rs → inner l))
    (@List.rec ProgressLevel
      (fun rest => LevelsShape inner last (l :: rest) →
        (rest = [] → last l) ∧ (∀ (r : ProgressLevel) (rs : List ProgressLevel), rest = r :: rs → inner l))
      (fun shape => ⟨fun _ => shape, fun r rs e => False.elim (nilNeCons r rs e)⟩)
      (fun r0 rs0 _ shape => ⟨fun e => False.elim (nilNeCons r0 rs0 (Eq.symm e)), fun _ _ _ => shape.1⟩)
      rest)
    (fun x P' ih shape =>
      ih (@List.rec ProgressLevel
        (fun P' => LevelsShape inner last (x :: catL P' (l :: rest)) →
          LevelsShape inner last (catL P' (l :: rest)))
        (fun s => s.2) (fun _ _ _ s => s.2) P' shape))
    P

-- ----- the temporal argument -----

-- What a nested certificate gives about a run: every state is a goal state or carries levels
-- (one list per state), boundedly long; a level other than the last names a strongly fair
-- helper that is disabled at the state, and the last names a fair helper enabled there; a step
-- of the last helper goes below the levels or wakes a helper above it, and every step does
-- that or keeps the levels.
structure LevelRun {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) : Prop where
  runs : _root_.Trust.Temporal.Runs M b
  cover : ∀ n : Nat, G (b n) ∨ ∃ L : List ProgressLevel, Lv (b n) L
  unique : ∀ (s : σ) (L E : List ProgressLevel), Lv s L → Lv s E → L = E
  bounded : ∀ (s : σ) (L : List ProgressLevel), Lv s L → lenL L ≤ bound
  shape : ∀ (s : σ) (L : List ProgressLevel), Lv s L →
    LevelsShape
      (fun l => ¬ _root_.Trust.Temporal.Enabled (A l.helper) s ∧
        _root_.Trust.Temporal.StrongFair (A l.helper) b)
      (fun l => _root_.Trust.Temporal.Enabled (A l.helper) s ∧
        (_root_.Trust.Temporal.WeakFair (A l.helper) b ∨ _root_.Trust.Temporal.StrongFair (A l.helper) b))
      L
  helper : ∀ (s t : σ) (L : List ProgressLevel) (l : ProgressLevel), Lv s L → LastIs l L →
    _root_.Trust.Temporal.NonStuttering (A l.helper) s t →
    G t ∨ ∃ E : List ProgressLevel, Lv t E ∧
      (lexDownB E L = true ∨ Wakes (fun h => _root_.Trust.Temporal.Enabled (A h) t) E (dropLastL L))
  other : ∀ (s t : σ) (L : List ProgressLevel), Lv s L → M.next s t →
    G t ∨ ∃ E : List ProgressLevel, Lv t E ∧
      (lexDownB E L = true ∨ prefixB L E = true ∨
        Wakes (fun h => _root_.Trust.Temporal.Enabled (A h) t) E L)

-- from index n on: no goal, every state's levels begin with P, and no helper of P is enabled
def LevelCtx {σ : Type} (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop)
    (Lv : σ → List ProgressLevel → Prop) (A : Nat → σ → σ → Prop) (P : List ProgressLevel)
    (n : Nat) : Prop :=
  ∀ d : Nat, ¬ G (b (n + d)) ∧ (∃ L : List ProgressLevel, Lv (b (n + d)) (catL P L)) ∧
    AllL (fun x => ¬ _root_.Trust.Temporal.Enabled (A x.helper) (b (n + d))) P

theorem ctxShift {σ : Type} (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop)
    (Lv : σ → List ProgressLevel → Prop) (A : Nat → σ → σ → Prop) (P : List ProgressLevel)
    (n : Nat) (c : LevelCtx b G Lv A P n) (m : Nat) : LevelCtx b G Lv A P (n + m) :=
  fun d => Eq.mpr
    (congrArg (fun z => ¬ G (b z) ∧ (∃ L : List ProgressLevel, Lv (b z) (catL P L)) ∧
        AllL (fun x => ¬ _root_.Trust.Temporal.Enabled (A x.helper) (b z)) P)
      (Nat.add_assoc n m d))
    (c (m + d))

-- under the context, every state has a level after P
theorem ctxCons {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) (H : LevelRun M b G Lv A bound)
    (P : List ProgressLevel) (n : Nat) (c : LevelCtx b G Lv A P n) (d : Nat) :
    ∃ l : ProgressLevel, ∃ rest : List ProgressLevel, Lv (b (n + d)) (catL P (l :: rest)) :=
  Exists.elim (c d).2.1 (fun L hL =>
    @List.rec ProgressLevel
      (fun L => Lv (b (n + d)) (catL P L) →
        ∃ l : ProgressLevel, ∃ rest : List ProgressLevel, Lv (b (n + d)) (catL P (l :: rest)))
      (fun h0 =>
        False.elim
          (shapeNotAllOff
            (fun l => ¬ _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
              _root_.Trust.Temporal.StrongFair (A l.helper) b)
            (fun l => _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
              (_root_.Trust.Temporal.WeakFair (A l.helper) b ∨ _root_.Trust.Temporal.StrongFair (A l.helper) b))
            (fun l => _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)))
            (fun l h => h.1) P
            (H.shape (b (n + d)) P (Eq.mp (congrArg (fun z => Lv (b (n + d)) z) (catNil P)) h0))
            (c d).2.2))
      (fun l rest _ h1 => ⟨l, rest, h1⟩)
      L hL)

-- a run that never gets below level l (after the context's P) keeps l at that level
theorem levelStay {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) (H : LevelRun M b G Lv A bound)
    (P : List ProgressLevel) (n : Nat) (c : LevelCtx b G Lv A P n)
    (l : ProgressLevel) (rest0 : List ProgressLevel) (start : Lv (b n) (catL P (l :: rest0)))
    (never : ¬ ∃ d : Nat, ∃ l' : ProgressLevel, ∃ rest' : List ProgressLevel,
      Nat.lt l'.rank l.rank ∧ Lv (b (n + d)) (catL P (l' :: rest'))) :
    ∀ d : Nat, ∃ rest : List ProgressLevel, Lv (b (n + d)) (catL P (l :: rest)) :=
  fun d => @Nat.rec (fun d => ∃ rest : List ProgressLevel, Lv (b (n + d)) (catL P (l :: rest)))
    ⟨rest0, start⟩
    (fun d prev => Exists.elim prev (fun rest hs =>
      Or.elim (H.runs.2 (n + d))
        (fun st =>
          Or.elim (H.other (b (n + d)) (b (Nat.succ (n + d))) (catL P (l :: rest)) hs st)
            (fun g => False.elim ((c (Nat.succ d)).1 g))
            (fun ex => Exists.elim ex (fun E facts =>
              Exists.elim (ctxCons M b G Lv A bound H P n c (Nat.succ d)) (fun l2 r2 =>
                Exists.elim r2 (fun rest2 h2 =>
                  (fun eqE : E = catL P (l2 :: rest2) =>
                    (fun same : l2 = l =>
                      @Exists.intro (List ProgressLevel)
                        (fun rest => Lv (b (n + Nat.succ d)) (catL P (l :: rest))) rest2
                        (Eq.mp (congrArg (fun z => Lv (b (n + Nat.succ d)) (catL P (z :: rest2))) same) h2))
                    (Or.elim facts.2
                      (fun down =>
                        Or.elim
                          (orBCases (Nat.blt l2.rank l.rank) (andB (lvEq l2 l) (lexDownB rest2 rest))
                            (lexDownCat (l2 :: rest2) (l :: rest) P
                              (Eq.mp (congrArg (fun z => lexDownB z (catL P (l :: rest)) = true) eqE) down)))
                          (fun lt => False.elim (never ⟨Nat.succ d, l2, rest2, bltLt l2.rank l.rank lt, h2⟩))
                          (fun same => lvEqSound l2 l (boolRecAnd (lvEq l2 l) (lexDownB rest2 rest) same).1))
                      (fun r => Or.elim r
                        (fun pre => lvEqSound l2 l
                          (boolRecAnd (lvEq l2 l) (prefixB rest rest2)
                            (prefixCat (l :: rest) (l2 :: rest2) P
                              (Eq.mp (congrArg (fun z => prefixB (catL P (l :: rest)) z = true) eqE) pre))).1)
                        (fun wk => Or.elim
                          (wakesCat (fun h => _root_.Trust.Temporal.Enabled (A h) (b (n + Nat.succ d)))
                            (l2 :: rest2) (l :: rest) P
                            (Eq.mp (congrArg (fun z =>
                              Wakes (fun h => _root_.Trust.Temporal.Enabled (A h) (b (n + Nat.succ d))) z
                                (catL P (l :: rest))) eqE) wk))
                          (fun any => False.elim
                            (anyAllFalse (fun x => _root_.Trust.Temporal.Enabled (A x.helper) (b (n + Nat.succ d)))
                              P any (c (Nat.succ d)).2.2))
                          (fun w => lvEqSound l2 l w.1)))))
                  (H.unique (b (n + Nat.succ d)) E (catL P (l2 :: rest2)) facts.1 h2))))))
        (fun stutter =>
          @Exists.intro (List ProgressLevel)
            (fun rest => Lv (b (n + Nat.succ d)) (catL P (l :: rest))) rest
            (Eq.mpr (congrArg (fun z => Lv z (catL P (l :: rest))) stutter) hs))))
    d

-- staying at level l, a step of l's helper is impossible
theorem levelHelperStuck {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) (H : LevelRun M b G Lv A bound)
    (P : List ProgressLevel) (n : Nat) (c : LevelCtx b G Lv A P n) (l : ProgressLevel)
    (stay : ∀ d : Nat, ∃ rest : List ProgressLevel, Lv (b (n + d)) (catL P (l :: rest)))
    (d : Nat)
    (step : _root_.Trust.Temporal.NonStuttering (A l.helper) (b (n + d)) (b (n + Nat.succ d))) :
    False :=
  Exists.elim (stay d) (fun rest hs =>
    @List.rec ProgressLevel (fun rest => Lv (b (n + d)) (catL P (l :: rest)) → False)
      (fun h0 =>
        Or.elim (H.helper (b (n + d)) (b (n + Nat.succ d)) (catL P [l]) l h0 (lastIsCat l P) step)
          (fun g => (c (Nat.succ d)).1 g)
          (fun ex => Exists.elim ex (fun E facts =>
            Exists.elim (stay (Nat.succ d)) (fun rest3 h3 =>
              (fun eqE : E = catL P (l :: rest3) =>
                Or.elim facts.2
                  (fun down =>
                    Or.elim
                      (orBCases (Nat.blt l.rank l.rank) (andB (lvEq l l) (lexDownB rest3 []))
                        (lexDownCat (l :: rest3) [l] P
                          (Eq.mp (congrArg (fun z => lexDownB z (catL P [l]) = true) eqE) down)))
                      (fun lt => bltSelf l.rank lt)
                      (fun same => Bool.noConfusion (Eq.trans (Eq.symm (lexDownNil rest3))
                        (boolRecAnd (lvEq l l) (lexDownB rest3 []) same).2)))
                  (fun wk =>
                    Or.elim
                      (wakesCat (fun h => _root_.Trust.Temporal.Enabled (A h) (b (n + Nat.succ d)))
                        (l :: rest3) [] P
                        (Eq.mp (congrArg (fun z =>
                            Wakes (fun h => _root_.Trust.Temporal.Enabled (A h) (b (n + Nat.succ d))) z
                              (catL P []))
                          eqE)
                          (Eq.mpr (congrArg (fun z =>
                              Wakes (fun h => _root_.Trust.Temporal.Enabled (A h) (b (n + Nat.succ d))) E z)
                            (catNil P))
                            (Eq.mp (congrArg (fun z =>
                                Wakes (fun h => _root_.Trust.Temporal.Enabled (A h) (b (n + Nat.succ d))) E z)
                              (dropLastCat l P)) wk))))
                      (fun any => anyAllFalse
                        (fun x => _root_.Trust.Temporal.Enabled (A x.helper) (b (n + Nat.succ d)))
                        P any (c (Nat.succ d)).2.2)
                      (fun w => w)))
              (H.unique (b (n + Nat.succ d)) E (catL P (l :: rest3)) facts.1 h3)))))
      (fun r rs _ h1 =>
        ((shapeAt
          (fun l => ¬ _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
            _root_.Trust.Temporal.StrongFair (A l.helper) b)
          (fun l => _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
            (_root_.Trust.Temporal.WeakFair (A l.helper) b ∨ _root_.Trust.Temporal.StrongFair (A l.helper) b))
          l (r :: rs) P (H.shape (b (n + d)) (catL P (l :: r :: rs)) h1)).2 r rs rfl).1
          ⟨b (n + Nat.succ d), step⟩)
      rest hs)

-- One level of the argument.  At the level after P the rank never rises, so it settles at some
-- l.  If l's helper is enabled again and again, fairness takes its step, which leaves l: so
-- eventually it is never enabled, and the argument goes one level deeper (`deeper`).
theorem levelDescend {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) (H : LevelRun M b G Lv A bound)
    (P : List ProgressLevel)
    (deeper : ∀ (l : ProgressLevel) (n : Nat), LevelCtx b G Lv A (catL P [l]) n → False) :
    ∀ (k n : Nat) (l : ProgressLevel) (rest0 : List ProgressLevel),
      LevelCtx b G Lv A P n → l.rank = k → Lv (b n) (catL P (l :: rest0)) → False :=
  natStrong
    (fun k => ∀ (n : Nat) (l : ProgressLevel) (rest0 : List ProgressLevel),
      LevelCtx b G Lv A P n → l.rank = k → Lv (b n) (catL P (l :: rest0)) → False)
    (fun k ih n l rest0 c hk start =>
      Or.elim (Classical.em (∃ d : Nat, ∃ l' : ProgressLevel, ∃ rest' : List ProgressLevel,
          Nat.lt l'.rank l.rank ∧ Lv (b (n + d)) (catL P (l' :: rest'))))
        (fun lower => Exists.elim lower (fun d r1 => Exists.elim r1 (fun l' r2 =>
          Exists.elim r2 (fun rest' facts =>
            ih l'.rank (Eq.mp (congrArg (fun z => Nat.lt l'.rank z) hk) facts.1) (n + d) l' rest'
              (ctxShift b G Lv A P n c d) rfl facts.2))))
        (fun never =>
          (fun stay : ∀ d : Nat, ∃ rest : List ProgressLevel, Lv (b (n + d)) (catL P (l :: rest)) =>
            Or.elim (Classical.em (∃ m : Nat, ∀ d : Nat,
                ¬ _root_.Trust.Temporal.Enabled (A l.helper) (b (n + (m + d)))))
              (fun off => Exists.elim off (fun m offm =>
                deeper l (n + m) (fun d =>
                  Eq.mpr
                    (congrArg (fun z => ¬ G (b z) ∧
                        (∃ L : List ProgressLevel, Lv (b z) (catL (catL P [l]) L)) ∧
                        AllL (fun x => ¬ _root_.Trust.Temporal.Enabled (A x.helper) (b z)) (catL P [l]))
                      (Nat.add_assoc n m d))
                    (Exists.elim (stay (m + d)) (fun rest hs =>
                      ⟨(c (m + d)).1,
                       @Exists.intro (List ProgressLevel)
                         (fun L => Lv (b (n + (m + d))) (catL (catL P [l]) L)) rest
                         (Eq.mp (congrArg (fun z => Lv (b (n + (m + d))) z) (catAssoc l rest P)) hs),
                       allCatSingle
                         (fun x => ¬ _root_.Trust.Temporal.Enabled (A x.helper) (b (n + (m + d))))
                         l P (c (m + d)).2.2 (offm d)⟩)))))
              (fun notOff =>
                (fun inf : ∀ m : Nat, ∃ d : Nat,
                    _root_.Trust.Temporal.Enabled (A l.helper) (b (n + (m + d))) =>
                  Or.elim (Classical.em (∃ d : Nat, ∃ r : ProgressLevel, ∃ rs : List ProgressLevel,
                      Lv (b (n + d)) (catL P (l :: r :: rs))))
                    (fun innerSomewhere => Exists.elim innerSomewhere (fun d r1 => Exists.elim r1 (fun r r2 =>
                      Exists.elim r2 (fun rs hs =>
                        (fun sf : _root_.Trust.Temporal.StrongFair (A l.helper) b =>
                          Exists.elim (sf n inf) (fun d2 act =>
                            levelHelperStuck M b G Lv A bound H P n c l stay d2 act))
                        ((shapeAt
                          (fun l => ¬ _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
                            _root_.Trust.Temporal.StrongFair (A l.helper) b)
                          (fun l => _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
                            (_root_.Trust.Temporal.WeakFair (A l.helper) b ∨
                              _root_.Trust.Temporal.StrongFair (A l.helper) b))
                          l (r :: rs) P (H.shape (b (n + d)) (catL P (l :: r :: rs)) hs)).2 r rs rfl).2))))
                    (fun allLast =>
                      (fun lastAt : ∀ d : Nat, Lv (b (n + d)) (catL P [l]) =>
                        (fun lastFacts : ∀ d : Nat,
                            _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
                            (_root_.Trust.Temporal.WeakFair (A l.helper) b ∨
                              _root_.Trust.Temporal.StrongFair (A l.helper) b) =>
                          Or.elim (lastFacts 0).2
                            (fun wf => Exists.elim
                              (wf n ⟨0, fun d => Eq.mpr
                                (congrArg (fun z => _root_.Trust.Temporal.Enabled (A l.helper) (b (n + z)))
                                  (Nat.zero_add d))
                                (lastFacts d).1⟩)
                              (fun d2 act => levelHelperStuck M b G Lv A bound H P n c l stay d2 act))
                            (fun sf => Exists.elim
                              (sf n (fun m => ⟨0, (lastFacts m).1⟩))
                              (fun d2 act => levelHelperStuck M b G Lv A bound H P n c l stay d2 act)))
                        (fun d => (shapeAt
                          (fun l => ¬ _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
                            _root_.Trust.Temporal.StrongFair (A l.helper) b)
                          (fun l => _root_.Trust.Temporal.Enabled (A l.helper) (b (n + d)) ∧
                            (_root_.Trust.Temporal.WeakFair (A l.helper) b ∨
                              _root_.Trust.Temporal.StrongFair (A l.helper) b))
                          l [] P (H.shape (b (n + d)) (catL P [l]) (lastAt d))).1 rfl))
                      (fun d => Exists.elim (stay d) (fun rest hs =>
                        @List.rec ProgressLevel
                          (fun rest => Lv (b (n + d)) (catL P (l :: rest)) → Lv (b (n + d)) (catL P [l]))
                          (fun h0 => h0)
                          (fun r rs _ h1 => False.elim (allLast ⟨d, r, rs, h1⟩))
                          rest hs))))
                (fun m => Or.elim (Classical.em (∃ d : Nat,
                    _root_.Trust.Temporal.Enabled (A l.helper) (b (n + (m + d)))))
                  (fun yes => yes)
                  (fun no => False.elim (notOff ⟨m, fun d en => no ⟨d, en⟩⟩)))))
          (levelStay M b G Lv A bound H P n c l rest0 start never)))

theorem levelStuck {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) (H : LevelRun M b G Lv A bound) :
    ∀ (e : Nat) (P : List ProgressLevel), lenL P + e = bound →
      ∀ n : Nat, LevelCtx b G Lv A P n → False :=
  fun e => @Nat.rec
    (fun e => ∀ (P : List ProgressLevel), lenL P + e = bound →
      ∀ n : Nat, LevelCtx b G Lv A P n → False)
    (fun P hlen n c => Exists.elim (ctxCons M b G Lv A bound H P n c 0) (fun l r =>
      Exists.elim r (fun rest hs =>
        Nat.lt_irrefl (lenL P)
          (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right (lenL P) (lenL rest)))
            (Eq.mp (congrArg (fun z => Nat.le (lenL P + lenL (l :: rest)) z) (Eq.symm hlen))
              (Eq.mp (congrArg (fun z => Nat.le z bound) (lenCat (l :: rest) P))
                (H.bounded (b (n + 0)) (catL P (l :: rest)) hs)))))))
    (fun e ih P hlen n c => Exists.elim (ctxCons M b G Lv A bound H P n c 0) (fun l r =>
      Exists.elim r (fun rest hs =>
        levelDescend M b G Lv A bound H P
          (fun l' n' c' => ih (catL P [l'])
            (Eq.trans (congrArg (fun z => z + e) (lenCat [l'] P))
              (Eq.trans (Nat.add_assoc (lenL P) (lenL [l']) e)
                (Eq.trans (congrArg (fun z => lenL P + z) (Nat.add_comm (lenL [l']) e)) hlen)))
            n' c')
          l.rank n l rest c rfl hs)))
    e

-- THE NESTED RULE, temporally: a run that a level structure covers reaches the goal again and again
theorem levelsProgress {σ : Type} (M : _root_.Trust.Temporal.StateMachine σ)
    (b : _root_.Trust.Temporal.Behavior σ) (G : σ → Prop) (Lv : σ → List ProgressLevel → Prop)
    (A : Nat → σ → σ → Prop) (bound : Nat) (H : LevelRun M b G Lv A bound) :
    _root_.Trust.Temporal.Always (_root_.Trust.Temporal.Eventually (_root_.Trust.Temporal.Lift G)) b :=
  fun n => Or.elim (Classical.em (∃ d : Nat, G (b (n + d))))
    (fun found => found)
    (fun none => False.elim
      (levelStuck M b G Lv A bound H bound [] (Nat.zero_add bound) n
        (fun d => ⟨fun g => none ⟨d, g⟩,
          Or.elim (H.cover (n + d)) (fun g => False.elim (none ⟨d, g⟩)) (fun ex => ex),
          True.intro⟩)))

-- ===== 9b. the compiled step, the other way: a row the action moves is a state it moves =====

theorem optionCases {α : Type} (o : Option α) : o = none ∨ ∃ x : α, o = some x :=
  @Option.rec α (fun o => o = none ∨ ∃ x : α, o = some x) (Or.inl rfl) (fun x => Or.inr ⟨x, rfl⟩) o

theorem lookupSlotDeclares (name : String) (vs : List StateVar) :
    ∀ i : Nat, lookupSlot vs name = some i →
      ∃ entry : StateVar, Member entry vs ∧ entry.name = name :=
  @List.rec StateVar
    (fun vs => ∀ i : Nat, lookupSlot vs name = some i →
      ∃ entry : StateVar, Member entry vs ∧ entry.name = name)
    (fun i h => False.elim (noneNeSome h))
    (fun v rest ih i h =>
      Or.elim (boolCases (decide (v.name = name)))
        (fun hd => ⟨v, Member.head rest, lsName v name hd⟩)
        (fun hd => Exists.elim (lsFalse v rest name i hd h) (fun j facts =>
          Exists.elim (ih j facts.1) (fun entry ef => ⟨entry, Member.tail v rest ef.1, ef.2⟩))))
    vs

theorem lookupSlotStep (v : StateVar) (rest : List StateVar) (name : String) (b : Bool)
    (hd : decide (v.name = name) = b) :
    lookupSlot (v :: rest) name =
      @Bool.rec (fun _ => Option Nat)
        (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i)) (lookupSlot rest name))
        (some 0) b :=
  congrArg (fun z => @Bool.rec (fun _ => Option Nat)
    (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i)) (lookupSlot rest name))
    (some 0) z) hd

theorem lookupSlotFinds (name : String) (vs : List StateVar) :
    (∃ entry : StateVar, Member entry vs ∧ entry.name = name) →
      ∃ i : Nat, lookupSlot vs name = some i :=
  @List.rec StateVar
    (fun vs => (∃ entry : StateVar, Member entry vs ∧ entry.name = name) →
      ∃ i : Nat, lookupSlot vs name = some i)
    (fun declared => Exists.elim declared (fun _ facts => False.elim (memberNilFalse facts.1)))
    (fun v rest ih declared =>
      Or.elim (boolCases (decide (v.name = name)))
        (fun hd => ⟨0, lookupSlotStep v rest name true hd⟩)
        (fun hd => Exists.elim declared (fun entry facts =>
          Or.elim (memberConsInv facts.1)
            (fun same => False.elim (of_decide_eq_false hd
              (Eq.trans (congrArg StateVar.name (Eq.symm same)) facts.2)))
            (fun later => Exists.elim (ih ⟨entry, later, facts.2⟩) (fun j found =>
              ⟨Nat.succ j, Eq.trans (lookupSlotStep v rest name false hd)
                (congrArg (fun o => @Option.rec Nat (fun _ => Option Nat) none
                  (fun i => some (Nat.succ i)) o) found)⟩)))))
    vs

theorem guardComplete (model : ScalarModel) (st : State) (row : List Nat)
    (denote : ScalarCoordinatesDenote st model.variables row) (g : Guard) (cg : CExpr)
    (h : compileGuard model.variables model.constants g = some cg)
    (holds : evalB row cg = true) : GuardHolds model.asModel st g :=
  @Guard.rec
    (fun g => compileGuard model.variables model.constants g = some cg →
      GuardHolds model.asModel st g)
    (fun _ => True.intro)
    (fun e k => Eq.mp
      (congrArg (fun z => Evaluates model.asModel [] st e (Value.bool z)) holds)
      (compileExact model st row denote e Srt.bool cg k).derives)
    g h

def foundIsDup (f : Found) : Bool := @Found.rec (fun _ => Bool) false (fun _ => false) true f

-- an action that compiled updates no declared variable twice, and each update compiles
def FoundOk (vars : List StateVar) (consts : List Constant) (us : List Update) (v : StateVar) : Prop :=
  (findU us v.name = Found.dup → False) ∧
  (∀ e : ScalarExpr, findU us v.name = Found.one e →
    ∃ c : CExpr, compileS vars consts e Srt.nat = some c)

theorem compileUpdsFound (vars : List StateVar) (consts : List Constant) (us : List Update)
    (vs : List StateVar) :
    ∀ upd : List (Option CExpr), compileUpds vars consts us vs = some upd →
      ∀ v : StateVar, Member v vs → FoundOk vars consts us v :=
  @List.rec StateVar
    (fun vs => ∀ upd : List (Option CExpr), compileUpds vars consts us vs = some upd →
      ∀ v : StateVar, Member v vs → FoundOk vars consts us v)
    (fun upd _ v mem => False.elim (memberNilFalse mem))
    (fun hd rest ih upd h v mem =>
      Or.elim (foundCases (findU us hd.name))
        (fun hf =>
          Exists.elim (optionMapSome (compileUpds vars consts us rest) (fun xs => none :: xs) upd
              (Eq.trans (Eq.symm (compileUpdsStep vars consts us hd rest Found.none hf)) h))
            (fun upd' f => Or.elim (memberConsInv mem)
              (fun same => Eq.mpr (congrArg (fun z => FoundOk vars consts us z) same)
                (And.intro
                  (fun hdup => Bool.noConfusion (congrArg foundIsNone (Eq.trans (Eq.symm hdup) hf)))
                  (fun e hone => False.elim
                    (Bool.noConfusion (congrArg foundIsNone (Eq.trans (Eq.symm hone) hf))))))
              (fun later => ih upd' f.1 v later)))
        (fun rest2 => Or.elim rest2
          (fun one => Exists.elim one (fun e0 hf =>
            Exists.elim (optionBindSome (compileS vars consts e0 Srt.nat)
                (fun c => consOpt (some c) (compileUpds vars consts us rest)) upd
                (Eq.trans (Eq.symm (compileUpdsStep vars consts us hd rest (Found.one e0) hf)) h))
              (fun c0 f1 =>
                Exists.elim (optionMapSome (compileUpds vars consts us rest)
                    (fun xs => some c0 :: xs) upd f1.2)
                  (fun upd' f2 => Or.elim (memberConsInv mem)
                    (fun same => Eq.mpr (congrArg (fun z => FoundOk vars consts us z) same)
                      (And.intro
                        (fun hdup => Bool.noConfusion
                          (congrArg foundIsDup (Eq.trans (Eq.symm hf) hdup)))
                        (fun e hone => ⟨c0, Eq.mp
                          (congrArg (fun z => compileS vars consts z Srt.nat = some c0)
                            (oneInj (Eq.trans (Eq.symm hf) hone))) f1.1⟩)))
                    (fun later => ih upd' f2.1 v later)))))
          (fun hf => False.elim (noneNeSome
            (Eq.trans (Eq.symm (compileUpdsStep vars consts us hd rest Found.dup hf)) h)))))
    vs

-- the after-state of `a` from a state denoting `row`: every declared variable takes its
-- update's compiled value (or keeps its own), everything else is zero
def stepScalar (model : ScalarModel) (a : Action) (row : List Nat) (s : State) (name : String) : Nat :=
  @Option.rec Nat (fun _ => Nat) 0
    (fun _ => @Found.rec (fun _ => Nat) (s.scalar name)
      (fun e => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c)
        (compileS model.variables model.constants e Srt.nat))
      0 (findU a.updates name))
    (lookupSlot model.variables name)

def stepState (model : ScalarModel) (a : Action) (row : List Nat) (s : State) : State :=
  State.mk (stepScalar model a row s) (fun _ _ => false)

theorem stepScalarDeclared (model : ScalarModel) (a : Action) (row : List Nat) (s : State)
    (name : String) (i : Nat) (found : lookupSlot model.variables name = some i) :
    stepScalar model a row s name =
      @Found.rec (fun _ => Nat) (s.scalar name)
        (fun e => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c)
          (compileS model.variables model.constants e Srt.nat))
        0 (findU a.updates name) :=
  congrArg (fun o => @Option.rec Nat (fun _ => Nat) 0
    (fun _ => @Found.rec (fun _ => Nat) (s.scalar name)
      (fun e => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c)
        (compileS model.variables model.constants e Srt.nat))
      0 (findU a.updates name)) o) found

theorem stepCanonical (model : ScalarModel) (a : Action) (row : List Nat) (s : State) :
    CanonicalState model.asModel (stepState model a row s) :=
  And.intro
    (fun name undeclared =>
      Or.elim (optionCases (lookupSlot model.variables name))
        (fun none_ => congrArg (fun o => @Option.rec Nat (fun _ => Nat) 0
          (fun _ => @Found.rec (fun _ => Nat) (s.scalar name)
            (fun e => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c)
              (compileS model.variables model.constants e Srt.nat))
            0 (findU a.updates name)) o) none_)
        (fun some_ => Exists.elim some_ (fun i found =>
          False.elim (undeclared (lookupSlotDeclares name model.variables i found)))))
    (fun _ _ _ => rfl)

-- one declared variable's clause of ActionHolds
def StepClause (model : ScalarModel) (a : Action) (row : List Nat) (s : State)
    (entry : StateVar) : Prop :=
  (∃ update : Update, Member update a.updates ∧ update.var = entry.name ∧
      Evaluates model.asModel [] s update.value
        (Value.nat ((stepState model a row s).scalar entry.name))) ∨
  (NoUpdate a entry.name ∧
    (stepState model a row s).scalar entry.name = s.scalar entry.name)

theorem stepClauseNone (model : ScalarModel) (a : Action) (row : List Nat) (s : State)
    (entry : StateVar) (i : Nat) (found : lookupSlot model.variables entry.name = some i)
    (hf : findU a.updates entry.name = Found.none) : StepClause model a row s entry :=
  Or.inr (And.intro
    (fun (update : Update) (umem : Member update a.updates) =>
      everyMember (fun u : Update => ¬ (u.var = entry.name)) update a.updates
        (findUNone entry.name a.updates hf) umem)
    (Eq.trans (stepScalarDeclared model a row s entry.name i found)
      (congrArg (fun f => @Found.rec (fun _ => Nat) (s.scalar entry.name)
        (fun e => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c)
          (compileS model.variables model.constants e Srt.nat)) 0 f) hf)))

theorem stepScalarOne (model : ScalarModel) (a : Action) (row : List Nat) (s : State)
    (name : String) (i : Nat) (found : lookupSlot model.variables name = some i)
    (e : ScalarExpr) (hf : findU a.updates name = Found.one e)
    (c : CExpr) (hc : compileS model.variables model.constants e Srt.nat = some c) :
    (stepState model a row s).scalar name = evalN row c :=
  Eq.trans (stepScalarDeclared model a row s name i found)
    (Eq.trans
      (congrArg (fun f => @Found.rec (fun _ => Nat) (s.scalar name)
        (fun e => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c)
          (compileS model.variables model.constants e Srt.nat)) 0 f) hf)
      (congrArg (fun o => @Option.rec CExpr (fun _ => Nat) 0 (fun c => evalN row c) o) hc))

theorem stepClauseOne (model : ScalarModel) (a : Action) (row : List Nat) (s : State)
    (den : ScalarRowDenotes model row s)
    (entry : StateVar) (i : Nat) (found : lookupSlot model.variables entry.name = some i)
    (e : ScalarExpr) (hf : findU a.updates entry.name = Found.one e)
    (c : CExpr) (hc : compileS model.variables model.constants e Srt.nat = some c) :
    StepClause model a row s entry :=
  Exists.elim (findUOne entry.name e a.updates hf).2 (fun w wf =>
    Or.inl (@Exists.intro Update
      (fun update => Member update a.updates ∧ update.var = entry.name ∧
        Evaluates model.asModel [] s update.value
          (Value.nat ((stepState model a row s).scalar entry.name)))
      w
      (And.intro wf.1 (And.intro wf.2
        (Eq.mpr
          (congrArg (fun z => Evaluates model.asModel [] s z
              (Value.nat ((stepState model a row s).scalar entry.name)))
            (everyMember (fun u : Update => u.var = entry.name → u.value = e) w a.updates
              (findUOne entry.name e a.updates hf).1 wf.1 wf.2))
          (Eq.mpr
            (congrArg (fun z => Evaluates model.asModel [] s e (Value.nat z))
              (stepScalarOne model a row s entry.name i found e hf c hc))
            (compileExact model s row den.2 e Srt.nat c hc).derives))))))

theorem stepScalarClause (model : ScalarModel) (a : Action) (ca : CAction)
    (hca : compileAction model.variables model.constants a = some ca)
    (row : List Nat) (s : State) (den : ScalarRowDenotes model row s)
    (entry : StateVar) (mem : Member entry model.variables) :
    StepClause model a row s entry :=
  Exists.elim (lookupSlotFinds entry.name model.variables
      (@Exists.intro StateVar (fun e => Member e model.variables ∧ e.name = entry.name) entry
        (And.intro mem rfl)))
    (fun i found =>
      Or.elim (foundCases (findU a.updates entry.name))
        (fun hf => stepClauseNone model a row s entry i found hf)
        (fun rest => Or.elim rest
          (fun one => Exists.elim one (fun e hf =>
            Exists.elim
              ((compileUpdsFound model.variables model.constants a.updates model.variables ca.upd
                (compileActionSound model.variables model.constants a ca hca).2 entry mem).2 e hf)
              (fun c hc => stepClauseOne model a row s den entry i found e hf c hc)))
          (fun hf => False.elim
            ((compileUpdsFound model.variables model.constants a.updates model.variables ca.upd
              (compileActionSound model.variables model.constants a ca hca).2 entry mem).1 hf))))

-- COMPLETENESS of the compiled step: a true compiled guard is a step of the action
theorem actionHoldsIntro (model : Model) (a : Action) (before after : State)
    (guard : GuardHolds model before a.guard)
    (canonical : CanonicalState model after)
    (scalars : ∀ entry : StateVar, Member entry model.variables →
      ((∃ update : Update, Member update a.updates ∧
          update.var = entry.name ∧
          Evaluates model [] before update.value
            (Value.nat (after.scalar entry.name))) ∨
       (NoUpdate a entry.name ∧
          after.scalar entry.name = before.scalar entry.name)))
    (functions : ∀ entry : FunctionVar, Member entry model.functionVariables →
      ((∃ update : Update, Member update a.updates ∧
          update.var = entry.name ∧
          Evaluates model [] before update.value
            (Value.function entry.rangeConstant (after.function entry.name))) ∨
       (NoUpdate a entry.name ∧
          after.function entry.name = before.function entry.name))) :
    ActionHolds model a before after :=
  And.intro guard (And.intro canonical (And.intro scalars functions))

theorem stepHolds (model : ScalarModel) (a : Action) (ca : CAction)
    (hca : compileAction model.variables model.constants a = some ca)
    (row : List Nat) (s : State) (den : ScalarRowDenotes model row s)
    (guard : evalB row ca.guard = true) :
    ActionHolds model.asModel a s (stepState model a row s) :=
  actionHoldsIntro model.asModel a s (stepState model a row s)
    (guardComplete model s row den.2 a.guard ca.guard
      (compileActionSound model.variables model.constants a ca hca).1 guard)
    (stepCanonical model a row s)
    (fun (entry : StateVar) (mem : Member entry model.asModel.variables) =>
      stepScalarClause model a ca hca row s den entry mem)
    (fun (entry : FunctionVar) (mem : Member entry model.asModel.functionVariables) =>
      False.elim (memberNilFalse mem))

theorem rowEqRefl (a : List Nat) : rowEq a a = true :=
  @List.rec Nat (fun a => rowEq a a = true) rfl
    (fun x xs ih => Eq.trans
      (congrArg (fun z => @Bool.rec (fun _ => Bool) false (rowEq xs xs) z) (Nat.beq_refl x)) ih)
    a

-- a state denotes one row
theorem denoteUnique (st : State) (vs : List StateVar) :
    ∀ r1 r2 : List Nat, ScalarCoordinatesDenote st vs r1 → ScalarCoordinatesDenote st vs r2 →
      r1 = r2 :=
  @List.rec StateVar
    (fun vs => ∀ r1 r2 : List Nat,
      ScalarCoordinatesDenote st vs r1 → ScalarCoordinatesDenote st vs r2 → r1 = r2)
    (fun r1 =>
      @List.rec Nat
        (fun r1 => ∀ r2 : List Nat, ScalarCoordinatesDenote st [] r1 →
          ScalarCoordinatesDenote st [] r2 → r1 = r2)
        (fun r2 =>
          @List.rec Nat
            (fun r2 => ScalarCoordinatesDenote st [] [] → ScalarCoordinatesDenote st [] r2 → [] = r2)
            (fun _ _ => rfl) (fun _ _ _ _ d2 => False.elim d2) r2)
        (fun _ _ _ _ d1 _ => False.elim d1)
        r1)
    (fun v rest ih r1 =>
      @List.rec Nat
        (fun r1 => ∀ r2 : List Nat, ScalarCoordinatesDenote st (v :: rest) r1 →
          ScalarCoordinatesDenote st (v :: rest) r2 → r1 = r2)
        (fun _ d1 _ => False.elim d1)
        (fun x xs _ r2 =>
          @List.rec Nat
            (fun r2 => ScalarCoordinatesDenote st (v :: rest) (x :: xs) →
              ScalarCoordinatesDenote st (v :: rest) r2 → x :: xs = r2)
            (fun _ d2 => False.elim d2)
            (fun y ys _ d1 d2 =>
              Eq.trans
                (congrArg (fun z => z :: xs) (Eq.trans (Eq.symm d1.1) d2.1))
                (congrArg (fun zs => y :: zs) (ih xs ys d1.2 d2.2)))
            r2)
        r1)
    vs

theorem movesParts (row : List Nat) (ca : CAction) (h : movesRow row ca = true) :
    evalB row ca.guard = true ∧ rowEq (succRow row ca.upd row) row = false :=
  (fun both => And.intro both.1
    (@Bool.rec (fun b => notB b = true → b = false) (fun _ => rfl)
      (fun k => Bool.noConfusion k) (rowEq (succRow row ca.upd row) row) both.2))
  (boolRecAnd (evalB row ca.guard) (notB (rowEq (succRow row ca.upd row) row)) h)

theorem enabledIntro {σ : Type} (A : σ → σ → Prop) (s t : σ) (step : A s t)
    (moved : ¬ (t = s)) : _root_.Trust.Temporal.Enabled A s :=
  @Exists.intro σ (fun t' => _root_.Trust.Temporal.NonStuttering A s t') t (And.intro step moved)

theorem namedIntro (model : Model) (name : String) (a : Action) (s t : State)
    (mem : Member a model.actions) (named : a.name = name)
    (holds : ActionHolds model a s t) : NamedAction model name s t :=
  @Exists.intro Action
    (fun a' => Member a' model.actions ∧ a'.name = name ∧ ActionHolds model a' s t)
    a (And.intro mem (And.intro named holds))

-- a compiled step that moves the row leaves the state
theorem stepMoves (model : ScalarModel) (a : Action) (ca : CAction)
    (hca : compileAction model.variables model.constants a = some ca)
    (row : List Nat) (s t : State) (den : ScalarRowDenotes model row s)
    (holds : ActionHolds model.asModel a s t)
    (differs : rowEq (succRow row ca.upd row) row = false) : ¬ (t = s) :=
  fun same : t = s =>
    Bool.noConfusion (Eq.trans (Eq.symm differs)
      (Eq.trans
        (congrArg (fun z => rowEq z row)
          (denoteUnique s model.variables (succRow row ca.upd row) row
            (Eq.mp
              (congrArg (fun z => ScalarCoordinatesDenote z model.variables
                (succRow row ca.upd row)) same)
              (succDenotes model a s t row den.2 holds
                model.variables (fun entry m => m) row ca.upd den.2
                (compileActionSound model.variables model.constants a ca hca).2))
            den.2))
        (rowEqRefl row)))

theorem movesEnabled (model : ScalarModel) (a : Action) (ca : CAction) (name : String)
    (mem : Member a model.actions) (named : a.name = name)
    (hca : compileAction model.variables model.constants a = some ca)
    (row : List Nat) (s : State) (den : ScalarRowDenotes model row s)
    (moves : movesRow row ca = true) :
    _root_.Trust.Temporal.Enabled (NamedAction model.asModel name) s :=
  enabledIntro (NamedAction model.asModel name) s (stepState model a row s)
    (namedIntro model.asModel name a s (stepState model a row s) mem named
      (stepHolds model a ca hca row s den (movesParts row ca moves).1))
    (stepMoves model a ca hca row s (stepState model a row s) den
      (stepHolds model a ca hca row s den (movesParts row ca moves).1)
      (movesParts row ca moves).2)

-- ===== 9c. a fair NAME is one action: the one at its slot =====

theorem countStep {α : Type} (p : α → Bool) (x : α) (xs : List α) (b : Bool) (hb : p x = b) :
    countB p (x :: xs) = @Bool.rec (fun _ => Nat) (countB p xs) (Nat.succ (countB p xs)) b :=
  congrArg (fun z => @Bool.rec (fun _ => Nat) (countB p xs) (Nat.succ (countB p xs)) z) hb

theorem countZero {α : Type} (p : α → Bool) (xs : List α) :
    countB p xs = 0 → ∀ x : α, Member x xs → p x = false :=
  @List.rec α (fun xs => countB p xs = 0 → ∀ x : α, Member x xs → p x = false)
    (fun _ x mem => False.elim (memberNilFalse mem))
    (fun hd tl ih h x mem =>
      Or.elim (boolCases (p hd))
        (fun ht => Nat.noConfusion (Eq.trans (Eq.symm (countStep p hd tl true ht)) h))
        (fun hf => Or.elim (memberConsInv mem)
          (fun same => Eq.trans (congrArg p same) hf)
          (fun later => ih (Eq.trans (Eq.symm (countStep p hd tl false hf)) h) x later)))
    xs

theorem countOneUnique {α : Type} (p : α → Bool) (xs : List α) :
    countB p xs = 1 → ∀ x y : α, Member x xs → Member y xs → p x = true → p y = true → x = y :=
  @List.rec α
    (fun xs => countB p xs = 1 →
      ∀ x y : α, Member x xs → Member y xs → p x = true → p y = true → x = y)
    (fun _ x _ mem _ _ _ => False.elim (memberNilFalse mem))
    (fun hd tl ih h x y mx my px py =>
      Or.elim (boolCases (p hd))
        (fun ht =>
          (fun none : ∀ z : α, Member z tl → p z = false =>
            (fun isHead : ∀ z : α, Member z (hd :: tl) → p z = true → z = hd =>
              Eq.trans (isHead x mx px) (Eq.symm (isHead y my py)))
            (fun (z : α) (mz : Member z (hd :: tl)) (pz : p z = true) =>
              Or.elim (memberConsInv mz) (fun same => same)
                (fun later => Bool.noConfusion (Eq.trans (Eq.symm (none z later)) pz))))
          (countZero p tl (congrArg Nat.pred
            (Eq.trans (Eq.symm (countStep p hd tl true ht)) h))))
        (fun hf =>
          (fun inTail : ∀ z : α, Member z (hd :: tl) → p z = true → Member z tl =>
            ih (Eq.trans (Eq.symm (countStep p hd tl false hf)) h) x y
              (inTail x mx px) (inTail y my py) px py)
          (fun (z : α) (mz : Member z (hd :: tl)) (pz : p z = true) =>
            Or.elim (memberConsInv mz)
              (fun same => Bool.noConfusion
                (Eq.trans (Eq.symm hf) (Eq.trans (congrArg p (Eq.symm same)) pz)))
              (fun later => later))))
    xs

theorem firstSlotStep (a : Action) (rest : List Action) (name : String) (b : Bool)
    (hd : decide (a.name = name) = b) :
    firstActionSlot (a :: rest) name =
      @Bool.rec (fun _ => Option Nat)
        (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i))
          (firstActionSlot rest name))
        (some 0) b :=
  congrArg (fun z => @Bool.rec (fun _ => Option Nat)
    (@Option.rec Nat (fun _ => Option Nat) none (fun i => some (Nat.succ i))
      (firstActionSlot rest name))
    (some 0) z) hd

-- the action at a name's first slot compiles to the compiled action at that slot
theorem slotCompiled (f : Action → Option CAction) (name : String) (acts : List Action) :
    ∀ (cacts : List CAction) (h : Nat) (ca : CAction),
      mapOpt f acts = some cacts → firstActionSlot acts name = some h →
      nthAction cacts h = some ca →
      ∃ a : Action, Member a acts ∧ a.name = name ∧ f a = some ca :=
  @List.rec Action
    (fun acts => ∀ (cacts : List CAction) (h : Nat) (ca : CAction),
      mapOpt f acts = some cacts → firstActionSlot acts name = some h →
      nthAction cacts h = some ca →
      ∃ a : Action, Member a acts ∧ a.name = name ∧ f a = some ca)
    (fun _ _ _ _ hs _ => False.elim (noneNeSome hs))
    (fun a rest ih cacts h ca hm hs hn =>
      Exists.elim (optionBindSome (f a)
          (fun y => @Option.rec (List CAction) (fun _ => Option (List CAction)) none
            (fun ys => some (y :: ys)) (mapOpt f rest)) cacts hm)
        (fun ca0 f1 =>
          Exists.elim (optionMapSome (mapOpt f rest) (fun ys => ca0 :: ys) cacts f1.2)
            (fun cacts' f2 =>
              Or.elim (boolCases (decide (a.name = name)))
                (fun hd =>
                  @Exists.intro Action (fun x => Member x (a :: rest) ∧ x.name = name ∧ f x = some ca) a
                    (And.intro (Member.head rest)
                      (And.intro (of_decide_eq_true hd)
                        (Eq.trans f1.1
                          (Eq.mp
                            (congrArg (fun z => nthAction (ca0 :: cacts') z = some ca)
                              (Eq.symm (someInj (Eq.trans
                                (Eq.symm (firstSlotStep a rest name true hd)) hs))))
                            (Eq.mp (congrArg (fun z => nthAction z h = some ca) (Eq.symm f2.2))
                              hn))))))
                (fun hd =>
                  Exists.elim (optionMapSome (firstActionSlot rest name) Nat.succ h
                      (Eq.trans (Eq.symm (firstSlotStep a rest name false hd)) hs))
                    (fun j f3 =>
                      Exists.elim (ih cacts' j ca f2.1 f3.1
                          (Eq.mp
                            (congrArg (fun z => nthAction (ca0 :: cacts') z = some ca)
                              (Eq.symm f3.2))
                            (Eq.mp (congrArg (fun z => nthAction z h = some ca) (Eq.symm f2.2))
                              hn)))
                        (fun x xf =>
                          @Exists.intro Action
                            (fun x => Member x (a :: rest) ∧ x.name = name ∧ f x = some ca) x
                            (And.intro (Member.tail a rest xf.1) xf.2)))))))
    acts

theorem actionSlotParts (acts : List Action) (name : String) (h : Nat)
    (hs : actionSlot acts name = some h) :
    countB (fun (a : Action) => decide (a.name = name)) acts = 1 ∧
      firstActionSlot acts name = some h :=
  Or.elim (boolCases (Nat.beq (countB (fun (a : Action) => decide (a.name = name)) acts) 1))
    (fun ht => And.intro
      (natBeqSound (countB (fun (a : Action) => decide (a.name = name)) acts) 1 ht)
      (Eq.trans
        (congrArg (fun b => @Bool.rec (fun _ => Option Nat) none (firstActionSlot acts name) b)
          (Eq.symm ht)) hs))
    (fun hf => False.elim (noneNeSome (Eq.trans
      (congrArg (fun b => @Bool.rec (fun _ => Option Nat) none (firstActionSlot acts name) b)
        (Eq.symm hf)) hs)))

theorem decideTrue (a b : String) (same : a = b) : decide (a = b) = true :=
  Or.elim (boolCases (decide (a = b))) (fun t => t)
    (fun f => False.elim (of_decide_eq_false f same))

-- the action(s) named by a fair name: there is one, and every one compiles to the slot's action
theorem namedSlot (model : ScalarModel) (cm : CModel)
    (hacts : mapOpt (compileAction model.variables model.constants) model.actions = some cm.actions)
    (name : String) (h : Nat) (ca : CAction)
    (hs : actionSlot model.actions name = some h) (hn : nthAction cm.actions h = some ca) :
    (∃ a : Action, Member a model.actions ∧ a.name = name ∧
      compileAction model.variables model.constants a = some ca) ∧
    (∀ a : Action, Member a model.actions → a.name = name →
      compileAction model.variables model.constants a = some ca) :=
  (fun parts : countB (fun (a : Action) => decide (a.name = name)) model.actions = 1 ∧
      firstActionSlot model.actions name = some h =>
    (fun first : ∃ a : Action, Member a model.actions ∧ a.name = name ∧
        compileAction model.variables model.constants a = some ca =>
      And.intro first
        (fun (a : Action) (mem : Member a model.actions) (named : a.name = name) =>
          Exists.elim first (fun a0 facts =>
            Eq.mpr
              (congrArg (fun z => compileAction model.variables model.constants z = some ca)
                (countOneUnique (fun (x : Action) => decide (x.name = name)) model.actions parts.1
                  a a0 mem facts.1 (decideTrue a.name name named)
                  (decideTrue a0.name name facts.2.1)))
              facts.2.2)))
    (slotCompiled (compileAction model.variables model.constants) name model.actions
      cm.actions h ca hacts parts.2 hn))
  (actionSlotParts model.actions name h hs)

-- ===== 9d. the model's facts the rule's semantics reads =====

theorem certFindStep (e : ProgressRow) (rest : List ProgressRow) (t : List Nat) (b : Bool)
    (hb : rowEq e.row t = b) :
    certFind (e :: rest) t = @Bool.rec (fun _ => Option ProgressRow) (certFind rest t) (some e) b :=
  congrArg (fun z => @Bool.rec (fun _ => Option ProgressRow) (certFind rest t) (some e) z) hb

theorem certFindSound (t : List Nat) (cert : List ProgressRow) :
    ∀ e : ProgressRow, certFind cert t = some e → Member e cert ∧ e.row = t :=
  @List.rec ProgressRow
    (fun cert => ∀ e : ProgressRow, certFind cert t = some e → Member e cert ∧ e.row = t)
    (fun e h => False.elim (noneNeSome h))
    (fun hd tl ih e h =>
      Or.elim (boolCases (rowEq hd.row t))
        (fun ht =>
          Eq.mp
            (congrArg (fun z => Member z (hd :: tl) ∧ z.row = t)
              (someInj (Eq.trans (Eq.symm (certFindStep hd tl t true ht)) h)))
            (And.intro (Member.head tl) (rowEqSound hd.row t ht)))
        (fun hf =>
          (fun inner : Member e tl ∧ e.row = t => And.intro (Member.tail hd tl inner.1) inner.2)
          (ih e (Eq.trans (Eq.symm (certFindStep hd tl t false hf)) h))))
    cert

theorem succInFound (cert : List ProgressRow) (ok : List Nat → ProgressRow → Bool)
    (row : List Nat) (ca : CAction) (h : succIn (certFind cert) ok row ca = true) :
    ∃ e : ProgressRow, certFind cert (succRow row ca.upd row) = some e ∧
      ok (succRow row ca.upd row) e = true :=
  optionRecSome (certFind cert (succRow row ca.upd row))
    (fun e => ok (succRow row ca.upd row) e)
    (Eq.trans
      (Eq.symm (forceRowEq (succRow row ca.upd row) (fun t =>
        @Option.rec ProgressRow (fun _ => Bool) false (fun e => ok t e) (certFind cert t))))
      h)

theorem stepOkFound (cert : List ProgressRow) (ok : List Nat → ProgressRow → Bool)
    (row : List Nat) (acts : List CAction)
    (h : allB (stepOk (certFind cert) ok row) acts = true)
    (ca : CAction) (mem : Member ca acts) (guard : evalB row ca.guard = true) :
    ∃ e : ProgressRow, certFind cert (succRow row ca.upd row) = some e ∧
      ok (succRow row ca.upd row) e = true :=
  succInFound cert ok row ca
    (boolRecImp (evalB row ca.guard) (succIn (certFind cert) ok row ca)
      (allBSound (stepOk (certFind cert) ok row) acts h ca mem) guard)

theorem anyBSound {α : Type} (p : α → Bool) (xs : List α) :
    anyB p xs = true → ∃ x : α, Member x xs ∧ p x = true :=
  @List.rec α (fun xs => anyB p xs = true → ∃ x : α, Member x xs ∧ p x = true)
    (fun h => Bool.noConfusion h)
    (fun hd tl ih h =>
      Or.elim (orBCases (p hd) (anyB p tl) h)
        (fun here => @Exists.intro α (fun x => Member x (hd :: tl) ∧ p x = true) hd
          (And.intro (Member.head tl) here))
        (fun later => Exists.elim (ih later) (fun x facts =>
          @Exists.intro α (fun x => Member x (hd :: tl) ∧ p x = true) x
            (And.intro (Member.tail hd tl facts.1) facts.2))))
    xs

theorem mapOptSource {α β : Type} (f : α → Option β) (xs : List α) :
    ∀ ys : List β, mapOpt f xs = some ys →
      ∀ y : β, Member y ys → ∃ x : α, Member x xs ∧ f x = some y :=
  @List.rec α
    (fun xs => ∀ ys : List β, mapOpt f xs = some ys →
      ∀ y : β, Member y ys → ∃ x : α, Member x xs ∧ f x = some y)
    (fun ys h y mem =>
      False.elim (memberNilFalse (Eq.mp (congrArg (fun zs => Member y zs) (Eq.symm (someInj h))) mem)))
    (fun x0 rest ih ys h y mem =>
      Exists.elim (optionBindSome (f x0)
          (fun y0 => @Option.rec (List β) (fun _ => Option (List β)) none
            (fun ys' => some (y0 :: ys')) (mapOpt f rest)) ys h)
        (fun y0 f1 =>
          Exists.elim (optionMapSome (mapOpt f rest) (fun ys' => y0 :: ys') ys f1.2)
            (fun ys' f2 =>
              Or.elim (memberConsInv
                  (Eq.mp (congrArg (fun zs => Member y zs) (Eq.symm f2.2)) mem))
                (fun same => @Exists.intro α (fun x => Member x (x0 :: rest) ∧ f x = some y) x0
                  (And.intro (Member.head rest)
                    (Eq.trans f1.1 (congrArg some (Eq.symm same)))))
                (fun later => Exists.elim (ih ys' f2.1 y later) (fun x facts =>
                  @Exists.intro α (fun x => Member x (x0 :: rest) ∧ f x = some y) x
                    (And.intro (Member.tail x0 rest facts.1) facts.2))))))
    xs

-- a helper slot the rule accepted is the slot of a weakly fair name
theorem weakName (acts : List Action) (names : List String) (weak : List Nat) (h : Nat)
    (hw : mapOpt (actionSlot acts) names = some weak) (hm : natMem h weak = true) :
    ∃ name : String, Member name names ∧ actionSlot acts name = some h :=
  Exists.elim (anyBSound (fun m => Nat.beq h m) weak hm) (fun m facts =>
    Exists.elim (mapOptSource (actionSlot acts) names weak hw m facts.1) (fun name nf =>
      @Exists.intro String (fun name => Member name names ∧ actionSlot acts name = some h) name
        (And.intro nf.1
          (Eq.trans nf.2 (congrArg some (Eq.symm (natBeqSound h m facts.2)))))))

theorem compileDistinctSome (model : ScalarModel) (cm : CModel)
    (h : compileDistinct model = some cm) : compileModel model = some cm :=
  Or.elim (boolCases (distinctVars model.variables))
    (fun ht => Eq.trans
      (congrArg (fun b => @Bool.rec (fun _ => Option CModel) none (compileModel model) b)
        (Eq.symm ht)) h)
    (fun hf => False.elim (noneNeSome (Eq.trans
      (congrArg (fun b => @Bool.rec (fun _ => Option CModel) none (compileModel model) b)
        (Eq.symm hf)) h)))

-- REUSE: the body of consecutionOfCheck, for one action
theorem stepDenotes (model : ScalarModel) (a : Action) (ca : CAction)
    (hca : compileAction model.variables model.constants a = some ca)
    (row : List Nat) (s t : State) (den : ScalarRowDenotes model row s)
    (holds : ActionHolds model.asModel a s t) :
    evalB row ca.guard = true ∧ ScalarRowDenotes model (succRow row ca.upd row) t :=
  And.intro
    (guardSound model s row den.2 a.guard ca.guard
      (compileActionSound model.variables model.constants a ca hca).1 holds.1)
    (And.intro holds.2.1
      (succDenotes model a s t row den.2 holds model.variables (fun entry m => m) row ca.upd den.2
        (compileActionSound model.variables model.constants a ca hca).2))

-- REUSE: compileExact at the goal
theorem goalOfRow (model : ScalarModel) (goal : ScalarExpr) (g : CExpr)
    (hg : compileS model.variables model.constants goal Srt.bool = some g)
    (row : List Nat) (s : State) (den : ScalarRowDenotes model row s)
    (h : evalB row g = true) : GoalHolds model.asModel goal s :=
  Eq.mp (congrArg (fun z => Evaluates model.asModel [] s goal (Value.bool z)) h)
    (compileExact model s row den.2 goal Srt.bool g hg).derives


-- the first entry found for a row a state denotes: a certificate entry whose row the state denotes
theorem foundDenotes (model : ScalarModel) (cert : List ProgressRow) (t : List Nat)
    (e : ProgressRow) (found : certFind cert t = some e) (s : State)
    (den : ScalarRowDenotes model t s) : Member e cert ∧ ScalarRowDenotes model e.row s :=
  And.intro (certFindSound t cert e found).1
    (Eq.mpr (congrArg (fun z => ScalarRowDenotes model z s) (certFindSound t cert e found).2) den)


-- the name of the action at position h ("" past the end)
def slotName (acts : List Action) (h : Nat) : String :=
  @List.rec Action (fun _ => Nat → String) (fun _ => "")
    (fun a _ ih i => @Nat.rec (fun _ => String) a.name (fun j _ => ih j) i) acts h

-- the action at position h, as a relation: the helper a level names
def SlotAction (p : ScalarProgress) (h : Nat) (s t : State) : Prop :=
  NamedAction p.model.asModel (slotName p.model.actions h) s t

theorem slotNameFirst (name : String) (acts : List Action) :
    ∀ h : Nat, firstActionSlot acts name = some h → slotName acts h = name :=
  @List.rec Action (fun acts => ∀ h : Nat, firstActionSlot acts name = some h → slotName acts h = name)
    (fun h hs => False.elim (noneNeSome hs))
    (fun a rest ih h hs =>
      Or.elim (boolCases (decide (a.name = name)))
        (fun hd =>
          Eq.mpr (congrArg (fun z => slotName (a :: rest) z = name)
              (Eq.symm (someInj (Eq.trans (Eq.symm (firstSlotStep a rest name true hd)) hs))))
            (of_decide_eq_true hd))
        (fun hd =>
          Exists.elim (optionMapSome (firstActionSlot rest name) Nat.succ h
              (Eq.trans (Eq.symm (firstSlotStep a rest name false hd)) hs))
            (fun j f3 =>
              Eq.mpr (congrArg (fun z => slotName (a :: rest) z = name) (Eq.symm f3.2))
                (ih j f3.1))))
    acts

-- the compiled action at a position is the compilation of the action of that slot's name
theorem slotNameCompiled (f : Action → Option CAction) (acts : List Action) :
    ∀ (cacts : List CAction) (h : Nat) (ca : CAction),
      mapOpt f acts = some cacts → nthAction cacts h = some ca →
      ∃ a : Action, Member a acts ∧ a.name = slotName acts h ∧ f a = some ca :=
  @List.rec Action
    (fun acts => ∀ (cacts : List CAction) (h : Nat) (ca : CAction),
      mapOpt f acts = some cacts → nthAction cacts h = some ca →
      ∃ a : Action, Member a acts ∧ a.name = slotName acts h ∧ f a = some ca)
    (fun cacts h ca hm hn =>
      False.elim (noneNeSome (Eq.trans (congrArg (fun z => nthAction z h) (someInj hm)) hn)))
    (fun a rest ih cacts h ca hm hn =>
      Exists.elim (optionBindSome (f a)
          (fun y => @Option.rec (List CAction) (fun _ => Option (List CAction)) none
            (fun ys => some (y :: ys)) (mapOpt f rest)) cacts hm)
        (fun ca0 f1 =>
          Exists.elim (optionMapSome (mapOpt f rest) (fun ys => ca0 :: ys) cacts f1.2)
            (fun cacts' f2 =>
              @Nat.rec
                (fun h => nthAction (ca0 :: cacts') h = some ca →
                  ∃ a' : Action, Member a' (a :: rest) ∧ a'.name = slotName (a :: rest) h ∧ f a' = some ca)
                (fun hn0 => ⟨a, Member.head rest, rfl, Eq.trans f1.1 hn0⟩)
                (fun j _ hnj => Exists.elim (ih cacts' j ca f2.1 hnj) (fun x xf =>
                  ⟨x, Member.tail a rest xf.1, xf.2.1, xf.2.2⟩))
                h
                (Eq.mp (congrArg (fun z => nthAction z h = some ca) (Eq.symm f2.2)) hn))))
    acts

-- a name's first slot is a position of the compiled list
theorem slotExists (f : Action → Option CAction) (name : String) (acts : List Action) :
    ∀ (cacts : List CAction) (h : Nat), mapOpt f acts = some cacts →
      firstActionSlot acts name = some h → ∃ ca : CAction, nthAction cacts h = some ca :=
  @List.rec Action
    (fun acts => ∀ (cacts : List CAction) (h : Nat), mapOpt f acts = some cacts →
      firstActionSlot acts name = some h → ∃ ca : CAction, nthAction cacts h = some ca)
    (fun _ _ _ hs => False.elim (noneNeSome hs))
    (fun a rest ih cacts h hm hs =>
      Exists.elim (optionBindSome (f a)
          (fun y => @Option.rec (List CAction) (fun _ => Option (List CAction)) none
            (fun ys => some (y :: ys)) (mapOpt f rest)) cacts hm)
        (fun ca0 f1 =>
          Exists.elim (optionMapSome (mapOpt f rest) (fun ys => ca0 :: ys) cacts f1.2)
            (fun cacts' f2 =>
              Eq.mpr (congrArg (fun z => ∃ ca : CAction, nthAction z h = some ca) (Eq.symm f2.2))
                (Or.elim (boolCases (decide (a.name = name)))
                  (fun hd =>
                    Eq.mpr (congrArg (fun z => ∃ ca : CAction, nthAction (ca0 :: cacts') z = some ca)
                        (Eq.symm (someInj (Eq.trans (Eq.symm (firstSlotStep a rest name true hd)) hs))))
                      ⟨ca0, rfl⟩)
                  (fun hd =>
                    Exists.elim (optionMapSome (firstActionSlot rest name) Nat.succ h
                        (Eq.trans (Eq.symm (firstSlotStep a rest name false hd)) hs))
                      (fun j f3 =>
                        Eq.mpr (congrArg (fun z => ∃ ca : CAction, nthAction (ca0 :: cacts') z = some ca)
                            (Eq.symm f3.2))
                          (ih cacts' j f2.1 f3.1)))))))
    acts

-- a fair position is the slot of a fair name, and the slot's name is that name
theorem slotFair (acts : List Action) (names : List String) (slots : List Nat) (h : Nat)
    (hw : mapOpt (actionSlot acts) names = some slots) (hm : natMem h slots = true) :
    ∃ name : String, Member name names ∧ actionSlot acts name = some h ∧ slotName acts h = name :=
  Exists.elim (weakName acts names slots h hw hm) (fun name nf =>
    ⟨name, nf.1, nf.2, slotNameFirst name acts h (actionSlotParts acts name h nf.2).2⟩)

-- two canonical states with one row are one state
theorem coordAgree (s t : State) (vs : List StateVar) :
    ∀ row : List Nat, ScalarCoordinatesDenote s vs row → ScalarCoordinatesDenote t vs row →
      ∀ entry : StateVar, Member entry vs → s.scalar entry.name = t.scalar entry.name :=
  @List.rec StateVar
    (fun vs => ∀ row : List Nat, ScalarCoordinatesDenote s vs row → ScalarCoordinatesDenote t vs row →
      ∀ entry : StateVar, Member entry vs → s.scalar entry.name = t.scalar entry.name)
    (fun row _ _ entry m => False.elim (memberNilFalse m))
    (fun v rest ih row =>
      @List.rec Nat
        (fun row => ScalarCoordinatesDenote s (v :: rest) row → ScalarCoordinatesDenote t (v :: rest) row →
          ∀ entry : StateVar, Member entry (v :: rest) → s.scalar entry.name = t.scalar entry.name)
        (fun d1 _ => False.elim d1)
        (fun x xs _ d1 d2 entry m =>
          Or.elim (memberConsInv m)
            (fun same => Eq.mpr (congrArg (fun (z : StateVar) => s.scalar z.name = t.scalar z.name) same)
              (Eq.trans d1.1 (Eq.symm d2.1)))
            (fun later => ih xs d1.2 d2.2 entry later))
        row)
    vs

theorem stateEta (s : State) : State.mk s.scalar s.function = s :=
  @State.rec (fun s => State.mk s.scalar s.function = s) (fun _ _ => rfl) s

theorem rowState (model : ScalarModel) (row : List Nat) (s t : State)
    (ds : ScalarRowDenotes model row s) (dt : ScalarRowDenotes model row t) : s = t :=
  Eq.trans (Eq.symm (stateEta s))
    (Eq.trans
      (congrArg (fun f => State.mk f s.function)
        (funext (fun name => Or.elim (Classical.em (DeclaresScalar model.asModel name))
          (fun dec => Exists.elim dec (fun entry facts =>
            Eq.mpr (congrArg (fun z => s.scalar z = t.scalar z) (Eq.symm facts.2))
              (coordAgree s t model.variables row ds.2 dt.2 entry facts.1)))
          (fun und => Eq.trans (ds.1.1 name und) (Eq.symm (dt.1.1 name und))))))
      (Eq.trans
        (congrArg (fun f => State.mk t.scalar f)
          (funext (fun name => funext (fun value =>
            (fun none_ : ¬ DeclaresFunctionAt model.asModel name value =>
              Eq.trans (ds.1.2 name value none_) (Eq.symm (dt.1.2 name value none_)))
            (fun d => Exists.elim d (fun range facts =>
              Exists.elim facts.1 (fun entry f2 => memberNilFalse f2.1)))))))
        (stateEta t)))

theorem notBTrue (b : Bool) (h : notB b = true) : b = false :=
  @Bool.rec (fun b => notB b = true → b = false) (fun _ => rfl) (fun k => Bool.noConfusion k) b h

-- a guard that holds and a step that does not move the row: the successor is the row
theorem stillSame (row : List Nat) (ca : CAction) (guard : evalB row ca.guard = true)
    (h : movesRow row ca = false) : rowEq (succRow row ca.upd row) row = true :=
  @Bool.rec (fun b => notB b = false → b = true) (fun k => Bool.noConfusion k) (fun _ => rfl)
    (rowEq (succRow row ca.upd row) row)
    (Eq.trans (Eq.symm (congrArg (fun z => andB z (notB (rowEq (succRow row ca.upd row) row))) guard)) h)

theorem movesAtOf (cm : CModel) (h : Nat) (row : List Nat) (ca : CAction)
    (hn : nthAction cm.actions h = some ca) (hm : movesRow row ca = true) : movesAt cm h row = true :=
  Eq.trans (congrArg (fun o => @Option.rec CAction (fun _ => Bool) false (fun ca => movesRow row ca) o) hn) hm

-- a position that moves the row is an enabled helper
theorem enabledOfMoves (p : ScalarProgress) (cm : CModel)
    (hacts : mapOpt (compileAction p.model.variables p.model.constants) p.model.actions = some cm.actions)
    (h : Nat) (row : List Nat) (s : State) (den : ScalarRowDenotes p.model row s)
    (moves : movesAt cm h row = true) :
    _root_.Trust.Temporal.Enabled (SlotAction p h) s :=
  Exists.elim (optionRecSome (nthAction cm.actions h) (fun ca => movesRow row ca) moves) (fun ca f1 =>
    Exists.elim (slotNameCompiled (compileAction p.model.variables p.model.constants) p.model.actions
        cm.actions h ca hacts f1.1) (fun a af =>
      movesEnabled p.model a ca (slotName p.model.actions h) af.1 af.2.1 af.2.2 row s den f1.2))

-- the slot of a fair (so unique) name that cannot move the row is not enabled at its state
theorem notEnabledOfStill (model : ScalarModel) (cm : CModel)
    (hacts : mapOpt (compileAction model.variables model.constants) model.actions = some cm.actions)
    (name : String) (h : Nat) (hs : actionSlot model.actions name = some h)
    (row : List Nat) (s : State) (den : ScalarRowDenotes model row s)
    (still : movesAt cm h row = false) :
    ¬ _root_.Trust.Temporal.Enabled (NamedAction model.asModel name) s :=
  fun en => Exists.elim en (fun t ns => Exists.elim ns.1 (fun a af =>
    Exists.elim (slotExists (compileAction model.variables model.constants) name model.actions
        cm.actions h hacts (actionSlotParts model.actions name h hs).2) (fun ca hn =>
      (fun hca : compileAction model.variables model.constants a = some ca =>
        (fun sd : evalB row ca.guard = true ∧ ScalarRowDenotes model (succRow row ca.upd row) t =>
          ns.2 (rowState model row t s
            (Eq.mp (congrArg (fun z => ScalarRowDenotes model z t)
              (rowEqSound (succRow row ca.upd row) row
                (stillSame row ca sd.1
                  (Eq.trans (Eq.symm (congrArg (fun o =>
                    @Option.rec CAction (fun _ => Bool) false (fun ca => movesRow row ca) o) hn)) still))))
              sd.2)
            den))
        (stepDenotes model a ca hca row s t den af.2.2))
      ((namedSlot model cm hacts name h ca hs hn).2 a af.1 af.2.1))))

-- ===== 9e. what `progressRule = true` says =====

def ProgressFacts (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) : Prop :=
  compileModel p.model = some cm ∧
  compileS p.model.variables p.model.constants p.goal Srt.bool = some g ∧
  mapOpt (actionSlot p.model.actions) p.weak = some weak ∧
  mapOpt (actionSlot p.model.actions) p.strong = some strong ∧
  (∃ e : ProgressRow, certFind cert cm.init = some e) ∧
  allB (entryOk cm g weak strong (certFind cert)) cert = true

theorem compiledParts (cm : CModel) (g : CExpr) (weak strong : List Nat) (cert : List ProgressRow)
    (h : progressRows cm g weak strong (certFind cert) cert = true) :
    (∃ e : ProgressRow, certFind cert cm.init = some e) ∧
      allB (entryOk cm g weak strong (certFind cert)) cert = true :=
  (fun both =>
    And.intro
      (Exists.elim (optionRecSome (certFind cert cm.init) (fun _ => true) both.1)
        (fun e facts => @Exists.intro ProgressRow (fun e => certFind cert cm.init = some e) e facts.1))
      both.2)
  (boolRecAnd
    (@Option.rec ProgressRow (fun _ => Bool) false (fun _ => true) (certFind cert cm.init))
    (allB (entryOk cm g weak strong (certFind cert)) cert) h)

-- what `progressWith p body = true` says: the claim compiles, and `body`
-- accepted the compiled form
theorem progressWithParts (p : ScalarProgress) (body : CModel → CExpr → List Nat → List Nat → Bool)
    (h : progressWith p body = true) :
    ∃ cm : CModel, ∃ g : CExpr, ∃ weak : List Nat, ∃ strong : List Nat,
      compileDistinct p.model = some cm ∧
      compileS p.model.variables p.model.constants p.goal Srt.bool = some g ∧
      mapOpt (actionSlot p.model.actions) p.weak = some weak ∧
      mapOpt (actionSlot p.model.actions) p.strong = some strong ∧ body cm g weak strong = true :=
  Exists.elim
    (optionRecSome (compileDistinct p.model)
      (fun cm0 => @Option.rec CExpr (fun _ => Bool) false
        (fun g0 => @Option.rec (List Nat) (fun _ => Bool) false
          (fun weak0 => @Option.rec (List Nat) (fun _ => Bool) false
            (fun strong0 => forceCM cm0 (fun cm => forceCExpr g0 (fun g => forceRow weak0 (fun weak =>
              forceRow strong0 (fun strong => body cm g weak strong)))))
            (mapOpt (actionSlot p.model.actions) p.strong))
          (mapOpt (actionSlot p.model.actions) p.weak))
        (compileS p.model.variables p.model.constants p.goal Srt.bool))
      h)
    (fun cm f1 =>
      Exists.elim
        (optionRecSome (compileS p.model.variables p.model.constants p.goal Srt.bool)
          (fun g0 => @Option.rec (List Nat) (fun _ => Bool) false
            (fun weak0 => @Option.rec (List Nat) (fun _ => Bool) false
              (fun strong0 => forceCM cm (fun cm' => forceCExpr g0 (fun g => forceRow weak0 (fun weak =>
                forceRow strong0 (fun strong => body cm' g weak strong)))))
              (mapOpt (actionSlot p.model.actions) p.strong))
            (mapOpt (actionSlot p.model.actions) p.weak))
          f1.2)
        (fun g f2 =>
          Exists.elim
            (optionRecSome (mapOpt (actionSlot p.model.actions) p.weak)
              (fun weak0 => @Option.rec (List Nat) (fun _ => Bool) false
                (fun strong0 => forceCM cm (fun cm' => forceCExpr g (fun g' => forceRow weak0 (fun weak =>
                  forceRow strong0 (fun strong => body cm' g' weak strong)))))
                (mapOpt (actionSlot p.model.actions) p.strong))
              f2.2)
            (fun weak f3 =>
              Exists.elim
                (optionRecSome (mapOpt (actionSlot p.model.actions) p.strong)
                  (fun strong0 => forceCM cm (fun cm' => forceCExpr g (fun g' => forceRow weak (fun weak' =>
                    forceRow strong0 (fun strong => body cm' g' weak' strong)))))
                  f3.2)
                (fun strong f4 =>
                  ⟨cm, g, weak, strong, f1.1, f2.1, f3.1, f4.1,
                    Eq.trans
                      (Eq.symm (Eq.trans
                        (forceCMEq cm (fun cm' => forceCExpr g (fun g' => forceRow weak (fun weak' =>
                          forceRow strong (fun strong' => body cm' g' weak' strong')))))
                        (Eq.trans
                          (forceCExprEq g (fun g' => forceRow weak (fun weak' =>
                            forceRow strong (fun strong' => body cm g' weak' strong'))))
                          (Eq.trans
                            (forceRowEq weak (fun weak' => forceRow strong (fun strong' => body cm g weak' strong')))
                            (forceRowEq strong (fun strong' => body cm g weak strong'))))))
                      f4.2⟩))))

theorem progressParts (p : ScalarProgress) (cert : List ProgressRow)
    (h : progressRule p cert = true) :
    ∃ cm : CModel, ∃ g : CExpr, ∃ weak : List Nat, ∃ strong : List Nat,
      ProgressFacts p cert cm g weak strong :=
  Exists.elim (progressWithParts p
      (fun cm g weak strong => progressRows cm g weak strong (certFind cert) cert) h)
    (fun cm r1 => Exists.elim r1 (fun g r2 => Exists.elim r2 (fun weak r3 =>
      Exists.elim r3 (fun strong f =>
        ⟨cm, g, weak, strong, compileDistinctSome p.model cm f.1, f.2.1, f.2.2.1, f.2.2.2.1,
          compiledParts cm g weak strong cert f.2.2.2.2⟩))))

-- ===== 9f. the certificate's invariant and levels, and the premises of `levelsProgress` =====

-- the invariant: the state denotes a certificate row
def CertCovered (model : ScalarModel) (cert : List ProgressRow) (s : State) : Prop :=
  ∃ e : ProgressRow, Member e cert ∧ ScalarRowDenotes model e.row s

-- the levels of a state: those of the FIRST entry for the non-goal row it denotes
def CertLv (p : ScalarProgress) (g : CExpr) (cert : List ProgressRow) (s : State)
    (L : List ProgressLevel) : Prop :=
  ∃ row : List Nat, ∃ e : ProgressRow, ScalarRowDenotes p.model row s ∧
    certFind cert row = some e ∧ evalB row g = false ∧ e.levels = L

def sumLev (cert : List ProgressRow) : Nat :=
  @List.rec ProgressRow (fun _ => Nat) 0 (fun e _ ih => lenL e.levels + ih) cert

theorem sumLevMember (e : ProgressRow) (cert : List ProgressRow) (m : Member e cert) :
    lenL e.levels ≤ sumLev cert :=
  @Member.rec ProgressRow e (fun list _ => lenL e.levels ≤ sumLev list)
    (fun tail => Nat.le_add_right (lenL e.levels) (sumLev tail))
    (fun hd tail _ ih => Nat.le_trans ih
      (Eq.mp (congrArg (fun z => Nat.le (sumLev tail) z) (Nat.add_comm (sumLev tail) (lenL hd.levels)))
        (Nat.le_add_right (sumLev tail) (lenL hd.levels))))
    cert m

theorem certFindMember (e : ProgressRow) (cert : List ProgressRow) (m : Member e cert) :
    ∃ e' : ProgressRow, certFind cert e.row = some e' :=
  @Member.rec ProgressRow e (fun list _ => ∃ e' : ProgressRow, certFind list e.row = some e')
    (fun tail => ⟨e, certFindStep e tail e.row true (rowEqRefl e.row)⟩)
    (fun hd tail _ ih => Or.elim (boolCases (rowEq hd.row e.row))
      (fun ht => ⟨hd, certFindStep hd tail e.row true ht⟩)
      (fun hf => Exists.elim ih (fun e' found =>
        ⟨e', Eq.trans (certFindStep hd tail e.row false hf) found⟩)))
    cert m

theorem entryParts (cm : CModel) (g : CExpr) (weak strong : List Nat) (cert : List ProgressRow)
    (r : ProgressRow) (h : entryOk cm g weak strong (certFind cert) r = true)
    (ng : evalB r.row g = false) :
    levelsOk cm g weak strong (certFind cert) r.row r.levels = true ∧
      allB (stepOk (certFind cert) (anyStepB cm g r.levels) r.row) cm.actions = true :=
  boolRecAnd (levelsOk cm g weak strong (certFind cert) r.row r.levels)
    (allB (stepOk (certFind cert) (anyStepB cm g r.levels) r.row) cm.actions)
    (Eq.trans
      (congrArg (fun b => @Bool.rec (fun _ => Bool)
          (andB (levelsOk cm g weak strong (certFind cert) r.row r.levels)
            (allB (stepOk (certFind cert) (anyStepB cm g r.levels) r.row) cm.actions))
          (allB (stepOk (certFind cert) (fun (_ : List Nat) (_ : ProgressRow) => true) r.row) cm.actions) b)
        (Eq.symm ng))
      h)

theorem entryClosure (cm : CModel) (g : CExpr) (weak strong : List Nat) (cert : List ProgressRow)
    (r : ProgressRow) (h : entryOk cm g weak strong (certFind cert) r = true)
    (ca : CAction) (mem : Member ca cm.actions) (guard : evalB r.row ca.guard = true) :
    ∃ e : ProgressRow, certFind cert (succRow r.row ca.upd r.row) = some e :=
  Or.elim (boolCases (evalB r.row g))
    (fun tg =>
      Exists.elim
        (stepOkFound cert (fun (_ : List Nat) (_ : ProgressRow) => true) r.row cm.actions
          (Eq.trans
            (congrArg (fun b => @Bool.rec (fun _ => Bool)
                (andB (levelsOk cm g weak strong (certFind cert) r.row r.levels)
                  (allB (stepOk (certFind cert) (anyStepB cm g r.levels) r.row) cm.actions))
                (allB (stepOk (certFind cert) (fun (_ : List Nat) (_ : ProgressRow) => true) r.row) cm.actions) b)
              (Eq.symm tg))
            h)
          ca mem guard)
        (fun e facts => ⟨e, facts.1⟩))
    (fun ng =>
      Exists.elim
        (stepOkFound cert (anyStepB cm g r.levels) r.row cm.actions
          (entryParts cm g weak strong cert r h ng).2 ca mem guard)
        (fun e facts => ⟨e, facts.1⟩))

theorem walkShape (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (row : List Nat) (L : List ProgressLevel) :
    ∀ (ls : List ProgressLevel) (prev : ProgressLevel),
      levelsWalk cm g weak strong find row L ls prev = true →
      LevelsShape (fun l => innerOk cm strong row l = true)
        (fun l => lastOk cm g weak strong find row L l = true) (prev :: ls) :=
  fun ls => @List.rec ProgressLevel
    (fun ls => ∀ prev : ProgressLevel, levelsWalk cm g weak strong find row L ls prev = true →
      LevelsShape (fun l => innerOk cm strong row l = true)
        (fun l => lastOk cm g weak strong find row L l = true) (prev :: ls))
    (fun prev h => h)
    (fun x xs ih prev h =>
      (fun parts => ⟨parts.1, ih x parts.2⟩)
      (boolRecAnd (innerOk cm strong row prev) (levelsWalk cm g weak strong find row L xs x) h))
    ls

theorem levelsShapeOfOk (cm : CModel) (g : CExpr) (weak strong : List Nat)
    (find : List Nat → Option ProgressRow) (row : List Nat) (L : List ProgressLevel)
    (h : levelsOk cm g weak strong find row L = true) :
    LevelsShape (fun l => innerOk cm strong row l = true)
      (fun l => lastOk cm g weak strong find row L l = true) L :=
  @List.rec ProgressLevel
    (fun M => @List.rec ProgressLevel (fun _ => Bool) false
        (fun l ls _ => levelsWalk cm g weak strong find row L ls l) M = true →
      LevelsShape (fun l => innerOk cm strong row l = true)
        (fun l => lastOk cm g weak strong find row L l = true) M)
    (fun k => Bool.noConfusion k)
    (fun l ls _ k => walkShape cm g weak strong find row L ls l k)
    L h

theorem shapeMono (i1 l1 i2 l2 : ProgressLevel → Prop)
    (mi : ∀ l : ProgressLevel, i1 l → i2 l) (ml : ∀ l : ProgressLevel, l1 l → l2 l)
    (L : List ProgressLevel) : LevelsShape i1 l1 L → LevelsShape i2 l2 L :=
  @List.rec ProgressLevel (fun L => LevelsShape i1 l1 L → LevelsShape i2 l2 L)
    (fun h => h)
    (fun x xs ih => @List.rec ProgressLevel
      (fun xs => (LevelsShape i1 l1 xs → LevelsShape i2 l2 xs) →
        LevelsShape i1 l1 (x :: xs) → LevelsShape i2 l2 (x :: xs))
      (fun _ h => ml x h)
      (fun _ _ _ ih' h => ⟨mi x h.1, ih' h.2⟩)
      xs ih)
    L

theorem shapeLast (i l : ProgressLevel → Prop) (x : ProgressLevel) (L : List ProgressLevel) :
    LevelsShape i l L → LastIs x L → l x :=
  @List.rec ProgressLevel (fun L => LevelsShape i l L → LastIs x L → l x)
    (fun s _ => False.elim s)
    (fun y ys ih => @List.rec ProgressLevel
      (fun ys => (LevelsShape i l ys → LastIs x ys → l x) →
        LevelsShape i l (y :: ys) → LastIs x (y :: ys) → l x)
      (fun _ s e => Eq.mp (congrArg l e) s)
      (fun _ _ _ ih' s e => ih' s.2 e)
      ys ih)
    L

theorem wakesSound (cm : CModel) (t : List Nat) (en : Nat → Prop)
    (hen : ∀ h : Nat, movesAt cm h t = true → en h) :
    ∀ E L : List ProgressLevel, wakesB cm t E L = true → Wakes en E L :=
  fun E => @List.rec ProgressLevel
    (fun E => ∀ L : List ProgressLevel, wakesB cm t E L = true → Wakes en E L)
    (fun L k => Bool.noConfusion k)
    (fun e es ih L => @List.rec ProgressLevel
      (fun L => wakesB cm t (e :: es) L = true → Wakes en (e :: es) L)
      (fun k => Bool.noConfusion k)
      (fun l ls _ k =>
        (fun parts =>
          ⟨parts.1, Or.elim (orBCases (movesAt cm l.helper t) (wakesB cm t es ls) parts.2)
            (fun m => Or.inl (hen l.helper m))
            (fun w => Or.inr (ih ls w))⟩)
        (boolRecAnd (lvEq e l) (orB (movesAt cm l.helper t) (wakesB cm t es ls)) k))
      L)
    E

theorem coveredInit (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong) :
    ∀ s : State, Initial p.model.asModel s → CertCovered p.model cert s :=
  fun s init => Exists.elim facts.2.2.2.2.1 (fun e found =>
    (fun fd : Member e cert ∧ ScalarRowDenotes p.model e.row s =>
      @Exists.intro ProgressRow (fun e => Member e cert ∧ ScalarRowDenotes p.model e.row s) e fd)
    (foundDenotes p.model cert cm.init e found s
      (Eq.mpr
        (congrArg (fun z => ScalarRowDenotes p.model z s) (compileModelSound p.model cm facts.1).1)
        (And.intro init.1
          (initDenotes p.model s init p.model.variables
            (fun (entry : StateVar) (m : Member entry p.model.variables) => m))))))

theorem coveredStep (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong) :
    ∀ s t : State, CertCovered p.model cert s → Next p.model.asModel s t →
      CertCovered p.model cert t :=
  fun s t cov next =>
    Exists.elim cov (fun r rf =>
      Exists.elim next (fun a af =>
        Exists.elim
          (mapOptMember (compileAction p.model.variables p.model.constants) p.model.actions
            cm.actions (compileModelSound p.model cm facts.1).2.1 a af.1)
          (fun ca cf =>
            (fun sd : evalB r.row ca.guard = true ∧
                ScalarRowDenotes p.model (succRow r.row ca.upd r.row) t =>
              Exists.elim
                (entryClosure cm g weak strong cert r
                  (allBSound (entryOk cm g weak strong (certFind cert)) cert facts.2.2.2.2.2 r rf.1)
                  ca cf.1 sd.1)
                (fun e found =>
                  @Exists.intro ProgressRow
                    (fun e => Member e cert ∧ ScalarRowDenotes p.model e.row t) e
                    (foundDenotes p.model cert (succRow r.row ca.upd r.row) e found t sd.2)))
            (stepDenotes p.model a ca cf.2 r.row s t rf.2 af.2))))

theorem certClassify (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong)
    (s : State) (cov : CertCovered p.model cert s) :
    GoalHolds p.model.asModel p.goal s ∨ ∃ L : List ProgressLevel, CertLv p g cert s L :=
  Exists.elim cov (fun e ef => Exists.elim (certFindMember e cert ef.1) (fun e' found =>
    Or.elim (boolCases (evalB e.row g))
      (fun tg => Or.inl (goalOfRow p.model p.goal g facts.2.1 e.row s ef.2 tg))
      (fun ng => Or.inr ⟨e'.levels, e.row, e', ef.2, found, ng, rfl⟩)))

theorem certUnique (p : ScalarProgress) (g : CExpr) (cert : List ProgressRow) :
    ∀ (s : State) (L E : List ProgressLevel), CertLv p g cert s L → CertLv p g cert s E → L = E :=
  fun s L E h1 h2 => Exists.elim h1 (fun r1 x1 => Exists.elim x1 (fun e1 f1 =>
    Exists.elim h2 (fun r2 x2 => Exists.elim x2 (fun e2 f2 =>
      (fun same : r1 = r2 =>
        Eq.trans (Eq.symm f1.2.2.2)
          (Eq.trans
            (congrArg (fun (e : ProgressRow) => e.levels)
              (someInj (Eq.trans (Eq.symm f1.2.1)
                (Eq.mpr (congrArg (fun z => certFind cert z = some e2) same) f2.2.1))))
            f2.2.2.2))
      (denoteUnique s p.model.variables r1 r2 f1.1.2 f2.1.2)))))

theorem certBounded (p : ScalarProgress) (g : CExpr) (cert : List ProgressRow) :
    ∀ (s : State) (L : List ProgressLevel), CertLv p g cert s L → lenL L ≤ sumLev cert :=
  fun s L h => Exists.elim h (fun row x => Exists.elim x (fun e f =>
    Eq.mp (congrArg (fun z => lenL z ≤ sumLev cert) f.2.2.2)
      (sumLevMember e cert (certFindSound row cert e f.2.1).1)))

theorem slotWeakFair (p : ScalarProgress) (weak : List Nat)
    (hw : mapOpt (actionSlot p.model.actions) p.weak = some weak)
    (b : _root_.Trust.Temporal.Behavior State)
    (weakFair : ∀ name : String, Member name p.weak →
      _root_.Trust.Temporal.WeakFair (NamedAction p.model.asModel name) b)
    (h : Nat) (hm : natMem h weak = true) : _root_.Trust.Temporal.WeakFair (SlotAction p h) b :=
  Exists.elim (slotFair p.model.actions p.weak weak h hw hm) (fun name nf =>
    Eq.mpr (congrArg (fun z => _root_.Trust.Temporal.WeakFair (NamedAction p.model.asModel z) b) nf.2.2)
      (weakFair name nf.1))

theorem slotStrongFair (p : ScalarProgress) (strong : List Nat)
    (hs : mapOpt (actionSlot p.model.actions) p.strong = some strong)
    (b : _root_.Trust.Temporal.Behavior State)
    (strongFair : ∀ name : String, Member name p.strong →
      _root_.Trust.Temporal.StrongFair (NamedAction p.model.asModel name) b)
    (h : Nat) (hm : natMem h strong = true) : _root_.Trust.Temporal.StrongFair (SlotAction p h) b :=
  Exists.elim (slotFair p.model.actions p.strong strong h hs hm) (fun name nf =>
    Eq.mpr (congrArg (fun z => _root_.Trust.Temporal.StrongFair (NamedAction p.model.asModel z) b) nf.2.2)
      (strongFair name nf.1))

-- the helper of a last level is the slot of a fair name
theorem slotOfLast (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong) (h : Nat)
    (hm : orB (natMem h weak) (natMem h strong) = true) :
    ∃ name : String, actionSlot p.model.actions name = some h ∧ slotName p.model.actions h = name :=
  Or.elim (orBCases (natMem h weak) (natMem h strong) hm)
    (fun w => Exists.elim (slotFair p.model.actions p.weak weak h facts.2.2.1 w) (fun name nf =>
      ⟨name, nf.2.1, nf.2.2⟩))
    (fun st => Exists.elim (slotFair p.model.actions p.strong strong h facts.2.2.2.1 st) (fun name nf =>
      ⟨name, nf.2.1, nf.2.2⟩))

theorem certShape (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong)
    (b : _root_.Trust.Temporal.Behavior State)
    (weakFair : ∀ name : String, Member name p.weak →
      _root_.Trust.Temporal.WeakFair (NamedAction p.model.asModel name) b)
    (strongFair : ∀ name : String, Member name p.strong →
      _root_.Trust.Temporal.StrongFair (NamedAction p.model.asModel name) b) :
    ∀ (s : State) (L : List ProgressLevel), CertLv p g cert s L →
      LevelsShape
        (fun l => ¬ _root_.Trust.Temporal.Enabled (SlotAction p l.helper) s ∧
          _root_.Trust.Temporal.StrongFair (SlotAction p l.helper) b)
        (fun l => _root_.Trust.Temporal.Enabled (SlotAction p l.helper) s ∧
          (_root_.Trust.Temporal.WeakFair (SlotAction p l.helper) b ∨
            _root_.Trust.Temporal.StrongFair (SlotAction p l.helper) b))
        L :=
  fun s L lv => Exists.elim lv (fun row x => Exists.elim x (fun e ef =>
    (fun sound : Member e cert ∧ e.row = row =>
      (fun den : ScalarRowDenotes p.model e.row s =>
        Eq.mp
          (congrArg (fun Z => LevelsShape
              (fun l => ¬ _root_.Trust.Temporal.Enabled (SlotAction p l.helper) s ∧
                _root_.Trust.Temporal.StrongFair (SlotAction p l.helper) b)
              (fun l => _root_.Trust.Temporal.Enabled (SlotAction p l.helper) s ∧
                (_root_.Trust.Temporal.WeakFair (SlotAction p l.helper) b ∨
                  _root_.Trust.Temporal.StrongFair (SlotAction p l.helper) b))
              Z) ef.2.2.2)
          (shapeMono
            (fun l => innerOk cm strong e.row l = true)
            (fun l => lastOk cm g weak strong (certFind cert) e.row e.levels l = true)
            (fun l => ¬ _root_.Trust.Temporal.Enabled (SlotAction p l.helper) s ∧
              _root_.Trust.Temporal.StrongFair (SlotAction p l.helper) b)
            (fun l => _root_.Trust.Temporal.Enabled (SlotAction p l.helper) s ∧
              (_root_.Trust.Temporal.WeakFair (SlotAction p l.helper) b ∨
                _root_.Trust.Temporal.StrongFair (SlotAction p l.helper) b))
            (fun l hi =>
              (fun parts =>
                Exists.elim (slotFair p.model.actions p.strong strong l.helper facts.2.2.2.1 parts.1)
                  (fun name nf =>
                    ⟨Eq.mpr (congrArg (fun z => ¬ _root_.Trust.Temporal.Enabled
                          (NamedAction p.model.asModel z) s) nf.2.2)
                        (notEnabledOfStill p.model cm (compileModelSound p.model cm facts.1).2.1
                          name l.helper nf.2.1 e.row s den
                          (notBTrue (movesAt cm l.helper e.row) parts.2)),
                     slotStrongFair p strong facts.2.2.2.1 b strongFair l.helper parts.1⟩))
              (boolRecAnd (natMem l.helper strong) (notB (movesAt cm l.helper e.row)) hi))
            (fun l hl =>
              (fun parts =>
                ⟨Exists.elim
                    (optionRecSome (nthAction cm.actions l.helper)
                      (fun ca => andB (movesRow e.row ca)
                        (succIn (certFind cert) (helperStepB cm g e.levels) e.row ca)) parts.2)
                    (fun ca cf =>
                      enabledOfMoves p cm (compileModelSound p.model cm facts.1).2.1 l.helper e.row s den
                        (movesAtOf cm l.helper e.row ca cf.1
                          (boolRecAnd (movesRow e.row ca)
                            (succIn (certFind cert) (helperStepB cm g e.levels) e.row ca) cf.2).1)),
                 Or.elim (orBCases (natMem l.helper weak) (natMem l.helper strong) parts.1)
                   (fun w => Or.inl (slotWeakFair p weak facts.2.2.1 b weakFair l.helper w))
                   (fun st => Or.inr (slotStrongFair p strong facts.2.2.2.1 b strongFair l.helper st))⟩)
              (boolRecAnd (orB (natMem l.helper weak) (natMem l.helper strong))
                (@Option.rec CAction (fun _ => Bool) false
                  (fun ca => andB (movesRow e.row ca)
                    (succIn (certFind cert) (helperStepB cm g e.levels) e.row ca))
                  (nthAction cm.actions l.helper)) hl))
            e.levels
            (levelsShapeOfOk cm g weak strong (certFind cert) e.row e.levels
              (entryParts cm g weak strong cert e
                (allBSound (entryOk cm g weak strong (certFind cert)) cert facts.2.2.2.2.2 e sound.1)
                (Eq.mpr (congrArg (fun z => evalB z g = false) sound.2) ef.2.2.1)).1)))
      (Eq.mpr (congrArg (fun z => ScalarRowDenotes p.model z s) sound.2) ef.1))
    (certFindSound row cert e ef.2.1)))

-- what the helper's step reached, as the premise states it
theorem helperCases (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong)
    (t' : List Nat) (e' : ProgressRow) (found : certFind cert t' = some e')
    (t : State) (den : ScalarRowDenotes p.model t' t) (L : List ProgressLevel)
    (hs : helperStepB cm g L t' e' = true) :
    GoalHolds p.model.asModel p.goal t ∨ ∃ E : List ProgressLevel, CertLv p g cert t E ∧
      (lexDownB E L = true ∨
        Wakes (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t) E (dropLastL L)) :=
  Or.elim (boolCases (evalB t' g))
    (fun tg => Or.inl (goalOfRow p.model p.goal g facts.2.1 t' t den tg))
    (fun ng => Or.inr ⟨e'.levels, ⟨t', e', den, found, ng, rfl⟩,
      Or.elim (orBCases (lexDownB e'.levels L) (orB (evalB t' g) (wakesB cm t' e'.levels (dropLastL L))) hs)
        (fun down => Or.inl down)
        (fun rest => Or.elim (orBCases (evalB t' g) (wakesB cm t' e'.levels (dropLastL L)) rest)
          (fun tg => False.elim (Bool.noConfusion (Eq.trans (Eq.symm ng) tg)))
          (fun wk => Or.inr (wakesSound cm t' (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t)
            (fun h m => enabledOfMoves p cm (compileModelSound p.model cm facts.1).2.1 h t' t den m)
            e'.levels (dropLastL L) wk)))⟩)

-- what any step reached, as the premise states it
theorem anyCases (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong)
    (t' : List Nat) (e' : ProgressRow) (found : certFind cert t' = some e')
    (t : State) (den : ScalarRowDenotes p.model t' t) (L : List ProgressLevel)
    (hs : anyStepB cm g L t' e' = true) :
    GoalHolds p.model.asModel p.goal t ∨ ∃ E : List ProgressLevel, CertLv p g cert t E ∧
      (lexDownB E L = true ∨ prefixB L E = true ∨
        Wakes (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t) E L) :=
  Or.elim (boolCases (evalB t' g))
    (fun tg => Or.inl (goalOfRow p.model p.goal g facts.2.1 t' t den tg))
    (fun ng => Or.inr ⟨e'.levels, ⟨t', e', den, found, ng, rfl⟩,
      Or.elim (orBCases (lexDownB e'.levels L)
          (orB (prefixB L e'.levels) (orB (evalB t' g) (wakesB cm t' e'.levels L))) hs)
        (fun down => Or.inl down)
        (fun r1 => Or.elim (orBCases (prefixB L e'.levels) (orB (evalB t' g) (wakesB cm t' e'.levels L)) r1)
          (fun pre => Or.inr (Or.inl pre))
          (fun r2 => Or.elim (orBCases (evalB t' g) (wakesB cm t' e'.levels L) r2)
            (fun tg => False.elim (Bool.noConfusion (Eq.trans (Eq.symm ng) tg)))
            (fun wk => Or.inr (Or.inr (wakesSound cm t'
              (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t)
              (fun h m => enabledOfMoves p cm (compileModelSound p.model cm facts.1).2.1 h t' t den m)
              e'.levels L wk)))))⟩)

theorem certHelper (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong) :
    ∀ (s t : State) (L : List ProgressLevel) (l : ProgressLevel), CertLv p g cert s L → LastIs l L →
      _root_.Trust.Temporal.NonStuttering (SlotAction p l.helper) s t →
      GoalHolds p.model.asModel p.goal t ∨ ∃ E : List ProgressLevel, CertLv p g cert t E ∧
        (lexDownB E L = true ∨
          Wakes (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t) E (dropLastL L)) :=
  fun s t L l lv last ns => Exists.elim lv (fun row x => Exists.elim x (fun e ef =>
    (fun sound : Member e cert ∧ e.row = row =>
      (fun den : ScalarRowDenotes p.model e.row s =>
        (fun lastB : lastOk cm g weak strong (certFind cert) e.row e.levels l = true =>
          (fun lp =>
            Exists.elim
              (optionRecSome (nthAction cm.actions l.helper)
                (fun ca => andB (movesRow e.row ca)
                  (succIn (certFind cert) (helperStepB cm g e.levels) e.row ca)) lp.2)
              (fun ca cf =>
                (fun mv =>
                  Exists.elim (succInFound cert (helperStepB cm g e.levels) e.row ca mv.2) (fun e' sf =>
                    Exists.elim (slotOfLast p cert cm g weak strong facts l.helper lp.1) (fun name nf =>
                      Exists.elim ns.1 (fun a af =>
                        (fun hca : compileAction p.model.variables p.model.constants a = some ca =>
                          (fun sd : evalB e.row ca.guard = true ∧
                              ScalarRowDenotes p.model (succRow e.row ca.upd e.row) t =>
                            Eq.mp
                              (congrArg (fun Z => GoalHolds p.model.asModel p.goal t ∨
                                  ∃ E : List ProgressLevel, CertLv p g cert t E ∧
                                    (lexDownB E Z = true ∨
                                      Wakes (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t) E
                                        (dropLastL Z)))
                                ef.2.2.2)
                              (helperCases p cert cm g weak strong facts (succRow e.row ca.upd e.row) e'
                                sf.1 t sd.2 e.levels sf.2))
                          (stepDenotes p.model a ca hca e.row s t den af.2.2))
                        ((namedSlot p.model cm (compileModelSound p.model cm facts.1).2.1 name l.helper ca
                          nf.1 cf.1).2 a af.1 (Eq.trans af.2.1 nf.2))))))
                (boolRecAnd (movesRow e.row ca)
                  (succIn (certFind cert) (helperStepB cm g e.levels) e.row ca) cf.2)))
          (boolRecAnd (orB (natMem l.helper weak) (natMem l.helper strong))
            (@Option.rec CAction (fun _ => Bool) false
              (fun ca => andB (movesRow e.row ca)
                (succIn (certFind cert) (helperStepB cm g e.levels) e.row ca))
              (nthAction cm.actions l.helper)) lastB))
        (shapeLast
          (fun l => innerOk cm strong e.row l = true)
          (fun l => lastOk cm g weak strong (certFind cert) e.row e.levels l = true)
          l e.levels
          (levelsShapeOfOk cm g weak strong (certFind cert) e.row e.levels
            (entryParts cm g weak strong cert e
              (allBSound (entryOk cm g weak strong (certFind cert)) cert facts.2.2.2.2.2 e sound.1)
              (Eq.mpr (congrArg (fun z => evalB z g = false) sound.2) ef.2.2.1)).1)
          (Eq.mpr (congrArg (fun Z => LastIs l Z) ef.2.2.2) last)))
      (Eq.mpr (congrArg (fun z => ScalarRowDenotes p.model z s) sound.2) ef.1))
    (certFindSound row cert e ef.2.1)))

theorem certOther (p : ScalarProgress) (cert : List ProgressRow) (cm : CModel) (g : CExpr)
    (weak strong : List Nat) (facts : ProgressFacts p cert cm g weak strong) :
    ∀ (s t : State) (L : List ProgressLevel), CertLv p g cert s L → Next p.model.asModel s t →
      GoalHolds p.model.asModel p.goal t ∨ ∃ E : List ProgressLevel, CertLv p g cert t E ∧
        (lexDownB E L = true ∨ prefixB L E = true ∨
          Wakes (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t) E L) :=
  fun s t L lv next => Exists.elim lv (fun row x => Exists.elim x (fun e ef =>
    (fun sound : Member e cert ∧ e.row = row =>
      (fun den : ScalarRowDenotes p.model e.row s =>
        Exists.elim next (fun a af =>
          Exists.elim
            (mapOptMember (compileAction p.model.variables p.model.constants) p.model.actions
              cm.actions (compileModelSound p.model cm facts.1).2.1 a af.1)
            (fun ca cf =>
              (fun sd : evalB e.row ca.guard = true ∧
                  ScalarRowDenotes p.model (succRow e.row ca.upd e.row) t =>
                Exists.elim
                  (stepOkFound cert (anyStepB cm g e.levels) e.row cm.actions
                    (entryParts cm g weak strong cert e
                      (allBSound (entryOk cm g weak strong (certFind cert)) cert facts.2.2.2.2.2 e sound.1)
                      (Eq.mpr (congrArg (fun z => evalB z g = false) sound.2) ef.2.2.1)).2
                    ca cf.1 sd.1)
                  (fun e' sf =>
                    Eq.mp
                      (congrArg (fun Z => GoalHolds p.model.asModel p.goal t ∨
                          ∃ E : List ProgressLevel, CertLv p g cert t E ∧
                            (lexDownB E Z = true ∨ prefixB Z E = true ∨
                              Wakes (fun h => _root_.Trust.Temporal.Enabled (SlotAction p h) t) E Z))
                        ef.2.2.2)
                      (anyCases p cert cm g weak strong facts (succRow e.row ca.upd e.row) e'
                        sf.1 t sd.2 e.levels sf.2)))
              (stepDenotes p.model a ca cf.2 e.row s t den af.2))))
      (Eq.mpr (congrArg (fun z => ScalarRowDenotes p.model z s) sound.2) ef.1))
    (certFindSound row cert e ef.2.1)))

-- THE RULE IS SOUND: a certificate it accepts proves the claim
theorem progressOfRule (p : ScalarProgress) (cert : List ProgressRow)
    (h : progressRule p cert = true) : ScalarProgress.claim p :=
  Exists.elim (progressParts p cert h) (fun cm r1 => Exists.elim r1 (fun g r2 =>
    Exists.elim r2 (fun weak r3 => Exists.elim r3 (fun strong facts =>
      fun b runs weakFair strongFair =>
        levelsProgress (StateMachine p.model.asModel) b (GoalHolds p.model.asModel p.goal)
          (CertLv p g cert) (SlotAction p) (sumLev cert)
          (LevelRun.mk runs
            (fun n => certClassify p cert cm g weak strong facts (b n)
              (runInvariant (StateMachine p.model.asModel) (CertCovered p.model cert) b runs
                (coveredInit p cert cm g weak strong facts)
                (coveredStep p cert cm g weak strong facts) n))
            (certUnique p g cert)
            (certBounded p g cert)
            (certShape p cert cm g weak strong facts b weakFair strongFair)
            (certHelper p cert cm g weak strong facts)
            (certOther p cert cm g weak strong facts))))))

-- ===== 9g. the index answers as the rule's linear scan: `progressCheck` IS the rule =====
--
-- No invariant of the trie is needed.  An insert and a lookup with the same
-- hash take the same path, so the lookup ends in the tip the insert extended:
-- one more step of `certFind`.  A lookup for a different row reads the same
-- tips with the same answers, wherever the insert went.  So for ANY index,
-- looking up `r` after inserting `e` is `some e` if `e.row = r` and the old
-- lookup otherwise, which is `certFind` on the longer certificate.

theorem boolRecF {β : Type} (x y : β) (b : Bool) (hb : b = false) :
    @Bool.rec (fun _ => β) x y b = x :=
  congrArg (fun z => @Bool.rec (fun _ => β) x y z) hb

-- which of the four `pick4` takes depends on `m` alone
theorem pickCases (m : Nat) :
    (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c0) ∨
    (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c1) ∨
    (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c2) ∨
    (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c3) :=
  @Nat.rec
    (fun m =>
      (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c0) ∨
      (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c1) ∨
      (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c2) ∨
      (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 m = c3))
    (Or.inl (fun β c0 c1 c2 c3 => rfl))
    (fun m1 _ =>
      @Nat.rec
        (fun m1 =>
          (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ m1) = c0) ∨
          (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ m1) = c1) ∨
          (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ m1) = c2) ∨
          (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ m1) = c3))
        (Or.inr (Or.inl (fun β c0 c1 c2 c3 => rfl)))
        (fun m2 _ =>
          @Nat.rec
            (fun m2 =>
              (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ (Nat.succ m2)) = c0) ∨
              (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ (Nat.succ m2)) = c1) ∨
              (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ (Nat.succ m2)) = c2) ∨
              (∀ (β : Type) (c0 c1 c2 c3 : β), pick4 c0 c1 c2 c3 (Nat.succ (Nat.succ m2)) = c3))
            (Or.inr (Or.inr (Or.inl (fun β c0 c1 c2 c3 => rfl))))
            (fun _ _ => Or.inr (Or.inr (Or.inr (fun β c0 c1 c2 c3 => rfl))))
            m2)
        m1)
    m

theorem pickPush {β γ : Type} (k : β → γ) (c0 c1 c2 c3 : β) (m : Nat) :
    pick4 (k c0) (k c1) (k c2) (k c3) m = k (pick4 c0 c1 c2 c3 m) :=
  Or.elim (pickCases m)
    (fun s => Eq.trans (s γ (k c0) (k c1) (k c2) (k c3)) (congrArg k (Eq.symm (s β c0 c1 c2 c3))))
    (fun r1 => Or.elim r1
      (fun s => Eq.trans (s γ (k c0) (k c1) (k c2) (k c3)) (congrArg k (Eq.symm (s β c0 c1 c2 c3))))
      (fun r2 => Or.elim r2
        (fun s => Eq.trans (s γ (k c0) (k c1) (k c2) (k c3)) (congrArg k (Eq.symm (s β c0 c1 c2 c3))))
        (fun s => Eq.trans (s γ (k c0) (k c1) (k c2) (k c3)) (congrArg k (Eq.symm (s β c0 c1 c2 c3))))))

theorem pickSame {β : Type} (c : β) (m : Nat) : pick4 c c c c m = c :=
  Or.elim (pickCases m)
    (fun s => s β c c c c)
    (fun r1 => Or.elim r1 (fun s => s β c c c c)
      (fun r2 => Or.elim r2 (fun s => s β c c c c) (fun s => s β c c c c)))

-- a lookup at a fork, with the hash's quotient as written (not forced)
theorem pfindFork (r : List Nat) (a b c d : PIndex) (h : Nat) :
    pfindH r (PIndex.fork a b c d) h =
      pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
        (pfindH r d (Nat.div h 4)) (Nat.mod h 4) :=
  forceNatEq (Nat.div h 4) (fun q =>
    pick4 (pfindH r a q) (pfindH r b q) (pfindH r c q) (pfindH r d q) (Nat.mod h 4))

theorem pickCongr {β : Type} (x0 x1 x2 x3 y0 y1 y2 y3 : β) (m : Nat)
    (e0 : x0 = y0) (e1 : x1 = y1) (e2 : x2 = y2) (e3 : x3 = y3) :
    pick4 x0 x1 x2 x3 m = pick4 y0 y1 y2 y3 m :=
  Eq.trans (congrArg (fun z => pick4 z x1 x2 x3 m) e0)
    (Eq.trans (congrArg (fun z => pick4 y0 z x2 x3 m) e1)
      (Eq.trans (congrArg (fun z => pick4 y0 y1 z x3 m) e2)
        (congrArg (fun z => pick4 y0 y1 y2 z m) e3)))

-- four picks by one `m`, picked by `m` again: only the diagonal is read
theorem pickDiag {β : Type} (x0 x1 x2 x3 u1 u2 u3 v0 v2 v3 w0 w1 w3 z0 z1 z2 : β) (m : Nat) :
    pick4 (pick4 x0 u1 u2 u3 m) (pick4 v0 x1 v2 v3 m) (pick4 w0 w1 x2 w3 m) (pick4 z0 z1 z2 x3 m) m =
      pick4 x0 x1 x2 x3 m :=
  Or.elim (pickCases m)
    (fun s =>
      Eq.trans
        (s β (pick4 x0 u1 u2 u3 m) (pick4 v0 x1 v2 v3 m) (pick4 w0 w1 x2 w3 m) (pick4 z0 z1 z2 x3 m))
        (Eq.trans (s β x0 u1 u2 u3) (Eq.symm (s β x0 x1 x2 x3))))
    (fun r1 => Or.elim r1
      (fun s =>
        Eq.trans
          (s β (pick4 x0 u1 u2 u3 m) (pick4 v0 x1 v2 v3 m) (pick4 w0 w1 x2 w3 m) (pick4 z0 z1 z2 x3 m))
          (Eq.trans (s β v0 x1 v2 v3) (Eq.symm (s β x0 x1 x2 x3))))
      (fun r2 => Or.elim r2
        (fun s =>
          Eq.trans
            (s β (pick4 x0 u1 u2 u3 m) (pick4 v0 x1 v2 v3 m) (pick4 w0 w1 x2 w3 m) (pick4 z0 z1 z2 x3 m))
            (Eq.trans (s β w0 w1 x2 w3) (Eq.symm (s β x0 x1 x2 x3))))
        (fun s =>
          Eq.trans
            (s β (pick4 x0 u1 u2 u3 m) (pick4 v0 x1 v2 v3 m) (pick4 w0 w1 x2 w3 m) (pick4 z0 z1 z2 x3 m))
            (Eq.trans (s β z0 z1 z2 x3) (Eq.symm (s β x0 x1 x2 x3))))))

-- a lookup in the index after an insert at a fork: the lookup in each of the four candidates
theorem pfindInsertFork (e : ProgressRow) (r : List Nat) (a b c d : PIndex) (h h2 : Nat) :
    pfindH r (pinsertH e (PIndex.fork a b c d) h) h2 =
      pick4 (pfindH r (PIndex.fork (pinsertH e a (Nat.div h 4)) b c d) h2)
        (pfindH r (PIndex.fork a (pinsertH e b (Nat.div h 4)) c d) h2)
        (pfindH r (PIndex.fork a b (pinsertH e c (Nat.div h 4)) d) h2)
        (pfindH r (PIndex.fork a b c (pinsertH e d (Nat.div h 4))) h2) (Nat.mod h 4) :=
  Eq.symm
    (pickPush (fun z => pfindH r z h2)
      (PIndex.fork (pinsertH e a (Nat.div h 4)) b c d) (PIndex.fork a (pinsertH e b (Nat.div h 4)) c d)
      (PIndex.fork a b (pinsertH e c (Nat.div h 4)) d) (PIndex.fork a b c (pinsertH e d (Nat.div h 4)))
      (Nat.mod h 4))

-- at a tip the insert is the new head of the bucket
theorem pfindInsertSameTip (e : ProgressRow) (r : List Nat) (bucket : List ProgressRow) (h : Nat) :
    pfindH r (pinsertH e (PIndex.tip bucket) h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r (PIndex.tip bucket) h) (some e) (rowEq e.row r) :=
  rfl
-- an insert and a lookup on ONE hash: one more step of `certFind`.  The
-- fork case goes in steps: the lookup after an insert at a fork, by `m` ...
theorem pfindInsertForkPicks (e : ProgressRow) (r : List Nat) (a b c d : PIndex) (h : Nat) :
    pfindH r (pinsertH e (PIndex.fork a b c d) h) h =
      pick4 (pick4 (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4)) (pfindH r b (Nat.div h 4))
              (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
              (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4))
              (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
              (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4)) (Nat.mod h 4))
            (Nat.mod h 4) :=
      Eq.trans (pfindInsertFork e r a b c d h h)
          (pickCongr
            (pfindH r (PIndex.fork (pinsertH e a (Nat.div h 4)) b c d) h)
            (pfindH r (PIndex.fork a (pinsertH e b (Nat.div h 4)) c d) h)
            (pfindH r (PIndex.fork a b (pinsertH e c (Nat.div h 4)) d) h)
            (pfindH r (PIndex.fork a b c (pinsertH e d (Nat.div h 4))) h)
            (pick4 (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4)) (pfindH r b (Nat.div h 4))
              (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
              (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4))
              (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
              (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4)) (Nat.mod h 4))
            (Nat.mod h 4)
            (pfindFork r (pinsertH e a (Nat.div h 4)) b c d h)
            (pfindFork r a (pinsertH e b (Nat.div h 4)) c d h)
            (pfindFork r a b (pinsertH e c (Nat.div h 4)) d h)
            (pfindFork r a b c (pinsertH e d (Nat.div h 4)) h))

-- ... of which only the diagonal is read ...
theorem pfindInsertDiag (e : ProgressRow) (r : List Nat) (a b c d : PIndex) (h : Nat) :
    pick4 (pick4 (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4)) (pfindH r b (Nat.div h 4))
              (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
              (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4))
              (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4)) (pfindH r d (Nat.div h 4)) (Nat.mod h 4))
            (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
              (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4)) (Nat.mod h 4))
            (Nat.mod h 4) =
    pick4 (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4)) (Nat.mod h 4) :=
            pickDiag
              (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4))
              (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4))
              (pfindH r a (Nat.div h 4)) (pfindH r c (Nat.div h 4)) (pfindH r d (Nat.div h 4))
              (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r d (Nat.div h 4))
              (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
              (Nat.mod h 4)

-- ... each a lookup one level down (the hypotheses) ...
theorem pfindInsertBelow (e : ProgressRow) (r : List Nat) (a b c d : PIndex) (h : Nat)
    (ia : ∀ h : Nat, pfindH r (pinsertH e a h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r a h) (some e) (rowEq e.row r))
    (ib : ∀ h : Nat, pfindH r (pinsertH e b h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r b h) (some e) (rowEq e.row r))
    (ic : ∀ h : Nat, pfindH r (pinsertH e c h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r c h) (some e) (rowEq e.row r))
    (id : ∀ h : Nat, pfindH r (pinsertH e d h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r d h) (some e) (rowEq e.row r)) :
    pick4 (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4))
              (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4)) (Nat.mod h 4) =
    pick4 (@Bool.rec (fun _ => Option ProgressRow) (pfindH r a (Nat.div h 4)) (some e) (rowEq e.row r))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r b (Nat.div h 4)) (some e) (rowEq e.row r))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r c (Nat.div h 4)) (some e) (rowEq e.row r))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r d (Nat.div h 4)) (some e) (rowEq e.row r))
                (Nat.mod h 4) :=
              pickCongr
                (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h 4))
                (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h 4))
                (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h 4))
                (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h 4))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r a (Nat.div h 4)) (some e) (rowEq e.row r))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r b (Nat.div h 4)) (some e) (rowEq e.row r))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r c (Nat.div h 4)) (some e) (rowEq e.row r))
                (@Bool.rec (fun _ => Option ProgressRow) (pfindH r d (Nat.div h 4)) (some e) (rowEq e.row r))
                (Nat.mod h 4)
                (ia (Nat.div h 4)) (ib (Nat.div h 4)) (ic (Nat.div h 4)) (id (Nat.div h 4))
-- ... the step of `certFind` taken out of the pick ...
theorem pickPushInsert (e : ProgressRow) (r : List Nat) (a b c d : PIndex) (h : Nat) :
    pick4 (@Bool.rec (fun _ => Option ProgressRow) (pfindH r a (Nat.div h 4)) (some e) (rowEq e.row r))
      (@Bool.rec (fun _ => Option ProgressRow) (pfindH r b (Nat.div h 4)) (some e) (rowEq e.row r))
      (@Bool.rec (fun _ => Option ProgressRow) (pfindH r c (Nat.div h 4)) (some e) (rowEq e.row r))
      (@Bool.rec (fun _ => Option ProgressRow) (pfindH r d (Nat.div h 4)) (some e) (rowEq e.row r))
      (Nat.mod h 4) =
    @Bool.rec (fun _ => Option ProgressRow)
      (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
        (pfindH r d (Nat.div h 4)) (Nat.mod h 4)) (some e) (rowEq e.row r) :=
  pickPush
    (fun z => @Bool.rec (fun _ => Option ProgressRow) z (some e) (rowEq e.row r))
    (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
    (pfindH r d (Nat.div h 4)) (Nat.mod h 4)
-- ... and the pick folded back into the lookup at the fork
theorem pfindForkBack (e : ProgressRow) (r : List Nat) (a b c d : PIndex) (h : Nat) :
    @Bool.rec (fun _ => Option ProgressRow)
      (pick4 (pfindH r a (Nat.div h 4)) (pfindH r b (Nat.div h 4)) (pfindH r c (Nat.div h 4))
        (pfindH r d (Nat.div h 4)) (Nat.mod h 4)) (some e) (rowEq e.row r) =
    @Bool.rec (fun _ => Option ProgressRow) (pfindH r (PIndex.fork a b c d) h) (some e) (rowEq e.row r) :=
  congrArg (fun z => @Bool.rec (fun _ => Option ProgressRow) z (some e) (rowEq e.row r))
    (Eq.symm (pfindFork r a b c d h))

-- the fork case, from the four below it (stated as lemmas: the in-process
-- elaborator does not take this chain inline under `PIndex.rec`)
theorem pfindInsertSameFork (e : ProgressRow) (r : List Nat) (a b c d : PIndex)
    (ia : ∀ h : Nat, pfindH r (pinsertH e a h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r a h) (some e) (rowEq e.row r))
    (ib : ∀ h : Nat, pfindH r (pinsertH e b h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r b h) (some e) (rowEq e.row r))
    (ic : ∀ h : Nat, pfindH r (pinsertH e c h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r c h) (some e) (rowEq e.row r))
    (id : ∀ h : Nat, pfindH r (pinsertH e d h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r d h) (some e) (rowEq e.row r)) (h : Nat) :
    pfindH r (pinsertH e (PIndex.fork a b c d) h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r (PIndex.fork a b c d) h) (some e) (rowEq e.row r) :=
  Eq.trans (pfindInsertForkPicks e r a b c d h)
    (Eq.trans (pfindInsertDiag e r a b c d h)
      (Eq.trans (pfindInsertBelow e r a b c d h ia ib ic id)
        (Eq.trans (pickPushInsert e r a b c d h) (pfindForkBack e r a b c d h))))

theorem pfindInsertSame (e : ProgressRow) (r : List Nat) (t : PIndex) :
    ∀ h : Nat, pfindH r (pinsertH e t h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r t h) (some e) (rowEq e.row r) :=
  @PIndex.rec
    (fun t => ∀ h : Nat, pfindH r (pinsertH e t h) h =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r t h) (some e) (rowEq e.row r))
    (fun bucket h => pfindInsertSameTip e r bucket h)
    (fun a b c d ia ib ic id h => pfindInsertSameFork e r a b c d ia ib ic id h)
    t

-- a lookup for any other row does not see the insert, whatever the two hashes
theorem pfindInsertOther (e : ProgressRow) (r : List Nat) (ne : rowEq e.row r = false) (t : PIndex) :
    ∀ h h2 : Nat, pfindH r (pinsertH e t h) h2 = pfindH r t h2 :=
  @PIndex.rec (fun t => ∀ h h2 : Nat, pfindH r (pinsertH e t h) h2 = pfindH r t h2)
    (fun bucket h h2 => boolRecF (certFind bucket r) (some e) (rowEq e.row r) ne)
    (fun a b c d ia ib ic id h h2 =>
      Eq.trans (pfindInsertFork e r a b c d h h2)
        (Eq.trans
          (pickCongr
            (pfindH r (PIndex.fork (pinsertH e a (Nat.div h 4)) b c d) h2)
            (pfindH r (PIndex.fork a (pinsertH e b (Nat.div h 4)) c d) h2)
            (pfindH r (PIndex.fork a b (pinsertH e c (Nat.div h 4)) d) h2)
            (pfindH r (PIndex.fork a b c (pinsertH e d (Nat.div h 4))) h2)
            (pfindH r (PIndex.fork a b c d) h2) (pfindH r (PIndex.fork a b c d) h2)
            (pfindH r (PIndex.fork a b c d) h2) (pfindH r (PIndex.fork a b c d) h2)
            (Nat.mod h 4)
            (Eq.trans (pfindFork r (pinsertH e a (Nat.div h 4)) b c d h2)
              (Eq.trans
                (pickCongr (pfindH r (pinsertH e a (Nat.div h 4)) (Nat.div h2 4)) (pfindH r b (Nat.div h2 4))
                  (pfindH r c (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (pfindH r a (Nat.div h2 4)) (pfindH r b (Nat.div h2 4)) (pfindH r c (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (Nat.mod h2 4) (ia (Nat.div h 4) (Nat.div h2 4)) rfl rfl rfl)
                (Eq.symm (pfindFork r a b c d h2))))
            (Eq.trans (pfindFork r a (pinsertH e b (Nat.div h 4)) c d h2)
              (Eq.trans
                (pickCongr (pfindH r a (Nat.div h2 4)) (pfindH r (pinsertH e b (Nat.div h 4)) (Nat.div h2 4))
                  (pfindH r c (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (pfindH r a (Nat.div h2 4)) (pfindH r b (Nat.div h2 4)) (pfindH r c (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (Nat.mod h2 4) rfl (ib (Nat.div h 4) (Nat.div h2 4)) rfl rfl)
                (Eq.symm (pfindFork r a b c d h2))))
            (Eq.trans (pfindFork r a b (pinsertH e c (Nat.div h 4)) d h2)
              (Eq.trans
                (pickCongr (pfindH r a (Nat.div h2 4)) (pfindH r b (Nat.div h2 4))
                  (pfindH r (pinsertH e c (Nat.div h 4)) (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (pfindH r a (Nat.div h2 4)) (pfindH r b (Nat.div h2 4)) (pfindH r c (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (Nat.mod h2 4) rfl rfl (ic (Nat.div h 4) (Nat.div h2 4)) rfl)
                (Eq.symm (pfindFork r a b c d h2))))
            (Eq.trans (pfindFork r a b c (pinsertH e d (Nat.div h 4)) h2)
              (Eq.trans
                (pickCongr (pfindH r a (Nat.div h2 4)) (pfindH r b (Nat.div h2 4))
                  (pfindH r c (Nat.div h2 4)) (pfindH r (pinsertH e d (Nat.div h 4)) (Nat.div h2 4))
                  (pfindH r a (Nat.div h2 4)) (pfindH r b (Nat.div h2 4)) (pfindH r c (Nat.div h2 4)) (pfindH r d (Nat.div h2 4))
                  (Nat.mod h2 4) rfl rfl rfl (id (Nat.div h 4) (Nat.div h2 4)))
                (Eq.symm (pfindFork r a b c d h2)))))
          (pickSame (pfindH r (PIndex.fork a b c d) h2) (Nat.mod h 4))))
    t

-- one insert is one step of `certFind`
theorem pfindInsert (e : ProgressRow) (r : List Nat) (t : PIndex) :
    pfindH r (pinsertH e t (rowHash e.row)) (rowHash r) =
      @Bool.rec (fun _ => Option ProgressRow) (pfindH r t (rowHash r)) (some e) (rowEq e.row r) :=
  Or.elim (boolCases (rowEq e.row r))
    (fun eq =>
      Eq.mp
        (congrArg
          (fun z => pfindH r (pinsertH e t (rowHash z)) (rowHash r) =
            @Bool.rec (fun _ => Option ProgressRow) (pfindH r t (rowHash r)) (some e) (rowEq e.row r))
          (Eq.symm (rowEqSound e.row r eq)))
        (pfindInsertSame e r t (rowHash r)))
    (fun ne =>
      Eq.trans (pfindInsertOther e r ne t (rowHash e.row) (rowHash r))
        (Eq.symm (boolRecF (pfindH r t (rowHash r)) (some e) (rowEq e.row r) ne)))

-- nothing is found in an empty index
theorem pfindEmpty (r : List Nat) (d : Nat) : ∀ h : Nat, pfindH r (pempty d) h = none :=
  @Nat.rec (fun d => ∀ h : Nat, pfindH r (pempty d) h = none)
    (fun h => rfl)
    (fun d ih h =>
      Eq.trans (pfindFork r (pempty d) (pempty d) (pempty d) (pempty d) h)
        (Eq.trans (pickSame (pfindH r (pempty d) (Nat.div h 4)) (Nat.mod h 4)) (ih (Nat.div h 4))))
    d

-- THE INDEX IS THE SCAN: the entry the index holds for a row is the first entry with that row
theorem pfindBuild (r : List Nat) (d : Nat) (cert : List ProgressRow) :
    pfindH r (pbuild cert (pempty d)) (rowHash r) = certFind cert r :=
  @List.rec ProgressRow
    (fun cert => pfindH r (pbuild cert (pempty d)) (rowHash r) = certFind cert r)
    (pfindEmpty r d (rowHash r))
    (fun e rest ih =>
      Eq.trans (pfindInsert e r (pbuild rest (pempty d)))
        (congrArg (fun z => @Bool.rec (fun _ => Option ProgressRow) z (some e) (rowEq e.row r)) ih))
    cert

theorem pfindKBuild (d : Nat) (cert : List ProgressRow) (r : List Nat) :
    pfindK (pbuild cert (pempty d)) r = certFind cert r :=
  Eq.trans (forceNatEq (rowHash r) (fun h => pfindH r (pbuild cert (pempty d)) h)) (pfindBuild r d cert)

-- the forced (value) forms equal the plain forms
theorem pinsertKEq {α : Type} (e : ProgressRow) (t : PIndex) :
    ∀ (h : Nat) (k : PIndex → α), pinsertK e t h k = k (pinsertH e t h) :=
  @PIndex.rec (fun t => ∀ (h : Nat) (k : PIndex → α), pinsertK e t h k = k (pinsertH e t h))
    (fun bucket h k => rfl)
    (fun a b c d ia ib ic id h k =>
      Eq.trans
        (forceNatEq (Nat.div h 4) (fun q =>
          pick4 (pinsertK e a q (fun x => k (PIndex.fork x b c d)))
            (pinsertK e b q (fun x => k (PIndex.fork a x c d)))
            (pinsertK e c q (fun x => k (PIndex.fork a b x d)))
            (pinsertK e d q (fun x => k (PIndex.fork a b c x))) (Nat.mod h 4)))
        (Eq.trans
          (pickCongr
            (pinsertK e a (Nat.div h 4) (fun x => k (PIndex.fork x b c d)))
            (pinsertK e b (Nat.div h 4) (fun x => k (PIndex.fork a x c d)))
            (pinsertK e c (Nat.div h 4) (fun x => k (PIndex.fork a b x d)))
            (pinsertK e d (Nat.div h 4) (fun x => k (PIndex.fork a b c x)))
            (k (PIndex.fork (pinsertH e a (Nat.div h 4)) b c d))
            (k (PIndex.fork a (pinsertH e b (Nat.div h 4)) c d))
            (k (PIndex.fork a b (pinsertH e c (Nat.div h 4)) d))
            (k (PIndex.fork a b c (pinsertH e d (Nat.div h 4))))
            (Nat.mod h 4)
            (ia (Nat.div h 4) (fun x => k (PIndex.fork x b c d)))
            (ib (Nat.div h 4) (fun x => k (PIndex.fork a x c d)))
            (ic (Nat.div h 4) (fun x => k (PIndex.fork a b x d)))
            (id (Nat.div h 4) (fun x => k (PIndex.fork a b c x))))
          (pickPush k (PIndex.fork (pinsertH e a (Nat.div h 4)) b c d)
            (PIndex.fork a (pinsertH e b (Nat.div h 4)) c d)
            (PIndex.fork a b (pinsertH e c (Nat.div h 4)) d)
            (PIndex.fork a b c (pinsertH e d (Nat.div h 4))) (Nat.mod h 4))))
    t

theorem pemptyKEq {α : Type} (d : Nat) : ∀ k : PIndex → α, pemptyK d k = k (pempty d) :=
  @Nat.rec (fun d => ∀ k : PIndex → α, pemptyK d k = k (pempty d))
    (fun _ => rfl)
    (fun d ih k => ih (fun t => k (PIndex.fork t t t t)))
    d

theorem pbuildKEq {α : Type} (t0 : PIndex) (cert : List ProgressRow) :
    ∀ k : PIndex → α, pbuildK cert t0 k = k (pbuild cert t0) :=
  @List.rec ProgressRow (fun cert => ∀ k : PIndex → α, pbuildK cert t0 k = k (pbuild cert t0))
    (fun _ => rfl)
    (fun e rest ih k =>
      Eq.trans (ih (fun t => forceNat (rowHash e.row) (fun h => pinsertK e t h k)))
        (Eq.trans (forceNatEq (rowHash e.row) (fun h => pinsertK e (pbuild rest t0) h k))
          (pinsertKEq e (pbuild rest t0) (rowHash e.row) k)))
    cert

theorem forceEntriesEq {α : Type} (cert : List ProgressRow) :
    ∀ k : List ProgressRow → α, forceEntries cert k = k cert :=
  @List.rec ProgressRow (fun cert => ∀ k : List ProgressRow → α, forceEntries cert k = k cert)
    (fun _ => rfl)
    (fun e rest ih k => ih (fun es => k (e :: es)))
    cert

-- whatever the count, a continuation that answers `x` for every count answers `x`
theorem lengthKConst {α : Type} (x : α) (k : Nat → α) (hk : ∀ n : Nat, k n = x)
    (cert : List ProgressRow) : ∀ acc : Nat, lengthK cert acc k = x :=
  @List.rec ProgressRow (fun cert => ∀ acc : Nat, lengthK cert acc k = x)
    (fun acc => hk acc)
    (fun _ rest ih acc =>
      Eq.trans (forceNatEq (Nat.succ acc) (fun n' => lengthK rest n' k)) (ih (Nat.succ acc)))
    cert

-- the indexed pass at any depth is the rule's pass
theorem progressAtDepth (cm : CModel) (g : CExpr) (weak strong : List Nat) (cert : List ProgressRow)
    (d : Nat) :
    pemptyK d (fun t0 => pbuildK cert t0 (fun t => progressRows cm g weak strong (pfindK t) cert)) =
      progressRows cm g weak strong (certFind cert) cert :=
  Eq.trans
    (pemptyKEq d (fun t0 => pbuildK cert t0 (fun t => progressRows cm g weak strong (pfindK t) cert)))
    (Eq.trans
      (pbuildKEq (pempty d) cert (fun t => progressRows cm g weak strong (pfindK t) cert))
      (congrArg (fun (find : List Nat → Option ProgressRow) => progressRows cm g weak strong find cert)
        (funext (fun r => pfindKBuild d cert r))))

theorem progressIndexedRule (cm : CModel) (g : CExpr) (weak strong : List Nat) (cert : List ProgressRow) :
    progressIndexed cm g weak strong cert = progressRows cm g weak strong (certFind cert) cert :=
  Eq.trans
    (forceEntriesEq cert (fun es => lengthK es 0 (fun n => forceNat (pdepth n) (fun d =>
      pemptyK d (fun t0 => pbuildK es t0 (fun t => progressRows cm g weak strong (pfindK t) es))))))
    (lengthKConst (progressRows cm g weak strong (certFind cert) cert)
      (fun n => forceNat (pdepth n) (fun d =>
        pemptyK d (fun t0 => pbuildK cert t0 (fun t => progressRows cm g weak strong (pfindK t) cert))))
      (fun n =>
        Eq.trans
          (forceNatEq (pdepth n) (fun d =>
            pemptyK d (fun t0 => pbuildK cert t0 (fun t => progressRows cm g weak strong (pfindK t) cert))))
          (progressAtDepth cm g weak strong cert (pdepth n)))
      cert 0)

-- EXACTNESS: the check answers exactly as the rule does, on every claim and every certificate
theorem progressCheckRule (p : ScalarProgress) (cert : List ProgressRow) :
    progressCheck p cert = progressRule p cert :=
  Eq.trans (boolRecId (progressWith p (fun cm g weak strong => progressIndexed cm g weak strong cert)))
    (congrArg (fun (body : CModel → CExpr → List Nat → List Nat → Bool) => progressWith p body)
      (funext (fun cm => funext (fun g => funext (fun weak => funext (fun strong =>
        progressIndexedRule cm g weak strong cert))))))

-- SOUNDNESS: a certificate the check accepts proves the claim
theorem progressOfCheck (p : ScalarProgress) (cert : List ProgressRow)
    (h : progressCheck p cert = true) : ScalarProgress.claim p :=
  progressOfRule p cert (Eq.trans (Eq.symm (progressCheckRule p cert)) h)

end FiniteModel
end Temporal
end Trust
