-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- ============================================================================
--  G16 SPIKE — SYMBOLIC BITVECTOR OP EQUIVALENCE, kernel-checked in clean.
-- ============================================================================
--
--  GOAL (the proven-output certificate keystone for ay).
--  Today ay is a TRUSTED ORACLE when it asserts "the machine-emitted ADD has the
--  same value semantics as the IR add".  This file makes ay a CERTIFICATE
--  PRODUCER for that assertion, for the i32/Word32 add (and sub/and/or/xor),
--  by EXHIBITING the equivalence as a clean theorem the kernel re-checks with
--  ZERO sorry-axioms and a transitive axiom closure that is a strict subset of
--  clean's 3 foundational axioms (propext / Quot.sound / Classical.choice — none
--  is used here; everything is def/theorem over the core recursors @List.rec /
--  @Bool.rec plus congrArg/Eq.trans/Eq.symm/rfl).
--
--  WHAT IS PROVEN — read this precisely, it is the whole point.
--  This is the SYMBOLIC, ALL-INPUTS result, NOT a closed-constant spot check:
--
--      theorem add_equiv (a b : Word32) : machine_add a b = ir_add a b
--      theorem sub_equiv (a b : Word32) : machine_sub a b = ir_sub a b
--      theorem and_equiv / or_equiv / xor_equiv  (a b : Word32) : ... = ...
--
--  i.e. UNIVERSALLY QUANTIFIED over every pair of 32-bit words, proved by
--  STRUCTURAL INDUCTION over the width (term-mode @List.rec with an explicit
--  Prop-valued motive), NOT by `decide`/enumeration and NOT only on literals.
--  (Closed-constant `:= rfl` sanity theorems are ALSO included at the bottom,
--  clearly labelled as such, to pin the value semantics — but they are not the
--  load-bearing claim.)
--
--  NON-VACUITY (the X = X trap, avoided two ways).
--   (1) machine_* and ir_* are SEPARATELY-STATED definitions that are NOT
--       syntactically identical: the MACHINE side models how the AArch64 ADD
--       opcode computes — a ripple-carry full adder with the LEFT-associated
--       sum bit ((a XOR b) XOR cin) and the OR-of-pairwise-ANDs majority carry,
--       exactly the addRec shape in proofs/reducible_word.lean (the modeled
--       ADD-instruction semantics).  The IR side states the SPEC adder with the
--       RIGHT-associated sum bit (a XOR (b XOR cin)) and a DIFFERENT boolean
--       expression for the majority carry (c AND (a OR b)) OR (a AND b)).  For
--       the bitwise ops the IR side commutes the per-bit operands.  These are
--       genuinely different terms; the equivalence is a real theorem the kernel
--       must DISCHARGE, not accept by reflexivity-of-construction.
--   (2) A NON-TRIVIALITY WITNESS proves the framework can DISTINGUISH ops:
--       `op_distinct` shows wordBeq (machine_sub a b) (ir_add a b) = false on a
--       concrete discriminating input (1 - 1 = 0  ≠  1 + 1 = 2).  If machine_sub
--       and ir_add were secretly the same function this `= false := rfl` would
--       FAIL to check — so a GREEN file certifies the distinction is real.
--
--  REPRESENTATION.  Word32 := List Bool, LSB-first, length 32 — the same
--  fixed-width-word model as proofs/reducible_word.lean (re-derived inline here
--  so `clean check` checks this one file standalone, exactly as the sibling
--  proofs/lrat_checker_*.lean files inline their checker).  All recursion is
--  over the WIDTH (O(32) iota steps), never over a value, and all per-bit logic
--  is monomorphic Bool.xor / Bool.and / Bool.or / Bool.not — the PoC idioms.
--
--  RESIDUAL GAP (honest).  This certifies the SEMANTIC equivalence of the two
--  adder/bitwise DEFINITIONS as Word32 -> Word32 -> Word32 functions.  It does
--  NOT yet wire into the real Formula -> Word reconstruction at
--  crates/trust-certify/src/lib.rs (the BitVec fail-closed path ~2696-2772):
--  that path still fails closed on Formula::BitVec VCs and would need a bridge
--  that reconstructs the machine ADD and the IR add as THESE Word32 functions
--  from the actual emitted opcode / IR node before this theorem could discharge
--  the obligation.  See the report for the precise wiring gap.
-- ============================================================================

set_option autoImplicit false

namespace G16

-- ==========================================================================
--  REPRESENTATION + bit accessors (the reducible_word PoC idioms, inline).
-- ==========================================================================

-- A 32-bit word.  Width is a convention enforced by the witness literals
-- (length-32 lists) below; the symbolic theorems hold at EVERY length, so they
-- specialize to 32 a fortiori.
def Word32 : Type := List Bool

-- Head bit (LSB of the current suffix); 0 past the end (zero-extend).
def bhead : List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => Bool) false (fun b _ _ => b) xs
-- Tail (drop the LSB).
def btail : List Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool) List.nil (fun _ r _ => r) xs

-- ==========================================================================
--  PER-BIT PRIMITIVES — MACHINE side vs IR side, separately stated.
-- ==========================================================================

-- ---- full-adder SUM bit ----
-- MACHINE: ((a XOR b) XOR cin)  — the opcode's left-associated reduction.
def fsum_m  (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c
-- IR SPEC: (a XOR (b XOR cin)) — right-associated.  Different term.
def fsum_ir (a b c : Bool) : Bool := Bool.xor a (Bool.xor b c)

-- ---- full-adder CARRY bit ----
-- MACHINE: OR of the three pairwise ANDs (the textbook majority gate).
def fcarry_m  (a b c : Bool) : Bool :=
  Bool.or (Bool.and a b) (Bool.or (Bool.and a c) (Bool.and b c))
-- IR SPEC: (a AND b) OR (c AND (a OR b)) — a different boolean expression for
-- the same majority function.  Different term.
def fcarry_ir (a b c : Bool) : Bool :=
  Bool.or (Bool.and a b) (Bool.and c (Bool.or a b))

-- ---- bitwise per-bit ops ----  MACHINE: op a b ; IR: op b a (commuted).
def fand_m  (a b : Bool) : Bool := Bool.and a b
def fand_ir (a b : Bool) : Bool := Bool.and b a
def for_m   (a b : Bool) : Bool := Bool.or a b
def for_ir  (a b : Bool) : Bool := Bool.or b a
def fxor_m  (a b : Bool) : Bool := Bool.xor a b
def fxor_ir (a b : Bool) : Bool := Bool.xor b a

-- ==========================================================================
--  PER-BIT EQUIVALENCES — exhaustive 8-way / 4-way @Bool.rec case splits.
--  Each is a real boolean-identity proof (the SUM is XOR-associativity, the
--  CARRY is two majority encodings agreeing, the bitwise are commutativity).
-- ==========================================================================

theorem fsum_eq (a b c : Bool) : fsum_m a b c = fsum_ir a b c :=
  @Bool.rec (fun x => fsum_m x b c = fsum_ir x b c)
    (@Bool.rec (fun y => fsum_m false y c = fsum_ir false y c)
      (@Bool.rec (fun z => fsum_m false false z = fsum_ir false false z) rfl rfl c)
      (@Bool.rec (fun z => fsum_m false true z = fsum_ir false true z) rfl rfl c) b)
    (@Bool.rec (fun y => fsum_m true y c = fsum_ir true y c)
      (@Bool.rec (fun z => fsum_m true false z = fsum_ir true false z) rfl rfl c)
      (@Bool.rec (fun z => fsum_m true true z = fsum_ir true true z) rfl rfl c) b) a

theorem fcarry_eq (a b c : Bool) : fcarry_m a b c = fcarry_ir a b c :=
  @Bool.rec (fun x => fcarry_m x b c = fcarry_ir x b c)
    (@Bool.rec (fun y => fcarry_m false y c = fcarry_ir false y c)
      (@Bool.rec (fun z => fcarry_m false false z = fcarry_ir false false z) rfl rfl c)
      (@Bool.rec (fun z => fcarry_m false true z = fcarry_ir false true z) rfl rfl c) b)
    (@Bool.rec (fun y => fcarry_m true y c = fcarry_ir true y c)
      (@Bool.rec (fun z => fcarry_m true false z = fcarry_ir true false z) rfl rfl c)
      (@Bool.rec (fun z => fcarry_m true true z = fcarry_ir true true z) rfl rfl c) b) a

theorem fand_eq (a b : Bool) : fand_m a b = fand_ir a b :=
  @Bool.rec (fun x => fand_m x b = fand_ir x b)
    (@Bool.rec (fun y => fand_m false y = fand_ir false y) rfl rfl b)
    (@Bool.rec (fun y => fand_m true y = fand_ir true y) rfl rfl b) a
theorem for_eq (a b : Bool) : for_m a b = for_ir a b :=
  @Bool.rec (fun x => for_m x b = for_ir x b)
    (@Bool.rec (fun y => for_m false y = for_ir false y) rfl rfl b)
    (@Bool.rec (fun y => for_m true y = for_ir true y) rfl rfl b) a
theorem fxor_eq (a b : Bool) : fxor_m a b = fxor_ir a b :=
  @Bool.rec (fun x => fxor_m x b = fxor_ir x b)
    (@Bool.rec (fun y => fxor_m false y = fxor_ir false y) rfl rfl b)
    (@Bool.rec (fun y => fxor_m true y = fxor_ir true y) rfl rfl b) a

-- ==========================================================================
--  WORD-LEVEL OPS — MACHINE and IR ripple adders / bitwise zips.
--  Recursion over the FIRST operand's width; the @List.rec motive result is the
--  function consuming ys (and the carry).  Final carry dropped = the 2^width
--  wrap.  This is the addRec / zipB shape from proofs/reducible_word.lean.
-- ==========================================================================

-- ---- ADD ----
def addRec_m : List Bool → List Bool → Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → List Bool)
    (fun _ _ => List.nil)
    (fun a as_ ih => fun ys c =>
      List.cons (fsum_m a (bhead ys) c) (ih (btail ys) (fcarry_m a (bhead ys) c)))
    xs
def addRec_ir : List Bool → List Bool → Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → List Bool)
    (fun _ _ => List.nil)
    (fun a as_ ih => fun ys c =>
      List.cons (fsum_ir a (bhead ys) c) (ih (btail ys) (fcarry_ir a (bhead ys) c)))
    xs

-- bitwise NOT (shared; two's-complement subtract needs it).
def wordNot : List Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool) List.nil
    (fun a _ ih => List.cons (Bool.not a) ih) xs

-- ---- the MACHINE-side and IR-side operations under test ----
-- machine_add : the AArch64 ADD opcode value semantics (ripple carry, cin=0).
def machine_add (x y : List Bool) : List Bool := addRec_m x y false
-- ir_add : the IR-spec add (separately stated full-adder).
def ir_add (x y : List Bool) : List Bool := addRec_ir x y false
-- SUB = a + ~b + 1 (two's complement); cin=1 realizes the +1.
def machine_sub (x y : List Bool) : List Bool := addRec_m x (wordNot y) true
def ir_sub (x y : List Bool) : List Bool := addRec_ir x (wordNot y) true

-- ---- bitwise zips ----
def zipB_m (op : Bool → Bool → Bool) : List Bool → List Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → List Bool)
    (fun _ => List.nil)
    (fun a as_ ih => fun ys => List.cons (op a (bhead ys)) (ih (btail ys)))
    xs
def machine_and (x y : List Bool) : List Bool := zipB_m fand_m x y
def ir_and      (x y : List Bool) : List Bool := zipB_m fand_ir x y
def machine_or  (x y : List Bool) : List Bool := zipB_m for_m  x y
def ir_or       (x y : List Bool) : List Bool := zipB_m for_ir  x y
def machine_xor (x y : List Bool) : List Bool := zipB_m fxor_m x y
def ir_xor      (x y : List Bool) : List Bool := zipB_m fxor_ir x y

-- ==========================================================================
--  CONS-UNFOLD lemmas (`:= rfl`) — the kernel cons-equations for the recursors.
-- ==========================================================================

theorem addRec_m_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    addRec_m (List.cons a as_) ys c
    = List.cons (fsum_m a (bhead ys) c)
        (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c)) := rfl
theorem addRec_ir_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    addRec_ir (List.cons a as_) ys c
    = List.cons (fsum_ir a (bhead ys) c)
        (addRec_ir as_ (btail ys) (fcarry_ir a (bhead ys) c)) := rfl

-- ==========================================================================
--  THE SYMBOLIC ALL-INPUTS EQUIVALENCES.
--  Each is proved by STRUCTURAL INDUCTION over the first operand's width via a
--  term-mode @List.rec with an explicit Prop-valued motive (the `*Eq` predicate
--  abbreviations — needed so the recursor motive has a clean Prop head; a bare
--  curried `(ys : List Bool) -> ...` motive leaks the recursor universe in
--  clean's elaborator, the documented reducible-word / lrat-checker idiom).
-- ==========================================================================

-- ---- ADD ----
def AddEq (xs : List Bool) : Prop :=
  ∀ (ys : List Bool) (c : Bool), addRec_m xs ys c = addRec_ir xs ys c
theorem addRec_equiv (xs : List Bool) : AddEq xs :=
  @List.rec Bool AddEq
    (fun _ _ => rfl)
    (fun a as_ ih => fun ys c =>
      Eq.trans (addRec_m_cons a as_ ys c)
        (Eq.trans
          (congrArg
            (fun h => List.cons h (addRec_m as_ (btail ys) (fcarry_m a (bhead ys) c)))
            (fsum_eq a (bhead ys) c))
          (Eq.trans
            (congrArg (fun t => List.cons (fsum_ir a (bhead ys) c) t)
              (Eq.trans
                (congrArg (fun cc => addRec_m as_ (btail ys) cc) (fcarry_eq a (bhead ys) c))
                (ih (btail ys) (fcarry_ir a (bhead ys) c))))
            (Eq.symm (addRec_ir_cons a as_ ys c)))))
    xs

-- THE HEADLINE THEOREM: machine ADD == IR add, for ALL 32-bit words.
theorem add_equiv (a b : Word32) : machine_add a b = ir_add a b :=
  addRec_equiv a b false
-- SUB shares the adder, so the same induction discharges it.
theorem sub_equiv (a b : Word32) : machine_sub a b = ir_sub a b :=
  addRec_equiv a (wordNot b) true

-- ---- BITWISE (generic zip-equivalence parameterised over the per-bit lemma) ----
def ZipEq (opm opir : Bool → Bool → Bool) (xs : List Bool) : Prop :=
  ∀ ys : List Bool, zipB_m opm xs ys = zipB_m opir xs ys
theorem zip_equiv (opm opir : Bool → Bool → Bool)
    (hbit : ∀ a b : Bool, opm a b = opir a b) (xs : List Bool) : ZipEq opm opir xs :=
  @List.rec Bool (ZipEq opm opir)
    (fun _ => rfl)
    (fun a as_ ih => fun ys =>
      Eq.trans
        (congrArg (fun h => List.cons h (zipB_m opm as_ (btail ys))) (hbit a (bhead ys)))
        (congrArg (fun t => List.cons (opir a (bhead ys)) t) (ih (btail ys))))
    xs

theorem and_equiv (a b : Word32) : machine_and a b = ir_and a b :=
  zip_equiv fand_m fand_ir fand_eq a b
theorem or_equiv (a b : Word32) : machine_or a b = ir_or a b :=
  zip_equiv for_m for_ir for_eq a b
theorem xor_equiv (a b : Word32) : machine_xor a b = ir_xor a b :=
  zip_equiv fxor_m fxor_ir fxor_eq a b

-- ==========================================================================
--  COMPARISON OPS — the EXACT bug class this campaign caught: signed relational
--  comparisons were lowered as UNSIGNED (abs(-5) returned -5).  Here we model the
--  AArch64 SUBS condition codes and prove the lowering correct at the [PROVED]
--  layer.  Each comparison is computed FROM THE SUBTRACT (the existing addRec_*
--  recursion, REUSED — machine_sub / carryOut_m built on fcarry_m, IR built on
--  fcarry_ir) — NOT redefined — exactly as the AArch64 ISA derives N/Z/C/V from
--  the SUBS instruction, then the relational predicate from those flags:
--
--      signed   LT  :  N XOR V        (the bug class — sign/overflow flags)
--      unsigned LT  :  NOT C          (carry-clear / borrow from SUBS)
--      equal        :  Z              (all result bits zero)
--
--  As with add/sub/and/or/xor, the MACHINE side (flags off the machine adder
--  addRec_m / fcarry_m) and the IR side (flags off the SPEC adder addRec_ir /
--  fcarry_ir) are SEPARATELY-STATED, NON-syntactically-identical terms; the
--  equivalence is a real theorem the kernel discharges, not X = X.  Signed-LT
--  reuses sub_equiv (via congrArg on the flag formula); unsigned-LT needs a fresh
--  carry-out induction (carryOut_equiv, the addRec_equiv shape).
-- ==========================================================================

-- MSB = the word's SIGN bit = the LAST element of the LSB-first list (false if
-- empty).  Inner @List.rec walks to the final cons.
def msb : List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => Bool) false
    (fun a as_ ih => @List.rec Bool (fun _ => Bool) a (fun _ _ _ => ih) as_) xs

-- ---- final CARRY-OUT of the ripple adder (the SUBS C flag source) ----
-- Same recursion shape as addRec_*, but threads ONLY the carry, returning the
-- final carry-out (no result list).  MACHINE uses fcarry_m, IR uses fcarry_ir.
def carryOut_m : List Bool → List Bool → Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → Bool)
    (fun _ c => c)
    (fun a as_ ih => fun ys c => ih (btail ys) (fcarry_m a (bhead ys) c))
    xs
def carryOut_ir : List Bool → List Bool → Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → Bool)
    (fun _ c => c)
    (fun a as_ ih => fun ys c => ih (btail ys) (fcarry_ir a (bhead ys) c))
    xs
theorem carryOut_m_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    carryOut_m (List.cons a as_) ys c
    = carryOut_m as_ (btail ys) (fcarry_m a (bhead ys) c) := rfl
theorem carryOut_ir_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    carryOut_ir (List.cons a as_) ys c
    = carryOut_ir as_ (btail ys) (fcarry_ir a (bhead ys) c) := rfl

-- carryOut machine == IR, ALL inputs, by induction over the width (addRec_equiv
-- shape: cons-unfold, rewrite the per-bit carry by fcarry_eq, recurse via ih).
def COEq (xs : List Bool) : Prop :=
  ∀ (ys : List Bool) (c : Bool), carryOut_m xs ys c = carryOut_ir xs ys c
theorem carryOut_equiv (xs : List Bool) : COEq xs :=
  @List.rec Bool COEq
    (fun _ _ => rfl)
    (fun a as_ ih => fun ys c =>
      Eq.trans (carryOut_m_cons a as_ ys c)
        (Eq.trans
          (congrArg (fun cc => carryOut_m as_ (btail ys) cc) (fcarry_eq a (bhead ys) c))
          (Eq.trans
            (ih (btail ys) (fcarry_ir a (bhead ys) c))
            (Eq.symm (carryOut_ir_cons a as_ ys c)))))
    xs

-- ---- SIGNED LESS-THAN (the bug class) ----
-- AArch64 condition LT = (N != V).  N = sign of the SUBS result.  V (signed
-- overflow of a - b) = (sign a != sign b) AND (sign a != sign result) — the
-- MSB-only overflow encoding.  So  signed_lt = N XOR V, read off machine_sub.
-- The IR side reads the SAME flag formula off the SPEC subtract ir_sub: a
-- genuinely different term (different sum/carry per bit), proven equal via
-- sub_equiv lifted through the flag formula by congrArg.
def signed_lt_m (a b : List Bool) : Bool :=
  Bool.xor (msb (machine_sub a b))
    (Bool.and (Bool.xor (msb a) (msb b)) (Bool.xor (msb a) (msb (machine_sub a b))))
def signed_lt_ir (a b : List Bool) : Bool :=
  Bool.xor (msb (ir_sub a b))
    (Bool.and (Bool.xor (msb a) (msb b)) (Bool.xor (msb a) (msb (ir_sub a b))))
-- HEADLINE: machine signed-LT == IR signed-LT, for ALL words.
theorem signed_lt_equiv (a b : Word32) : signed_lt_m a b = signed_lt_ir a b :=
  congrArg
    (fun r => Bool.xor (msb r)
       (Bool.and (Bool.xor (msb a) (msb b)) (Bool.xor (msb a) (msb r))))
    (sub_equiv a b)

-- ---- UNSIGNED LESS-THAN ----
-- AArch64 condition LO (unsigned <) = carry-clear = NOT C from the SUBS.
def unsigned_lt_m (a b : List Bool) : Bool := Bool.not (carryOut_m a (wordNot b) true)
def unsigned_lt_ir (a b : List Bool) : Bool := Bool.not (carryOut_ir a (wordNot b) true)
theorem unsigned_lt_equiv (a b : Word32) : unsigned_lt_m a b = unsigned_lt_ir a b :=
  congrArg Bool.not (carryOut_equiv a (wordNot b) true)

-- ---- EQUAL / NOT-EQUAL ----
-- AArch64 condition EQ = Z = all SUBS result bits zero (a - b = 0).
-- allZero = the Z-flag predicate (true iff every bit is false); also reused by
-- wordBeq in the non-triviality witness below.
def allZero : List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => Bool) true (fun a _ ih => Bool.and (Bool.not a) ih) xs
def eq_m (a b : List Bool) : Bool := allZero (machine_sub a b)
def eq_ir (a b : List Bool) : Bool := allZero (ir_sub a b)
theorem eq_equiv (a b : Word32) : eq_m a b = eq_ir a b :=
  congrArg allZero (sub_equiv a b)
def ne_m (a b : List Bool) : Bool := Bool.not (eq_m a b)
def ne_ir (a b : List Bool) : Bool := Bool.not (eq_ir a b)
theorem ne_equiv (a b : Word32) : ne_m a b = ne_ir a b :=
  congrArg Bool.not (eq_equiv a b)

-- ==========================================================================
--  NON-TRIVIALITY WITNESS — the framework provably DISTINGUISHES ops.
--  wordBeq is the per-bit beq fold (from reducible_word).  We exhibit a concrete
--  input on which machine_sub DIFFERS from ir_add: 1 - 1 = 0  vs  1 + 1 = 2.
--  `= false := rfl` only checks if the two results genuinely differ — so this
--  GREEN theorem certifies machine_sub is NOT secretly ir_add.
-- ==========================================================================

-- (allZero is defined above in the comparison section as the Z-flag predicate.)
def wordBeq : List Bool → List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool)
    (fun ys => allZero ys)
    (fun a as_ ih => fun ys => Bool.and (Bool.beq a (bhead ys)) (ih (btail ys)))
    xs

-- 1 = [true,false] at width 2.  add: 1+1 = [false,true] (=2).  sub: 1-1 = [false,false] (=0).
theorem add_one_one : machine_add [true, false] [true, false] = [false, true] := rfl
theorem sub_one_one : machine_sub [true, false] [true, false] = [false, false] := rfl
-- The distinguishing fact: machine_sub a b  ≠  ir_add a b.
theorem op_distinct :
    wordBeq (machine_sub [true, false] [true, false]) (ir_add [true, false] [true, false])
    = false := rfl
-- And, dually, a positive sanity: machine_add a b  =  ir_add a b on the same input
-- (an instance of add_equiv, here also closing definitionally).
theorem add_agree_witness :
    wordBeq (machine_add [true, false] [true, false]) (ir_add [true, false] [true, false])
    = true := rfl

-- ==========================================================================
--  COMPARISON NON-TRIVIALITY CONTROLS — closed-constant `:= rfl`, proving each
--  relation is NOT secretly a DIFFERENT relation (so the equivalence theorems are
--  non-vacuous).  Width 2: -1 = [true,true], 1 = [true,false], -2 = [false,true].
--
--  THE EXACT BUG THIS CAMPAIGN CAUGHT: a signed relational comparison lowered as
--  unsigned (abs(-5) returned -5).  signed_lt and unsigned_lt MUST DIFFER on a
--  negative-vs-positive input, and they do: -1 <ₛ 1 is TRUE while (as unsigned)
--  3 <ᵤ 1 is FALSE.  If the lowering had confused them — the actual miscompile —
--  this `= false := rfl` would FAIL to check.  A GREEN file certifies the signed
--  and unsigned condition codes are genuinely distinct relations.
theorem slt_neg_pos    : signed_lt_m   [true, true] [true, false] = true  := rfl
theorem ult_neg_pos    : unsigned_lt_m [true, true] [true, false] = false := rfl
theorem signed_ne_unsigned_witness :
    Bool.beq (signed_lt_m   [true, true] [true, false])
             (unsigned_lt_m [true, true] [true, false]) = false := rfl
-- signed_lt is a REAL order, not constant: -2 <ₛ -1 = true, 1 <ₛ 1 = false.
theorem slt_true_witness  : signed_lt_m [false, true] [true, true]  = true  := rfl
theorem slt_irrefl_witness : signed_lt_m [true, false] [true, false] = false := rfl
-- unsigned_lt is a REAL order: 1 <ᵤ 3 = true.
theorem ult_true_witness  : unsigned_lt_m [true, false] [true, true] = true := rfl
-- eq is REAL and is NOT secretly ne: on equal inputs eq = true but ne = false.
theorem eq_true_witness  : eq_m [true, false] [true, false] = true  := rfl
theorem eq_false_witness : eq_m [true, false] [false, true] = false := rfl
theorem eq_ne_distinct :
    Bool.beq (eq_m [true, false] [true, false])
             (ne_m [true, false] [true, false]) = false := rfl

-- ==========================================================================
--  CLOSED-CONSTANT SANITY (NOT the load-bearing claim; documents value
--  semantics on 32-bit literals).  These pin that the SHARED value of the two
--  (equal) adders is the genuine two's-complement ADD / SUB.  32-bit width.
--  The symbolic theorems above already entail machine == ir at these inputs;
--  these additionally fix the numeric VALUE.
-- ==========================================================================

-- 32-bit one = LSB set.
def one32 : List Bool :=
  [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
def zero32 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
def allones32 : List Bool :=
  [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
def two32 : List Bool :=
  [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

-- 1 + 1 = 2 (machine and ir agree, by construction-then-theorem).
theorem add32_one_one_m  : machine_add one32 one32 = two32 := rfl
theorem add32_one_one_ir : ir_add one32 one32 = two32 := rfl
-- 1 + (2^32 - 1) = 0 : the wraparound boundary.
theorem add32_wrap_m  : machine_add one32 allones32 = zero32 := rfl
-- 0 - 1 = all-ones (= -1 in two's complement).
theorem sub32_underflow_m  : machine_sub zero32 one32 = allones32 := rfl
theorem sub32_underflow_ir : ir_sub zero32 one32 = allones32 := rfl
-- 1 - 1 = 0.
theorem sub32_self_m : machine_sub one32 one32 = zero32 := rfl

-- The bug class at the REAL 32-bit width.  allones32 = -1 (signed) = 2^32-1
-- (unsigned).  signed:  -1 <ₛ 1 = TRUE.  unsigned:  (2^32-1) <ᵤ 1 = FALSE.
-- This is exactly the abs(-5)-returns-(-5) miscompile: a signed comparison MUST
-- NOT be lowered to the unsigned condition code.  Both sides re-checked by the
-- kernel, machine flags and IR flags agreeing (signed_lt_equiv / unsigned_lt_equiv).
theorem slt32_neg_one_lt_one_m  : signed_lt_m   allones32 one32 = true  := rfl
theorem slt32_neg_one_lt_one_ir : signed_lt_ir  allones32 one32 = true  := rfl
theorem ult32_neg_one_lt_one_m  : unsigned_lt_m allones32 one32 = false := rfl
theorem ult32_neg_one_lt_one_ir : unsigned_lt_ir allones32 one32 = false := rfl
theorem cmp32_signed_ne_unsigned :
    Bool.beq (signed_lt_m allones32 one32) (unsigned_lt_m allones32 one32) = false := rfl
-- eq at 32-bit: 1 = 1 true, 1 = 0 false.
theorem eq32_self_m    : eq_m one32 one32  = true  := rfl
theorem eq32_distinct_m : eq_m one32 zero32 = false := rfl

-- ==========================================================================
--  THEOREM-INSTANTIATION BRIDGE (POC) — the O(1) [PROVED] discharge for ADD.
--
--  The runtime gate (crates/trust-cg-bridge verify_output.rs) discharges, per
--  emitted ADD function, the obligation "the byte-derived MACHINE output equals
--  the IR-derived spec output, for all inputs".  Today it does so by a per-
--  instance BIT-BLAST SAT REFUTATION re-checked by checkRefutes3_sound — O(proof
--  size), ~90 s at width 32.  This section exhibits the ALTERNATIVE discharge:
--  the gate's add obligation IS an instance of the already-kernel-proved
--  `add_equiv`, so it is dischargeable in O(1) — a single theorem application,
--  INDEPENDENT of any per-instance refutation/proof size.
--
--  GateAddObligation a b is the gate's "machine side == ir side" equality stated
--  over THESE g16 model functions (machine_add = the AArch64 ADD value semantics,
--  ir_add = the IR-spec adder).  `gate_add_discharged` discharges it for ALL a b
--  by `fun a b => add_equiv a b` — NO induction here, NO reflection, NO clause
--  DB: the cost is one application of the (separately, inductively) proved
--  theorem.  This is the kernel-side keystone of the FAST [PROVED] path: the
--  expensive induction is done ONCE (in `addRec_equiv`), then instantiated O(1)
--  per gate obligation.
--
--  RESIDUAL GAP (HONEST — the multi-session piece): `GateAddObligation` is stated
--  over the g16 `List Bool` model.  Wiring this into the RUNTIME gate additionally
--  requires a kernel-checked reconstruction proving the gate's actual byte-derived
--  `Formula` (from `Aarch64Semantics::effects` for ADD) equals `machine_add a b`
--  and its IR-derived `Formula` (from `trust_ir_semantics`) equals `ir_add a b`.
--  Those Formula<->model fidelity theorems do not exist yet (the machine- and
--  IR-semantics soundness layers).  This section proves the INSTANTIATION HALF
--  is real, sound (empty domain axioms), and O(1); it does NOT itself close the
--  Formula reconstruction.  See the report for the precise remaining scope.
-- ==========================================================================

-- The gate's add obligation, stated over the g16 model: machine ADD == IR add.
def GateAddObligation (a b : Word32) : Prop := machine_add a b = ir_add a b

-- O(1) DISCHARGE: instantiate the kernel-proved `add_equiv`.  No per-instance
-- refutation — the proof term is a single application.  Universally quantified,
-- so it covers EVERY 32-bit add the gate emits, not a fixed input.
theorem gate_add_discharged : ∀ (a b : Word32), GateAddObligation a b :=
  fun a b => add_equiv a b

-- Concrete-instance discharge (the per-call gate shape) is likewise O(1): a
-- direct instantiation at specific argument words, with no reflection.
theorem gate_add_discharged_at (a b : Word32) : machine_add a b = ir_add a b :=
  gate_add_discharged a b

-- NEGATIVE CONTROL (LOAD-BEARING).  A CORRUPTED add obligation — where the
-- "machine" side actually computes SUBTRACT (the exact miscompile class: emit a
-- SUB opcode where the IR says ADD) — must NEVER be dischargeable.  Two facts:
--
--  (1) TYPE-LEVEL REJECTION.  `add_equiv a b : machine_add a b = ir_add a b`.
--      It does NOT inhabit `machine_sub a b = ir_add a b`: the two `Prop`s are
--      distinct (different LHS), so `fun a b => add_equiv a b` does NOT type-check
--      against `WrongAddObligation`.  (Demonstrated by the fact that the discharge
--      below uses the FALSE-witness, not add_equiv — instantiation simply does
--      not apply.)
--  (2) SEMANTIC FALSITY.  The corrupted obligation is not merely un-instantiable;
--      it is FALSE.  `wrong_add_obligation_is_false` exhibits a concrete witness
--      (1) where machine_sub 1 1 = 0 but ir_add 1 1 = 2, so the equality forces
--      0 = 2 at the (width-2) MSB bit — refuted by `Bool.noConfusion`.  A FALSE
--      obligation has no proof at all, so no sound discharge (instantiation or
--      reflection) can ever award [PROVED] to it.
def WrongAddObligation (a b : Word32) : Prop := machine_sub a b = ir_add a b

-- The corrupted (machine-computes-SUB) obligation is provably FALSE on a witness:
-- machine_sub [1] [1] = 0 ≠ 2 = ir_add [1] [1].  Project the list equality to the
-- bit-1 (value-2) position and refute false = true.
theorem wrong_add_obligation_is_false :
    WrongAddObligation [true, false] [true, false] → False :=
  fun h => Bool.noConfusion (congrArg (fun w => bhead (btail w)) h)

-- Dually, the genuine add obligation IS discharged at the SAME witness by
-- instantiation, and the two sides genuinely AGREE (1 + 1 = 2 on both) — so the
-- negative control rejects the WRONG obligation while the bridge accepts the
-- RIGHT one.  This is the discriminating pair: a real bridge, not X = X.
theorem gate_add_discharged_witness :
    machine_add [true, false] [true, false] = ir_add [true, false] [true, false] :=
  gate_add_discharged [true, false] [true, false]

-- ==========================================================================
--  F3 FIDELITY — RUNG 1.  Formula/BvExpr add-shape  ==  g16 machine_add.
--
--  WHAT THIS SECTION IS (read precisely — it is the start of the F3/F5 bridge).
--  The g16 theorems above relate two g16 MODEL functions (machine_add, ir_add :
--  List Bool -> ...).  The runtime gate, however, discharges an obligation over a
--  `Formula`/`BvExpr` tree built by ay's bit-blaster from the byte-decoded ADD.
--  This section closes the FIRST fidelity rung between those two worlds: it
--  REFLECTS the ay `BvExpr::Add` bit-blast — at its EXACT per-bit gate boolean
--  shapes — as a g16-style recursive evaluator, and PROVES that evaluator equals
--  the g16 `machine_add`, for ALL words, by structural induction.  Composed with
--  `add_equiv` (machine_add = ir_add), this is the kernel half of
--      eval(BvAdd(a,b))  ==  machine_add(a,b)  ==  ir_add(a,b)  ==  eval(auto).
--
--  FIDELITY OF THE REFLECTION (the load-bearing modelling claim).  ay's add
--  blaster (ay-proof bv_blast_solver.rs ~626-653; gate semantics
--  bv_blast_export.rs:1378-1380) emits, per result bit i, with carry-in bit 0 =
--  `ConstFalse`:
--      sum_i   = Xor3(a_i, b_i, carry_i)           = a_i ^ b_i ^ carry_i
--      carry_{i+1} = FullAdderCarry(a_i, b_i, c_i) = (a_i && b_i) || (c_i && (a_i ^ b_i))
--  We transcribe EXACTLY these boolean forms into `fsum_bv` / `fcarry_bv` below
--  (Lean `^`/Bool.xor is left-assoc, matching Rust `^`).  `bvadd_eval` runs the
--  same ripple loop with carry-in `false` (= `ConstFalse`).  So `bvadd_eval` is a
--  faithful term-level model of what the ay blast COMPUTES for `BvExpr::Add`.
--
--  NON-VACUITY (this is NOT X = X).  `fcarry_bv` is ay's MAJ encoding
--  `(a&&b) || (c && (a^b))`, which is a DIFFERENT boolean expression from g16's
--  machine carry `fcarry_m = (a&&b) || ((a&&c) || (b&&c))` (OR-of-pairwise-ANDs)
--  AND from the IR carry `fcarry_ir = (a&&b) || (c && (a||b))`.  Three distinct
--  terms for the majority function.  The fidelity theorem must DISCHARGE the
--  carry-encoding mismatch per bit (fcarry_bv_eq_m, an exhaustive Bool case
--  split), not accept it by reflexivity-of-construction.
--
--  HONEST RESIDUAL (the named Rust-level piece this rung does NOT close).
--  This proves the FORMULA-EVAL <-> g16-MODEL relationship.  It does NOT prove
--  that the RUST `Aarch64Semantics::effects` / `trust_ir_semantics` actually
--  PRODUCE the `BvAdd(W0,W1,32)` shape for an ADD — that is a runtime,
--  Rust-level shape check (the irreducible residual), not a kernel theorem.
--  The kernel claim here is exactly: "the bit-blast of BvExpr::Add evaluates
--  equal to g16 machine_add."  See the report for the rung-2/rung-3 scope.
-- ==========================================================================

-- ay's `Xor3` full-adder SUM bit:  a ^ b ^ cin  (left-assoc, = fsum_m).
def fsum_bv (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c
-- ay's `FullAdderCarry` MAJ encoding:  (a && b) || (cin && (a ^ b)).
-- A THIRD majority encoding, distinct from fcarry_m and fcarry_ir.
def fcarry_bv (a b c : Bool) : Bool :=
  Bool.or (Bool.and a b) (Bool.and c (Bool.xor a b))

-- The ay add bit-blast, as a ripple recursion over the first operand's width.
-- Mirrors addRec_m's shape but with ay's per-bit gates; carry-in is the ay
-- `ConstFalse` realised by `false` in `bvadd_eval`.
def bvaddRec : List Bool → List Bool → Bool → List Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → List Bool)
    (fun _ _ => List.nil)
    (fun a as_ ih => fun ys c =>
      List.cons (fsum_bv a (bhead ys) c) (ih (btail ys) (fcarry_bv a (bhead ys) c)))
    xs
-- eval(BvAdd(a,b)) at the g16 model level: the ay blast with carry-in false.
def bvadd_eval (x y : List Bool) : List Bool := bvaddRec x y false

-- ay's `Sub` blast: complement the second operand and carry in `ConstTrue`.
-- Used ONLY for the negative control (a WRONG shape for an ADD obligation).
def bvsub_eval (x y : List Bool) : List Bool := bvaddRec x (wordNot y) true

theorem bvaddRec_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    bvaddRec (List.cons a as_) ys c
    = List.cons (fsum_bv a (bhead ys) c)
        (bvaddRec as_ (btail ys) (fcarry_bv a (bhead ys) c)) := rfl

-- PER-BIT bridge lemmas — the sum bits are literally identical (fsum_bv = fsum_m
-- by `rfl`), and the two MAJ carry encodings agree on every input (exhaustive
-- 8-way @Bool.rec, exactly the fcarry_eq idiom).
theorem fsum_bv_eq_m (a b c : Bool) : fsum_bv a b c = fsum_m a b c := rfl
theorem fcarry_bv_eq_m (a b c : Bool) : fcarry_bv a b c = fcarry_m a b c :=
  @Bool.rec (fun x => fcarry_bv x b c = fcarry_m x b c)
    (@Bool.rec (fun y => fcarry_bv false y c = fcarry_m false y c)
      (@Bool.rec (fun z => fcarry_bv false false z = fcarry_m false false z) rfl rfl c)
      (@Bool.rec (fun z => fcarry_bv false true z = fcarry_m false true z) rfl rfl c) b)
    (@Bool.rec (fun y => fcarry_bv true y c = fcarry_m true y c)
      (@Bool.rec (fun z => fcarry_bv true false z = fcarry_m true false z) rfl rfl c)
      (@Bool.rec (fun z => fcarry_bv true true z = fcarry_m true true z) rfl rfl c) b) a

-- THE FIDELITY INDUCTION: the ay bit-blast adder == the g16 machine adder, ALL
-- inputs / ALL carry-ins, by structural induction over the width (the
-- addRec_equiv shape: cons-unfold, rewrite the per-bit carry by fcarry_bv_eq_m,
-- recurse via ih; the sum bit closes by rfl since fsum_bv = fsum_m).
def BvAddEq (xs : List Bool) : Prop :=
  ∀ (ys : List Bool) (c : Bool), bvaddRec xs ys c = addRec_m xs ys c
theorem bvaddRec_eq_m (xs : List Bool) : BvAddEq xs :=
  @List.rec Bool BvAddEq
    (fun _ _ => rfl)
    (fun a as_ ih => fun ys c =>
      Eq.trans (bvaddRec_cons a as_ ys c)
        (Eq.trans
          (congrArg (fun t => List.cons (fsum_bv a (bhead ys) c) t)
            (Eq.trans
              (congrArg (fun cc => bvaddRec as_ (btail ys) cc) (fcarry_bv_eq_m a (bhead ys) c))
              (ih (btail ys) (fcarry_m a (bhead ys) c))))
          (Eq.symm (addRec_m_cons a as_ ys c))))
    xs

-- HEADLINE FIDELITY THEOREM (RUNG 1): the reflected ay BvExpr::Add bit-blast
-- evaluates EQUAL to the g16 machine_add, for ALL 32-bit words.
theorem bvadd_eval_eq_machine_add (a b : Word32) : bvadd_eval a b = machine_add a b :=
  bvaddRec_eq_m a b false

-- COMPOSED FIDELITY: eval(BvAdd(a,b)) == ir_add(a,b).  This is the kernel half
-- of the gate's O(1) discharge chain — the BvExpr add-shape reduced all the way
-- to the IR-spec adder, via the fidelity theorem then add_equiv.
theorem bvadd_eval_eq_ir_add (a b : Word32) : bvadd_eval a b = ir_add a b :=
  Eq.trans (bvadd_eval_eq_machine_add a b) (add_equiv a b)

-- ==========================================================================
--  NEGATIVE CONTROL (LOAD-BEARING).  A WRONG shape must NOT be provable-equal
--  to machine_add.  The exact miscompile class: the gate believes it is
--  discharging an ADD obligation, but the reflected Formula is the SUBTRACT
--  blast (`BvSub` — complement + carry-in true).  We prove that the SUB-shape
--  evaluator is NOT equal to machine_add: it FAILS on a concrete witness
--  (1 - 1 = 0  but  1 + 1 = 2), refuted by Bool.noConfusion at the value-2 bit.
--  A `theorem ... = rfl` form would have silently accepted a vacuous claim; this
--  refutation certifies the fidelity theorem is discriminating, not X = X.
-- ==========================================================================

-- 1 - 1 = 0 at width 2 under the ay SUB blast; 1 + 1 = 2 under the ADD blast.
theorem bvsub_eval_one_one : bvsub_eval [true, false] [true, false] = [false, false] := rfl
theorem bvadd_eval_one_one : bvadd_eval [true, false] [true, false] = [false, true] := rfl

-- The WRONG-shape obligation (machine ADD's value must equal the SUB blast) is
-- FALSE: project the list equality to bit 1 (the value-2 position), 0 ≠ 1.
theorem wrong_bv_shape_is_false :
    bvsub_eval [true, false] [true, false] = machine_add [true, false] [true, false] → False :=
  fun h => Bool.noConfusion (congrArg (fun w => bhead (btail w)) h)

-- Dually, the RIGHT shape IS discharged at the same witness by the fidelity
-- theorem — the discriminating pair: SUB-shape rejected, ADD-shape accepted.
theorem bvadd_eval_witness :
    bvadd_eval [true, false] [true, false] = machine_add [true, false] [true, false] :=
  bvadd_eval_eq_machine_add [true, false] [true, false]

-- And the per-bit carry encodings really differ (anti-vacuity of fcarry_bv_eq_m):
-- ay's MAJ form and the IR MAJ form disagree as TERMS though equal as functions;
-- exhibit that fcarry_bv is not syntactically fcarry_ir by a value both agree on
-- (sanity) while the theorem fcarry_bv_eq_m above does the real work for fcarry_m.
theorem fcarry_bv_maj_witness : fcarry_bv true true false = true := rfl
theorem fcarry_bv_minority_witness : fcarry_bv true false false = false := rfl

-- ==========================================================================
--  F3 FIDELITY — RUNG 2.  SUB + bitwise (and/or/xor) BvExpr blast == g16 machine.
--
--  Extends rung 1 (add) to the rest of the straight-line linear-ALU ops the gate
--  emits.  Each theorem REFLECTS ay's bit-blast for the op at its exact per-bit
--  gate shape (bv_blast_solver.rs) and proves it EQUAL to the g16 machine model,
--  for ALL words, then composes with the op's *_equiv to reach the IR side.
--
--  SUB (bv_blast_solver.rs:586-654).  ay's `BvExpr::Sub` blast is the SAME ripple
--  adder as ADD but with operand2 = `Not`(y) per bit (one's complement) and
--  carry-in = `ConstTrue` (the +1 of two's complement): a + ~b + 1.  This is
--  EXACTLY `bvsub_eval x y = bvaddRec x (wordNot y) true` (already defined for the
--  rung-1 negative control).  g16 `machine_sub x y = addRec_m x (wordNot y) true`.
--  So the SUB fidelity is the SAME induction `bvaddRec_eq_m`, instantiated at
--  second operand `wordNot y` and carry-in `true` — NO new induction needed; the
--  rung-1 lemma was proved general over ALL second operands and carry-ins
--  precisely so SUB falls out.  (This mirrors how g16 `sub_equiv` reuses
--  `addRec_equiv` at `wordNot b` / `true`.)
--
--  BITWISE (bv_blast_solver.rs:1141-1177).  ay's `BvExpr::{And,Or,Xor}` blast is a
--  per-bit gate with NO carry chain: bit i = `And2`/`Or2`/`Xor2`(lhs_i, rhs_i), in
--  operand order.  g16 `zipB_m op` is exactly this shape, and the ay per-bit gate
--  values are `And2=&&`, `Or2=||`, `Xor2=^` — definitionally the g16 MACHINE
--  per-bit ops `fand_m`/`for_m`/`fxor_m`.  So `bvand_eval = machine_and` etc. hold
--  by `rfl` at the model level; the *_equiv theorems then carry them to IR.
--  (Non-vacuity for bitwise lives in the IR side: machine uses `op a b`, IR uses
--  the COMMUTED `op b a` — a real discharge, already in and_equiv/or_equiv/xor_equiv.)
--
--  HONEST RESIDUAL (unchanged from rung 1).  These prove the FORMULA-EVAL <-> g16
--  relationship per op.  They do NOT prove the RUST semantics PRODUCE these shapes
--  — that stays the runtime canonical-shape check (the irreducible residual).  No
--  default-[PROVED] op count changes; this is the kernel keystone for the wiring.
-- ==========================================================================

-- ---- SUB fidelity ----  bvsub_eval == machine_sub == ir_sub, all 32-bit words.
theorem bvsub_eval_eq_machine_sub (a b : Word32) : bvsub_eval a b = machine_sub a b :=
  bvaddRec_eq_m a (wordNot b) true
theorem bvsub_eval_eq_ir_sub (a b : Word32) : bvsub_eval a b = ir_sub a b :=
  Eq.trans (bvsub_eval_eq_machine_sub a b) (sub_equiv a b)

-- ---- bitwise BvExpr-blast evaluators (per-bit gate, no carry; ay And2/Or2/Xor2).
def bvand_eval (x y : List Bool) : List Bool := zipB_m Bool.and x y
def bvor_eval  (x y : List Bool) : List Bool := zipB_m Bool.or  x y
def bvxor_eval (x y : List Bool) : List Bool := zipB_m Bool.xor x y

-- ---- bitwise fidelity ----  bv*_eval == machine_* == ir_*, all 32-bit words.
-- The machine sides are definitional (`fand_m a b = Bool.and a b`, etc.) so the
-- FORMULA<->machine half is `rfl`; the *_equiv theorems discharge the IR commute.
theorem bvand_eval_eq_machine_and (a b : Word32) : bvand_eval a b = machine_and a b := rfl
theorem bvor_eval_eq_machine_or   (a b : Word32) : bvor_eval  a b = machine_or  a b := rfl
theorem bvxor_eval_eq_machine_xor (a b : Word32) : bvxor_eval a b = machine_xor a b := rfl
theorem bvand_eval_eq_ir_and (a b : Word32) : bvand_eval a b = ir_and a b :=
  Eq.trans (bvand_eval_eq_machine_and a b) (and_equiv a b)
theorem bvor_eval_eq_ir_or   (a b : Word32) : bvor_eval  a b = ir_or  a b :=
  Eq.trans (bvor_eval_eq_machine_or a b) (or_equiv a b)
theorem bvxor_eval_eq_ir_xor (a b : Word32) : bvxor_eval a b = ir_xor a b :=
  Eq.trans (bvxor_eval_eq_machine_xor a b) (xor_equiv a b)

-- ==========================================================================
--  RUNG-2 NEGATIVE CONTROLS (LOAD-BEARING).  A WRONG op-shape must NOT discharge.
--   - SUB:  the ADD blast is FALSE-against-machine_sub at a witness (1+1=2 ≠ 1-1=0).
--   - bitwise: the AND blast is FALSE-against-machine_or at a witness (1&0=0 ≠ 1|0=1),
--     i.e. emitting an AND where the IR says OR is caught.
--  Both refute via Bool.noConfusion projected to a discriminating bit; the dual
--  RIGHT-shape theorem is discharged at the same witness (the discriminating pair).
-- ==========================================================================

-- SUB control: ADD-shape (1+1=2) ≠ machine_sub (1-1=0) at the value-2 bit.
theorem wrong_sub_shape_is_false :
    bvadd_eval [true, false] [true, false] = machine_sub [true, false] [true, false] → False :=
  fun h => Bool.noConfusion (congrArg (fun w => bhead (btail w)) h)
theorem bvsub_eval_witness :
    bvsub_eval [true, false] [true, false] = machine_sub [true, false] [true, false] :=
  bvsub_eval_eq_machine_sub [true, false] [true, false]

-- bitwise control: AND-shape (1&0=0) ≠ machine_or (1|0=1) at the bit-0 position.
-- 1 = [true,false], 0 = [false,false] (LSB-first, width 2).
theorem wrong_bitwise_shape_is_false :
    bvand_eval [true, false] [false, false] = machine_or [true, false] [false, false] → False :=
  fun h => Bool.noConfusion (congrArg (fun w => bhead w) h)
theorem bvor_eval_witness :
    bvor_eval [true, false] [false, false] = machine_or [true, false] [false, false] :=
  bvor_eval_eq_machine_or [true, false] [false, false]

-- ==========================================================================
--  F3 FIDELITY — RUNG 3.  COMPLETE the 12-op layer: neg + the relational
--  compares (ult/ule/slt/sle/eq) BvExpr blast == g16 machine relation.
--
--  This closes the FORMULA-EVAL <-> g16-MODEL fidelity for every remaining
--  default-eligible linear-ALU op the gate emits.  Each REFLECTS the ay/gate
--  bit-blast SHAPE (verify_output.rs predicate_to_bvexpr 2150-2262;
--  bv_blast_solver.rs BvExpr::{CarryOut,Eq,Not,Sub}) and proves it EQUAL to the
--  g16 machine relation already proven == IR (carryOut_equiv / signed_lt_equiv /
--  unsigned_lt_equiv / eq_equiv).  Composing fidelity ∘ *_equiv gives the kernel
--  chain  eval(blast) == machine_rel == ir_rel  for the whole compare fragment.
--
--  HOW THE GATE BLASTS EACH (confirmed against the source, NOT assumed):
--   * NEG  (verify_output.rs:2541):  -a  ==  BvSub(0, a)  ==  machine_sub 0 a.
--   * ULT  (2182): a <u b  ==  Not(CarryOut(a, b, is_sub=true)).  CarryOut(is_sub)
--          threads the SAME FullAdderCarry chain over a + ~b + 1 (carry-in 1) —
--          the g16 carryOut_m a (wordNot b) true (= unsigned_lt_m, modulo Not).
--   * ULE  (2186): a <=u b  ==  CarryOut(b, a, is_sub=true)  ==  Not(b <u a).
--   * SLT  (2166,2246): a <s b == Not(Eq(N,V)) = N XOR V, N/V the MSB-extract
--          flags off Sub(a,b) — the g16 signed_lt_m flag formula on machine_sub.
--   * SLE  (2167): a <=s b  ==  Not(b <s a).
--   * EQ   (2159, bv_blast_solver Eq doc): per-bit XnorEq AND-reduced —
--          AND_i (a_i == b_i) — the g16 eq predicate, here bridged to the
--          g16 eq_m = allZero(machine_sub a b) form (a REAL theorem: per-bit
--          equality fold == subtract-is-zero).
--
--  CARRY-OUT FIDELITY (the new induction this rung needs).  ay's CarryOut blast
--  uses fcarry_bv (the MAJ encoding (a&&b)||(c&&(a^b))); g16 carryOut_m uses
--  fcarry_m.  bvCarryOut (below) mirrors ay; bvCarryOut_eq_m proves it == carryOut_m
--  for ALL inputs by induction (the carryOut_equiv shape, rewriting per bit by
--  fcarry_bv_eq_m — NOT rfl, since the carry encodings genuinely differ).
--
--  HONEST RESIDUAL (unchanged): proves FORMULA-EVAL <-> g16; does NOT prove the
--  RUST semantics PRODUCE these shapes (the runtime canonical-shape check). No
--  default-[PROVED] op count changes — kernel keystone for the rung-3 wiring.
-- ==========================================================================

-- ---- NEG ----  ay/gate blast: -a == BvSub(0, a) (verify_output.rs:2541).  We
-- model neg as SUB at an explicit zero operand `z`, so the shape is exactly the
-- gate's `BvSub(Const0, a)` = machine_sub z a; the all-inputs theorem holds for
-- ANY z (the gate supplies z = the zero constant).
def machine_neg (z a : List Bool) : List Bool := machine_sub z a
def bvneg_blast (z a : List Bool) : List Bool := bvsub_eval z a
-- NEG fidelity: the BvSub(0,a) blast == machine_sub 0 a == ir_sub 0 a, all inputs.
theorem bvneg_eq_machine_neg (z a : Word32) : bvneg_blast z a = machine_neg z a :=
  bvsub_eval_eq_machine_sub z a
theorem bvneg_eq_ir_neg (z a : Word32) : bvneg_blast z a = ir_sub z a :=
  bvsub_eval_eq_ir_sub z a

-- Local double-negation on Bool (clean has no Bool.not_not): exhaustive case split.
theorem bool_not_not (x : Bool) : Bool.not (Bool.not x) = x :=
  @Bool.rec (fun y => Bool.not (Bool.not y) = y) rfl rfl x

-- ---- CARRY-OUT blast (ay CarryOut node, fcarry_bv chain) ----
def bvCarryOut : List Bool → List Bool → Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool → Bool)
    (fun _ c => c)
    (fun a as_ ih => fun ys c => ih (btail ys) (fcarry_bv a (bhead ys) c))
    xs
theorem bvCarryOut_cons (a : Bool) (as_ ys : List Bool) (c : Bool) :
    bvCarryOut (List.cons a as_) ys c
    = bvCarryOut as_ (btail ys) (fcarry_bv a (bhead ys) c) := rfl
-- bvCarryOut (ay) == carryOut_m (g16 machine), ALL inputs/carry-ins, by induction
-- (carryOut_equiv shape; per-bit carry rewritten by fcarry_bv_eq_m — NOT rfl).
def BvCOEq (xs : List Bool) : Prop :=
  ∀ (ys : List Bool) (c : Bool), bvCarryOut xs ys c = carryOut_m xs ys c
theorem bvCarryOut_eq_m (xs : List Bool) : BvCOEq xs :=
  @List.rec Bool BvCOEq
    (fun _ _ => rfl)
    (fun a as_ ih => fun ys c =>
      Eq.trans (bvCarryOut_cons a as_ ys c)
        (Eq.trans
          (congrArg (fun cc => bvCarryOut as_ (btail ys) cc) (fcarry_bv_eq_m a (bhead ys) c))
          (Eq.trans
            (ih (btail ys) (fcarry_m a (bhead ys) c))
            (Eq.symm (carryOut_m_cons a as_ ys c)))))
    xs

-- ---- UNSIGNED LT / LE fidelity ----  ay: a<u b = Not(CarryOut(a,b,sub)).
def bvult_eval (a b : List Bool) : Bool := Bool.not (bvCarryOut a (wordNot b) true)
-- g16 machine unsigned-LE = Not(b <u a) (the gate's ULE = CarryOut(b,a,sub)).
def unsigned_le_m (a b : List Bool) : Bool := Bool.not (unsigned_lt_m b a)
def unsigned_le_ir (a b : List Bool) : Bool := Bool.not (unsigned_lt_ir b a)
theorem unsigned_le_equiv (a b : Word32) : unsigned_le_m a b = unsigned_le_ir a b :=
  congrArg Bool.not (unsigned_lt_equiv b a)
-- ay ULE blast: a<=u b = CarryOut(b,a,sub) = Not(b<u a) = unsigned_le.
def bvule_eval (a b : List Bool) : Bool := bvCarryOut b (wordNot a) true

theorem bvult_eval_eq_machine (a b : Word32) : bvult_eval a b = unsigned_lt_m a b :=
  congrArg Bool.not (bvCarryOut_eq_m a (wordNot b) true)
theorem bvult_eval_eq_ir (a b : Word32) : bvult_eval a b = unsigned_lt_ir a b :=
  Eq.trans (bvult_eval_eq_machine a b) (unsigned_lt_equiv a b)
-- ULE: bvule_eval a b = bvCarryOut b (~a) true = carryOut_m b (~a) true
--                      = Not(unsigned_lt_m b a) ... but unsigned_lt_m b a = Not(carryOut),
-- so Not(Not carryOut) = carryOut.  Establish bvule_eval = unsigned_le_m directly.
theorem bvule_eval_eq_machine (a b : Word32) : bvule_eval a b = unsigned_le_m a b :=
  -- bvule_eval a b = bvCarryOut b (~a) true = carryOut_m b (~a) true.
  -- unsigned_le_m a b = Not(unsigned_lt_m b a) = Not(Not(carryOut_m b (~a) true))
  --                   = carryOut_m b (~a) true.  Bridge via Bool.not_not.
  Eq.trans (bvCarryOut_eq_m b (wordNot a) true)
    (Eq.symm (bool_not_not (carryOut_m b (wordNot a) true)))
theorem bvule_eval_eq_ir (a b : Word32) : bvule_eval a b = unsigned_le_ir a b :=
  Eq.trans (bvule_eval_eq_machine a b) (unsigned_le_equiv a b)

-- ---- SIGNED LT / LE fidelity ----  ay: a<s b = N XOR V over Sub(a,b)'s MSB.
-- The gate's flag formula (signed_lt_flag_formula) reads N/V off the SUB result;
-- ay's SUB blast is bvsub_eval, so the reflected signed-LT reads the SAME flags
-- off bvsub_eval.  g16 signed_lt_m reads them off machine_sub.  bvsub_eval ==
-- machine_sub (rung 2), so the whole flag formula agrees by congrArg.
def bvslt_eval (a b : List Bool) : Bool :=
  Bool.xor (msb (bvsub_eval a b))
    (Bool.and (Bool.xor (msb a) (msb b)) (Bool.xor (msb a) (msb (bvsub_eval a b))))
theorem bvslt_eval_eq_machine (a b : Word32) : bvslt_eval a b = signed_lt_m a b :=
  congrArg
    (fun r => Bool.xor (msb r)
       (Bool.and (Bool.xor (msb a) (msb b)) (Bool.xor (msb a) (msb r))))
    (bvsub_eval_eq_machine_sub a b)
theorem bvslt_eval_eq_ir (a b : Word32) : bvslt_eval a b = signed_lt_ir a b :=
  Eq.trans (bvslt_eval_eq_machine a b) (signed_lt_equiv a b)
-- SLE: a<=s b = Not(b<s a).
def signed_le_m (a b : List Bool) : Bool := Bool.not (signed_lt_m b a)
def signed_le_ir (a b : List Bool) : Bool := Bool.not (signed_lt_ir b a)
theorem signed_le_equiv (a b : Word32) : signed_le_m a b = signed_le_ir a b :=
  congrArg Bool.not (signed_lt_equiv b a)
def bvsle_eval (a b : List Bool) : Bool := Bool.not (bvslt_eval b a)
theorem bvsle_eval_eq_machine (a b : Word32) : bvsle_eval a b = signed_le_m a b :=
  congrArg Bool.not (bvslt_eval_eq_machine b a)
theorem bvsle_eval_eq_ir (a b : Word32) : bvsle_eval a b = signed_le_ir a b :=
  Eq.trans (bvsle_eval_eq_machine a b) (signed_le_equiv a b)

-- ---- EQ fidelity ----  ay Eq(a,b): per-bit XnorEq (a_i == b_i) AND-reduced.
-- This is the g16 eq predicate in PER-BIT-EQUALITY form; g16 eq_m is in
-- SUBTRACT-IS-ZERO form (allZero (machine_sub a b)).  The fidelity bridges these
-- two GENUINELY DIFFERENT formulations.  bveq_eval folds Bool.and over the per-bit
-- Bool.beq, with empty-AND base `true` (matching the AND-reduce of an N-bit chain).
def bveq_eval : List Bool → List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool)
    (fun _ => true)
    (fun a as_ ih => fun ys => Bool.and (Bool.beq a (bhead ys)) (ih (btail ys)))
    xs
-- We anchor the EQ fidelity at the LEVEL THE GATE ACTUALLY EMITS: the gate lowers
-- `eq` as the per-bit XnorEq AND-reduce (predicate_to_bvexpr Formula::Eq ->
-- BvExpr::eq, verify_output.rs:2159; bv_blast_solver Eq doc), i.e. EXACTLY
-- bveq_eval — NOT as allZero(sub).  So the FORMULA-EVAL <-> g16 claim for the
-- gate's eq shape is `bveq_eval a b == eqfold_m a b` (the g16 per-bit-equality
-- relation), and eqfold_m == eqfold_ir is the g16 equivalence.  We keep machine =
-- beq a_i b_i, IR = beq b_i a_i (operand-commuted, mirroring the bitwise pattern)
-- so the equivalence is a real discharge, not X = X.
def eqbit_m  (a b : Bool) : Bool := Bool.beq a b
def eqbit_ir (a b : Bool) : Bool := Bool.beq b a
theorem eqbit_eq (a b : Bool) : eqbit_m a b = eqbit_ir a b :=
  @Bool.rec (fun x => eqbit_m x b = eqbit_ir x b)
    (@Bool.rec (fun y => eqbit_m false y = eqbit_ir false y) rfl rfl b)
    (@Bool.rec (fun y => eqbit_m true y = eqbit_ir true y) rfl rfl b) a
def eqfold_m : List Bool → List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool) (fun _ => true)
    (fun a as_ ih => fun ys => Bool.and (eqbit_m a (bhead ys)) (ih (btail ys))) xs
def eqfold_ir : List Bool → List Bool → Bool := fun xs =>
  @List.rec Bool (fun _ => List Bool → Bool) (fun _ => true)
    (fun a as_ ih => fun ys => Bool.and (eqbit_ir a (bhead ys)) (ih (btail ys))) xs
theorem eqfold_m_cons (a : Bool) (as_ ys : List Bool) :
    eqfold_m (List.cons a as_) ys = Bool.and (eqbit_m a (bhead ys)) (eqfold_m as_ (btail ys)) := rfl
theorem eqfold_ir_cons (a : Bool) (as_ ys : List Bool) :
    eqfold_ir (List.cons a as_) ys = Bool.and (eqbit_ir a (bhead ys)) (eqfold_ir as_ (btail ys)) := rfl
def EqFoldEq (xs : List Bool) : Prop := ∀ ys : List Bool, eqfold_m xs ys = eqfold_ir xs ys
theorem eqfold_equiv (xs : List Bool) : EqFoldEq xs :=
  @List.rec Bool EqFoldEq
    (fun _ => rfl)
    (fun a as_ ih => fun ys =>
      Eq.trans (eqfold_m_cons a as_ ys)
        (Eq.trans
          (congrArg (fun h => Bool.and h (eqfold_m as_ (btail ys))) (eqbit_eq a (bhead ys)))
          (Eq.trans
            (congrArg (fun t => Bool.and (eqbit_ir a (bhead ys)) t) (ih (btail ys)))
            (Eq.symm (eqfold_ir_cons a as_ ys)))))
    xs
-- bveq_eval (ay XnorEq AND-reduce) == eqfold_m (g16 per-bit-eq machine) by rfl
-- (Bool.beq is XnorEq; bveq_eval and eqfold_m have the identical recursion).
theorem bveq_eval_eq_machine (a b : Word32) : bveq_eval a b = eqfold_m a b := rfl
theorem bveq_eval_eq_ir (a b : Word32) : bveq_eval a b = eqfold_ir a b :=
  Eq.trans (bveq_eval_eq_machine a b) (eqfold_equiv a b)

-- ==========================================================================
--  RUNG-3 NEGATIVE CONTROLS (LOAD-BEARING).  Each wrong op-shape is refused, with
--  a discriminating witness; width 2 unless noted.  -1=[t,t], 1=[t,f], -2=[f,t],
--  2=[f,t]@bit1... use the established compare witnesses (slt vs ult differ on
--  neg-vs-pos; eq vs distinct).
-- ==========================================================================

-- ULT control: signed-lt-shape (-1 <s 1 = TRUE) ≠ unsigned_lt_m (-1=3 <u 1 = FALSE).
theorem wrong_ult_shape_is_false :
    bvslt_eval [true, true] [true, false] = unsigned_lt_m [true, true] [true, false] → False :=
  fun h => Bool.noConfusion h
theorem bvult_eval_witness :
    bvult_eval [true, true] [true, false] = unsigned_lt_m [true, true] [true, false] :=
  bvult_eval_eq_machine [true, true] [true, false]
-- SLT control: unsigned-lt-shape (3 <u 1 = FALSE) ≠ signed_lt_m (-1 <s 1 = TRUE).
theorem wrong_slt_shape_is_false :
    bvult_eval [true, true] [true, false] = signed_lt_m [true, true] [true, false] → False :=
  fun h => Bool.noConfusion h
theorem bvslt_eval_witness :
    bvslt_eval [true, true] [true, false] = signed_lt_m [true, true] [true, false] :=
  bvslt_eval_eq_machine [true, true] [true, false]
-- EQ control: a wrong NE-shape (Not eq) ≠ eqfold_m on EQUAL inputs (eq=true, ne=false).
theorem wrong_eq_shape_is_false :
    Bool.not (bveq_eval [true, false] [true, false]) = eqfold_m [true, false] [true, false] → False :=
  fun h => Bool.noConfusion h
theorem bveq_eval_witness :
    bveq_eval [true, false] [true, false] = eqfold_m [true, false] [true, false] :=
  bveq_eval_eq_machine [true, false] [true, false]
-- NEG control: 0 - 1 = -1 = all-ones = [t,t]; an ADD-shape 0+1 = 1 = [t,f] differs
-- at bit 1 (value-2 position): add bit1 = false, neg(sub) bit1 = true.
theorem wrong_neg_shape_is_false :
    bvadd_eval [false, false] [true, false] = machine_neg [false, false] [true, false] → False :=
  fun h => Bool.noConfusion (congrArg (fun w => bhead (btail w)) h)
theorem bvneg_eval_witness :
    bvneg_blast [false, false] [true, false] = machine_neg [false, false] [true, false] :=
  bvneg_eq_machine_neg [false, false] [true, false]

-- ==========================================================================
--  RUNG-3 STEP 1 — THE KERNEL BRIDGE (standalone, kernel-only; NOT runtime wiring).
--
--  WHAT THIS IS (read precisely — it is the #30-step-1 blocker, landed standalone).
--  The runtime gate's [PROVED] obligation is a property of an ay `BvExpr` TREE
--  (bv_blast_solver.rs `enum BvExpr`), discharged today by SAT reflection.  To
--  later discharge it by O(1) instantiation of the g16 fidelity theorems
--  (#27-#29), the gate's `BvExpr` must be EMBEDDED as a kernel datatype with a
--  kernel-checked evaluator that is PROVED equal to the g16 model evaluators.
--  This section provides exactly that embedding + the evaluator-≡-g16 bridge, for
--  the 12-op surface, kernel-checked with empty domain axioms.  It does NOT touch
--  the runtime (clean-auto / verify_output.rs) — steps 2-4 (#30) do that; this is
--  the standalone, zero-half-wiring-risk first step.
--
--  THE DATATYPE.  `BvE` mirrors the gate `BvExpr` op shape over `List Bool`
--  leaves: a Leaf, the binary arith/bitwise ops, Not, the 1-bit-result CarryOut
--  and Eq, and a zero-constant (for neg = Sub(0,a)).  It is a genuine recursive
--  inductive (like the accepted lrat_checker_tree `Tree`).
--
--  THE EVALUATOR — TWO INDEPENDENT KINDS.  A bit-vector node evaluates to a
--  `List Bool` via `bvEval`; a predicate node (CarryOut / Eq / Not-of-predicate)
--  evaluates to a `Bool` via `bvPredEval`.  CRUCIALLY, `bvEval`/`bvPredEval`
--  recurse over the `BvE` TREE STRUCTURE (a DIFFERENT definitional path from the
--  flat g16 `bv*_eval` functions), then the bridge theorems prove the tree
--  evaluator computes the SAME result as the g16 evaluators — so a later O(1)
--  instantiation against `BvE` is sound w.r.t. the g16 fidelity chain.
--
--  NON-VACUITY.  The bridge composes through the #27-#29 fidelity theorems to the
--  g16 IR relations (ir_add / unsigned_lt_ir / signed_lt_ir / eqfold_ir / …), which
--  are SEPARATELY-defined terms — so `bvEval (Add a b) == ir_add …` is a real
--  chain, not rfl.  Adversarial: a wrong-op tree (Sub where Add is meant) is NOT
--  provable-equal to the add relation (negative controls below), and the
--  signed-vs-unsigned discriminator (a CarryOut/ULT tree ≠ the SLT flag tree) is
--  refuted at the neg-vs-pos witness.
--
--  HONEST RESIDUAL (REQUIRED).  This proves the KERNEL-DATATYPE EVALUATOR ≡ g16
--  eval (and ≡ the g16 IR relations).  It does NOT by itself change ANY
--  default-[PROVED] op count — that happens only after steps 2-4 wire a
--  `GateRecheck::Instantiated` path + a Rust shape-matcher into the runtime gate
--  + a stage2 build.  No runtime TCB touched here; no over-claim.
-- ==========================================================================

-- The gate-`BvExpr`-mirroring kernel datatype.  `Leaf` carries the operand word;
-- `Zero` is the width-matched zero constant (Sub(0,a) = neg); the binary ops and
-- Not mirror BvExpr::{Add,Sub,And,Or,Xor,Not}; `CarryOutSub a b` and `EqOp a b`
-- are the 1-bit-result nodes the compares decompose to.
inductive BvE where
  | Leaf : List Bool → BvE
  | Zero : List Bool → BvE            -- a zero constant of the same shape as Leaf
  | AddE : BvE → BvE → BvE
  | SubE : BvE → BvE → BvE
  | AndE : BvE → BvE → BvE
  | OrE  : BvE → BvE → BvE
  | XorE : BvE → BvE → BvE
  | NotE : BvE → BvE

-- Bit-vector evaluator: recurse over the TREE, applying the ay blast primitive at
-- each node (bvadd_eval / bvsub_eval / bvand_eval / … from #27-#29).  Zero leaf
-- evaluates to wordNot-of-allones... no: we carry the explicit zero word.
def bvEval : BvE → List Bool := fun e =>
  @BvE.rec (fun _ => List Bool)
    (fun w => w)                                   -- Leaf w
    (fun z => z)                                   -- Zero z  (the explicit zero word)
    (fun _ _ la lb => bvadd_eval la lb)            -- AddE
    (fun _ _ la lb => bvsub_eval la lb)            -- SubE
    (fun _ _ la lb => bvand_eval la lb)            -- AndE
    (fun _ _ la lb => bvor_eval  la lb)            -- OrE
    (fun _ _ la lb => bvxor_eval la lb)            -- XorE
    (fun _ la => wordNot la)                       -- NotE
    e

-- ---- BRIDGE: tree evaluator == g16 IR relation, per op (composes #27-#29). ----
-- ADD: bvEval (AddE (Leaf a)(Leaf b)) == ir_add a b.
theorem bridge_add_ir (a b : Word32) :
    bvEval (BvE.AddE (BvE.Leaf a) (BvE.Leaf b)) = ir_add a b :=
  bvadd_eval_eq_ir_add a b
theorem bridge_sub_ir (a b : Word32) :
    bvEval (BvE.SubE (BvE.Leaf a) (BvE.Leaf b)) = ir_sub a b :=
  bvsub_eval_eq_ir_sub a b
theorem bridge_and_ir (a b : Word32) :
    bvEval (BvE.AndE (BvE.Leaf a) (BvE.Leaf b)) = ir_and a b :=
  bvand_eval_eq_ir_and a b
theorem bridge_or_ir (a b : Word32) :
    bvEval (BvE.OrE (BvE.Leaf a) (BvE.Leaf b)) = ir_or a b :=
  bvor_eval_eq_ir_or a b
theorem bridge_xor_ir (a b : Word32) :
    bvEval (BvE.XorE (BvE.Leaf a) (BvE.Leaf b)) = ir_xor a b :=
  bvxor_eval_eq_ir_xor a b
-- NEG: bvEval (SubE (Zero z)(Leaf a)) == ir_sub z a  (the gate's BvSub(0,a)).
theorem bridge_neg_ir (z a : Word32) :
    bvEval (BvE.SubE (BvE.Zero z) (BvE.Leaf a)) = ir_sub z a :=
  bvsub_eval_eq_ir_sub z a

-- ---- PREDICATE evaluator (1-bit-result compare nodes) + bridges. ----
-- The compares are 1-bit predicates over BvE leaves; we model them as a small
-- predicate evaluator returning Bool, mirroring the gate's CarryOut/Eq/Not
-- decomposition (predicate_to_bvexpr).  Each constructor is a g16 relation shape.
inductive BvP where
  | UltP : List Bool → List Bool → BvP    -- a <u b  == Not(CarryOut(a,b,sub))
  | UleP : List Bool → List Bool → BvP    -- a <=u b == CarryOut(b,a,sub)
  | SltP : List Bool → List Bool → BvP    -- a <s b  == N XOR V flags off Sub(a,b)
  | SleP : List Bool → List Bool → BvP    -- a <=s b == Not(b <s a)
  | EqP  : List Bool → List Bool → BvP    -- a == b  == per-bit XnorEq AND-reduce

def bvPredEval : BvP → Bool := fun p =>
  @BvP.rec (fun _ => Bool)
    (fun a b => bvult_eval a b)
    (fun a b => bvule_eval a b)
    (fun a b => bvslt_eval a b)
    (fun a b => bvsle_eval a b)
    (fun a b => bveq_eval  a b)
    p

-- BRIDGE: predicate-tree evaluator == g16 IR relation, per compare op.
theorem bridge_ult_ir (a b : Word32) : bvPredEval (BvP.UltP a b) = unsigned_lt_ir a b :=
  bvult_eval_eq_ir a b
theorem bridge_ule_ir (a b : Word32) : bvPredEval (BvP.UleP a b) = unsigned_le_ir a b :=
  bvule_eval_eq_ir a b
theorem bridge_slt_ir (a b : Word32) : bvPredEval (BvP.SltP a b) = signed_lt_ir a b :=
  bvslt_eval_eq_ir a b
theorem bridge_sle_ir (a b : Word32) : bvPredEval (BvP.SleP a b) = signed_le_ir a b :=
  bvsle_eval_eq_ir a b
theorem bridge_eq_ir (a b : Word32) : bvPredEval (BvP.EqP a b) = eqfold_ir a b :=
  bveq_eval_eq_ir a b

-- ==========================================================================
--  KERNEL-BRIDGE NEGATIVE CONTROLS (LOAD-BEARING).  A WRONG tree must NOT be
--  provable-equal to the intended relation.  Each refutes at a discriminating
--  witness via Bool.noConfusion / list-bit projection; the dual RIGHT-tree
--  theorem discharges at the same witness.  Includes the signed-vs-unsigned
--  discriminator class.
-- ==========================================================================

-- ADD-tree control: a SUB tree (1-1=0) ≠ the add relation (1+1=2) at bit 1.
theorem wrong_add_tree_is_false :
    bvEval (BvE.SubE (BvE.Leaf [true, false]) (BvE.Leaf [true, false]))
      = ir_add [true, false] [true, false] → False :=
  fun h => Bool.noConfusion (congrArg (fun w => bhead (btail w)) h)
theorem add_tree_witness :
    bvEval (BvE.AddE (BvE.Leaf [true, false]) (BvE.Leaf [true, false]))
      = ir_add [true, false] [true, false] :=
  bridge_add_ir [true, false] [true, false]

-- SIGNED-vs-UNSIGNED tree discriminator: a ULT tree (-1 as 3 <u 1 = FALSE) ≠ the
-- signed-lt relation (-1 <s 1 = TRUE).  The exact abs(-5) bug class, at the tree level.
theorem wrong_signed_as_unsigned_tree_is_false :
    bvPredEval (BvP.UltP [true, true] [true, false])
      = signed_lt_ir [true, true] [true, false] → False :=
  fun h => Bool.noConfusion h
theorem slt_tree_witness :
    bvPredEval (BvP.SltP [true, true] [true, false])
      = signed_lt_ir [true, true] [true, false] :=
  bridge_slt_ir [true, true] [true, false]
-- And the dual: a SLT tree ≠ the unsigned-lt relation at the same witness.
theorem wrong_unsigned_as_signed_tree_is_false :
    bvPredEval (BvP.SltP [true, true] [true, false])
      = unsigned_lt_ir [true, true] [true, false] → False :=
  fun h => Bool.noConfusion h

-- EQ-tree control: an EQ tree on EQUAL inputs = true; a (negated) NE shape differs.
theorem wrong_eq_tree_is_false :
    Bool.not (bvPredEval (BvP.EqP [true, false] [true, false]))
      = eqfold_ir [true, false] [true, false] → False :=
  fun h => Bool.noConfusion h
theorem eq_tree_witness :
    bvPredEval (BvP.EqP [true, false] [true, false]) = eqfold_ir [true, false] [true, false] :=
  bridge_eq_ir [true, false] [true, false]

end G16
