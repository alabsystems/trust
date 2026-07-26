// trust-clean/src/mirsem — GOAL-ITEM #4, Phase 1: the FAITHFULNESS meta-theorem.
//
// THE GAP THIS CLOSES.
// Even a perfect structural reflection `R : Rust → Clean` is, today, *trusted*:
// there is no proof that the Clean denotation captures Rust/MIR semantics. A proof
// discharged over `R` is therefore "proven IF you trust R." Goal #4 closes that by
// (1) pinning the MIR operational semantics IN CLEAN — the `Trust.MirSem` anchor —
// and (2) proving `R` ADEQUATE to it: a checked-by-construction refinement between
// the operational meaning of a MIR construct and its grounded Clean denotation.
//
// PHASE 1 SCOPE (this file). The scalar-operand fragment that Trust reflects via
// `clean_ground::operand_to_formula` / `ground_int`:
//
//   * `Trust.MirSem.Operand` — a minimal inductive modeling the operands the
//     reflection actually consumes: `Var idx | Const c | Move src`.
//   * `Trust.MirSem.eval : Env → Operand → Int` — the operational evaluator,
//     with `Env = Nat → Int` the parameter binding (`Var p` ↦ the p-th binding).
//   * Lemma 1A (operand adequacy) — for each operand form, the grounded Clean
//     denotation (what `ground_int(operand_to_formula(O))` produces, as an `Expr`)
//     EQUALS `MirSem.eval Env O`. Proven modulo the 3 foundational axioms, in the
//     REAL clean-kernel. `Const`/`Var`/`Move` are each closed-form (the recursor's
//     ι-reduction makes `eval Env O` def-eq to the denotation, so the adequacy
//     witness is `Eq.refl`).
//
// SOUNDNESS DISCIPLINE (mirrors clean_ground.rs).
//   * The inductive + every lemma must kernel-check with `axiom_deps ⊆
//     {propext, Quot.sound, Classical.choice}` — modulo exactly 3 axioms, NO 4th
//     axiom, NO opaque/sorry. Each builder returns the kernel's own `axiom_deps`
//     verdict so a non-foundational residue is reported, never hidden.
//   * Fail-closed certificate: a DELIBERATELY-WRONG adequacy claim (e.g. `eval Env
//     (Const 5) = 6`) must NOT prove. The unit tests assert this.
//
// This module does NOT touch reflect.rs or clean_ground.rs's reflect path; it pins
// the semantics in parallel and exposes an `operand_adequacy_witness` hook the §6
// pipeline can later attach (see `faithfulness_certified` in prove.rs).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, LevelVec, Name, TypeChecker,
};

// ---------------------------------------------------------------------------
// Canonical Clean names for the MirSem anchor
// ---------------------------------------------------------------------------
/// The MIR-operand inductive pinned in Clean (the semantic anchor's syntax).
pub const MIRSEM_OPERAND: &str = "Trust.MirSem.Operand";

/// `Var (idx : Nat)` — a parameter reference (the `idx`-th binding).
pub const MIRSEM_OPERAND_VAR: &str = "Trust.MirSem.Operand.Var";

/// `Const (c : Int)` — an integer literal operand.
pub const MIRSEM_OPERAND_CONST: &str = "Trust.MirSem.Operand.Const";

/// `Move (src : Operand)` — a move out of another operand (semantically the
/// referent: `eval (Move src) = eval src`).
pub const MIRSEM_OPERAND_MOVE: &str = "Trust.MirSem.Operand.Move";

/// `Index (s i : Operand) : Operand` — a SLICE-ELEMENT access `s[i]`, the array
/// index arm of a guarded `if i < s.len() { s[i] } else { 0 }` return.
///
/// ADDITIVE FOURTH constructor (mirrors the And-Cond discipline): it adds the
/// `eval (Index s i) = idx_elem (eval e s) (eval e i)` arm WITHOUT touching
/// `Var`/`Const`/`Move` or their `eval` arms, so every existing operand
/// reflexivity/adequacy certificate stays byte-identical and def-eq (the new minor
/// premise the recursor gains is simply ignored on a `Var`/`Const`/`Move` value).
/// The element value is modeled by the UNINTERPRETED total `idx_elem` (below): the
/// soundness of an index-arm function rests on its BOUNDS VC (`i < s.len()`,
/// discharged from the guard) and the branch refinement, NOT on any concrete
/// element value — so an opaque, total `Int → Int → Int` element model is sound.
pub const MIRSEM_OPERAND_INDEX: &str = "Trust.MirSem.Operand.Index";

/// `Len (s : Operand) : Operand` — a SLICE LENGTH `s.len()` (`Rvalue::UnaryOp
/// (PtrMetadata, s)` / `Rvalue::Len`), the `b` operand of an index guard `i < s.len()`.
///
/// ADDITIVE FIFTH constructor (same discipline as `Index`): it adds the
/// `eval (Len s) = slice_len (eval e s)` arm WITHOUT touching any existing
/// constructor or its `eval` arm. The length value is UNINTERPRETED — modeled by the
/// total `slice_len` (below); the index guard's faithfulness rests on the bounds VC +
/// branch refinement, not on a concrete length.
pub const MIRSEM_OPERAND_LEN: &str = "Trust.MirSem.Operand.Len";

/// `PreOpNot (s : Operand) : Operand` — the bitwise-complement pre-operation
/// used by a call argument such as `count_ones(!self)`. Its evaluator is the
/// exact two's-complement identity `Int.xor (eval e s) (-1)`, reusing the
/// existing non-axiom `Int.xor` opaque head.
pub const MIRSEM_OPERAND_PREOP_NOT: &str = "Trust.MirSem.Operand.PreOpNot";

/// `PreOpNeg (s : Operand) : Operand` — the arithmetic-negation pre-operation
/// used by a call argument. Its evaluator is exactly `Int.sub 0 (eval e s)`.
pub const MIRSEM_OPERAND_PREOP_NEG: &str = "Trust.MirSem.Operand.PreOpNeg";

/// The auto-derived recursor for the operand inductive.
pub const MIRSEM_OPERAND_REC: &str = "Trust.MirSem.Operand.rec";

/// The operational evaluator `eval : Env → Operand → Int`.
pub const MIRSEM_EVAL: &str = "Trust.MirSem.eval";

/// `slice_len : Int → Int` — the UNINTERPRETED total slice-length function:
/// `slice_len (slice-handle)` is the modeled `Int` length of `s`. Installed as a
/// `Declaration::Opaque` (never unfolded), like `idx_elem`/`Int.div` — NOT an
/// `Axiom`, so a term referencing it gains no axiom dependency. Sound and total: it
/// asserts no particular length, so nothing is FALSELY discharged from it.
pub const MIRSEM_SLICE_LEN: &str = "Trust.MirSem.slice_len";

/// `idx_elem : Int → Int → Int` — the UNINTERPRETED total slice-element selector:
/// `idx_elem (slice-handle) (index)` is the modeled `Int` value of `s[i]`. Installed
/// as a `Declaration::Opaque` (a type-correct, never-unfolded placeholder body),
/// EXACTLY like the prelude's `Int.div`/`Int.mod`: `Opaque` is NOT a
/// `ConstantKind::Axiom`, so a term referencing it gains NO axiom dependency
/// (`axiom_deps` counts only `Axiom`), keeping the index fragment's closure ⊆ the 3
/// foundational axioms. It is a SOUND, TOTAL `Int`-valued function of `(slice, idx)`:
/// it asserts no particular element value, so no obligation can be FALSELY discharged
/// from it — the bounds VC + branch refinement carry the faithfulness.
pub const MIRSEM_IDX_ELEM: &str = "Trust.MirSem.idx_elem";

/// Trust: W19 mutators inc-1 (2026-07-24) — `idx_elem_prime : Int → Int → Int → Int` — the
/// GENERATION-RE-KEYED field-content base of the field-setter post-state surface (the
/// recon's `idx_elem'`): `idx_elem_prime recv k g` is the modeled `Int` value of the
/// receiver `recv`'s field `k` at generation `g`. Installed as a `Declaration::Opaque`
/// (a type-correct, never-unfolded placeholder), EXACTLY like `idx_elem`/`iter_seq`:
/// `Opaque` is NOT an `Axiom`, so a term referencing it gains NO axiom dependency
/// (`axiom_deps` counts only `Axiom`), keeping the surface's closure ⊆ the 3
/// foundational axioms. Distinct 3-arg (generation-keyed) symbol from the LIVE 2-arg
/// (untimed) field-read
/// `idx_elem` — Opaque non-reduction + differing head/arity block any def-eq bridge.
/// F12-FENCED: `ground_int` has NO arm for this Pred (fall-through `None`), pinned by
/// `field_post_preds_are_fail_closed_in_mirsem_grounder`; NO axiom-shaped bridge to
/// the 2-arg `idx_elem` is minted (option-(ii) cross-instantiation, deferred).
pub const MIRSEM_IDX_ELEM_PRIME: &str = "Trust.MirSem.idx_elem_prime";

/// Trust: W19 mutators inc-1 (2026-07-24) — `set_key_eq : Int → Int → Bool :=
/// λ k f. Int.beq k f` — the SHARED key-guard head of the field-setter post-state
/// surface (the `iter_has_next2` role: a named `Bool` head the theorems can
/// hypothesize on). A reducible `Declaration::Definition` wrapping the EXISTING
/// `Opaque` `Int.beq` the grounder already uses for `Eq` (`clean_ground.rs`
/// `Eq(a,b) → Int.beq (g a) (g b)`) ⇒ EMPTY `axiom_deps`. It need NOT reduce: the
/// `congrArg` transport carries the guard as a hypothesis and never reduces it
/// (exactly as `iter_has_next2`'s `decide(g < iter_len)` is stuck on the opaque
/// `iter_len`). F12-FENCED alongside `idx_elem_prime`/`set_post`.
pub const MIRSEM_SET_KEY_EQ: &str = "Trust.MirSem.set_key_eq";

// ---- Lemma 1B (rvalue adequacy) anchor: BinOp + Rvalue + eval_rvalue ----
/// The MIR-binop inductive pinned in Clean (`Add | Sub | Mul | Div | Rem` — the
/// arithmetic binops whose grounded shape is a clean `Int.<op>` term `ground_int`
/// emits: `Add`/`Sub`/`Mul` ground to the reducible `Int.add`/`sub`/`mul`, `Div`
/// to the prelude's `Opaque` `Int.div` (`ground_int`'s `F::Div` arm), and `Rem`
/// — Trust: witness-tier Rem arm — to the prelude's `Opaque` T-remainder
/// `Int.mod` (`ground_int`'s `F::Rem` arm, landed with the M3 Rem promotion; the
/// VALUE semantics were already three-way-checked there, this constructor closes
/// the WITNESS-tier coverage gap). Shift/bitwise binops are bitvector-grounded,
/// still excluded (fail-closed).
pub const MIRSEM_BINOP: &str = "Trust.MirSem.BinOp";

/// `Add : BinOp` — grounds to the prelude's `Int.add`.
pub const MIRSEM_BINOP_ADD: &str = "Trust.MirSem.BinOp.Add";

/// `Sub : BinOp` — grounds to `Int.sub`.
pub const MIRSEM_BINOP_SUB: &str = "Trust.MirSem.BinOp.Sub";

/// `Mul : BinOp` — grounds to `Int.mul`.
pub const MIRSEM_BINOP_MUL: &str = "Trust.MirSem.BinOp.Mul";

/// `Div : BinOp` — grounds to the prelude's `Opaque` (native-reduced, non-axiom)
/// `Int.div`, matching `ground_int`'s `F::Div(a,b) => app2("Int.div", g(a), g(b))`.
pub const MIRSEM_BINOP_DIV: &str = "Trust.MirSem.BinOp.Div";

/// `Rem : BinOp` — Trust: witness-tier Rem arm — grounds to the prelude's `Opaque`
/// (native-reduced, non-axiom) TRUNCATED remainder `Int.mod` (round toward zero,
/// sign follows the DIVIDEND: `-7 % 3 == -1` — rustc's `%`), matching
/// `ground_int`'s `F::Rem(a,b) => app2("Int.mod", g(a), g(b))` arm EXACTLY.
pub const MIRSEM_BINOP_REM: &str = "Trust.MirSem.BinOp.Rem";

/// Trust: BITWISE SHAPE LANE (2026-07-08) — `BitAnd : BinOp` — grounds to a NEW
/// prelude `Opaque` (native-reduced by the SAME `Int.div`/`Int.mod` discipline,
/// non-axiom) total `Int → Int → Int` function `Int.land` — the EXACT spelling
/// `trustir_bridge.rs`'s kernel bridge already proves wrapped-semantics
/// agreement for (`bridge_semIntBinOp_agreement_all`'s `And` arm). MirSem
/// registers its OWN `Int.land`/`Int.lor`/`Int.xor`/`Int.shiftLeft` Opaque
/// placeholders (`register_int_bitwise`) rather than depending on trust-ir's
/// Basic.lean: `mirsem_env()` never loads Basic.lean (unlike the trust-ir
/// bridge's own environment), so there is no `Duplicate declaration` collision
/// risk — see `register_int_bitwise`'s doc for why the base prelude
/// (`data_types_arithmetic.rs`) deliberately omits these names.
pub const MIRSEM_BINOP_BITAND: &str = "Trust.MirSem.BinOp.BitAnd";

/// `BitOr : BinOp` — Trust: BITWISE SHAPE LANE — grounds to the Opaque
/// `Int.lor`, matching `ground_int`'s new `F::Pred("Int.lor", [a,b])` arm.
pub const MIRSEM_BINOP_BITOR: &str = "Trust.MirSem.BinOp.BitOr";

/// `BitXor : BinOp` — Trust: BITWISE SHAPE LANE — grounds to the Opaque
/// `Int.xor`, matching `ground_int`'s new `F::Pred("Int.xor", [a,b])` arm.
pub const MIRSEM_BINOP_BITXOR: &str = "Trust.MirSem.BinOp.BitXor";

/// `Shl : BinOp` — Trust: BITWISE SHAPE LANE — grounds to the Opaque
/// `Int.shiftLeft` (the UNBOUNDED `a * 2^n` denotation the `clean-compiler`
/// const-folder already spells this name for — `Int.shiftLeft`/`Int.shiftL`,
/// `crates/clean-compiler/src/const_fold_ext2.rs`), matching `ground_int`'s
/// new `F::Pred("Int.shiftLeft", [a,b])` arm.
pub const MIRSEM_BINOP_SHL: &str = "Trust.MirSem.BinOp.Shl";

/// `Shr : BinOp` — Trust: M6 rung 6, UNSIGNED-Shr arm (closing the bitwise
/// shape lane's own named `Shr` residue) — grounds to the Opaque
/// `Int.shiftRight` (the `a / 2^n` floor denotation, which for a NONNEGATIVE
/// shifted value — the ONLY case admitted, see the UNSIGNED-ONLY gate in
/// [`sem_rvalue_of_mir_at_depth`] — coincides EXACTLY with the machine's
/// logical right shift: unsigned `x >> n` never overflows and loses no
/// value, unlike `Shl`). The SIGNED (arithmetic) right shift is NOT modeled
/// — its floor-vs-truncation semantics on negatives differs from the naive
/// `Int` division story, so a signed `Shr` fails closed at the gate.
pub const MIRSEM_BINOP_SHR: &str = "Trust.MirSem.BinOp.Shr";

/// The auto-derived recursor for the binop inductive.
pub const MIRSEM_BINOP_REC: &str = "Trust.MirSem.BinOp.rec";

/// The MIR-rvalue inductive pinned in Clean (`Use(Operand) | Bin(BinOp,Operand,Operand)`
/// — exactly the rvalue forms `extract_return_formula` / `resolve_local_value`
/// reflect to a scalar `Formula`).
pub const MIRSEM_RVALUE: &str = "Trust.MirSem.Rvalue";

/// `Use (op : Operand) : Rvalue` — a direct operand use.
pub const MIRSEM_RVALUE_USE: &str = "Trust.MirSem.Rvalue.Use";

/// `Bin (op : BinOp) (a b : Operand) : Rvalue` — a binary arithmetic rvalue.
pub const MIRSEM_RVALUE_BIN: &str = "Trust.MirSem.Rvalue.Bin";

/// `Sel (c : Cond) (a b : Operand) : Rvalue` — the CONDITIONAL-UPDATE rvalue
/// `if c then a else b` (Trust: Step 6CU, the `max_scan`-shape conditional accumulator
/// update). ADDITIVE third constructor: its `eval_rvalue` arm grounds to
/// `iteI e c (eval e a) (eval e b)` — a `Bool.rec` case-split over the update condition.
/// Adding it forces `eval_rvalue`'s `Rvalue.rec` fold to gain a THIRD minor premise, and
/// the `Cond`/`eval_cond`/`iteI` decls to register BEFORE `Rvalue` (its field references
/// `Cond`). No EXISTING decl's STATEMENT changes — the reorder + the new arm are additive,
/// and the enumeration of constructor fields (`Cond`, `Operand`, `Operand`) stays in the
/// `{propext, Quot.sound, Classical.choice}` axiom closure.
pub const MIRSEM_RVALUE_SEL: &str = "Trust.MirSem.Rvalue.Sel";

/// `Cmp (op : CmpOp) (ra rb : Rvalue) : Rvalue` — Trust: COMPARE-AS-VALUE — a
/// comparison used as a Bool-typed VALUE (not a `SwitchInt` branch guard):
/// `_0 := Eq(_2, 0); return _0` (`ts-is-even`'s shape), `_0 := Le(_t, 127); return _0`
/// (`u8::is_ascii`'s shape). ADDITIVE fourth constructor, RECURSIVE in `ra`/`rb`
/// (the SAME pattern `Trust.MirSem.Cond.And` already established for `Cond`) — so
/// a comparison's SIDE can itself be an arithmetic sub-expression, INLINED rather
/// than left as a cross-reference to a non-parameter local (mirrors
/// `resolve_cast_source_operand`'s inlining discipline, generalized from a single
/// `Use` wrap to the full `sem_rvalue_of_mir` fragment). Grounds via the SAME
/// "Rust bool is the opaque Int 0/1 carrier" idiom `bool_as_int`/`cmp_bool_expr`
/// already establish for the CALL-THEN-PUREOP comparison shape, applied here to
/// the recursor-supplied induction hypotheses (`eval_rvalue e ra`/`eval_rvalue e
/// rb`) instead of a call result. Adding it forces `eval_rvalue`'s `Rvalue.rec`
/// fold to gain a FOURTH minor premise; every existing `Use`/`Bin`/`Sel` reduction
/// is untouched (the recursor simply ignores the new minor on those values), so
/// every prior rvalue certificate stays def-eq.
pub const MIRSEM_RVALUE_CMP: &str = "Trust.MirSem.Rvalue.Cmp";

/// `Or (ra rb : Rvalue) : Rvalue` — Trust: BOOL-CONNECTIVE (BitOr-on-Bool
/// multi-join, 2026-07-08) — a `bool | bool` VALUE (`_a := cmp1; _b := cmp2;
/// _0 := BitOr(_a, _b)`, the `is_ascii_alphanumeric`-class shape: `core`'s own
/// `is_ascii_digit() | is_ascii_uppercase() | is_ascii_lowercase()`). ADDITIVE
/// fifth constructor, RECURSIVE in `ra`/`rb` — the SAME pattern `Cmp` already
/// established (mirrored here one more time: a BitOr's SIDE can itself be a
/// nested comparison OR another BitOr/BitAnd, INLINED via
/// [`resolve_cmp_side`]'s EXISTING temp-inlining discipline, unchanged). Grounds
/// via PURE ARITHMETIC on the two recursor-supplied induction hypotheses
/// (`iha := eval_rvalue e ra`, `ihb := eval_rvalue e rb`, each ALREADY
/// `bool_as_int`-encoded 0/1 by construction — see `eval_rvalue`'s `or_case`/
/// `and_case` doc for why arithmetic — `Int.sub (Int.add iha ihb) (Int.mul iha
/// ihb)`, NOT a `Bool.rec`/decide round-trip — is the ONLY shape that stays
/// def-eq to the live grounder's independent computation). Adding it forces
/// `eval_rvalue`'s `Rvalue.rec` fold to gain a FIFTH minor premise; every
/// existing `Use`/`Bin`/`Sel`/`Cmp` reduction is untouched.
pub const MIRSEM_RVALUE_OR: &str = "Trust.MirSem.Rvalue.Or";

/// `And (ra rb : Rvalue) : Rvalue` — the `&&`-flavored twin of [`MIRSEM_RVALUE_OR`]
/// (`bool & bool`), ADDITIVE sixth constructor, same recursive/grounding
/// discipline (`Bool.and` in place of `Bool.or`).
pub const MIRSEM_RVALUE_AND: &str = "Trust.MirSem.Rvalue.And";

/// `BitBin (op : BinOp) (ra rb : Rvalue) : Rvalue` — Trust: BIT_FIELD
/// NESTED-RVALUE (2026-07-08) — a bitwise/shift rvalue (`BitAnd`/`BitOr`/
/// `BitXor`/`Shl`, reusing the EXISTING `BinOp` field — the same four
/// bitwise constructors the BITWISE SHAPE LANE already added) whose
/// OPERAND(s) can themselves be a NESTED computed rvalue, not just an
/// atomic `Operand` — the `bit_field::get_bit`/`set_bit` shape
/// `(*self & (1 << bit)) != 0`, where `BitAnd`'s second operand is itself a
/// computed `Shl(1, bit)` rvalue that the flat `Bin`'s atomic-operand slot
/// cannot represent. ADDITIVE seventh constructor, RECURSIVE in `ra`/`rb`
/// (the SAME op-parameterized recursive pattern `Cmp` already established —
/// mirrored here one more time, `BinOp` in place of `CmpOp`). Adding it
/// forces `eval_rvalue`'s `Rvalue.rec` fold to gain a SEVENTH minor premise;
/// every existing `Use`/`Bin`/`Sel`/`Cmp`/`Or`/`And` reduction is untouched
/// (the recursor simply ignores the new minor on those values), so every
/// prior rvalue certificate stays def-eq. The flat `Bin` shape (both
/// operands atomic) stays the PREFERRED representation when both operands
/// resolve flatly (see `sem_rvalue_of_mir_at_depth`'s bitwise arm) —
/// `BitBin` is built ONLY when at least one operand genuinely needs the
/// recursive-rvalue representation, so every prior FLAT bitwise certificate
/// (e.g. `sem_rvalue_of_mir_resolves_bitand_on_non_bool_as_genuine_int`)
/// stays byte-identical.
pub const MIRSEM_RVALUE_BITBIN: &str = "Trust.MirSem.Rvalue.BitBin";

/// Trust: W-CMP-DISCR (2026-07-16) — `ArithBin (op : BinOp) (ra rb : Rvalue) :
/// Rvalue`, the ARITHMETIC twin of [`MIRSEM_RVALUE_BITBIN`]: a `+`/`-`/`*`
/// rvalue whose OPERAND(s) can themselves be a NESTED computed rvalue (not just
/// an atomic `Operand`), so a value built by combining two computed sub-values
/// arithmetically is representable — the `signum` normalization
/// `(self > 0) - (self < 0)`, where a `Sub` combines two computed `Cmp`
/// sub-rvalues that the flat `Bin`'s atomic-operand slots cannot hold. ADDITIVE
/// EIGHTH constructor, RECURSIVE in `ra`/`rb` (the SAME op-parameterized
/// recursive pattern `Cmp`/`BitBin` already established). Adding it forces
/// `eval_rvalue`'s `Rvalue.rec` fold to gain an EIGHTH minor premise; every
/// existing `Use`/`Bin`/`Sel`/`Cmp`/`Or`/`And`/`BitBin` reduction is untouched
/// (the recursor ignores the new minor on those values), so every prior rvalue
/// certificate stays def-eq. Its `eval_rvalue` arm is IDENTICAL to `BitBin`'s
/// (`BinOp.rec`-dispatched `int_binop_expr` over the two IHs); the ONLY
/// difference is its `to_formula` reflection — native `F::Add`/`F::Sub`/`F::Mul`
/// (like the FLAT `Bin`) instead of `BitBin`'s opaque `F::Pred` — so the
/// grounder emits the SAME `Int.add`/`Int.sub`/`Int.mul` term the arm reduces
/// to, and adequacy closes by `Eq.refl` exactly as `Bin`/`Cmp` already do. Built
/// ONLY by the fail-closed `signum` recognizer (`resolve_signum_ordering_sign`),
/// always with `op = Sub` over two `Cmp` children.
pub const MIRSEM_RVALUE_ARITHBIN: &str = "Trust.MirSem.Rvalue.ArithBin";

/// The auto-derived recursor for the rvalue inductive.
pub const MIRSEM_RVALUE_REC: &str = "Trust.MirSem.Rvalue.rec";

/// The operational rvalue evaluator `eval_rvalue : Env → Rvalue → Int`.
pub const MIRSEM_EVAL_RVALUE: &str = "Trust.MirSem.eval_rvalue";

// ---- Lemma 1C (return-witness adequacy) anchor: Stmt + exec ----
/// The MIR-statement inductive pinned in Clean (`Assign (idx : Nat) (rv : Rvalue)`
/// — the SSA assignment `extract_return_formula` folds through).
pub const MIRSEM_STMT: &str = "Trust.MirSem.Stmt";

/// `Assign (idx : Nat) (rv : Rvalue) : Stmt` — bind local `idx` to `rv`.
pub const MIRSEM_STMT_ASSIGN: &str = "Trust.MirSem.Stmt.Assign";

/// The auto-derived recursor for the statement inductive.
pub const MIRSEM_STMT_REC: &str = "Trust.MirSem.Stmt.rec";

/// The env-update primitive `set : Env → Nat → Int → Env` — `set e i v` is the
/// environment that agrees with `e` everywhere except index `i`, where it is `v`.
pub const MIRSEM_SET: &str = "Trust.MirSem.set";

/// The statement-list executor `exec : Env → List Stmt → Env` — left-fold each
/// `Assign(i, R)` by `set (eval_rvalue env R)` at index `i`. This is the
/// env-threading fold the SSA-temp-return adequacy reasons over.
pub const MIRSEM_EXEC: &str = "Trust.MirSem.exec";

// ---- Step 6N (NESTED LOOPS) anchor: the OUTER-statement language `OStmt` + `execO`.
//
// The flat loop body `List Stmt` (where `Stmt = Assign`) cannot hold an inner loop:
// to run a dynamic inner loop to completion inside the OUTER body, a body statement
// must itself be able to BE a loop. This is the STRATIFIED, fully ADDITIVE fix.
//
// CRITICAL DESIGN (kernel-empirical, see the OStmt admission probe): a SELF-nested
// `Stmt.Loop : Cond → List Stmt → Stmt` is a NESTED inductive — the kernel's
// nested-elimination rewrites it into a MUTUAL block with an auxiliary `Stmt._List`,
// CHANGING `Stmt.rec`'s arity/motives, which BREAKS the existing `exec` (it no longer
// type-checks) and regresses every flat-body certificate. NON-ADDITIVE. Instead we add
// a SEPARATE outer-statement type `OStmt` that references the EXISTING flat `Stmt`
// (`List Stmt`) for the inner-loop body — so `OStmt` is NOT nested (the recursion is
// through a DIFFERENT, already-closed type), its recursor is a SIMPLE non-mutual
// recursor, and `Stmt`/`exec`/`Stmt.rec` stay BYTE-IDENTICAL. The inner loop reuses the
// EXISTING `exec_loop`. This handles ONE level of nesting (an outer body whose
// statements are plain assignments or fully-flat inner `while` loops) — exactly the
// `while i<n { while j<n {…} i=i+1 }` shape.
/// The OUTER-statement inductive `OStmt : Type` (two constructors, NOT nested):
/// `Assign (idx : Nat)(rv : Rvalue) : OStmt` (a plain outer assignment) and
/// `Loop (cond : Cond)(body : List Stmt)(fuel : Nat) : OStmt` (a fully-FLAT inner
/// `while cond { body }` run for `fuel` guarded iterations). The `Loop` field
/// `body : List Stmt` references the EXISTING flat statement type, so `OStmt` is a
/// plain (non-nested, non-mutual) inductive whose `OStmt.rec` is the simple recursor.
pub const MIRSEM_OSTMT: &str = "Trust.MirSem.OStmt";

/// `OStmt.Assign (idx : Nat)(rv : Rvalue) : OStmt` — a plain outer assignment, the
/// same shape as `Stmt.Assign`, executed identically (`set e idx (eval_rvalue e rv)`).
pub const MIRSEM_OSTMT_ASSIGN: &str = "Trust.MirSem.OStmt.Assign";

/// `OStmt.Loop (cond : Cond)(body : List Stmt)(fuel : Nat) : OStmt` — an inner
/// `while cond { body }` loop with a FLAT body, run for `fuel` guarded iterations via
/// the existing `exec_loop`. This is the constructor that lets the outer body run a
/// dynamic inner loop to completion.
pub const MIRSEM_OSTMT_LOOP: &str = "Trust.MirSem.OStmt.Loop";

/// The auto-derived (simple, non-mutual) recursor for `OStmt`.
pub const MIRSEM_OSTMT_REC: &str = "Trust.MirSem.OStmt.rec";

/// The OUTER statement-list executor `execO : Env → List OStmt → Env` — the
/// `exec`-analogue over `List OStmt`. The `Assign(i, R)` arm threads `set e i
/// (eval_rvalue e R)` (identical to `exec`); the `Loop(cond, body, fuel)` arm threads
/// `exec_loop e cond body fuel` (runs the inner loop to completion). Requires
/// `exec_loop` registered. Carries no non-foundational axiom (`List.rec`/`OStmt.rec`/
/// `set`/`eval_rvalue`/`exec_loop` are all defs).
pub const MIRSEM_EXEC_O: &str = "Trust.MirSem.execO";

/// `stepLoopO : Env → Cond → List OStmt → Env` — ONE guarded OUTER loop iteration,
/// the `stepLoop`-analogue over `execO`: `if eval_cond e cond then execO e body else e`.
pub const MIRSEM_STEP_LOOP_O: &str = "Trust.MirSem.stepLoopO";

/// `exec_loopO : Env → Cond → List OStmt → Nat → Env` — the fuel-indexed OUTER loop,
/// the `exec_loop`-analogue over `stepLoopO`/`execO`. Front-peels via `Nat.rec`.
pub const MIRSEM_EXEC_LOOP_O: &str = "Trust.MirSem.exec_loopO";

/// The OUTER guarded-step invariant-preservation lemma `stepPreservesInvO`
/// (the `stepPreservesInv`-analogue over `stepLoopO`/`execO`): one guarded outer
/// iteration preserves `I` given the `execO`-body preservation hypothesis.
pub const MIRSEM_STEP_PRESERVES_INV_O: &str = "Trust.MirSem.stepPreservesInvO";

/// The OUTER Hoare WHILE rule `loopInvariantRuleO` (the `loopInvariantRule`-analogue
/// over `exec_loopO`/`execO`): `∀ I cond body, (∀ e, I e → eval_cond e cond = true →
/// I (execO e body)) → ∀ n e, I e → I (exec_loopO e cond body n)`. The PARTIAL
/// correctness rule for a loop whose body is `List OStmt` (i.e. may contain an inner
/// loop). Proven by `Nat.rec` on `n`, exactly mirroring `loopInvariantRule`.
pub const MIRSEM_LOOP_INVARIANT_RULE_O: &str = "Trust.MirSem.loopInvariantRuleO";

/// The NESTED-LOOP untouched-local LEMMA `loopKeepsUntouched` — `∀ (cond : Cond)
/// (body : List Stmt)(fuel : Nat)(r : Nat)(c : Int)(e : Env), Eq Int (e r) c →
/// (the inner body never writes `r`) → Eq Int (exec_loop e cond body fuel r) c`. This
/// is the genuinely NEW content: the INNER loop, run for an ARBITRARY (symbolic) fuel,
/// leaves a local `r` it never writes unchanged. It is `loopInvariantRule` instantiated
/// at the inner invariant `Ir := λ e'. Eq Int (e' r) c`, whose preservation is
/// definitional (the inner body's `set` indices all differ from `r`). It is the bridge
/// that lets the OUTER untouched-local invariant survive a completed inner loop.
pub const MIRSEM_LOOP_KEEPS_UNTOUCHED: &str = "Trust.MirSem.loopKeepsUntouched";

// ---- Lemma 1C-cf (CONTROL-FLOW return adequacy) anchor: CmpOp + Cond + eval_cond
// + eval_ite ----
//
// A guarded function returns via a `SwitchInt` over a Bool comparison temp whose
// two arms each assign `_0 := <rvalue>` and converge at a bare `Return` block —
// `if cmp(a,b) { then } else { else }`. The straight-line return model
// (`SemReturn`) does not capture this (the `Return` block carries no `_0 := …`),
// so these were fail-closed. This anchor pins the conditional (if-then-else over a
// comparison) so the CONTROL-FLOW return reflection certifies modulo 3.
/// The MIR comparison-op inductive pinned in Clean (`Lt | Le | Eq | Ne | Gt | Ge`
/// — exactly the integer comparison ops a guard's `BinaryOp(cmp, a, b)` discr temp
/// uses). Each grounds to a Bool-valued, AXIOM-FREE prelude comparison: `Lt`/`Le`
/// to `decide (Int.lt/le …)` via the prelude's `Int.decLt`/`Int.decLe` Decidable
/// instances; `Gt`/`Ge` to the SWAPPED `decide (Int.lt/le …)`; `Eq` to the
/// native-reduced `Int.beq`; `Ne` to `Bool.not (Int.beq …)`. NONE is an `Axiom`
/// (`decide`/`Int.decLt`/`Int.decLe`/`Int.beq`/`Bool.not` are prelude DEFINITIONS /
/// native reducers), so the inductive + `eval_cond` carry no non-foundational axiom.
pub const MIRSEM_CMPOP: &str = "Trust.MirSem.CmpOp";

/// `Lt : CmpOp` — grounds to `decide (Int.lt (eval a) (eval b))`.
pub const MIRSEM_CMPOP_LT: &str = "Trust.MirSem.CmpOp.Lt";

/// `Le : CmpOp` — grounds to `decide (Int.le (eval a) (eval b))`.
pub const MIRSEM_CMPOP_LE: &str = "Trust.MirSem.CmpOp.Le";

/// `Eq : CmpOp` — grounds to `Int.beq (eval a) (eval b)`.
pub const MIRSEM_CMPOP_EQ: &str = "Trust.MirSem.CmpOp.Eq";

/// `Ne : CmpOp` — grounds to `Bool.not (Int.beq (eval a) (eval b))`.
pub const MIRSEM_CMPOP_NE: &str = "Trust.MirSem.CmpOp.Ne";

/// `Gt : CmpOp` — grounds to the SWAPPED `decide (Int.lt (eval b) (eval a))`.
pub const MIRSEM_CMPOP_GT: &str = "Trust.MirSem.CmpOp.Gt";

/// `Ge : CmpOp` — grounds to the SWAPPED `decide (Int.le (eval b) (eval a))`.
pub const MIRSEM_CMPOP_GE: &str = "Trust.MirSem.CmpOp.Ge";

/// The auto-derived recursor for the comparison-op inductive.
pub const MIRSEM_CMPOP_REC: &str = "Trust.MirSem.CmpOp.rec";

/// The MIR-condition inductive pinned in Clean (`Cmp (op : CmpOp) (a b : Operand)`
/// — a single integer comparison, the shape of a guard's discriminant temp).
pub const MIRSEM_COND: &str = "Trust.MirSem.Cond";

/// `Cmp (op : CmpOp) (a b : Operand) : Cond` — the comparison condition.
pub const MIRSEM_COND_CMP: &str = "Trust.MirSem.Cond.Cmp";

/// `And (c1 c2 : Cond) : Cond` — the conjunctive (short-circuit `&&`) guard.
/// ADDITIVE second constructor: it adds the `eval_cond (And c1 c2) = Bool.and …`
/// arm WITHOUT touching `Cmp` or its `eval_cond` arm, so every existing `Cmp`
/// reflexivity/refinement certificate stays byte-identical and def-eq (the new
/// minor premise the recursor gains is simply ignored on a `Cmp` value).
pub const MIRSEM_COND_AND: &str = "Trust.MirSem.Cond.And";

/// `Or (c1 c2 : Cond) : Cond` — Trust: RANGE+DISJUNCTION guard (2026-07-08) — the
/// disjunctive (short-circuit `||`) guard, the CONTROL-FLOW dual of the BitOr-on-Bool
/// VALUE connective: `core`'s `u8::is_ascii_control` (`*self <= 31 || *self == 127`)
/// and `ascii_utils`' `is_space` (`b == 32 || (9 <= b && b <= 13)`) lower the `||` as
/// pure branching (the arms write `_0` directly — no `BitOr` rvalue anywhere), so the
/// guarded-return COND itself must carry the disjunction. ADDITIVE third constructor,
/// the EXACT recipe `And` established: `Cmp`/`And` keep constructor slots 0/1
/// (byte-identical types), the auto-derived recursor gains a THIRD minor premise that
/// existing `Cmp`/`And`-only reductions ignore, so every prior guard certificate stays
/// def-eq. Its `eval_cond` arm folds the two recursor-supplied IHs with `Bool.or` (a
/// prelude definition with a native reducer — no axiom), the exact dual of `And`'s
/// `Bool.and` arm, and `clean_ground::ground_bool` gains the matching `Formula::Or`
/// arm (a left-nested `Bool.or` fold) so the branch refinement (`refinementB`) closes
/// reflexively at the same term from both sides.
pub const MIRSEM_COND_OR: &str = "Trust.MirSem.Cond.Or";

/// The auto-derived recursor for the condition inductive.
pub const MIRSEM_COND_REC: &str = "Trust.MirSem.Cond.rec";

/// The operational condition evaluator `eval_cond : Env → Cond → Bool`.
pub const MIRSEM_EVAL_COND: &str = "Trust.MirSem.eval_cond";

/// The conditional-return evaluator `eval_ite : Env → Cond → Rvalue → Rvalue → Int`
/// — `eval_ite e c t f = (if eval_cond e c then eval_rvalue e t else eval_rvalue e
/// f)`, i.e. `Bool.rec (λ_.Int) (eval_rvalue e f) (eval_rvalue e t) (eval_cond e c)`.
/// This is the if-then-else over a comparison the guarded control-flow return folds.
pub const MIRSEM_EVAL_ITE: &str = "Trust.MirSem.eval_ite";

/// The NESTED-branch (multi-way `if/else if/else`) if-then-else denotation
/// `iteI : Env → Cond → Int → Int → Int` — `iteI e c t f = Bool.rec (λ_:Bool. Int) f
/// t (eval_cond e c)`. ADDITIVE (a new appended definition; nothing existing changes).
/// Unlike `eval_ite` (whose two arms are `Rvalue` SYNTAX), `iteI`'s two arms are
/// already-evaluated `Int`s, so a nested guard's ELSE arm can itself be a (recursive)
/// `iteI` term — the half a multi-way guarded return needs WITHOUT a new `Rvalue`
/// constructor (no recursor-arity change, no env reordering, no 4th axiom). For the
/// depth-1 case `iteI e c (eval_rvalue e t) (eval_rvalue e f)` is DEF-EQ to
/// `eval_ite e c t f`, so the nested refinement is the faithful generalization of
/// `refinementB`. `Bool.rec`/`eval_cond` are prelude / MirSem definitions, so `iteI`
/// carries no non-foundational axiom.
pub const MIRSEM_ITE_I: &str = "Trust.MirSem.iteI";

/// The NESTED-branch substitution denotation, a reducible wrapper over `iteI`, pinned
/// so the nested-branch refinement (`refinementBNested`) connects it to the live
/// grounder. `denote_substitutedBNested e c t f = iteI e c t f`.
pub const MIRSEM_DENOTE_SUBST_B_NESTED: &str = "Trust.MirSem.denote_substitutedBNested";

/// The nested-branch refinement theorem: `∀ x⃗. <nested iteI-tree denotation> =
/// ground_int(nested Ite formula)`, reflexivity-after-reduction (the multi-way analogue
/// of `refinementB`).
pub const MIRSEM_REFINEMENT_B_NESTED: &str = "Trust.MirSem.refinementBNested";

/// Verdict on registering the `MirSem` anchor: did the inductive AND `eval` both
/// kernel-check resting on ONLY the 3 foundational axioms?
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnchorVerdict {
    /// Anchor pinned; inductive + eval both rest on ⊆ the 3 foundational axioms.
    Modulo3,
    /// A declaration carries non-foundational axioms (residue listed).
    Residue(Vec<String>),
    /// The kernel rejected a declaration (should never happen — soundness bug).
    KernelRejected(String),
}

// ---------------------------------------------------------------------------
// Step 2 — Lemma 1A: operand adequacy (each operand form, proven modulo 3)
// ---------------------------------------------------------------------------
/// The scalar-operand fragment `MirSem` models — exactly the operands the
/// reflection's `operand_to_formula` consumes for the SSA-scalar path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemOperand {
    /// `Var idx` — the `idx`-th parameter binding (`Operand::Copy/Move` of a
    /// parameter place in MIR).
    Var(u64),
    /// `Const c` — an integer-literal operand (`Operand::Constant(Int)`).
    Const(i128),
    /// `Move src` — a move out of a sub-operand (`Operand::Move`).
    Move(Box<SemOperand>),
    /// `Index s i` — a SLICE-ELEMENT access `s[i]` (`Operand::Copy/Move` of a place
    /// with a `[Deref, Index(_)]` projection). The element value is UNINTERPRETED —
    /// modeled by the total `idx_elem` (see [`MIRSEM_IDX_ELEM`]); the soundness rests
    /// on the bounds VC + branch refinement, not on the element value.
    Index(Box<SemOperand>, Box<SemOperand>),
    /// `Len s` — a SLICE LENGTH `s.len()` (`PtrMetadata(s)` / `Rvalue::Len`), the `b`
    /// operand of an index guard `i < s.len()`. UNINTERPRETED — modeled by the total
    /// `slice_len` (see [`MIRSEM_SLICE_LEN`]).
    Len(Box<SemOperand>),
    /// Trust: field-read leaf — `Field base fld` — a struct-FIELD READ `(*base).fld`
    /// (a `[Deref, Field(fld)]` place projection on an IMMUTABLE reference parameter,
    /// e.g. `(*self).0`). Modeled by INTENTIONAL REUSE of the SLICE-INDEX carrier
    /// (`to_operand_expr`/`denotation`/`to_formula` desugar to
    /// `Index base (Const fld)`, grounding through the SAME opaque total `idx_elem`
    /// selector `Index`/`Len` already use): a struct-field read and a slice-element
    /// read are the SAME opaque-projection shape at this fidelity — an
    /// UNINTERPRETED, TOTAL, DETERMINISTIC `Int → Int → Int` keyed by (handle,
    /// integer key), asserting NOTHING about the field's VALUE, only that it denotes
    /// SOME Int stably determined by (base, fld). No new Clean declaration: this is a
    /// documentation-level Rust variant over the EXISTING `Index`/`idx_elem` path (a
    /// second, behaviorally-identical opaque symbol would be pure duplication).
    Field(Box<SemOperand>, u64),
    /// Trust: discriminant-guard leaf — `Discriminant base` — an ENUM-TAG READ
    /// (`Rvalue::Discriminant(place)`, the `SwitchInt` guard `Either::is_left`-class
    /// bodies use: `_2 = Discriminant((*_1)); switchInt(_2) -> [0: …, 1: …]`).
    /// Modeled by REUSE of the SAME `Index`/`idx_elem` opaque carrier `Field` reuses
    /// (see its doc) — an UNINTERPRETED, TOTAL, DETERMINISTIC Int value stably
    /// determined by `base`, asserting NOTHING about the tag's actual bit pattern.
    /// This is exactly the right abstraction for a branch guard: the SOUNDNESS of a
    /// discriminant-guarded return rests on the `SwitchInt`'s OWN CFG semantics (which
    /// arm is reached for which tag value), never on the tag's concrete value.
    ///
    /// Keyed at the RESERVED literal [`MIRSEM_DISCRIMINANT_TAG_KEY`] (`-1`) — a key no
    /// real `Field(fld: u64)` read can EVER produce (`fld` is unsigned, always ≥ 0), so
    /// a function that ALSO reads a real field 0 on the SAME base (`(*self).0` on a
    /// non-enum struct, via `sem_field_read_operand`) is never mis-equated with this
    /// discriminant read — the two carriers are provably disjoint BY CONSTRUCTION, not
    /// by convention. (In practice the two recognizers never fire on the same operand
    /// anyway: `sem_field_read_operand` requires a literal `[Deref, Field(fld)]`
    /// projection, `Discriminant` requires the dedicated `Rvalue::Discriminant`
    /// constructor — but the disjoint key is a belt-and-suspenders soundness margin,
    /// not the only thing preventing collision.)
    Discriminant(Box<SemOperand>),
    /// Trust: CAST-TEMP GUARD READ (2026-07-08) — `Cast base dest_width
    /// dest_signed` — a NARROWING (or signedness-REINTERPRETING) integer CAST
    /// `_2 := Cast(base_op, dest_ty)` used as a GUARD operand (`_2 = _1 as u8;
    /// <guard reads _2>` — the `<char as Check>::{is_control,is_extended,
    /// is_printable,is_us_ascii}` shape, `ascii_utils` 0.9.3: `self : char` is
    /// ALREADY `Ty::Int{width:32,signed:false}` in this IR, so a `char`-source
    /// cast is the SAME `Ty::Int` shape as an `int`-source cast — one arm
    /// covers both).
    ///
    /// A narrowing/reinterpreting cast is NOT value-preserving (unlike the
    /// WIDENING, same-signedness case [`resolve_widening_cast_rvalue`] already
    /// models as the exact identity) — claiming an exact arithmetic relationship
    /// here would be dishonest. Instead this REUSES the SAME opaque
    /// `Index`/`idx_elem` carrier `Field`/`Discriminant` already establish as a
    /// sound, honest fidelity tier (see their docs): an UNINTERPRETED, TOTAL,
    /// DETERMINISTIC function of the resolved source — `to_operand_expr`/
    /// `denotation`/`to_formula` desugar to `Index base (Const key)`,
    /// grounding through the EXISTING opaque `idx_elem` selector. ZERO new
    /// Clean declaration (a second, behaviorally-identical opaque symbol would
    /// be pure duplication — see [`mirsem_cast_tag_key`] for the reserved,
    /// per-`(dest_width, dest_signed)` disjoint key).
    ///
    /// The soundness content proven for a guard built from this carrier is:
    /// "the function's control flow is a deterministic function of `base`'s
    /// real value, matching the exact branch structure" — it does NOT assert
    /// the cast's numeric relationship (e.g. `cast_value == base mod 256`).
    /// Honest and never a false certificate; simply a WEAKER claim than the
    /// widening case's exact identity.
    Cast(Box<SemOperand>, u64, bool),
    /// A pure unary operation materialized into a call-argument temporary.
    /// `Not` denotes `Int.xor base (-1)` and `Neg` denotes `Int.sub 0 base`;
    /// both use dedicated kernel-checked Operand constructors whose evaluator
    /// reduces to the same term emitted by the live grounder.
    PreOp(Box<SemOperand>, SemPreOp),
    /// Trust: ITER-NEXT VALUE-PATH (2026-07-21) — the ENTRY-TIME REMAINING-REGION
    /// HANDLE `iter_region(param)` of the pinned `&mut core::slice::iter::Iter`
    /// parameter `param` (0-based). The abstract `[cursor..end]` sequence at function
    /// ENTRY whose element-0 value-slot is the reference `<Iter as Iterator>::next`
    /// returns in its `Some` arm. Denoted through the trust-ir witness's
    /// `trustir_adt::sem_operand_to_expr` (which maps it to the `Trust.MirSem.iter_region`
    /// OPAQUE — a total `Int → Int` handle constructor, `Declaration::Opaque` with EMPTY
    /// axiom_deps, the SAME honesty tier as `idxElem`/`sliceLen`), where it appears ONLY
    /// as the base of an `Index(IterRegion(p), Const 0)` payload — `idxElem(iter_region(e
    /// p), 0)`. It is MINTED ONLY by `clean_ground::sem_iter_next_shape_of` and consumed
    /// ONLY by that witness path; every other `SemOperand` consumer (the MirSem
    /// self-denotation lane, the guarded-return grounder, the opaque-call chain) treats
    /// it as a FAIL-CLOSED / never-reached carrier (see each arm) so an entry-time-indexed
    /// iterator handle can NEVER leak into a non-iter lane or be composed across a call
    /// site (GATE-ITER-REGION-NO-CROSS-INSTANTIATION). ENTRY-TIME by recognizer
    /// discipline only — the Clean side cannot express the time index, so the handle is
    /// single-Env-local and NON-COMPOSABLE by mechanism.
    IterRegion(u64),
}

/// Pure, total unary pre-operations admitted for call arguments. Logical Bool
/// negation and unsigned arithmetic negation are deliberately outside the lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemPreOp {
    /// Integer bitwise complement, modeled exactly as xor with all ones.
    Not,
    /// Signed integer arithmetic negation, modeled exactly as `0 - base`.
    Neg,
}

/// Trust: discriminant-guard leaf — the RESERVED opaque-carrier key
/// [`SemOperand::Discriminant`] uses, chosen to be UNREACHABLE by any real
/// `SemOperand::Field(_, fld: u64)` (whose `fld` is unsigned, always ≥ 0). See
/// [`SemOperand::Discriminant`]'s doc for the disjointness argument.
///
/// Trust: DISCRIMINANT-SWITCH ADT-RETURN (M5 residue #1, 2026-07-08) —
/// widened to `pub(crate)` (value unchanged) so `trustir_adt::sem_operand_to_expr`
/// can denote a `SemOperand::Discriminant` GUARD operand through the SAME
/// reserved key `idx_elem` carrier this file's own `denotation`/`to_formula`
/// already use — the SAME widening rationale as `sem_operand_to_expr`'s own
/// `pub(crate)` (a second, behaviorally-identical reserved-key constant would
/// be pure duplication).
pub(crate) const MIRSEM_DISCRIMINANT_TAG_KEY: i128 = -1;

impl SemOperand {
    /// The Clean syntax term for this operand: a closed `Trust.MirSem.Operand`
    /// value built from the constructors. This is the `O` in Lemma 1A.
    fn to_operand_expr(&self) -> Expr {
        match self {
            SemOperand::Var(p) => Expr::app(cst(MIRSEM_OPERAND_VAR), Expr::nat_lit(*p)),
            SemOperand::Const(c) => Expr::app(cst(MIRSEM_OPERAND_CONST), int_lit(*c)),
            SemOperand::Move(src) => Expr::app(cst(MIRSEM_OPERAND_MOVE), src.to_operand_expr()),
            SemOperand::Index(s, i) => {
                Expr::apps(cst(MIRSEM_OPERAND_INDEX), [s.to_operand_expr(), i.to_operand_expr()])
            }
            SemOperand::Len(s) => Expr::app(cst(MIRSEM_OPERAND_LEN), s.to_operand_expr()),
            // Trust: field-read leaf — REUSE `Operand.Index base (Operand.Const fld)`
            // (see the `Field` variant doc): no new Clean constructor.
            SemOperand::Field(base, fld) => Expr::apps(
                cst(MIRSEM_OPERAND_INDEX),
                [base.to_operand_expr(), SemOperand::Const(i128::from(*fld)).to_operand_expr()],
            ),
            // Trust: discriminant-guard leaf — REUSE `Operand.Index base (Operand.Const
            // -1)` (see the `Discriminant` variant doc): no new Clean constructor.
            SemOperand::Discriminant(base) => Expr::apps(
                cst(MIRSEM_OPERAND_INDEX),
                [
                    base.to_operand_expr(),
                    SemOperand::Const(MIRSEM_DISCRIMINANT_TAG_KEY).to_operand_expr(),
                ],
            ),
            // Trust: CAST-TEMP GUARD READ — REUSE `Operand.Index base (Operand.Const
            // key)` (see the `Cast` variant doc): no new Clean constructor.
            SemOperand::Cast(base, dw, ds) => Expr::apps(
                cst(MIRSEM_OPERAND_INDEX),
                [
                    base.to_operand_expr(),
                    SemOperand::Const(mirsem_cast_tag_key(*dw, *ds)).to_operand_expr(),
                ],
            ),
            SemOperand::PreOp(base, SemPreOp::Not) => {
                Expr::app(cst(MIRSEM_OPERAND_PREOP_NOT), base.to_operand_expr())
            }
            SemOperand::PreOp(base, SemPreOp::Neg) => {
                Expr::app(cst(MIRSEM_OPERAND_PREOP_NEG), base.to_operand_expr())
            }
            // Trust: ITER-NEXT VALUE-PATH — an entry-time iterator-region handle has NO
            // representation in the `Trust.MirSem.Operand` SYNTAX (it is denoted ONLY on
            // the trust-ir witness side via `trustir_adt::sem_operand_to_expr`, keyed to
            // the `Trust.MirSem.iter_region` opaque). This MirSem self-denotation is NEVER
            // reached for an `IterRegion` carrier (it is minted only by
            // `sem_iter_next_shape_of` into a `SemAdtReturn` consumed by the trust-ir
            // lane), so this arm is a FAIL-CLOSED POISON: a reference to an undeclared
            // constant that the kernel would reject (`UnknownConst`) rather than mint a
            // false Operand syntax value.
            SemOperand::IterRegion(_) => cst("Trust.MirSem.Operand.__iter_region_trustir_witness_only"),
        }
    }

    /// The GROUNDED REFLECTION denotation `E_O` under an environment `e` — the
    /// exact `Int` term `ground_int(operand_to_formula(O))` produces (a parameter
    /// `Var p` grounds to the env value `e p`; a `Const c` to `int_lit c`; a `Move
    /// src` to the referent's denotation). This is the term Lemma 1A claims equals
    /// `eval e O`.
    ///
    /// `e_ref` is the de-Bruijn term denoting the environment `e` in the current
    /// context (so the caller controls the binder depth).
    fn denotation(&self, e_ref: &Expr) -> Expr {
        match self {
            // The reflection grounds a parameter operand to the env binding at its
            // index: `operand_to_formula → Formula::Var(name)`; `ground_int` looks
            // the name up in the parameter map, whose value (by construction) is the
            // p-th binding. In MirSem's `Env = Nat → Int` that is exactly `e p`.
            SemOperand::Var(p) => Expr::app(e_ref.clone(), Expr::nat_lit(*p)),
            // `operand_to_formula → Formula::Int(c)`; `ground_int → int_lit_to_expr(c)`.
            SemOperand::Const(c) => int_lit(*c),
            // `operand_to_formula(Move src) = operand_to_formula(src)` (the move is
            // transparent to the scalar value), so the denotation is the referent's.
            SemOperand::Move(src) => src.denotation(e_ref),
            // `operand_to_formula(Index s i) = Formula::Select(s, i)`; `ground_int`
            // grounds `Select` to `idx_elem (g s) (g i)` — exactly what
            // `eval e (Index s i)` reduces to (the `idx_elem` opaque, byte-identical).
            SemOperand::Index(s, i) => {
                Expr::apps(cst(MIRSEM_IDX_ELEM), [s.denotation(e_ref), i.denotation(e_ref)])
            }
            // `operand_to_formula(Len s) = Formula::Pred("…len…", [s])`-shaped; grounds
            // to `slice_len (g s)` — exactly what `eval e (Len s)` reduces to.
            SemOperand::Len(s) => Expr::app(cst(MIRSEM_SLICE_LEN), s.denotation(e_ref)),
            // Trust: field-read leaf — `idx_elem (g base) fld` (the SAME opaque
            // selector `Index` denotes through, applied at the literal field key).
            SemOperand::Field(base, fld) => Expr::apps(
                cst(MIRSEM_IDX_ELEM),
                [base.denotation(e_ref), int_lit(i128::from(*fld))],
            ),
            // Trust: discriminant-guard leaf — `idx_elem (g base) -1` (the SAME opaque
            // selector `Index`/`Field` denote through, applied at the reserved tag key).
            SemOperand::Discriminant(base) => Expr::apps(
                cst(MIRSEM_IDX_ELEM),
                [base.denotation(e_ref), int_lit(MIRSEM_DISCRIMINANT_TAG_KEY)],
            ),
            // Trust: CAST-TEMP GUARD READ — `idx_elem (g base) key` (the SAME opaque
            // selector `Index`/`Field`/`Discriminant` denote through, applied at the
            // reserved per-`(width, signed)` cast key).
            SemOperand::Cast(base, dw, ds) => Expr::apps(
                cst(MIRSEM_IDX_ELEM),
                [base.denotation(e_ref), int_lit(mirsem_cast_tag_key(*dw, *ds))],
            ),
            SemOperand::PreOp(base, SemPreOp::Not) => {
                Expr::apps(cst("Int.xor"), [base.denotation(e_ref), int_lit(-1)])
            }
            SemOperand::PreOp(base, SemPreOp::Neg) => Expr::apps(
                cst("Int.sub"),
                [Expr::app(cst("Int.ofNat"), Expr::nat_lit(0)), base.denotation(e_ref)],
            ),
            // Trust: ITER-NEXT VALUE-PATH — the MirSem GROUNDED denotation is NEVER
            // reached for an `IterRegion` carrier (see `to_operand_expr`'s arm). The
            // entry-time handle is denoted ONLY on the trust-ir side (`Trust.MirSem.
            // iter_region (e p)`); here it is a FAIL-CLOSED POISON const so any accidental
            // MirSem-anchor use is `UnknownConst`-rejected, never a false Int denotation.
            SemOperand::IterRegion(_) => cst("Trust.MirSem.Operand.__iter_region_trustir_witness_only"),
        }
    }

    /// The `trust_types::Formula` this operand reflects to — EXACTLY what
    /// `clean_ground::operand_to_formula` produces for the same MIR operand:
    ///   * `Var p`   → `Formula::Var(var_name(p), Int)` — a parameter is a free
    ///     variable named by its index (`operand_to_formula` keys parameters by name;
    ///     we use the canonical `var_name(p)`, and the GROUNDER-CONNECTED adequacy
    ///     binds that SAME name to its de-Bruijn binder, so the round-trip is exact).
    ///   * `Const c` → `Formula::Int(c)`.
    ///   * `Move src`→ `operand_to_formula(src)` (the move is transparent to the
    ///     scalar value — `operand_to_formula` resolves `Operand::Move` to the place's
    ///     formula).
    ///
    /// This is the bridge into the LIVE `clean_ground::ground_int`: grounding
    /// `O.to_formula()` through the live grounder yields the term the §6 reflection
    /// pipeline ACTUALLY produces for this operand.
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::{Formula as F, Sort};
        match self {
            SemOperand::Var(p) => F::Var(var_name(*p), Sort::Int),
            SemOperand::Const(c) => F::Int(*c),
            SemOperand::Move(src) => src.to_formula(),
            // A slice-element access reflects to `Formula::Select(slice, idx)` — the
            // array-read shape `clean_ground::ground_int` grounds to `idx_elem (g
            // slice) (g idx)`, byte-identical to `eval (Index s i)`'s reduct.
            SemOperand::Index(s, i) => {
                F::Select(Box::new(s.to_formula()), Box::new(i.to_formula()))
            }
            // A slice length reflects to the UNINTERPRETED unary `Pred` keyed by the
            // canonical `slice_len` name — `clean_ground::ground_int` grounds THIS
            // specific Pred to `slice_len (g slice)`, byte-identical to `eval (Len s)`.
            SemOperand::Len(s) => {
                F::Pred(trust_types::Symbol::intern(MIRSEM_SLICE_LEN), vec![s.to_formula()])
            }
            // Trust: field-read leaf — reflects EXACTLY like `Index base (Const
            // fld)`: `Formula::Select(base, Int(fld))`, which `clean_ground::ground_int`
            // ALREADY grounds to `idx_elem (g base) (g fld)` (the existing Select arm,
            // untouched) — so this is grounder-connected with ZERO new `ground_int` arm.
            SemOperand::Field(base, fld) => {
                F::Select(Box::new(base.to_formula()), Box::new(F::Int(i128::from(*fld))))
            }
            // Trust: discriminant-guard leaf — reflects EXACTLY like `Index base (Const
            // -1)`: `Formula::Select(base, Int(-1))`, which `clean_ground::ground_int`
            // ALREADY grounds via its existing `Select` arm — grounder-connected with
            // ZERO new `ground_int` arm.
            SemOperand::Discriminant(base) => F::Select(
                Box::new(base.to_formula()),
                Box::new(F::Int(MIRSEM_DISCRIMINANT_TAG_KEY)),
            ),
            // Trust: CAST-TEMP GUARD READ — reflects EXACTLY like `Index base (Const
            // key)`: `Formula::Select(base, Int(key))`, which `clean_ground::ground_int`
            // ALREADY grounds via its existing `Select` arm — grounder-connected with
            // ZERO new `ground_int` arm.
            SemOperand::Cast(base, dw, ds) => F::Select(
                Box::new(base.to_formula()),
                Box::new(F::Int(mirsem_cast_tag_key(*dw, *ds))),
            ),
            SemOperand::PreOp(base, SemPreOp::Not) => {
                F::Pred(trust_types::Symbol::intern("Int.xor"), vec![base.to_formula(), F::Int(-1)])
            }
            SemOperand::PreOp(base, SemPreOp::Neg) => F::Neg(Box::new(base.to_formula())),
            // Trust: ITER-NEXT VALUE-PATH — the honest OPAQUE handle Pred
            // `Trust.MirSem.iter_region(param)`. This MirSem-lane `Formula` is never
            // grounded on the verdict path (the certificate rides the trust-ir witness,
            // not `ground_int`); `clean_ground::ground_int` has NO `iter_region` Pred arm,
            // so if this ever reached the MirSem grounder it FALLS THROUGH to `None`
            // (fail-closed) — never a false Int denotation.
            SemOperand::IterRegion(p) => F::Pred(
                trust_types::Symbol::intern("Trust.MirSem.iter_region"),
                vec![F::Var(var_name(*p), trust_types::Sort::Int)],
            ),
        }
    }

    /// The distinct parameter indices this operand references (through transparent
    /// moves), in first-appearance order — the variables the grounder-connected
    /// adequacy binds as `Int` binders.
    fn var_indices(&self, out: &mut Vec<u64>) {
        match self {
            SemOperand::Var(p) => {
                if !out.contains(p) {
                    out.push(*p);
                }
            }
            SemOperand::Const(_) => {}
            SemOperand::Move(src) => src.var_indices(out),
            // Both the slice operand and the index operand contribute their indices,
            // in first-appearance order (slice first, matching the formula nesting).
            SemOperand::Index(s, i) => {
                s.var_indices(out);
                i.var_indices(out);
            }
            SemOperand::Len(s) => s.var_indices(out),
            // Trust: field-read leaf — only the base contributes (the field index is
            // a closed literal, like `Index`'s slice/index pair contributes both but
            // `Field`'s `fld` is not itself a `SemOperand`).
            SemOperand::Field(base, _fld) => base.var_indices(out),
            // Trust: discriminant-guard leaf — only the base contributes (the reserved
            // tag key is a closed literal, not itself a `SemOperand`).
            SemOperand::Discriminant(base) => base.var_indices(out),
            // Trust: CAST-TEMP GUARD READ — only the base contributes (the reserved
            // cast key is a closed literal, not itself a `SemOperand`).
            SemOperand::Cast(base, _dw, _ds) => base.var_indices(out),
            // The operation kind and its closed -1/0 literals add no variables.
            SemOperand::PreOp(base, _kind) => base.var_indices(out),
            // Trust: ITER-NEXT VALUE-PATH — the handle references exactly its own pinned
            // `&mut Iter` parameter index (the SAME index the guard's `IterHasNext(p)`
            // carries; coherence enforces they match).
            SemOperand::IterRegion(p) => {
                if !out.contains(p) {
                    out.push(*p);
                }
            }
        }
    }
}

/// Verdict of checking Lemma 1A for one operand form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdequacyVerdict {
    /// PROVEN modulo 3: `∀(e:Env). eval e O = E_O` kernel-checks and its axiom
    /// closure is ⊆ the 3 foundational axioms.
    ProvenModulo3,
    /// Type-checks, but the proof depends on these non-foundational axioms.
    Residue(Vec<String>),
    /// The kernel rejected the adequacy proof — the claim is NOT proven (this is
    /// the fail-closed outcome for a wrong claim, and a soundness bug for a true one).
    KernelRejected(String),
}

// ---------------------------------------------------------------------------
// Step 2B — Lemma 1B: rvalue adequacy (Use + Add/Sub/Mul, proven modulo 3)
// ---------------------------------------------------------------------------
/// The arithmetic binops `MirSem` models — the binops whose grounded shape
/// is a clean `Int.<op>` term `ground_int` emits: `Add`/`Sub`/`Mul` (grounding to
/// the reducible `Int.add`/`sub`/`mul`), `Div` (grounding to the prelude's
/// `Opaque` `Int.div`, `ground_int`'s `F::Div` arm), and — Trust: witness-tier Rem
/// arm — `Rem` (grounding to the prelude's `Opaque` TRUNCATED `Int.mod`,
/// `ground_int`'s `F::Rem` arm from the M3 Rem promotion). Shift/bitwise binops
/// are bitvector-grounded, still out of fragment (fail-closed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemBinOp {
    /// `+` — grounds to `Int.add`.
    Add,
    /// `-` — grounds to `Int.sub`.
    Sub,
    /// `*` — grounds to `Int.mul`.
    Mul,
    /// `/` — grounds to the prelude's `Opaque` (native-reduced, non-axiom)
    /// `Int.div`, EXACTLY `ground_int`'s `F::Div(a,b) => app2("Int.div", …)` arm.
    Div,
    /// `%` — Trust: witness-tier Rem arm — grounds to the prelude's `Opaque`
    /// (native-reduced, non-axiom) TRUNCATED remainder `Int.mod` (round toward
    /// zero, sign follows the dividend — rustc's `%`), EXACTLY `ground_int`'s
    /// `F::Rem(a,b) => app2("Int.mod", …)` arm.
    Rem,
    /// Trust: BITWISE SHAPE LANE (2026-07-08) — `&` on GENUINE `Int` operands
    /// (never the Bool-connective `&&`-on-bool `BitOr`/`BitAnd` opcode reuse —
    /// see `mir_operand_is_bool_typed`'s gate, tried FIRST) — grounds to a NEW
    /// `Opaque` (native-reduced by the SAME `Int.div`/`Int.mod` discipline,
    /// non-axiom) `Int.land`, the EXACT spelling `trustir_bridge.rs`'s kernel
    /// bridge already proves wrapped-semantics agreement for.
    BitAnd,
    /// `|` on GENUINE `Int` operands — grounds to the Opaque `Int.lor`.
    BitOr,
    /// `^` on GENUINE `Int` operands — grounds to the Opaque `Int.xor`.
    BitXor,
    /// `<<` — grounds to the Opaque `Int.shiftLeft` (the UNBOUNDED `a * 2^n`
    /// denotation; overflow/truncation to the destination WIDTH is a SEPARATE
    /// concern the shift-overflow VC already carries — see the mission report's
    /// "shift-by-param overflow VC honest" probe).
    Shl,
    /// `>>` on an UNSIGNED shifted value — Trust: M6 rung 6, UNSIGNED-Shr arm
    /// (the bitwise shape lane's own named `Shr` residue, closed for the
    /// unsigned fragment). Grounds to the Opaque `Int.shiftRight`. UNSIGNED
    /// `x >> n` is the logical shift `x / 2^n` — for `x ≥ 0` (guaranteed by
    /// the UNSIGNED-ONLY admission gate in [`sem_rvalue_of_mir_at_depth`])
    /// the unbounded `Int` denotation coincides EXACTLY with the machine
    /// value (no overflow, no truncation — unlike `Shl`). A SIGNED `>>`
    /// (arithmetic shift, floor semantics on negatives) is NOT admitted —
    /// fail-closed at the gate, never a false certificate.
    Shr,
}

impl SemBinOp {
    /// The closed `Trust.MirSem.BinOp` constructor value for this op.
    fn to_binop_expr(self) -> Expr {
        cst(match self {
            SemBinOp::Add => MIRSEM_BINOP_ADD,
            SemBinOp::Sub => MIRSEM_BINOP_SUB,
            SemBinOp::Mul => MIRSEM_BINOP_MUL,
            SemBinOp::Div => MIRSEM_BINOP_DIV,
            // Trust: witness-tier Rem arm.
            SemBinOp::Rem => MIRSEM_BINOP_REM,
            // Trust: BITWISE SHAPE LANE.
            SemBinOp::BitAnd => MIRSEM_BINOP_BITAND,
            SemBinOp::BitOr => MIRSEM_BINOP_BITOR,
            SemBinOp::BitXor => MIRSEM_BINOP_BITXOR,
            SemBinOp::Shl => MIRSEM_BINOP_SHL,
            // Trust: M6 rung 6, UNSIGNED-Shr arm.
            SemBinOp::Shr => MIRSEM_BINOP_SHR,
        })
    }
}

/// The rvalue fragment `MirSem` models — exactly the rvalue forms
/// `extract_return_formula` / `resolve_local_value` reflect to a scalar `Formula`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemRvalue {
    /// `Use op` — a direct operand use (`Rvalue::Use`).
    Use(SemOperand),
    /// `Bin op a b` — a binary arithmetic rvalue (`Rvalue::BinaryOp` /
    /// `CheckedBinaryOp`, field 0).
    Bin(SemBinOp, SemOperand, SemOperand),
    /// `Sel c a b` — the CONDITIONAL-UPDATE rvalue `if c then a else b` (Trust: Step 6CU,
    /// the `max_scan`-shape conditional accumulator update `m := if i > m { i } else { m }`).
    /// Grounds (via `Rvalue.Sel`/`eval_rvalue`) to `iteI e c (eval e a) (eval e b)`, the
    /// `Bool.rec` case-split over the update condition `c`. ONLY the loop-body
    /// (`body_list_expr` → `to_rvalue_expr`) path uses this variant — the straight-line
    /// adequacy paths (`denotation`/`to_formula`) are never invoked for a conditional update.
    Sel(SemCond, SemOperand, SemOperand),
    /// Trust: COMPARE-AS-VALUE — `Cmp op ra rb`, a comparison used as a Bool-typed
    /// VALUE (not a `SwitchInt` guard): `_0 := Eq(_2, 0); return _0`. RECURSIVE in
    /// `ra`/`rb` (the SAME shape `Cond.And` established for `Cond`) so a side that
    /// is itself a computed temp (`_2 := Rem(_1, 2)`) is INLINED as a nested
    /// `SemRvalue`, never left as a bare cross-reference to a non-parameter local.
    Cmp(SemCmpOp, Box<SemRvalue>, Box<SemRvalue>),
    /// Trust: BOOL-CONNECTIVE (BitOr-on-Bool multi-join, 2026-07-08) — `Or ra rb`,
    /// a `bool | bool` VALUE (`_a := cmp1; _b := cmp2; _0 := BitOr(_a, _b)`).
    /// RECURSIVE in `ra`/`rb` (the SAME shape `Cmp` established) — a side that is
    /// itself a nested comparison or ANOTHER `Or`/`And` inlines the SAME way `Cmp`'s
    /// sides do. Fail-closed at construction time on a non-`Bool`-typed MIR operand
    /// (never built from anything else — see `mir_operand_is_bool_typed`).
    Or(Box<SemRvalue>, Box<SemRvalue>),
    /// The `&&`-flavored twin of [`SemRvalue::Or`] (`bool & bool`).
    And(Box<SemRvalue>, Box<SemRvalue>),
    /// Trust: BIT_FIELD NESTED-RVALUE (2026-07-08) — `BitBin op ra rb`, a
    /// bitwise/shift rvalue (`BitAnd`/`BitOr`/`BitXor`/`Shl`) whose operand(s)
    /// can themselves be a NESTED computed rvalue — `bit_field::get_bit`'s
    /// `(*self & (1 << bit)) != 0` shape, where `BitAnd`'s second operand is
    /// itself a computed `Shl(1, bit)` rvalue. RECURSIVE in `ra`/`rb` (the SAME
    /// op-parameterized recursive pattern [`SemRvalue::Cmp`] established).
    /// Built ONLY when the flat [`SemRvalue::Bin`] resolution (both operands
    /// atomic) declines on at least one side — see
    /// `sem_rvalue_of_mir_at_depth`'s bitwise arm — so every prior FLAT
    /// bitwise certificate is untouched.
    BitBin(SemBinOp, Box<SemRvalue>, Box<SemRvalue>),
    /// Trust: W-CMP-DISCR (2026-07-16) — `ArithBin op ra rb`, an ARITHMETIC
    /// (`+`/`-`/`*`) rvalue whose operand(s) can themselves be a NESTED computed
    /// rvalue — the ARITHMETIC twin of [`SemRvalue::BitBin`] (built the same
    /// recursive way, `BinOp` op-parameterized). The `signum` normalization: the
    /// three-way sign `(self > 0) - (self < 0)` is a `Sub` combining two computed
    /// `Cmp` sub-rvalues that the flat [`SemRvalue::Bin`]'s atomic-operand slots
    /// cannot represent. Reflects (`to_formula`) to the NATIVE `F::Add`/`F::Sub`/
    /// `F::Mul` (like the flat `Bin`), NOT the opaque `F::Pred` `BitBin` uses — so
    /// the grounder emits the SAME `Int.<op>` term `eval_rvalue`'s `ArithBin` arm
    /// reduces to, and adequacy closes reflexively. Built ONLY by the fail-closed
    /// `signum` recognizer ([`resolve_signum_ordering_sign`]), always `op = Sub`
    /// over two `Cmp` children.
    ArithBin(SemBinOp, Box<SemRvalue>, Box<SemRvalue>),
}

impl SemRvalue {
    /// The Clean syntax term for this rvalue: a closed `Trust.MirSem.Rvalue` value.
    fn to_rvalue_expr(&self) -> Expr {
        match self {
            SemRvalue::Use(op) => Expr::app(cst(MIRSEM_RVALUE_USE), op.to_operand_expr()),
            SemRvalue::Bin(op, a, b) => Expr::apps(
                cst(MIRSEM_RVALUE_BIN),
                [op.to_binop_expr(), a.to_operand_expr(), b.to_operand_expr()],
            ),
            // `Sel c a b` → `Rvalue.Sel (Cond.Cmp …) a b` — the conditional-update syntax;
            // `eval_rvalue` reduces this to `iteI e c (eval e a) (eval e b)`.
            SemRvalue::Sel(c, a, b) => Expr::apps(
                cst(MIRSEM_RVALUE_SEL),
                [c.to_cond_expr(), a.to_operand_expr(), b.to_operand_expr()],
            ),
            // Trust: COMPARE-AS-VALUE — `Rvalue.Cmp op ra rb`, RECURSIVE in the two
            // `Rvalue` sub-terms (mirrors `Cond.And`'s own recursive syntax).
            SemRvalue::Cmp(op, ra, rb) => Expr::apps(
                cst(MIRSEM_RVALUE_CMP),
                [op.to_cmpop_expr(), ra.to_rvalue_expr(), rb.to_rvalue_expr()],
            ),
            // Trust: BOOL-CONNECTIVE — `Rvalue.Or/And ra rb`, RECURSIVE in the two
            // `Rvalue` sub-terms (mirrors `Cmp`'s own recursive syntax exactly).
            SemRvalue::Or(ra, rb) => {
                Expr::apps(cst(MIRSEM_RVALUE_OR), [ra.to_rvalue_expr(), rb.to_rvalue_expr()])
            }
            SemRvalue::And(ra, rb) => {
                Expr::apps(cst(MIRSEM_RVALUE_AND), [ra.to_rvalue_expr(), rb.to_rvalue_expr()])
            }
            // Trust: BIT_FIELD NESTED-RVALUE — `Rvalue.BitBin op ra rb`,
            // RECURSIVE in the two `Rvalue` sub-terms (mirrors `Cmp`'s own
            // recursive syntax, op-parameterized the SAME way).
            SemRvalue::BitBin(op, ra, rb) => Expr::apps(
                cst(MIRSEM_RVALUE_BITBIN),
                [op.to_binop_expr(), ra.to_rvalue_expr(), rb.to_rvalue_expr()],
            ),
            // Trust: W-CMP-DISCR — `Rvalue.ArithBin op ra rb`, RECURSIVE in the
            // two `Rvalue` sub-terms (mirrors `BitBin`'s syntax, same
            // op-parameterization).
            SemRvalue::ArithBin(op, ra, rb) => Expr::apps(
                cst(MIRSEM_RVALUE_ARITHBIN),
                [op.to_binop_expr(), ra.to_rvalue_expr(), rb.to_rvalue_expr()],
            ),
        }
    }

    /// The GROUNDED REFLECTION denotation under `e` — the exact `Int` term
    /// `ground_int(<reflected rvalue formula>)` produces. `Use op` grounds to the
    /// operand's denotation; `Bin op a b` grounds to `Int.<op> (denot a) (denot b)`,
    /// the EXACT `app2("Int.add"/"Int.sub"/"Int.mul"/"Int.div"/"Int.mod", g(a), g(b))`
    /// shape `ground_int` emits for `Formula::Add`/`Sub`/`Mul`/`Div`/`Rem`. This is
    /// the term Lemma 1B claims equals `eval_rvalue e R`.
    fn denotation(&self, e_ref: &Expr) -> Expr {
        match self {
            SemRvalue::Use(op) => op.denotation(e_ref),
            SemRvalue::Bin(op, a, b) => {
                int_binop_expr(op, a.denotation(e_ref), b.denotation(e_ref))
            }
            // The `Sel` denotation grounds to `iteI e c (denot a) (denot b)` — the same
            // term `eval_rvalue e (Sel c a b)` reduces to. Only exercised if a conditional
            // update ever entered a straight-line adequacy claim (it does not today: the
            // conditional-update path uses ONLY `to_rvalue_expr` in the loop body), but we
            // keep the denotation faithful rather than panic.
            SemRvalue::Sel(c, a, b) => Expr::apps(
                cst(MIRSEM_ITE_I),
                [e_ref.clone(), c.to_cond_expr(), a.denotation(e_ref), b.denotation(e_ref)],
            ),
            // Trust: COMPARE-AS-VALUE — grounds to `bool_as_int(cmp_bool_expr(op,
            // ra.denotation, rb.denotation))`, the SAME "Bool is the opaque Int 0/1
            // carrier" encoding `sem_call_then_pureop_of_mir`'s `Cmp` arm already
            // establishes, applied here to the two NESTED sub-rvalue denotations
            // rather than a call result / bare operand.
            SemRvalue::Cmp(op, ra, rb) => {
                bool_as_int(cmp_bool_expr(*op, ra.denotation(e_ref), rb.denotation(e_ref)))
            }
            // Trust: BOOL-CONNECTIVE — PURE ARITHMETIC on the 0/1 `Int` encoding
            // (`And := a*b`, `Or := a+b-a*b`), mirroring `eval_rvalue`'s kernel-side
            // `or_case`/`and_case` EXACTLY — see that case's doc for why a
            // `Bool.rec`/decide round-trip does NOT work here (it is NOT def-eq to
            // what the live grounder's `to_formula` independently computes).
            SemRvalue::And(ra, rb) => {
                Expr::apps(cst("Int.mul"), [ra.denotation(e_ref), rb.denotation(e_ref)])
            }
            SemRvalue::Or(ra, rb) => {
                let a = ra.denotation(e_ref);
                let b = rb.denotation(e_ref);
                let sum = Expr::apps(cst("Int.add"), [a.clone(), b.clone()]);
                let prod = Expr::apps(cst("Int.mul"), [a, b]);
                Expr::apps(cst("Int.sub"), [sum, prod])
            }
            // Trust: BIT_FIELD NESTED-RVALUE — grounds to `Int.<op> (denot ra)
            // (denot rb)`, EXACTLY `int_binop_expr`'s shape (reused verbatim,
            // recursing on the two sub-rvalues' OWN denotations instead of a
            // bare operand's) — the term `eval_rvalue e (BitBin op ra rb)`
            // reduces to via the new `BinOp.rec`-dispatched `bitbin_case`.
            SemRvalue::BitBin(op, ra, rb) => {
                int_binop_expr(op, ra.denotation(e_ref), rb.denotation(e_ref))
            }
            // Trust: W-CMP-DISCR — grounds to `Int.<op> (denot ra) (denot rb)`,
            // the EXACT `int_binop_expr` shape (reused verbatim, recursing on the
            // two sub-rvalues' OWN denotations) — the term `eval_rvalue e
            // (ArithBin op ra rb)` reduces to via the `BinOp.rec`-dispatched
            // `arithbin_case`. For `Sub` this is `Int.sub (denot ra) (denot rb)`,
            // BYTE-IDENTICAL to what `to_formula`'s `F::Sub` grounds to.
            SemRvalue::ArithBin(op, ra, rb) => {
                int_binop_expr(op, ra.denotation(e_ref), rb.denotation(e_ref))
            }
        }
    }

    /// The `trust_types::Formula` this rvalue reflects to — EXACTLY what
    /// `clean_ground::extract_return_formula` / `resolve_local_value` produce: `Use op`
    /// → `op.to_formula()`; `Bin op a b` → `Formula::{Add,Sub,Mul,Div,Rem}(a, b)` (the
    /// `binop_formula` arms in clean_ground). The LIVE `ground_int` of this formula is
    /// the term the §6 pipeline actually grounds for this rvalue.
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::Formula as F;
        let bx = |o: &SemOperand| Box::new(o.to_formula());
        match self {
            SemRvalue::Use(op) => op.to_formula(),
            SemRvalue::Bin(SemBinOp::Add, a, b) => F::Add(bx(a), bx(b)),
            SemRvalue::Bin(SemBinOp::Sub, a, b) => F::Sub(bx(a), bx(b)),
            SemRvalue::Bin(SemBinOp::Mul, a, b) => F::Mul(bx(a), bx(b)),
            SemRvalue::Bin(SemBinOp::Div, a, b) => F::Div(bx(a), bx(b)),
            // Trust: witness-tier Rem arm — EXACTLY clean_ground's `binop_formula` Rem arm.
            SemRvalue::Bin(SemBinOp::Rem, a, b) => F::Rem(bx(a), bx(b)),
            // Trust: BITWISE SHAPE LANE — no NATIVE `Formula::BitAnd`/`BitOr`/
            // `BitXor`/`Shl` arithmetic-Int variant exists (unlike Add/Sub/Mul/Div/
            // Rem): a genuine bitwise op on ARBITRARY (non-0/1) integers has no
            // polynomial identity the way the BOOL-CONNECTIVE `Or`/`And` arms reuse
            // (those are sound ONLY because their operands are 0/1-encoded — see
            // `to_formula`'s `Or`/`And` doc). Instead reuse the EXISTING GENERIC
            // `Formula::Pred(name, args)` opaque-function-application carrier — the
            // SAME shape `SemOperand::Len`'s `slice_len` reflection already
            // establishes — tagged with the EXACT registered Opaque constant name
            // (`Int.land`/`Int.lor`/`Int.xor`/`Int.shiftLeft`), so `ground_int`'s
            // new matching `F::Pred` arm (clean_ground.rs) grounds to the SAME
            // term `eval_rvalue`'s kernel-side `BinOp.rec` dispatch reduces to.
            SemRvalue::Bin(SemBinOp::BitAnd, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.land"), vec![*bx(a), *bx(b)])
            }
            SemRvalue::Bin(SemBinOp::BitOr, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.lor"), vec![*bx(a), *bx(b)])
            }
            SemRvalue::Bin(SemBinOp::BitXor, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.xor"), vec![*bx(a), *bx(b)])
            }
            SemRvalue::Bin(SemBinOp::Shl, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.shiftLeft"), vec![*bx(a), *bx(b)])
            }
            // Trust: M6 rung 6, UNSIGNED-Shr arm — the SAME opaque-application
            // carrier discipline as the four bitwise arms above.
            SemRvalue::Bin(SemBinOp::Shr, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.shiftRight"), vec![*bx(a), *bx(b)])
            }
            // `Sel c a b` reflects to `Ite(c, a, b)` — the faithful if-then-else formula.
            // Not exercised by the conditional-update loop path (which uses `to_rvalue_expr`
            // only), but kept faithful for completeness.
            SemRvalue::Sel(c, a, b) => F::Ite(Box::new(c.to_formula()), bx(a), bx(b)),
            // Trust: COMPARE-AS-VALUE — reflects to the SAME comparison relation
            // `SemCond::to_formula` builds for the GUARD leaf (`clean_ground::cmp_formula`
            // produces the byte-identical shape at the VALUE position — see
            // `extract_return_formula`'s comparison fallback), over the two nested
            // sub-rvalues' OWN formulas (not bare operands).
            SemRvalue::Cmp(op, ra, rb) => {
                let (a, b) = (ra.to_formula(), rb.to_formula());
                match op {
                    SemCmpOp::Lt => F::Lt(Box::new(a), Box::new(b)),
                    SemCmpOp::Le => F::Le(Box::new(a), Box::new(b)),
                    SemCmpOp::Gt => F::Gt(Box::new(a), Box::new(b)),
                    SemCmpOp::Ge => F::Ge(Box::new(a), Box::new(b)),
                    SemCmpOp::Eq => F::Eq(Box::new(a), Box::new(b)),
                    SemCmpOp::Ne => F::Not(Box::new(F::Eq(Box::new(a), Box::new(b)))),
                }
            }
            // Trust: BOOL-CONNECTIVE — reflects to PURE ARITHMETIC over the two nested
            // sub-rvalues' OWN formulas (`And := Mul(a,b)`, `Or := Sub(Add(a,b),
            // Mul(a,b))`) — REUSES the ALREADY-grounded `F::Add`/`F::Sub`/`F::Mul`
            // arms `clean_ground::ground_int` carries (no NEW grounder case needed;
            // see `eval_rvalue`'s `or_case`/`and_case` doc for why this arithmetic
            // form — not `Formula::Or`/`And` — is what makes Lemma 1B's live-
            // grounder-connected adequacy close reflexively).
            SemRvalue::And(ra, rb) => F::Mul(Box::new(ra.to_formula()), Box::new(rb.to_formula())),
            SemRvalue::Or(ra, rb) => {
                let (a, b) = (ra.to_formula(), rb.to_formula());
                F::Sub(
                    Box::new(F::Add(Box::new(a.clone()), Box::new(b.clone()))),
                    Box::new(F::Mul(Box::new(a), Box::new(b))),
                )
            }
            // Trust: BIT_FIELD NESTED-RVALUE — reflects to the SAME generic
            // opaque-function-application carrier `Formula::Pred(name, [a,b])`
            // the FLAT `SemRvalue::Bin(BitAnd/BitOr/BitXor/Shl, ..)` arm above
            // already establishes, over the two NESTED sub-rvalues' OWN
            // formulas (not bare operands) — `clean_ground::ground_int`
            // already recurses generically through its `g(&args[..])` calls
            // (it grounds ANY `Formula`, not just an atomic `Var`/`Const`), so
            // a nested `F::Pred("Int.land", [.., F::Pred("Int.shiftLeft", ..)])`
            // grounds correctly with ZERO grounder changes needed.
            SemRvalue::BitBin(op, ra, rb) => {
                let name = match op {
                    SemBinOp::BitAnd => "Int.land",
                    SemBinOp::BitOr => "Int.lor",
                    SemBinOp::BitXor => "Int.xor",
                    SemBinOp::Shl => "Int.shiftLeft",
                    // Trust: M6 rung 6, UNSIGNED-Shr arm — the fifth bitwise
                    // member (nested `Shr` composes exactly like nested `Shl`).
                    SemBinOp::Shr => "Int.shiftRight",
                    // `BitBin` is only ever CONSTRUCTED (by
                    // `sem_rvalue_of_mir_at_depth`) for one of the five bitwise
                    // ops above; a non-bitwise `op` here is unreachable by
                    // construction, but stay total/fail-closed rather than
                    // panic — no `F::Pred` name means the grounder declines.
                    SemBinOp::Add
                    | SemBinOp::Sub
                    | SemBinOp::Mul
                    | SemBinOp::Div
                    | SemBinOp::Rem => "",
                };
                F::Pred(trust_types::Symbol::intern(name), vec![ra.to_formula(), rb.to_formula()])
            }
            // Trust: W-CMP-DISCR — the ARITHMETIC twin of `BitBin`: reflects to
            // the NATIVE `F::Add`/`F::Sub`/`F::Mul` arithmetic-Int variant (like
            // the FLAT `Bin`), recursing on the two sub-rvalues' OWN formulas
            // (not bare operands). `clean_ground::ground_int` already recurses
            // generically (`F::Sub(a, b) => Int.sub (g a) (g b)`, and `g` of a
            // nested `F::Gt`/`F::Lt` yields `bool_as_int(..)`), so a nested
            // `F::Sub(F::Gt(..), F::Lt(..))` grounds to `Int.sub (bool_as_int ..)
            // (bool_as_int ..)` — DEF-EQ to the `arithbin_case`/`cmp_case`
            // reduct, closing adequacy reflexively. `ArithBin` is only ever built
            // with an arithmetic `op` (Sub, in practice); Div/Rem reuse the flat
            // `Bin`'s heads and bitwise/shift reuse `BitBin`'s `F::Pred` heads for
            // totality, but the recognizer never constructs those.
            SemRvalue::ArithBin(op, ra, rb) => {
                let (a, b) = (ra.to_formula(), rb.to_formula());
                let bxf = |f: trust_types::Formula| Box::new(f);
                match op {
                    SemBinOp::Add => F::Add(bxf(a), bxf(b)),
                    SemBinOp::Sub => F::Sub(bxf(a), bxf(b)),
                    SemBinOp::Mul => F::Mul(bxf(a), bxf(b)),
                    SemBinOp::Div => F::Div(bxf(a), bxf(b)),
                    SemBinOp::Rem => F::Rem(bxf(a), bxf(b)),
                    SemBinOp::BitAnd => {
                        F::Pred(trust_types::Symbol::intern("Int.land"), vec![a, b])
                    }
                    SemBinOp::BitOr => F::Pred(trust_types::Symbol::intern("Int.lor"), vec![a, b]),
                    SemBinOp::BitXor => F::Pred(trust_types::Symbol::intern("Int.xor"), vec![a, b]),
                    SemBinOp::Shl => {
                        F::Pred(trust_types::Symbol::intern("Int.shiftLeft"), vec![a, b])
                    }
                    SemBinOp::Shr => {
                        F::Pred(trust_types::Symbol::intern("Int.shiftRight"), vec![a, b])
                    }
                }
            }
        }
    }

    /// The distinct parameter indices this rvalue references, in first-appearance
    /// order (the variables the grounder-connected adequacy binds as `Int` binders).
    fn var_indices(&self) -> Vec<u64> {
        let mut out = Vec::new();
        match self {
            SemRvalue::Use(op) => op.var_indices(&mut out),
            SemRvalue::Bin(_, a, b) => {
                a.var_indices(&mut out);
                b.var_indices(&mut out);
            }
            // The condition's operands AND both arms reference variables.
            SemRvalue::Sel(c, a, b) => {
                c.a.var_indices(&mut out);
                c.b.var_indices(&mut out);
                a.var_indices(&mut out);
                b.var_indices(&mut out);
            }
            // Trust: COMPARE-AS-VALUE — both nested sub-rvalues contribute their own
            // referenced indices, in first-appearance order (`ra` before `rb`,
            // matching the `Bin`/`Sel` left-to-right convention above).
            SemRvalue::Cmp(_, ra, rb) => {
                for idx in ra.var_indices() {
                    if !out.contains(&idx) {
                        out.push(idx);
                    }
                }
                for idx in rb.var_indices() {
                    if !out.contains(&idx) {
                        out.push(idx);
                    }
                }
            }
            // Trust: BOOL-CONNECTIVE — SAME dedup/order discipline as `Cmp` above.
            // Trust: BIT_FIELD NESTED-RVALUE — `BitBin` joins the SAME dedup/order
            // group (both sub-rvalues contribute their own referenced indices).
            // Trust: W-CMP-DISCR — `ArithBin` joins the SAME group.
            SemRvalue::Or(ra, rb)
            | SemRvalue::And(ra, rb)
            | SemRvalue::BitBin(_, ra, rb)
            | SemRvalue::ArithBin(_, ra, rb) => {
                for idx in ra.var_indices() {
                    if !out.contains(&idx) {
                        out.push(idx);
                    }
                }
                for idx in rb.var_indices() {
                    if !out.contains(&idx) {
                        out.push(idx);
                    }
                }
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Step 2C — Lemma 1C: return-witness adequacy (closed cases, proven modulo 3)
// ---------------------------------------------------------------------------
/// The minimal SSA-statement fragment `MirSem` models for the return trace: an
/// `Assign(idx, rvalue)` (`Statement::Assign` to local `idx`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemStmt {
    /// The assigned local index.
    pub idx: u64,
    /// The rvalue bound to it.
    pub rvalue: SemRvalue,
}

impl SemStmt {
    /// The closed `Trust.MirSem.Stmt` constructor value.
    fn to_stmt_expr(&self) -> Expr {
        Expr::apps(cst(MIRSEM_STMT_ASSIGN), [Expr::nat_lit(self.idx), self.rvalue.to_rvalue_expr()])
    }
}

/// A return witness: the SSA assignments leading to the return, plus the returned
/// operand (`Terminator::Return` of local `_0`, or the `_0 := …` operand the
/// return block uses). This is the `exec` input Lemma 1C reasons over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemReturn {
    /// The (ordered) SSA assignments preceding the return.
    pub stmts: Vec<SemStmt>,
    /// The operand returned (folded over the assignments' env by `exec`).
    pub ret: SemOperand,
}

impl SemReturn {
    /// The closed `List Trust.MirSem.Stmt` value for the assignment prefix — the
    /// syntactic SSA trace (`List.cons (Assign …) … List.nil`). Pins the trace as a
    /// real prelude-`List` term so the model carries the statements explicitly, even
    /// though the closed-case theorem evaluates the return operand directly.
    fn to_stmts_expr(&self) -> Expr {
        let stmt_ty = cst(MIRSEM_STMT);
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            stmt_ty.clone(),
        );
        // Right-fold: cons s0 (cons s1 … nil).
        self.stmts.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty.clone(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The GROUNDED REFLECTION denotation `E_ret` under `e` — what `ground_int`
    /// produces for the formula `extract_return_formula` reflects. For the CLOSED
    /// cases Lemma 1C proves, the return operand is a parameter or constant whose
    /// denotation does not depend on the preceding assignments (the SSA fold leaves
    /// a parameter/constant operand untouched), so the denotation is the return
    /// operand's own denotation.
    fn denotation(&self, e_ref: &Expr) -> Expr {
        self.ret.denotation(e_ref)
    }
}

// ---------------------------------------------------------------------------
// Step 3 — the faithfulness certificate hook
// ---------------------------------------------------------------------------
/// A kernel-checked operand-adequacy certificate: the operand `O` and the modulo-3
/// verdict for `∀e. eval e O = E_O`. Carries the proof that `O`'s reflection is
/// faithful to MirSem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdequacyCertificate {
    /// The operand whose reflection this certifies.
    pub operand: SemOperand,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl AdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

/// A kernel-checked rvalue-adequacy certificate (Lemma 1B): the rvalue `R` and the
/// modulo-3 verdict for `∀e. eval_rvalue e R = E_R`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RvalueAdequacyCertificate {
    /// The rvalue whose reflection this certifies.
    pub rvalue: SemRvalue,
    /// The kernel-checked verdict.
    pub verdict: AdequacyVerdict,
}

impl RvalueAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

/// A kernel-checked return-adequacy certificate (Lemma 1C): the return witness and
/// the modulo-3 verdict for the closed return trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnAdequacyCertificate {
    /// The return witness whose reflection this certifies.
    pub ret: SemReturn,
    /// The kernel-checked verdict.
    pub verdict: AdequacyVerdict,
}

impl ReturnAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

// ---------------------------------------------------------------------------
// Lemma 1C-cf — CONTROL-FLOW return adequacy (the guarded `if cmp { t } else { f }`)
// ---------------------------------------------------------------------------
/// The comparison-op fragment `MirSem` models for a guard's discriminant temp —
/// exactly the integer comparison `BinOp`s a `SwitchInt`'s `BinaryOp(cmp,a,b)` discr
/// uses. Each grounds to a Bool-valued, axiom-free prelude term (`eval_cond`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemCmpOp {
    /// `<` — grounds to `decide (Int.lt …)`.
    Lt,
    /// `≤` — grounds to `decide (Int.le …)`.
    Le,
    /// `==` — grounds to `Int.beq …`.
    Eq,
    /// `!=` — grounds to `Bool.not (Int.beq …)`.
    Ne,
    /// `>` — grounds to the SWAPPED `decide (Int.lt …)`.
    Gt,
    /// `≥` — grounds to the SWAPPED `decide (Int.le …)`.
    Ge,
}

impl SemCmpOp {
    /// The closed `Trust.MirSem.CmpOp` constructor value.
    fn to_cmpop_expr(self) -> Expr {
        cst(match self {
            SemCmpOp::Lt => MIRSEM_CMPOP_LT,
            SemCmpOp::Le => MIRSEM_CMPOP_LE,
            SemCmpOp::Eq => MIRSEM_CMPOP_EQ,
            SemCmpOp::Ne => MIRSEM_CMPOP_NE,
            SemCmpOp::Gt => MIRSEM_CMPOP_GT,
            SemCmpOp::Ge => MIRSEM_CMPOP_GE,
        })
    }
}

/// A guard condition: a single integer comparison `cmp(a, b)` over two modeled
/// operands — the `Trust.MirSem.Cond.Cmp` shape, modeling a `SwitchInt`'s
/// `BinaryOp(cmp, a, b)` discriminant temp.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCond {
    /// The comparison operator.
    pub op: SemCmpOp,
    /// The left operand.
    pub a: SemOperand,
    /// The right operand.
    pub b: SemOperand,
}

impl SemCond {
    /// The closed `Trust.MirSem.Cond` constructor value (`Cmp op a b`).
    fn to_cond_expr(&self) -> Expr {
        Expr::apps(
            cst(MIRSEM_COND_CMP),
            [self.op.to_cmpop_expr(), self.a.to_operand_expr(), self.b.to_operand_expr()],
        )
    }

    /// The comparison `Formula` this guard reflects to — EXACTLY what
    /// `clean_ground::cmp_formula` produces for the same MIR `BinaryOp(cmp, a, b)`
    /// discriminant: `Lt/Le/Gt/Ge/Eq` to the matching relation, `Ne` to `Not(Eq)` (the
    /// shape `clean_ground::ground_bool` consumes). The LIVE grounder maps this to the
    /// SAME `Bool` term `eval_cond` reduces to.
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::Formula as F;
        let a = || Box::new(self.a.to_formula());
        let b = || Box::new(self.b.to_formula());
        match self.op {
            SemCmpOp::Lt => F::Lt(a(), b()),
            SemCmpOp::Le => F::Le(a(), b()),
            SemCmpOp::Gt => F::Gt(a(), b()),
            SemCmpOp::Ge => F::Ge(a(), b()),
            SemCmpOp::Eq => F::Eq(a(), b()),
            SemCmpOp::Ne => F::Not(Box::new(F::Eq(a(), b()))),
        }
    }
}

/// A guard CONDITION TREE: either a single comparison leaf (`Cmp`) or a conjunction
/// of two sub-trees (`And`) — the Rust analogue of the kernel `Trust.MirSem.Cond`
/// inductive, with `Leaf` mapping to the `Cmp` constructor and `And` to the ADDITIVE
/// `And` constructor. A bare comparison guard is `Leaf(SemCond)` and grounds to the
/// byte-identical `Cmp op a b` it always did; a conjunctive (short-circuit `&&`)
/// guard is `And(Box, Box)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemCondTree {
    /// A single comparison `cmp(a, b)` — the `Trust.MirSem.Cond.Cmp` shape.
    Leaf(SemCond),
    /// A conjunction `c1 && c2` — the ADDITIVE `Trust.MirSem.Cond.And` shape.
    And(Box<SemCondTree>, Box<SemCondTree>),
    /// Trust: RANGE+DISJUNCTION guard — a disjunction `c1 || c2`, the ADDITIVE
    /// `Trust.MirSem.Cond.Or` shape (the `is_ascii_control`-class control-flow
    /// `||`: `*self <= 31 || *self == 127`).
    Or(Box<SemCondTree>, Box<SemCondTree>),
    /// Trust: ITER-NEXT VALUE-PATH (2026-07-21) — the OPAQUE DISPATCH HEAD
    /// `iter_has_next(param)` of the pinned `&mut core::slice::iter::Iter` parameter
    /// `param` (0-based). `<Iter as Iterator>::next` returns `None` iff the entry cursor
    /// equals the entry end and `Some(..)` otherwise; that dispatch is modeled as an
    /// OPAQUE total `iter_has_next : Int → Bool` (`Trust.MirSem.iter_has_next`,
    /// `Declaration::Opaque`, EMPTY axiom_deps — the SAME honesty tier as `sliceLen`),
    /// NOT as the concrete raw-pointer `Eq(cursor, end)` comparison. The guard's kernel
    /// MEANING is abstract; its tie to the real `ptr != end` `SwitchInt` is enforced by
    /// the RECOGNIZER (`sem_iter_next_shape_of`, via `cursor_end_operand_pair` +
    /// `iter_not_equal_guard_dominates` machinery over the folded live CFG), never
    /// asserted in the logic — so the certificate assumes NO bridge premise
    /// (`ptr != end ↔ len(region) ≥ 1`). `IterHasNext(p)` is TRUE == the `!=`-edge
    /// (has-next). MINTED ONLY by `sem_iter_next_shape_of` and denoted ONLY by
    /// `trustir_adt::cond_bool`; every other `SemCondTree` consumer treats it as
    /// FAIL-CLOSED / never-reached (see each arm).
    IterHasNext(u64),
}

impl From<SemCond> for SemCondTree {
    fn from(c: SemCond) -> Self {
        SemCondTree::Leaf(c)
    }
}

impl SemCondTree {
    /// The closed `Trust.MirSem.Cond` constructor value. `Leaf` reflects to the
    /// BYTE-IDENTICAL `Cmp op a b` (preserving every existing leaf certificate);
    /// `And c1 c2` reflects to the new `And (to_cond_expr c1) (to_cond_expr c2)`.
    fn to_cond_expr(&self) -> Expr {
        match self {
            SemCondTree::Leaf(c) => c.to_cond_expr(),
            SemCondTree::And(c1, c2) => {
                Expr::apps(cst(MIRSEM_COND_AND), [c1.to_cond_expr(), c2.to_cond_expr()])
            }
            // Trust: RANGE+DISJUNCTION guard — the `Or` twin of the `And` arm.
            SemCondTree::Or(c1, c2) => {
                Expr::apps(cst(MIRSEM_COND_OR), [c1.to_cond_expr(), c2.to_cond_expr()])
            }
            // Trust: ITER-NEXT VALUE-PATH — the opaque `iter_has_next` dispatch head has
            // NO `Trust.MirSem.Cond` SYNTAX constructor (it is denoted ONLY on the
            // trust-ir witness side via `trustir_adt::cond_bool`, keyed to the
            // `Trust.MirSem.iter_has_next` opaque). This MirSem self-denotation is NEVER
            // reached for an `IterHasNext` guard (minted only into a `SemAdtReturn`
            // consumed by the trust-ir lane), so this arm is a FAIL-CLOSED POISON const —
            // `UnknownConst`-rejected by the kernel rather than a false Cond syntax value.
            SemCondTree::IterHasNext(_) => {
                cst("Trust.MirSem.Cond.__iter_has_next_trustir_witness_only")
            }
        }
    }

    /// The `Formula` this guard tree reflects to — `Leaf` to the comparison
    /// `clean_ground::cmp_formula` produces (unchanged), `And` to `Formula::And([c1,
    /// c2])` (the shape `clean_ground::ground_bool`/`guarded_return_formula` consume
    /// for a conjunctive guard). The LIVE grounder maps this to the SAME `Bool` term
    /// `eval_cond` reduces to (a `Bool.and` of the two sub-conditions for `And`).
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::Formula as F;
        match self {
            SemCondTree::Leaf(c) => c.to_formula(),
            SemCondTree::And(c1, c2) => F::And(vec![c1.to_formula(), c2.to_formula()]),
            // Trust: RANGE+DISJUNCTION guard — `Formula::Or([c1, c2])`, the shape
            // `clean_ground::ground_bool`'s new `Or` arm consumes (a left-nested
            // `Bool.or` fold, the exact dual of the `And` arm's `Bool.and`).
            SemCondTree::Or(c1, c2) => F::Or(vec![c1.to_formula(), c2.to_formula()]),
            // Trust: ITER-NEXT VALUE-PATH — the honest OPAQUE dispatch Pred
            // `Trust.MirSem.iter_has_next(param)`. Never grounded on the verdict path
            // (the certificate rides the trust-ir witness); `clean_ground::ground_bool`
            // has NO `iter_has_next` arm, so a MirSem-lane grounding FALLS THROUGH to
            // `None` (fail-closed).
            SemCondTree::IterHasNext(p) => F::Pred(
                trust_types::Symbol::intern("Trust.MirSem.iter_has_next"),
                vec![F::Var(var_name(*p), trust_types::Sort::Int)],
            ),
        }
    }

    /// Accumulate the parameter indices the guard references, in first-appearance
    /// order with no duplicates, into `out`. For a `Leaf` this is exactly the old
    /// `cond.a.var_indices(out); cond.b.var_indices(out)` sequence (both
    /// `SemOperand::var_indices` calls already dedup against `out`), so a leaf guard's
    /// index list — and hence its grounding env — is byte-identical to before.
    fn collect_var_indices(&self, out: &mut Vec<u64>) {
        match self {
            SemCondTree::Leaf(c) => {
                c.a.var_indices(out);
                c.b.var_indices(out);
            }
            SemCondTree::And(c1, c2) | SemCondTree::Or(c1, c2) => {
                c1.collect_var_indices(out);
                c2.collect_var_indices(out);
            }
            // Trust: ITER-NEXT VALUE-PATH — the guard references exactly its pinned
            // `&mut Iter` parameter index.
            SemCondTree::IterHasNext(p) => {
                if !out.contains(p) {
                    out.push(*p);
                }
            }
        }
    }
}

/// A CONTROL-FLOW return witness: the guard condition plus the THEN/ELSE rvalues the
/// two arms assign to `_0`. Models a guarded `if cond { then } else { else }`
/// return — a `SwitchInt` (or, for a conjunctive `&&` guard, a short-circuit chain
/// of two `SwitchInt`s) over the comparison temp whose two arms each `_0 :=
/// <rvalue>` and converge at a bare `Return` block. The straight-line `SemReturn`
/// does NOT capture this (the `Return` block carries no `_0 := …`); this is the
/// shape Lemma 1C-cf certifies. `cond` is a `SemCondTree` — a `Leaf` for a single
/// comparison (byte-identical to before) or an `And` for a conjunctive guard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCfReturn {
    /// The guard condition tree (the `SwitchInt`(s)' comparison-temp discriminant).
    pub cond: SemCondTree,
    /// The value the THEN arm returns (`cond` true → `_0 := then`).
    pub then_rv: SemRvalue,
    /// The value the ELSE arm returns (`cond` false → `_0 := else`).
    pub else_rv: SemRvalue,
}

impl SemCfReturn {
    /// The `trust_types::Formula::Ite(cond, then, else)` this guarded return reflects
    /// to — EXACTLY what `clean_ground::guarded_return_formula` produces for the same
    /// guarded MIR shape. The LIVE `clean_ground::ground_int` grounds this `Ite` to the
    /// `Bool.rec` if-then-else that `eval_ite` ι-reduces to, so the branch refinement
    /// (`refinementB`) links to the live pipeline.
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::Formula as F;
        F::Ite(
            Box::new(self.cond.to_formula()),
            Box::new(self.then_rv.to_formula()),
            Box::new(self.else_rv.to_formula()),
        )
    }

    /// The distinct parameter indices this guarded return references across the guard
    /// condition (all comparison leaves) and both arm values, in first-appearance
    /// order (the variables the grounder-connected branch refinement binds as `Int`
    /// binders).
    fn var_indices(&self) -> Vec<u64> {
        let mut out = Vec::new();
        self.cond.collect_var_indices(&mut out);
        for op in self.then_rv.var_indices() {
            if !out.contains(&op) {
                out.push(op);
            }
        }
        for op in self.else_rv.var_indices() {
            if !out.contains(&op) {
                out.push(op);
            }
        }
        out
    }
}

// ===========================================================================
// NESTED / MULTI-WAY guarded return — the additive frontier.
//
// A single-branch `SemCfReturn` models `if c { then } else { else }`, where both arms
// are scalar `SemRvalue`s. A NESTED guard `if c1 { t1 } else if c2 { t2 } else { e }`
// (e.g. `sign`, a 3-arm clamp) has an ELSE arm that is ITSELF a guarded if-then-else,
// which `SemCfReturn`'s scalar `else_rv` cannot host. `SemBranchTree` is the recursive
// witness for that nested shape: a `Leaf(SemRvalue)` arm value or a `Node(cond, then,
// else)` whose `then`/`else` are themselves trees. It is purely additive — `SemCfReturn`
// and `SemRvalue` are untouched, so every existing single-branch certificate is
// byte-identical.
//
// Its kernel denotation nests the Int-armed `iteI` (NOT `eval_ite`, whose arms are
// `Rvalue` SYNTAX): a `Leaf(rv)` denotes `eval_rvalue E rv`, a `Node(c, t, f)` denotes
// `iteI E c (denote t) (denote f)`. This whole term ι/δ-reduces (through `iteI` →
// `Bool.rec`, leaves through `eval_rvalue`/`eval_cond`) to EXACTLY the nested `Bool.rec`
// the live `clean_ground::ground_int` emits for the nested `Formula::Ite`, so the
// nested-branch refinement closes by `Eq.refl` — the multi-way generalization of
// `refinementB`.
// ===========================================================================
/// A NESTED / multi-way guarded return witness: a `Leaf` arm value or an `if/else`
/// `Node` whose THEN/ELSE branches are themselves trees. A depth-1 tree
/// `Node(c, Leaf(t), Leaf(f))` models the SAME return as `SemCfReturn { cond: c,
/// then_rv: t, else_rv: f }`; a depth-≥2 tree is the genuinely-new multi-way shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemBranchTree {
    /// A scalar arm value (`SemRvalue` — `Use`/`Bin`), the leaf of the if/else tree.
    Leaf(SemRvalue),
    /// Trust: BRANCHY call-arm sub-axis — a leaf arm whose value is the OPAQUE
    /// result of a certified-callee call (`if c { g(a) } else { h(b) }`'s `g(a)`
    /// arm, or a MIX with a plain scalar arm). Produced ONLY by
    /// [`sem_nested_branch_of_mir`] when called WITH a certified-callee registry
    /// (`callees: Some(_)`) — the MirSem-certifying paths
    /// ([`branch_refinement_witness`], [`nested_branch_refinement_witness`])
    /// ALWAYS call it with `callees: None` (see their docs), so a tree reaching
    /// [`SemBranchTree::to_formula`]/[`SemBranchTree::denotation`] NEVER contains a
    /// `CallLeaf` — this is a structural invariant enforced at the call sites, not
    /// a convention. Consumed ONLY by the trust-ir-primary shape-only path
    /// (`mirsem::sem_branch_call_shape_of` / `prove::branch_call_fully_faithful_via_trustir`),
    /// which never mints a MirSem kernel certificate for it (Seam B, exactly like
    /// the standalone [`SemCallReturn`]).
    CallLeaf(SemCallReturn),
    /// A guarded `if cond { then } else { else }`, with recursive sub-trees.
    Node(SemCondTree, Box<SemBranchTree>, Box<SemBranchTree>),
}

impl SemBranchTree {
    /// The `trust_types::Formula` this nested return reflects to — `Leaf` to the arm
    /// rvalue's `Formula` (unchanged), `Node` to `Formula::Ite(cond, then, else)` over
    /// the recursively-reflected sub-trees. For a depth-2 nest this is the NESTED
    /// `Ite(c1, t1, Ite(c2, t2, e2))` the live `clean_ground::ground_int` grounds (its
    /// `F::Ite` arm already recurses into a nested else).
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::Formula as F;
        match self {
            SemBranchTree::Leaf(rv) => rv.to_formula(),
            // See the variant doc: structurally unreachable — only a `callees: None`
            // tree ever reaches `to_formula` (the MirSem-certifying paths), and such a
            // tree never contains a `CallLeaf`. There is no MirSem `Formula` for an
            // opaque call (fail-closed by construction, not by a silent placeholder).
            SemBranchTree::CallLeaf(_) => unreachable!(
                "SemBranchTree::CallLeaf has no MirSem Formula — only reachable via the \
                 callees:Some(_) recognizer path, which never feeds the MirSem-certifying \
                 to_formula/denotation consumers"
            ),
            SemBranchTree::Node(cond, then_, else_) => F::Ite(
                Box::new(cond.to_formula()),
                Box::new(then_.to_formula()),
                Box::new(else_.to_formula()),
            ),
        }
    }

    /// Whether this tree is genuinely NESTED (an `if/else` whose THEN or ELSE branch is
    /// itself a `Node`). A non-nested tree (`Leaf`, or a `Node` of two `Leaf`s) is the
    /// single-branch shape already covered by `SemCfReturn`; only a nested tree needs
    /// the new multi-way machinery, so the witness fail-closes a non-nested tree to the
    /// existing single-branch path.
    fn is_nested(&self) -> bool {
        match self {
            SemBranchTree::Leaf(_) | SemBranchTree::CallLeaf(_) => false,
            SemBranchTree::Node(_, t, f) => {
                matches!(**t, SemBranchTree::Node(..)) || matches!(**f, SemBranchTree::Node(..))
            }
        }
    }

    /// Trust: BRANCHY call-arm sub-axis — whether this tree contains at least one
    /// `CallLeaf` anywhere. Used by [`sem_branch_call_shape_of`] to reserve itself for
    /// the genuinely NEW call-armed shape (a tree with none is already covered by the
    /// existing `sem_cf_return_shape_of`/`sem_nested_branch_shape_of` paths).
    fn contains_call_leaf(&self) -> bool {
        match self {
            SemBranchTree::Leaf(_) => false,
            SemBranchTree::CallLeaf(_) => true,
            SemBranchTree::Node(_, t, f) => t.contains_call_leaf() || f.contains_call_leaf(),
        }
    }

    /// The distinct parameter indices this nested return references across every guard
    /// condition and every leaf arm, in first-appearance order (the variables the
    /// nested-branch refinement binds as `Int` binders). Mirrors `SemCfReturn::var_indices`.
    fn var_indices(&self) -> Vec<u64> {
        let mut out = Vec::new();
        self.collect_var_indices(&mut out);
        out
    }

    fn collect_var_indices(&self, out: &mut Vec<u64>) {
        match self {
            SemBranchTree::Leaf(rv) => {
                for op in rv.var_indices() {
                    if !out.contains(&op) {
                        out.push(op);
                    }
                }
            }
            // Trust: BRANCHY call-arm sub-axis — a call arm's referenced indices are
            // its actual arguments' (its `SemCallReturn` carries no separate guard).
            SemBranchTree::CallLeaf(call) => {
                for op in &call.args {
                    op.var_indices(out);
                }
            }
            SemBranchTree::Node(cond, then_, else_) => {
                cond.collect_var_indices(out);
                then_.collect_var_indices(out);
                else_.collect_var_indices(out);
            }
        }
    }

    /// The kernel `Int` DENOTATION of this tree under the supplied env ref `e_ref`:
    ///   * `Leaf(rv)` → `eval_rvalue e rv` (the arm's evaluated value).
    ///   * `Node(c, t, f)` → `iteI e c (denote t) (denote f)` — the Int-armed
    ///     if-then-else, RECURSING into the sub-trees so a nested else arm is itself an
    ///     `iteI`. This whole term ι/δ-reduces to the nested `Bool.rec` that
    ///     `clean_ground::ground_int` emits for `self.to_formula()`, so the nested-branch
    ///     refinement closes by reflexivity.
    fn denotation(&self, e_ref: &Expr) -> Expr {
        match self {
            SemBranchTree::Leaf(rv) => {
                Expr::apps(cst(MIRSEM_EVAL_RVALUE), [e_ref.clone(), rv.to_rvalue_expr()])
            }
            // See `to_formula`'s doc: structurally unreachable (a `callees: None` tree
            // never contains a `CallLeaf`), fail-closed by construction.
            SemBranchTree::CallLeaf(_) => unreachable!(
                "SemBranchTree::CallLeaf has no MirSem denotation — see to_formula's doc"
            ),
            SemBranchTree::Node(cond, then_, else_) => Expr::apps(
                cst(MIRSEM_ITE_I),
                [
                    e_ref.clone(),
                    cond.to_cond_expr(),
                    then_.denotation(e_ref),
                    else_.denotation(e_ref),
                ],
            ),
        }
    }

    /// Collect every leaf arm's `SemRvalue` (in left-to-right order) — used to certify
    /// each arm's rvalue adequacy (Lemma 1B) when minting the nested-faithfulness
    /// certificate, mirroring the single-branch `[then_rv, else_rv]` arm certification.
    /// A `CallLeaf` contributes NOTHING (no `SemRvalue` exists for a call arm; it is
    /// certified separately via the trust-ir call-return instance) — harmless even if
    /// ever reached, though by construction ([`SemBranchTree::to_formula`]'s doc) this
    /// method is likewise only ever invoked on a `callees: None` (CallLeaf-free) tree.
    fn leaf_rvalues(&self) -> Vec<&SemRvalue> {
        let mut out = Vec::new();
        self.collect_leaf_rvalues(&mut out);
        out
    }

    fn collect_leaf_rvalues<'a>(&'a self, out: &mut Vec<&'a SemRvalue>) {
        match self {
            SemBranchTree::Leaf(rv) => out.push(rv),
            SemBranchTree::CallLeaf(_) => {}
            SemBranchTree::Node(_, t, f) => {
                t.collect_leaf_rvalues(out);
                f.collect_leaf_rvalues(out);
            }
        }
    }
}

/// A kernel-checked control-flow-return-adequacy certificate (Lemma 1C-cf): the
/// guarded return witness `r` and the modulo-3 verdict for `∀e. eval_ite e c t f =
/// (if eval_cond e c then eval_rvalue e t else eval_rvalue e f)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfReturnAdequacyCertificate {
    /// The control-flow return witness whose reflection this certifies.
    pub ret: SemCfReturn,
    /// The kernel-checked verdict.
    pub verdict: AdequacyVerdict,
}

impl CfReturnAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

/// Trust: COMPARE-AS-VALUE recursion bound — the maximum temp-inlining depth the
/// `sem_rvalue_of_mir` ↔ [`resolve_cmp_side`] mutual recursion may reach. Real
/// rustc-emitted MIR temp chains are acyclic by construction (temp numbering is
/// SSA-shaped), but `local_soundly_resolvable` is a PER-LOCAL single-assignment
/// gate that cannot detect a CYCLIC chain across locals in a malformed/
/// adversarial `VerifiableBody` (`_2 := Eq(_3, 0); _3 := Eq(_2, 0)`) — without a
/// bound, that input would recurse to stack overflow (crash, not unsoundness).
/// The measured real shapes are depth ≤ 2 (`ts-is-even`: one comparison over one
/// inlined arithmetic temp); 8 leaves generous headroom while keeping the
/// fail-closed guarantee (a deeper chain DECLINES, never crashes).
const CMP_INLINE_MAX_DEPTH: usize = 8;

/// Trust: GUARDED-LOCAL layer (BOOL-CONNECTIVE composition, 2026-07-08) — the
/// BOUNDED sub-CFG size gate for [`sem_guarded_local_value`]: the maximum number of
/// `SwitchInt`s a single guarded-local's own range-check chain may contain. Real
/// shapes measure ≤ 2 (a two-sided range check, `lo <= x && x <= hi`); 4 leaves
/// headroom for a 3+-comparison conjunction while still declining an unbounded or
/// adversarially bloated candidate set (never a crash, never a runaway scan — just a
/// fail-closed decline).
const GUARDED_LOCAL_MAX_SWITCHES: usize = 4;

// ---------------------------------------------------------------------------
// Step 2D — Lemma 2: SAFETY-VC adequacy (the unsigned arithmetic-OVERFLOW case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the highest-§6-value faithfulness piece).
// Lemmas 1A/1B/1C certify the CONTRACT/RETURN reflection (operand/rvalue/return
// adequacy). They do NOT certify that the SAFETY VC a safety proof discharges
// actually CAPTURES the unsafe condition. So far, when the §6 pipeline refutes a
// reflected overflow VC, it refutes a *trusted* formula — there is no proof that
// that formula IS the machine-overflow condition. Lemma 2 closes that for the
// unsigned arithmetic-overflow case: it pins the machine-overflow SEMANTICS in
// Clean (`uadd_overflows`) and proves that the term trust-vcgen+`ground_prop`
// produce for the unsigned `BinaryOp(Add)` overflow obligation IS (def-eq) that
// machine-overflow condition. So the discharge is faithful — refuting the VC is
// refuting EXACTLY the unsafe condition, not a reflected formula we merely trust.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `overflow_vc_shape_matches_trust_vcgen_emission`).
//   * The unsigned-add `VcKind::ArithmeticOverflow` (Int-path) VC is raised for an
//     unsigned `Rvalue::BinaryOp(Add, a, b)` — the UNCHECKED arithmetic whose
//     overflow is the implicit safety obligation. (`Rvalue::CheckedBinaryOp` is the
//     explicitly-checked form and emits NO implicit overflow VC: the check is the
//     source branch.) The emitted formula is
//        And([ 0≤a≤MAX, 0≤b≤MAX, Or([ Lt(a+b, 0), Gt(a+b, MAX) ]) ])
//     where `MAX = type_max_formula(w,false) = Formula::Int(2^w − 1)`,
//     `min = Formula::Int(0)`, and the violation core is the `out_of_range`
//     disjunction `Or([Lt(result, 0), Gt(result, MAX)])`. For `u32` the threshold
//     literal is EXACTLY `Int(4294967295)` = `2^32 − 1` (confirmed by probing the
//     emitter). See `crates/trust-vcgen/src/generate/overflow_vc.rs` (the
//     unsigned-add Int branch) + `crates/trust-vcgen/src/range.rs::type_max_formula`.
//   * `clean_ground::ground_prop` grounds that disjunction to a Clean `Prop`:
//        - `Formula::Gt(x, y)`  ↦  `Int.lt (ground_int y) (ground_int x)`  (SWAPPED)
//        - `Formula::Lt(x, y)`  ↦  `Int.lt (ground_int x) (ground_int y)`
//        - `Formula::Or([p,q])` ↦  `Or (ground p) (ground q)`
//        - `Formula::Add(x,y)`  ↦  `Int.add (ground x) (ground y)`
//        - `Formula::Int(k)`    ↦  `int_lit_to_expr k` (`Int.ofNat`/`Int.negSucc`)
//     So the OVERFLOW disjunct `Gt(a+b, MAX)` grounds to EXACTLY
//        `Int.lt (Int.ofNat (2^w−1)) (Int.add a b)`   :  Prop
//     i.e. the proposition `(2^w − 1) < (a + b)`.
//
// THE SPEC. `uadd_overflows a b w` is DEFINED as `(2^w − 1) < (a + b)` over Int
// (`Int.lt (Int.ofNat (2^w−1)) (Int.add a b)`). For in-range `0 ≤ a,b ≤ 2^w−1`
// this is the mathematical overflow condition of `u_w` wrapping-add: the
// machine sum `(a+b) mod 2^w` differs from `a+b` IFF `a+b ≥ 2^w` IFF
// `a+b > 2^w−1`. (`Int.lt` is `Prop`-valued in the prelude:
// `Int.lt p q := Int.le (Int.add p 1) q`, `Int.le p q := Int.NonNeg (Int.sub q p)`
// — both reducible prelude DEFINITIONS, so the spec carries no non-foundational
// axiom.)
//
// THE ADEQUACY (Lemma 2). The reflected overflow-disjunct term is LITERALLY the
// spec term, so adequacy is `@Eq.{1} Prop reflected uadd_overflows` witnessed by
// `Eq.refl` — kernel-checked modulo the 3 foundational axioms. A WRONG threshold
// (`2^w` instead of `2^w−1`) or a WRONG width (w=16 reflected as a w=32 spec)
// changes the closed `Int.ofNat` literal, so the two `Prop` terms are NOT def-eq
// and the `Eq.refl` proof is KERNEL-REJECTED — the off-by-one fails closed.
//
// SCOPE / HONEST GAP. This pins the OVERFLOW (`a+b > MAX`) disjunct of the
// unsigned-add VC — the disjunct that IS the overflow condition. The full
// emitted `out_of_range` also carries the `Lt(a+b, 0)` underflow disjunct, which
// is UNSATISFIABLE for unsigned add (`a,b ≥ 0 ⇒ a+b ≥ 0`) and is not part of the
// overflow SPEC; we ground and pin the whole disjunction too (so the modeled VC
// matches the emitted one byte-for-byte) but the machine-overflow EQUIVALENCE is
// stated against the overflow disjunct, which is the load-bearing claim. The
// wrapping-result bridge (`(a+b) mod 2^w = a+b ⟺ ¬overflow`) needs `mod`/order
// reasoning the def-eq kernel cannot close by reflexivity; it is the deferred
// breadth, NOT faked here. Widths w ∈ {8,16,32,64} all reduce by the same
// reflexivity (the threshold is a closed `Int.ofNat` literal at each width).
/// The unsigned integer widths the overflow-adequacy lemma is pinned for — exactly
/// the `u8`/`u16`/`u32`/`u64` widths whose `2^w − 1` threshold is a closed prelude
/// `Int.ofNat` literal. (`u128`'s `2^128 − 1` exceeds the `int_lit` `u64` literal
/// range and is out of this fragment, matching `trust-vcgen`'s `UInt` fallback.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UWidth {
    /// `u8` — threshold `2^8 − 1 = 255`.
    W8,
    /// `u16` — threshold `2^16 − 1 = 65535`.
    W16,
    /// `u32` — threshold `2^32 − 1 = 4294967295`.
    W32,
    /// `u64` — threshold `2^64 − 1 = 18446744073709551615`.
    W64,
}

impl UWidth {
    /// The bit width `w`.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            UWidth::W8 => 8,
            UWidth::W16 => 16,
            UWidth::W32 => 32,
            UWidth::W64 => 64,
        }
    }

    /// The overflow threshold `2^w − 1` (= `u_w::MAX`) as the exact `i128` value
    /// `trust-vcgen::range::type_max_formula(w, false)` emits (`(1i128 << w) - 1`).
    #[must_use]
    pub fn max_value(self) -> i128 {
        (1i128 << self.bits()) - 1
    }

    /// Map a Trust MIR integer type (`width`, `signed`) to the modeled unsigned
    /// width, when it is one of the pinned unsigned widths. `None` (out of
    /// fragment) for a signed type or an unmodeled width (e.g. `u128`).
    #[must_use]
    pub fn from_mir(width: u32, signed: bool) -> Option<UWidth> {
        if signed {
            return None;
        }
        match width {
            8 => Some(UWidth::W8),
            16 => Some(UWidth::W16),
            32 => Some(UWidth::W32),
            64 => Some(UWidth::W64),
            _ => None,
        }
    }
}

/// A kernel-checked overflow-VC adequacy certificate (Lemma 2): the modeled width
/// and the modulo-3 verdict for `<reflected overflow disjunct> = uadd_overflows_uW`.
/// Carries the proof that the reflected overflow VC IS the machine-overflow condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OverflowAdequacyCertificate {
    /// The unsigned width this certifies the overflow VC adequate for.
    pub width: UWidth,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl OverflowAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

// ---------------------------------------------------------------------------
// Step 2E — Lemma 3: SAFETY-VC adequacy (the array-BOUNDS / index-OOB case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the same gap Lemma 2 closes, now for bounds).
// Lemma 2 certifies that the reflected unsigned-add overflow VC IS the machine
// overflow condition. Lemma 3 does the same for the array-BOUNDS obligation: it
// pins the index-out-of-bounds SEMANTICS in Clean (`idx_oob`) and proves the term
// trust-vcgen+`ground_prop` produce for a slice/array index `s[i]` IS (def-eq) the
// OOB condition. So discharging the bounds VC refutes EXACTLY `len ≤ i`, not a
// reflected formula we merely trust.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `bounds_vc_shape_matches_trust_vcgen_emission`).
//   * A slice/array index load `s[i]` (an `Rvalue::Use(Copy place)` whose `place`
//     carries a `Projection::Index(i_local)` over a `Ty::Array{len}` / `Ty::Slice`)
//     raises a `VcKind::IndexOutOfBounds` / `SliceBoundsCheck` VC. For an UNSIGNED
//     index the emitted formula is EXACTLY the single disjunct
//        Ge(index, len)                      (rvalue_safety::index_bounds_violation)
//     where `index = Var(i)` and `len = Int(N)` (array, N the constant length) or
//     `len = Var("…__slice_len")` (slice). For a SIGNED index it is the FULL
//     disjunction `Or([Lt(index, 0), Ge(index, len)])` whose OOB-HIGH disjunct is
//     the SAME `Ge(index, len)` — the disjunct that IS the upper-bound violation.
//     (Confirmed by probing the emitter: a u32 array index emits `Ge(Var i, Int 8)`,
//     a signed index emits `Or([Lt(i,0), Ge(i,8)])`.) See
//     `crates/trust-vcgen/src/rvalue_safety.rs::{index_bounds_violation,
//     index_projection_vc,collection_len_formula}`.
//   * `clean_ground::ground_prop` grounds `Ge(x, y)` with the arguments SWAPPED to
//     `Int.le`:  `Formula::Ge(x, y) ↦ Int.le (ground_int y) (ground_int x)`. So the
//     OOB disjunct `Ge(index, len)` grounds to EXACTLY
//        `Int.le (ground len) (ground index)`   :  Prop
//     i.e. the proposition `len ≤ index`.
//
// THE SPEC. `idx_oob len i` is DEFINED as `len ≤ i` over Int
// (`Int.le len i`). For an in-range index `0 ≤ i`, this is exactly the OOB
// condition of indexing a collection of length `len`: the access `s[i]` is out
// of bounds IFF `i ≥ len` IFF `len ≤ i`. (`Int.le` is `Prop`-valued in the prelude:
// `Int.le p q := Int.NonNeg (Int.sub q p)` — a reducible prelude DEFINITION, so the
// spec carries no non-foundational axiom.)
//
// THE ADEQUACY (Lemma 3). The reflected OOB disjunct grounds to LITERALLY the spec
// term (`Ge` swaps to `Int.le len i`; the spec is `Int.le len i`), so adequacy is
// `@Eq.{1} Prop reflected idx_oob` witnessed by `Eq.refl` — kernel-checked modulo
// the 3 foundational axioms. A STRICT-vs-NON-STRICT off-by-one (`len < i` instead of
// `len ≤ i`, i.e. `Int.lt` vs `Int.le`) or a WRONG ARGUMENT ORDER (`i ≤ len` instead
// of `len ≤ i`) is a different `Prop` term — NOT def-eq — and the `Eq.refl` proof is
// KERNEL-REJECTED. The off-by-one fails closed.
//
// SCOPE / HONEST GAP. This pins the upper-bound OOB disjunct `Ge(i, len)` — the
// disjunct that IS the out-of-bounds condition for a non-negative (`usize`) index,
// the dominant case. For a SIGNED index the emitted VC adds the `Lt(i, 0)`
// lower-bound disjunct; that disjunct is the SEPARATE negativity check, and we model
// + pin the upper-bound disjunct (`idx_oob`), which is the load-bearing claim. The
// modeled `len` is the symbolic slice length / constant array length the emitter
// uses; whether `i` is actually non-negative (the `usize` invariant) is the deferred
// breadth, NOT faked here.
/// The canonical Clean name of the index-out-of-bounds predicate
/// `Trust.MirSem.idx_oob`.
const MIRSEM_IDX_OOB: &str = "Trust.MirSem.idx_oob";

// ---------------------------------------------------------------------------
// Step 2F — Lemma 4: SAFETY-VC adequacy (the DIVISION-BY-ZERO case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the same gap, now for div/rem-by-zero).
// Lemma 4 pins the divisor-is-zero SEMANTICS in Clean (`div_by_zero`) and proves the
// term trust-vcgen+`ground_prop` produce for `a / b` (or `a % b`) IS (def-eq) the
// divisor-zero condition. So discharging the div-by-zero VC refutes EXACTLY `b = 0`.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `div_vc_shape_matches_trust_vcgen_emission`).
//   * An integer `Rvalue::BinaryOp(Div, _, b)` / `BinaryOp(Rem, _, b)` with a
//     SYMBOLIC divisor `b` raises a `VcKind::DivisionByZero` / `RemainderByZero` VC.
//     The emitted formula is EXACTLY
//        Eq(divisor, Int(0))                  (block_defs.rs::v2_divisor_is_zero_formula)
//     where `divisor = Var(b)` and the zero is `Formula::Int(0)`. (Confirmed by
//     probing the emitter: `a / b` over i32 emits `Eq(Var b, Int 0)`.) A nonzero
//     CONSTANT divisor is `Bool(false)` (provably nonzero, no obligation), so the
//     modeled fragment is the symbolic-divisor case. See
//     `crates/trust-vcgen/src/generate/block_defs.rs::v2_divisor_is_zero_formula`.
//   * `clean_ground::ground_prop` grounds `Eq(x, y)` to `@Eq Int (ground x) (ground
//     y)`. So the div-by-zero VC `Eq(b, 0)` grounds to EXACTLY
//        `@Eq Int b (Int.ofNat 0)`            :  Prop
//     i.e. the proposition `b = 0`.
//
// THE SPEC. `div_by_zero b` is DEFINED as `b = 0` over Int
// (`@Eq Int b (Int.ofNat 0)`). This is exactly the divisor-zero condition of `a / b`:
// the division (or remainder) is UB/panics IFF the divisor `b` is zero. (`Eq` and
// `Int.ofNat` are prelude DEFINITIONS, so the spec carries no non-foundational axiom.)
//
// THE ADEQUACY (Lemma 4). The reflected div-by-zero term grounds to LITERALLY the
// spec term, so adequacy is `@Eq.{1} Prop reflected div_by_zero` witnessed by
// `Eq.refl` — kernel-checked modulo the 3 foundational axioms. A WRONG VALUE
// (`b = 1` instead of `b = 0`) changes the closed `Int.ofNat` literal, so the two
// `Prop` terms are NOT def-eq and the `Eq.refl` proof is KERNEL-REJECTED — the
// wrong-claim fails closed.
//
// SCOPE / HONEST GAP. This pins the divisor-zero EQUALITY `b = 0` — the exact
// condition the div/rem-by-zero obligation guards. The float div-by-zero (which
// routes through a bit-magnitude check, `FloatDivisionByZero`) and the SEPARATE
// signed `MIN / -1` arithmetic-overflow VC are out of THIS fragment (they are
// distinct VC kinds); this lemma is stated against the integer divisor-zero VC,
// which is the load-bearing claim for `DivisionByZero` / `RemainderByZero`.
/// The canonical Clean name of the divisor-is-zero predicate
/// `Trust.MirSem.div_by_zero`.
const MIRSEM_DIV_BY_ZERO: &str = "Trust.MirSem.div_by_zero";

// ---------------------------------------------------------------------------
// Step 2H — Lemma 5: SAFETY-VC adequacy (the SIGNED arithmetic-OVERFLOW case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the dominant unmodeled safety VC).
// Lemma 2 certifies the UNSIGNED-add overflow VC. But the most common arithmetic
// in real code is SIGNED (`i32`/`i64`), and a signed `a + b` / `a - b` raises a
// `VcKind::ArithmeticOverflow` whose reflected formula was, until now, UNMODELED —
// so a function as simple as `fn bump(x:i32){ x+1 }` could not be FULLY FAITHFUL:
// its one safety VC fell into the fail-closed "unmodeled" bucket. Lemma 5 closes
// that. It pins the machine SIGNED-overflow SEMANTICS in Clean (`sadd_overflows_iW`
// / `ssub_overflows_iW`) and proves the term trust-vcgen+`ground_prop` produce for a
// signed `BinaryOp(Add|Sub)` overflow obligation IS (def-eq) that machine condition.
// So discharging the VC refutes EXACTLY the signed-overflow condition.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `signed_overflow_vc_shape_matches_trust_vcgen_emission`).
//   * A signed `Rvalue::BinaryOp(Add|Sub, a, b)` whose result local is `i8`/`i16`/
//     `i32`/`i64` raises a `VcKind::ArithmeticOverflow{op, (i_W, i_W)}` (Int-path)
//     VC. Empirically (i32 add) the violation core is the FULL out-of-range
//     disjunction — BOTH disjuncts LIVE, unlike unsigned add where the lower one was
//     vacuous:
//        Or([ Lt(result, MIN), Gt(result, MAX) ])
//     where `result = Add(a,b)` / `Sub(a,b)`, `MIN = type_min_formula(W,true) =
//     Formula::Int(−2^(W−1))` and `MAX = type_max_formula(W,true) =
//     Formula::Int(2^(W−1)−1)`. For i32: `MIN = Int(−2147483648)`,
//     `MAX = Int(2147483647)` (probed: byte-exact). See
//     `crates/trust-vcgen/src/generate/overflow_vc.rs` (the binop overflow
//     `out_of_range`) + `crates/trust-vcgen/src/range.rs::{type_min_formula,
//     type_max_formula,signed_min,signed_max}`.
//   * `clean_ground::ground_prop` grounds that disjunction to a Clean `Prop`:
//        - `Formula::Lt(x, y)`  ↦  `Int.lt (ground x) (ground y)`   (in order)
//        - `Formula::Gt(x, y)`  ↦  `Int.lt (ground y) (ground x)`   (SWAPPED)
//        - `Formula::Or([p,q])` ↦  `Or (ground p) (ground q)`
//        - `Formula::Int(k<0)`  ↦  `int_lit_to_expr k = Int.negSucc (|k|−1)`
//        - `Formula::Int(k≥0)`  ↦  `Int.ofNat k`
//     So the signed out-of-range core grounds to EXACTLY
//        Or (Int.lt (Int.<op> a b) (Int.negSucc (2^(W−1)−1)))     -- a∘b < MIN
//           (Int.lt (Int.ofNat (2^(W−1)−1)) (Int.<op> a b))       -- MAX < a∘b
//     i.e. the proposition `(a∘b) < −2^(W−1) ∨ (2^(W−1)−1) < (a∘b)`.
//     (`Int.negSucc (2^(W−1)−1)` IS `−2^(W−1)`; we build it through the SAME
//     `int_lit` helper the grounder uses, so the literal is byte-identical — NOT
//     `Int.neg (Int.ofNat …)`, which would be a different closed term.)
//
// THE SPEC. `s<op>_overflows_iW a b` is DEFINED as that exact disjunction over Int.
// For in-range `−2^(W−1) ≤ a,b ≤ 2^(W−1)−1`, the mathematical `a∘b` overflows the
// signed width IFF it falls OUTSIDE `[−2^(W−1), 2^(W−1)−1]` — i.e. `a∘b < −2^(W−1)`
// (underflow) OR `a∘b > 2^(W−1)−1` (overflow). BOTH disjuncts are load-bearing for
// signed arithmetic (unlike unsigned add, where `a,b ≥ 0 ⇒ a+b ≥ 0` made the lower
// disjunct vacuous). `Or`/`Int.lt`/`Int.add`/`Int.sub`/`Int.ofNat`/`Int.negSucc` are
// all reducible prelude DEFINITIONS, so the spec carries no non-foundational axiom.
//
// THE ADEQUACY (Lemma 5). The reflected signed out-of-range term is LITERALLY the
// spec term, so adequacy is `@Eq.{1} Prop reflected s<op>_overflows_iW` witnessed by
// `Eq.refl` — kernel-checked modulo the 3 foundational axioms. A WRONG threshold
// (`2^31` vs `2^31−1`, or `−2^31+1` vs `−2^31`), a WRONG width, a DROPPED disjunct
// (just the overflow half), or a WRONG direction changes the closed `Prop` term, so
// the `Eq.refl` proof is KERNEL-REJECTED — every wrong claim fails closed.
//
// SCOPE / HONEST GAP. This pins the FULL signed out-of-range disjunction for ADD, SUB
// AND MUL — both live disjuncts — at widths W ∈ {8,16,32,64}, with the spec body heading
// `Int.add`/`Int.sub`/`Int.mul` respectively. The MUL adequacy is a true `Int`-level
// fact (`smul_overflows_iW a b = (a*b<MIN ∨ a*b>MAX)`), proven by the same reflexivity.
//
// THE MUL EMISSION CAVEAT (why modeling MUL closes the LIA fragment but NOT `var*var`).
// trust-vcgen emits a signed mul's overflow VC in TWO shapes:
//   * a CONSTANT-multiplier mul (`x * 4`, linear) → the SAME clean LIA disjunction
//     `Or([Lt(Int.mul a b, MIN), Gt(Int.mul a b, MAX)])` — this arm certifies it by
//     reflexivity exactly as Add/Sub.
//   * a `var*var` mul (genuinely nonlinear) → a BITVECTOR formula
//     (`Not(Or([Eq(BvExtract(BvMul(BvSignExt …)), 0), Eq(…, all-ones)]))`), NOT an
//     `F::Mul`-cored LIA disjunction. The formula-aware bridge finds no such leaf and
//     DECLINES — so the BV mul stays DEFERRED (fail-closed), never faked. The real
//     `mul_*`/`sq_nonneg` corpus is all `var*var`, so it stays HONESTLY not-faithful
//     (its product is genuinely unbounded ⇒ genuine overflow, not a missing feature).
// The wrapping-result bridge (`(a∘b) mod 2^W = a∘b ⟺ ¬overflow`) is, as for Lemma 2,
// the deferred breadth — the EQUIVALENCE to the out-of-range predicate is the
// load-bearing claim and is what we prove.

// ---------------------------------------------------------------------------
// Trust: WRAP-TIER design note (`core::num::<impl iN>::wrapping_{add,sub,mul}`,
// 2026-07-18 — arith-guarded corpus item 7). WHY the stdlib `wrapping_*` leaves are
// NOT (yet) FULLY_FAITHFUL, and what a sound wrap-VALUE tier would need. This is a
// DELIBERATE deferral, not a missing hookup — recording it so a future pass does not
// mistake the honest gap for an oversight or "fix" it by forging a discharge.
//
// THE EXTRACTED SHAPES (empirical, arith-guarded/dumps).
//   * `wrapping_add`/`wrapping_sub` lower to a STRAIGHT-LINE `_0 = BinaryOp(Add|Sub,
//     self, rhs); Return` — NO CheckedBinaryOp, NO Assert. The contract fragment
//     ALREADY models this return (`sem_binop_of_mir` maps Add/Sub → `Int.add`/`Int.sub`;
//     `sem_return_of_mir`'s BinaryOp arm accepts it), so the SHAPE witness's contract
//     conjunct (a) passes and Lemma-5 certifies the emitted signed-overflow VC's
//     ADEQUACY (LIA `Or([Lt(Int.add a b, MIN), Gt(…, MAX)])`). Verdict: SAFETY_GAP —
//     the overflow VC is faithful but genuinely UNDISCHARGEABLE, because for
//     `wrapping_add` the overflow CAN occur (that is the whole point) and there is no
//     precondition ruling it out. `function_safety_vcs_all_discharged` correctly fails.
//   * `wrapping_mul` lowers to `_0 = BinaryOp(Mul, self, rhs); Return`. Mul is ALSO
//     already in the contract fragment (`sem_binop_of_mir` → `Int.mul`) AND already a
//     modeled safety-VC kind (`signed_overflow_vc_modeled` accepts `BinOp::Mul`). But
//     the emitter (`trust-vcgen/src/generate.rs`:~19801) grounds a `var*var` signed mul
//     overflow check to a BITVECTOR formula, NOT the LIA `F::Mul` disjunction — so
//     `safety_vc_is_faithful_formula_aware` finds no LIA leaf and DECLINES, which makes
//     `function_fully_faithful_witness` return `None` (the safety-VC-faithfulness
//     sub-conjunct of the SHAPE witness fails). Verdict: SHAPE_GAP — but the cause is
//     the BV-encoded mul VC at the formula-aware def-eq bridge, NOT a missing op. Mul is
//     already "in the shape set"; there is NO sound trust-clean-only edit that moves
//     `wrapping_mul` to SAFETY_GAP (making the BV VC faithful would require the emitter
//     to grind `var*var` mul to LIA — a global change that would regress the
//     `mul_*`/`sq_nonneg` corpus — or a genuine BV↔LIA kernel bridge; both out of scope
//     and neither a "wrap" fix).
//
// NO WRAPPING-PROVENANCE MARKER. The extracted MIR of a `wrapping_*` body is a BARE
// `Add`/`Sub`/`Mul` rvalue — the wrap semantics were compiled into the type's modular
// arithmetic and are NOT recoverable from the rvalue. The ONLY exact signal is the
// enclosing def_path (`core::num::<impl iN>::wrapping_add`, an exact stdlib leaf). We do
// NOT key any modeling on a fn-name string; and even keyed on the exact def_path, see
// below why no sound VALUE tier follows.
//
// WHY NO SOUND WRAP-VALUE TIER WITH EXISTING KERNEL MACHINERY.
//   * To be VALUE-faithful, `wrapping_add`'s result must model as `(self + rhs) mod
//     2^W` (roundToWidth/truncation), NOT the unbounded `Int.add self rhs` the
//     straight-line lane emits. The `(a∘b) mod 2^W = a∘b ⟺ ¬overflow` wrapping-result
//     bridge needs `mod`/order reasoning that the def-eq (reflexivity) kernel lane
//     CANNOT close — stated at the Lemma-2 (unsigned) note above and again just above
//     here (Lemma 5). That is the SAME deferred breadth; there is no `roundToWidth`
//     value carrier in the straight-line return witness today.
//   * The uninterpreted-but-total call-return tier (W-BITINTRIN, which DOES flip the
//     saturating INTRINSICS) does NOT apply: `wrapping_add`'s body is a straight-line
//     `Add` rvalue, not a body-less `Terminator::Call` to a total intrinsic. Re-routing
//     a straight-line `Add` to an opaque carrier would (i) DOWNGRADE the faithful
//     `Int.add` model for the no-overflow case, and (ii) NOT help — trust-vcgen still
//     emits the overflow VC on the `Add`, so the verdict would stay SAFETY_GAP.
//   * Suppressing the overflow VC by def_path (claiming "wrap is defined, so no
//     obligation") WITHOUT also modeling the result as `mod 2^W` would certify the FALSE
//     value model `_0 = self + rhs` (unbounded). That is UNSOUND and is exactly the
//     forged discharge this note forbids.
//
// CONCLUSION. wrapping_add/sub stay SAFETY_GAP; wrapping_mul stays SHAPE_GAP; both are
// the honest, fail-closed states. A real wrap tier is a `mod-2^W`-value kernel lemma
// (the deferred breadth), NOT a trust-clean recognizer change.
// ---------------------------------------------------------------------------
/// The signed integer widths Lemma 5 is pinned for — `i8`/`i16`/`i32`/`i64`, whose
/// `±2^(W−1)` thresholds are closed prelude `Int.ofNat`/`Int.negSucc` literals.
/// (`i128`'s `2^127` exceeds the `i128`-domain `int_lit` literal range and is out of
/// this fragment, matching `trust-vcgen`'s bitvector/`i128` handling.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SWidth {
    /// `i8` — range `[−128, 127]`.
    W8,
    /// `i16` — range `[−32768, 32767]`.
    W16,
    /// `i32` — range `[−2147483648, 2147483647]`.
    W32,
    /// `i64` — range `[−9223372036854775808, 9223372036854775807]`.
    W64,
}

impl SWidth {
    /// The bit width `W`.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            SWidth::W8 => 8,
            SWidth::W16 => 16,
            SWidth::W32 => 32,
            SWidth::W64 => 64,
        }
    }

    /// The signed MAX `2^(W−1) − 1`, exactly the `i128` value
    /// `trust-vcgen::range::signed_max(W)` emits (`(1i128 << (W−1)) − 1`).
    #[must_use]
    pub fn max_value(self) -> i128 {
        (1i128 << (self.bits() - 1)) - 1
    }

    /// The signed MIN `−2^(W−1)`, exactly the `i128` value
    /// `trust-vcgen::range::signed_min(W)` emits (`−(1i128 << (W−1))`).
    #[must_use]
    pub fn min_value(self) -> i128 {
        -(1i128 << (self.bits() - 1))
    }

    /// Map a Trust MIR integer type (`width`, `signed`) to the modeled SIGNED width,
    /// when it is one of the pinned signed widths. `None` (out of fragment) for an
    /// unsigned type or an unmodeled width (e.g. `i128`).
    #[must_use]
    pub fn from_mir(width: u32, signed: bool) -> Option<SWidth> {
        if !signed {
            return None;
        }
        match width {
            8 => Some(SWidth::W8),
            16 => Some(SWidth::W16),
            32 => Some(SWidth::W32),
            64 => Some(SWidth::W64),
            _ => None,
        }
    }
}

/// The signed-overflow binops Lemma 5 models. ADD, SUB and MUL all ground to a clean
/// LIA out-of-range disjunction `Or([Lt(Int.<op> a b, MIN), Gt(Int.<op> a b, MAX)])`
/// over mathematical `Int` — the spec is op-uniform, the result head is the ONLY thing
/// that varies (`Int.add`/`Int.sub`/`Int.mul`).
///
/// HONEST MUL SCOPE (the load-bearing soundness caveat). The Lemma-5 *adequacy* for MUL
/// is a true `Int`-level fact (`smul_overflows_iW a b = (a*b<MIN ∨ a*b>MAX)`), proven by
/// reflexivity exactly as for Add/Sub. But the EMITTER only grounds to this clean LIA
/// disjunction for a CONSTANT-multiplier mul (`x * 4`, linear, Int-path). A general
/// `var * var` signed mul is emitted as a BITVECTOR formula (`BvMul`/`BvSignExt`/
/// `BvExtract`), NOT this disjunction — so the formula-aware bridge
/// (`safety_vc_is_faithful_formula_aware`) finds NO `Or([Lt(Mul…),Gt(Mul…)])` leaf in it
/// and DECLINES (fail-closed). Thus modeling MUL here certifies the const-multiplier LIA
/// fragment and leaves `var*var` (the real `mul_*`/`sq_nonneg` corpus) HONESTLY deferred
/// — the kind is "modeled" (necessary), but the live-grounded def-eq is the load-bearing
/// gate that the BV shape never passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignedOp {
    /// `a + b` — the result is `Int.add a b`.
    Add,
    /// `a − b` — the result is `Int.sub a b`.
    Sub,
    /// `a * b` — the result is `Int.mul a b`. Modeled only for the LIA (constant-
    /// multiplier) emission shape; a `var*var` BV-encoded mul VC declines at the
    /// formula-aware def-eq bridge (see the type-level note above).
    Mul,
}

impl SignedOp {
    /// The prelude head for this op's Int result term (`Int.add` / `Int.sub` / `Int.mul`).
    fn int_head(self) -> &'static str {
        match self {
            SignedOp::Add => "Int.add",
            SignedOp::Sub => "Int.sub",
            SignedOp::Mul => "Int.mul",
        }
    }

    /// The lowercase op tag used in the predicate name (`add` / `sub` / `mul`).
    fn tag(self) -> &'static str {
        match self {
            SignedOp::Add => "add",
            SignedOp::Sub => "sub",
            SignedOp::Mul => "mul",
        }
    }
}

/// A kernel-checked signed-overflow-VC adequacy certificate (Lemma 5): the op + width
/// and the modulo-3 verdict for `<reflected signed out-of-range> = s<op>_overflows_iW`.
/// Carries the proof that the reflected signed overflow VC IS the machine condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedOverflowAdequacyCertificate {
    /// The signed op this certifies (Add / Sub).
    pub op: SignedOp,
    /// The signed width this certifies the overflow VC adequate for.
    pub width: SWidth,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl SignedOverflowAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

/// A kernel-checked negation-overflow-VC adequacy certificate (Lemma 6): the width and
/// the modulo-3 verdict for `<reflected negation core> = neg_overflows_iW`. Carries the
/// proof that the reflected negation VC IS the machine condition `x = MIN`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NegationAdequacyCertificate {
    /// The signed width this certifies the negation overflow VC adequate for.
    pub width: SWidth,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl NegationAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

// ---------------------------------------------------------------------------
// Step 2J — Lemma 7: SAFETY-VC adequacy (the SHIFT-AMOUNT-OOB case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the last LIA-tractable unmodeled safety VC).
// A shift `x << n` / `x >> n` is UB IFF the shift amount `n` is `≥` the bit-width `W`
// of the shifted value (shifting by ≥ the width is undefined). Until now that
// `VcKind::ShiftOverflow` VC was UNMODELED, so `fn shl(x:u32, n:u32) { x << n }` could
// not be FULLY FAITHFUL. Lemma 7 closes that. It pins the machine shift-amount-OOB
// SEMANTICS in Clean (`shift_amount_oob_W`) and proves the term trust-vcgen+
// `ground_prop` produce for a `BinaryOp(Shl|Shr)` shift-amount obligation IS (def-eq)
// that machine condition. So discharging the VC refutes EXACTLY `W ≤ n`.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `shift_vc_shape_matches_trust_vcgen_emission`).
//   * A `Rvalue::BinaryOp(Shl|Shr, x, n)` raises a `VcKind::ShiftOverflow{op,
//     operand_ty, shift_ty}` VC. The emitted formula is
//        And([ shift_range(n), <invalid_shift> ])
//     where `shift_range(n)` is the in-range premise on `n`, `W = i128::from(value
//     width)` is the bit-width of the SHIFTED value, and the violation CORE
//     `<invalid_shift>` depends on the SHIFT-AMOUNT signedness:
//        - UNSIGNED amount (`n:u_W`): the single disjunct `Ge(n, Int(W))`
//          (probed i32-value/u32-amount: `Ge(Var n, Int(32))`).
//        - SIGNED amount (`n:i_W`):  the FULL disjunction `Or([Lt(n, Int(0)),
//          Ge(n, Int(W))])` — a negative-amount check OR the `≥W` check (probed
//          i32-amount: `Or([Lt(n,0), Ge(n,32)])`).
//     See `crates/trust-vcgen/src/generate/checked_vcs.rs::v2_build_shift_overflow_vc`.
//   * `clean_ground::ground_prop` grounds `Ge(x, y)` with the arguments SWAPPED to
//     `Int.le (g y) (g x)`, and `Lt(x, y)` in order to `Int.lt (g x) (g y)`. So the
//     UNSIGNED-amount CORE `Ge(n, Int(W))` grounds to EXACTLY
//        `Int.le (Int.ofNat W) n`   :  Prop          i.e. `W ≤ n`
//     and the SIGNED-amount CORE `Or([Lt(n,0), Ge(n,W)])` grounds to
//        `Or (Int.lt n (Int.ofNat 0)) (Int.le (Int.ofNat W) n)`   i.e. `n < 0 ∨ W ≤ n`.
//
// THE SPEC. `shift_amount_oob_W n` is DEFINED as `W ≤ n` over Int
// (`Int.le (Int.ofNat W) n`) — the UNSIGNED-amount machine condition. The companion
// `shift_amount_oob_signed_W n` is DEFINED as `n < 0 ∨ W ≤ n` for the SIGNED-amount
// case. Both bodies are reducible prelude `Int.le`/`Int.lt`/`Or`/`Int.ofNat`
// DEFINITIONS, so neither carries a non-foundational axiom.
//
// THE ADEQUACY (Lemma 7). The reflected shift-amount-OOB CORE term is LITERALLY the
// spec term, so adequacy is `@Eq.{1} Prop reflected shift_amount_oob_W` witnessed by
// `Eq.refl` — kernel-checked modulo the 3 foundational axioms. A `<` vs `≤` off-by-one
// (`W < n` / a `W−1` threshold instead of `W ≤ n`), a WRONG width, a WRONG direction
// (`n ≤ W`), or — for the signed case — a DROPPED disjunct changes the closed `Prop`
// term, so the `Eq.refl` proof is KERNEL-REJECTED — every wrong claim fails closed.
//
// SCOPE. This pins the shift-amount-OOB CORE for the value widths W ∈
// {8,16,32,64,128}, for BOTH unsigned and signed shift amounts (both are clean LIA).
// The shift VALUE-overflow side (the actual `x << n` result bitvector) is NOT what
// this VC is about — the emitter's `ShiftOverflow` VC is the shift-AMOUNT UB check,
// and that is exactly what we pin. NOTE the width-128 case (the former "128-bit
// shift VC width" residue): UNLIKE the overflow lanes — whose `2^W−1`/`±2^(W−1)`
// thresholds leave the closed `Int.ofNat` literal fragment at W=128 — the shift
// lane's threshold is the WIDTH LITERAL ITSELF (`Int(128)`, a small closed
// `Int.ofNat`), so the `i128`/`u128` value widths ARE modeled; nothing about them
// ever left the fragment. That is why the lane is keyed by its own `ShiftWidth`
// (with a 128 member) and not by `SWidth` (which correctly has none).
/// The shifted-VALUE widths Lemma 7 models a shift-amount-OOB threshold for — the
/// bit-width `W` of the SHIFTED value drives the `n ≥ W` UB check, and each modeled
/// `W` is a closed `Int.ofNat` literal (INCLUDING 128 — see the scope note above).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShiftWidth {
    /// 8-bit shifted value — UB threshold `n ≥ 8`.
    W8,
    /// 16-bit shifted value — UB threshold `n ≥ 16`.
    W16,
    /// 32-bit shifted value — UB threshold `n ≥ 32`.
    W32,
    /// 64-bit shifted value — UB threshold `n ≥ 64`.
    W64,
    /// 128-bit shifted value (`i128`/`u128`) — UB threshold `n ≥ 128`.
    W128,
}

impl ShiftWidth {
    /// The bit width `W` — the shift-amount-OOB threshold literal itself.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            ShiftWidth::W8 => 8,
            ShiftWidth::W16 => 16,
            ShiftWidth::W32 => 32,
            ShiftWidth::W64 => 64,
            ShiftWidth::W128 => 128,
        }
    }

    /// Map an emitted threshold / value width to the modeled shift width
    /// (`8/16/32/64/128`), else `None` (fail closed).
    #[must_use]
    pub fn from_bits(width: u32) -> Option<ShiftWidth> {
        match width {
            8 => Some(ShiftWidth::W8),
            16 => Some(ShiftWidth::W16),
            32 => Some(ShiftWidth::W32),
            64 => Some(ShiftWidth::W64),
            128 => Some(ShiftWidth::W128),
            _ => None,
        }
    }

    /// All modeled shift widths.
    pub const ALL: [ShiftWidth; 5] =
        [ShiftWidth::W8, ShiftWidth::W16, ShiftWidth::W32, ShiftWidth::W64, ShiftWidth::W128];
}

/// A kernel-checked shift-amount-OOB-VC adequacy certificate (Lemma 7): the value
/// width + shift-amount signedness and the modulo-3 verdict for
/// `<reflected shift-OOB core> = shift_amount_oob_W`. Carries the proof that the
/// reflected shift VC IS the machine condition `W ≤ n` (/ `n<0 ∨ W≤n`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShiftAdequacyCertificate {
    /// The shifted-value width this certifies the shift-amount-OOB VC adequate for.
    pub width: ShiftWidth,
    /// Whether the shift AMOUNT is signed (signed adds the `n < 0` disjunct).
    pub amount_signed: bool,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl ShiftAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

/// A kernel-checked unsigned-sub underflow-VC adequacy certificate (Lemma 8): the
/// modeled width and the modulo-3 verdict for
/// `<reflected underflow disjunct> = usub_underflows_uW`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UsubUnderflowAdequacyCertificate {
    /// The unsigned width this certifies the underflow VC adequate for.
    pub width: UWidth,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl UsubUnderflowAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

// ---------------------------------------------------------------------------
// Step 2J — Lemma 9: SAFETY-VC adequacy (the REMAINDER-BY-ZERO case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the remainder twin of Lemma 4).
// Lemma 4 pins the DIVISION divisor-zero VC. The REMAINDER (`a % b`) operation raises
// its OWN distinct `VcKind::RemainderByZero` obligation. Empirically the emitted
// formula is byte-identical to the division case (`Eq(b, 0)`), and the divisor-zero
// SEMANTICS are the same (`b = 0`). Lemma 4 already spells out a `div_by_zero b` spec
// that IS `@Eq Int b (Int.ofNat 0)`; rather than silently fold `RemainderByZero` into
// it, Lemma 9 gives the remainder VC its OWN named predicate (`rem_by_zero`) and its
// OWN adequacy proof, so the per-kind faithfulness tally is HONEST: a `%`-only function
// reports a `RemByZero` certificate, not a borrowed `DivByZero` one.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `rem_by_zero_vc_shape_matches_trust_vcgen_emission`).
//   * An integer `Rvalue::BinaryOp(Rem, _, b)` with a SYMBOLIC divisor `b` raises a
//     `VcKind::RemainderByZero` VC. The emitted formula is EXACTLY
//        Eq(divisor, Int(0))                  (block_defs.rs::v2_divisor_is_zero_formula)
//     where `divisor = Var(b)` and the zero is `Formula::Int(0)`. (Probed: `a % b`
//     over u32 emits `Eq(Var b, Int 0)` — the SAME `v2_divisor_is_zero_formula` body
//     the `Div` path uses.) A nonzero CONSTANT divisor is provably nonzero (no
//     obligation), so the modeled fragment is the symbolic-divisor case. See
//     `crates/trust-vcgen/src/generate/safety.rs` (the `RemainderByZero` arms).
//   * `clean_ground::ground_prop` grounds `Eq(x, y)` to `@Eq Int (ground x) (ground
//     y)`. So the rem-by-zero VC `Eq(b, 0)` grounds to EXACTLY
//        `@Eq Int b (Int.ofNat 0)`            :  Prop
//     i.e. the proposition `b = 0`.
//
// THE SPEC. `rem_by_zero b` is DEFINED as `b = 0` over Int (`@Eq Int b (Int.ofNat 0)`)
// — the exact divisor-zero condition the `%`-by-zero obligation guards. `Eq` and
// `Int.ofNat` are prelude DEFINITIONS, so the spec carries no non-foundational axiom.
// (The body is IDENTICAL to `div_by_zero`'s — reusing `div_by_zero_body` keeps the two
// closed terms byte-equal — but `rem_by_zero` is a SEPARATE named predicate so the
// per-kind tally distinguishes a `%` obligation from a `/` one.)
//
// THE ADEQUACY (Lemma 9). The reflected rem-by-zero term grounds to LITERALLY the spec
// term, so adequacy is `@Eq.{1} Prop reflected rem_by_zero` witnessed by `Eq.refl` —
// kernel-checked modulo the 3 foundational axioms. A WRONG VALUE (`b = 1` instead of
// `b = 0`) changes the closed `Int.ofNat` literal, so the two `Prop` terms are NOT
// def-eq and the `Eq.refl` proof is KERNEL-REJECTED — the wrong-claim fails closed.
//
// SCOPE / HONEST GAP. This pins the divisor-zero EQUALITY `b = 0` for the remainder
// obligation. The SEPARATE signed `MIN % -1` arithmetic-overflow VC (an
// `ArithmeticOverflow{op:Rem}`) is a distinct VC kind, out of THIS fragment; this lemma
// is stated against the integer `RemainderByZero` VC, which is the load-bearing claim.
/// The canonical Clean name of the remainder-divisor-is-zero predicate
/// `Trust.MirSem.rem_by_zero`.
const MIRSEM_REM_BY_ZERO: &str = "Trust.MirSem.rem_by_zero";

/// A kernel-checked remainder-by-zero-VC adequacy certificate (Lemma 9): the modulo-3
/// verdict for `<reflected rem-by-zero VC> = rem_by_zero`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RemByZeroAdequacyCertificate {
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl RemByZeroAdequacyCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

// ---------------------------------------------------------------------------
// Step 2G — the generalized safety-VC-faithfulness metric (overflow ∨ bounds ∨ div)
// ---------------------------------------------------------------------------
/// The modeled SAFETY-VC kinds whose reflected obligation MirSem certifies adequate
/// to its machine semantics. A function's safety VC must classify into one of these
/// for the function to count in the generalized `safety_vc_faithful` metric.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafetyVcKind {
    /// An unsigned-add OVERFLOW VC of a modeled width (Lemma 2).
    Overflow(UWidth),
    /// An UNSIGNED-SUBTRACTION UNDERFLOW VC of a modeled width (Lemma 8) — the single
    /// underflow disjunct `Lt(Sub(a,b), 0)` ⇒ `usub_underflows_uW` (`(a−b) < 0`).
    UnsignedSubUnderflow(UWidth),
    /// A SIGNED add/sub OVERFLOW VC of a modeled width (Lemma 5) — the FULL
    /// out-of-range disjunction `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])` ⇒
    /// `s<op>_overflows_iW`.
    SignedOverflow(SignedOp, SWidth),
    /// An UNSIGNED-MUL OVERFLOW VC of a modeled width — the CONSTANT-multiplier LIA
    /// overflow disjunct `Gt(Mul(a,b), MAX)` ⇒ `umul_overflows_uW` (`(2^W−1) < a*b`).
    /// Its own kind (distinct from the unsigned-ADD `Overflow`) so the per-kind
    /// faithfulness tally is honest. A `var*var` (BV) unsigned mul declines at the
    /// formula-aware bridge and never mints this cert.
    UnsignedMulOverflow(UWidth),
    /// An array/slice index OUT-OF-BOUNDS VC (`IndexOutOfBounds`/`SliceBoundsCheck`)
    /// — `Ge(i, len)` ⇒ `idx_oob` (Lemma 3).
    Bounds,
    /// An integer DIVISION-by-zero VC — `Eq(b, 0)` ⇒ `div_by_zero` (Lemma 4).
    DivByZero,
    /// An integer REMAINDER-by-zero VC — `Eq(b, 0)` ⇒ `rem_by_zero` (Lemma 9). Its own
    /// kind (distinct from `DivByZero`) so the per-kind faithfulness tally is honest.
    RemByZero,
    /// A signed NEGATION-overflow VC of a modeled width (Lemma 6) — the core
    /// `Eq(x, MIN)` ⇒ `neg_overflows_iW` (`x = −2^(W−1)`).
    NegationOverflow(SWidth),
    /// A SHIFT-amount-OOB VC of a modeled value width (Lemma 7) — the core
    /// `Ge(n, W)` ⇒ `shift_amount_oob_W` (`W ≤ n`; the signed-amount form adds the
    /// `n < 0` disjunct). The bool is the shift AMOUNT's signedness.
    ShiftOob(ShiftWidth, bool),
}

/// A kernel-checked safety-VC adequacy certificate spanning ALL modeled kinds: the
/// per-kind verdict that the reflected safety VC is PROVEN (modulo 3) def-eq to its
/// pinned machine-semantics condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyVcCertificate {
    /// Which modeled safety-VC kind this certifies.
    pub kind: SafetyVcKind,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: AdequacyVerdict,
}

impl SafetyVcCertificate {
    /// Whether this certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, AdequacyVerdict::ProvenModulo3)
    }
}

/// A per-kind tally of a function's CERTIFIED safety VCs (each entry is a modulo-3
/// certificate). The generalized metric counts a function iff it has ≥1 modeled
/// safety VC AND every safety VC the emitter raises classifies into a modeled kind
/// whose adequacy certifies — fail-closed on any unmodeled safety VC kind.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionSafetyVcCertificates {
    /// The unsigned-add overflow-VC certificates (Lemma 2), one per modeled width raised.
    pub overflow: Vec<SafetyVcCertificate>,
    /// The UNSIGNED-SUB underflow-VC certificates (Lemma 8), one per modeled width the
    /// function raises an unsigned `ArithmeticOverflow{op:Sub}` VC for.
    pub usub: Vec<SafetyVcCertificate>,
    /// The SIGNED add/sub overflow-VC certificates (Lemma 5), one per modeled
    /// (op, width) the function raises a signed `ArithmeticOverflow` VC for.
    pub signed_overflow: Vec<SafetyVcCertificate>,
    /// The UNSIGNED-MUL overflow-VC certificates, one per modeled width the function
    /// raises a CONSTANT-multiplier unsigned `ArithmeticOverflow{op:Mul}` VC for.
    pub umul: Vec<SafetyVcCertificate>,
    /// The bounds-VC certificate (Lemma 3) — present iff the function raises ≥1
    /// modeled array/slice index OOB VC.
    pub bounds: Option<SafetyVcCertificate>,
    /// The div-by-zero-VC certificate (Lemma 4) — present iff the function raises ≥1
    /// modeled integer DIVISION-by-zero VC.
    pub div: Option<SafetyVcCertificate>,
    /// The remainder-by-zero-VC certificate (Lemma 9) — present iff the function raises
    /// ≥1 modeled integer REMAINDER-by-zero VC.
    pub rem: Option<SafetyVcCertificate>,
    /// The signed NEGATION-overflow VC certificates (Lemma 6), one per modeled width
    /// the function raises a `NegationOverflow` VC for.
    pub negation: Vec<SafetyVcCertificate>,
    /// The SHIFT-amount-OOB VC certificates (Lemma 7), one per modeled
    /// (value width, amount signedness) the function raises a `ShiftOverflow` VC for.
    pub shift: Vec<SafetyVcCertificate>,
}

impl FunctionSafetyVcCertificates {
    /// Whether ANY modeled safety VC was certified (≥1 cert across the kinds).
    #[must_use]
    pub fn any(&self) -> bool {
        !self.overflow.is_empty()
            || !self.usub.is_empty()
            || !self.signed_overflow.is_empty()
            || !self.umul.is_empty()
            || self.bounds.is_some()
            || self.div.is_some()
            || self.rem.is_some()
            || !self.negation.is_empty()
            || !self.shift.is_empty()
    }

    /// Whether EVERY held certificate is a modulo-3 proof (a certificate set that
    /// exists is modulo-3 by construction — the builder is fail-closed — but this
    /// re-checks the invariant defensively).
    #[must_use]
    pub fn all_modulo_3(&self) -> bool {
        self.overflow.iter().all(SafetyVcCertificate::is_modulo_3)
            && self.usub.iter().all(SafetyVcCertificate::is_modulo_3)
            && self.signed_overflow.iter().all(SafetyVcCertificate::is_modulo_3)
            && self.umul.iter().all(SafetyVcCertificate::is_modulo_3)
            && self.bounds.as_ref().is_none_or(SafetyVcCertificate::is_modulo_3)
            && self.div.as_ref().is_none_or(SafetyVcCertificate::is_modulo_3)
            && self.rem.as_ref().is_none_or(SafetyVcCertificate::is_modulo_3)
            && self.negation.iter().all(SafetyVcCertificate::is_modulo_3)
            && self.shift.iter().all(SafetyVcCertificate::is_modulo_3)
    }
}

// ---------------------------------------------------------------------------
// FORMULA-AWARE safety-VC faithfulness (the model→grounder bridge).
//
// THE INTEGRITY FIX. The per-kind `check_*_adequacy(w)` lemmas prove a
// MODEL-INTERNAL fact: `reflected_core(w) = spec(w)`, where BOTH sides are hand-built
// by THIS module. That certifies nothing about the reflection the §6 pipeline
// ACTUALLY discharges — and the width `w` was read from `VcKind.operand_ty`, which the
// emitter FABRICATES for a constant shifted value (`1i32 << n` records i64 ⇒ a 64-wide
// cert over a formula whose emitted threshold is 32 — a FALSE certificate).
//
// `safety_vc_is_faithful_formula_aware` closes the bridge: for the REAL `vc.formula`
// it (1) extracts the violation core the spec models, (2) grounds that core through the
// LIVE `clean_ground::ground_prop`, (3) recovers the width/threshold FROM THE EMITTED
// FORMULA (never from `operand_ty`), and (4) kernel-checks the grounded term `is_def_eq`
// to `spec(operands)` modulo the 3 foundational axioms. The cert is minted ONLY on
// def-eq success. A formula whose emitted threshold disagrees with any modeled spec
// (the `1i32<<n` case: live-grounded `32 ≤ n`, no def-eq to a 64-width spec) FAILS
// CLOSED — no false cert. The certified term IS the live-grounded term, so the cert is
// adequate to the discharge, not a disguised identity over a shape the grounder never
// emits.
// ---------------------------------------------------------------------------
/// One leaf of a VC formula's violation tree paired with the de-Bruijn `params` map
/// (operand variable name → its bvar `Expr`) under which to ground it.
struct CoreGround<'a> {
    /// The violation-core sub-formula to ground via the LIVE `ground_prop`.
    core: &'a trust_types::Formula,
    /// The grounding environment: each operand variable name → its de-Bruijn `Expr`.
    params: std::collections::HashMap<String, Expr>,
}

// ---------------------------------------------------------------------------
// Step 4 — whole-function composition (the composed faithfulness witness)
// ---------------------------------------------------------------------------
/// A COMPOSED whole-function adequacy certificate (Goal #4, whole-function tier):
/// every operand (Lemma 1A), every rvalue (Lemma 1B), and the return witness
/// (Lemma 1C) of the function's reflected contract carries a modulo-3 kernel
/// certificate. Minted ONLY when all pieces certify (fail-closed): any uncertified
/// piece ⇒ no composed witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionAdequacyCertificate {
    /// The operand-adequacy certificates (Lemma 1A), one per reflected operand.
    pub operands: Vec<AdequacyCertificate>,
    /// The rvalue-adequacy certificates (Lemma 1B), one per reflected rvalue.
    pub rvalues: Vec<RvalueAdequacyCertificate>,
    /// The return-witness certificate (Lemma 1C, straight-line OR control-flow).
    pub ret: ReturnCertificate,
}

/// A whole-function return-adequacy certificate (Lemma 1C): a STRAIGHT-LINE return
/// (the last `_0 := rvalue` flows to the `Return` block — closed param/const or
/// SSA-temp), whose adequacy is the genuine `ground_int(return) = MirSem.eval`
/// equality. This is the ONLY return shape the whole-function tier counts.
///
/// The `ControlFlow` variant is RETAINED for the internal `eval_ite` reduction lemma
/// machinery (and its wrong-branch guard tests) but is NO LONGER minted by
/// `function_adequacy_witness` — see FIX 2 in `check_cf_return_adequacy`: the cf-return
/// lemma is a definitional unfolding (`eval_ite = eval_ite-def`), not return
/// faithfulness, so guarded returns are honestly DEFERRED from the faithfulness tally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnCertificate {
    /// A straight-line return (Lemma 1C: closed operand or exec-folded SSA temp).
    StraightLine(ReturnAdequacyCertificate),
    /// A guarded control-flow return shape (INTERNAL `eval_ite` reduction, NOT a
    /// faithfulness certificate — never minted into the whole-function tally; FIX 2).
    ControlFlow(CfReturnAdequacyCertificate),
    /// A NESTED / multi-way guarded return whose `refinementBNested` proves modulo 3 —
    /// the nested `iteI`-tree denotation ≡ the live-grounded NESTED `Ite`. ADDITIVE: a
    /// new variant for the multi-way frontier; existing variants are byte-identical.
    /// Minted (like the single-branch `ControlFlow` arm beside it) only once the
    /// nested-branch refinement kernel-proves modulo 3.
    NestedControlFlow(NestedBranchRefinementCertificate),
    /// Trust: call-spine increment — a CALL return (the FOURTH return shape): `_0`
    /// (or the traced temp) is written by a `Terminator::Call` whose callee is in
    /// the caller-supplied ALREADY-CERTIFIED registry. The return denotes the
    /// opaque `call_result` of the `Call` inductive, and the adequacy witness is a
    /// kernel-checked PER-CALL INSTANCE of the PROVEN `callRefinesContract`
    /// transport lemma (never a new axiom). ADDITIVE: minted only when a non-empty
    /// certified-callee registry is threaded down; existing variants byte-identical.
    Call(CallReturnAdequacyCertificate),
    /// Trust: CALL-THEN-PUREOP — the FIFTH return shape (closes the "Call-then-
    /// Compare" named residue, `fixtures/leaf-call-corpus/PROVENANCE.md`): the sole
    /// call writes a TEMP (not `_0` — that's [`ReturnCertificate::Call`]'s own
    /// shape), and `_0`'s sole write is a pure op (arithmetic OR comparison)
    /// consuming the call's opaque result. The adequacy witness is a kernel-checked
    /// PER-CALL INSTANCE of the SAME PROVEN `callRefinesContract` transport lemma
    /// [`ReturnCertificate::Call`] uses, applied at a WRAPPED predicate (never a new
    /// axiom — see [`call_then_pureop_adequacy_witness`]).
    CallThenPureOp(CallThenPureOpAdequacyCertificate),
    /// Trust: CALL-OP-CALL — the SIXTH return shape (closes the residue
    /// [`SemCallThenPureOp`]'s own doc names: "BOTH operands being the call
    /// result ALSO declines — not this shape"): `_0`'s sole write is a pure op
    /// over TWO call results (each from its OWN sole-written temp, either
    /// callee — including the SAME callee twice). The adequacy witness is a
    /// kernel-checked PER-CALL-PAIR instance transporting BOTH calls' opaque
    /// results through TWO nested applications of the SAME PROVEN
    /// `callRefinesContract` transport lemma (never a new axiom — see
    /// [`call_op_call_adequacy_witness`]).
    CallOpCall(CallOpCallAdequacyCertificate),
    /// Trust: CALL-RESULT-AWARE COMPOSITION — the SEVENTH return shape
    /// (closes the TO_ASCII CHAIN residue, `reports/bit-field-nested-rvalue-
    /// to-ascii-chain-2026-07-09.md`): `_0`'s sole write is a pure bitwise op
    /// combining a flat operand with the VALUE field of a checked-arith Mul
    /// whose multiplicand is a call result, chased through a bool-identity
    /// `Cast`. The adequacy witness is a kernel-checked PER-CALL INSTANCE of
    /// the SAME PROVEN `callRefinesContract` transport lemma
    /// [`ReturnCertificate::Call`] uses, applied at a BIGGER WRAPPED
    /// predicate (never a new axiom — see [`call_chain_pureop_adequacy_
    /// witness`]).
    CallChainPureOp(CallChainPureOpAdequacyCertificate),
    /// Trust: TWO-CALL CHAIN — the EIGHTH return shape (`min_max`'s
    /// `a.min(b).max(c)`): `_0` is written by a SECOND `Terminator::Call` whose
    /// callee is certified, one of whose actual arguments is the SINGLE-ASSIGNED,
    /// SINGLE-USE, non-aliased result temp of a FIRST certified call. The witness
    /// is TWO kernel-checked per-call `callReturnInstance` transports (one per
    /// call, the SAME PROVEN `callRefinesContract` [`ReturnCertificate::Call`]
    /// uses — never a new axiom); the structural recognizer carries the chain
    /// connection (the inner result flows into the outer call's argument). See
    /// [`two_call_chain_adequacy_witness`].
    TwoCallChain(TwoCallChainAdequacyCertificate),
    /// Trust: CALL-THEN-PROJECT — the NINTH return shape
    /// (`overflowing_add(a,b).0`): the sole call writes a TUPLE-typed temp whose
    /// SOLE use is a single `Field(i)` projection into `_0`. The witness is a
    /// kernel-checked per-call `callThenProjectInstance` transport of the SAME
    /// PROVEN `callRefinesContract`, applied at the FIELD-PROJECTION wrapped
    /// predicate `λx. post (idx_elem x i)` (never a new axiom — the `idx_elem`
    /// opaque total selector is the carrier `SemOperand::Field` already denotes
    /// through). See [`call_then_project_adequacy_witness`].
    CallThenProject(CallThenProjectAdequacyCertificate),
}

impl ReturnCertificate {
    /// Whether this return certificate is a genuine modulo-3 faithfulness proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        match self {
            ReturnCertificate::StraightLine(c) => c.is_modulo_3(),
            ReturnCertificate::ControlFlow(c) => c.is_modulo_3(),
            ReturnCertificate::NestedControlFlow(c) => c.is_modulo_3(),
            ReturnCertificate::Call(c) => c.is_modulo_3(),
            ReturnCertificate::CallThenPureOp(c) => c.is_modulo_3(),
            ReturnCertificate::CallOpCall(c) => c.is_modulo_3(),
            ReturnCertificate::CallChainPureOp(c) => c.is_modulo_3(),
            ReturnCertificate::TwoCallChain(c) => c.is_modulo_3(),
            ReturnCertificate::CallThenProject(c) => c.is_modulo_3(),
        }
    }
}

// ---------------------------------------------------------------------------
// Trust: call-spine increment — the CALL return shape (the #1 real-code exit).
// A caller whose return value flows out of a `Terminator::Call` to a SAFE,
// same-crate callee that is ITSELF already fully-faithful-certified. The call's
// denotation is the EXISTING `Call`/`call_result` machinery (registered at
// `register_call_inductive`/`register_call_result`), and the adequacy witness
// instantiates the PROVEN `callRefinesContract` transport lemma per call site.
// Fail-closed EVERYWHERE: uncertified/unresolved/ambiguous callee, self call,
// arity mismatch, non-Int dest, any arg/dest projection, foreign/atomic ABI, a
// second call, a re-written dest, any unmodeled statement/terminator on the
// return spine ⇒ `None`, never a false adequacy certificate.
// ---------------------------------------------------------------------------
/// A fact about an ALREADY-CERTIFIED callee, threaded down from the corpus
/// driver (`prove::prove_dump_dir` iterates callees-first and accumulates the
/// fully-faithful set). MEMBERSHIP in the registry is the Rust-side guarantee:
/// the keyed def-path was ITSELF minted a `FullFaithfulnessCertificate` (or the
/// trust-ir-primary equivalent) EARLIER in the callees-first pass — modular
/// verification's "the callee is separately verified" hypothesis.
///
/// Trust: call-requires establishment — the fact now ALSO carries the callee's
/// `#[requires]` PRECONDITION (`requires` + `param_names`), and the caller's
/// fully-faithful bar (`prove.rs`) requires every conjunct ESTABLISHED at the
/// call site with the actual arguments substituted for the formals
/// (`prove::call_site_requires_established`, discharged through the SAME
/// `vc_refute` lane the safety VCs use, under the CALLER's own preconditions +
/// type bounds). The prior honesty caveat — "the registry says nothing about
/// the callee's `#[requires]` being established; `caller(2000)` would panic
/// inside `helper` while `caller` carries a silent certificate" — is CLOSED: a
/// caller that does not establish its callee's requires does NOT count as
/// fully faithful (fail-closed). The adequacy axis is unchanged: it models the
/// call's return as the opaque `call_result` (the value the separately-verified
/// callee returns), which is denotationally faithful independent of the
/// requires establishment — the establishment is a SEPARATE, additional clause
/// of the counted verdict, exactly like safety-VC discharge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeFact {
    /// The callee's declared parameter count — the call site's actual-arg arity
    /// must match exactly (fail-closed on any mismatch: a spread/vararg/ABI
    /// mismatch is an unmodeled shape).
    pub arg_count: usize,
    /// Trust: call-requires establishment — the callee's `#[requires]`
    /// precondition as parsed conjuncts over its FORMAL PARAMETER NAMES.
    ///
    ///   * `Some(cs)` with `cs` nonempty — the COMPLETE parsed conjunct set
    ///     (one per declared clause; completeness is checked at registry-build
    ///     time by [`CalleeFact::of_certified`]).
    ///   * `Some(vec![])` — the callee declares NO requires: every call site is
    ///     VACUOUSLY established (the pre-increment behavior, unchanged).
    ///   * `None` — the precondition is NOT fully known (a declared clause did
    ///     not parse into a `Formula`): every call site FAILS CLOSED.
    pub requires: Option<Vec<trust_types::Formula>>,
    /// The callee's formal parameter names (locals `1..=arg_count`, in
    /// declaration order). A `None` entry is an unnamed formal — it cannot be
    /// referenced by name in a requires clause, and the establishment's
    /// free-variable check fails closed on any variable left unmapped.
    pub param_names: Vec<Option<String>>,
}

impl CalleeFact {
    /// Build the fact for a JUST-CERTIFIED callee from its own
    /// `VerifiableFunction` — the registry-build path (`prove_dump_dir`).
    ///
    /// FAIL-CLOSED COMPLETENESS: `requires` is `Some(func.preconditions)` only
    /// when the parsed conjunct count matches the DECLARED clause count (both
    /// the raw `spec.requires` strings and the `ContractKind::Requires`
    /// contract entries). Any mismatch — a clause the spec parser could not
    /// lower — makes the precondition UNKNOWN (`None`), so no call site can
    /// ever treat a partially-parsed precondition as the whole one.
    #[must_use]
    pub fn of_certified(func: &trust_types::VerifiableFunction) -> CalleeFact {
        let declared = func.spec.requires.len().max(
            func.contracts
                .iter()
                .filter(|c| matches!(c.kind, trust_types::ContractKind::Requires))
                .count(),
        );
        // Trust: discriminant-guard leaf — the extractor APPENDS synthesized
        // ALWAYS-TRUE facts to `preconditions` alongside the parsed declared
        // clauses (`trust-mir-extract::enum_discriminant_range_preconditions`:
        // the enum-tag range `_d ∈ {tags}` over an INTERNAL non-argument temp;
        // `either::is_left`'s dump carries exactly one). Those are type
        // tautologies bound to the callee's INTERNAL vocabulary — true at every
        // well-typed call site by construction, NEVER a caller obligation (the
        // extractor's own doc: a parameter-named precondition "would become a
        // call-site PROVE obligation — a separate mechanism", so it emits these
        // for non-argument locals only). Counting them against `declared` made
        // the completeness gate below return `None` for ANY callee whose body
        // reads an enum discriminant — fail-closed but the wrong population. So:
        // partition them out via the TIGHT shape+vocabulary recognizer
        // (`is_internal_discriminant_range_fact` — the exact emitted shape over
        // an exact internal-local reference; anything unrecognized stays in the
        // declared count and the gate still fails closed). The extractor's OTHER
        // synthesized families (char-range over internal locals; the int
        // type-range over PARAMETER names) are NOT partitioned yet — a fixture
        // exhibiting them will measure as a `requires: None` decline (fail
        // closed, never unsound), the honest signal to extend the recognizer.
        // Trust: structural-fold rung E — the doc note below anticipated this
        // extension: the extractor's SECOND synthesized family, the INT
        // TYPE-RANGE fact over a PARAMETER name (`0 ≤ p ∧ p ≤ u32::MAX` for a
        // `u32` formal), is now partitioned out by the TIGHT recognizer
        // `is_parameter_type_range_fact` — the bounds must be EXACTLY the
        // declared parameter type's full range, which every well-typed call
        // site satisfies by construction (rustc types the actual), the same
        // type-tautology argument as the discriminant family. Anything looser
        // (a narrowed range, a non-parameter var, a non-Int formal) stays in
        // the declared count and the completeness gate still fails closed.
        let caller_vocab: Vec<trust_types::Formula> = func
            .preconditions
            .iter()
            .filter(|f| {
                !is_internal_discriminant_range_fact(f, &func.body)
                    && !is_parameter_type_range_fact(f, &func.body)
                    // Trust: Item 4 — the char VALIDITY-RANGE synthesized fact over an
                    // INTERNAL local (the `char::is_ascii` leaf's `_3 ∈ scalar range`):
                    // a type tautology, partitioned out like the other two families.
                    && !is_internal_char_range_fact(f, &func.body)
            })
            .cloned()
            .collect();
        let requires = if caller_vocab.len() == declared {
            Some(caller_vocab)
        } else {
            None // a declared clause did not parse — the precondition is unknown.
        };
        let param_names = (1..=func.body.arg_count)
            .map(|i| func.body.locals.get(i).and_then(|l| l.name.clone()))
            .collect();
        CalleeFact { arg_count: func.body.arg_count, requires, param_names }
    }
}

/// The recognized CALL-RETURN shape: the caller's `_0` (directly, or via a
/// single moved temp) is written by exactly one `Terminator::Call` to a
/// registry-certified callee, with every actual argument a modeled scalar
/// operand. Produced ONLY by [`sem_call_return_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallReturn {
    /// The RESOLVED callee def-path — a key of the certified registry.
    pub callee: String,
    /// The callee's index in the (sorted) certified registry — the `Nat`
    /// callee-id the kernel `Call.mk` instance names.
    pub callee_id: u64,
    /// The modeled actual-argument operands (each gets Lemma-1A certified).
    pub args: Vec<SemOperand>,
}

// ---------------------------------------------------------------------------
// Trust: W-BITINTRIN — the PURE, TOTAL, BODY-LESS compiler bit-intrinsics
// (`intrinsics::{ctpop,cttz,ctlz,bswap,bitreverse}`, ARITY 1) plus the ARITY-2
// TOTAL saturating intrinsics (`intrinsics::{saturating_add,saturating_sub}`) as
// a FIRST-CLASS reflected return value. The DIRECT ANALOGUE of the ptr offset/read
// intrinsic modeling (`reflect::PtrArith`): a body-less `Terminator::Call` to a
// KNOWN pure intrinsic def-path is resolved to the opaque, uninterpreted-but-TOTAL
// `call_result` of that call — the SAME kernel machinery [`sem_call_return_of_mir`]
// uses for a certified callee, with NO new axiom and NO new opaque constant.
//
// HONESTY TIER — UNINTERPRETED-BUT-TOTAL (exactly the `idx_elem` tier). We do NOT
// model the popcount / count-trailing-zeros / SATURATION VALUE theory:
// `count_ones(self)` does NOT ground to "the number of 1 bits in `self`", and
// `saturating_add(a, b)` does NOT ground to "the clamped sum" (NO saturation-value
// claim). Instead each grounds to `call_result (Call.mk <intrinsic-id> arg0 ret)` —
// a deterministic, TOTAL Int function of the call, whose ONLY asserted property is
// that the reflection is FAITHFUL to what the MIR computes (the return IS that
// intrinsic's result). This is shape-faithful, not value-faithful: `count_ones` is
// `_0 = ctpop(self); Return` and `saturating_add` is `_0 = saturating_add(self,
// rhs); Return`, so the return literally IS a pinned-total intrinsic result
// returned — FULLY_FAITHFUL without a bit-counting/clamping theory, precisely as
// `s[i]` is faithful via the uninterpreted-total `idx_elem` without an
// array-content theory.
//
// ARITY-2 SOUNDNESS (the saturating extension). The kernel `Call.mk (callee : Nat)
// (arg : Operand)(ret : Int)` carries a SINGLE `arg` operand, and
// [`call_return_adequacy_witness`] tags the instance with `args.first()` (arg0).
// That tag is SEMANTICALLY VACUOUS — the transport lemma `callRefinesContract` is a
// tautology `∀ post ∀ ret, post(call_result c) → post(call_result c)`, universal
// over the Call, so the certificate makes NO claim tying the opaque result to arg0
// alone (or to the arg count). BOTH actual args STILL get Lemma-1A certified at the
// recognizer→witness boundary; only the opaque NAMING tag uses arg0. So keeping the
// unary `Call.mk` shape for a binary intrinsic is byte-identical soundness — the
// model asserts only "the return is SOME total Int of the call", which is TRUE for a
// 2-arg total intrinsic exactly as for a 1-arg one. We do NOT extend the `Call.mk`
// inductive (that would change the recursor arity and break `exec`).
//
// SOUNDNESS — why "no requires to establish" is CORRECT here (the load-bearing
// gate). `function_call_requires_established` treats this shape as "nothing
// registry-backed to establish" (it falls through to `true`). That is sound ONLY
// because every admitted intrinsic is TOTAL — defined on every bit pattern with
// no precondition (`cttz(0)`/`ctlz(0)` are the bit width; `ctpop`/`bswap`/
// `bitreverse` are total permutations/counts; `saturating_add`/`saturating_sub`
// CLAMP to the type's MIN/MAX on overflow — NO UB, NO panic, defined on every
// input pair). The PARTIAL siblings `cttz_nonzero`/`ctlz_nonzero` (UB on 0) and
// every `unchecked_*` intrinsic (`unchecked_add`/`unchecked_mul`/… — UB on
// overflow) carry a real precondition and are DELIBERATELY EXCLUDED from the pinned
// set — admitting one would certify a claim silent about its UB. This is the exact
// analogue of the ptr lane's fail-closed bounds VC: there the offset carries a
// separate obligation; here totality is what makes the empty obligation set honest.
/// A PINNED, PURE, TOTAL, body-less compiler intrinsic — the modeled set. Each is a
/// deterministic total function of its integer argument(s) (no precondition, defined
/// on every bit pattern / input pair). The ARITY-1 bit-intrinsics
/// (`ctpop`/`cttz`/`ctlz`/`bswap`/`bitreverse`) and the ARITY-2 saturating
/// intrinsics (`saturating_add`/`saturating_sub`) share this enum because they share
/// the SAME uninterpreted-but-total honesty tier (see [`arity`] for the per-variant
/// arity). Partial siblings (`cttz_nonzero`/`ctlz_nonzero`) and every
/// effectful/`unchecked_*` intrinsic (`unchecked_add`/`unchecked_mul`/… — UB on
/// overflow) are DELIBERATELY absent (fail-closed), because their UB/precondition is
/// not modeled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PureTotalIntrinsic {
    /// `ctpop(x)` — population count (number of 1 bits). Backs `count_ones`
    /// (and `count_zeros`, via `ctpop(!x)`). Total. ARITY 1.
    Ctpop,
    /// `cttz(x)` — count trailing zeros. Backs `trailing_zeros`. Total
    /// (`cttz(0)` = bit width — distinct from the PARTIAL `cttz_nonzero`). ARITY 1.
    Cttz,
    /// `ctlz(x)` — count leading zeros. Backs `leading_zeros`. Total
    /// (`ctlz(0)` = bit width — distinct from the PARTIAL `ctlz_nonzero`). ARITY 1.
    Ctlz,
    /// `bswap(x)` — reverse byte order. Backs `swap_bytes`. Total. ARITY 1.
    Bswap,
    /// `bitreverse(x)` — reverse bit order. Backs `reverse_bits`. Total. ARITY 1.
    Bitreverse,
    /// `saturating_add(a, b)` — CLAMPS the sum to `[T::MIN, T::MAX]` on overflow.
    /// Backs `T::saturating_add`. TOTAL (no UB, no panic — defined on every input
    /// pair). ARITY 2. The synthetic callee-id is pinned to `6` (past `count_ones`'s
    /// `5`; see [`synthetic_callee_id`]) to keep the tiny-`Nat` distinctness the
    /// tests assert, though the id is semantically vacuous.
    SaturatingAdd = 6,
    /// `saturating_sub(a, b)` — CLAMPS the difference to `[T::MIN, T::MAX]` on
    /// overflow. Backs `T::saturating_sub`. TOTAL (no UB, no panic). ARITY 2.
    /// Synthetic callee-id `7`.
    SaturatingSub = 7,
}

impl PureTotalIntrinsic {
    /// STRICT, fail-closed classification of a `Terminator::Call` callee path
    /// into the pinned pure-total intrinsic set. Accepts ONLY a path carrying
    /// [`trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX`], which the MIR extractor
    /// stamps after `TyCtxt` confirms the direct `FnDef` is an exact modeled
    /// compiler intrinsic. After removing that non-source-spellable prefix and
    /// generic args (`::<…>`), the segments must be exactly
    /// `intrinsics::<name>` (the dump's truncated spelling) or
    /// `{core,std}::intrinsics::<name>`. An unmarked source-spellable lookalike,
    /// a marked path outside that exact grammar, a partial sibling
    /// (`cttz_nonzero`), partial arithmetic sibling (`unchecked_add`), or any
    /// unmodeled intrinsic returns `None` (never guessed pure). The modeled names
    /// include unary bit intrinsics and binary saturating add/sub. The marker
    /// prevents a collision in compiler-extracted DefPaths; it is forgeable in hand-edited
    /// serialized IR, whose authority must instead come from the authenticated
    /// compiler transport/session.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        // Trust (spelling reconciliation, 2026-07-18 — ASYMMETRIC marker policy).
        // The MIR extractor stamps the non-source-spellable
        // `@trust-rustc-intrinsic::` marker for the body-less BIT intrinsics
        // (ctpop/cttz/ctlz/bswap/bitreverse — the num/bitmethods corpora dump
        // them MARKED, e.g. `@trust-rustc-intrinsic::intrinsics::ctpop::<u8>`).
        // A bit-intrinsic call therefore ALWAYS arrives marked, so an UNMARKED
        // bit-intrinsic def-path is a forgery and MUST decline — the invariant
        // pinned by `pure_total_intrinsic_classify_is_strict` and
        // `bit_intrinsic_recognizer_fails_closed_on_forgeries` (e.g.
        // `std::intrinsics::bswap::<u64>` / `intrinsics::ctpop::<u8>` unmarked
        // must decline).
        //
        // The ARITY-2 SATURATING intrinsics were added later and the extractor
        // does NOT stamp them: a real `T::saturating_{add,sub}` body calls the
        // intrinsic with the LEGACY `[core|std]::intrinsics::saturating_{add,sub}`
        // def-path, UNMARKED (exactly what the committed num corpus dumps carry —
        // `std::intrinsics::saturating_add::<i32>`). Requiring the marker for
        // these would decline every real saturating call (a capability loss).
        //
        // Hence: the MARKED lane admits ANY modeled intrinsic; the UNMARKED
        // legacy lane admits ONLY the saturating pair. This preserves the
        // bit-intrinsic forgery gate intact while recognizing the (marker-less)
        // saturating spelling. Admitting an unmarked saturating path is benign
        // even against a hand-forged IR: both saturating intrinsics are TOTAL
        // (clamp on overflow, no UB/precondition), so the opaque `call_result`
        // model asserts nothing a forgery could exploit — unlike a partial
        // `unchecked_*` sibling, which is excluded by name on BOTH lanes.
        if let Some(marked) = callee.strip_prefix(trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX) {
            return Self::classify_intrinsic_segments(marked);
        }
        // UNMARKED legacy spelling — the saturating pair ONLY. Every bit-intrinsic
        // MUST carry the marker (handled above); an unmarked one fails closed here.
        match Self::classify_intrinsic_segments(callee) {
            Some(k @ (PureTotalIntrinsic::SaturatingAdd | PureTotalIntrinsic::SaturatingSub)) => {
                Some(k)
            }
            _ => None,
        }
    }

    /// The shared segment grammar for an intrinsic def-path with the marker (if
    /// any) already removed: drop generic segments, require `intrinsics` as the
    /// penultimate segment, allow at most one `core`/`std` crate root, and map
    /// the exact pinned name to its variant. A forged crate root (`evil::`), a
    /// malformed structure (`a::intrinsics::x::b`), a partial sibling
    /// (`cttz_nonzero`/`unchecked_add`), or an unmodeled name all decline.
    fn classify_intrinsic_segments(callee: &str) -> Option<Self> {
        // Drop the monomorphization/generic segments (`<u8>`, `<impl …>`).
        let segs: Vec<&str> = callee.split("::").filter(|s| !s.starts_with('<')).collect();
        let name = *segs.last()?;
        // The segment immediately before the method name must be `intrinsics`.
        let n = segs.len();
        if n < 2 || segs[n - 2] != "intrinsics" {
            return None;
        }
        // At most one crate-root segment before `intrinsics`, and it must be a
        // real std/core root (never a forged wrapper crate).
        match n {
            2 => {} // `intrinsics::<name>` — the dump's truncated spelling.
            3 if matches!(segs[0], "core" | "std") => {}
            _ => return None, // extra/foreign segments ⇒ fail closed.
        }
        match name {
            "ctpop" => Some(PureTotalIntrinsic::Ctpop),
            "cttz" => Some(PureTotalIntrinsic::Cttz),
            "ctlz" => Some(PureTotalIntrinsic::Ctlz),
            "bswap" => Some(PureTotalIntrinsic::Bswap),
            "bitreverse" => Some(PureTotalIntrinsic::Bitreverse),
            // ARITY-2 TOTAL saturating intrinsics — clamp on overflow, no UB/panic.
            "saturating_add" => Some(PureTotalIntrinsic::SaturatingAdd),
            "saturating_sub" => Some(PureTotalIntrinsic::SaturatingSub),
            // cttz_nonzero / ctlz_nonzero / unchecked_add / unchecked_mul / transmute
            // / saturating_mul (not a real intrinsic) / … ⇒ decline (partial or
            // unmodeled).
            _ => None,
        }
    }

    /// The intrinsic's EXACT arity — the recognizer's arity gate fails closed on any
    /// mismatch (a forgery / misextraction). The bit-intrinsics are UNARY (one
    /// integer argument); the saturating intrinsics are BINARY (two).
    #[must_use]
    pub fn arity(self) -> usize {
        match self {
            PureTotalIntrinsic::SaturatingAdd | PureTotalIntrinsic::SaturatingSub => 2,
            PureTotalIntrinsic::Ctpop
            | PureTotalIntrinsic::Cttz
            | PureTotalIntrinsic::Ctlz
            | PureTotalIntrinsic::Bswap
            | PureTotalIntrinsic::Bitreverse => 1,
        }
    }

    /// A STABLE, deterministic `call_result` callee-id for this intrinsic. The
    /// kernel transport lemma `callRefinesContract` is UNIVERSAL over the `Call`
    /// value, so the concrete id is semantically vacuous — it only NAMES which
    /// call. It MUST be SMALL: the kernel encodes it as a `Nat` literal inside
    /// `Call.mk`, and the certified-callee lane's own ids are the tiny registry
    /// indices `0..N` (the sizes `nat_lit` / def-eq are tuned for). A large id
    /// (e.g. a hash) can drive pathological `Nat` reduction in the kernel proof's
    /// def-eq — so this stays in the intrinsic-enum's small range: the bit-intrinsics
    /// occupy `0..5`, `count_ones` (the pinned method) takes `5`, and the saturating
    /// intrinsics take `6`/`7` (explicit discriminants that SKIP `5` to stay distinct
    /// from `count_ones`). All ids remain `< 8`. The certificate is self-contained
    /// per function (it never composes against the registry), so overlap with a
    /// registry index is harmless.
    #[must_use]
    pub fn synthetic_callee_id(self) -> u64 {
        self as u64
    }
}

/// A pinned pure-total callable accepted without a certified-callee registry
/// entry: either a compiler-marked unary bit or binary saturating intrinsic, or
/// a stdlib method whose body is the already-certified bit-intrinsic shape. Each
/// carries its exact arity and a small stable synthetic `Call.mk` callee id.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PinnedTotalCallable {
    Intrinsic(PureTotalIntrinsic),
    Method(PinnedTotalMethod),
}

/// Pinned total stdlib methods whose exact implementation family is known to be
/// a pure, total bit intrinsic. The set is deliberately closed and tiny.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PinnedTotalMethod {
    /// Primitive-integer `count_ones`, used by `count_zeros` as
    /// `(!self).count_ones()`.
    CountOnes,
}

impl PinnedTotalMethod {
    /// Accept only the canonical primitive-integer inherent-method spelling.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        let segments: Vec<&str> =
            callee.split("::").filter(|segment| !segment.starts_with('<')).collect();
        if segments.as_slice() != ["num", "count_ones"] {
            return None;
        }
        let impl_segment = callee.split("::").find(|segment| segment.starts_with("<impl "))?;
        let receiver = impl_segment
            .trim_start_matches("<impl ")
            .trim_end_matches('>')
            .split_whitespace()
            .next()?;
        match receiver {
            "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i32" | "i64"
            | "i128" | "isize" => Some(Self::CountOnes),
            _ => None,
        }
    }
}

impl PinnedTotalCallable {
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        PureTotalIntrinsic::classify(callee)
            .map(Self::Intrinsic)
            .or_else(|| PinnedTotalMethod::classify(callee).map(Self::Method))
    }

    /// EXACT arity — the bit-intrinsics and `count_ones` are UNARY (one integer
    /// argument); the saturating intrinsics are BINARY (delegated via `i.arity()`).
    #[must_use]
    pub fn arity(self) -> usize {
        match self {
            Self::Intrinsic(intrinsic) => intrinsic.arity(),
            Self::Method(PinnedTotalMethod::CountOnes) => 1,
        }
    }

    /// A SMALL, stable synthetic `Call.mk` callee-id (semantically vacuous — the
    /// transport lemma is universal over the `Call`; see
    /// [`PureTotalIntrinsic::synthetic_callee_id`]). The bit-intrinsics occupy `0..5`;
    /// `count_ones` takes `5`; the saturating intrinsics take `6`/`7` — all distinct
    /// within the tiny `< 8` range, self-contained per function.
    #[must_use]
    pub fn synthetic_callee_id(self) -> u64 {
        match self {
            Self::Intrinsic(intrinsic) => intrinsic.synthetic_callee_id(),
            Self::Method(PinnedTotalMethod::CountOnes) => 5,
        }
    }
}

// ---------------------------------------------------------------------------
// Trust: CALL-THEN-PUREOP — closes the "Call-then-Compare" named residue this
// corpus's PROVENANCE.md names (`arrayvec::ArrayVec::<T,CAP>::is_empty`): the sole
// call writes a TEMP `_t` (not `_0` directly — that's `sem_call_return_of_mir`'s own
// shape, tried FIRST at every call site, left byte-identical), and `_0`'s SOLE write
// is a PURE `Rvalue::BinaryOp` consuming `_t` as one operand and a param/const as
// the other. This is a genuinely common real-crate shape (`is_empty` = `len() ==
// 0`, and more generally any comparison or arithmetic op applied to a call
// result), one level removed from the bare call-return passthrough.
// ---------------------------------------------------------------------------
/// The pure op a CALL-THEN-PUREOP shape applies to the call's opaque result: an
/// arithmetic op (`SemBinOp` — reuses the Lemma-1B fragment `sem_binop_of_mir`
/// already models) or a comparison op (`SemCmpOp` — reuses the Lemma-1C-cf guard
/// fragment `sem_cmpop_of_mir` already models, applied here as a returned VALUE,
/// not a branch discriminant).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallThenOp {
    /// `op(callResult, other)` / `op(other, callResult)` — an arithmetic op.
    Bin(SemBinOp),
    /// `op(callResult, other)` / `op(other, callResult)` — a comparison op.
    Cmp(SemCmpOp),
    /// A same-width signedness-reinterpretation cast of the call result. The
    /// unary result is carried through the same type-keyed opaque projection
    /// used by [`SemOperand::Cast`]; `other` is an ignored closed dummy.
    Cast(u64, bool),
}

/// The recognized CALL-THEN-PUREOP shape: the sole call writes a temp `_t`, and
/// `_0`'s sole write is `op(callResult, other)` (`call_is_lhs = true`) or
/// `op(other, callResult)` (`call_is_lhs = false`). Produced ONLY by
/// [`sem_call_then_pureop_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallThenPureOp {
    /// The recognized call (resolved certified callee + modeled args) writing `_t`.
    pub call: SemCallReturn,
    /// The pure op `_0`'s sole write applies.
    pub op: CallThenOp,
    /// The NON-call operand (a modeled param/const — see
    /// [`call_then_pureop_adequacy_witness`]'s scope note on the kernel side).
    pub other: SemOperand,
    /// Whether the call's result is the op's FIRST (`true`) or SECOND (`false`)
    /// operand.
    pub call_is_lhs: bool,
}

// ---------------------------------------------------------------------------
// Trust: CALL-OP-CALL — closes the residue [`sem_call_then_pureop_of_mir`]'s own
// doc names ("BOTH operands being the call result ALSO declines — not this
// shape"): a body with EXACTLY TWO `Terminator::Call`s, each writing its OWN
// sole-written temp (never `_0`, never a parameter), whose results are the pure
// op's TWO operands (`Stack::is_full`'s `len() == capacity()`, `Stack::
// remaining`'s `capacity() - len()`, `Stack::double_len`'s `len() + len()` —
// the SAME callee twice, allowed). The op reaches `_0` either DIRECTLY (`_0 :=
// BinaryOp(op, _a, _b)` — `is_full`'s `Eq`) or through the EXISTING
// checked-arith tuple modeling (`_t := CheckedBinaryOp(op, _a, _b)`, `_0 :=
// Use(_t.0)` — `remaining`'s `Sub`, `double_len`'s `Add`; REUSES the SAME
// tuple/`.0`-field shape [`resolve_checked_field_rvalue`] already models,
// generalized here to BOTH operands being call-result temps rather than a
// param/const).
// ---------------------------------------------------------------------------
/// The recognized CALL-OP-CALL shape: `_0`'s sole write is a pure op over TWO
/// call results (`call_a`'s result is the op's LEFT operand, `call_b`'s the
/// RIGHT). Produced ONLY by [`sem_call_op_call_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallOpCall {
    /// The call whose result is the op's LEFT operand.
    pub call_a: SemCallReturn,
    /// The call whose result is the op's RIGHT operand.
    pub call_b: SemCallReturn,
    /// The pure op combining the two call results.
    pub op: CallThenOp,
}

// ---------------------------------------------------------------------------
// Trust: M6 rung 8 — CALL-OR-CALL (short-circuit `||` of TWO CALLS). Closes the
// mission's ||-OF-CALLS residue's FOUNDATIONAL compositional primitive: unlike
// [`sem_call_op_call_of_mir`] (which requires a straight-LINE spine — both calls
// UNCONDITIONALLY execute), this recognizes the genuinely BRANCHING short-circuit
// `||` MIR shape rustc emits for `callee_a(..) || callee_b(..)`:
//
//   bb0: _a := Call(callee_a, args_a) -> bb1
//   bb1: switchInt(move _a) -> [0: bb_false, otherwise: bb_true]
//   bb_true:  _0 := const true; goto bb_ret
//   bb_false: _0 := Call(callee_b, args_b) -> bb_ret
//   bb_ret:   return
//
// SHORT-CIRCUIT HONESTY (fail-closed by construction, not by a side condition):
// `callee_b` is recognized ONLY as the SOLE terminator of the "false" switch arm —
// it is NEVER admitted as a straight-line-preceding call (that is
// `sem_call_op_call_of_mir`'s shape, which this recognizer's own `call_count`-based
// scan structurally cannot produce: a body containing this exact branching pattern
// has NO acyclic Goto-only walk from entry to Return through BOTH calls, so
// `sem_call_op_call_of_mir` itself already declines it). The kernel-side witness
// ([`crate::trustir_call::check_call_or_call_instance`]) never claims `callee_b`
// unconditionally evaluates — see that function's doc for the encoding.
// ---------------------------------------------------------------------------
/// The recognized CALL-OR-CALL shape: `callee_a`'s Bool result is the switch
/// discriminant; `callee_b` is called ONLY on the false arm, its result flowing
/// DIRECTLY into `_0`. Produced ONLY by [`sem_call_or_call_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallOrCall {
    /// The call whose Bool result is the switch discriminant (ALWAYS evaluated).
    pub call_a: SemCallReturn,
    /// The call evaluated ONLY when `call_a`'s result is `false` (the short-circuit
    /// arm).
    pub call_b: SemCallReturn,
}

// ---------------------------------------------------------------------------
// Trust: M6 rung 9 — CALL-OR-GUARDED-COMPARE (the RICHER-|| ARM). Generalizes
// [`sem_call_or_call_of_mir`]'s false arm from a BARE second call to a small
// guarded sub-computation: a field read, a second call, then a comparison of
// the two — `Abstractor::should_descend`'s REAL shape:
//
//   bb0: _3 := Call(has_fvar_quick, expr) -> bb1
//   bb1: switchInt(move _3) -> [0: bb3, otherwise: bb2]
//   bb2: _0 := true; goto bb5
//   bb3: _4 := (*self).depth              [FIELD READ]
//        _5 := Call(loose_bvar_range, expr) -> bb4   [SECOND CALL]
//   bb4: _0 := Lt(_4, _5); goto bb5       [COMPARE, not a bare call]
//   bb5: return
//
// `sem_call_or_call_of_mir` honestly declines this (its false arm hard-requires
// NO statements and a call writing `_0` directly) — see its own module doc's
// honesty note. This is a SEPARATE, ADDITIVE recognizer, not a modification of
// it: the STRICT "two bare calls" shape stays reachable and unchanged.
//
// The kernel witness ([`crate::trustir_call::check_call_or_guarded_compare_
// instance`]) reuses the SAME `callRefinesContract` transport (applied twice,
// nested) CALL-OR-CALL uses, generalized with a THIRD ∀-bound `fieldVal`
// parameter (mirroring CALL-THEN-PUREOP's own PARAM-operand generalization) —
// it never claims `callee_b` unconditionally evaluates; see that function's doc
// for the short-circuit-honesty boundary, identical in kind to CALL-OR-CALL's.
// ---------------------------------------------------------------------------
/// The recognized CALL-OR-GUARDED-COMPARE shape: `callee_a`'s Bool result is the
/// switch discriminant (ALWAYS evaluated); on the false arm, an entry-time FIELD
/// READ and a second call `callee_b` (evaluated ONLY on that arm) feed a
/// comparison whose Bool result is `_0`. Produced ONLY by
/// [`sem_call_or_guarded_compare_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallOrGuardedCompare {
    /// The call whose Bool result is the switch discriminant (ALWAYS evaluated).
    pub call_a: SemCallReturn,
    /// The call evaluated ONLY when `call_a`'s result is `false`.
    pub call_b: SemCallReturn,
    /// The comparison's non-call operand — an entry-time FIELD read of a
    /// parameter (mirrors [`sem_call_then_pureop_of_mir`]'s FIELD-READ `other`
    /// operand — the SAME `Lifter::should_descend`-class fixed-scalar reasoning).
    pub field: SemOperand,
    /// The comparison op.
    pub cmp_op: SemCmpOp,
    /// Whether the field operand is the comparison's LHS (`field OP callB`) —
    /// `false` means `callB OP field`.
    pub field_is_lhs: bool,
}

// ---------------------------------------------------------------------------
// Trust: CALL-RESULT-AWARE COMPOSITION (2026-07-09) — closes the TO_ASCII CHAIN
// residue named by `reports/bit-field-nested-rvalue-to-ascii-chain-2026-07-09.md`:
// `to_ascii_{lower,upper}case`'s 4-hop shape
//
//   _5 := Call is_ascii_uppercase(self) -> bool
//   _4 := Cast(Move(_5), u8)                          // bool -> u8, IDENTITY
//   _6 := CheckedBinaryOp(Mul, Copy(_4), Const(32))   // (u8, bool) tuple
//   _3 := Use(Move(_6.0))
//   _0 := BinaryOp(BitOr, Move(_2), Move(_3))          // self | (flag*32)
//
// — an opaque CALL result flowing THROUGH a Cast into a checked-arithmetic
// operand slot, then through the tuple's value-field projection into the
// final pure op. None of the landed call recognizers admit this:
// `sem_call_return_of_mir` is only a direct passthrough; `sem_call_then_
// pureop_of_mir` is one hop (the RAW call-dest temp consumed directly, no
// Cast/CheckedBinaryOp/projection between); `sem_call_op_call_of_mir` needs
// BOTH operands to be call results, and also does not admit a Cast. This
// section builds a STRATIFIED, additive resolution family — [`ChainOperand`]
// — that walks a `Cast` hop down to a call-destination LEAF, and a new
// recognizer, [`sem_call_chain_pureop_of_mir`], that composes it with the
// EXISTING checked-arith tuple/`.0`-field shape [`resolve_checked_field_
// rvalue`]/[`sem_call_op_call_of_mir`]'s own inline tuple arm already model.
//
// KERNEL SIDE: ZERO new Clean declarations, ZERO new axioms. The proven
// `callRefinesContract` transport lemma is universally quantified over ANY
// predicate `post`; [`call_then_pureop_instance_type_param`]/[`call_then_
// pureop_instance_proof_param`] already generalize it to an ARBITRARY `wrap :
// Expr -> Expr -> Expr` closure (see their doc: "`wrap` embeds the pure op
// via the ALREADY-MODELED pieces"). This section's kernel witness,
// [`call_chain_pureop_instance_verdict`], REUSES those two functions
// VERBATIM — unchanged — with a `wrap` that ALSO composes the inner
// checked-arith Mul (the SAME `int_binop_expr` every unchecked/checked-arith
// VALUE in this file already grounds through — `resolve_checked_field_
// rvalue`'s own reasoning: field 0 of a checked op grounds IDENTICALLY to the
// unchecked op). The bool -> int CAST hop needs NO Expr-level content at all:
// MirSem's own established convention (see `bool_as_int`'s doc) already
// models a Bool value as 0/1 on the SAME opaque Int carrier a call result is
// — so `(x : bool) as u8` denotes EXACTLY the SAME `call_result` term the
// un-cast Bool would, and `wrap` simply never builds a separate Cast node.
// This is why the mission's option (a) ("thread a callees registry through
// the general recursive family") is not needed EITHER: the composition
// happens entirely in already-abstracted `Expr` space, not in a new
// `SemOperand`/`Rvalue` kernel constructor.
// ---------------------------------------------------------------------------
/// Trust: CALL-RESULT-AWARE COMPOSITION — the maximum `Cast`-hop depth
/// [`resolve_chain_operand`] may chase before reaching a call-destination LEAF
/// or declining. Mirrors [`CMP_INLINE_MAX_DEPTH`]'s cycle/stack-overflow
/// defense (a malformed/adversarial body could otherwise recurse
/// unboundedly); the real shape is depth 1 (one `Cast` hop), so this is
/// generous headroom while staying fail-closed on a pathological chain.
const CHAIN_OPERAND_MAX_DEPTH: usize = 8;

/// Trust: CALL-RESULT-AWARE COMPOSITION — a STRATIFIED, ADDITIVE operand-chain
/// resolution result: mirrors the codebase's existing precedent for a small
/// extension type layered ONTO an existing vocabulary rather than modifying it
/// (`Trust.TrustIr.XOperand`'s `Base(op)|Index(s,i)|Len(s)` stratification over
/// the plain `Operand` inductive — see `reports/branchy-multicall-spine-
/// scoping-2026-07-03.md`). Never itself a kernel type: [`resolve_chain_
/// operand`] uses it PURELY to walk the Rust-side MIR and decide WHICH `wrap`
/// closure to build; every kernel `Expr` this section produces is built
/// directly by [`call_chain_pureop_instance_verdict`], reusing the EXISTING
/// `Expr`-level vocabulary (see the module doc above).
#[derive(Debug, Clone, PartialEq, Eq)]
enum ChainOperand {
    /// A flat, already-modeled operand — the base case, the EXISTING
    /// [`resolve_cast_source_operand`] leaf (param/const/field-read, or one
    /// level of `Use`-wrapped temp inlining). BYTE-IDENTICAL to what every
    /// other recognizer in this file already resolves.
    Base(SemOperand),
    /// The operand IS the call-destination local itself — the opaque result
    /// of a REGISTERED call.
    Call,
    /// A `Cast` over a nested chain operand, admitted ONLY as the BOOL-SOURCE
    /// IDENTITY case (the cast's DECLARED source type is `Ty::Bool`; the
    /// destination is `Ty::Int` of any width/signedness — a Rust `bool as
    /// $int` is ALWAYS exactly 0 or 1, so this is a genuine identity on the
    /// SAME 0/1-on-Int carrier MirSem's `bool_as_int` convention already
    /// establishes, never a new numeric claim). A genuine int-width
    /// truncating/widening cast over a call-chain operand is a NAMED
    /// RESIDUE, still fail-closed here (out of THIS increment's scope).
    BoolCast(Box<ChainOperand>),
}

impl ChainOperand {
    /// Whether this chain genuinely reaches the call leaf (as opposed to
    /// resolving entirely through the flat, non-call [`ChainOperand::Base`]
    /// fragment) — the gate [`resolve_chain_checked_mul_operand`] uses to
    /// decide which of a `CheckedBinaryOp`'s two operands is "the chain side"
    /// versus the flat multiplier constant.
    fn involves_call(&self) -> bool {
        match self {
            ChainOperand::Base(_) => false,
            ChainOperand::Call => true,
            ChainOperand::BoolCast(inner) => inner.involves_call(),
        }
    }
}

/// The recognized CALL-RESULT-AWARE COMPOSITION shape: `_0`'s sole write is a
/// pure bitwise op combining a FLAT "other" operand with the VALUE field of a
/// checked-arith Mul whose multiplicand is a call result, chased through a
/// bool-identity `Cast` (see the module doc's 4-hop diagram). Produced ONLY by
/// [`sem_call_chain_pureop_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallChainPureOp {
    /// The recognized call (resolved certified callee + modeled args).
    pub call: SemCallReturn,
    /// The inner checked-arith op applied to the (bool-identity-cast) call
    /// result and a constant multiplier (`Mul`, 32 in the real shape).
    pub inner_op: SemBinOp,
    /// The constant multiplier (32 in the real shape).
    pub inner_const: i128,
    /// Whether the call's (cast) result is the inner op's FIRST (`true`) or
    /// SECOND (`false`) operand.
    pub inner_call_is_lhs: bool,
    /// The outer pure op combining the inner checked-arith VALUE with the
    /// non-call "other" operand (`BitOr`/`BitXor` in the real shapes — the
    /// genuine-`Int` bitwise fragment, never the Bool-connective one).
    pub outer_op: SemBinOp,
    /// The non-call, flat operand (e.g. `self`'s own value).
    pub other: SemOperand,
    /// Whether the inner checked-arith VALUE is the outer op's FIRST (`true`)
    /// or SECOND (`false`) operand.
    pub outer_mul_is_lhs: bool,
}

/// Trust: call-spine increment — a CALL-RETURN adequacy certificate: the
/// kernel-checked PER-CALL INSTANCE of the PROVEN `callRefinesContract`
/// transport lemma at this call site's concrete `(callee-id, arg)` `Call.mk`
/// value (see [`call_return_adequacy_witness`]). The call's return DENOTATION is
/// the opaque `call_result` recursor projection — the value the SEPARATELY-
/// VERIFIED callee returns (modular verification); the instance transports any
/// callee contract of that value to the call site, resting on ⊆ the 3
/// foundational axioms. NO new axiom, NO new inductive: the increment wires the
/// existing proven machinery into the return-witness composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallReturnAdequacyCertificate {
    /// The recognized call-return shape (resolved certified callee + modeled args).
    pub call: SemCallReturn,
    /// The kernel verdict for the per-call `callRefinesContract` instance.
    pub verdict: RefinementVerdict,
}

impl CallReturnAdequacyCertificate {
    /// Whether the per-call instance kernel-checked modulo exactly 3.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

impl FunctionAdequacyCertificate {
    /// Whether EVERY piece (operands, rvalues, return) is a modulo-3 proof. A
    /// composed certificate that exists is modulo-3 by construction (the witness
    /// builder is fail-closed), but this re-checks the invariant defensively.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        self.ret.is_modulo_3()
            && self.operands.iter().all(AdequacyCertificate::is_modulo_3)
            && self.rvalues.iter().all(RvalueAdequacyCertificate::is_modulo_3)
    }
}

/// The final reachable write that defines `_0` on a validated straight-line
/// return spine. Statements execute before their block terminator, so walking
/// the spine in order also handles nested contract wrappers and an explicit
/// assignment after a wrapper without selecting a stale earlier value.
pub(crate) enum StraightLineReturnDefinition<'a> {
    Assignment { rvalue: &'a trust_types::Rvalue, block: trust_types::BlockId, statement: usize },
    ContractWrapper { value: &'a trust_types::Operand, block: trust_types::BlockId },
}

// ---------------------------------------------------------------------------
// Trust: ADT-return leaf (gap-queue #2, 2026-07-07) — the Result/Option-ADT
// AGGREGATE RETURN shape: a 2-arm guarded return whose arms each CONSTRUCT an
// enum variant (`Rvalue::Aggregate(AggregateKind::Adt{name,variant,..}, ops)`)
// into `_0` and return it — `if guard { Ok(x) } else { Err(e) }`. This is the
// CONSTRUCTION dual of the discriminant-guard CONSUMPTION shape: that shape
// reads an enum's tag (`Rvalue::Discriminant`); this one WRITES it (a
// `SetDiscriminant`-carrying `Aggregate` rvalue). The two compose: a caller
// that discriminant-matches on a callee's ADT-constructed return sees the
// SAME tag convention on both ends.
// ---------------------------------------------------------------------------
/// A single arm's CONSTRUCTED variant: the declared discriminant selected by the
/// `Aggregate`'s `variant` INDEX plus its (at most one) payload field's resolved
/// value.  rustc MIR stores declaration-order indices in
/// `AggregateKind::Adt::variant`, not discriminant tags.  The recognizers therefore
/// cross-check the aggregate's enum name against the destination's first-class
/// [`trust_types::VariantDef`] metadata and map the index through that metadata.
/// Missing/legacy metadata, a wrong enum name, or an out-of-range index declines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtArm {
    /// The constructed variant's declared discriminant, obtained by indexing the
    /// destination enum's [`trust_types::VariantDef`] list with the aggregate's
    /// declaration-order variant index.
    pub variant: i128,
    /// The variant's single payload field, if it carries one (`Ok(x)`/`Err(e)`).
    /// `None` for a nullary arm (a fieldless variant, e.g. a hypothetical
    /// `None`-shaped arm — supported for generality though the initial target
    /// family always populates this).
    pub payload: Option<SemAdtPayload>,
}

/// A resolved ADT payload value — either a plain scalar (Int-carrying) field, or a
/// NESTED nullary-variant construction (the `Error::Underflow`-class shape: a
/// same-block temp assigned via ANOTHER zero-operand `Aggregate`, e.g. the payload
/// of `Err(Error::Underflow)`).  The nested `enum_name` is cross-checked against
/// the payload local's declared type and its `variant` index is mapped through that
/// type's first-class variant metadata with the SAME no-guessing discipline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemAdtPayload {
    /// A scalar field value — a resolved MirSem operand (a parameter, a constant,
    /// or a single-assigned temp's resolved source.  Casts are deliberately NOT
    /// erased into this variant: only an actual `Use` rvalue may produce it.
    Scalar(SemOperand),
    /// An exact Rust integer-cast payload.  `source` is the value read by the MIR
    /// `Cast`, while `width`/`signed` are copied from its destination type.  The
    /// ADT refinement witness interprets this as modular truncation followed by
    /// signed observation when required, rather than assuming that an arbitrary
    /// guarded cast is the identity.  This distinction is load-bearing for
    /// narrowing and same-width sign-changing fallible-cast implementations.
    IntCast { source: SemOperand, width: u32, signed: bool },
    /// A NESTED fieldless-variant construction (`Error::Underflow`-class).
    NullaryNested {
        /// The nested enum's `Ty::Adt` name (e.g. `"Error"`).
        enum_name: String,
        /// The nested constructor's discriminant.
        variant: i128,
    },
    /// Trust: RECORD-WITNESS inc-2 (ok/err DOWNCAST-FIELD payload, 2026-07-22) — a
    /// payload read from a DOWNCAST + FIELD projection off the dispatched SELF enum:
    /// `Use(Move((_self as v#N).f))` (the `Result::ok`/`Result::err` `Some(x)` payload).
    /// Denotes at the `idxElem` VALUE tier via a VARIANT-DISJOINT FLATTENED field key —
    /// the position of `__v{N}_{field}` in the SELF `Ty::Adt`'s flattened `fields` list
    /// (`Result`: `__v0_0` ↦ 1, `__v1_0` ↦ 2), NEVER the WITHIN-VARIANT index `f`. With
    /// within-variant keys `⟦(_self as v#0).0⟧` and `⟦(_self as v#1).0⟧` would BOTH be
    /// `idxElem(self, 0)` — def-eq — and a forged wrong-variant `Some` claim would
    /// kernel-ACCEPT; the flattened key makes them DISTINCT opaque `Int`s so the forgery
    /// is kernel-REJECTED (DOWNCAST-KEY-DISJOINTNESS). The `downcast_variant` is pinned
    /// EQUAL to the variant the dispatch arm established for this path in the recognizer
    /// ([`arm_adt_ctor_value_for`]'s TAG↔DOWNCAST provenance link). VALUE-TIER: SOME `Int`
    /// stably determined by (self, key); NO address/aliasing/validity content. The
    /// theorem builder is UNCHANGED — this denotes through the EXISTING
    /// `sem_operand_to_expr` `Field`-as-`idxElem` path (denotation extension, not a recipe
    /// change).
    DowncastField {
        /// The 0-based parameter index of the downcast base (the dispatched `self`).
        base_param: u64,
        /// The VARIANT-DISJOINT flattened field key (the position of
        /// `__v{downcast_variant}_{field}` in the self `Ty::Adt.fields`). Always ≥ 1
        /// (index 0 is the `__tag` slot), so it is disjoint from the reserved negative
        /// `idxElem` keys (`Discriminant` = -1, cast keys ≤ -2).
        flat_key: u64,
        /// The downcast variant INDEX (`Downcast(v)`), retained for auditability; the
        /// recognizer has already pinned `variants[v].discriminant` equal to the dispatch
        /// tag routing to this arm.
        downcast_variant: usize,
    },
}

/// A recognized Result/Option-ADT AGGREGATE RETURN: a 2-arm guarded return whose
/// arms each construct a DIFFERENT variant of the SAME outer enum. Mirrors
/// [`SemCfReturn`] exactly at the guard layer (same `cond`/arm extraction); diverges
/// only in the ARM VALUE, which is a [`SemAdtArm`] (a constructed variant) instead of
/// a scalar [`SemRvalue`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtReturn {
    /// The guard condition tree — BYTE-IDENTICAL extraction to [`SemCfReturn::cond`].
    pub cond: SemCondTree,
    /// The THEN arm's constructed variant.
    pub then_arm: SemAdtArm,
    /// The ELSE arm's constructed variant.
    pub else_arm: SemAdtArm,
    /// The outer enum's `Ty::Adt` name (e.g. `"core::result::Result"`).
    pub enum_name: String,
}

/// Trust: W-PRIMED increment 1 (2026-07-22) — GATE-ITER-REGION-NO-CROSS-INSTANTIATION
/// documented lift #1 — the recognized POST-STATE STEP witness for the pinned
/// `<core::slice::iter::Iter as Iterator>::next` dump. A NEW sibling to [`SemAdtReturn`]
/// (SemAdtReturn is NOT extended, [`CalleeFact`] is NOT touched — increment 1 is
/// CALL-SITE-INERT): it licenses the T-STEP certificate quadruple (T-VAL2/T-NONE2/
/// T-POST-SOME/T-POST-NONE, `trustir_adt::check_iter_step_refinement`) over the two-key
/// (generation-re-keyed) primed surface `iter_seq`/`iter_len`/`iter_has_next2`. Minted ONLY
/// by [`crate::clean_ground::sem_iter_step_shape_of`], which REUSES the existing D3 step
/// recognizer VERBATIM (no recognizer logic weakened/forked) plus two adversarial mint
/// fences (GATE-STEP-TERMINATOR-WRITE-COMPLETENESS: decline any live `Drop`/`Opaque`
/// write channel + any bare receiver capture; GATE-INC1-CLAIM-EXACTNESS NOUNWIND: every
/// live `Assert`/`Drop` must be nounwind) and the explicit `&[` / non-`str` element decline.
///
/// TRUST: GATE-ITER-GEN-KEY-DISCIPLINE (gate-1 transplant) — THE CONSUMPTION SEAM. This
/// witness is CALL-SITE-INERT: NOTHING consumes a `SemIterStep` into a caller frame, NO
/// instantiation chokepoint learns `iter_seq`/`iter_len`/`iter_has_next2`, and `CalleeFact`
/// stays requires-only so the tripwire (this file, the FENCE-COMPLIANCE-BY-CONSTRUCTION
/// block at ~33948) does NOT fire.
///
/// Trust: HONEST FLOOR inc-2 (2026-07-23) — THE F12 STRUCTURAL REFUSAL (durable record).
/// The "kernel-composed count conditional" that would consume this T-STEP surface into an
/// env-level whole-trace count theorem was adversarially REFUSED (all four skeptics
/// NEEDS-GATE) and is NOT built here. It is not merely unbuilt — it is STRUCTURALLY
/// IMPOSSIBLE under the F12 grounder fence (`clean_ground.rs`, the fail-closed pin
/// `iter_handle_preds_are_fail_closed_in_mirsem_grounder`, ~18554): the ghost `exec_loop`
/// ([`exec_loop`](MIRSEM_EXEC_LOOP), mirsem.rs:23918) IS the GROUNDED loop semantics over the
/// Int ghost slots `i_ghost`/`n_ghost`, so the two-key symbols (`iter_seq`/`iter_len`/
/// `iter_has_next2`) — which the fence bars from the MIR grounder — can NEVER share an
/// `exec_loop` term with the ghost counter. The count tie
/// `n_ghost = iter_len(recv) = sliceLen(s)` is the D-INIT residue: it has NO bridge law
/// permitted (`trustir_anchor.rs`:588/595) and can NEVER be a kernel equation, so a mis-bound
/// `n_ghost` would kernel-check a FALSE count. Therefore P-ITER-COUNT is NOT
/// kernel-composable in this architecture — the whole-trace count remains a RECOGNIZER-TRUST
/// premise (tie = D-INIT, direction = D-ORIENT, `trustir_anchor.rs`:606-608) PERMANENTLY
/// unless F12 is lifted (which would re-open the MIR-driven cross-instantiation F12 protects
/// against). Any future increment that re-attempts the composition MUST confront F12 first;
/// do not delete this record.
///
/// GATE-ITER-GEN-KEY-DISCIPLINE is now LANDED as EXECUTABLE, fail-closed defense-in-depth
/// (HONEST FLOOR inc-2): [`admit_t_step_instantiation`] enforces clause (ii) (the generation
/// key structurally bound to the ghost counter, the mandatory exactly-+1 advance, and the
/// RECV-BINDING PIN) and consults the one-arg decline half, while
/// [`sem_loop_function_carries_entry_iter_handle`] is the wired clause-(i) decline (the
/// `SemLoopFunction` sibling of `clean_ground::sem_adt_return_carries_entry_iter_handle`),
/// called fail-closed at the re-anchored chokepoints. HONEST SCOPE: because T-STEP has ZERO
/// live consumers (the whole two-key surface is `#[cfg(test)]`-only, per the standing F12
/// refusal above), the detector's LIVE effect today is NIL — it is REGRESSION-PROTECTION that
/// code-enforces call-site inertness, exactly as `sem_adt_return_carries_entry_iter_handle` is
/// "vacuously false in the live lane." It closes NO active hole.
///   (a) ENUMERATED, RE-ANCHORED chokepoint list: `loop_instance_env` mirsem.rs:30005 (the
///       env build — the blanket env-level guard is documented there; no per-fn loop flows
///       through it), `loop_refinement_witness` mirsem.rs:30135 (WIRED: declines any projected
///       loop that carries the two-key handle), `iter_loop_partial_witness` mirsem.rs:34317
///       (WIRED on `ilf.projected`), the composed-chain builder (REFUSED — see the F12 record
///       above), and any env-level theorem-instantiation surface. The detector both DECLINES
///       one-arg SemAdtReturn carriers (via the wired decline half) and ADMITS a T-STEP
///       instantiation ONLY when its generation key is structurally bound to the ghost counter
///       with the mandatory +1 advance across every admitted receiver mutation —
///       `sem_adt_return_carries_entry_iter_handle` alone CANNOT express this (wrong type, no
///       two-key arms);
///   (b) forgery probe F-SAMEGEN: two chained `next()` both instantiated at g=0 are
///       chokepoint-DECLINED (a literal generation key is not the ghost counter — F-NEGGEN's
///       0≤g does not cover it);
///   (c) the F-CHAIN-INERT successor: a straight-line two-chained-next() caller with no
///       ghost-counter loop DECLINES (an unbound generation key);
///   (d) F-BRIDGE: any consumption referencing the one-arg `iter_region`/`iter_has_next`
///       family DECLINES via the wired decline half (the recognizer refuses it; `check_type`
///       can never refuse the rfl-provable elem0=elem1);
///   (e) the FENCE-COMPLIANCE-BY-CONSTRUCTION block (mirsem.rs:33948) carries the SAME F12
///       record; its ghost-vars-only premise stays TRUE precisely because the composition that
///       would falsify it is refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemIterStep {
    /// The MIR LOCAL INDEX of the `&mut core::slice::iter::Iter` receiver whose Int carrier
    /// the two-key surface keys on (for `next(&mut self)` this is local 1). The theorem
    /// quantifies `recv` abstractly; this is the recognized param the mint gate pinned — a
    /// recognizer IDENTITY only, NOT a shape-bearing carrier routed anywhere (the CalleeFact
    /// tripwire is not tripped). Increment 2 re-derives / binds it to the ghost counter.
    pub recv_param: u64,
    /// The stride pointee element type of the one-stride cursor advance (from D3's
    /// [`crate::clean_ground::IterNextStepShape`]). Pins the `&[`/non-`str` element decline
    /// (F-STRTYPE — the D6 `&str`→u8 conflation may not reach the two-key claim). The theorem
    /// payload `iter_seq recv g` is Int-valued regardless; this field is a GATE only.
    pub element_ty: trust_types::Ty,
}

/// Trust: W19 mutators inc-1 (2026-07-24) — the recognized `&mut self` SINGLE-SCALAR-
/// FIELD SETTER witness for the `fn set_x(&mut self, v: T) { self.x = v; }` shape. A NEW
/// sibling to [`SemIterStep`] (NEITHER [`SemAdtReturn`] NOR [`CalleeFact`] is touched —
/// inc-1 is CALL-SITE-INERT): it licenses the T-SET / T-FRAME certificate pair
/// ([`crate::trustir_adt::check_field_set_refinement`]) over the field-setter post-state
/// surface `idx_elem_prime`/`set_key_eq`/`set_post`. Minted ONLY by
/// [`crate::clean_ground::sem_field_set_shape_of`] (G1–G9 + G-STRUCT-KIND), which has
/// ZERO production callers (exercised only by `#[cfg(test)]` probes) — the
/// `sem_iter_step_shape_of` posture verbatim.
///
/// INERT / NO-FLIP: this adds NO verdict, cluster, or funnel bit. A real `set_x` still
/// returns UNKNOWN in the live lane (`sem_field_read_operand` declines `&mut self`,
/// `deref_write_exists` fails closed on the write). The certificate proves modulo 3 that
/// IF a body is a recognized single-scalar-field setter THEN the post-state selector
/// equals `v` at the written field and is FRAMED (equals `idx_elem_prime recv k g`)
/// elsewhere — a lowered-shape equality, with the compiled-store-vs-model bridge resting
/// ENTIRELY on this recognizer's fail-closed structural attestation (the SOLE
/// faithfulness bearer of this thin tier), NOT on the kernel.
///
/// Trust: THE F12 STRUCTURAL REFUSAL (durable record — the twin of the record on
/// [`SemIterStep`]). Option (ii) — a caller-visible READ-AFTER-SET that redirects a
/// downstream `(*self).x` read to the post-value — requires `idx_elem_prime`/`set_post`
/// INSIDE the MIR grounder field-read lane, the EXACT cross-instantiation the F12
/// grounder fence bars (`clean_ground.rs`, the fail-closed pin
/// `field_post_preds_are_fail_closed_in_mirsem_grounder`, mirroring
/// `iter_handle_preds_are_fail_closed_in_mirsem_grounder`). It is not merely unbuilt —
/// it is STRUCTURALLY IMPOSSIBLE under that fence: `ground_int` returns `None` on
/// `Pred(idx_elem_prime, ..)` / `Pred(set_post, ..)` / `Pred(set_key_eq, ..)`, so a
/// real field read can NEVER kernel-check a FALSE post-state. The setter analogue of the
/// permanently-refused P-ITER-COUNT inc-2 composition. Any future consumer (inc-1.5 RMW,
/// inc-2 multi-field/Vec, or the option-(ii) read-after-set) MUST confront F12 first; do
/// NOT wire `idx_elem_prime`/`set_post` into `ground_int`, and do NOT mint an
/// axiom-shaped bridge from the 3-arg `idx_elem_prime` to the LIVE 2-arg `idx_elem`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemFieldSet {
    /// The MIR LOCAL INDEX of the `&mut S` receiver whose Int carrier the surface keys
    /// on (for `set_x(&mut self, v)` this is local 1). The theorem quantifies `recv`
    /// abstractly; this is the recognized param the mint gate pinned (G2) — a recognizer
    /// IDENTITY only, routed nowhere shape-bearing (the CalleeFact tripwire is not
    /// tripped).
    pub recv_param: u64,
    /// The flattened `Field(n)` index of the SOLE written field (G1). Non-negative,
    /// disjoint from `idx_elem`'s reserved negative keys (Discriminant = -1, casts
    /// ≤ -2). The `<fld>` literal the per-certificate `set_post` / `set_key_eq` guard
    /// is parameterized by.
    pub field_key: u64,
    /// The MIR LOCAL INDEX of the entry-state value parameter written (G4/G9): the
    /// post-state at the written field equals THIS independent param, with NO dependence
    /// on the pre-state (a `self.x += 1` RMW post = f(pre) is deferred to inc-1.5 and
    /// declined by G4).
    pub value_param: u64,
    /// Every declared field index of `S` (G5): `0..S.fields.len()`. The minted frame is
    /// the TOTAL `∀k` conditional, so it structurally covers every `k ≠ fld`; this is
    /// pinned for auditability and for the inc-1.5/inc-2 consumers that must enumerate
    /// the other fields.
    pub all_field_keys: Vec<u64>,
    /// The declared scalar type of the written field (G8): `Int`/`Bool`, equal to
    /// `value_param`'s declared type. A non-scalar field (nested Adt/ptr/PhantomData)
    /// declines (needs RECORD-WITNESS/ptr machinery, out of scope). Int-valued theorem
    /// payload regardless; this field is a GATE only.
    pub field_ty: trust_types::Ty,
}

/// Trust: W19 mutators inc-1.5 (2026-07-24) — the arithmetic operation of a recognized
/// CHECKED read-modify-write field setter. Each maps to the prelude's axiom-free
/// reducible `Int.<op>` (see [`SemFieldRmw`]'s faithfulness record for why the guard is
/// what licenses the MATHEMATICAL reading).
///
/// THE REAL REASON FOR THIS FRAGMENT BOUNDARY (stated precisely, because an earlier
/// draft justified it with two claims that are false against Trust's own model):
/// Add/Sub/Mul are the ops rustc lowers to a `CheckedBinaryOp` VALUE/FLAG PAIR, so they
/// are the only ops for which a guarded `_t.0` is provably the mathematical result —
/// the flag is what the partial-correctness argument keys on. `Div`/`Rem`/`Shl`/`Shr`
/// DO carry `Overflow(op)`-class asserts, but they produce a bare `Rvalue::BinaryOp`
/// with NO flag to key that argument on; the bitwise ops are unguarded and would need a
/// bitvector faithfulness argument that does not exist in this tree. All of them
/// decline fail-closed at the mint gate — double-gated, by the `CheckedBinaryOp` match
/// and by this enum having no constructor for them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemRmwOp {
    /// `+=` — `CheckedBinaryOp(Add, ..)` + `Assert(Overflow(Add))` ⇒ `Int.add`.
    Add,
    /// `-=` — `CheckedBinaryOp(Sub, ..)` + `Assert(Overflow(Sub))` ⇒ `Int.sub`.
    Sub,
    /// `*=` — `CheckedBinaryOp(Mul, ..)` + `Assert(Overflow(Mul))` ⇒ `Int.mul`.
    Mul,
}

/// Trust: W19 mutators inc-1.5 (2026-07-24) — the RIGHT-HAND operand of a recognized
/// checked RMW. Both arms denote an ENTRY-STATE `Int`: a closed literal, or a
/// parameter routed through the [`sem_operand_of_mir`] PARAM-ROOT chokepoint (which
/// fail-closes on a reassigned parameter). A right-hand operand that reads the
/// RECEIVER (`self.y`), a temp, or any other rvalue shape DECLINES — the certificate
/// quantifies over exactly one abstract value binder, so a second pre-state read would
/// need a second generation-keyed term this increment does not mint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemRmwRhs {
    /// `self.x += 1` — a closed integer literal (the `bump` shape). The certificate's
    /// `v` binder is then VACUOUS (quantified but unused); the theorem is still
    /// non-trivial because its left summand is the pre-state selector.
    Const(i128),
    /// `self.written += amt` — the MIR LOCAL INDEX of an entry-state scalar parameter
    /// distinct from the receiver. Bound to the certificate's `v` binder.
    Param(u64),
}

/// Trust: W19 mutators inc-1.5 (2026-07-24) — the recognized `&mut self` CHECKED
/// READ-MODIFY-WRITE field setter witness for `fn bump(&mut self) { self.x += 1; }`.
/// The sibling of [`SemFieldSet`] whose written value DEPENDS ON THE PRE-STATE: it
/// licenses the T-SET / T-FRAME pair ([`crate::trustir_adt::check_field_rmw_refinement`])
/// over the per-certificate `rmw_post` selector, whose TRUE minor is
/// `Int.<op> (idx_elem_prime recv <fld> g) <rhs>` — i.e. the claimed post-value of the
/// written field is a FUNCTION OF THAT FIELD'S OWN PRE-VALUE rather than an independent
/// parameter, which is the entire delta from inc-1. (The W-PRIMED T-STEP quadruple
/// already relates a post-state to a pre-state at the GENERATION counter; this is the
/// first one to do so at a FIELD's content.) Minted ONLY by
/// [`crate::clean_ground::sem_field_rmw_shape_of`], which has ZERO production callers
/// (exercised only by `#[cfg(test)]` probes) — the [`SemFieldSet`] posture verbatim.
///
/// INERT / NO-FLIP: adds NO verdict, cluster, or funnel bit. A real `bump` still
/// returns UNKNOWN in the live lane. The certificate proves modulo 3 that IF a body is
/// a recognized checked RMW field setter THEN the post-state selector equals the
/// arithmetic term at the written field and is FRAMED elsewhere — a lowered-shape
/// equality, with the compiled-store-vs-model bridge resting ENTIRELY on this
/// recognizer's fail-closed structural attestation (the SOLE faithfulness bearer of
/// this thin tier), NOT on the kernel.
///
/// Trust: THE WRAP-vs-INT FAITHFULNESS RECORD (inc-1.5's load-bearing argument; the
/// reason this witness is scoped to the CHECKED lowering and no other).
/// `Int.add`/`sub`/`mul` are UNBOUNDED mathematical operations; a machine `i64` add is
/// not. The two agree exactly when the operation does not overflow — and NOTHING in
/// this lane proves that (`idx_elem_prime` is a totally unconstrained opaque, and there
/// is no wrap/`mod 2^W` value tier anywhere in trust-clean; see the ratified WRAP-TIER
/// deferral note in this file). What licenses the mathematical reading is the PROGRAM's
/// OWN runtime guard: the mint gate admits ONLY the
/// `_t := CheckedBinaryOp(op, (*recv).fld, rhs)` + `Assert{cond: _t.1, expected: false,
/// msg: Overflow(op)}` + `(*recv).fld := Use(_t.0)` spine, in which the write is
/// executed ONLY on the Assert's `target` successor — i.e. only on runs where the
/// overflow flag was FALSE, on which `_t.0` IS the mathematical result. So the claim is
/// a PARTIAL-CORRECTNESS one: *if the call returns normally, the post-state at the
/// written field is the mathematical term.* It is NOT a totality claim and does NOT
/// discharge the `VcKind::ArithmeticOverflow` obligation the same body raises — that
/// remains a SEPARATE, separately-discharged axis (the standing checked-arith
/// doctrine), and this inert surface cannot see its discharge.
///
/// WHERE THAT SIDE CONDITION LIVES (do not misread the certificate): the "returns
/// normally" / "the overflow flag was false" condition appears in **NO kernel
/// hypothesis**. T-SET's and T-FRAME's only hypothesis is `set_key_eq k <fld> = <pol>`;
/// the kernel term is UNCONDITIONAL, and it is a d/ι-unfolding of a `rmw_post`
/// definition this certificate itself mints. The side condition is discharged
/// ENTIRELY by this mint gate's structural admission of the Assert spine — i.e. at the
/// recognizer tier, not the kernel tier. Concretely: because
/// `trustir_adt::check_field_rmw_refinement`'s signature takes a `SemFieldRmw` value,
/// re-deriving the theorem from a HAND-BUILT one (as the probe suite does) carries no
/// overflow guarantee whatsoever — only a witness that came out of
/// `clean_ground::sem_field_rmw_shape_of` does. The minted theorem is named
/// `…field_rmw_normal_return_*` so the caveat travels with the kernel object.
/// CONSEQUENCE, ENFORCED AT THE MINT GATE: the UNCHECKED `Rvalue::BinaryOp(op, ..)`
/// store — the `-C overflow-checks=off` lowering, whose machine result WRAPS — must
/// NEVER mint here. Claiming `post = Int.add pre 1` for a wrapping add certifies a
/// FALSE value model. That refusal is pinned RED by TWO probes, which cover different
/// gates and are BOTH needed: `field_set_unchecked_wrapping_binaryop_still_declines`
/// (the realistic direct-store lowering — it declines at G-SPINE, since a `BinaryOp`
/// yields a scalar and so cannot form the two-block `.0`/`.1` spine at all) and
/// `field_rmw_unchecked_binaryop_in_spine_declines` (the same spine with an unchecked
/// rvalue in the arithmetic slot — this one reaches G-OVFL itself).
///
/// Trust: THE ENCODER-FIDELITY COROLLARY (found by adversarial review, 2026-07-24) —
/// AND ITS SEQUEL THE SAME DAY. The mathematical reading is only as faithful as the
/// ENCODING of the operands. `trustir_anchor::int_lit` rendered an `i128` as
/// `Expr::nat_lit(n as u64)` — a SILENT TRUNCATION at |n| ≥ 2^64 — so a 128-bit field's
/// in-range literal could encode to a value 2^64 away from the one the body adds,
/// minting a FALSE value model ON THE NON-OVERFLOWING PATH. The mint gate therefore
/// carries G-WIDTH (field width ≤ 64) and G-LITRANGE (the literal is representable in
/// the field's declared type), pinned by `field_rmw_128_bit_field_declines`,
/// `field_rmw_out_of_range_literal_declines`, and the positive boundary
/// `field_rmw_u64_max_literal_mints_and_proves_modulo3`.
///
/// SEQUEL — READ BEFORE RE-JUSTIFYING G-WIDTH. Generalizing this exact concern one lane
/// over found a LIVE FALSE ACCEPT in the grounder (a false `ensures` reached the PROVEN
/// list), and the fix made ALL FIVE pinned literal encoders EXACT over the full `i128`
/// range via `Expr::nat_lit_u128`. So the truncation that ORIGINALLY motivated G-WIDTH
/// no longer exists. G-WIDTH is RETAINED, but its honest justification is now
/// CONSERVATIVE SCOPE, not encoder fidelity: this witness's arithmetic argument has only
/// ever been exercised at widths ≤ 64, and a narrower admission set is the standing
/// discipline. Widening it to 128-bit fields is now a scope decision with no encoder
/// blocker — it needs its own faithfulness battery, not a bug fix. G-LITRANGE keeps its
/// ORIGINAL, encoder-independent justification: a literal outside the field's declared
/// type is not that operand's value in any well-formed lowering.
///
/// Trust: THE F12 STRUCTURAL REFUSAL (durable record — the twin of the records on
/// [`SemFieldSet`] / [`SemIterStep`]). A caller-visible READ-AFTER-SET that redirects a
/// downstream `(*self).x` read to the post-value requires `idx_elem_prime`/`rmw_post`
/// INSIDE the MIR grounder field-read lane, the EXACT cross-instantiation the F12
/// grounder fence bars (`clean_ground.rs`, the fail-closed pin
/// `field_post_preds_are_fail_closed_in_mirsem_grounder`, which this increment EXTENDS
/// with `rmw_post`). `ground_int` returns `None` on every one of those Preds, so a real
/// field read can NEVER kernel-check a FALSE post-state. Note the specific temptation
/// this increment creates and refuses: the RMW's pre-state read `(*self).x` IS a real
/// field read, so it is the natural place to smuggle in a bridge from the 3-arg
/// `idx_elem_prime` to the LIVE 2-arg `idx_elem`. It is mapped DIRECTLY to
/// `idx_elem_prime recv <fld> g` at the SAME generation key as the frame, and no such
/// bridge is minted (pinned by `trustir_adt::tests::field_rmw_no_bridge_to_live_idx_elem`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemFieldRmw {
    /// The MIR LOCAL INDEX of the `&mut S` receiver (G2). Recognizer IDENTITY only.
    pub recv_param: u64,
    /// The flattened `Field(n)` index BOTH read and written (G-PRE-READ requires the
    /// read and the write hit the SAME field — a cross-field `self.x = self.y + 1` is
    /// sound under the same machinery but is a deliberately deferred widening).
    /// Non-negative, disjoint from `idx_elem`'s reserved negative keys.
    pub field_key: u64,
    /// The recognized checked arithmetic operation (G-OVFL).
    pub op: SemRmwOp,
    /// The recognized right-hand operand (G-RHS).
    pub rhs: SemRmwRhs,
    /// Every declared field index of `S` (G5) — the minted frame is the TOTAL `∀k`
    /// conditional, so it structurally covers every `k ≠ fld`.
    pub all_field_keys: Vec<u64>,
    /// The declared scalar type of the read/written field (G8): `Int` only (a `Bool`
    /// field has no arithmetic RMW lowering).
    pub field_ty: trust_types::Ty,
}

// ===========================================================================
// Trust: HONEST FLOOR inc-2 (2026-07-23) — GATE-ITER-GEN-KEY-DISCIPLINE, LANDED as an
// EXECUTABLE, fail-closed T-STEP admission detector (defense-in-depth). See the doc on
// `SemIterStep` for the full discipline text + the F12 structural-refusal record.
//
// HONEST SCOPE (do NOT overstate): the two-key T-STEP surface has ZERO live consumers — the
// whole `iter_seq`/`iter_len`/`iter_has_next2` family is `#[cfg(test)]`-only and the
// kernel-composition that would consume it is REFUSED (structurally impossible under the F12
// grounder fence). So this detector's LIVE effect TODAY is NIL. It exists to CODE-ENFORCE
// call-site inertness so that IF a future increment ever wires a T-STEP consumer, it declines
// unless the generation key is structurally bound to the ghost counter — regression
// protection, exactly like `clean_ground::sem_adt_return_carries_entry_iter_handle` is
// "vacuously false in the live lane." It closes no active hole and flips no verdict/cluster/
// funnel bit.
// ===========================================================================
/// The generation key a candidate consumer would bind a T-STEP theorem's abstract `g : Int`
/// to at a call position. The T-STEP quadruple quantifies `g` abstractly (plain-Pi,
/// `trustir_adt::IterStepThm`); GATE-ITER-GEN-KEY-DISCIPLINE requires the consumer bind it to
/// the ghost counter `i_ghost` — a LITERAL (F-SAMEGEN) or an unbound key (F-CHAIN-INERT)
/// declines fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TStepGenKey {
    /// `g := Var(i_ghost)` — structurally bound to the ghost counter env slot `i_ghost`.
    GhostCounter(u64),
    /// `g := Const(k)` — a LITERAL generation (the F-SAMEGEN forgery: two chained `next()`
    /// both instantiated at `g = 0` reuse a generation, breaking the `g = i` binding).
    Literal(i128),
    /// `g` bound to a non-ghost MIR local / free var with NO ghost-counter loop behind it
    /// (the F-CHAIN-INERT successor: a straight-line two-chained-next() caller).
    Unbound,
}

/// A candidate consumption of a `SemIterStep` T-STEP theorem into a caller frame, exactly as
/// a certificate-instantiation chokepoint would present it. Every field is a recognizer-trust
/// binding the chokepoint would have to establish BEFORE the kernel checks the composition
/// UNDER it — the kernel proves only a fully generic `loopInvariantRule` and never DERIVES the
/// `g = i` / recv / `n = iter_len` bindings (see the F12 record on `SemIterStep`), so this
/// detector is the sole barrier against instantiating T-STEP without them.
#[derive(Debug, Clone)]
pub struct TStepInstantiation {
    /// The recognized receiver-param IDENTITY the T-STEP mint pinned ([`SemIterStep::recv_param`]).
    pub step_recv_param: u64,
    /// The generation key the consumer proposes to bind the theorem's abstract `g` to.
    pub gen_key: TStepGenKey,
    /// The ghost-counter env slot `i_ghost` at this call position (from the projected loop).
    pub ghost_counter: u64,
    /// The receiver-mutation advance the consumer claims across this admitted step. MUST be
    /// exactly `+1` (T-POST-SOME: `post2 recv g = Int.add g 1`); a double-advance (two
    /// `next()` per one `i`-increment) or a step `!= +1` declines.
    pub advance: i128,
    /// RECV-BINDING PIN input: the sole `into_iter(Copy s)` result MIR local (G3).
    pub into_iter_result_local: u64,
    /// RECV-BINDING PIN input: the G1/G2 def-path header `next()`-receiver MIR local.
    pub header_receiver_local: u64,
    /// The one-arg decline half, wired: `= clean_ground::sem_adt_return_carries_entry_iter_
    /// handle(companion)` for any companion value-lane `SemAdtReturn` the consumer also
    /// presents. `true` ⇒ the consumption references the one-arg entry-time iterator handle
    /// (`IterHasNext`/`IterRegion`) family — non-composable by mechanism (F-BRIDGE) ⇒ DECLINE.
    pub companion_carries_entry_iter_handle: bool,
}

/// The chokepoint verdict for a candidate T-STEP instantiation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TStepAdmission {
    /// The candidate binds `g := i_ghost`, advances by exactly `+1`, its recv is the sole
    /// `into_iter`/header-`next()` receiver local, and it carries no one-arg entry-iter
    /// handle — ADMIT. (Still verdict-neutral: there is no live consumer to admit today.)
    Admit,
    /// Fail-closed DECLINE with a reason (F-SAMEGEN / F-CHAIN-INERT / DOUBLE-ADVANCE /
    /// MALFORMED-BINDING / RECV-BINDING / F-BRIDGE).
    Decline(String),
}

/// Trust: RECORD-WITNESS inc-2 (ok/err drop-ladder epilogue, 2026-07-22) — a recognized
/// VALUE-TRANSPARENT conditional-drop ladder tail. `Result::ok`/`Result::err` bodies
/// converge (both arms `Goto`) at a SECOND `SwitchInt(Discriminant(self))` that routes
/// ONLY to `Return` / `Drop(self) → Return` / `Unreachable` blocks — a pure post-`Option`
/// aggregate drop epilogue — instead of directly at the `Return` block. This carries the
/// two facts the recognizer needs to admit the shape fail-closed: the ladder's own
/// `SwitchInt` block (EXCLUDED from the guard analysis) and the self local it re-reads
/// (cross-checked EQUAL to the dispatch self local — gate B(i)).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DropLadderEpilogue {
    /// The ladder head block (the arms' common `Goto` target): reads
    /// `_t = Discriminant(self)` then `SwitchInt`es to `Return` / `Drop(self)` blocks.
    switch_block: trust_types::BlockId,
    /// The self local whose discriminant the ladder re-reads AND whose value the ladder's
    /// `Drop` place is. Cross-checked EQUAL to the dispatch self local by the caller.
    self_local: usize,
}

/// Trust: RECORD-WITNESS (single-variant struct-constructor, increment 1, 2026-07-22)
/// — one field's value in a recognized straight-line struct-CONSTRUCTOR return. A
/// [`Scalar`](Self::Scalar) field denotes through the witness's `sem_operand_to_expr`
/// (the entry-time env-application `Int`/`Bool` tier); a [`Unit`](Self::Unit) MARKER
/// field (`PhantomData`, reflecting to kernel `Unit`) is the
/// closed `Unit.unit` constructor argument, accepted BY the field's TYPE — never from
/// a scalar operand. The two are disjoint: a scalar operand in a Unit slot (or a
/// `Unit` constant in a scalar slot) declines the recognizer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemStructField {
    /// A scalar field value — a resolved entry-time [`SemOperand`] (a parameter, a
    /// constant, or a transparent move / deref-of-scalar-ref). Routed through the
    /// [`sem_operand_of_mir`] PARAM-ROOT chokepoint so a reassigned parameter root
    /// (or a non-`Int`/`Bool` place) fails closed BEFORE it can denote an entry `Var`.
    Scalar(SemOperand),
    /// A `Unit`/`PhantomData` MARKER field — the closed `Unit.unit` constructor
    /// argument. Accepted only when the DECLARED field type is a Unit-carrier
    /// (`Ty::Unit` or the exact canonical `PhantomData` ADT) AND the MIR
    /// operand is a `ConstValue::Unit`. Kept in the `.mk` arity so MIR field order
    /// lines up with the constructor's positions.
    Unit,
    /// Trust: RECORD-WITNESS increment 3 (2026-07-22) — GATE-PTR-SLOT-OPACITY(a) —
    /// a SLICE-START pointer field (`slice::Iter::ptr` — the `NonNull<T>` cursor set at
    /// construction to `&raw const (*s)`, chased via [`crate::clean_ground`]'s
    /// `live_slice_addr_of_root` to the slice PARAMETER `s`). Denotes
    /// `sliceStart ⟦root⟧` — a FRESH opaque handle-constructor APPLICATION on the root
    /// env read (NEVER the bare `e p` slot itself: bare-slot would claim
    /// `sliceLen(ptr-slot) = Len(s)`, refutable by two subslices with identical runtime
    /// ptr but distinct lengths). VALUE-TIER: SOME Int stably determined by the operand,
    /// NO address/aliasing/validity content; NEVER jointly consumed with the raw-CFG
    /// PtrModel offset discharge as an address-tier one-past-the-end claim
    /// (GATE-PTR-SLOT-OPACITY(c) — enforced by recognizer + probe, not by this type).
    SliceStart(SemOperand),
    /// Trust: RECORD-WITNESS increment 3 (2026-07-22) — GATE-PTR-SLOT-OPACITY(a)+(b) —
    /// a ONE-PAST-THE-END pointer field (`slice::Iter::end_or_len` on the non-ZST lane —
    /// `Rvalue::PtrOffset { ptr: <slice start>, count: <slice length> }`). Denotes
    /// `ptrOffset (sliceStart ⟦base⟧) ⟦count⟧ (lit elem_size)`, where `base` roots at the
    /// offset base pointer's slice parameter, `count` is the [`SemOperand::Len`]
    /// (`⟦count⟧ = sliceLen ⟦q⟧`) of the metadata's slice parameter, and `elem_size` is
    /// the BYTE size of the offset base pointer's POINTEE sort, pinned from the MIR
    /// pointer type. The pointee-indexed `elem_size` argument makes a pointee-recast that
    /// changes element size (`*const u8 → *const u64`) denote DISTINCTLY — `is_pointerish`'s
    /// pointee-blind cast passthrough is INADMISSIBLE at this value tier. Same value-tier /
    /// no-joint-promotion discipline as [`SliceStart`](Self::SliceStart).
    EndOffset {
        /// The offset base pointer's resolved slice-start root operand (denoted under
        /// `sliceStart`).
        base: SemOperand,
        /// The offset element COUNT operand — a [`SemOperand::Len`] of the metadata's
        /// slice parameter, denoting `sliceLen ⟦q⟧`.
        count: SemOperand,
        /// The BYTE size of the offset base pointer's POINTEE sort (pinned from the MIR
        /// pointer type; the pointee sort is cross-checked to equal the count slice's
        /// element sort, so the offset units and the length units agree).
        elem_size: u64,
    },
}

/// Trust: RECORD-WITNESS (single-variant struct-constructor, increment 1, 2026-07-22)
/// — a recognized straight-line struct-CONSTRUCTOR return: a body whose SOLE `_0`
/// write is `_0 = Aggregate(AggregateKind::Adt { <struct>, variant 0, active_field:
/// None }, [op_0 .. op_n])` immediately followed by `Return`, over a CONCRETE
/// non-generic struct (`Ty::Adt` with `variants: []`) carrying FRESH first-class field
/// metadata (legacy `__tag`/`__v`-flattened dumps decline). The `expr::types::
/// BinderData::new`-class shape (`fn new(a, b) -> S { S { a, b } }`).
///
/// The kernel witness ([`crate::trustir_adt::check_struct_return_refinement`]) is
/// GUARD-FREE MODEL-ONLY: `∀ (e:Env), S.mk ⟦op_0⟧e … ⟦op_n⟧e = <that same ctor app>`,
/// proved by `Eq.refl`. With no guard hypothesis the theorem is definitional, so
/// 100% of the soundness burden sits on THIS recognizer's gates (sole-writer,
/// spine-statement whitelist, PARAM-ROOT admission, `active_field == None`, carrier
/// re-get admission + arity, concrete-only, fresh-metadata); the claimed-override
/// probe keeps the recipe provably non-tautological.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemStructReturn {
    /// The CONCRETE struct return type (`Ty::Adt` with `variants: []`), carried
    /// verbatim so the kernel witness reflects the SAME single-`.mk` carrier this
    /// recognizer cross-checked — field order + Unit marker fields included.
    pub struct_ty: trust_types::Ty,
    /// Per-field values in MIR / constructor order (incl. Unit markers).
    /// `fields.len()` equals the Aggregate operand count AND the `.mk` arity.
    pub fields: Vec<SemStructField>,
}

// ---------------------------------------------------------------------------
// Trust: W20 REFERENCE-RETURN (value-tier reference denotation, 2026-07-21) — the
// slice-element-reference return lane (`Some(&s[i])`): `core::slice::first` and
// `SliceIndex::get`. An immutable `&s[i]` RETURN denotes its referent's ELEMENT VALUE
// at the idx_elem tier (`idxElem(s, i)`) deref-transparently — a VALUE claim, never an
// address/aliasing claim. The recognition + gate machinery is shared between the value
// constructor (`arm_adt_ctor_value_for`'s Ref arm) and the guard↔projection coherence
// gate (`sem_adt_return_shape_of` step 5.5).
// ---------------------------------------------------------------------------
/// The recognized slice-element projection behind an immutable `&s[i]` reference
/// return, with the base slice PARAMETER's de-Bruijn index.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SliceRefProj {
    /// The base slice parameter's 0-based binding index (`SemOperand::Var(base_param)`).
    base_param: u64,
    kind: SliceRefProjKind,
}

/// The slice-element projection shape: a dynamic `s[k]` index or a constant
/// (possibly from-end) `ConstantIndex`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum SliceRefProjKind {
    /// `s[k]` — the resolved dynamic index operand (`SliceIndex::get`).
    Index(SemOperand),
    /// `s[offset]` (`from_end:false`, index `offset`) or `s[len-offset]`
    /// (`from_end:true`, index `sliceLen(s) - offset` — `slice::last`).
    ConstantIndex { offset: usize, min_length: usize, from_end: bool },
}

impl SliceRefProjKind {
    /// The denoted element-INDEX operand, or `None` (fail-closed) when it is not
    /// expressible in the current `SemOperand` fragment. `from_end:true`
    /// (`slice::last`) denotes `sliceLen(s) - offset`, which no current operand composes
    /// (no Sub / Len-minus-const carrier) — so it declines here.
    fn index_operand(&self) -> Option<SemOperand> {
        match self {
            SliceRefProjKind::Index(op) => Some(op.clone()),
            SliceRefProjKind::ConstantIndex { offset, from_end: false, .. } => {
                Some(SemOperand::Const(i128::try_from(*offset).ok()?))
            }
            SliceRefProjKind::ConstantIndex { from_end: true, .. } => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Trust: OPAQUE-CHAIN ADT-RETURN (M6 Tier-1 SHAPE_GAP, 2026-07-10) — the
// guarded `Option` return whose arm payload is produced by a LINEAR CHAIN of
// opaque steps (calls whose results are ∀-BOUND in the kernel witness, never
// interpreted): the `clean-kernel` `expr/subst.rs` `fold_fvar_opt`/
// `fold_bvar_opt` leaf family.
//
//   fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
//       if id == self.id { Some(ek(ExprKind::BVar(self.depth))) } else { None }
//   }
//
// HONESTY TIER (read before extending): every call result in this shape is an
// ∀-BOUND instance variable in the kernel statement — the SAME "an arbitrary
// Int standing in for whatever value this operand denotes; never a fresh
// axiom" framing `trustir_call::TrustIrOtherOperand::Param` and the
// `callReturnInstance`'s own `∀ (ret : Int)` binder already use. The witness
// therefore claims the GUARD→VARIANT dispatch exactly ("when the guard holds,
// the function returns `Some(<the chain's product>)`; the payload value itself
// is quantified, not asserted") — it does NOT claim the callee's value content
// (that would require the certified-callee registry, which these leaf callees
// — `expr::kind::ek`, `Clone::clone`, `expr::checked_add_u32` — cannot enter
// today). The guard is either a REAL entry-time comparison (denoted exactly)
// or the result of a `__trust_total_clone`-sentinel derived-`PartialEq` call
// (∀-bound `Bool` — the extraction-side `is_total_derived_trait_call` proof is
// what justifies admitting a CALL in guard position at all).
// ---------------------------------------------------------------------------
/// One opaque step of a recognized [`SemAdtReturnOpaque`] chain: a
/// `Terminator::Call` whose dest is a fresh, sole-written temp. The result is
/// ∀-bound in the kernel witness (`Bool`-sorted iff the dest local is
/// `Ty::Bool`, else the usual `Int` collapse) — the callee name is recorded
/// for diagnostics/tests only and carries ZERO semantic weight in the claim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemOpaqueStep {
    /// The callee name, exactly as extracted (diagnostic only — see type doc).
    pub callee: String,
    /// Whether the dest local is `Ty::Bool` (binds a `Bool` instead of `Int`).
    pub bool_typed: bool,
}

/// A value in the opaque chain: an entry-time-resolvable operand, or the
/// ∀-bound result of step `i`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemChainVal {
    /// An entry-time operand — restricted by the recognizer to
    /// `Var`/`Const`/`Field(Var, fld)` (everything else fails closed).
    Operand(SemOperand),
    /// The ∀-bound result of the `i`-th recognized step.
    Step(usize),
}

/// The guard of a recognized [`SemAdtReturnOpaque`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemOpaqueCond {
    /// A REAL entry-time comparison (`_g := BinaryOp(cmp, a, b)`), denoted
    /// exactly (the `fold_bvar_opt` family's `idx >= self.start`). Operands are
    /// entry-time [`SemOperand`]s only — a step-result comparison operand is
    /// out of this fragment (fail-closed).
    Cmp { op: SemCmpOp, a: SemOperand, b: SemOperand },
    /// The ∀-bound `Bool` result of step `i` — admitted ONLY for the
    /// `__trust_total_clone` total-derived-trait sentinel over a newtype-u64
    /// operand pair (the `fold_fvar_opt` family's `id == self.id`; see
    /// [`sem_adt_return_opaque_shape_of`]'s gate (G)).
    StepBool(usize),
}

/// One arm of a recognized [`SemAdtReturnOpaque`]: the constructed `Option`
/// variant tag (read DIRECTLY off the arm's own `Aggregate`, never guessed)
/// plus its payload chain value, if any.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemOpaqueArm {
    /// The constructed variant's discriminant.
    pub variant: i128,
    /// The single payload value (`None` for the nullary `Option::None` arm).
    pub payload: Option<SemChainVal>,
}

/// A recognized OPAQUE-CHAIN ADT-RETURN — see the section comment above for
/// the shape and its honesty tier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtReturnOpaque {
    /// Every opaque step (prefix + both arm chains), in walk order.
    pub steps: Vec<SemOpaqueStep>,
    /// The guard.
    pub cond: SemOpaqueCond,
    /// The THEN arm (guard true — the `SwitchInt`'s `otherwise` path).
    pub then_arm: SemOpaqueArm,
    /// The ELSE arm (guard false — the value-0 target path).
    pub else_arm: SemOpaqueArm,
    /// The outer enum's `Ty::Adt` name — always the `Option` spelling here
    /// (gate (0)), cross-checked against each arm's own `Aggregate`.
    pub enum_name: String,
}

/// The local-def ledger entry for [`sem_adt_return_opaque_shape_of`]'s walk.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OpaqueDef {
    /// An entry-time-resolvable value (`Var`/`Const`/`Field(Var, fld)`).
    Op(SemOperand),
    /// An IMMUTABLE reference (`Rvalue::Ref { mutable: false, .. }`) to an
    /// exact entry-time parameter or parameter field. It is consumable only
    /// by the unique sentinel call used as gate (G); references to arbitrary
    /// chain temporaries are deliberately outside this heap-free model.
    RefOf(OpaqueRefOrigin),
    /// A copied immutable shared-reference field of an entry parameter. This
    /// marker is deliberately more restrictive than [`OpaqueDef::RefOf`]: it
    /// may feed only an arm's final, direct payload-producing call. The
    /// refinement binds call results but has no heap transition, so admitting
    /// such an alias before the guard or before a later semantic read would be
    /// unsound even when the call signature itself is safe.
    FieldRefArg,
    /// A non-`_0` ADT `Aggregate` over resolved values — consumable ONLY as a
    /// call argument (the `ExprKind::BVar(x)` ctor feeding `ek`).
    Ctor,
    /// The ∀-bound result of step `i`.
    Step(usize),
    /// A comparison (`BinaryOp(cmp, a, b)`) over entry-time operands —
    /// consumable ONLY as the guard `SwitchInt` discriminant.
    Cmp(SemCmpOp, SemOperand, SemOperand),
}

/// Structural source identity for an immutable reference passed to the
/// total-derived-trait sentinel. This deliberately does not use [`SemOperand`]:
/// a newtype ADT such as `FVarId` is not itself a scalar kernel operand.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OpaqueRefOrigin {
    Param(u64),
    ParamField { param: u64, field: u64 },
}

// ---------------------------------------------------------------------------
// Trust: exact ORDERING-DISPATCH OPAQUE-CHAIN leaf (2026-07-11).
//
// This is deliberately not a generic `Ord::cmp` recognizer. The extractor
// represents several derived-trait calls with the same sentinel, so attaching
// comparison semantics from a callee/type spelling alone is unsound. Admission
// requires the exact audited Instantiator leaf identity and whole-body content
// hash, then rechecks the complete 10-block cmp/discriminant/three-arm shape as
// defense in depth. Any mutation, alias channel, interior-mutable depth carrier,
// intervening effect, forged sentinel/type/tag, or changed checked subtraction
// changes the hash and also fails one of the structural conjuncts below.
// ---------------------------------------------------------------------------
/// Exact extracted owner admitted by the ordering-dispatch leaf lane.
pub const INSTANTIATOR_ORD_LEAF_DEF_PATH: &str =
    "<expr::subst::Instantiator<'_> as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt";

/// Stable [`trust_types::VerifiableFunction::content_hash`] of the audited
/// owner above. Names are checked separately because content hashes exclude
/// `def_path` by design.
// B3-1 added `faithful_enum_repr`; outer `None` is exactly the historical
// flattened-struct meaning and is omitted only from stable hash material. The
// non-default faithful states remain hash-visible. Therefore this retains the
// audited pre-B3 pin instead of making legacy fixtures drift merely because
// their lossless wire now carries an explicit null field.
//
// UNWIND-EDGE RE-AUDIT NOTE: `Terminator::{Call,Assert,Drop}` gained the
// serde-defaulted `unwind: UnwindEdge` field (b62 unwind modeling), which IS
// hash-visible; `UnwindEdge::Unreachable` is the documented pre-unwind-modeling
// semantics (edge absent), so the audited SEMANTICS are unchanged and this pin
// already reflects the unwind-carrying schema. The value is the live
// `load_instantiator_ordering_leaf().content_hash()` and is asserted exactly by
// `instantiator_ordering_leaf_exact_vc_hash_and_discharge`.
pub const INSTANTIATOR_ORD_LEAF_CONTENT_HASH: &str =
    "b278bfb4d47462acaacc8863d4262cf43b536dd3881b74c69f5a8944c08c1c10";

/// Kernel-witness input for the exact ordering-dispatch leaf.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtReturnOpaqueOrd {
    /// Opaque call results in execution order: cmp, lift_at, bvar.
    pub steps: Vec<SemOpaqueStep>,
    /// Index of the cmp sentinel step.
    pub cmp_step: usize,
    /// Ordering variants in declaration order, with extracted tags.
    pub ord_variants: Vec<(String, i128)>,
    /// Option-producing arms in Ordering declaration order.
    pub arms: Vec<(String, SemOpaqueArm)>,
    /// Extracted outer enum name.
    pub enum_name: String,
    /// Exactly one checked-subtraction assert is crossed.
    pub crossed_asserts: usize,
}

// ===========================================================================
// Trust: SCALAR SENTINEL-SELECT (cmp-mono-select fixture, 2026-07-16) — the
// kernel-recognizable shape of a MONOMORPHIZED `<iN as Ord>::min` / `::max`: a
// two-arm `SwitchInt` select over the `__trust_total_clone` TOTAL sentinel Bool
// whose two arms each return ONE of the two by-VALUE scalar-int parameters.
//
// SHAPE (verified against every committed fixture under
// `fixtures/cmp-mono-select-2026-07-16/dumps/`; all int widths structurally
// identical):
//   BB0: _6 = const bool <flag>; _4 = &_2; _5 = &_1;
//        -> Call __trust_total_clone(<ref>, <ref>) dest=_3:Bool target=BB1
//   BB1: SwitchInt(_3) { 0 -> ELSE } otherwise -> THEN            (no value stmts)
//   THEN: _0 = <param P_then>;            -> Drop(<the other param>) target=JOIN
//   ELSE: _6 = const bool <flag>; _0 = <param P_else>; -> Drop(<other>)  = JOIN
//   JOIN: -> Return
//   (+ drop-flag unwind cleanup blocks that are UNREACHABLE on the happy path)
//
// HONESTY TIER — UNINTERPRETED-BUT-TOTAL, SHAPE-FAITHFUL (never value-faithful):
// `__trust_total_clone` is [`trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL`],
// modeled by the extractor (`apply_total_clone_sentinel`) as a TOTAL but
// UNINTERPRETED Bool — per `trust-vcgen`'s own note it "also covers `lt`/`le`/…",
// i.e. the primitive comparison IS this opaque Bool. So the ONLY sound claim is
// "min/max returns one of {self, other}, deterministically selected by the total
// Bool" — NEVER that it returns the numerically-smaller/larger value (the guard
// Bool carries no value, so a value claim would be a forgery). This is the
// SCALAR-Int specialization of [`sem_adt_return_opaque_shape_of`]'s `StepBool`
// tier: the two arms pass through a by-value parameter instead of constructing an
// `Option` variant. The kernel witness
// (`trustir_adt::check_scalar_sentinel_select_refinement`) binds the guard as a
// ∀-bound `Bool` and proves BOTH `g = true → then_param` and `g = false →
// else_param` by `congrArg` transport — genuine (a wrong claimed arm is
// KernelRejected), asserting nothing about the guard's value.
//
// DROP SOUNDNESS: the two arm `Drop`s discard the by-value scalar-int parameter
// the arm did NOT return. A primitive integer is `Copy`, so it CANNOT `impl Drop`
// and has TRIVIAL (no-op) drop glue; treating the `Drop` as a no-op is sound ONLY
// for such a place (a non-`Copy`-scalar dropped place DECLINES — the recognizer's
// `is_copy_scalar_int` guard). The drop-flag temp and the unwind/cleanup blocks
// are UNREACHABLE from entry on the happy path (verified by an exhaustive
// reachability walk), so they cannot affect the observable return.
// ===========================================================================
/// A recognized SCALAR SENTINEL-SELECT — see the section comment above for the
/// shape and its honesty tier (uninterpreted-but-total, shape-faithful, NOT
/// value-faithful).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemScalarSentinelSelect {
    /// The parameter op-index (`local - 1`) the guard-TRUE arm (the `SwitchInt`
    /// `otherwise` edge) returns.
    pub then_var: u64,
    /// The parameter op-index the guard-FALSE arm (the `SwitchInt` value-`0` edge)
    /// returns.
    pub else_var: u64,
    /// The scalar return width — documentation / certificate provenance only (the
    /// kernel carrier is the unbounded `Int` regardless of width/sign).
    pub width: u32,
    /// The scalar return signedness — documentation only.
    pub signed: bool,
}

// ---------------------------------------------------------------------------
// Trust: ADT PAYLOAD-EXTRACTION SELECT (optres-payload-extract, 2026-07-17) —
// the FIRST recognizer that reads a variant's PAYLOAD out of an enum (not just
// its tag): the value-faithful `Option::<i32>::unwrap_or` / `Result::<T,E>::
// unwrap_or` TOTAL-SELECT shape
//
//   bb0: _d := Discriminant(self);  SwitchInt(_d) { <def_tag> -> DEFAULT,
//                                                   <ext_tag> -> PAYLOAD }
//                                                   otherwise -> UNREACHABLE
//   PAYLOAD: _0 := Use(self.Downcast(ext_tag).Field(f));  <join>
//   DEFAULT: _0 := Use(Move/Copy <default param>);        <join>
//
// certified by the enum inductive's auto-derived RECURSOR: the extraction MODEL
//   `E.rec.{1} (λ_.Int) [default-minor := d] [ext-minor := λx.x] o`
// ι-reduces to `x` on the extract variant and `d` on the other — value-faithful
// PAYLOAD extraction + dispatch-faithful arm routing (the kernel witness lives
// in `trustir_adt::check_payload_extract_refinement`, an ι-reduction TAUTOLOGY
// that verifies the recursor MODEL; the WHOLE denotation burden falls on the
// gates below).
//
// SOUND-SUBSET BOUNDARY (adversarial phase, wf_779b8c2b): the DEFAULT arm is
// admitted ONLY as `Use(Move/Copy <parameter>)` — a genuine parameter local,
// value-faithful. A `__trust_total_clone` None arm (`unwrap_or_default`'s
// `Default::default()` sentinel) is a many-to-one HAVOC erasure over all
// panic-free total calls, NOT provably `<T as Default>::default() == 0` — so it
// is DECLINED here (it writes `_0` via a `Terminator::Call` dest, which fails
// both the `local_write_count(_0) == 2` statement-write gate and the explicit
// no-Call-dest-writes-`_0` gate). Modeling it as the scalar `0` would be a FALSE
// certificate; this recognizer never does.
// ---------------------------------------------------------------------------
/// A recognized ADT payload-extraction select (`unwrap_or` with a PARAMETER
/// default). The SOUND SUBSET only: the default arm reads a genuine parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtPayloadExtract {
    /// The CONCRETE monomorphized enum self type (e.g. `Option<i32>`,
    /// `Result<i32,u8>`) — the `Ty::Adt` of the by-value `self` parameter, from
    /// which `reflect_enum` builds the real multi-constructor Clean inductive.
    pub self_ty: trust_types::Ty,
    /// The variant whose payload is extracted (`Some`=1 for `Option`, `Ok`=0 for
    /// `Result`). EQUAL, by the load-bearing provenance triple, to (a) the switch
    /// tag routing to the payload arm, (b) that arm's `Downcast` variant index,
    /// and (c) the constructor index in the recursor's field-reading minor.
    pub extract_variant: usize,
    /// The field index within `extract_variant` read out (0 for `Option`/`Result`).
    pub extract_field_idx: usize,
    /// The DEFAULT arm's parameter op-index (`local - 1`) — `unwrap_or`'s
    /// `default`. The SOUND SUBSET: only a genuine `Use(Move/Copy <param>)`
    /// default is recognized (a `__trust_total_clone` None arm is declined).
    pub default_var: u64,
}

// ---------------------------------------------------------------------------
// Trust: W6 CLOSURE-COMPOSITION (increment 1, 2026-07-18) — the FIRST
// substrate-wall rung: the recognized monomorphized
// `Option::<i32>::map::<i32, {closure@…}>` over a NON-CAPTURING, spec-free
// FnOnce closure. The closure call is the EXPLICIT, un-inlined
// `<{closure@span} as FnOnce<(i32,)>>::call_once(move env, move (x,))` Call
// terminator (span-shaped `func` string with NO def_path_hash — callee identity
// therefore comes SOLELY from the env operand's `Ty::Closure.name`, resolved
// EXACT-ONLY against the certified registry; see [`resolve_certified_callee_exact`]
// and the recognizer's gate 6).
//
// SHAPE (the harvested 6-block body, `fixtures/w6-map-closure-2026-07-18`):
//   bb0: `_d := Discriminant(_1)`; SwitchInt(_d) [t_none → NONE arm, t_call →
//        CALL arm] otherwise → Unreachable, exhaustive.
//   bb1: Unreachable.
//   NONE arm: `_0 := Aggregate(Adt{E, none_variant}, [])`; Drop(_2) → JOIN.
//   CALL arm: `_x := Use(Move/Copy _1.Downcast(t_call).Field(0))`;
//             `_e := Move(_2)`; `_t := Aggregate(Tuple, [Copy/Move _x])`;
//             Call `_y = call_once(Move _e, Move _t)` → CONT.
//   CONT: `_0 := Aggregate(Adt{E, call_variant}, [Move/Copy _y])`; Goto JOIN.
//   JOIN: Return.
//
// HONESTY TIER — MODEL-ONLY, split-claims (do not overclaim). The witness
// certifies dispatch + Some(call_result)/None construction faithfulness over the
// per-call reflected Option<i32> carrier, PLUS certified-leaf closure safety +
// requires establishment. The closure CALL is the opaque `callResult` carrier
// pinned to the EXACT certified callee (identity via the exact-match gate + the
// registry index) — NOT an `f(x)` value claim. The payload→arg dataflow (x → f)
// is recognizer-pinned SYNTACTICALLY (gates 3+5), kernel-restated only up to the
// inherited one-arg model. This is a recognizer-faithfulness verdict for the mono
// map instance (unlocking it as a registry callee), NOT an end-to-end
// wrapper-chain proof and NOT `map(o,f) computes f(x)` in-kernel.
// ---------------------------------------------------------------------------
/// The closure-composition RETURN discipline — the ONE axis on which the
/// increment-1 `map` shape and the increment-2 `and_then` shape differ (W6
/// increment 2, 2026-07-18). BOTH share every base gate (dispatch, TAG↔DOWNCAST,
/// env chain, args tuple, EXACT-callee resolution); only the closure's declared
/// return type and the CALL-continuation construction differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComposeReturn {
    /// `Option::<i32>::map`: the closure returns `Int`; the CALL-continuation block
    /// RE-WRAPS the Int call dest as `Some(dest)` (`_0 := Aggregate(Adt{E,
    /// call_variant}, [Move dest])`). The kernel some-minor is `C_some(callResult …)`.
    MapWrap,
    /// `Option::<i32>::and_then`: the closure returns the SAME `Option` enum, and
    /// the call dest IS `_0` directly (no re-wrap; the CALL-continuation block only
    /// drops storage before the join). The kernel some-minor is the bare opaque
    /// carrier-typed return `ret : T` (the call result IS the return).
    AndThenFlat,
}

/// A recognized W6 closure-composition (`Option::<i32>::{map,and_then}` over a
/// non-capturing, spec-free FnOnce closure). Produced ONLY by
/// [`sem_adt_map_compose_of_discriminant_switch`] (fail-closed). See that
/// function's section comment for the shape + the MODEL-ONLY honesty tier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtMapCompose {
    /// Whether the closure result is `Some`-rewrapped (`map`) or flows straight to
    /// `_0` (`and_then`). Determined from the closure's declared `call.ret` type
    /// (Int ⇒ [`ComposeReturn::MapWrap`]; the SAME `Option` carrier ⇒
    /// [`ComposeReturn::AndThenFlat`]) and cross-checked against the MIR
    /// continuation shape.
    pub kind: ComposeReturn,
    /// The CONCRETE monomorphized 2-variant enum self type (`Option<i32>`), from
    /// which `reflect_enum` builds the real multi-constructor Clean inductive that
    /// is BOTH the input and (same registered carrier) the output.
    pub self_ty: trust_types::Ty,
    /// The SOME/CALL variant index — the one the CONT block constructs as
    /// `Aggregate(Adt{E, call_variant}, [Move _y])` with EXACTLY one Int field, and
    /// whose switch tag equals the payload arm's `Downcast` variant (the load-bearing
    /// provenance link). `disc_index_safe` ⇒ tag == variant index.
    pub call_variant: usize,
    /// The NONE variant index — the direct switch arm the NONE block constructs as
    /// `Aggregate(Adt{E, none_variant}, [])` (nullary), tag == variant index.
    pub none_variant: usize,
    /// The EXACT resolved closure def-path — EQUAL to the env operand's
    /// `Ty::Closure.name` AND to the certified-registry key (exact-only; NEVER a
    /// suffix match — the mandatory adversarial gate).
    pub callee: String,
    /// The closure's index in the (sorted) certified registry — the `Nat` callee-id
    /// the kernel `Call.mk` instance names.
    pub callee_id: u64,
    /// The closure ENV operand (`Var(env_param_idx)`) — the FnOnce env the Call's
    /// first actual moves, traced to the bare closure parameter. This is the ONLY
    /// actual the kernel `Call.mk` pins (the inherited one-arg-model residue).
    pub env_operand: SemOperand,
}

// ---------------------------------------------------------------------------
// Trust: W6 CLOSURE-COMPOSITION (increment 2, 2026-07-18) — the PREDICATE-FILTER
// rung: the recognized monomorphized `Option::<i32>::filter::<{closure@…}>` over a
// NON-CAPTURING, spec-free `FnOnce(&i32) -> bool` closure. Strictly richer than the
// `map`/`and_then` shapes: the closure takes a REF to the payload, returns a
// `bool`, and the body carries a SECOND `SwitchInt` (on the predicate result),
// Drop plumbing, and an unwind Resume block.
//
// SHAPE (the harvested 11-block body, `fixtures/w6-map-closure-2026-07-18`):
//   bb0(ENTRY): `_d := Discriminant(_1)`; SwitchInt(_d) [some_tag → SETUP, none_tag →
//               NONE] otherwise → Unreachable, exhaustive.
//   NONE arm: `_0 := Aggregate(Adt{E, none}, [])`; Drop(_2) → JOIN.
//   SETUP arm: `_x := Use(Move/Copy _1.Downcast(some_tag).Field(0))`;
//              `_e := Move(_2)`; `_r := Ref(false, _x)`; `_t := Aggregate(Tuple,
//              [Copy/Move _r])`; Call `_b = call_once(Move _e, Move _t)` → BOOLSW.
//   BOOLSW: SwitchInt(_b) [0 → DROP] otherwise → KEEP (a 1-target bool switch; the
//           explicit tag orients keep-vs-drop).
//   KEEP: `_y := Use(Move/Copy _x)` (reconstruct from the ORIGINAL payload);
//         `_0 := Aggregate(Adt{E, some_tag}, [Move/Copy _y])`; Goto JOIN.
//   DROP: Drop(_x) → NONE2; NONE2: `_0 := Aggregate(Adt{E, none}, [])`; Goto JOIN.
//   JOIN: Return.  (plus an UNWIND Drop(_x) → Resume pair, UNREACHABLE from entry.)
//
// HONESTY TIER — MODEL-ONLY, split-claims (same as `map`/`and_then`). The witness
// certifies dispatch + the predicate-conditioned Some(x)/None reconstruction over
// the reflected Option<i32> carrier: on `Some(x)`, filter returns `if <predicate>
// then Some(x) else None`, where `<predicate>` is a ∀-bound OPAQUE `Bool` (the SAME
// ∀-bound-opaque device the `adt_return_opaque` StepBool tier uses — the Int
// `callResult` can NOT carry a Bool). Some(x) is RECONSTRUCTED from the ORIGINAL
// payload (the recognizer pins the reconstruct local == the extracted payload, so a
// forged reconstruct-with-a-different-value declines). The closure identity is the
// recognizer's EXACT-match gate + the per-site `check_call_return_instance`; NOT a
// `predicate(x)` value claim. The `&x` argument denotes `x` by the W-REF-FWD
// immutable-ref-transparency argument (the arg is content-free in the kernel term
// anyway). Fail-closed on every deviation (a reachable Resume, a Drop of anything
// but the payload/closure, a non-ref arg, a second call, a broken TAG↔DOWNCAST
// triple, an EXACT-callee miss, a reconstruct off a substitute local).
// ---------------------------------------------------------------------------
/// A recognized W6 increment-2 PREDICATE-FILTER composition
/// (`Option::<i32>::filter` over a non-capturing, spec-free `FnOnce(&i32) -> bool`
/// closure). Produced ONLY by [`sem_adt_filter_compose_of_discriminant_switch`]
/// (fail-closed). See that function's section comment for the shape + honesty tier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtFilterCompose {
    /// The CONCRETE monomorphized 2-variant enum self type (`Option<i32>`).
    pub self_ty: trust_types::Ty,
    /// The SOME/KEEP variant index — the one the KEEP block RECONSTRUCTS from the
    /// original payload as `Aggregate(Adt{E, some_variant}, [Move recon])`.
    pub some_variant: usize,
    /// The NONE variant index — both the direct NONE arm and the predicate-false
    /// DROP path construct it (nullary).
    pub none_variant: usize,
    /// The EXACT resolved closure def-path (exact-only; NEVER a suffix match).
    pub callee: String,
    /// The closure's index in the (sorted) certified registry.
    pub callee_id: u64,
    /// The closure ENV operand (`Var(env_param_idx)`).
    pub env_operand: SemOperand,
}

// ---------------------------------------------------------------------------
// Trust: DIVERGENCE-GUARDED ADT PAYLOAD EXTRACTION (W-UNWRAP-DIVERGE,
// 2026-07-17) — the value-faithful `Option/Result::{unwrap,expect}` shape: a
// two-arm `SwitchInt(Discriminant(self))` whose PAYLOAD arm reads
// `self.Downcast(v).Field(f)` and RETURNS, and whose OTHER arm DIVERGES (the
// `unwrap_failed`/`expect_failed` panic call — an `Opaque`/`Unreachable`/`Resume`
// closure that never writes `_0` and never reaches `Return`). Composes TWO landed
// lanes:
//
//   * the recursor PAYLOAD witness (`trustir_adt::build_payload_extract`'s SOME
//     obligation) — "on the Some/Ok arm, the return IS the payload"; and
//   * the divergence-guard discipline (the fail-closed CFG-closure walk
//     `cfg_reachable_from`) — the panic arm provably DIVERGES.
//
// HONESTY TIER (do not overclaim): on the NON-panicking path, `unwrap`/`expect`
// returns the Some/Ok payload (value-faithful via recursor ι-reduction); the
// None/Err path DIVERGES (panic), modeled as divergence, NOT as a value. The
// kernel obligation is the SOME-side ι-reduction ONLY — there is NO None-side
// value obligation (the paired `unwrap_or` lane's caller-default arm is REPLACED
// by divergence here). The panic itself is a SAFETY-VC concern, not a value one:
// the panic `Opaque` terminator raises an `UnsupportedMir` VC (bb targets), which
// is NOT an `is_safety_vc_kind` obligation — so it does NOT trip
// `function_emits_unmodeled_safety_vc_pub` and needs no discharge. This is an
// honest fact about the emitter's VC taxonomy, NOT a weakening of any safety gate.
//
// DISJOINT from the paired `sem_adt_payload_extract_of_discriminant_switch`: that
// recognizer requires `_0` written EXACTLY twice (two value arms); this one
// requires EXACTLY once (the sole happy arm — the panic arm writes no `_0`). So no
// body is accepted by both, and `unwrap_or_default`'s `__trust_total_clone` Call
// -dest None arm (a havoc sentinel) is declined by BOTH the Call-dest gate AND the
// divergence gate (its "None" arm reaches `Return`, it does not diverge).
// ---------------------------------------------------------------------------
/// A recognized DIVERGENCE-GUARDED ADT payload extraction (`unwrap`/`expect`): the
/// payload arm reads `self.Downcast(extract_variant).Field(extract_field_idx)` and
/// returns; the OTHER arm DIVERGES (panic), modeled as divergence — NOT a value.
/// Unlike [`SemAdtPayloadExtract`] there is NO `default_var` (the non-payload arm
/// carries no value obligation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtPayloadExtractDiverging {
    /// The CONCRETE monomorphized enum self type (`Option<i32>`, `Result<i32,u8>`).
    pub self_ty: trust_types::Ty,
    /// The variant whose payload is extracted (`Some`=1 for `Option`, `Ok`=0 for
    /// `Result`) — EQUAL, by the load-bearing provenance triple, to the switch tag
    /// routing to the payload arm and to that arm's `Downcast` variant index.
    pub extract_variant: usize,
    /// The field index within `extract_variant` read out (0 for `Option`/`Result`).
    pub extract_field_idx: usize,
}

// ---------------------------------------------------------------------------
// Trust: RANGE+DISJUNCTION guard (2026-07-08) — the DECISION-DAG recognizer for
// a 2-arm guarded return whose switch graph encodes a short-circuit BOOLEAN
// COMBINATION (with `||`) rather than the single linear `&&` chain
// [`sem_conjunctive_chain`] models. The `core::u8::is_ascii_control` shape:
//
// ```text
//   bb0: _2 := Le(0, *self);   switchInt(_2)  { 0 → bb2, _ → bb3 }
//   bb3: _3 := Le(*self, 31);  switchInt(_3)  { 0 → bb2, _ → bb4 }   -- range fail → eq test
//   bb2:                       switchInt(*self) { 127 → bb4, _ → bb1 } -- RAW-VALUE eq
//   bb4: _0 := true;  goto bb5
//   bb1: _0 := false; goto bb5
// ```
//
// denotes `(0 <= *self && *self <= 31) || *self == 127`, and `ascii_utils`'
// `is_space` the mirror `b == 32 || (9 <= b && b <= 13)`. Two genuinely new
// pieces beyond the conjunctive chain:
//   * a RAW-VALUE equality leaf — a `SwitchInt` whose discriminant is the modeled
//     scalar ITSELF (a parameter / deref-self read), with ONE explicit target
//     value `v`: cond `discr == v`, success = the `v` target, failure =
//     `otherwise` (the multi-value generalization stays with `trustir_multieq`);
//   * the DISJUNCTIVE combination, denoted via the ADDITIVE `Cond.Or`.
//
// The recognizer walks the switch DAG from its unique head and denotes each
// switch recursively over (success-branch denotation `ds`, failure-branch
// denotation `df`) with EXACTLY four composition rules (True = reaches the THEN
// arm, False = reaches the ELSE arm):
//
//   (ds=True,  df=False) → c                     -- a bare test
//   (ds=True,  df=D)     → Or(c, D)              -- `c || D` (success short-circuits)
//   (ds=D,     df=False) → And(c, D)             -- `c && D` (failure short-circuits)
//   (ds=Or(x,e), df=e)   → Or(And(c, x), e)      -- the ABSORB rule: a conjunct's
//                                                -- failure falls into the SAME next
//                                                -- clause its successor's failure
//                                                -- does — `if c {x||e} else {e}`
//                                                -- ≡ `(c && x) || e`
//
// Anything else (a shape needing `Not`, mismatched failure continuations, a
// True/True degenerate…) DECLINES. Fail-closed gates: every switch in the body
// must be visited exactly once along the walk (no stray/unvisited switch), the
// head must be unique, the DAG bounded ([`DISJ_DAG_MAX_SWITCHES`]), and cycles
// decline via a path-visited set. Both (then, else) arm assignments are tried —
// the rules are asymmetric (no negation), so at most one succeeds on real shapes;
// each successful denotation is faithful FOR ITS OWN assignment, so trying both
// is a completeness measure, never a soundness risk.
// ---------------------------------------------------------------------------
/// Bounded sub-CFG size for [`sem_decision_dag_chain`]: the maximum number of
/// `SwitchInt`s the decision DAG may contain. Real shapes measure 2–3
/// (`is_ascii_control`: 3; `is_space`: 3); 8 leaves headroom for a longer clause
/// list while declining adversarially bloated graphs.
const DISJ_DAG_MAX_SWITCHES: usize = 8;

/// The intermediate denotation of a decision-DAG node: reaches the THEN arm
/// (`True`), the ELSE arm (`False`), or a computed condition.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DagDenote {
    True,
    False,
    Cond(SemCondTree),
}

// ---------------------------------------------------------------------------
// Trust: ADT-return leaf, 3-OUTCOME GUARD CHAIN (gap-queue #2 follow-up #1,
// 2026-07-08) — `if cond1 { <construct A> } else if cond2 { <construct B> } else
// { <construct C> }`, the `cast` 0.3.0 `from_signed!`-class shape:
//
// ```text
//   fn cast(src) -> Result<$dst, Error> {
//       Err(if src < $dst::MIN as $src { Error::Underflow }
//           else if src > $dst::MAX as $src { Error::Overflow }
//           else { return Ok(src as $dst); })
//   }
// ```
//
// which lowers to TWO sequential single-target `SwitchInt`s (the first's
// value-0/FALSE edge feeding the second switch's OWN block — a linear guard
// chain, NOT the conjunctive `&&` chain [`sem_conjunctive_chain`] models: THAT
// shape requires every switch's value-0 edge to converge on the SAME else arm;
// THIS shape's first switch's value-0 edge is the SECOND TEST, not an arm).
//
// Real MIR adds one wrinkle beyond a flat 3-way split: the source's `Err(if …)`
// desugars so the guard's TRUE arms often each write a SHARED payload temp (the
// `Error` value under construction) and Goto a COMMON "wrap in Err" sink block —
// e.g. `from_signed!`'s Underflow/Overflow arms both write `_2` then Goto the
// SAME `_0 := Aggregate(Result, Err, [_2])` block, `_2`'s value differing per
// incoming edge. `arm_adt_ctor_value_for`'s whole-body single-writer search
// would (rightly) decline `_2` as multiply-assigned; each arm's resolution here
// is instead WALK-LOCAL (the value `_2` holds is read off the SINGLE write seen
// ALONG THAT ARM'S OWN straight-line Goto/Assert walk from its branch target to
// the sink — sound because a Goto/Assert chain has no other incoming edge that
// could interfere, and a DIFFERENT arm's walk is free to write the SAME local
// without that being a soundness hazard for THIS arm's resolution).
// ---------------------------------------------------------------------------
/// A recognized 3-outcome guard-chain ADT return. Mirrors [`SemAdtReturn`] at the
/// guard layer (each `cond` is a bare comparison leaf — a chained guard is always a
/// simple compare in the target family, never a conjunction or discriminant read;
/// out of scope, declines) but diverges into THREE arms instead of two.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtReturn3 {
    /// The FIRST guard — `arm_a` is taken when TRUE.
    pub cond1: SemCondTree,
    /// The SECOND guard, tested only when `cond1` is FALSE — `arm_b` is taken
    /// when TRUE, `arm_c` when FALSE.
    pub cond2: SemCondTree,
    /// `cond1` TRUE.
    pub arm_a: SemAdtArm,
    /// `cond1` FALSE, `cond2` TRUE.
    pub arm_b: SemAdtArm,
    /// `cond1` FALSE, `cond2` FALSE.
    pub arm_c: SemAdtArm,
    /// The outer enum's `Ty::Adt` name (e.g. `"core::result::Result"`).
    pub enum_name: String,
}

/// One arm's WALK-LOCAL resolution result: the [`SemAdtArm`] plus the sink block
/// (the block whose `_0 := …` statement supplied it) — callers use the sink to
/// enforce the "no extra `_0` write" well-formedness gate (generalized from
/// [`sem_adt_return_shape_of`]'s fixed `== 2` to the DISTINCT-sink count, since two
/// arms legitimately sharing one sink is the target family's own real shape).
struct ChainArm {
    arm: SemAdtArm,
    sink: trust_types::BlockId,
}

// ---------------------------------------------------------------------------
// Trust: MULTI-VALUE SwitchInt disjunctive-equality guard (2026-07-08) —
// `if discr ∈ {v1,...,vN} { then } else { else }`: ONE `SwitchInt` whose
// EXPLICIT targets (2 or more DISTINCT literal values) ALL converge on a
// SINGLE arm block, `otherwise` reaching the OTHER arm — the
// `core::u8::is_ascii_whitespace`-class shape (real MIR:
// `SwitchInt((*_1)) {9→T, 10→T, 12→T, 13→T, 32→T, otherwise→F}`, rustc's
// lowering of a Rust OR-pattern match it does not fold into a range or
// comparison chain — `ascii_utils`'s hand-written `9<=b && b<=13 || b==32`
// lowers DIFFERENTLY, as nested single-target switches, which the EXISTING
// `sem_cf_return_of_mir`/`sem_conjunctive_chain` machinery already covers).
//
// Denoted as a disjunctive equality guard `discr==v1 ∨ discr==v2 ∨ … ∨
// discr==vN` — a NEW, SELF-CONTAINED kernel witness
// (`trustir_multieq::check_multi_eq_refinement`, mirroring `trustir_adt`'s
// `Bool.rec` + `congrArg`-transport recipe, generalized from a SINGLE
// comparison guard to an N-ARY `Bool.or` FOLD of equality tests over an `Int`
// motive), never touching the shared `SemCondTree`/`Formula`/
// `clean_ground::ground_bool` machinery the OTHER recognizers use (a
// narrowly-scoped sibling, not a refactor or extension of that shared type).
//
// No float-guard defense needed here (unlike the guard-COMPARISON shapes
// above): `Terminator::SwitchInt`'s OWN discriminant is, by rustc's MIR
// invariants, always an integer/bool/char/enum-discriminant SCALAR value
// directly — never a float (a float comparison always lowers through an
// intermediate `BinaryOp` Bool temp, the shape the `sem_adt_guard_operand_of_mir`-
// gated recognizers above cover, not this one).
// ---------------------------------------------------------------------------
/// A recognized multi-value disjunctive-equality guarded return.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemMultiEqReturn {
    /// The switched-on discriminant (a bare parameter, or an immutable-reference
    /// deref of one — the GAP-DEREF-SELF shape `sem_operand_of_mir` already models).
    pub discr: SemOperand,
    /// The 2+ DISTINCT literal values whose match reaches the THEN arm, in the
    /// `SwitchInt`'s OWN target order (immaterial to the guard's truth —
    /// `Bool.or` is associative/commutative — kept for a deterministic,
    /// non-reordering witness).
    pub values: Vec<i128>,
    /// The arm reached when `discr` matches ANY of `values` — a bare `Use`
    /// (parameter or constant) rvalue only; anything richer is out of scope,
    /// declines (this shape's real target family — `bool`-literal arms — never
    /// needs more).
    pub then_op: SemOperand,
    /// The arm reached otherwise.
    pub else_op: SemOperand,
}

/// The recognized shape of a FIELDLESS-ENUM `Clone::clone`: a single-block
/// `fn clone(&self) -> E { *self }` — the SOLE statement copies `(*self)` into
/// the return place `_0` and the block returns. `self_param` is the 0-based
/// parameter index of the `&self` argument (read from the MIR — 0 in the
/// derived impl).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemFieldlessEnumClone {
    pub self_param: u64,
}

/// The recognized shape of a FIELDLESS-ENUM `PartialEq::eq`: a single-block
/// `fn eq(&self, other: &E) -> bool { disc(*self) == disc(*other) }` — two
/// `Rvalue::Discriminant` reads (one per `&E` param) feeding the SINGLE `Eq`
/// binop that produces the returned `bool`. `self_param`/`other_param` are the
/// two 0-based parameter indices (0 and 1 in the derived impl, read from the
/// MIR).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemFieldlessEnumEq {
    pub self_param: u64,
    pub other_param: u64,
}

/// The recognized shape of a FIELDLESS-ENUM guarded identity select such as
/// `Ordering::then`: return `other` for one exact discriminant tag and return
/// `self` for every other tag. The selected tag is read from the sole
/// `SwitchInt` target and retained as an `Int`; no variant name or def-path
/// spelling is trusted as semantic authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemFieldlessEnumThen {
    pub self_param: u64,
    pub other_param: u64,
    pub selected_tag: i128,
}

// ---------------------------------------------------------------------------
// Step 5 — the COMPLETE per-function verdict: FULLY FAITHFUL
// ---------------------------------------------------------------------------
//
// THE CULMINATION (Goal #4). `function_adequacy_witness` certifies a function's
// WHOLE CONTRACT reflection (operand/rvalue/return adequacy, Lemmas 1A+1B+1C).
// `function_safety_vcs_faithful` certifies its SAFETY VCs (overflow/bounds/div,
// Lemmas 2/3/4). Each is a SEPARATE axis. A function is FULLY FAITHFUL only when
// BOTH axes close at once over its ENTIRE reflection: the whole-function contract
// is kernel-adequate to MirSem AND every single safety VC the emitter raises is a
// modeled kind whose adequacy certifies modulo 3. The composed certificate's mere
// EXISTENCE is the end-to-end claim — this function's reflection is proven adequate
// to the MIR operational semantics, modulo exactly the 3 foundational axioms,
// nothing trusted.
//
// FAIL-CLOSED, in both directions:
//   * any uncertified contract piece (operand/rvalue/return) ⇒ NOT fully faithful;
//   * ANY safety VC the emitter raises that is UNMODELED (signed overflow, float
//     div, shift/cast/negation, …) ⇒ NOT fully faithful — even one unmodeled safety
//     VC means the function's reflection is NOT end-to-end kernel-proven, so it must
//     not carry the verdict;
//   * a modeled safety VC whose adequacy does not kernel-check modulo 3 ⇒ NOT fully
//     faithful.
// A function with NO safety VC and a certified contract IS fully faithful (vacuously
// on the safety side — there is no unsafe condition to capture, and the contract is
// proven adequate). The verdict MEANS what it says: "fully faithful" = genuinely,
// end-to-end, kernel-verified adequate to MIR semantics, modulo 3.
/// The COMPLETE per-function faithfulness verdict (Goal #4 culmination). Minted ONLY
/// when a function's ENTIRE reflection is kernel-proven adequate to the MIR
/// operational semantics, modulo exactly the 3 foundational axioms:
///
///   * `contract` — the COMPOSED whole-function contract certificate
///     ([`FunctionAdequacyCertificate`]): every operand (Lemma 1A), every rvalue
///     (Lemma 1B), and the return witness (Lemma 1C) certifies modulo 3.
///   * `safety` — the per-kind safety-VC certificates
///     ([`FunctionSafetyVcCertificates`]) covering EVERY safety VC the function
///     emits, when it emits any. `None` is the VACUOUS-SAFE case: the function
///     raises NO safety VC at all (so there is nothing to capture), and the contract
///     adequacy alone makes it fully faithful. A `Some` carries the certificates for
///     a function whose every (modeled) safety VC certified.
///
/// A function with an UNMODELED safety VC, or any uncertified contract/safety piece,
/// gets NO `FullFaithfulnessCertificate` (fail-closed) — never a false one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullFaithfulnessCertificate {
    /// The whole-function contract adequacy certificate (Lemmas 1A+1B+1C, modulo 3).
    pub contract: FunctionAdequacyCertificate,
    /// The safety-VC adequacy certificates (Lemmas 2/3/4) covering every safety VC
    /// the function emits — or `None` when the function emits NO safety VC at all
    /// (the vacuously-safe case: nothing to capture, contract adequacy suffices).
    pub safety: Option<FunctionSafetyVcCertificates>,
}

impl FullFaithfulnessCertificate {
    /// Whether this complete verdict rests on ONLY the 3 foundational axioms: the
    /// composed contract certificate is modulo 3 AND, if present, every safety-VC
    /// certificate is modulo 3. A certificate that EXISTS is modulo 3 by construction
    /// (the witness builder is fail-closed), but this re-checks defensively.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        self.contract.is_modulo_3()
            && self.safety.as_ref().is_none_or(FunctionSafetyVcCertificates::all_modulo_3)
    }

    /// Whether this function carries a modeled safety VC (i.e. the safety axis was
    /// non-vacuously certified). `false` = vacuously safe (no safety VC emitted).
    #[must_use]
    pub fn has_certified_safety_vc(&self) -> bool {
        self.safety.as_ref().is_some_and(FunctionSafetyVcCertificates::any)
    }
}

// ===========================================================================
// Step 6 — THE FAITHFULNESS META-THEOREM (Goal #4 capstone): a single
// Clean-checked REFINEMENT theorem, proven by STRUCTURAL INDUCTION (List.rec),
// that the reflection's SUBSTITUTION denotation refines the MIR operational
// (env-threading) semantics for the modeled straight-line fragment.
// ===========================================================================
//
// WHAT THE INGREDIENTS GAVE US, AND THE GAP THIS CLOSES.
// Lemmas 1A/1B/1C and `function_adequacy_witness` certify each PIECE (operand,
// rvalue, single-return) of a function's reflection by REFLEXIVITY — `eval e O`
// ι-reduces to the grounded denotation. But the per-function witness COMPOSES
// those pieces in Rust, not in the kernel: there was no META-LEVEL theorem that
// the Clean denotation of the WHOLE reflected body equals its MIR operational
// semantics. A reflexivity composition cannot express that, because the two
// whole-body semantics are GENUINELY DIFFERENT functions (see below) — relating
// them needs a real induction over the statement list.
//
// THE TWO GENUINELY-DIFFERENT DENOTATIONS OF A STRAIGHT-LINE BODY.
// Model a body as a statement LIST split into a processed prefix `l1` and a
// remaining suffix `l2`, plus a return operand `ret` (a `Function` is the triple
// `(l1, l2, ret)`; a whole body is `(stmts, [], ret)` and the theorem is general
// over the split, so it covers every body+suffix decomposition):
//
//   * `exec_threaded   e l1 l2 ret := eval (exec e (l1 ++ l2)) ret`
//        the OPERATIONAL semantics — env-THREAD the whole concatenated trace
//        `l1 ++ l2` (each statement's rvalue evaluated under the running env),
//        then read the return under the FINAL env.
//   * `denote_substituted e l1 l2 ret := eval (exec (exec e l1) l2) ret`
//        the REFLECTION's SUBSTITUTION semantics — thread the prefix `l1` to a
//        sub-env, then SUBSTITUTE the suffix `l2` (re-thread it on top of that
//        sub-env), then read the return. This is the compositional form the
//        grounder uses: it processes a trace by substituting later assignments
//        on top of the already-computed earlier ones, rather than threading the
//        flat list. (`exec (exec e l1) l2` is `exec ∘ exec`, NOT `exec` of the
//        append — the kernel does NOT see them as def-eq; verified by test.)
//
// These are DISTINCT FUNCTIONS: `exec_threaded` recurses on `l1 ++ l2`,
// `denote_substituted` on `l1` then `l2`. A bare `Eq.refl` does NOT prove them
// equal for a VARIABLE `l1` (tested: `refinement_is_genuinely_inductive`), so the
// theorem is NOT a trivial reflexivity — it requires the inductive proof.
//
// THE REFINEMENT THEOREM (kernel-proven, modulo 3, by induction).
//   refinement : ∀ (e : Env)(l1 l2 : List Stmt)(ret : Operand),
//                  exec_threaded e l1 l2 ret = denote_substituted e l1 l2 ret
// It is `congrArg (λ env. eval env ret)` applied to the ENV-LEVEL append law
//   execAppendLaw : ∀ (l1 l2 : List Stmt)(e : Env),
//                     exec (exec e l1) l2 = exec e (l1 ++ l2)
// which is proven by STRUCTURAL INDUCTION on `l1` (`List.rec` at a Prop motive):
//   * BASE (l1 = nil): `exec e nil ≡ e` and `nil ++ l2 ≡ l2`, so both sides
//     ι-reduce to `exec e l2` — closed by `Eq.refl` (this is the per-op return
//     adequacy at the empty-prefix position: the reflection of a return with no
//     processed prefix IS its operational value).
//   * STEP (l1 = Assign i R :: rest, IH : ∀ l2 e, exec (exec e rest) l2 =
//     exec e (rest ++ l2)): the goal's LHS `exec (exec e (s::rest)) l2`
//     ι-reduces (the `exec`-on-cons fold) to `exec (exec (step e s) rest) l2`,
//     and the RHS `exec e ((s::rest) ++ l2)` to `exec (step e s) (rest ++ l2)`
//     — where `step e s = set e i (eval_rvalue e R)` composes the per-rvalue
//     adequacy (Lemma 1B's `eval_rvalue` reduct) INSIDE the env update. The two
//     reducts are exactly `IH l2 (step e s)` — the induction hypothesis applied
//     at the STEPPED environment. So the step proof is `λ s rest ih l2 e.
//     ih l2 (step e s)`: it genuinely USES the IH at a different env, the
//     hallmark of a real induction (never `Eq.refl`).
//
// HONEST SCOPE (what the theorem covers vs. DEFERS).
// The `Function` fragment is the STRAIGHT-LINE SSA body the reflection's
// `extract_return_formula` consumes: a `List Stmt` of `Assign(idx, rvalue)` with
// `rvalue ∈ {Use, Bin(Add/Sub/Mul/Div)}` over scalar operands (`Var`/`Const`/
// `Move`), terminating in a return `Operand`. The refinement theorem is GENERAL
// over ALL such `(l1, l2, ret)` triples — it is the substitution/threading law
// for the whole straight-line fragment, by induction on the statement list.
// It DEFERS (does NOT claim): branches / `SwitchInt` (the guarded-cf return,
// `eval_ite`), loops (no multi-block fixpoint `exec`), and calls (no inter-
// procedural env) — those statement/terminator forms are simply not in the
// `Stmt`/`Operand`/`Rvalue` fragment the `Function` value ranges over, so the
// theorem says nothing false about them. This is the strongest tractable,
// genuinely-inductive refinement: a whole-STRAIGHT-LINE-body operational ≡
// substitution equality, kernel-proven modulo 3 — NOT a whole-program claim.
/// `appendStmt : List Stmt → List Stmt → List Stmt` — our own axiom-free list
/// concatenation over `Stmt`, pinned so the refinement theorem can talk about the
/// concatenated trace `l1 ++ l2` without depending on a prelude `List.append`.
/// Defined by `List.rec` on the first list (`nil ++ l2 = l2`, `(s::rest) ++ l2 =
/// s :: (rest ++ l2)`); `List.rec`/`List.cons`/`List.nil` are prelude inductive
/// machinery, so it carries no non-foundational axiom.
pub const MIRSEM_APPEND_STMT: &str = "Trust.MirSem.appendStmt";

/// `exec_threaded : Env → List Stmt → List Stmt → Operand → Int` — the OPERATIONAL
/// whole-body semantics: env-thread the concatenated trace `l1 ++ l2`, then read
/// the return under the final env. `eval (exec e (appendStmt l1 l2)) ret`.
pub const MIRSEM_EXEC_THREADED: &str = "Trust.MirSem.exec_threaded";

/// `denote_substituted : Env → List Stmt → List Stmt → Operand → Int` — the
/// REFLECTION's SUBSTITUTION whole-body semantics: thread the prefix `l1`, then
/// substitute the suffix `l2` on top, then read the return.
/// `eval (exec (exec e l1) l2) ret`. A DIFFERENT function from `exec_threaded`.
pub const MIRSEM_DENOTE_SUBST: &str = "Trust.MirSem.denote_substituted";

/// The ENV-LEVEL append/threading law `∀ l1 l2 e, exec (exec e l1) l2 =
/// exec e (l1 ++ l2)` — the inductive heart of the refinement (proven by
/// `List.rec` on `l1`).
pub const MIRSEM_EXEC_APPEND_LAW: &str = "Trust.MirSem.execAppendLaw";

/// The whole-function REFINEMENT theorem `∀ e l1 l2 ret, exec_threaded e l1 l2 ret
/// = denote_substituted e l1 l2 ret` — the faithfulness meta-theorem.
pub const MIRSEM_REFINEMENT: &str = "Trust.MirSem.refinement";

// ---- Step 6L (THE LOOP REFINEMENT) anchor: stepLoop + exec_loop + the
// fuel-indexed loop denotations + execLoopUnrollLaw + loopRefinement ----
//
// A bounded/structured `while cond { body }` (a back-edge / multi-block fixpoint)
// is the deepest remaining fragment. We do NOT host an unbounded fixpoint (that
// needs domain theory / a termination-or-invariant argument the CIC kernel cannot
// represent directly). Instead we model the loop FUEL-INDEXED: a `Nat` iteration
// count bounding the number of times the guarded body may re-run. The single
// guarded iteration is `stepLoop e := if eval_cond e cond then exec e body else e`
// (a `Bool.rec` over the guard); the whole loop is `stepLoop` iterated `fuel` times.
/// `stepLoop : Env → Cond → List Stmt → Env` — ONE guarded loop iteration:
/// `λ e cond body. @Bool.rec (λ_.Env) e (exec e body) (eval_cond e cond)`. The
/// guard is checked at the CURRENT env; on `false` the env is unchanged (the loop
/// would exit), on `true` the body is threaded once (`exec e body`). `Bool.rec`/
/// `eval_cond`/`exec` are prelude/Trust DEFINITIONS, so it carries no axiom.
pub const MIRSEM_STEP_LOOP: &str = "Trust.MirSem.stepLoop";

/// `exec_loop : Env → Cond → List Stmt → Nat → Env` — the OPERATIONAL fuel-indexed
/// loop, FRONT-PEELing the iteration count via `Nat.rec` at an `Env → Env` motive
/// (the same CPS/fold trick `exec` uses for `List`): `exec_loop e cond body 0 = e`,
/// `exec_loop e cond body (succ n) = exec_loop (stepLoop e cond body) cond body n`.
/// This recurses on a STEPPED env — the guarded body is applied at the front and
/// the remaining fuel folded over the result. Genuinely structural on `Nat`.
pub const MIRSEM_EXEC_LOOP: &str = "Trust.MirSem.exec_loop";

/// The fuel-indexed LOOP UNROLL law `∀ (fuel : Nat)(e : Env),
/// exec_loop (stepLoop e) fuel = stepLoop (exec_loop e fuel)` — front-peel iterate
/// equals outer-peel iterate of `stepLoop` (the classic `f (fⁿ x) = fⁿ (f x)`),
/// the inductive heart of the loop refinement, proven by `Nat.rec` on `fuel` (the
/// step USES the IH at the STEPPED env `stepLoop e` — a genuine induction, never
/// `Eq.refl`).
pub const MIRSEM_EXEC_LOOP_UNROLL_LAW: &str = "Trust.MirSem.execLoopUnrollLaw";

/// `loop_threaded : Env → Cond → List Stmt → Nat → Operand → Int` — the OPERATIONAL
/// whole-loop denotation: run `succ fuel` front-peeled guarded iterations, then read
/// the return under the final env. `eval (exec_loop e cond body (succ fuel)) ret`.
pub const MIRSEM_LOOP_THREADED: &str = "Trust.MirSem.loop_threaded";

/// `loop_substituted : Env → Cond → List Stmt → Nat → Operand → Int` — the
/// SUBSTITUTION whole-loop denotation: run `fuel` iterations, then SUBSTITUTE one
/// more guarded step (`stepLoop`) on top of that env, then read the return.
/// `eval (stepLoop (exec_loop e cond body fuel)) ret`. A DIFFERENT function from
/// `loop_threaded` (one recurses on `succ fuel`, the other applies `stepLoop`
/// OUTSIDE a `fuel`-iteration — not def-eq for a variable `fuel`).
pub const MIRSEM_LOOP_SUBST: &str = "Trust.MirSem.loop_substituted";

/// The whole-loop REFINEMENT theorem `∀ e cond body fuel ret,
/// loop_threaded e cond body fuel ret = loop_substituted e cond body fuel ret` —
/// the bounded/fuel-indexed loop faithfulness meta-theorem (`congrArg (eval · ret)`
/// over `execLoopUnrollLaw`).
pub const MIRSEM_LOOP_REFINEMENT: &str = "Trust.MirSem.loopRefinement";

// ---------------------------------------------------------------------------
// Step 6W — the UNBOUNDED-loop Hoare WHILE rule (PARTIAL correctness) and the
// inter-procedural CONTRACT-CALL rule (assume-the-callee). These are the two
// compositional Hoare-logic rules the fuel-indexed loop refinement LACKS: a
// genuine loop INVARIANT (a predicate `I` maintained for an ARBITRARY run
// length — NO termination claim) and an inter-procedural CALL (denoting the
// callee's postcondition, ASSUMING the callee is verified separately).
// ---------------------------------------------------------------------------
/// The guarded-step INVARIANT-PRESERVATION lemma
/// `∀ (I : Env → Prop)(cond : Cond)(body : List Stmt),
///   (∀ e, I e → eval_cond e cond = true → I (exec e body))
///   → ∀ e, I e → I (stepLoop e cond body)` — ONE guarded iteration preserves
/// the invariant `I`. The proof case-splits on the guard `eval_cond e cond :
/// Bool` (dependent `Bool.rec`): the FALSE arm leaves `e` unchanged so `I e`
/// carries through; the TRUE arm invokes the `preservation` hypothesis. This is
/// the heart of the Hoare while-rule (the invariant survives the guarded body).
pub const MIRSEM_STEP_PRESERVES_INV: &str = "Trust.MirSem.stepPreservesInv";

/// The UNBOUNDED-loop Hoare WHILE rule (PARTIAL correctness)
/// `∀ (I : Env → Prop)(cond : Cond)(body : List Stmt),
///   (∀ e, I e → eval_cond e cond = true → I (exec e body))   -- preservation
///   → ∀ (n : Nat)(e : Env), I e → I (exec_loop e cond body n)`.
/// The invariant `I` is maintained for an ARBITRARY iteration count `n` — proven
/// by genuine `Nat.rec` induction on `n` (base: `exec_loop e 0 ≡ e`; step: the IH
/// at the STEPPED env `stepLoop e`, fed `stepPreservesInv`). This is PARTIAL
/// correctness: it claims NOTHING about termination — only that IF the loop runs
/// `n` guarded steps, `I` still holds. `I` is a genuine `Prop` PARAMETER, so the
/// theorem is a real Hoare rule (`∀ I, preservation → …`), not a tautology.
pub const MIRSEM_LOOP_INVARIANT_RULE: &str = "Trust.MirSem.loopInvariantRule";

// ---- Step 6BRK (BREAK / EARLY-EXIT loops) anchor: a STRATIFIED, ADDITIVE
// break-able-loop layer parallel to `stepLoop`/`exec_loop`/`stepPreservesInv`/
// `loopInvariantRule`, whose effective guard is the COMBINED `cond ∧ ¬brk`.
//
// A loop that may exit early — `while cond { if brk { break } i = i+1 }` — runs the
// body ONLY while `cond` holds AND the break-condition `brk` does NOT. It therefore
// has TWO exit points: (a) the guard-FALSE exit (`cond` becomes false) and (b) the
// BREAK exit (`brk` becomes true mid-loop). The faithful model takes a guarded step
// exactly when the COMBINED guard `cond ∧ ¬brk` is true; at EITHER exit point the
// combined guard is false (`cond` false ⇒ false; `brk` true ⇒ `¬brk` false ⇒ false),
// so the SINGLE invariant theorem `loopInvariantRuleBrk` — the invariant survives an
// arbitrary number of combined-guarded steps — yields `I` at BOTH exits with one
// kernel proof. This is BYTE-IDENTICAL in structure to the base while-rule, just with
// the scrutinee `eval_cond e cond : Bool` replaced by `Bool.and (eval_cond e cond)
// (Bool.not (eval_cond e brk)) : Bool`; the generalised-guard `Bool.rec` case-split
// works on ANY `Bool` term, so the proof carries over verbatim. STRATIFIED (a NEW
// `*Brk` family) so `stepLoop`/`exec_loop`/`stepPreservesInv`/`loopInvariantRule`
// stay BYTE-IDENTICAL and every existing flat-loop certificate is unchanged.
/// The break-able guarded-step function `stepLoopBrk : Env → Cond → Cond → List Stmt
/// → Env` = `λ e cond brk body. if (eval_cond e cond ∧ ¬eval_cond e brk) then exec e
/// body else e`. The COMBINED guard `Bool.and (eval_cond e cond) (Bool.not (eval_cond
/// e brk))` selects the body ONLY when the loop guard holds AND the break-condition
/// does NOT; once EITHER fails the step is the identity (an exit/stable env). Carries
/// no non-foundational axiom (`Bool.rec`/`Bool.and`/`Bool.not`/`eval_cond`/`exec` are
/// prelude / MirSem definitions).
pub const MIRSEM_STEP_LOOP_BRK: &str = "Trust.MirSem.stepLoopBrk";

/// The break-able fuel-indexed loop `exec_loopBrk : Env → Cond → Cond → List Stmt →
/// Nat → Env`, the `exec_loop`-analogue over `stepLoopBrk` (front-peels via `Nat.rec`).
pub const MIRSEM_EXEC_LOOP_BRK: &str = "Trust.MirSem.exec_loopBrk";

/// The break-able guarded-step INVARIANT-PRESERVATION lemma `stepPreservesInvBrk`
/// `∀ (I : Env→Prop)(cond brk : Cond)(body : List Stmt),
///   (∀ e, I e → (eval_cond e cond ∧ ¬eval_cond e brk) = true → I (exec e body))
///   → ∀ e, I e → I (stepLoopBrk e cond brk body)` — ONE combined-guarded iteration
/// preserves `I`. Proof: the SAME generalised-guard `Bool.rec` case-split as
/// `stepPreservesInv`, scrutinising the COMBINED `Bool`. The FALSE arm (either exit)
/// leaves `e` unchanged so `I e` carries through; the TRUE arm invokes preservation.
pub const MIRSEM_STEP_PRESERVES_INV_BRK: &str = "Trust.MirSem.stepPreservesInvBrk";

/// The BREAK / EARLY-EXIT Hoare WHILE rule (PARTIAL correctness)
/// `∀ (I : Env→Prop)(cond brk : Cond)(body : List Stmt),
///   (∀ e, I e → (eval_cond e cond ∧ ¬eval_cond e brk) = true → I (exec e body))
///   → ∀ (n : Nat)(e : Env), I e → I (exec_loopBrk e cond brk body n)`.
/// The invariant `I` is maintained for an ARBITRARY combined-guarded iteration count
/// `n` — by genuine `Nat.rec` induction on `n` (front-peel + `stepPreservesInvBrk`).
/// Because the combined guard `cond ∧ ¬brk` is false at BOTH exit points (guard-false
/// AND break), THIS ONE theorem certifies `I` at EITHER exit env: `I (exec_loopBrk e
/// cond brk body n)` holds for the `n` at which the guard goes false OR the break
/// fires. `I`/`cond`/`brk` are genuine PARAMETERS — a WRONG invariant (not preserved
/// by the body under the combined guard, e.g. one the body violates before the break
/// fires) fails to supply preservation ⇒ the per-function instance is KernelRejected.
pub const MIRSEM_LOOP_INVARIANT_RULE_BRK: &str = "Trust.MirSem.loopInvariantRuleBrk";

/// The `Bool.and` LEFT-projection lemma `andLeftTrue : ∀ (a b : Bool), Bool.and a b =
/// true → a = true`. The break-loop preservation proof receives the COMBINED guard
/// `Bool.and (eval_cond e cond) (Bool.not (eval_cond e brk)) = true` and must extract
/// the loop-guard component `eval_cond e cond = true` (the synthesized invariant `i ≤
/// n` is re-established from the LOOP guard `i < n`, NOT the break-condition). Proven
/// by `Bool.rec` on `a`: the FALSE arm's domain `Bool.and false b = true` ι-reduces to
/// `false = true`, which IS the (`a := false`) codomain `a = true`, so the arm is the
/// identity `λ h. h`; the TRUE arm's codomain `true = true` is `Eq.refl`. No
/// `noConfusion` needed. Rests on ⊆ the 3 foundational axioms (`Bool.rec`/`Eq.refl`).
pub const MIRSEM_AND_LEFT_TRUE: &str = "Trust.MirSem.andLeftTrue";

// ---------------------------------------------------------------------------
// Step 6T — TOTAL correctness: the TERMINATION (well-founded RANKING) while-rule.
// `loopInvariantRule` is PARTIAL correctness (invariant survives `n` steps, NO
// halting claim). TOTAL correctness = partial + termination. The termination
// half is a well-founded RANKING argument: pin `R : Env → Nat`; if the rank
// STRICTLY DECREASES on every GUARDED iteration, then a strictly-decreasing
// `Nat` measure bottoms out — the guard MUST go false within `R e` iterations.
// We prove this by genuine strong/bounded induction on the rank (`Nat.rec` on a
// fuel bound `k` with the invariant `R e ≤ k`). `R` is a real `Env → Nat`
// PARAMETER, so the theorem is `∀ R, decrease → terminates` — the genuine rule.
// ---------------------------------------------------------------------------
/// `nat_le_trans : ∀ (a b c : Nat), Nat.le a b → Nat.le b c → Nat.le a c` — RAW
/// `Nat.le` transitivity, proven by `Nat.le.rec` on the SECOND premise (`Nat.le b
/// c`, params `b`, index `c`): the `refl` minor returns the first premise, the
/// `step` minor wraps the IH in `Nat.le.step`. Built locally (not the typeclass
/// `Nat.le_trans`) so the term stays in the RAW `Nat.le` shape `Nat.lt` unfolds
/// to, avoiding `LE.le`/`instLENat` unfolding friction. Rests on ⊆ the 3 axioms.
pub const MIRSEM_NAT_LE_TRANS: &str = "Trust.MirSem.nat_le_trans";

/// The guard-FALSE STABILITY lemma `∀ (cond : Cond)(body : List Stmt)(n : Nat)(e :
/// Env), eval_cond e cond = false → eval_cond (exec_loop e cond body n) cond =
/// false` — once the guard is false at `e`, it stays false for ANY fuel `n`
/// (`stepLoop` is idempotent at an exit env). Proven by `Nat.rec` on `n`, using
/// the generalised-guard `Bool.rec` trick to collapse `stepLoop e ≡ e` under the
/// false-guard hypothesis. The base of the termination argument's exit case.
pub const MIRSEM_GUARD_FALSE_STABLE: &str = "Trust.MirSem.guardFalseStable";

/// The BOUNDED-HALT lemma `∀ (R : Env→Nat)(cond)(body), decrease → ∀ (k : Nat)(e),
/// Nat.le (R e) k → eval_cond (exec_loop e cond body k) cond = false` — if the rank
/// is ≤ the fuel bound `k`, the loop has reached a guard-false (exit/stable) env by
/// fuel `k`. Proven by `Nat.rec` on `k`: base (`k=0`, so `R e ≤ 0`) the guard
/// CANNOT be true (else `decrease` gives `succ _ ≤ R e ≤ 0`, refuted by
/// `not_succ_le_zero`); step (`k=succ k'`) peels one guarded iteration — false ⇒
/// `guardFalseStable`; true ⇒ `decrease` + `nat_le_trans` + `le_of_succ_le_succ`
/// shrink the bound to `k'`, then the IH at the stepped env. The heart of the
/// well-founded descent.
pub const MIRSEM_BOUNDED_HALT: &str = "Trust.MirSem.boundedHalt";

/// The TOTAL-CORRECTNESS TERMINATION while-rule (well-founded RANKING)
/// `∀ (R : Env→Nat)(cond : Cond)(body : List Stmt),
///   (∀ e, eval_cond e cond = true → Nat.lt (R (exec e body)) (R e))   -- decrease
///   → ∀ e, eval_cond (exec_loop e cond body (R e)) cond = false`.
/// GIVEN the rank `R` STRICTLY DECREASES on every guarded iteration, the loop
/// HALTS within `R e` iterations — the guard is false at the env reached after
/// `R e` guarded steps (a stable / exit state). `= boundedHalt R … (R e) e
/// (Nat.le.refl (R e))` — instantiate the fuel bound at the rank itself. `R` is a
/// genuine `Env → Nat` PARAMETER (the theorem is `∀ R, decrease → terminates`), so
/// a NON-decreasing rank fails to supply `decrease` and the rule does not fire.
/// Combined with `loopInvariantRule` (partial) this is TOTAL correctness — and that
/// combination is now a SINGLE kernel-checked theorem `loopTotalCorrect` (below), the
/// `And` of this halting conclusion with the invariant-at-the-halting-state conclusion.
pub const MIRSEM_LOOP_RANK_TERMINATES: &str = "Trust.MirSem.loopRankTerminates";

/// The COMPOSED TOTAL-CORRECTNESS while-theorem `loopTotalCorrect`
/// `∀ (I : Env→Prop)(R : Env→Nat)(cond : Cond)(body : List Stmt),
///   (∀ e, I e → eval_cond e cond = true → I (exec e body))             -- preservation
///   → (∀ e, eval_cond e cond = true → Nat.lt (R (exec e body)) (R e))   -- decrease
///   → ∀ (e : Env), I e
///       → And (I (exec_loop e cond body (R e)))                         -- (a) PARTIAL: invariant
///             (eval_cond (exec_loop e cond body (R e)) cond = false)`.  -- (b) TERMINATION
/// TOTAL CORRECTNESS AS ONE THEOREM, not two lemmas: the conclusion is the GENUINE
/// CONJUNCTION (kernel `And` / `And.intro`) of (a) the invariant holding at the HALTING
/// state — `loopInvariantRule` instantiated at fuel `n := R e` — and (b) the loop
/// terminating within `R e` guarded steps — `loopRankTerminates` at the SAME `e`. Both
/// conjuncts share the fuel index `R e` (the rank of the start env), so the invariant is
/// asserted EXACTLY at the state the loop halts in. Proof: `And.intro A B
/// (loopInvariantRule I cond body pres (R e) e hI) (loopRankTerminates R cond body
/// decrease e)`. `I`/`R` are genuine PARAMETERS; DROPPING either conjunct-hypothesis
/// (`pres` or `decrease`) leaves `And.intro` unable to build its respective half, so the
/// theorem fails closed (kernel-rejected). Rests on ⊆ the 3 foundational axioms.
///
/// SHIPPED-WIRING HONESTY (applies to this rule AND to `loopInvariantRule`,
/// `loopRankTerminates`, `cfgRefinement`, `cfgRankTerminates`, and the call-transport
/// lemmas `callRefinesContract` / `openWorldCallRefines`): all of these are proven as
/// GENERAL ∀-quantified theorems and kernel-checked modulo 3, but they are NOT
/// instantiated per-compiled-function in the shipped `prove` pass. The shipped pass
/// instantiates ONLY straight-line refinement and single-branch refinement per function
/// (see `crates/trust-clean/src/prove.rs`). The loop/CFG/call theorems are available as a
/// verified meta-theory; do NOT claim they are wired per-function — they are not.
pub const MIRSEM_LOOP_TOTAL_CORRECT: &str = "Trust.MirSem.loopTotalCorrect";

/// The inter-procedural CALL inductive `Call : Type` with one constructor
/// `Call.mk (callee : Nat)(arg : Operand)(ret : Int) : Call`. `callee` names the
/// called function, `arg` is the argument operand, and `ret` is the value the
/// SEPARATELY-VERIFIED callee returns at the call site (modular verification — we
/// do NOT compute it here; it is the witness the callee's own proof supplies).
pub const MIRSEM_CALL: &str = "Trust.MirSem.Call";

pub const MIRSEM_CALL_MK: &str = "Trust.MirSem.Call.mk";

pub const MIRSEM_CALL_REC: &str = "Trust.MirSem.Call.rec";

/// `call_result : Call → Int` = `Call.rec (λ callee arg ret. ret)` — the call
/// site's DENOTATION: the value flowing out of the call (the callee's contractual
/// return). A genuine recursor projection, NOT a bare identity.
pub const MIRSEM_CALL_RESULT: &str = "Trust.MirSem.call_result";

/// `call_callee : Call → Nat` = `Call.rec (λ callee arg ret. callee)` — the call
/// site's CALLEE-ID projection (which mutually-recursive function is named). A
/// genuine recursor projection of the first field. Used by the mutual-recursion
/// contract rule to look up the called function's contract.
pub const MIRSEM_CALL_CALLEE: &str = "Trust.MirSem.call_callee";

/// The DEPTH-BOUNDED mutual-contract lemma `∀ (Post : Nat→Int→Prop)(rank :
/// Call→Nat)(step), ∀ (k : Nat)(c : Call), Nat.le (rank c) k → Post (call_callee
/// c) (call_result c)` — if a call's rank is ≤ the budget `k`, its callee's
/// contract holds at its result. Proven by `Nat.rec` on `k`, feeding `step` an
/// inner hypothesis that every STRICTLY-SMALLER-rank call already satisfies its
/// contract (`nat_le_trans` + `le_of_succ_le_succ`/`not_succ_le_zero`). The
/// well-founded heart of mutual-contract composition.
pub const MIRSEM_BOUNDED_SAT: &str = "Trust.MirSem.boundedSat";

/// The MUTUAL-RECURSION CONTRACT rule (assume-the-callees, well-founded over a
/// call-RANKING) `∀ (Post : Nat→Int→Prop)(rank : Call→Nat),
///   (∀ (c : Call),
///       (∀ (c' : Call), Nat.lt (rank c') (rank c) → Post (call_callee c') (call_result c'))
///       → Post (call_callee c) (call_result c))                    -- the mutual STEP
///   → ∀ (c : Call), Post (call_callee c) (call_result c)`.
/// READ PRECISELY: `Post i` is the contract of mutually-recursive callee `i`. The
/// STEP hypothesis is ASSUME-the-callees, modularly AND well-foundedly: callee
/// `call_callee c`'s contract holds at `c`, GIVEN every call `c'` of STRICTLY
/// SMALLER rank already satisfies ITS callee's contract. The CONCLUSION composes
/// the contracts over the whole (mutually-recursive) call graph: EVERY call
/// satisfies its callee's contract. Proven by strong/well-founded induction on the
/// rank (`= boundedSat … (rank c) c (Nat.le.refl (rank c))`). `Post`/`rank`/`step`
/// are all genuine PARAMETERS, so a WRONG contract fails to inhabit it. Does NOT
/// discharge any callee body — it composes the assumed per-callee steps.
pub const MIRSEM_MUTUAL_CALL_CONTRACTS: &str = "Trust.MirSem.mutualCallContracts";

/// The CONTRACT-CALL TRANSPORT lemma (modular ASSUME-GUARANTEE, inter-procedural)
/// `∀ (post : Int → Prop)(c : Call), post (call_result c) → post (call_result c)`.
/// HONEST LABEL: this is a TRANSPORT lemma, NOT a dispatch theorem. Its proof is the
/// IDENTITY (`λ post c h. h`, an A-implies-A): it TRANSPORTS an ASSUMED callee
/// contract `post (call_result c)` to the call site. READ PRECISELY: the HYPOTHESIS
/// `post (call_result c)` is the GUARANTEE — the ASSUMPTION that the callee satisfies
/// its contract at this call's result. The real work — DISCHARGING that the callee's
/// BODY actually satisfies `post` — is NOT done by this rule; it is done elsewhere
/// (the callee is verified SEPARATELY — modular verification) and is NOT proven here.
/// The CONCLUSION simply re-states that the call SITE's denotation (`call_result c`)
/// satisfies the SAME `post`. This rule proves NOTHING about dispatch and does NOT
/// discharge the callee body. `post` is a genuine `Prop`-valued PARAMETER, so a WRONG
/// postcondition (a different predicate) fails to inhabit the transport — fail-closed.
pub const MIRSEM_CALL_REFINES_CONTRACT: &str = "Trust.MirSem.callRefinesContract";

/// Trust: call-spine increment — the PER-CALL-SITE instance of
/// [`MIRSEM_CALL_REFINES_CONTRACT`]: the general transport lemma APPLIED at the
/// concrete `Call.mk <callee-id> <arg> ret` value of a recognized call return
/// (∀-quantified over the callee-supplied `ret` and the contract `post`). The
/// proof term is an APPLICATION of the registered proven theorem — never a new
/// axiom. See [`call_return_adequacy_witness`].
pub const MIRSEM_CALL_RETURN_INSTANCE: &str = "Trust.MirSem.callReturnInstance";

/// Trust: CALL-THEN-PUREOP — the PER-CALL-SITE instance of
/// [`MIRSEM_CALL_REFINES_CONTRACT`] APPLIED at a WRAPPED predicate (`λx. post
/// (wrap x)`), so the transported fact is about `wrap(call_result C[ret])` —
/// the pure op over the call's opaque result — rather than the bare result
/// itself. Still a plain APPLICATION of the SAME registered proven theorem
/// [`MIRSEM_CALL_RETURN_INSTANCE`] uses — never a new axiom. See
/// [`call_then_pureop_adequacy_witness`].
pub const MIRSEM_CALL_THEN_PUREOP_INSTANCE: &str = "Trust.MirSem.callThenPureOpInstance";

/// Trust: CALL-OP-CALL — the PER-CALL-PAIR instance transporting BOTH calls'
/// opaque results through TWO NESTED applications of the SAME registered proven
/// [`MIRSEM_CALL_REFINES_CONTRACT`] theorem (one per call), composing to a
/// single WRAPPED predicate `λ a b. post (wrap a b)` — never a new axiom. See
/// [`call_op_call_adequacy_witness`].
pub const MIRSEM_CALL_OP_CALL_INSTANCE: &str = "Trust.MirSem.callOpCallInstance";

/// Trust: CALL-RESULT-AWARE COMPOSITION — the PER-CALL-SITE instance of
/// [`MIRSEM_CALL_REFINES_CONTRACT`] APPLIED at the BIGGER WRAPPED predicate
/// the 4-hop chain composes (a `Cast` identity + checked-arith Mul + the outer
/// pure op — see [`call_chain_pureop_instance_verdict`]'s doc). Still a plain
/// APPLICATION of the SAME registered proven theorem [`MIRSEM_CALL_RETURN_
/// INSTANCE`] uses — never a new axiom. See [`call_chain_pureop_adequacy_
/// witness`].
pub const MIRSEM_CALL_CHAIN_PUREOP_INSTANCE: &str = "Trust.MirSem.callChainPureOpInstance";

/// Trust: CALL-THEN-PROJECT — the PER-CALL-SITE instance of
/// [`MIRSEM_CALL_REFINES_CONTRACT`] APPLIED at the FIELD-PROJECTION wrapped
/// predicate (`λx. post (idx_elem x i)`), so the transported fact is about the
/// `i`-th component `idx_elem(call_result C[ret], i)` of the callee's TUPLE
/// result rather than the bare (whole-tuple-handle) result itself. Still a plain
/// APPLICATION of the SAME registered proven theorem
/// [`MIRSEM_CALL_RETURN_INSTANCE`] uses — never a new axiom (the `idx_elem`
/// opaque total selector is the EXACT carrier `SemOperand::Field` already
/// denotes through). See [`call_then_project_adequacy_witness`].
pub const MIRSEM_CALL_THEN_PROJECT_INSTANCE: &str = "Trust.MirSem.callThenProjectInstance";

// ---------------------------------------------------------------------------
// Step 6U — the UNSTRUCTURED / IRREDUCIBLE CFG refinement. The structured loop
// (`exec_loop`/`stepLoop`) assumes a `while cond { body }` shape — a SINGLE
// back-edge under a guard. A general MIR CFG is an arbitrary basic-block graph:
// each block ends in a terminator (`goto target` | `switch cond targets` |
// `return`) and edges may form IRREDUCIBLE patterns (e.g. two entries into a
// loop, back-edges that are not a structured `while`). We model the CFG as a
// transition function `next : Nat → Env → CfgState` (current block index + env
// ↦ the successor state the terminator selects) and a fuel-indexed `exec_cfg`
// that follows terminator EDGES block-to-block — NOT assuming reducibility. The
// refinement (`execCfgUnrollLaw`) is the general transition-system version of
// the structured-loop unroll, by `Nat.rec` on FUEL. It subsumes the structured
// loop as the special case where `next` implements `stepLoop`.
// ---------------------------------------------------------------------------
/// The CFG-STATE inductive `CfgState : Type` with one constructor
/// `CfgState.mk (pc : Nat)(env : Env) : CfgState` — the abstract machine state of
/// a running CFG: `pc` is the CURRENT basic-block index (the program counter) and
/// `env` is the parameter binding. A `return` terminator is modeled by `next`
/// routing to a designated halt block whose `next` is the identity (idempotent),
/// the transition-system analogue of the guard-false exit env.
pub const MIRSEM_CFG_STATE: &str = "Trust.MirSem.CfgState";

pub const MIRSEM_CFG_STATE_MK: &str = "Trust.MirSem.CfgState.mk";

pub const MIRSEM_CFG_STATE_REC: &str = "Trust.MirSem.CfgState.rec";

/// `cfg_pc : CfgState → Nat` = `CfgState.rec (λ pc env. pc)` — the program-counter
/// projection (which basic block the machine is currently in). A genuine recursor
/// projection of the first field.
pub const MIRSEM_CFG_PC: &str = "Trust.MirSem.cfg_pc";

/// `cfg_env : CfgState → Env` = `CfgState.rec (λ pc env. env)` — the env projection
/// (the parameter binding at the current state). A genuine recursor projection.
pub const MIRSEM_CFG_ENV: &str = "Trust.MirSem.cfg_env";

/// `step_cfg : (Nat → Env → CfgState) → CfgState → CfgState` — ONE terminator-edge
/// step: `λ next s. next (cfg_pc s) (cfg_env s)`. `next` is the CFG's transition
/// function (block index + env ↦ the successor state the block's terminator selects:
/// `goto t` ↦ `CfgState.mk t env`; `switch` ↦ the env-selected target; `return` ↦ a
/// halt state). `next` is an ARBITRARY function PARAMETER, so this models arbitrary
/// edges — including irreducible back-edges — NOT a structured `while`.
pub const MIRSEM_STEP_CFG: &str = "Trust.MirSem.step_cfg";

/// `exec_cfg : (Nat → Env → CfgState) → Nat → CfgState → CfgState` — the OPERATIONAL
/// fuel-indexed CFG run, FRONT-PEELing the fuel via `Nat.rec` at a `CfgState →
/// CfgState` motive (the same fold `exec_loop` uses): `exec_cfg next 0 s = s`,
/// `exec_cfg next (succ n) s = exec_cfg next n (step_cfg next s)`. Steps block-to-block
/// by following the terminator `next` for a BOUNDED run of `n` steps over ANY CFG.
pub const MIRSEM_EXEC_CFG: &str = "Trust.MirSem.exec_cfg";

/// The fuel-indexed CFG UNROLL law `∀ (next : Nat → Env → CfgState)(fuel : Nat)(s :
/// CfgState), exec_cfg next fuel (step_cfg next s) = step_cfg next (exec_cfg next fuel s)`
/// — front-peel iterate equals outer-peel iterate of `step_cfg` (the classic
/// `f (fⁿ x) = fⁿ (f x)` for the CFG transition `f = step_cfg next`), proven by
/// genuine `Nat.rec` on `fuel` (the step USES the IH at the STEPPED state
/// `step_cfg next s` — a real induction, never `Eq.refl`). The general
/// transition-system version of `execLoopUnrollLaw`, holding for ARBITRARY (incl.
/// irreducible) `next`.
pub const MIRSEM_EXEC_CFG_UNROLL_LAW: &str = "Trust.MirSem.execCfgUnrollLaw";

/// `cfg_threaded : (Nat → Env → CfgState) → Nat → CfgState → CfgState` — the
/// OPERATIONAL whole-CFG denotation: run `succ fuel` front-peeled terminator steps.
/// `exec_cfg next (succ fuel) s`.
pub const MIRSEM_CFG_THREADED: &str = "Trust.MirSem.cfg_threaded";

/// `cfg_substituted : (Nat → Env → CfgState) → Nat → CfgState → CfgState` — the
/// SUBSTITUTION whole-CFG denotation: run `fuel` steps, then `step_cfg` ONE more on
/// top. `step_cfg next (exec_cfg next fuel s)`. A DIFFERENT function from
/// `cfg_threaded` (one recurses on `succ fuel`, the other applies `step_cfg` OUTSIDE
/// a `fuel`-iteration — not def-eq for a variable `fuel`).
pub const MIRSEM_CFG_SUBST: &str = "Trust.MirSem.cfg_substituted";

/// The whole-CFG REFINEMENT theorem `∀ next fuel s,
/// cfg_threaded next fuel s = cfg_substituted next fuel s` — the bounded/fuel-indexed
/// UNSTRUCTURED-CFG faithfulness meta-theorem (`execCfgUnrollLaw` applied; both
/// denotations are `exec_cfg`/`step_cfg` of the state, equated by the unroll law).
/// Covers arbitrary terminator edges (incl. irreducible back-edges) for a bounded
/// run. SUBSUMES the structured loop refinement as the special case `next = stepLoop`.
/// HONEST SCOPE: this is the BOUNDED (fuel-indexed) unstructured run; the UNBOUNDED
/// irreducible loop additionally needs a RANKING on the CFG state — supplied by
/// `cfgRankTerminates` below (the well-founded CFG-state descent), NOT here.
pub const MIRSEM_CFG_REFINEMENT: &str = "Trust.MirSem.cfgRefinement";

// ---------------------------------------------------------------------------
// Step 6X — the UNBOUNDED irreducible-CFG TERMINATION rule via a CFG-STATE
// RANKING. `cfgRefinement` proves the BOUNDED (fuel-indexed) unstructured run is
// faithful; it says NOTHING about whether the run halts. The UNBOUNDED irreducible
// CFG terminates exactly when it carries a RANKING `R : CfgState → Nat` that
// strictly DROPS on every terminator step until an exit/stable state. We compose
// the well-founded Nat descent (the `loopRankTerminates` pattern) with `CfgState`
// /`step_cfg`/`exec_cfg`: GIVEN the rank strictly decreases each step until exit,
// the CFG run reaches an exit state within `R s` steps. The exit states are
// fixpoints of `step_cfg` (a `return`/sink terminator), supplied as the `stable`
// hypothesis — sound and load-bearing, mirroring the loop's built-in idempotence
// at a false guard. This UPGRADES the bounded CFG refinement to TOTAL correctness
// for an UNBOUNDED irreducible CFG that has a ranking. A CFG with NO ranking
// (genuine non-termination / the halting problem) stays fail-closed — INHERENT.
// ---------------------------------------------------------------------------
/// The CFG-STATE EXIT-STABILITY lemma `∀ (at_exit : CfgState→Bool)(next),
///   (∀ s, at_exit s = true → step_cfg next s = s)            -- exit states are fixpoints
///   → ∀ (k : Nat)(s : CfgState), at_exit s = true
///       → at_exit (exec_cfg next k s) = true`. Once at an exit/stable state, the run
/// stays at exit for any further fuel — the CFG analog of `guardFalseStable` (where
/// the loop's `stepLoop` is idempotent at a false guard; here exit-fixity is the
/// `stable` hypothesis). Proven by `Nat.rec` on `k`, transporting the goal along
/// `step_cfg next s = s` via `Eq.rec`.
pub const MIRSEM_CFG_EXIT_STABLE: &str = "Trust.MirSem.cfgExitStable";

/// The CFG BOUNDED-HALT lemma `∀ (R : CfgState→Nat)(at_exit)(next),
///   (∀ s, at_exit s = true → step_cfg next s = s)                       -- stable
///   → (∀ s, at_exit s = false → Nat.lt (R (step_cfg next s)) (R s))     -- decrease
///   → ∀ (k : Nat)(s : CfgState), Nat.le (R s) k
///       → at_exit (exec_cfg next k s) = true`. Well-founded descent on the fuel
/// bound `k` (the CFG analog of `boundedHalt`): the Bool.rec on `at_exit s` splits
/// into the still-running arm (`= false`, decrease + IH on the stepped state) and
/// the halted arm (`= true`, `cfgExitStable`).
pub const MIRSEM_CFG_BOUNDED_HALT: &str = "Trust.MirSem.cfgBoundedHalt";

/// The UNBOUNDED irreducible-CFG TOTAL-CORRECTNESS TERMINATION rule via a CFG-state
/// RANKING `∀ (R : CfgState→Nat)(at_exit : CfgState→Bool)(next : Nat→Env→CfgState),
///   (∀ s, at_exit s = true → step_cfg next s = s)                       -- stable
///   → (∀ s, at_exit s = false → Nat.lt (R (step_cfg next s)) (R s))     -- decrease
///   → ∀ (s : CfgState), at_exit (exec_cfg next (R s) s) = true`.
/// READ PRECISELY: GIVEN a ranking `R` that strictly DROPS on every terminator step
/// until exit (and the exit states are step-fixpoints), the UNBOUNDED irreducible CFG
/// run reaches an EXIT/STABLE state within `R s` steps. `R` is a genuine
/// `CfgState → Nat` PARAMETER (quantified), so a NON-DECREASING rank (e.g. `λ_.0`)
/// fails to inhabit the conclusion — fail-closed. This is the total-correctness
/// upgrade of `cfgRefinement`: the bounded run is faithful (cfgRefinement) AND it
/// halts within `R s` steps (cfgRankTerminates). A CFG with NO ranking (genuine
/// non-termination — the halting problem) stays INHERENTLY fail-closed.
pub const MIRSEM_CFG_RANK_TERMINATES: &str = "Trust.MirSem.cfgRankTerminates";

// ---------------------------------------------------------------------------
// Step 6H — the HIGHER-ORDER (INDIRECT) call rule. The first-order contract-call
// (`callRefinesContract`) and mutual-recursion rule (`mutualCallContracts`) both
// name a STATICALLY-KNOWN callee. A higher-order call dispatches through a
// function VALUE (fn pointer / dyn dispatch) whose target is drawn from a known
// FINITE set of candidates (the devirtualization set), each with its OWN contract.
// We model the candidate set as indices into a per-candidate contract family
// `Post : Nat → Int → Prop`, an actual `target`, and the indirect-call result.
// GIVEN each candidate satisfies its contract, the indirect call refines to the
// RESOLVED candidate's postcondition — by instantiating the per-candidate
// hypothesis at the resolved target (the candidate case-split). For the
// two-candidate disjunction form, the case-split is an explicit `Or.rec` on which
// candidate the target resolved to. MODULAR: assume-the-candidates; a target with
// no membership witness in the finite set has no case to land in, so the rule
// cannot fire (closed-world / finite-candidate — open-world dispatch deferred).
// ---------------------------------------------------------------------------
/// The HIGHER-ORDER (indirect) CALL inductive `HoCall : Type` with one constructor
/// `HoCall.mk (target : Nat)(arg : Operand)(ret : Int) : HoCall`. `target` is the
/// resolved candidate INDEX (which function VALUE the fn-pointer/dyn dispatch landed
/// on — devirtualized to a known candidate), `arg` the argument, `ret` the value the
/// SEPARATELY-VERIFIED resolved candidate returns. Distinct from `Call`: the callee is
/// a function VALUE resolved against a finite candidate set, not a statically-fixed id.
pub const MIRSEM_HO_CALL: &str = "Trust.MirSem.HoCall";

pub const MIRSEM_HO_CALL_MK: &str = "Trust.MirSem.HoCall.mk";

pub const MIRSEM_HO_CALL_REC: &str = "Trust.MirSem.HoCall.rec";

/// `ho_target : HoCall → Nat` = `HoCall.rec (λ target arg ret. target)` — the resolved
/// candidate-INDEX projection (which function value the indirect call dispatched to).
pub const MIRSEM_HO_TARGET: &str = "Trust.MirSem.ho_target";

/// `ho_result : HoCall → Int` = `HoCall.rec (λ target arg ret. ret)` — the indirect
/// call's DENOTATION: the value the resolved candidate contractually returns.
pub const MIRSEM_HO_RESULT: &str = "Trust.MirSem.ho_result";

/// The HIGHER-ORDER CALL rule (devirtualized over a FINITE candidate set, by
/// CASE-SPLIT on the resolved target) `∀ (Post : Nat → Int → Prop)(c : HoCall),
///   (∀ (i : Nat), Post i (ho_result c))   -- assume EVERY candidate's contract
///   → Post (ho_target c) (ho_result c)`.  -- resolve to the ACTUAL candidate's.
/// READ PRECISELY: the HYPOTHESIS is the devirtualization set — EVERY candidate `i`
/// satisfies its own contract `Post i` at this call's result (each verified
/// SEPARATELY, modular). The CONCLUSION resolves to the ACTUAL target's contract
/// `Post (ho_target c)` — by instantiating the per-candidate hypothesis at the
/// resolved index. `Post` is a genuine `Nat → Int → Prop` family PARAMETER and the
/// conclusion names the RESOLVED target, so a WRONG candidate / a contract for a
/// DIFFERENT index fails to inhabit. (Closed-world; open-world dispatch deferred.)
pub const MIRSEM_HIGHER_ORDER_CALL: &str = "Trust.MirSem.higherOrderCallRefines";

/// The DISJUNCTION form of the higher-order call rule over a TWO-candidate set (the
/// devirtualization set `{0,1}`, the smallest non-trivial finite set that forces a
/// genuine CASE-SPLIT) `∀ (P0 P1 : Int → Prop)(c : HoCall),
///   (Or (Eq Nat (ho_target c) 0) (Eq Nat (ho_target c) 1))  -- target is ONE of the candidates
///   → (P0 (ho_result c)) → (P1 (ho_result c))               -- each candidate's contract
///   → Or (P0 (ho_result c)) (P1 (ho_result c))`.            -- the disjunction of postconditions
/// READ PRECISELY: GIVEN the target is one of the two candidates AND each candidate
/// satisfies its contract, the indirect call refines to the DISJUNCTION of the two
/// candidate postconditions — proven by `Or.rec` CASE-SPLIT on which candidate the
/// target resolved to (the resolved branch supplies its `Or.inl`/`Or.inr` injection).
/// A target proven OUTSIDE `{0,1}` cannot supply the membership hypothesis, so the rule
/// does not fire — the finite-candidate (closed-world) discipline. `P0`/`P1` are genuine
/// `Int → Prop` PARAMETERS, so a wrong candidate set fails the membership case-split.
pub const MIRSEM_HIGHER_ORDER_CALL_DISJ: &str = "Trust.MirSem.higherOrderCallDisjunction";

// ---------------------------------------------------------------------------
// Step 6O — the ASSUME-THE-TRAIT-CONTRACT TRANSPORT lemma for a `dyn Trait` call.
// HONEST LABEL (do NOT claim Liskov / behavioral-subtyping / open-world dispatch):
// this is a TRANSPORT lemma whose proof is essentially the identity. The
// finite-candidate rules above (`higherOrderCallRefines` / `higherOrderCallDisjunction`)
// resolve a dyn call against a CLOSED, KNOWN set of candidates by a GENUINE case-split
// on `ho_target`. This rule does NO case-split that matters: it ASSUMES the trait
// method's postcondition `TPost` holds (as a `∀ impl, TPost (ho_result c)` hypothesis),
// then TRANSPORTS that assumption to the call site. CRITICAL HONESTY NOTE: `ho_result c`
// does NOT depend on the implementor index `impl`, so the conclusion is INDEPENDENT of
// which implementor the dispatch lands on — the proof `h (ho_target c)` is a plain
// ∀-elimination at an index the result ignores. It therefore does NOT prove a genuine
// behavioral-subtyping / over-all-implementors dispatch theorem; it merely assumes the
// trait contract and re-states it. The real work — that every implementor's BODY
// actually satisfies `TPost` — is verified SEPARATELY and is NOT proven here.
// HONEST SCOPE: this needs a DECLARED trait contract `TPost`; a trait method with NO
// declared contract has nothing to assume (INHERENTLY fail-closed — no postcondition to
// transport). To upgrade this to a real dispatch theorem one would have to make
// `ho_result` (or the contract) depend on the dispatched target and prove a genuine
// case-split — which this lemma does NOT do.
// ---------------------------------------------------------------------------
/// The ASSUME-THE-TRAIT-CONTRACT TRANSPORT lemma for a `dyn Trait` call
/// `∀ (TPost : Int → Prop)(c : HoCall),
///   (∀ (impl : Nat), TPost (ho_result c))   -- ASSUME the trait postcondition holds
///   → TPost (ho_result c)`.                  -- transport it to the call site.
/// HONEST LABEL (this is NOT a Liskov / behavioral-subtyping / over-all-implementors
/// dispatch theorem): the proof is `λ TPost c h. h (ho_target c)`, a plain
/// ∀-elimination. CRITICAL: `ho_result c` does NOT depend on the implementor index
/// `impl`, so the `∀ impl` in the hypothesis ranges over an index the result IGNORES;
/// instantiating it at `ho_target c` (or at any index) yields the SAME `TPost
/// (ho_result c)`. The conclusion is therefore INDEPENDENT of the dispatched
/// implementor — the lemma TRANSPORTS an ASSUMED trait contract `TPost` to the call
/// site, and proves NOTHING about which implementor was dispatched. It does NOT do a
/// genuine case-split and does NOT establish behavioral subtyping. The real work —
/// that every implementor's BODY satisfies `TPost` — is verified SEPARATELY and is NOT
/// proven here. `TPost` is a genuine `Int → Prop` PARAMETER, so a wrong `TPost` the
/// hypothesis does not establish fails to inhabit the transport — fail-closed. A trait
/// method with NO declared contract has no `TPost` to assume (INHERENTLY deferred).
pub const MIRSEM_OPEN_WORLD_CALL: &str = "Trust.MirSem.openWorldCallRefines";

/// Verdict of checking the refinement theorem (general, or instantiated at a
/// function). `ProvenModulo3` ⇒ kernel-checked resting on exactly the 3
/// foundational axioms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefinementVerdict {
    /// PROVEN modulo 3: the refinement (`exec_threaded = denote_substituted`)
    /// kernel-checks and its axiom closure is ⊆ the 3 foundational axioms.
    ProvenModulo3,
    /// Type-checks, but rests on these non-foundational axioms.
    Residue(Vec<String>),
    /// Kernel-rejected — NOT proven (the fail-closed outcome for a wrong claim).
    KernelRejected(String),
}

/// A kernel-checked REFINEMENT certificate for a whole straight-line function: the
/// function's modeled `(stmts, ret)` witness plus the modulo-3 verdict for the
/// INSTANTIATED refinement theorem `exec_threaded e stmts [] ret =
/// denote_substituted e stmts [] ret`. Because this is the GENERAL meta-theorem
/// instantiated at the function's `MirSem.Function` value, the per-function
/// end-to-end adequacy is a COROLLARY of the meta-theorem, not a separately-built
/// proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefinementCertificate {
    /// The straight-line return witness (`stmts` + `ret`) this certifies.
    pub function: SemReturn,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl RefinementCertificate {
    /// Whether this certificate is a genuine modulo-3 refinement proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Step 6B — THE BRANCH REFINEMENT: refinementB (the guarded single-branch return,
// connected to the LIVE grounder), modulo 3.
// ===========================================================================
//
// THE GAP THIS CLOSES (the branch-scaffold gap the audit flagged).
// Step 6's `refinement` covers the STRAIGHT-LINE fragment; a guarded return was NOT
// connected at all, because `clean_ground::extract_return_formula` returned `None` for
// guarded returns — so there was no live-grounded term to connect the branch
// denotation TO. With `extract_return_formula` now reflecting a guarded return as a
// `Formula::Ite` (and `ground_int` grounding `Ite` to the `Bool.rec` if-then-else),
// the branch denotation `denote_substitutedB` (= `eval_ite`, the conditional eval the
// guarded control-flow return folds) can be connected to the LIVE grounder by the same
// grounder-connected discipline as Lemmas 1A/1B.
//
// THE BRANCH REFINEMENT (kernel-proven, modulo 3).
//   refinementB : ∀ (x⃗ : Int), denote_substitutedB E c t f = ground_int(Ite(cond,t,f))
// where `E` is the `set`-chain grounding env (each referenced parameter bound to its
// de-Bruijn `Int` binder), `c`/`t`/`f` are the closed guard/arm constructor values, and
// the RHS is the term the LIVE `clean_ground::ground_int` grounds the guarded return's
// `Formula::Ite` to. `denote_substitutedB E c t f` ι/δ-reduces (through `eval_ite` →
// `Bool.rec`, `eval_cond` → the grounded `decide`/`Int.beq` Bool, each `eval_rvalue` →
// the grounded arm) to EXACTLY `ground_int(Ite(...))`, so reflexivity at the
// live-grounded term inhabits the equality. The branch refinement therefore links to
// the LIVE pipeline — not a hand-built shape.
//
// HONEST SCOPE. This connects the SINGLE-BRANCH guarded return (one `SwitchInt` over a
// comparison, two converging arms of modeled scalar rvalues) — the exact shape
// `sem_cf_return_of_mir` / `guarded_return_formula` model. Nested/multi-condition
// guards (≥2 SwitchInts), loops, and calls remain DEFERRED (not in the modeled branch
// fragment), never falsely claimed.
/// `denote_substitutedB : Env → Cond → Rvalue → Rvalue → Int` — the branch
/// SUBSTITUTION denotation: the conditional eval the guarded control-flow return folds,
/// `λ e c t f. eval_ite e c t f`. The branch analogue of `denote_substituted` for the
/// straight-line fragment.
pub const MIRSEM_DENOTE_SUBST_B: &str = "Trust.MirSem.denote_substitutedB";

/// The branch REFINEMENT theorem name (per-instance; the general form is the
/// reflexivity-after-reduction connection of `denote_substitutedB` to the
/// live-grounded `Ite`).
pub const MIRSEM_REFINEMENT_B: &str = "Trust.MirSem.refinementB";

/// A kernel-checked BRANCH REFINEMENT certificate for a guarded single-branch return:
/// the guarded return witness plus the modulo-3 verdict for `refinementB`
/// (`denote_substitutedB` ≡ the live-grounded `Ite`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchRefinementCertificate {
    /// The guarded control-flow return witness this certifies.
    pub ret: SemCfReturn,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl BranchRefinementCertificate {
    /// Whether this certificate is a genuine modulo-3 branch refinement proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

/// A kernel-checked NESTED-BRANCH REFINEMENT certificate for a multi-way guarded
/// return: the recursive `SemBranchTree` witness plus the modulo-3 verdict for
/// `refinementBNested` (the `iteI`-tree denotation ≡ the live-grounded nested `Ite`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedBranchRefinementCertificate {
    /// The nested guarded-return witness this certifies.
    pub tree: SemBranchTree,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl NestedBranchRefinementCertificate {
    /// Whether this certificate is a genuine modulo-3 nested-branch refinement proof.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Step 6LF — PER-FUNCTION LOOP INSTANTIATION (closing the standalone-vs-wired gap).
//
// `loopInvariantRule` / `loopRankTerminates` / `loopTotalCorrect` above are GENERAL
// ∀-quantified theorems, kernel-checked modulo 3, but NOT instantiated at any
// concrete compiled function. This step INSTANTIATES the partial-correctness Hoare
// while-rule (`loopInvariantRule`) at ONE real loop function's concrete
// `(I, cond, body)`: it supplies a CONCRETE invariant `I`, a CONCRETE guard `cond`
// and body `body` built from the function's MIR loop, and a CONCRETE preservation
// PROOF, then kernel-checks the resulting per-function partial-correctness instance
// `∀ n e, I e → I (exec_loop e cond body n)` modulo 3, emitting a
// `LoopRefinementCertificate`.
//
// HONESTY (critical): this is a PROOF-OF-CONCEPT that the loop rule INSTANTIATES
// per-function with a PROVIDED / trivially-derived invariant. It is NOT general loop
// verification, which needs invariant INFERENCE (explicitly DEFERRED). The provided
// invariant here is the "untouched-local" class: `I := λ e. e[r] = c` for a local
// `r` the loop body NEVER assigns. Its preservation is then DEFINITIONAL — `exec e
// body` ι-reduces (through `exec`/`set`) to a `set`-chain that leaves index `r`
// untouched (each `set e iₖ vₖ r` ι-reduces to `e r` because `Nat.beq iₖ r`
// native-reduces to `false` for distinct literal indices), so `I (exec e body)` is
// def-eq to `I e` and preservation is `λ e hI _guard. hI`. This is a SOUND, genuine
// loop-carried invariant (the local `r` retains its entry value `c` across EVERY
// iteration because the loop never writes it), and a postcondition `ret = c` (return
// the untouched local) is a real COROLLARY of the kernel-checked per-function
// instance. A WRONG invariant — one the body does NOT preserve (it assigns the
// claimed local) — makes the def-eq preservation proof ill-typed ⇒ KernelRejected
// (fail-closed). What this does NOT do: infer invariants for arbitrary loops, prove
// arithmetic-decrease termination per function (the ranking decrease proof needs
// linear-arithmetic reasoning over the env values, DEFERRED), or claim general loop
// verification.
// ===========================================================================
/// A CONCRETE loop function to instantiate the Hoare while-rule at: the structured
/// `while cond { body }` extracted from the function's MIR loop, plus the PROVIDED
/// "untouched-local" invariant `I := λ e. e[inv_local] = inv_const`.
///
/// `cond` is the loop guard (the back-edge's `SwitchInt`-over-comparison
/// discriminant); `body` is the ordered SSA assignment trace of the loop body (one
/// `Assign(idx, rvalue)` per statement). `inv_local`/`inv_const` name the invariant:
/// local `inv_local` equals the constant `inv_const` at loop entry AND is NEVER
/// assigned by `body` — so the invariant is preserved DEFINITIONALLY. The certificate
/// is sound exactly because `body_assigns(inv_local)` is `false`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemLoopFunction {
    /// The loop guard condition (`while cond { … }`).
    pub cond: SemCondTree,
    /// The loop body's ordered SSA assignment trace.
    pub body: Vec<SemStmt>,
    /// The local the PROVIDED untouched-local invariant pins (`I := λ e.
    /// e[inv_local] = inv_const`). Used as the invariant ONLY when `synth_inv`
    /// is `None`.
    pub inv_local: u64,
    /// The constant value the untouched-local invariant pins that local to.
    pub inv_const: i128,
    /// An optional SYNTHESIZED invariant (Step 6SI) that REPLACES the
    /// untouched-local equality invariant when present. `None` ⇒ the original
    /// `I := λ e. e[inv_local] = inv_const`; `Some(s)` ⇒ the non-trivial,
    /// abstract-domain-INFERRED invariant `s` (e.g. the interval upper bound
    /// `i ≤ n`) carried with a GENUINE arithmetic preservation proof. See
    /// [`SynthInvariant`].
    pub synth_inv: Option<SynthInvariant>,
}

/// A SYNTHESIZED loop invariant (Step 6SI) — a NON-TRIVIAL abstract-domain fact
/// that trust-strengthen's invariant inference PROPOSES and the clean kernel
/// CHECKS for preservation. Unlike the untouched-local equality invariant (whose
/// preservation is DEFINITIONAL because the body never writes the local), a
/// synthesized invariant is a real arithmetic fact whose preservation is a
/// GENUINE kernel proof — a WRONG proposal does not type-check ⇒ fail-closed.
///
/// HONEST SCOPE: today exactly ONE synthesized form is wired — the interval
/// LOWER bound `0 ≤ i` for the recognized counter loop `while i < n { i = i+1 }`,
/// which is EXACTLY what trust-strengthen's INTERVAL abstract domain infers from
/// the init `i = 0` and body `i = i + 1` (lower bound 0, upper bound widened to
/// +∞ ⇒ the candidate `0 ≤ i`). Its preservation `I e → guard → I (exec e
/// [i:=i+1])` reduces to `Int.le 0 ((e i)+1)`, proved GENUINELY from the
/// loop-carried hypothesis `hI : Int.le 0 (e i)` by
/// `Int.le_trans 0 (e i) ((e i)+1) hI (Int.le_self_add_one (e i))` — a real
/// inductive arithmetic step that USES the hypothesis (unlike the untouched-local
/// equality invariant, whose preservation ignores it). A WRONG synthesized
/// constant (e.g. `1 ≤ i`, false at `i = 0`) makes the proof ill-typed ⇒ the
/// kernel rejects ⇒ fail-closed. Other domains (octagon, congruence), upper bounds
/// that need the guard (`i ≤ n`), and other loop shapes are DEFERRED.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SynthInvariant {
    /// `I := λ e. Int.le (int_lit c) (e i_idx)` — the interval LOWER bound `c ≤ i`
    /// synthesized for the counter loop `while i < n { i = i + 1 }` (the inferred
    /// `c` is the init value, `0` for `let mut i = 0`). `i_idx` is the counter env
    /// index (the `i` `recognize_counter_loop` returns). Preservation is inductive:
    /// `c ≤ i → c ≤ i + 1`.
    CounterGeConst { i_idx: u64, c: i128 },
    /// `I := λ e. Int.le (e i_idx) (e bound_idx)` — the GUARD-AWARE upper bound `i ≤ n`
    /// synthesized for the counter loop `while i < n { i = i + 1 }`. `bound_idx` is the
    /// guard's bound env index (the `n` `recognize_counter_loop` returns). UNLIKE the
    /// lower bound, preservation genuinely USES the guard: from `eval_cond e (i<n) = true`
    /// extract `Int.lt i n`, which is DEFINITIONALLY `Int.le (i+1) n` (`Int.lt a b :=
    /// Int.le (a+1) b` in the kernel) — EXACTLY the reduced codomain `I (exec e [i:=i+1])
    /// ≡ Int.le (i+1) n`. The loop-carried hypothesis `hI : i ≤ n` is genuinely UNNEEDED
    /// (the guard alone re-establishes the bound), which is why the lower bound (which
    /// ignores the guard) and this upper bound are COMPLEMENTARY synthesized facts. The
    /// synthesizer PROPOSES `i ≤ bound` from the guard STRUCTURE `i < bound`; the kernel
    /// VERIFIES via the guard-using preservation proof. A WRONG upper bound (e.g.
    /// `i ≤ n-1`, false at exit, or a guard that is not `Lt`) fails closed.
    CounterLeBound { i_idx: u64, bound_idx: u64 },
    /// `I := λ e. And (Int.le (int_lit c) (e i_idx)) (Int.le (e i_idx) (e bound_idx))` —
    /// the CONJOINED range invariant `c ≤ i ∧ i ≤ n` for the counter loop, the COMPLETE
    /// synthesized interval `i ∈ [c, n]`. Combines the inductive lower bound
    /// ([`SynthInvariant::CounterGeConst`]) and the guard-aware upper bound
    /// ([`SynthInvariant::CounterLeBound`]) into a single invariant whose preservation is
    /// `And.intro <lower-pres> <upper-pres>`. This is the strongest synthesized fact for
    /// the recognized shape and the one `count_to`'s postcondition `ret ≤ n` consumes at
    /// exit (`ret = i`, and at the halting state `i ≤ n` from the upper conjunct).
    CounterInRange { i_idx: u64, c: i128, bound_idx: u64 },
    /// `I := λ e. Int.le (e i_idx) (Int.add (e bound_idx) (int_lit 1))` — the GUARD-AWARE
    /// upper bound `i ≤ n + 1` synthesized for the `≤`-GUARDED counter loop
    /// `while i ≤ n { i = i + 1 }`. The `Le` guard is WEAKER than `Lt`: it yields only
    /// `Int.le i n` (NOT `Int.le (i+1) n`), so the bare `i ≤ n` is NOT preserved (it is
    /// FALSE after the last iteration at `i = n`, where `i` becomes `n+1`). The SOUND
    /// guard-aware upper bound is therefore `i ≤ n+1`: its preservation codomain
    /// `Int.le (i+1) (n+1)` follows from the guard `Int.le i n` by
    /// `Int.add_le_add_right i n hg 1`. The synthesizer PROPOSES `i ≤ bound+1` from the
    /// `Le`-guard STRUCTURE `i ≤ bound`; the kernel VERIFIES via that monotone-add step.
    /// A WRONG bound (`i ≤ n`, the too-tight bound a `Le` guard does NOT preserve) fails
    /// closed. See [`counter_le_bound_succ_preservation_proof`].
    CounterLeBoundSucc { i_idx: u64, bound_idx: u64 },
    /// `I := λ e. And (Int.le (int_lit c) (e i_idx)) (Int.le (e i_idx) (Int.add (e
    /// bound_idx) (int_lit 1)))` — the CONJOINED range `c ≤ i ∧ i ≤ n+1` for the
    /// `≤`-guarded counter loop, the complete synthesized interval `i ∈ [c, n+1]`. The
    /// `Le`-guard analogue of [`SynthInvariant::CounterInRange`]; its upper conjunct is the
    /// guard-aware `i ≤ n+1` ([`SynthInvariant::CounterLeBoundSucc`]). Discharges `ret ≤ n+1`.
    CounterInRangeSucc { i_idx: u64, c: i128, bound_idx: u64 },
    /// `I := λ e. Int.le (int_lit c) (e i_idx)` — the interval LOWER bound `c ≤ i`
    /// synthesized for the COUNTDOWN loop `let mut i = n; while i > 0 { i = i - 1 }`.
    /// `i_idx` is the counter env index. UNLIKE [`SynthInvariant::CounterGeConst`] (whose
    /// `+1` body preserves the lower bound regardless of the guard), the countdown body
    /// `i := i - 1` only preserves `0 ≤ i` BECAUSE of the guard `i > 0` (≡ `Int.lt 0 i` ≡
    /// `Int.le 1 i`): from `1 ≤ i` we get `0 ≤ i-1` (`Int.add_le_add_right`-derived
    /// `countdownGe0`). The synthesizer PROPOSES this from the `Gt (·, 0)` guard +
    /// `i := i - 1` body. A WRONG constant (`1 ≤ i`, false at the terminal `i = 0`) or a
    /// non-decrement body fails closed. See [`countdown_ge_const_preservation_proof`].
    CountdownGeConst { i_idx: u64, c: i128 },
    /// `I := λ e. Int.le (int_lit c) (e i_idx)` — the interval LOWER bound `c ≤ i`
    /// synthesized for the STRIDE counter loop `while i < n { i = i + k }` (`k ≥ 1` a
    /// positive constant). The lower bound `c ≤ i` is preserved for ANY positive stride
    /// (`c ≤ i → c ≤ i + k`, since `i ≤ i + k` for `k ≥ 0`); the guard-aware UPPER bound
    /// `i ≤ n` is NOT generally preserved by a stride `k > 1` (it can overshoot), so only
    /// the lower bound is synthesized for the stride shape. `k` is carried so the
    /// preservation chains the `+k` step for the actual stride. The synthesizer PROPOSES
    /// `c ≤ i` from the `+k` body; a WRONG constant fails closed, and a NON-positive stride
    /// is not recognized. See [`stride_ge_const_preservation_proof`].
    StrideGeConst { i_idx: u64, c: i128, k: i128 },
    /// `I := λ e. Int.le (int_lit c) (e s_idx)` — the interval LOWER bound `c ≤ s` on the
    /// ACCUMULATOR `s` of a MULTI-STATEMENT counter loop
    /// `while i < n { s = s + 1; i = i + 1 }`. UNLIKE every variant above (whose invariant
    /// is about the SAME local the guard tests and the ranking measures), this invariant is
    /// about a SECOND mutable local `s` that the body ALSO updates — DISTINCT from the guard
    /// counter `i`. The body has TWO assignments; the synthesizer must handle BOTH. The
    /// preservation `c ≤ s → c ≤ s + 1` is the SAME inductive lower-bound step as
    /// [`SynthInvariant::CounterGeConst`] (`Int.le_trans` + `Int.le_self_add_one`), now at
    /// `s_idx` — and it reduces correctly through the 2-statement `exec` because the OTHER
    /// statement (`i := i + 1`) does NOT touch `s_idx` (`Nat.beq i_idx s_idx ≡ false`). The
    /// TERMINATION ranking is still `toNat(n − i)` over the GUARD counter `i_idx` (which the
    /// body's second statement increments), so `i_idx`/`n_idx` are carried for the ranking.
    /// The synthesizer infers `c ≤ s` from the accumulator's init + `s := s + 1` body
    /// statement (the INTERVAL domain, same as the counter lower bound). A WRONG constant is
    /// ill-typed ⇒ KernelRejected; a body that does NOT increment `s` by 1, or whose `i`
    /// update is not the recognized `+1`, fails closed. See
    /// [`accum_ge_const_preservation_proof`]. DEFERRED: non-`+1` accumulator strides,
    /// relational invariants between `s` and `i` (e.g. `s ≤ i`), and >2-statement bodies.
    AccumGeConst { s_idx: u64, c: i128, i_idx: u64, n_idx: u64 },
    /// `I := λ e. And (@Eq Int (e s_idx) (e i_idx)) (Int.le (e i_idx) (e n_idx))` — the
    /// CONJOINED RELATIONAL + interval invariant `s == i ∧ i ≤ n` for the LOCKSTEP accumulator
    /// loop `while i < n { s = s + 1; i = i + 1 }`. PART 1 (RELATIONAL): unlike
    /// [`SynthInvariant::AccumGeConst`] (the bare interval lower bound `0 ≤ s`, which only
    /// proves `ret ≥ 0`), the LEFT conjunct is a RELATIONAL fact BETWEEN two locals — `s` and
    /// the guard counter `i` increment in LOCKSTEP from equal inits (`s = 0`, `i = 0`), so
    /// `s == i` holds throughout. This is the STRONGER fact: it discharges `ret ≤ n` (since at
    /// exit `i ≤ n` from the right conjunct AND `s == i`, so `s ≤ n`).
    ///
    /// PRESERVATION is the genuine `And.intro` of:
    ///  * (LEFT) `s == i → s + 1 == i + 1` by `Int` CONGRUENCE: `@congrArg Int Int (e s)(e i)
    ///    (λ x. Int.add x 1) hI_eq` — a real `Eq` step that USES the relational hypothesis. A
    ///    WRONG relational claim (`s == i + 1`, or `s == i` on a NON-lockstep body where one
    ///    update is not `+1`) makes the reduced codomain `((e s)+δ) == ((e i)+1)` (δ ≠ 1) NOT
    ///    def-eq to `congrArg`'s output `((e s)+1) == ((e i)+1)` ⇒ ill-typed ⇒ KernelRejected.
    ///  * (RIGHT) `i ≤ n → i + 1 ≤ n` from the `Lt` GUARD `i < n` (≡ `i + 1 ≤ n`), exactly as
    ///    [`counter_le_bound_preservation_proof`] — `of_decide_eq_true` on the guard.
    ///
    /// The synthesizer PROPOSES `s == i` from the SYNTACTIC LOCKSTEP structure (the OCTAGON
    /// relational domain consumed in `prove::synth_eq_counter_relation`: both `s` and `i` carry
    /// the difference constraints `s - i ≤ 0 ∧ i - s ≤ 0`, i.e. `s == i`, inferred from equal
    /// inits + identical `+1` strides); the kernel VERIFIES preservation. `s_idx`/`i_idx` are
    /// the accumulator/counter env indices; `n_idx` is the guard bound (also the ranking bound).
    /// DEFERRED: non-`+1` lockstep strides, relational facts over >2 locals (general octagon),
    /// and non-equal-init offsets (`s == i + k`).
    AccumEqCounter { s_idx: u64, i_idx: u64, n_idx: u64 },
    /// `I := λ e. (a₀ == i) ∧ (a₁ == i) ∧ … ∧ (aₘ == i) ∧ (i ≤ n)` — the GENERAL RELATIONAL
    /// invariant (PART 1: GENERAL OCTAGON over >2 variables) for the THREE-OR-MORE-local LOCKSTEP
    /// loop `while i < n { a₀ = a₀+1; a₁ = a₁+1; …; i = i+1 }`. This GENERALIZES the 2-var
    /// [`SynthInvariant::AccumEqCounter`] (`s == i`) to a SET of relational equalities — a fact the
    /// 2-var relational domain CANNOT express, since it relates `m+1` ≥ 3 distinct locals (each
    /// accumulator `aₖ` plus the guard counter `i`) through the conjoined GENERAL octagon
    /// difference constraints `aₖ − i ≤ 0 ∧ i − aₖ ≤ 0` (i.e. `aₖ == i`) for EVERY `k`.
    ///
    /// `accum_idxs` is the ORDERED set of accumulator env indices `[a₀, …, aₘ]` (length ≥ 1; for
    /// `m = 0` this is exactly the 2-var [`SynthInvariant::AccumEqCounter`] shape, but the dedicated
    /// general path is taken only for `m ≥ 1`, i.e. ≥ 2 accumulators / ≥ 3 interacting locals).
    ///
    /// `ret_idx` is the accumulator env index the RETURN reads — `accum_idxs[k]` for SOME `k` (the
    /// extractor pins it to whichever lockstep accumulator the `Return` block copies into `_0`). The
    /// relational invariant pins `aₖ == i` for EVERY `k`, so `ret == a_{ret} == i ≤ n` discharges
    /// `ret ≤ n` REGARDLESS of which accumulator is returned: the postcondition discharge projects the
    /// matching `a_{ret} == i` conjunct (the one at position `k` in the nested `And`) and `Eq.subst`s
    /// `i ≤ n` along it. (For the `three`/`four` lockstep demos `ret_idx == accum_idxs[0]` — the FIRST
    /// accumulator; for `three_ret_b` it is `accum_idxs[1]` — the SECOND.)
    ///
    /// PRESERVATION is a NESTED right-folded `And.intro`: for EACH `aₖ == i` a congruence step
    /// `aₖ == i → aₖ+1 == i+1` (`@congrArg Int Int (e aₖ)(e i)(λ x. x+1) (And.left … hI)`, the SAME
    /// `Eq`-congruence as the 2-var case, projected from the nested `And`), capped by the guard-aware
    /// upper bound `i+1 ≤ n` from the `Lt` guard (`of_decide_eq_true`). A WRONG relational claim
    /// (some `aₖ == i + δ`, δ ≠ 0, or `aₖ == i` on a non-lockstep body whose `aₖ` update is not `+1`)
    /// makes that conjunct's reduced codomain NOT def-eq to `congrArg`'s output ⇒ KernelRejected
    /// (fail-closed). DEFERRED: non-`+1` lockstep strides and non-equal-init offsets (`aₖ == i + k`).
    AccumEqCounterSet { accum_idxs: Vec<u64>, i_idx: u64, n_idx: u64, ret_idx: u64 },
    /// `I := λ e. And (Int.le (int_lit c) (e m_idx)) (Int.le (int_lit 0) (e i_idx))` — the
    /// CONDITIONALLY-UPDATED accumulator interval invariant `c ≤ m ∧ 0 ≤ i` for the
    /// `max_scan`-shape loop `while i < n { if i > m { m = i }; i = i + 1 }` (Trust: Step 6CU).
    ///
    /// UNLIKE every accumulator variant above (whose body updates `m` UNCONDITIONALLY by a fixed
    /// `+δ` step), here the body updates `m` CONDITIONALLY: `m := if i > m { i } else { m }`,
    /// reflected as the body statement `m := Sel (i>m) i m`, whose `eval_rvalue` is
    /// `iteI e (i>m) (e i)(e m)`. The invariant's LEFT conjunct `c ≤ m` is preserved across
    /// BOTH arms of that conditional:
    ///   * THEN-arm (`i > m` true): the new `m` is `i`, and the goal `c ≤ i` holds because the
    ///     RIGHT conjunct carries `0 ≤ i` (and `c = 0` here, the tractable INTERVAL case).
    ///   * ELSE-arm (`i > m` false): `m` is unchanged, so `c ≤ m` holds by the LEFT conjunct of
    ///     the hypothesis.
    /// The preservation PROOF is a `Bool.rec` CASE-SPLIT over `eval_cond e (i>m)` (the update
    /// condition): each arm discharges the reduced `iteI`-codomain from the matching hypothesis
    /// conjunct. The RIGHT conjunct `0 ≤ i` is the SAME inductive counter lower bound as
    /// [`SynthInvariant::CounterGeConst`] (`0 ≤ i → 0 ≤ i+1`), carried so the then-arm has
    /// `0 ≤ i` available. `m_idx`/`i_idx` are the accumulator/counter env indices; `n_idx` is the
    /// guard bound (ranking `toNat(n − i)` over `i_idx`).
    ///
    /// FAIL-CLOSED: a WRONG conditional invariant — e.g. one the THEN-arm breaks (claiming `c ≤ m`
    /// for a `c > 0` that `m := i` does not establish from `0 ≤ i`, or the relational `m ≤ i`
    /// whose then-arm congruence does not retype) — makes a `Bool.rec` arm's reduced codomain NOT
    /// def-eq to its proof ⇒ ill-typed ⇒ KernelRejected. DEFERRED (HONEST): the RELATIONAL case
    /// `m ≥ i` / `m ≤ i` (which needs the then-arm to RELATE `m` and `i` after `m := i`, not just
    /// an interval lower bound) — only the TRACTABLE interval case `c = 0` (`0 ≤ m`) is wired.
    CondUpdateGeConst { m_idx: u64, c: i128, i_idx: u64, n_idx: u64 },
    /// `I := λ e. Int.le (int_lit c) (e count_idx)` — the interval LOWER bound `c ≤ count`
    /// (Trust: Step 6CI, Increment B, real-loop-leaf frontier — sibling to
    /// [`SynthInvariant::CondUpdateGeConst`]) for the BOOL-CAST CONDITIONAL-INCREMENT
    /// accumulator loop `while i < n { count := count + Cast(<bool>, IntTy); i := i + k }`
    /// (the `memchr::count_raw` shape: `count += (*ptr == needle) as usize; ptr =
    /// ptr.offset(1)`).
    ///
    /// UNLIKE [`SynthInvariant::CondUpdateGeConst`] (whose then-arm commits an
    /// INDEPENDENT local `i`, needing the invariant's SECOND conjunct `0 ≤ i` to justify
    /// it), here the then-arm commits `count + 1` — DERIVED FROM `count` ITSELF — so its
    /// bound follows from the SAME single hypothesis `c ≤ count` via the ORDINARY
    /// `Int.le_trans` + `Int.le_self_add_one` step (no second conjunct needed). The
    /// invariant is therefore the BARE `c ≤ count`, structurally IDENTICAL to
    /// [`SynthInvariant::CounterGeConst`]/[`SynthInvariant::AccumGeConst`]; only the
    /// PRESERVATION proof differs (a `Bool.rec` case-split over the update condition,
    /// whose FALSE-arm is `hI` directly and whose TRUE-arm is the inductive `+1` step —
    /// see [`cond_incr_ge_const_preservation_proof`]).
    ///
    /// `i_idx`/`n_idx` are carried (as in [`SynthInvariant::AccumGeConst`]) for the
    /// ranking `toNat(n_idx − i_idx)` — the loop's OWN counter (here the walking
    /// pointer), DECOUPLED from `count`.
    ///
    /// FAIL-CLOSED: a WRONG `c` (one the TRUE-arm's `+1` step does not retype for) is
    /// KernelRejected. DEFERRED: the RELATIONAL case (`count` offset from `i` by a
    /// non-zero constant) and non-`+1` conditional strides.
    CondIncrGeConst { count_idx: u64, c: i128, i_idx: u64, n_idx: u64 },
}

impl SynthInvariant {
    /// The env index this synthesized invariant is ABOUT — the local its lower/range bound
    /// constrains and (for the loop fully-faithful path) the RETURN reads. For every
    /// counter/countdown/stride variant this is the guard counter `i_idx`; for the
    /// ACCUMULATOR variant it is the accumulator `s_idx` (the return-read local), NOT the
    /// guard counter. Lets a caller recover the invariant local without matching each shape.
    #[must_use]
    pub fn counter_index(&self) -> u64 {
        match self {
            SynthInvariant::CounterGeConst { i_idx, .. }
            | SynthInvariant::CounterLeBound { i_idx, .. }
            | SynthInvariant::CounterInRange { i_idx, .. }
            | SynthInvariant::CounterLeBoundSucc { i_idx, .. }
            | SynthInvariant::CounterInRangeSucc { i_idx, .. }
            | SynthInvariant::CountdownGeConst { i_idx, .. }
            | SynthInvariant::StrideGeConst { i_idx, .. } => *i_idx,
            SynthInvariant::AccumGeConst { s_idx, .. } => *s_idx,
            // The RELATIONAL accumulator returns `s` (`s == i` discharges `ret ≤ n`), so the
            // invariant local — the one the RETURN reads — is the accumulator `s_idx`.
            SynthInvariant::AccumEqCounter { s_idx, .. } => *s_idx,
            // The GENERAL RELATIONAL set returns the accumulator `ret_idx` (the return-read local —
            // ANY `aₖ`, not just `a₀`); `a_{ret} == i ≤ n` discharges `ret ≤ n`. (`ret_idx` is pinned
            // by the extractor to whichever lockstep accumulator the `Return` block reads.)
            SynthInvariant::AccumEqCounterSet { ret_idx, .. } => *ret_idx,
            // The CONDITIONALLY-UPDATED accumulator returns `m` (`c ≤ m` discharges `ret ≥ c`),
            // so the invariant local — the one the RETURN reads — is the accumulator `m_idx`.
            SynthInvariant::CondUpdateGeConst { m_idx, .. } => *m_idx,
            // The CONDITIONAL-INCREMENT accumulator (Increment B) returns `count` (`c ≤ count`
            // discharges `ret ≥ c`), so the invariant local is `count_idx`.
            SynthInvariant::CondIncrGeConst { count_idx, .. } => *count_idx,
        }
    }
}

impl SemLoopFunction {
    /// Whether the loop body assigns the local `idx` (program-order, any statement).
    /// The invariant `I := λ e. e[inv_local] = c` is preserved DEFINITIONALLY only
    /// when the body does NOT assign `inv_local`; this is the soundness predicate the
    /// certificate's preservation proof rests on.
    fn body_assigns(&self, idx: u64) -> bool {
        self.body.iter().any(|s| s.idx == idx)
    }

    /// The closed `List Trust.MirSem.Stmt` value for the loop body's SSA trace
    /// (`cons s0 (cons s1 … nil)`). Same right-fold the straight-line `SemReturn`
    /// uses, so the body is pinned as a real prelude-`List` term.
    fn body_list_expr(&self) -> Expr {
        let stmt_ty = cst(MIRSEM_STMT);
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            stmt_ty.clone(),
        );
        self.body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty.clone(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The CONCRETE invariant predicate as a closed `Env → Prop`.
    ///
    /// When `synth_inv` is `None` this is the untouched-local EQUALITY invariant
    /// `I := λ (e : Env). @Eq Int (e inv_local) (int_lit inv_const)`. `claimed_local`
    /// overrides the pinned local (the equality fail-closed hook: a WRONG invariant
    /// about a DIFFERENT local that the body DOES assign must not be preserved ⇒
    /// ill-typed preservation).
    ///
    /// When `synth_inv` is `Some(CounterGeConst { i_idx, c })` this is the
    /// SYNTHESIZED interval lower-bound invariant `I := λ (e : Env). Int.le (int_lit
    /// c) (e i_idx)` (`c ≤ i`). `claimed_local` is IGNORED for the synthesized form
    /// (its fail-closed hook is a WRONG `synth_inv` constant, not a claimed local).
    fn invariant_expr(&self, claimed_local: Option<u64>) -> Expr {
        let bd = || BinderData::from(BinderInfo::Default);
        // SYNTHESIZED forms — built inside `λ (e : Env)` (e = bvar(0)). `claimed_local`
        // is IGNORED for all synthesized variants (their fail-closed hook is a WRONG
        // bound/op, not a claimed local).
        match &self.synth_inv {
            Some(SynthInvariant::CounterGeConst { i_idx, c }) => {
                // I := λ e. Int.le (int_lit c) (e i_idx)   (`c ≤ i`).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let le = Expr::apps(cst("Int.le"), [int_lit(*c), e_i]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::CounterLeBound { i_idx, bound_idx }) => {
                // I := λ e. Int.le (e i_idx) (e bound_idx)   (`i ≤ n`).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_b = Expr::app(Expr::bvar(0), Expr::nat_lit(*bound_idx));
                let le = Expr::apps(cst("Int.le"), [e_i, e_b]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::CounterInRange { i_idx, c, bound_idx }) => {
                // I := λ e. And (Int.le (int_lit c) (e i_idx)) (Int.le (e i_idx) (e bound_idx)).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_b = Expr::app(Expr::bvar(0), Expr::nat_lit(*bound_idx));
                let lo = Expr::apps(cst("Int.le"), [int_lit(*c), e_i.clone()]);
                let hi = Expr::apps(cst("Int.le"), [e_i, e_b]);
                let and = Expr::apps(cst("And"), [lo, hi]);
                return Expr::lam(bd(), env_ty(), and);
            }
            Some(SynthInvariant::CounterLeBoundSucc { i_idx, bound_idx }) => {
                // I := λ e. Int.le (e i_idx) (Int.add (e bound_idx) 1)   (`i ≤ n+1`).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_b = Expr::app(Expr::bvar(0), Expr::nat_lit(*bound_idx));
                let b1 = Expr::apps(cst("Int.add"), [e_b, int_one()]);
                let le = Expr::apps(cst("Int.le"), [e_i, b1]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::CounterInRangeSucc { i_idx, c, bound_idx }) => {
                // I := λ e. And (Int.le (int_lit c) (e i_idx)) (Int.le (e i_idx) ((e bound_idx)+1)).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_b = Expr::app(Expr::bvar(0), Expr::nat_lit(*bound_idx));
                let b1 = Expr::apps(cst("Int.add"), [e_b, int_one()]);
                let lo = Expr::apps(cst("Int.le"), [int_lit(*c), e_i.clone()]);
                let hi = Expr::apps(cst("Int.le"), [e_i, b1]);
                let and = Expr::apps(cst("And"), [lo, hi]);
                return Expr::lam(bd(), env_ty(), and);
            }
            Some(SynthInvariant::CountdownGeConst { i_idx, c }) => {
                // I := λ e. Int.le (int_lit c) (e i_idx)   (`c ≤ i`) — same SHAPE as the
                // CounterGeConst lower bound; the DIFFERENCE is the preservation proof (the
                // countdown body `i := i-1` needs the guard, see the proof builder).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let le = Expr::apps(cst("Int.le"), [int_lit(*c), e_i]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::StrideGeConst { i_idx, c, .. }) => {
                // I := λ e. Int.le (int_lit c) (e i_idx)   (`c ≤ i`) — same SHAPE as the
                // counter lower bound; the stride `k` only affects the preservation proof.
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let le = Expr::apps(cst("Int.le"), [int_lit(*c), e_i]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::AccumGeConst { s_idx, c, .. }) => {
                // I := λ e. Int.le (int_lit c) (e s_idx)   (`c ≤ s`) — the lower bound on the
                // ACCUMULATOR `s` (NOT the guard counter); the multi-statement body only
                // affects the preservation proof's codomain reduction.
                let e_s = Expr::app(Expr::bvar(0), Expr::nat_lit(*s_idx));
                let le = Expr::apps(cst("Int.le"), [int_lit(*c), e_s]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::AccumEqCounter { s_idx, i_idx, n_idx }) => {
                // I := λ e. And (@Eq Int (e s_idx) (e i_idx)) (Int.le (e i_idx) (e n_idx))
                //   — the RELATIONAL conjunct `s == i` AND the guard-aware upper bound `i ≤ n`.
                let e_s = Expr::app(Expr::bvar(0), Expr::nat_lit(*s_idx));
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_n = Expr::app(Expr::bvar(0), Expr::nat_lit(*n_idx));
                let eq = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [int_ty(), e_s, e_i.clone()],
                );
                let le = Expr::apps(cst("Int.le"), [e_i, e_n]);
                let and = Expr::apps(cst("And"), [eq, le]);
                return Expr::lam(bd(), env_ty(), and);
            }
            Some(SynthInvariant::CondUpdateGeConst { m_idx, c, i_idx, .. }) => {
                // I := λ e. And (Int.le (int_lit c) (e m_idx)) (Int.le (int_lit 0) (e i_idx))
                //   — the conditionally-updated accumulator's lower bound `c ≤ m` CONJOINED with
                //   the counter lower bound `0 ≤ i` (the latter feeds the then-arm `m := i`).
                let e_m = Expr::app(Expr::bvar(0), Expr::nat_lit(*m_idx));
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let lo_m = Expr::apps(cst("Int.le"), [int_lit(*c), e_m]);
                let lo_i = Expr::apps(cst("Int.le"), [int_lit(0), e_i]);
                let and = Expr::apps(cst("And"), [lo_m, lo_i]);
                return Expr::lam(bd(), env_ty(), and);
            }
            Some(SynthInvariant::CondIncrGeConst { count_idx, c, .. }) => {
                // I := λ e. Int.le (int_lit c) (e count_idx)   (`c ≤ count`) — the BARE
                // lower bound, structurally identical to `CounterGeConst`/`AccumGeConst`;
                // the conditional-increment body only affects the preservation proof.
                let e_count = Expr::app(Expr::bvar(0), Expr::nat_lit(*count_idx));
                let le = Expr::apps(cst("Int.le"), [int_lit(*c), e_count]);
                return Expr::lam(bd(), env_ty(), le);
            }
            Some(SynthInvariant::AccumEqCounterSet { accum_idxs, i_idx, n_idx, .. }) => {
                // I := λ e. (a₀ == i) ∧ (a₁ == i) ∧ … ∧ (aₘ == i) ∧ (i ≤ n)  — a NESTED
                // right-folded `And` of the relational equalities, capped by the upper bound.
                // (Independent of which accumulator the return reads — `ret_idx` does not appear.)
                let e_at = |idx: u64| Expr::app(Expr::bvar(0), Expr::nat_lit(idx));
                let e_i = e_at(*i_idx);
                let e_n = e_at(*n_idx);
                let eq_of = |a: Expr, b: Expr| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        [int_ty(), a, b],
                    )
                };
                // The CAP conjunct: `i ≤ n`.
                let mut acc = Expr::apps(cst("Int.le"), [e_i.clone(), e_n]);
                // Right-fold the equalities `aₖ == i` over the cap (innermost first ⇒ iterate in
                // REVERSE so `a₀ == i` ends OUTERMOST, matching `accum_idxs[0]` = the return-read).
                for &a_idx in accum_idxs.iter().rev() {
                    let eq = eq_of(e_at(a_idx), e_i.clone());
                    acc = Expr::apps(cst("And"), [eq, acc]);
                }
                return Expr::lam(bd(), env_ty(), acc);
            }
            None => {}
        }
        let local = claimed_local.unwrap_or(self.inv_local);
        // inside `λ (e : Env)`: e = bvar(0).
        let e_at = Expr::app(Expr::bvar(0), Expr::nat_lit(local));
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), e_at, int_lit(self.inv_const)],
        );
        Expr::lam(bd(), env_ty(), eq)
    }
}

/// A PER-FUNCTION loop-refinement certificate: the Hoare while-rule
/// (`loopInvariantRule`) INSTANTIATED at a concrete compiled function's
/// `(I, cond, body)`, kernel-checked modulo 3. The certificate proves PARTIAL
/// correctness — the provided invariant `I := λ e. e[r] = c` is maintained for an
/// ARBITRARY iteration count (`∀ n e, I e → I (exec_loop e cond body n)`). A
/// postcondition `ret = c` follows as a COROLLARY when the function returns the
/// untouched local `r`. TOTAL correctness (the ranking-decrease termination half) is
/// NOT part of this certificate — its arithmetic decrease proof is DEFERRED.
#[derive(Debug, Clone)]
pub struct LoopRefinementCertificate {
    /// The concrete loop function this certifies.
    pub function: SemLoopFunction,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl LoopRefinementCertificate {
    /// Whether this certificate is a genuine modulo-3 per-function loop instance.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Step 6BRK — PER-FUNCTION BREAK / EARLY-EXIT CERTIFICATE (the break-able while-rule
// WIRED at a concrete `while cond { if brk { break } i = i+1 }` whose synthesized
// invariant `i ≤ n` holds at BOTH exit points).
//
// This instantiates `loopInvariantRuleBrk` (the break-able Hoare while-rule over
// `exec_loopBrk`, combined guard `cond ∧ ¬brk`) at the function's concrete `(I, cond,
// brk, body)`, where `body = [i := i+1]` and `I := λ e. e[i] ≤ e[n]` is the guard-aware
// upper bound. The break preservation proof extracts the LOOP-guard component
// `eval_cond e cond = true` from the combined guard via `andLeftTrue`, then
// re-establishes `i+1 ≤ n` from `i < n` via `of_decide_eq_true` — EXACTLY the
// non-break `CounterLeBound` proof, modulo the `andLeftTrue` projection. The result is
// `∀ n_fuel e, I e → I (exec_loopBrk e cond brk body n_fuel)`: the invariant survives
// an arbitrary number of combined-guarded steps, so it holds at the env the loop is in
// when it exits — whether by `cond` going false OR by `brk` firing. SOUND because the
// invariant is preserved by the body under the COMBINED guard (the loop-guard part of
// which still gives `i < n`).
// ===========================================================================
/// A CONCRETE break-able loop function: `while cond { if brk { break } body }` whose
/// synthesized invariant holds at BOTH exit points (guard-false AND break). The body
/// runs only when the COMBINED guard `cond ∧ ¬brk` is true. Today the wired synthesized
/// invariant is the guard-aware upper bound `i ≤ n` ([`SynthInvariant::CounterLeBound`])
/// for the recognized counter shape `while i < n { if brk { break } i = i+1 }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemBreakLoopFunction {
    /// The loop guard (`while cond { … }`).
    pub cond: SemCondTree,
    /// The BREAK condition (`if brk { break }` at the top of the body).
    pub brk: SemCondTree,
    /// The loop body's ordered SSA assignment trace (the part AFTER the break check).
    pub body: Vec<SemStmt>,
    /// The synthesized invariant — the guard-aware upper bound `i ≤ n` that holds at
    /// every combined-guarded step and hence at BOTH exit points. (Other variants are
    /// DEFERRED; today only `CounterLeBound` is wired for the break shape.)
    pub synth_inv: SynthInvariant,
}

impl SemBreakLoopFunction {
    /// The closed `List Trust.MirSem.Stmt` value for the body's SSA trace.
    fn body_list_expr(&self) -> Expr {
        let stmt_ty = cst(MIRSEM_STMT);
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            stmt_ty.clone(),
        );
        self.body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty.clone(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The synthesized invariant predicate as a closed `Env → Prop`. Reuses the EXACT
    /// `SemLoopFunction::invariant_expr` shape builder by constructing a throwaway
    /// `SemLoopFunction` carrying the same `synth_inv` (so the break and non-break paths
    /// pin BYTE-IDENTICAL invariant predicates for the same `synth_inv`).
    fn invariant_expr(&self) -> Expr {
        let lf = SemLoopFunction {
            cond: self.cond.clone(),
            body: self.body.clone(),
            inv_local: 0,
            inv_const: 0,
            synth_inv: Some(self.synth_inv.clone()),
        };
        lf.invariant_expr(None)
    }
}

/// A PER-FUNCTION break-loop certificate: the break-able Hoare while-rule
/// (`loopInvariantRuleBrk`) INSTANTIATED at a concrete early-exit loop, kernel-checked
/// modulo 3. Proves PARTIAL correctness — the synthesized invariant `i ≤ n` holds at the
/// env reached after an arbitrary number of combined-guarded steps, hence at BOTH the
/// guard-false exit AND the break exit. A postcondition `ret ≤ n` follows when the
/// function returns the counter `i`.
#[derive(Debug, Clone)]
pub struct BreakLoopCertificate {
    /// The concrete break-able loop function this certifies.
    pub function: SemBreakLoopFunction,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl BreakLoopCertificate {
    /// Whether this certificate is a genuine modulo-3 per-function break-loop instance.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Step 6N — PER-FUNCTION NESTED-LOOP CERTIFICATE (the OUTER while-rule WIRED at a
// concrete `while cond_outer { <inner while-loop>; counter += 1 }` whose OUTER
// invariant is an UNTOUCHED LOCAL the inner loop's write-set EXCLUDES).
//
// This instantiates `loopInvariantRuleO` (the OUTER Hoare while-rule over `execO`)
// at the function's concrete `(I, cond_outer, outer_body)`, where `outer_body =
// [Loop(cond_inner, inner_body, f), Assign(counter, counter+1)]` runs the inner loop
// to completion for a symbolic fuel `f`. The OUTER preservation proof composes the
// INNER untouched-local lemma (`loopInvariantRule` at the inner invariant `Ir := λ e'.
// e' t = e t`, preserved DEFINITIONALLY because `inner_body` never writes `t`) with
// the outer assignment leaving `t` untouched. SOUND exactly because NEITHER the inner
// body NOR the outer counter-assignment writes the untouched local `t`.
// ===========================================================================
/// A CONCRETE nested-loop function: an OUTER `while cond_outer { <inner loop>;
/// counter += 1 }` whose UNTOUCHED-LOCAL invariant `I := λ e. e[t_idx] = t_const` is
/// preserved across both loops because neither writes `t_idx`. The inner loop is the
/// flat `while cond_inner { inner_body }` (a `List Stmt`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemNestedLoopFunction {
    /// The OUTER loop guard.
    pub cond_outer: SemCondTree,
    /// The INNER loop guard.
    pub cond_inner: SemCondTree,
    /// The INNER loop body (flat `List Stmt`).
    pub inner_body: Vec<SemStmt>,
    /// The OUTER counter local (`counter += 1` in the outer body, AFTER the inner loop).
    pub counter_idx: u64,
    /// The untouched local the OUTER invariant pins (`I := λ e. e[t_idx] = t_const`).
    /// Neither the inner body nor the outer counter-assignment may write it.
    pub t_idx: u64,
    /// The constant the untouched local is pinned to (`I := λ e. e[t_idx] = t_const`).
    pub t_const: i128,
}

impl SemNestedLoopFunction {
    /// Whether the INNER loop body assigns local `idx` (the inner write-set membership).
    #[must_use]
    pub fn inner_assigns(&self, idx: u64) -> bool {
        self.inner_body.iter().any(|s| s.idx == idx)
    }

    /// The closed `List Trust.MirSem.Stmt` value for the INNER loop body.
    fn inner_body_list_expr(&self) -> Expr {
        let stmt_ty = cst(MIRSEM_STMT);
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            stmt_ty.clone(),
        );
        self.inner_body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty.clone(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The OUTER body as a closed `List OStmt`, with the inner loop's fuel taken from
    /// the de Bruijn ref `fuel_ref` (a free `Nat` variable bound OUTSIDE this term):
    /// `[ OStmt.Loop cond_inner inner_body fuel ; OStmt.Assign counter (counter+1) ]`.
    fn outer_body_list_expr(&self, fuel_ref: Expr) -> Expr {
        let ostmt_ty = cst(MIRSEM_OSTMT);
        // OStmt.Loop cond_inner inner_body fuel
        let loop_stmt = Expr::apps(
            cst(MIRSEM_OSTMT_LOOP),
            [self.cond_inner.to_cond_expr(), self.inner_body_list_expr(), fuel_ref],
        );
        // OStmt.Assign counter (Bin Add (Var counter) (Const 1))
        let inc_rv =
            SemRvalue::Bin(SemBinOp::Add, SemOperand::Var(self.counter_idx), SemOperand::Const(1));
        let assign_stmt = Expr::apps(
            cst(MIRSEM_OSTMT_ASSIGN),
            [Expr::nat_lit(self.counter_idx), inc_rv.to_rvalue_expr()],
        );
        // cons loop_stmt (cons assign_stmt nil)
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            ostmt_ty.clone(),
        );
        let cons = |head: Expr, tail: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [ostmt_ty.clone(), head, tail],
            )
        };
        cons(loop_stmt, cons(assign_stmt, nil))
    }

    /// The OUTER invariant `I := λ (e : Env). @Eq Int (e t_idx) (int_lit t_const)`.
    fn invariant_expr(&self) -> Expr {
        let bd = || BinderData::from(BinderInfo::Default);
        let e_at = Expr::app(Expr::bvar(0), Expr::nat_lit(self.t_idx));
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), e_at, int_lit(self.t_const)],
        );
        Expr::lam(bd(), env_ty(), eq)
    }
}

/// A PER-FUNCTION nested-loop certificate: the OUTER Hoare while-rule
/// (`loopInvariantRuleO`) INSTANTIATED at a concrete nested loop, kernel-checked
/// modulo 3. Proves PARTIAL correctness — the untouched-local invariant `I := λ e.
/// e[t_idx] = t_const` survives an arbitrary outer iteration count, AND each outer
/// iteration runs the inner loop to completion (the inner loop's untouched-local
/// preservation is composed in).
#[derive(Debug, Clone)]
pub struct NestedLoopCertificate {
    /// The concrete nested-loop function this certifies.
    pub function: SemNestedLoopFunction,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl NestedLoopCertificate {
    /// Whether this certificate is a genuine modulo-3 per-function nested-loop instance.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Step 6NM — PER-FUNCTION NESTED-LOOP CERTIFICATE where the INNER loop MODIFIES the
// OUTER-invariant variable (MONOTONICITY composition).
//
// The existing `SemNestedLoopFunction` certifies the case where the inner loop's
// write-set EXCLUDES the outer-invariant local (`I := λ e. e[t] = c`, preserved because
// neither loop writes `t`). This step handles the HARDER case: the inner loop WRITES the
// outer-invariant variable `s`, but MONOTONICALLY — it only INCREMENTS `s` — so the
// outer lower-bound invariant `I := λ e. 0 ≤ e[s]` is preserved THROUGH the inner loop.
// This is the `while i<n { while j<n { s=s+1; j=j+1; } i=i+1; }` shape with `ensures
// ret ≥ 0`.
//
// The composition is a genuine WRITE-SET / MONOTONICITY argument:
//   * INNER invariant `Ir := λ e'. 0 ≤ e'[s]` (a CLOSED predicate — unlike the untouched
//     case, it does NOT reference the outer `e`). The inner loop PRESERVES it: the body
//     `[s:=s+1; j:=j+1]` increments `s` (and the `j:=j+1` leaves `s` untouched), so
//     `0 ≤ s → 0 ≤ s+1` by the SAME inductive lower-bound step as the synthesized
//     `CounterGeConst` (`Int.le_trans 0 s (s+1) hr (Int.le_self_add_one s)`).
//   * The outer hypothesis `hI : 0 ≤ e[s]` IS `Ir e` (same predicate), so the inner
//     `loopInvariantRule` instance fed `hI` directly yields `Ir (exec_loop e cond_inner
//     inner_body fuel)` ≡ `0 ≤ (exec_loop …)[s]` — the inner loop's own invariant
//     transported across the completed inner run. NO `Eq.refl`/`Eq.trans` bridge.
//   * The outer counter increment `i:=i+1` leaves `s` untouched, so `execO`'s threading
//     of `[Loop(…); Assign(i, i+1)]` has the SAME value at `s` as the inner-loop result,
//     hence the outer codomain `0 ≤ (execO e outer_body)[s]` is DEF-EQ to the inner
//     `loopInvariantRule` result. The OUTER preservation proof IS that inner result.
//
// SOUND because (a) the inner body's net effect at `s` is `+δ` with δ ≥ 0 (here +1) so
// `0 ≤ s` is genuinely preserved, and (b) the outer increment does not touch `s`. A
// WRONG monotone claim — an inner body that DECREMENTS `s` — makes the inner
// preservation's `Int.le_self_add_one` codomain `0 ≤ s+1` differ from the actual
// `0 ≤ s-1` ⇒ ill-typed ⇒ KernelRejected. ADDITIVE on the OStmt layer (reuses
// `loopInvariantRuleO` for the outer loop and `loopInvariantRule` for the inner).
// ===========================================================================
/// A CONCRETE nested-loop function whose INNER loop MODIFIES the outer-invariant
/// variable `s` MONOTONICALLY: an OUTER `while cond_outer { <inner loop>; i += 1 }` whose
/// inner loop `while cond_inner { s := s+1; j := j+1 }` increments the accumulator `s`.
/// The outer lower-bound invariant `I := λ e. 0 ≤ e[s_idx]` is preserved through the
/// inner loop by the inner loop's OWN lower-bound invariant (monotone composition).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemMonotoneNestedLoopFunction {
    /// The OUTER loop guard.
    pub cond_outer: SemCondTree,
    /// The INNER loop guard.
    pub cond_inner: SemCondTree,
    /// The INNER loop body (flat `List Stmt`) — MUST increment `s_idx` by `+1` and leave
    /// `s_idx` non-decreasing (the monotonicity premise). Typically `[s:=s+1; j:=j+1]`.
    pub inner_body: Vec<SemStmt>,
    /// The OUTER counter local (`i += 1` AFTER the inner loop). Must differ from `s_idx`.
    pub counter_idx: u64,
    /// The accumulator the outer lower-bound invariant constrains (`I := λ e. c ≤ e[s_idx]`).
    /// The inner loop WRITES this (monotonically); the outer counter-assignment does NOT.
    pub s_idx: u64,
    /// The lower-bound constant (`I := λ e. c ≤ e[s_idx]`; `0` for `let mut s = 0`).
    pub c: i128,
}

impl SemMonotoneNestedLoopFunction {
    /// Whether the INNER loop body assigns local `idx` (the inner write-set membership).
    #[must_use]
    pub fn inner_assigns(&self, idx: u64) -> bool {
        self.inner_body.iter().any(|s| s.idx == idx)
    }

    /// The closed `List Trust.MirSem.Stmt` value for the INNER loop body.
    fn inner_body_list_expr(&self) -> Expr {
        let stmt_ty = cst(MIRSEM_STMT);
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            stmt_ty.clone(),
        );
        self.inner_body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty.clone(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The OUTER body as a closed `List OStmt` (inner loop at symbolic `fuel_ref`, then
    /// `i += 1`): `[ OStmt.Loop cond_inner inner_body fuel ; OStmt.Assign i (i+1) ]`.
    fn outer_body_list_expr(&self, fuel_ref: Expr) -> Expr {
        let ostmt_ty = cst(MIRSEM_OSTMT);
        let loop_stmt = Expr::apps(
            cst(MIRSEM_OSTMT_LOOP),
            [self.cond_inner.to_cond_expr(), self.inner_body_list_expr(), fuel_ref],
        );
        let inc_rv =
            SemRvalue::Bin(SemBinOp::Add, SemOperand::Var(self.counter_idx), SemOperand::Const(1));
        let assign_stmt = Expr::apps(
            cst(MIRSEM_OSTMT_ASSIGN),
            [Expr::nat_lit(self.counter_idx), inc_rv.to_rvalue_expr()],
        );
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            ostmt_ty.clone(),
        );
        let cons = |head: Expr, tail: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [ostmt_ty.clone(), head, tail],
            )
        };
        cons(loop_stmt, cons(assign_stmt, nil))
    }

    /// The OUTER lower-bound invariant `I := λ (e : Env). Int.le (int_lit c) (e s_idx)`
    /// (`c ≤ s`). This is ALSO the inner invariant `Ir` (the SAME closed predicate — the
    /// inner loop preserves the exact fact the outer loop carries).
    fn invariant_expr(&self) -> Expr {
        let bd = || BinderData::from(BinderInfo::Default);
        let e_s = Expr::app(Expr::bvar(0), Expr::nat_lit(self.s_idx));
        let le = Expr::apps(cst("Int.le"), [int_lit(self.c), e_s]);
        Expr::lam(bd(), env_ty(), le)
    }
}

/// A PER-FUNCTION monotone-nested-loop certificate: the OUTER Hoare while-rule
/// (`loopInvariantRuleO`) INSTANTIATED at a nested loop whose INNER loop MONOTONICALLY
/// modifies the outer-invariant variable `s`, kernel-checked modulo 3. Proves PARTIAL
/// correctness — the lower-bound invariant `c ≤ s` survives an arbitrary outer iteration
/// count, EACH of whose iterations runs the inner loop (which increments `s`) to
/// completion while preserving `c ≤ s` via the inner loop's own invariant. A
/// postcondition `ret ≥ 0` (for `c = 0`) follows when the function returns `s`.
#[derive(Debug, Clone)]
pub struct MonotoneNestedLoopCertificate {
    /// The concrete monotone-nested-loop function this certifies.
    pub function: SemMonotoneNestedLoopFunction,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl MonotoneNestedLoopCertificate {
    /// Whether this certificate is a genuine modulo-3 per-function instance.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

/// The kernel name of the COUNTDOWN lower-bound lemma `0 < i → 0 ≤ i-1`.
const MIRSEM_COUNTDOWN_GE0: &str = "Trust.MirSem.countdownGe0";

/// The kernel name of the COUNTDOWN ranking-decrease lemma `0 < i → toNat(i-1) < toNat(i)`.
const MIRSEM_COUNTDOWN_RANK_DECREASE: &str = "Trust.MirSem.countdownRankDecrease";

/// The GENERAL per-loop arithmetic DECREASE lemma — a kernel-checked `Declaration::Theorem`
/// the per-function termination instance applies:
///
/// `Trust.MirSem.loopRankDecrease : ∀ (a b : Int), Int.lt a b →
///    Nat.lt (Int.toNat (Int.sub b (Int.add a (Int.ofNat 1)))) (Int.toNat (Int.sub b a))`
///
/// i.e. when `a < b`, the gap `b - (a+1)` is STRICTLY SMALLER (as a `Nat`) than `b - a`
/// — the ranking-decrease fact the counter loop needs (with `a := i`, `b := n`, so
/// `toNat(n-(i+1)) < toNat(n-i)`). Proof: `Int.lt a b` def-unfolds to `Int.NonNeg (Int.sub
/// b (Int.add a 1))`; eliminate it with `Int.NonNeg.rec` to a `Nat k` with `Int.sub b
/// (a+1) ≡ Int.ofNat k`; bridge `Int.sub b a = Int.add (Int.sub b (a+1)) (Int.ofNat 1)`
/// via `Int.sub_add_sub_cancel` + `Int.add_one_sub_self`; in the `ofNat k` branch the RHS
/// REDUCES to `Int.ofNat (Nat.succ k)`, so `toNat(b-a) ≡ Nat.succ k` and `toNat(b-(a+1)) ≡
/// k`; close with `Nat.le.refl (Nat.succ k)` transported by the equality. Constructive
/// (axiom closure ⊆ the 3 foundational axioms). Requires the int-order lemmas registered
/// (see [`loop_total_correct_instance_env`]).
const MIRSEM_LOOP_RANK_DECREASE: &str = "Trust.MirSem.loopRankDecrease";

/// The forward `ofNat`-monotone cast `Trust.MirSem.ofNatLeOfNatOfLe`:
/// `∀ (m p : Nat), Nat.le m p → Int.le (Int.ofNat m) (Int.ofNat p)`. Proven by
/// `@Nat.le.rec` on the `Nat.le` witness (refl ⇒ `Int.le_refl`, step ⇒
/// `Int.le_trans … (Int.le_self_add_one …)`, using `ofNat (succ t) ≡ add (ofNat t) 1`).
const MIRSEM_OFNAT_LE_OFNAT_OF_LE: &str = "Trust.MirSem.ofNatLeOfNatOfLe";

/// The converse `ofNat`-cast `Trust.MirSem.leOfOfNatLeOfNat`:
/// `∀ (m p : Nat), Int.le (Int.ofNat m) (Int.ofNat p) → Nat.le m p`. Proven by
/// `@Or.rec` on `Nat.le_or_lt m p : Or (Nat.le m p) (Nat.le (succ p) m)`: the `inl`
/// branch returns the witness directly; the `inr` branch (`Nat.le (succ p) m`, i.e.
/// `p < m`) casts forward via `ofNatLeOfNatOfLe (succ p) m`, chains with the hypothesis
/// through `Int.le_trans` to `Int.le (ofNat (succ p)) (ofNat p)` (≡ `Int.lt (ofNat p)(ofNat p)`,
/// since `Int.lt x y := Int.le (x+1) y` and `ofNat (succ p) ≡ ofNat p + 1`), then closes
/// with `Int.lt_irrefl (ofNat p)` ⇒ `False.elim`.
const MIRSEM_LE_OF_OFNAT_LE_OFNAT: &str = "Trust.MirSem.leOfOfNatLeOfNat";

/// The kernel name of the `Int.toNat` monotonicity lemma.
const MIRSEM_TONAT_MONO: &str = "Trust.MirSem.toNatMono";

/// `Trust.MirSem.negSuccNotNonNeg : ∀ (q : Nat), Int.NonNeg (Int.negSucc q) → False`.
/// `@Int.NonNeg.rec` with the equation-carrying motive `λ x _. (x = negSucc q) → False`
/// discharges it: the only minor at index `ofNat n` gets `heq : ofNat n = negSucc q`,
/// refuted by `Int.noConfusion`. (The caller transports the actual `Int.le (ofNat 0)(negSucc
/// q)` witness — `≡ NonNeg (subNatNat 0 (succ q))` — to `NonNeg (negSucc q)` along
/// `Int.subNatNat_zero_succ`.)
const MIRSEM_NEGSUCC_NOT_NONNEG: &str = "Trust.MirSem.negSuccNotNonNeg";

// ===========================================================================
// `strideRankDecrease` — the STRIDE generalization of `loopRankDecrease`: when `a < b`
// and `k ≥ 1`, the gap `b - (a+k)` is STRICTLY SMALLER (as a `Nat`) than `b - a`.
// Composes `loopRankDecrease` (the `+1` case) with `toNatMono` (subtraction antitone).
// ===========================================================================
/// The kernel name of the stride ranking-decrease lemma.
const MIRSEM_STRIDE_RANK_DECREASE: &str = "Trust.MirSem.strideRankDecrease";

/// A PER-FUNCTION TOTAL-CORRECTNESS certificate: the composed `loopTotalCorrect`
/// theorem INSTANTIATED at a concrete compiled function's `(I, R, cond, body)` with a
/// SYNTHESIZED ranking `R` and a CONCRETE kernel-checked decrease proof, kernel-checked
/// modulo 3. It proves TOTAL correctness — the invariant `I` holds AT the halting state
/// AND the loop HALTS within `R e` guarded steps.
///
/// HONESTY: the ranking is now SYNTHESIZED (INFERRED from the loop structure by
/// [`synthesize_counter_ranking`]: a `counter < bound` guard + `+1` increment proposes
/// `R := λ e. toNat(bound - counter)`), not hand-supplied; the kernel VERIFIES the
/// decrease. The invariant `I` is either the untouched-local equality (provided) or a
/// SYNTHESIZED interval fact (lower bound `c ≤ i`, guard-aware upper bound `i ≤ n`, or
/// the conjoined range). General ranking synthesis for non-`+1` strides, non-`Lt` guards,
/// multi-statement bodies, and nested loops remains DEFERRED. A WRONG ranking (one whose
/// decrease proof does not retype) fails closed.
#[derive(Debug, Clone)]
pub struct LoopTotalCorrectCertificate {
    /// The concrete loop function this certifies.
    pub function: SemLoopFunction,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl LoopTotalCorrectCertificate {
    /// Whether this certificate is a genuine modulo-3 per-function total-correctness
    /// instance (invariant-at-halt AND termination, kernel-checked).
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ---------------------------------------------------------------------------
// LOOP POSTCONDITION DISCHARGE — connect the SYNTHESIZED loop invariant to the
// function's SOURCE postcondition `ret <op> bound/const`, kernel-checked modulo 3.
// ---------------------------------------------------------------------------
/// The source postcondition shape a counter loop's SYNTHESIZED invariant discharges —
/// a relation between the RETURN local `_0` (which, at the halting state, equals the
/// loop counter the body increments) and either the guard's bound or a constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopPostcondition {
    /// `ret ≤ n` — discharged by the synthesized UPPER bound conjunct `i ≤ n` (with the
    /// return reading the counter, so `ret = i` at exit). `bound_idx` is the guard bound's
    /// env index.
    RetLeBound { bound_idx: u64 },
    /// `c ≤ ret` (i.e. `ret ≥ c`) — discharged by the synthesized LOWER bound conjunct
    /// `c ≤ i`.
    ConstLeRet { c: i128 },
    /// `ret ≤ n + 1` — discharged by the `≤`-guarded UPPER bound conjunct `i ≤ n+1` (the
    /// `≤`-guarded loop `while i ≤ n { i = i+1 }` returns `n+1`). `bound_idx` is the guard
    /// bound's env index.
    RetLeBoundSucc { bound_idx: u64 },
}

/// A PER-FUNCTION LOOP-POSTCONDITION certificate: the source postcondition `ret <op>
/// bound/const` is kernel-proven (modulo 3) to hold AT the loop's halting state, by
/// projecting the relevant conjunct out of the SYNTHESIZED range invariant (whose
/// preservation-at-halt is the kernel-checked `loopTotalCorrect` instance). This is the
/// connection that makes a counter loop returning the counter (e.g. `count_to`/`count_up`)
/// FULLY FAITHFUL via the SYNTHESIZED invariant: the postcondition `ret ≤ n` is discharged
/// by the synthesized upper bound `i ≤ n`, not by an SMT call.
#[derive(Debug, Clone)]
pub struct LoopPostconditionCertificate {
    /// The concrete loop function this certifies.
    pub function: SemLoopFunction,
    /// The discharged postcondition shape.
    pub post: LoopPostcondition,
    /// The kernel-checked verdict (`ProvenModulo3` for a real certificate).
    pub verdict: RefinementVerdict,
}

impl LoopPostconditionCertificate {
    /// Whether this certificate is a genuine modulo-3 postcondition discharge.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// W2 INCREMENT-1 — SLICE-INDEX-LOOP PARTIAL-TIER LANE (the FIRST unbounded-loop
// certificate over real slice code). The recognized fragment is the index loop
// `let mut a=<c>; let mut i=0; while i < s.len() { a op= s[i]; i += 1 } a` over one
// immutable `&[T]` slice parameter (7bb MIR, ZERO calls). The lane certifies the
// GENUINELY-INDUCTIVE PARTIAL tier over a COUNTER-PROJECTED model:
//
//   (I)   loopInvariantRule at `CounterInRange 0≤i ∧ i≤n` (Nat.rec over arbitrary
//         iteration count) — reused verbatim via `loop_refinement_witness`;
//   (II)  the BoundsCheck assert `Inv ∧ Guard → Lt(i,n)` (reduces to `Lt(i,n) →
//         Lt(i,n)` after len-pinning normalization); and
//   (III) the counter-increment overflow assert `Inv ∧ Guard ∧ (n ≤ 2^w−1) →
//         (i+1 ≤ 2^w−1)`, using the usize type-bound on the slice length `n`.
//
// SPLIT-CLAIM / TRUST BOUNDARY (documented, recognizer-side): the accumulator and
// element-read statements are ELIDED from the kernel model — the projected body is
// exactly `[i := i+1]`. This is sound BECAUSE the recognizer's frame gate proves the
// slice is never written / mut-borrowed / address-taken (so every per-iteration
// `PtrMetadata(s)` recomputation is the SAME symbolic `n`), and the elided statements
// write only `{acc, its temps}` — never `{i, n}`, which the guard/asserts/invariant
// read. This is the SAME MIR→Sem mapping trust boundary every existing loop lane
// occupies, stated here as an explicit split-claim.
//
// THREE MANDATORY GATES (adversarial NEEDS-GATE verdicts, non-negotiable):
//   (1) TERMINATION-CLAIM GATE: the lane emits loopRankTerminates/loopTotalCorrect
//       (any "terminating"/"totally-correct" claim) ONLY IF the function's safety VCs
//       are ALL discharged — else the PARTIAL tier is certified with NO reach-Return
//       claim (a panic exit exists: `s=[i32::MAX,1]` fires the accumulator-overflow
//       assert at i=1 and never reaches Return, falsifying loopTotalCorrect's
//       guard-false-halt conjunct as a real-function claim). `slice_index_partial_witness`
//       emits termination ONLY when its `total_available` argument is true, which the
//       prove.rs entry sets to `function_safety_vcs_all_discharged(func)`.
//   (2) DECLARED-SPEC DECLINATION: enforced in the prove.rs entry — fail closed unless
//       the function's declared postcondition surface is EMPTY (no ensures may ride the
//       havocked accumulator).
//   (3) CLAIM-SURFACE HONESTY: `SliceIndexPartialCertificate::tier_claim` states the tier
//       as "invariant + assert-discharge modulo 3; termination NOT claimed" for the
//       partial tier, and documents the counter-projection trust boundary.
//
// OUT-OF-BAND QUARANTINE: `SliceIndexLoopFunction` is a DISTINCT `HavocProjected` type,
// NOT a bare `SemLoopFunction`; the projected model is reachable ONLY from this lane's
// own witness, never returned in-band from the shared `extract_synth_loop_function`
// dispatcher, so no existing consumer (`synth_loop_function_fully_faithful`,
// `sem_loop_to_ir_loop`, the trust-ir denotation path) can treat it as a normal
// counter loop or install the counter-only body as the function's denotation.
// ===========================================================================
/// The COUNTER-PROJECTED model of a recognized `while i < s.len() { a op= s[i]; i += 1 }`
/// slice-index loop. A distinct `HavocProjected` type (NOT a bare [`SemLoopFunction`]) so
/// the projection can never leak in-band to the shared loop consumers (out-of-band
/// quarantine — see the module comment above).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SliceIndexLoopFunction {
    /// The counter-PROJECTED loop: body `[i := i+1]`, guard `Lt(i, n)`, synthesized
    /// invariant `CounterInRange { i, 0, n }`. `n` is a fresh symbolic env slot modeling
    /// `sliceLen(s)` (the guard's len temp's MIR local).
    pub projected: SemLoopFunction,
    /// The loop guard `Lt(i, n)` (the header `SwitchInt` comparison).
    pub guard: SemCond,
    /// The `BoundsCheck` assert condition, LEN-PINNING-NORMALIZED so its len operand is
    /// the SAME symbolic slot `n` as the guard (justified by the frame gate: the slice is
    /// never written, so every `PtrMetadata(s)` recomputation is the same value). For the
    /// recognized fragment this is byte-identical to `guard`; a hidden-second-index /
    /// off-by-one forgery makes it differ, so its discharge implication is KernelRejected.
    pub bounds_cond: SemCond,
    /// The counter env index `i` (== its MIR local).
    pub i_idx: u64,
    /// The symbolic len slot `n` (== the guard's len temp MIR local).
    pub n_idx: u64,
    /// Bit width of the COUNTER's integer type — the counter-increment overflow goal is
    /// `i+1 ≤ 2^counter_width − 1`.
    pub counter_width: u32,
    /// Bit width of the LEN's `usize` type — the type-bound hypothesis is
    /// `n ≤ 2^len_width − 1`. For a slice length this is the pointer width (64).
    pub len_width: u32,
}

/// The PARTIAL-TIER certificate a recognized slice-index loop mints: the genuinely
/// inductive invariant + the two in-loop assert discharges, all kernel-checked modulo 3,
/// with termination CONDITIONAL on full safety-VC discharge (the mandatory termination
/// gate). For `while_idx` the accumulator-overflow VC is genuinely undischargeable
/// spec-free, so the certificate carries the PARTIAL tier: `termination_claimed = false`.
#[derive(Debug, Clone)]
pub struct SliceIndexPartialCertificate {
    /// The counter-projected loop this certifies.
    pub function: SliceIndexLoopFunction,
    /// (I) loopInvariantRule at `CounterInRange 0≤i ∧ i≤n`, kernel-checked modulo 3.
    pub invariant: RefinementVerdict,
    /// (II) the BoundsCheck assert discharge `Inv ∧ Guard → Lt(i,n)`, modulo 3.
    pub bounds_discharge: RefinementVerdict,
    /// (III) the counter-increment overflow discharge (under the usize len type-bound),
    /// modulo 3.
    pub counter_overflow_discharge: RefinementVerdict,
    /// The TERMINATION half (loopRankTerminates + loopTotalCorrect over the projected
    /// loop). `Some(verdict)` ONLY when `total_available` was true at mint time (i.e. the
    /// function's safety VCs are all discharged — the mandatory termination gate); `None`
    /// for the PARTIAL tier (a panic exit remains), where NO reach-Return claim is made.
    pub termination: Option<RefinementVerdict>,
}

impl SliceIndexPartialCertificate {
    /// Whether the three PARTIAL-tier kernel obligations (invariant + both assert
    /// discharges) all check modulo 3 — the tier this increment ships for `while_idx`.
    #[must_use]
    pub fn is_partial_modulo_3(&self) -> bool {
        matches!(self.invariant, RefinementVerdict::ProvenModulo3)
            && matches!(self.bounds_discharge, RefinementVerdict::ProvenModulo3)
            && matches!(self.counter_overflow_discharge, RefinementVerdict::ProvenModulo3)
    }

    /// Whether a TERMINATION / total-correctness claim is being made (only under the
    /// mandatory gate: full safety-VC discharge). `false` for the partial tier.
    #[must_use]
    pub fn termination_claimed(&self) -> bool {
        matches!(self.termination, Some(RefinementVerdict::ProvenModulo3))
    }

    /// The machine-readable CLAIM-SURFACE (mandatory gate 3). For the partial tier it
    /// states EXACTLY what is certified and — critically — that termination is NOT claimed,
    /// with the undischarged panic exit and the counter-projection trust boundary named.
    #[must_use]
    pub fn tier_claim(&self) -> String {
        if self.termination_claimed() {
            "slice-index-loop TOTAL tier: loopInvariantRule (CounterInRange 0≤i ∧ i≤n) + \
             BoundsCheck-assert discharge + counter-increment-overflow discharge (under usize \
             len type-bound) + loopRankTerminates/loopTotalCorrect (rank toNat(n−i)), all \
             modulo 3; every safety VC discharged so reach-Return holds. Counter-projection of \
             acc/elem is recognizer-trust (frame-gated: slice never written/mut-borrowed/\
             address-taken)."
                .to_string()
        } else {
            "slice-index-loop PARTIAL tier: loopInvariantRule (CounterInRange 0≤i ∧ i≤n) + \
             BoundsCheck-assert discharge + counter-increment-overflow discharge (under usize \
             len type-bound), all modulo 3; termination NOT claimed (undischarged \
             accumulator-overflow panic exit — e.g. s=[i32::MAX,1] panics at i=1 and never \
             reaches Return). Counter-projection of acc/elem is recognizer-trust (frame-gated: \
             slice never written/mut-borrowed/address-taken); the accumulator/element channel \
             is HAVOCKED (no ret-value claim)."
                .to_string()
        }
    }
}

// ===========================================================================
// Trust: W2 INCREMENT-2 — ITERATOR-FOR-LOOP PARTIAL WITNESS (CLASS-NEUTRAL).
//
// The out-of-band quarantine + witness for the for-desugar iterator loop
// `let mut acc=<c>; for x in s { <call-free, break-free body> } acc` over one
// immutable `&[T]` slice PARAMETER (sum_loop 8bb / count_pos 9bb). The recognizer
// (`prove::extract_iter_loop_function`) projects the iterator loop onto a GHOST-COUNTER
// index model with ZERO composition of `next()`'s theorem, via a four-link recognizer
// chain (region rooting on the sole `into_iter(s)` provenance; the def-path-pinned
// header `next()` Call with the G2-R result-provenance pin; the exhaustive Option
// dispatch; a ghost counter that counts completed `next()` calls) plus TWO named
// premises (P-ITER-CURSOR's pattern reused, and the NEW UNDISCHARGED [`P_ITER_COUNT`]).
//
// STRICTLY THINNER THAN INC1 (the adversarially-mandated honesty — this lane must NOT
// flip cluster verdicts): the certificate mints kernel obligation (I) ONLY — the
// loop-invariant instance `CounterInRange 0≤i ∧ i≤n` over the ghost counter, via
// [`loop_refinement_witness`] VERBATIM — UNDER the undischarged [`P_ITER_COUNT`] premise.
// There is NO analogue of INC1's obligation (II) (no `BoundsCheck` assert exists in the
// for-desugar caller — the element access lives inside `next()`'s fenced frame) and NO
// analogue of obligation (III) (the ghost counter has no MIR `CheckedAdd`; minting a
// discharge with no corresponding MIR assert would be claim inflation). NO MIR assert is
// discharged by this certificate: sum_loop's `Overflow(Add)` on `acc+*x` and count_pos's
// `Overflow(Add)` on `c+1` both ride the HAVOCKED accumulator channel, stay open safety
// VCs, so `function_safety_vcs_all_discharged(func)=false` for both exemplars,
// termination is NOT minted, and no reach-Return claim is made.
//
// FENCE COMPLIANCE BY CONSTRUCTION: the projected model mentions ONLY `Var(i_ghost)` and
// `Var(n_ghost)` — no IterRegion / IterHasNext / SemAdtReturn / call_result is
// instantiated, so `sem_adt_return_carries_entry_iter_handle` (and its `SemLoopFunction`
// sibling `sem_loop_function_carries_entry_iter_handle`) is vacuously false and nothing
// entry-Env-indexed is ever cross-instantiated. The ghost slots
// `i_ghost = body.locals.len()`, `n_ghost = +1` are OUTSIDE the MIR local index space,
// so no MIR statement can write them (the split-claim's "elided statements never write
// {i,n}" is STRUCTURAL, not frame-proved).
//
// Trust: HONEST FLOOR inc-2 (2026-07-23) — THE F12 STRUCTURAL REFUSAL (durable record; the
// twin of the record on `SemIterStep`). This block's ghost-vars-only premise stays TRUE
// PERMANENTLY, not by present accident: the "kernel-composed count conditional" that would
// have introduced the two-key symbols (`iter_seq`/`iter_len`/`iter_has_next2`) into the
// projected loop — falsifying this premise — was adversarially REFUSED and is STRUCTURALLY
// IMPOSSIBLE under the F12 grounder fence (`clean_ground.rs`, ~18554). `exec_loop`
// (mirsem.rs:23918) IS the grounded loop semantics over the Int ghost slots, and the fence
// bars the two-key symbols from the grounder, so the T-STEP surface can NEVER share an
// `exec_loop` term with the ghost counter. The count tie `n_ghost = iter_len(recv) =
// sliceLen(s)` is the D-INIT residue (NO bridge law permitted, `trustir_anchor.rs`:588/595)
// and can NEVER be a kernel equation; a mis-bound `n_ghost` would kernel-check a FALSE count.
// P-ITER-COUNT is therefore NOT kernel-composable in this architecture — the whole-trace
// count is a recognizer-trust premise (tie = D-INIT; direction = D-ORIENT) PERMANENTLY unless
// F12 is lifted. A future increment MUST confront F12 before re-attempting the composition;
// GATE-ITER-GEN-KEY-DISCIPLINE is landed as executable regression-protection
// (`admit_t_step_instantiation` + the wired `sem_loop_function_carries_entry_iter_handle`
// chokepoint guards) so any such attempt declines unless properly bound. Do not delete.
//
// TRIPWIRE (recorded per the INC1 open-risk carry-over): if a future increment makes
// `CalleeFact` shape-bearing, wiring `sem_adt_return_carries_entry_iter_handle` into the
// certificate-instantiation chokepoints becomes day-one load-bearing — INC2's G2
// normalizes callee resolution against the registry but composes NO theorem today.
// ===========================================================================
/// The named, UNDISCHARGED std-representation premise the iterator-loop projection carries
/// as an EXPLICIT hypothesis (the P-ITER-CURSOR pattern, but marked UNDISCHARGED): "an
/// iterator freshly minted by the pinned `<&[T]>::into_iter` from a frame-pinned immutable
/// slice param `s`, touched only by the pinned `slice::Iter::next` at a single call site,
/// returns `Some` on its (k+1)-th call iff `k < sliceLen(s)`, and `None` iff
/// `k = sliceLen(s)`." This — and only this — maps the Option-discriminant `SwitchInt`
/// edges onto the INC1 comparison guard `Lt(i,n)`. NOT establishable from the caller's MIR
/// without composing `next()`'s theorem; carried UNDISCHARGED (contrast the DISCHARGED
/// P-ITER-CURSOR cursor lane) and NAMED in the tier claim so the certificate never
/// overclaims. Its DIRECTION is guarded SOLELY by the recognizer's orientation pin
/// (`0=None→exit`, `1=Some→body`) because the kernel cannot check the premise's direction.
///
/// Trust: P-ITER-COUNT WITNESS DECORATION (2026-07-22). P-ITER-COUNT remains a SINGLE,
/// UNDISCHARGED WHOLE-TRACE premise — it is NOT retired, NOT split into separately
/// load-bearing residues, and NOT converted into a kernel-derived conclusion (the strong
/// "residue-shrink discharge" form was adversarially REFUTED on three counts: the
/// cross-generation glue is gate-1's violating pattern in premise form, the distance-init
/// premise at witnessed grade is the clause-(c)-forbidden address reading, and the
/// pre-loop-bypass caller shape falsifies the EXACTLY count). What lands is a per-link
/// RECOGNIZER WITNESS ([`IterCountPremiseWitness`]) that machine-checks each per-call /
/// entry-local INGREDIENT over the pinned dumps — the FULL step contract
/// [`P_ITER_COUNT_WITNESS_CONTRACT`] via D3, the whole-slice mint via D4, the callee value/
/// record lane status via D1/D2, the element-type match via D6, and the caller
/// LOOP-POSTDOMINATES-RETURN gate G8 — WITHOUT composing any of them into the whole-trace
/// count. The witness feeds only diagnostic surfaces (the tier claim text + the additive
/// `iter_premise_witnessed` column); it flips NO verdict / cluster / funnel bit.
pub const P_ITER_COUNT: &str = "P-ITER-COUNT";

/// Trust: P-ITER-COUNT WITNESS DECORATION (2026-07-22) — the BYTE-PINNED FULL per-call
/// step contract the D3 recognizer ([`crate::clean_ground::sem_iter_next_step_shape_of`])
/// witnesses over the pinned `slice::Iter::next` dump, and which the witnessed tier claim
/// names VERBATIM. This is the WIDENED text the premise-honesty adversarial gate mandated:
/// it states the ENTIRE conjunct list the ghost-to-real bridge consumes (guard domination,
/// discriminant polarity, no-other-receiver-writes, self.end-write-free), not merely the
/// stride-advance clause — so the witnessed strength is not silently stronger than the
/// stated text. It remains a NAMED, un-kernel-checked premise: the per-call step fact is
/// inherently two-Env, and a kernel-checked form additionally requires
/// GATE-ITER-REGION-NO-CROSS-INSTANTIATION's documented lift (`iter_region(recv,
/// generation)`), the residue-free bar this decoration does NOT reach.
pub const P_ITER_COUNT_WITNESS_CONTRACT: &str = "on every call, Some is returned iff entry \
    ptr != entry end (the dispatch discriminant matches the ptr!=end guard); on Some the SOLE \
    receiver write is the single one-stride ptr := PtrOffset(ptr,+1) store, with self.end \
    unchanged on all paths and no other receiver-field write and no reentrant call; on None \
    the receiver is write-free";

// ---------------------------------------------------------------------------
// Trust: W-ADDR increment 1 (2026-07-22) — the ADDRESS/PROVENANCE PREMISE FAMILY
// (P-ADDR-ALLOC / P-ADDR-EXTENT / P-ADDR-REFINE). NAMED, UNDISCHARGED memory-model
// premises the DIST-INIT consumer cites VERBATIM in its claim surface; they NAME
// address content but assert NOTHING at the kernel — the bridge equation H-OFF
// lives ONLY as the hypothesis `hOff` of `Trust.TrustIr.iterDistInit`
// (trustir_anchor.rs), never proven from MIR, never asserted, flipping NO verdict/
// cluster/funnel bit. The contract texts are BYTE-PINNED by the honesty probes and
// are the ONLY place the "one-past-the-end address reading" is written. Texts are
// std-EXACT per GATE-PREMISE-TEXT-STD-EXACT(W-ADDR): the len=0 dangling carve-out
// and the isize::MAX-vs-usize distinction match library/core/src/slice/raw.rs.
// ---------------------------------------------------------------------------
/// Trust: W-ADDR — the named allocation-layout premise (see the family header above).
pub const P_ADDR_ALLOC: &str = "P-ADDR-ALLOC";

/// Trust: W-ADDR — BYTE-PINNED P-ADDR-ALLOC contract. The one-contiguous-allocation claim is
/// SCOPED to `sliceLen(s) > 0`; the `sliceLen(s) = 0` case carries NO allocation-existence
/// claim (the base may be a dangling `NonNull::dangling()` in no allocation), matching
/// library/core/src/slice/raw.rs:17,20-24 exactly — an empty-slice instance therefore ships no
/// false std citation.
pub const P_ADDR_ALLOC_CONTRACT: &str = "for a frame-pinned immutable `&[T]`/`&[T; N]` \
    slice/array-ref PARAMETER s whose non-ZST scalar element has pinned byte size e \
    (scalar_pointee_byte_size; None declines): WHEN sliceLen(s) > 0 the referent occupies ONE \
    contiguous allocation (library/core/src/slice/raw.rs:17 — a slice never spans multiple \
    allocations), so the machine byte address of element i is base + i*e for every \
    0 <= i <= sliceLen(s), the i = sliceLen(s) address being one-past-the-end (never \
    dereferenced); WHEN sliceLen(s) = 0 NO allocation-existence claim is made — the base is \
    merely non-null and aligned and may be a dangling NonNull::dangling() lying in no \
    allocation (library/core/src/slice/raw.rs:20-24), the only address relation being the \
    degenerate base = one-past-the-end (start = end)";

/// Trust: W-ADDR — the named allocation-extent premise (see the family header above).
pub const P_ADDR_EXTENT: &str = "P-ADDR-EXTENT";

/// Trust: W-ADDR — BYTE-PINNED P-ADDR-EXTENT contract, claiming EXACTLY the std slice-validity
/// extent guarantee (library/core/src/slice/raw.rs:31-32): the total size is <= isize::MAX and
/// adding it to the base does not wrap the address space. It does NOT claim the base itself
/// stays within isize (addresses are usize-ranged — the deleted 'neither overflows isize' was
/// false on 32-bit/wasm32 where a valid base alone can exceed isize::MAX).
pub const P_ADDR_EXTENT_CONTRACT: &str = "the std slice-validity extent guarantee \
    (library/core/src/slice/raw.rs:31-32): the total size sliceLen(s)*e is no larger than \
    isize::MAX bytes, and adding that size to the base does not wrap around the address space; \
    NO bound on the base address itself is claimed (addresses are usize-ranged, so a valid \
    base may exceed isize::MAX on 32-bit/wasm32)";

/// Trust: W-ADDR — the named Int-carrier refinement premise (see the family header above).
pub const P_ADDR_REFINE: &str = "P-ADDR-REFINE";

/// Trust: W-ADDR — BYTE-PINNED P-ADDR-REFINE contract: at a D4-recognized whole-slice mint,
/// UNDER P-ADDR-ALLOC/EXTENT, the Int-carrier model refines machine addresses, yielding the
/// per-instance bridge equation H-OFF. H-OFF is a memory-model fact — NEVER establishable from
/// MIR, NEVER asserted — existing ONLY as `Trust.TrustIr.iterDistInit`'s undischarged
/// hypothesis, citable ONLY entry-locally at its mint.
pub const P_ADDR_REFINE_CONTRACT: &str = "at a D4-recognized whole-slice mint \
    (`end := PtrOffset(ptr, Len(s))` over the pinned into_iter dump), UNDER P-ADDR-ALLOC and \
    P-ADDR-EXTENT, the Int-carrier model refines machine addresses: sliceStart(s) denotes the \
    base address and ptrOffset(sliceStart s)(sliceLen s)(e) the one-past-the-end address of \
    s's referent, yielding the per-instance bridge equation H-OFF: \
    ptrOffset (sliceStart s) (sliceLen s) e = sliceStart s + sliceLen s * e. H-OFF is a \
    memory-model fact, NEVER establishable from MIR, NEVER asserted: it exists only as the \
    undischarged hypothesis of Trust.TrustIr.iterDistInit and is citable only entry-locally at \
    its mint (never across any receiver/cursor-field write)";

/// Trust: HONEST FLOOR inc-2 (2026-07-23) — the PER-FUNCTION classification of the
/// recognized accumulator's `Overflow(Add)` VC, computed at extraction from the G7
/// accumulator local's declared integer TYPE and its in-loop `CheckedAdd` update shape. It
/// keys the per-function overflow-falsifier text in [`IterLoopPartialCertificate::
/// tier_claim_base`] so that count_pos (an UNSIGNED `+1` counter whose value is bounded by
/// the iteration count — overflow INFEASIBLE) no longer surfaces sum_loop's REACHABLE
/// `s=[i32::MAX,1]` panic as its own overflow evidence (the honesty defect the claim-surface
/// adversarial verdict refuted). It flips NO verdict/cluster/funnel bit — it selects
/// certificate TEXT only, and the VC stays OPEN/undischarged in every case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccumulatorOverflowShape {
    /// A SIGNED value-accumulator whose in-loop `CheckedAdd` adds a NON-constant (element)
    /// operand — e.g. sum_loop's `sum += *x` over `i32`. Its `Overflow(Add)` VC has a
    /// REACHABLE panic: `s=[i32::MAX,1]` panics at `i=1` and never reaches `Return`.
    ReachableSignedValueAdd,
    /// An UNSIGNED accumulator whose in-loop `CheckedAdd` is a `+ 1` counter — e.g.
    /// count_pos's `c += 1` over `usize`. Its value is bounded by the iteration count
    /// (`≤ isize::MAX < usize::MAX`), so the `Overflow(Add)` VC is INFEASIBLE on this
    /// function (`count_pos(&[i32::MAX,1])` returns `2` and reaches `Return`); it stays
    /// undischarged ONLY because the value channel is havocked, NOT because a reachable
    /// panic exists.
    BoundedUnsignedCounter,
    /// Any other accumulator shape (a signed `+1` counter, an unsigned value-accumulator,
    /// or no recognized `CheckedAdd` update found). CONSERVATIVE: the VC is
    /// undischarged-because-havocked, but NO concrete reachable falsifier and NO
    /// infeasibility is asserted for this shape.
    Unclassified,
}

/// The GHOST-COUNTER-PROJECTED model of a recognized for-desugar iterator loop
/// `for x in s { <call-free, break-free body> }`. A DISTINCT `HavocProjected` type (NOT a
/// bare [`SemLoopFunction`]) so the projection can never leak in-band to the shared loop
/// consumers (out-of-band quarantine — mirrors [`SliceIndexLoopFunction`]). Consumed ONLY
/// by [`iter_loop_partial_witness`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IterLoopFunction {
    /// The ghost-counter-PROJECTED loop: body `[i := i+1]`, guard `Lt(i, n)`, synthesized
    /// invariant `CounterInRange { i, 0, n }`. Both `i_ghost` and `n_ghost` are GHOST env
    /// slots OUTSIDE the MIR local index space, so no MIR statement can write them BY
    /// CONSTRUCTION.
    pub projected: SemLoopFunction,
    /// The ghost counter env index (== `body.locals.len()`; outside the MIR local space).
    pub i_ghost: u64,
    /// The ghost bound env index (== `body.locals.len()+1`; models `sliceLen(s)`, the
    /// number of elements the pinned iterator yields under [`P_ITER_COUNT`]).
    pub n_ghost: u64,
    /// The named, UNDISCHARGED representation premise ([`P_ITER_COUNT`]) — carried in the
    /// certificate metadata, mirroring how P-ITER-CURSOR is carried, but marked
    /// undischarged (the honest conditional form).
    pub premise: &'static str,
    /// The def-path-pinned header `next()` callee (callee IDENTITY, shape-only — no
    /// theorem instantiated).
    pub next_key: String,
    /// The def-path-pinned `into_iter` callee that roots the iterator's sole provenance.
    pub into_iter_key: String,
    /// The frame-pinned immutable slice PARAM the bound `n` is rooted at (its length is a
    /// single entry-pinned symbolic value — this DISSOLVES the iter-region generation
    /// problem: nothing entry-time-indexed on the ITERATOR is ever mentioned).
    pub slice_param: usize,
    /// Trust: P-ITER-COUNT WITNESS (G8 anchors, ADDITIVE — the gate logic is unchanged).
    /// The caller-CFG blocks the recognizer already computed: the `next()` header block
    /// `bb_h`, the dispatch block `bb_s`, and the disc-0/None exit block `bb_exit`. Consumed
    /// ONLY by the G8 LOOP-POSTDOMINATES-RETURN caller gate of the witness bundle (they carry
    /// no proof authority themselves).
    pub header_block: trust_types::BlockId,
    pub dispatch_block: trust_types::BlockId,
    pub exit_block: trust_types::BlockId,
    /// Trust: HONEST FLOOR inc-2 (2026-07-23) — the per-function accumulator-overflow
    /// classification (from the G7 accumulator local's type + its `CheckedAdd` update).
    /// Keys the per-function overflow-falsifier text ONLY; flips no bit (see
    /// [`AccumulatorOverflowShape`]).
    pub accumulator_overflow: AccumulatorOverflowShape,
}

/// Trust: P-ITER-COUNT WITNESS DECORATION (2026-07-22) — the PER-LINK RECOGNIZER WITNESS
/// bundle. Every field is `true` in a minted witness (the bundle is `Some` ONLY when ALL
/// D-gates and G8 pass; a decline yields `None` and the reason is reported separately by
/// [`crate::prove::iter_count_premise_witness_decline_reason`]). It records the machine-
/// checked per-call / entry-local INGREDIENTS of the still-UNDISCHARGED whole-trace premise
/// [`P_ITER_COUNT`]; it carries NO proof authority and flips NO verdict/cluster/funnel bit.
///
/// FENCE COMPLIANCE (pinned by `iter_count_witness_mints_no_fenced_symbols`): every field is
/// a boolean / `u64` digest / a plain element-type name string — ZERO occurrences of
/// `iter_region`/`iter_has_next`/`IterRegion`/`sliceStart`/`ptrOffset` symbols. The D3/D4
/// recognizers scan the raw dumps and return fence-free structural descriptors; the exit
/// lemma is a pure Int-totality obligation over two fresh ghost `Var`s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IterCountPremiseWitness {
    /// D1 — the resolved `next()` def-path carries the EXACT slice-Iter VALUE-lane
    /// certificate (re-recognized over its pinned dump) with `function_ptr_offsets_all_
    /// discharged=true` and `requires==Some([])`, EXACT-only registry resolution.
    pub d1_next_value_lane: bool,
    /// D2 — the resolved `into_iter` def-path carries the EXACT inc-3 RECORD-lane certificate
    /// (its separate offset-discharge conjunct true), EXACT-only registry resolution.
    pub d2_into_iter_record_lane: bool,
    /// D3 — the STEP-shape re-recognition of `next()`'s sibling dump succeeded (the FULL
    /// per-call contract [`P_ITER_COUNT_WITNESS_CONTRACT`]), DIGEST-MATCHED to D1's dump.
    pub d3_next_step_shape: bool,
    /// D6 — the D3 and D4 stride pointees equal the loop's slice element type.
    pub d6_element_type_match: bool,
    /// D4 — the whole-slice MINT structural observation of `into_iter`'s dump succeeded.
    pub d4_into_iter_mint: bool,
    /// G8 — the caller-side LOOP-POSTDOMINATES-RETURN gate held (bb_h dominates Return, the
    /// sole-entry exit spine, and exactly ONE `_0` commit on Return-reaching Goto blocks).
    pub g8_loop_postdominates_return: bool,
    /// The Int-totality GHOST-MODEL exit lemma refuted modulo 3: `(0≤i ∧ i≤n ∧ ¬(i<n)) ⇒
    /// i=n` (via the #21 disequality-widening path). Extends obligation (I)'s ghost model
    /// with "at-exit i=n"; premise-conditional as ever, fence-free.
    pub exit_count_refuted_modulo_3: bool,
    /// Provenance digest of the pinned `next()` dump D1 re-recognized (and D3 re-scanned).
    pub next_dump_digest: u64,
    /// Provenance digest of the pinned `into_iter` dump D2/D4 observed.
    pub into_iter_dump_digest: u64,
    /// The witnessed stride/element type NAME (D6), e.g. `"Int { width: 32, signed: true }"`.
    pub element_type_name: String,
    /// Trust: W-ADDR increment 1 (2026-07-22) — the DIST-INIT address/provenance premise
    /// instance ([`crate::clean_ground::DistInitPremiseInstance`]), minted by
    /// [`crate::prove::iter_count_premise_witness`] when
    /// [`crate::clean_ground::iter_dist_init_premise_instance`] succeeds; `None` NEVER blocks
    /// the bundle (it is a diagnostic DECORATION at WITNESSED PREMISE grade — it flips no
    /// verdict/cluster/funnel bit and discharges nothing). FENCE COMPLIANCE (pinned by the
    /// UPDATED `iter_count_witness_fenced_symbols_only_in_dist_init`): the ONLY place a
    /// `sliceStart`/`ptrOffset` symbol may appear in the whole bundle is inside THIS field's
    /// kernel-rechecked `Trust.TrustIr.iterDistInit` theorem instance — every other field is a
    /// boolean / digest / element-type name.
    pub dist_init: Option<crate::clean_ground::DistInitPremiseInstance>,
}

/// The PARTIAL-TIER certificate a recognized iterator-for-loop mints — STRICTLY THINNER
/// than [`SliceIndexPartialCertificate`]: kernel obligation (I) ONLY (the loop-invariant
/// instance over the GHOST counter), UNDER the undischarged [`P_ITER_COUNT`] premise.
/// There is NO bounds-assert discharge field (no `BoundsCheck` assert exists in the
/// for-desugar caller) and NO counter-overflow discharge field (the ghost counter has no
/// MIR `CheckedAdd`) — those obligations DO NOT EXIST here, so their fields are ABSENT (a
/// vacuous guard→guard instance would be claim inflation). NO MIR assert is discharged:
/// the accumulator-overflow assert rides the havocked channel and stays OPEN.
#[derive(Debug, Clone)]
pub struct IterLoopPartialCertificate {
    /// The ghost-counter-projected loop this certifies.
    pub function: IterLoopFunction,
    /// (I) loopInvariantRule at `CounterInRange 0≤i ∧ i≤n` over the GHOST counter,
    /// kernel-checked modulo 3 (the INC1 [`loop_refinement_witness`] builder verbatim).
    pub invariant: RefinementVerdict,
    /// The TERMINATION half (loopRankTerminates + loopTotalCorrect, rank `toNat(n−i)`).
    /// `Some(verdict)` ONLY when `total_available` was true at mint time (the function's
    /// safety VCs are all discharged — the mandatory termination gate); `None` for the
    /// PARTIAL tier. For sum_loop/count_pos this is ALWAYS `None` (their accumulator
    /// overflow VCs are open), and even a future all-VCs-discharged run leaves termination
    /// conditional on P-ITER-COUNT's None-at-n direction (the tier claim says so).
    pub termination: Option<RefinementVerdict>,
    /// Trust: P-ITER-COUNT WITNESS DECORATION (2026-07-22) — the ADDITIVE, DIAGNOSTIC-ONLY
    /// per-link recognizer witness ([`IterCountPremiseWitness`]). `Some` ONLY when ALL
    /// D-gates (D1–D4, D6) AND the caller gate G8 pass over the pinned dumps; `None` in every
    /// registry-blind / dump-absent / declined run. It feeds ONLY [`Self::tier_claim`]'s TEXT
    /// and the additive `iter_premise_witnessed` diagnosis column — NEVER a verdict / cluster
    /// / funnel bit, and it does NOT change the invariant/termination obligations above.
    pub premise_witness: Option<IterCountPremiseWitness>,
}

impl IterLoopPartialCertificate {
    /// Whether the sole PARTIAL-tier kernel obligation (the invariant) checks modulo 3 —
    /// the tier this increment ships for sum_loop/count_pos.
    #[must_use]
    pub fn is_partial_modulo_3(&self) -> bool {
        matches!(self.invariant, RefinementVerdict::ProvenModulo3)
    }

    /// Whether a TERMINATION / total-correctness claim is being made (only under the
    /// mandatory gate: full safety-VC discharge). Always `false` for sum_loop/count_pos.
    #[must_use]
    pub fn termination_claimed(&self) -> bool {
        matches!(self.termination, Some(RefinementVerdict::ProvenModulo3))
    }

    /// The machine-readable CLAIM-SURFACE (mandatory honesty gate). Names, verbatim: the
    /// ghost-counter split-claim; the UNDISCHARGED [`P_ITER_COUNT`] premise; that this is
    /// STRICTLY THINNER than the slice-index lane (obligation I only); that NO MIR assert
    /// is discharged; the havocked value channel; and the falsifier `s=[i32::MAX,1]`.
    #[must_use]
    pub fn tier_claim(&self) -> String {
        let base = self.tier_claim_base();
        match &self.premise_witness {
            Some(_) => format!("{base} {}", Self::witnessed_addendum()),
            None => base,
        }
    }

    /// Trust: P-ITER-COUNT WITNESS — the WITNESSED-VARIANT addendum appended to the tier
    /// claim when a per-link witness bundle is attached. It names the byte-pinned
    /// [`P_ITER_COUNT_WITNESS_CONTRACT`] VERBATIM and states plainly, per the fence-compliance
    /// verdict, that the premise is NOT discharged.
    #[must_use]
    pub fn witnessed_addendum() -> String {
        format!(
            "PER-LINK WITNESS ATTACHED (diagnostic-only, flips no verdict): the D1/D2 callee \
             value/record-lane status + D3 step-shape re-recognition (\"{}\") + D4 whole-slice \
             mint observation + D6 element-type match + the caller G8 LOOP-POSTDOMINATES-RETURN \
             gate + the ghost-model Int-totality exit lemma ((0≤i ∧ i≤n ∧ ¬(i<n)) ⇒ i=n) ALL \
             hold over the pinned dumps. P-ITER-COUNT remains an UNDISCHARGED whole-trace \
             premise: the witness bundle machine-checks each per-link ingredient but the \
             cross-generation composition is NOT kernel-checked (it requires the \
             generation-re-keyed iter_region surface — the remaining documented fence lift; \
             the address/provenance surface landed 2026-07-22 at WITNESSED PREMISE grade: \
             DIST-INIT is carried as the kernel-rechecked conditional theorem \
             Trust.TrustIr.iterDistInit UNDER the undischarged hypotheses hOff/hLen resting on \
             P-ADDR-ALLOC / P-ADDR-EXTENT / P-ADDR-REFINE, memory-model facts never proven from \
             MIR; it discharges nothing and flips no verdict).",
            crate::mirsem::P_ITER_COUNT_WITNESS_CONTRACT
        )
    }

    /// Trust: HONEST FLOOR inc-2 (2026-07-23) — the PER-FUNCTION accumulator-overflow clause
    /// of the tier claim. The shipped literal minted ONE `falsifier s=[i32::MAX,1] panics
    /// sum_loop` sentence for BOTH sum_loop and count_pos; the claim-surface adversarial
    /// verdict refuted that as applied to count_pos (an `usize` accumulator with
    /// `c ≤ len ≤ isize::MAX < usize::MAX`, so `c+1` CANNOT overflow —
    /// `count_pos(&[i32::MAX,1])` returns `2` and REACHES `Return`). This selects the honest
    /// clause per [`IterLoopFunction::accumulator_overflow`]. The `Overflow(Add)` VC stays
    /// OPEN/undischarged in EVERY case — this flips no bit; only the falsifier TEXT differs.
    #[must_use]
    fn accumulator_overflow_clause(&self) -> &'static str {
        match self.function.accumulator_overflow {
            AccumulatorOverflowShape::ReachableSignedValueAdd => {
                "the accumulator-overflow assert rides the HAVOCKED channel and stays OPEN \
                 with a REACHABLE panic on this function (the signed value-accumulator \
                 overflows: falsifier s=[i32::MAX,1] panics at i=1 and never reaches Return)"
            }
            AccumulatorOverflowShape::BoundedUnsignedCounter => {
                "the accumulator-overflow Overflow(Add) VC is UNDISCHARGED-because-havocked \
                 and INFEASIBLE on this function (the accumulator is an UNSIGNED +1 counter \
                 whose value is bounded by the iteration count ≤ isize::MAX < usize::MAX, so \
                 c+1 cannot overflow — count_pos(&[i32::MAX,1]) returns 2 and reaches Return); \
                 it stays undischarged ONLY because the value channel is havocked, NOT because \
                 a reachable panic exists"
            }
            AccumulatorOverflowShape::Unclassified => {
                "the accumulator-overflow Overflow(Add) VC is UNDISCHARGED-because-havocked; \
                 NO concrete reachable falsifier and NO infeasibility is asserted for this \
                 accumulator shape (the value channel is havocked)"
            }
        }
    }

    /// The base (un-witnessed) claim surface — the pre-decoration text. The
    /// accumulator-overflow sentence is PER-FUNCTION (see [`Self::accumulator_overflow_clause`]);
    /// the rest of the surface is verbatim.
    #[must_use]
    fn tier_claim_base(&self) -> String {
        if self.termination_claimed() {
            "iterator-for-loop CONDITIONAL-TOTAL tier: loopInvariantRule (CounterInRange \
             0≤i ∧ i≤n over the GHOST counter i, n=sliceLen(s)) + loopRankTerminates/\
             loopTotalCorrect (rank toNat(n−i)), modulo 3, UNDER the UNDISCHARGED premise \
             P-ITER-COUNT (still conditional on its None-at-n direction). NO MIR assert is \
             discharged. The Some-payload/deref/accumulator value channel is HAVOCKED. The \
             ghost counter and the Some↔i<n guard bridge are recognizer-trust extensions of \
             the split-claim boundary."
                .to_string()
        } else {
            format!(
                "iterator-for-loop PARTIAL tier (STRICTLY THINNER than the slice-index lane — \
                 obligation I ONLY): loopInvariantRule (CounterInRange 0≤i ∧ i≤n over the GHOST \
                 counter i, n=sliceLen(s)) kernel-checked modulo 3, UNDER the UNDISCHARGED named \
                 premise P-ITER-COUNT (the pinned slice iterator yields Some exactly sliceLen(s) \
                 times — std's representation semantics, NOT establishable from this body). NO \
                 MIR assert is discharged: {clause}. NO BoundsCheck assert exists (the element \
                 access lives inside next()'s fenced frame). NO counter-overflow discharge is \
                 minted (the ghost counter has no MIR CheckedAdd). Termination NOT claimed. The \
                 Some-payload/deref/accumulator value channel is HAVOCKED (no ret-value/\
                 element-value claim). The ghost counter and the Some↔i<n guard bridge are \
                 recognizer-trust extensions of the split-claim boundary; the premise DIRECTION \
                 is guarded solely by the recognizer's orientation pin.",
                clause = self.accumulator_overflow_clause()
            )
        }
    }
}

/// A whole-function CALL-THEN-PUREOP adequacy certificate: the kernel-checked
/// per-call `callThenPureOpInstance` instance (never a new axiom — an application
/// of the SAME proven `callRefinesContract` [`call_return_adequacy_witness`] uses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallThenPureOpAdequacyCertificate {
    /// The recognized call-then-pureop shape.
    pub call_then_op: SemCallThenPureOp,
    /// The kernel verdict for the per-call `callThenPureOpInstance` instance.
    pub verdict: RefinementVerdict,
}

impl CallThenPureOpAdequacyCertificate {
    /// Whether the per-call instance kernel-checked modulo exactly 3.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

/// A whole-function CALL-RESULT-AWARE COMPOSITION adequacy certificate: the
/// kernel-checked per-call `callChainPureOpInstance` instance (never a new
/// axiom — an application of the SAME proven `callRefinesContract`
/// [`call_return_adequacy_witness`] uses, through the SAME PARAM-OPERAND
/// `wrap` generalization [`call_then_pureop_adequacy_witness`] uses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallChainPureOpAdequacyCertificate {
    /// The recognized call-chain-pureop shape.
    pub chain: SemCallChainPureOp,
    /// The kernel verdict for the per-call `callChainPureOpInstance` instance.
    pub verdict: RefinementVerdict,
}

impl CallChainPureOpAdequacyCertificate {
    /// Whether the per-call instance kernel-checked modulo exactly 3.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

/// A whole-function CALL-OP-CALL adequacy certificate: the kernel-checked
/// per-call-pair `callOpCallInstance` instance (never a new axiom — TWO nested
/// applications of the SAME proven `callRefinesContract` transport lemma
/// [`call_return_adequacy_witness`] uses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallOpCallAdequacyCertificate {
    /// The recognized call-op-call shape.
    pub call_op_call: SemCallOpCall,
    /// The kernel verdict for the per-call-pair `callOpCallInstance` instance.
    pub verdict: RefinementVerdict,
}

impl CallOpCallAdequacyCertificate {
    /// Whether the per-call-pair instance kernel-checked modulo exactly 3.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Trust: TWO-CALL CHAIN (`min_max`'s `a.min(b).max(c)`) — the certified-callee
// SEQUENTIAL-CALL COMPOSITION. Shape:
//
//   bb0: _t := Call(f, [args_f]) -> bb1          // inner call, dest an Int temp
//   bb1: _0 := Call(g, [.., _t, ..]) -> bb2      // outer call consumes _t as an arg
//   bb2: Return
//
// The single-call spine (`sem_call_return_of_mir`) requires EXACTLY ONE call;
// `sem_call_op_call_of_mir` (CALL-OP-CALL) requires `_0`'s write to be a PURE OP
// over two call results, but here `_0` is written DIRECTLY by the outer call and
// the inner result flows in as an ARGUMENT — so all four prior call recognizers
// decline. This section admits the composition additively.
//
// KERNEL SIDE — ZERO new axiom, ZERO new declaration. The witness is TWO
// per-call `callReturnInstance` transports (the EXISTING single-call machinery
// `call_return_adequacy_witness` mints), one for each call: (inner) `_t =
// call_result(CallF)`, (outer) `_0 = call_result(CallG)`. `call_result` is the
// opaque, uninterpreted-but-total projection — the SAME shape-faithful (not
// value-faithful) honesty tier the single-call lane already carries. The
// STRUCTURAL recognizer carries the chain connection (the inner temp is the
// outer call's argument, single-assigned, single-use, non-aliased); the kernel
// naming of the outer call reuses one of its OTHER (modeled) actual arguments,
// exactly as the single-call model already keys a call by its first arg alone.
//
// SCOPE (Int intermediate). The intermediate temp `_t` must be `Ty::Int` (the
// `min`/`max` result). A `Bool` or ADT intermediate (e.g. `checked_add(..)
// .is_some()`, whose intermediate is an `Option<T>` ADT threaded through a
// `Ref` + a second call taking `&_t`) is OUT OF FRAGMENT here — a named residue
// (documented in the report), not silently absorbed. The outer call must also
// have at least one MODELED (non-intermediate) argument to name its `Call.mk`
// by; an all-intermediate outer call (a unary `g(f(..))`) is likewise residue.
// ===========================================================================
/// Trust: TWO-CALL CHAIN — one actual argument of the OUTER call: either a
/// MODELED scalar operand (a parameter/const/field-read the existing
/// [`sem_call_arg_operand`] resolves) or the INTERMEDIATE marker (the inner
/// call's single-assigned result temp `_t`, threaded in as this argument). The
/// recognizer guarantees EXACTLY ONE `Intermediate` across the outer call's
/// arguments, and (via the whole-body use scan) that `_t` occurs NOWHERE else.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChainArg {
    /// A modeled scalar actual argument (param/const/field-read).
    Modeled(SemOperand),
    /// The inner call's result temp `_t`, consumed as this outer-call argument.
    Intermediate,
}

/// The recognized TWO-CALL CHAIN shape (`min_max`): a certified INNER call whose
/// result temp flows, single-use and non-aliased, into a certified OUTER call
/// that writes `_0`. Produced ONLY by [`sem_two_call_chain_of_mir`]
/// (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemTwoCallChain {
    /// The inner call `f` (resolved certified callee + FULLY modeled args).
    pub inner: SemCallReturn,
    /// The RESOLVED outer callee def-path (a key of the certified registry).
    pub outer_callee: String,
    /// The outer callee's registry index — the `Nat` callee-id its `Call.mk`
    /// instance names.
    pub outer_callee_id: u64,
    /// The outer call's actual arguments in program order: EXACTLY ONE is the
    /// [`ChainArg::Intermediate`] (the inner result temp `_t`), the rest are
    /// [`ChainArg::Modeled`] scalar operands (at least one — the naming arg).
    pub outer_args: Vec<ChainArg>,
    /// The intermediate temp `_t`'s integer type bound `(lo, hi)` — the SOUND
    /// fact "the inner callee's return, being `_t`'s integer type, lies in this
    /// range" that discharges the outer callee's `#[requires]` on the
    /// intermediate argument (see `two_call_chain_outer_requires_established`).
    pub intermediate_bound: (i128, i128),
}

impl SemTwoCallChain {
    /// The outer call's MODELED (non-intermediate) actual arguments, in order —
    /// the pieces certified by Lemma 1A and the naming arg of the outer
    /// `Call.mk` instance.
    #[must_use]
    pub fn outer_modeled_args(&self) -> Vec<SemOperand> {
        self.outer_args
            .iter()
            .filter_map(|a| match a {
                ChainArg::Modeled(op) => Some(op.clone()),
                ChainArg::Intermediate => None,
            })
            .collect()
    }
}

/// A whole-function TWO-CALL CHAIN adequacy certificate: TWO kernel-checked
/// per-call `callReturnInstance` transports (never a new axiom — each is an
/// application of the SAME proven `callRefinesContract`
/// [`call_return_adequacy_witness`] uses).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoCallChainAdequacyCertificate {
    /// The recognized two-call-chain shape.
    pub chain: SemTwoCallChain,
    /// The kernel verdict for the INNER call's `callReturnInstance` instance.
    pub inner_verdict: RefinementVerdict,
    /// The kernel verdict for the OUTER call's `callReturnInstance` instance.
    pub outer_verdict: RefinementVerdict,
}

impl TwoCallChainAdequacyCertificate {
    /// Whether BOTH per-call instances kernel-checked modulo exactly 3.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.inner_verdict, RefinementVerdict::ProvenModulo3)
            && matches!(self.outer_verdict, RefinementVerdict::ProvenModulo3)
    }
}

// ===========================================================================
// Trust: CALL-THEN-PROJECT (`overflowing_add(a,b).0`) — a TUPLE-returning
// certified call whose result's SINGLE field is projected into `_0`. Shape:
//
//   bb0: _t := Call(g, [args]) -> bb1            // dest a Tuple temp `(T, U, ..)`
//   bb1: _0 := Use(Copy/Move _t.Field(i))        // sole use: one field projection
//        Return
//
// `sem_call_return_of_mir` declines at its bare-Int-dest gate (the dest is a
// Tuple), and `_0`'s write is a PROJECTED use, not a bare passthrough. This
// section admits the field-projected return additively.
//
// KERNEL SIDE — ZERO new axiom, ZERO new declaration. The witness reuses the
// EXISTING `call_then_pureop_instance_type`/`_proof` with the wrap `wrap(x) =
// idx_elem(x, i)` — the EXACT opaque total selector `SemOperand::Field`'s own
// denotation grounds through (`MIRSEM_IDX_ELEM`, registered in `mirsem_env`).
// The return denotes `idx_elem(call_result C[ret], i)`: field `i` is SOME total
// function of the call — shape-faithful, not value-faithful (we never claim
// field 0 of `overflowing_add` equals `(a+b) mod 2^N`, only that it is that
// call's field-`i` component). The field index is read from the MIR, so a
// certificate claiming field 0 of a field-1 projection would name the WRONG
// selector key and the exact-statement kernel binding fails closed.
// ===========================================================================
/// The recognized CALL-THEN-PROJECT shape (`overflowing_add(a,b).0`): a
/// certified call to a TUPLE-returning callee whose result temp's SOLE use is a
/// single `Field(i)` projection into `_0`. Produced ONLY by
/// [`sem_call_then_project_of_mir`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCallThenProject {
    /// The recognized call (resolved certified callee + modeled args).
    pub call: SemCallReturn,
    /// The projected tuple-field index `i` (read from the MIR — the kernel
    /// selector key; a mismatched claim fails the exact-statement binding).
    pub field: u64,
}

/// A whole-function CALL-THEN-PROJECT adequacy certificate: the kernel-checked
/// per-call `callThenProjectInstance` (never a new axiom — the SAME proven
/// `callRefinesContract`, wrapped by the `idx_elem` field selector).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallThenProjectAdequacyCertificate {
    /// The recognized call-then-project shape.
    pub proj: SemCallThenProject,
    /// The kernel verdict for the per-call `callThenProjectInstance` instance.
    pub verdict: RefinementVerdict,
}

impl CallThenProjectAdequacyCertificate {
    /// Whether the per-call instance kernel-checked modulo exactly 3.
    #[must_use]
    pub fn is_modulo_3(&self) -> bool {
        matches!(self.verdict, RefinementVerdict::ProvenModulo3)
    }
}

// Every shape type, contract string, `impl` and import the families share stays
// here: the families are descendant modules, so they keep access to private
// fields and private consts without any visibility change. Each family is
// re-exported flat, so `mirsem::<name>` resolves exactly as it did when this
// module was a single file.
mod semantics_env;
mod adequacy;
mod lift_mir;
mod safety_overflow;
mod safety_bounds_div;
mod safety_signed;
mod vc_faithful;
mod call_lift;
mod ptr_spine;
mod return_lift;
mod adt_shapes;
mod adt_compose;
mod function_witness;
mod refinement;
mod loops;
mod loop_instances;
mod termination;
mod loop_postconditions;
mod call_contracts;
mod cfg_semantics;
mod open_world;
mod call_instances;

pub use semantics_env::*;
pub use adequacy::*;
pub use lift_mir::*;
pub use safety_overflow::*;
pub use safety_bounds_div::*;
pub use safety_signed::*;
pub use vc_faithful::*;
pub(crate) use call_lift::*;
pub(crate) use ptr_spine::*;
pub(crate) use return_lift::*;
pub use adt_shapes::*;
pub use adt_compose::*;
pub use function_witness::*;
pub use refinement::*;
pub use loops::*;
pub use loop_instances::*;
pub use termination::*;
pub use loop_postconditions::*;
use call_contracts::*;
use cfg_semantics::*;
pub use open_world::*;
pub use call_instances::*;

/// Trust: OPAQUE-CHAIN ADT-RETURN reduced test fixtures. These preserve the
/// audited control/data-flow shapes with internally coherent simplified type
/// graphs; they are not substitutes for the separately hash-pinned real dump
/// corpus, whose richer recursive type metadata must pass the production
/// assignment gate independently.
#[cfg(test)]
pub(crate) mod opaque_fixtures;
#[cfg(test)]
mod tests;
// ---------------------------------------------------------------------------
// Trust: W6 CLOSURE-COMPOSITION recognizer tests (increment 1, 2026-07-18).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod w6_map_compose_recognizer_tests;
// ---------------------------------------------------------------------------
// Trust: RECORD-WITNESS inc-2 (ok/err DowncastField + value-transparent drop-ladder
// epilogue, 2026-07-22) — recognizer-level probes over the REAL harvested
// `Result::<T,E>::ok`/`err` dumps. A separate module (kept off the sibling record-witness
// increment-1 suites). The mandatory KERNEL disjointness probe lives in `trustir_adt`.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod record_inc2_recognizer_tests;
