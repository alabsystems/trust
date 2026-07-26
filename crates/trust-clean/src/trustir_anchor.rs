// trust-clean/trustir_anchor.rs — RE-ANCHOR (goal item 1, Phase 0 POC + the
// STRAIGHT-LINE increment): relocate the faithfulness spec OFF the bespoke
// `Trust.MirSem` model ONTO a Clean denotation KEYED TO trust-ir's UNIVERSAL IR
// syntax.
//
// WHY THIS EXISTS.
// `mirsem.rs` pins `Trust.MirSem.{Operand,Rvalue,BinOp,eval,eval_rvalue}` — a
// MIR operational semantics INVENTED for trust-clean. The audit finding: that
// spec is a *trusted hand-spec*. There is no link tying `Trust.MirSem.BinOp.Add`
// to anything the rest of the toolchain (trust-cg, trust-mc, trust-ir) agrees
// on; trust-clean both writes the spec AND checks against it.
//
// THE RE-ANCHOR PRINCIPLE.
// trust-ir is the universal proof-carrying IR: `trust_ir::BinOp` (Add | Sub |
// Mul | SDiv | …) is the SHARED instruction vocabulary that trust-cg consumes
// and trust-mc/trust-wp reason over. If the faithfulness refinement is stated
// RELATIVE TO a denotation of *that* syntax — `Trust.TrustIr.BinOp` whose
// constructors are NAMED FOR and IN ONE-TO-ONE CORRESPONDENCE WITH
// `trust_ir::inst::BinOp` — then the trusted spec is no longer trust-clean's
// private MirSem; it is a denotation of the contract every t* tool already
// shares.
//
// WHAT THIS POC PROVES (additive; touches no MirSem decl, no vc_refute.rs).
// For a SIMPLE straight-line scalar binary body `f(a, b) = a OP b` (OP ∈ {Add,
// Sub, Mul, SDiv}):
//
//   1. A Clean inductive `Trust.TrustIr.BinOp` with constructors named EXACTLY
//      `Add`/`Sub`/`Mul`/`SDiv` (the trust-ir variant names — `trust_ir_name`
//      below is the bijection, verified against `trust_ir::inst::BinOp`).
//   2. A Clean denotation `Trust.TrustIr.evalBin : Env → BinOp → Nat → Nat → Int`
//      reflecting a binary op over two PARAMETER operands (the `Var i`/`Var j`
//      slots), folding each `BinOp` constructor to the prelude's reducible
//      `Int.add`/`Int.sub`/`Int.mul` (and the opaque `Int.div` for `SDiv`).
//   3. The REFINEMENT theorem, kernel-checked modulo 3:
//
//        ∀ (a b : Int), Trust.TrustIr.evalBin E OP 0 1 = ground_int(<a OP b>)
//
//      where the RHS is the EXACT term the LIVE `clean_ground::ground_int`
//      emits for the reflected `Formula::{Add,Sub,Mul,Div}(Var "_1", Var "_2")`,
//      and E is the env binding param 0↦a, 1↦b. Both sides ι/δ-reduce to the SAME
//      `Int.<op> a b`, so the proof is `Eq.refl` AT that grounded term — a
//      GENUINE refinement (its STATEMENT relates the trust-ir denotation to the
//      live grounder; it is NOT `Eq.refl` of a tautology — a WRONG claim, e.g.
//      evalBin Add = ground_int(<a SUB b>), is REJECTED by the kernel, which
//      `trustir_refinement_fail_closed` asserts).
//
// WHAT THE STRAIGHT-LINE INCREMENT ADDS (additive; still no MirSem/vc_refute edit).
// The POC's single-binary `evalBin` is now a full STRAIGHT-LINE denotation family
// keyed to the `trust_ir::Inst` arithmetic subset (`Copy`/`BinOp`/`UnOp`):
//
//   * OPERANDS — `Trust.TrustIr.Operand` (`Var i | Const c`) + `evalOperand : Env →
//     Operand → Int` (Var i → e i; Const c → c). `check_operand_refinement` proves
//     `evalOperand E op = ground_int(op.to_formula())` modulo 3.
//   * RVALUES — `Trust.TrustIr.Rvalue` (`Use op | BinaryOp op a b | UnaryOp op a`) +
//     `evalRvalue : Env → Rvalue → Int`. `UnOp` is `Trust.TrustIr.UnOp` (`Neg | Not`,
//     keyed to `trust_ir::inst::UnOp`). `check_rvalue_refinement` proves the
//     GROUNDER-CONNECTED arms (`Use`/`BinaryOp`/`UnaryOp Neg`) modulo 3.
//   * STATEMENT SEQUENCE — `Trust.TrustIr.Stmt` (`Assign i rvalue`) + `set` +
//     `evalBody : Env → List Stmt → Env`, the env-threading operational STEP (the
//     Clean analogue of trust-ir's `stepBlock`/`stepN` for the assignment fragment).
//   * BODY REFINEMENT (the headline) — `check_body_refinement` proves, modulo 3:
//
//        ∀ x⃗, evalOperand (evalBody E stmts) (Var ret) = ground_int(<inlined return>)
//
//     for a multi-statement straight-line body (e.g. `_2 := a+b; _3 := _2*c; ret _3`,
//     inlined `Mul(Add(a,b),c)`). This is GENUINE and GROUNDER-CONNECTED: the LHS runs
//     the SSA trace through `evalBody` (each `set`s its temp to `evalRvalue`), and its
//     ι/δ-reduction (env application → `set`-lookup via `Nat.beq i i → true`, nested
//     `evalRvalue`s) reconstructs EXACTLY the nested `Int.<op>` tree the LIVE grounder
//     independently emits for the inlined return formula. It is NOT `Eq.refl` of a
//     tautology — `trustir_body_refinement_fail_closed` asserts a WRONG inlined formula
//     (Mul body claimed to ground as Add) is REJECTED by the kernel.
//
// THE HONEST GAP (documented, not hidden).
//   * trust-ir's operational semantics LIVES IN LEAN (`first-party/trust-ir/
//     lean/trust_ir-semantics/TrustIr/Semantics/Arith.lean::semIntBinOp`), NOT in
//     Clean. There is no Lean→Clean kernel bridge in the live pipeline (Trust
//     kernel-checks in Clean). So this POC DEFINES the trust-ir denotation in
//     Clean (`Trust.TrustIr.evalBin`) — it does not IMPORT trust-ir's Lean
//     `semIntBinOp`. The faithfulness is therefore "Clean-denotation-of-trust-ir-
//     syntax", relocated from MirSem; the REMAINING trust gap is the Lean↔Clean
//     agreement of the two trust-ir denotations (a separate, future bridge).
//   * trust-ir's Lean `semIntBinOp Add = wrap (lhs + rhs)` is MODULAR (width-
//     aware). This POC's `evalBin Add = Int.add` is UNBOUNDED — sound EXACTLY as
//     MirSem's grounding is sound: the unbounded `Int.add` matches the modular
//     value under the NoOverflow obligation, which the L0 overflow VC discharges
//     SEPARATELY (see `mirsem::register_uadd_overflows`). The width/wrap layer is
//     out of POC scope and noted as the next step toward a full re-anchor.
//   * `UnOp::Not` (bitwise complement) has NO integer arm in the live grounder
//     (`Formula::Not` is BOOL-sorted only). So `Not` is modeled with the opaque
//     `Trust.TrustIr.bnot` and its refinement (`check_rvalue_refinement_model`) is
//     against the trust-ir DENOTATION, not the live grounder — GENUINE + fail-closed,
//     but NOT grounder-connected. `Neg` IS grounder-connected (live `F::Neg` arm).
//     Adding a live integer-`Not` grounder arm is deferred (it would edit
//     `clean_ground.rs`, kept untouched here).
//   * CONTROL FLOW + LOOPS remain the BULK of the re-anchor: this increment covers
//     only the STRAIGHT-LINE (assignment + return) fragment. Branches (`CondBr`),
//     `Switch`, and loops (`stepN` fixpoints) — and the §6 pipeline witness switch-
//     over + the MirSem teardown — are the next steps (see
//     reports/trustir-reanchor-scope.md §2 steps 3–5).
//
// SOUNDNESS DISCIPLINE (mirrors mirsem.rs exactly).
//   * Inductive + denotation + refinement all kernel-check with `axiom_deps ⊆
//     {propext, Quot.sound, Classical.choice}` — modulo exactly 3 axioms, no 4th,
//     no opaque/sorry. Each builder returns the kernel's own `axiom_deps` verdict.
//   * Fail-closed: a deliberately-wrong refinement (claim Add reduces to the Sub
//     grounding) MUST NOT prove. `trustir_refinement_fail_closed` asserts it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::HashMap;

use clean_kernel::{
    BinderData, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, LevelVec, Name, TypeChecker,
};
#[cfg(test)]
use clean_kernel::ExprKind;

use crate::clean_ground::ground_int;

// ---------------------------------------------------------------------------
// Canonical Clean names — the trust-ir-keyed anchor (parallel to MIRSEM_*)
// ---------------------------------------------------------------------------

/// The trust-ir binary-op inductive pinned in Clean. Its constructors are NAMED
/// FOR `trust_ir::inst::BinOp` (the universal IR's op vocabulary), so the
/// faithfulness spec is keyed to the shared contract, not to a trust-clean
/// invention. The supported fragment is `Add | Sub | Mul | SDiv | SRem | LShr`.
pub const TRUSTIR_BINOP: &str = "Trust.TrustIr.BinOp";
pub const TRUSTIR_BINOP_ADD: &str = "Trust.TrustIr.BinOp.Add";
pub const TRUSTIR_BINOP_SUB: &str = "Trust.TrustIr.BinOp.Sub";
pub const TRUSTIR_BINOP_MUL: &str = "Trust.TrustIr.BinOp.Mul";
/// `SDiv : BinOp` — trust-ir's signed division; grounds to the prelude's opaque
/// (non-axiom) `Int.div`, matching `ground_int`'s `F::Div` arm.
pub const TRUSTIR_BINOP_SDIV: &str = "Trust.TrustIr.BinOp.SDiv";
/// `SRem : BinOp` — Trust: witness-tier Rem arm — trust-ir's signed (TRUNCATED)
/// remainder; grounds to the prelude's opaque (non-axiom) `Int.mod`, matching
/// `ground_int`'s `F::Rem` arm and trust-ir's `semIntBinOp .SRem` (Arith.lean's
/// `Int.mod sl sr` — the T-rounding rustc's `%` uses; the M3 differential pinned
/// this three-way at the value tier). MIR `Rem` translates onto `SRem`: for
/// SIGNED operands they agree by definition; for UNSIGNED operands the values are
/// nonnegative, where SRem and URem coincide pointwise (`Int.mod a b` with
/// `a, b ≥ 0` IS the unsigned remainder), so the map is honest for both — the
/// unsigned story is a coincidence-of-semantics on the nonnegative fragment,
/// documented, not an assumption.
pub const TRUSTIR_BINOP_SREM: &str = "Trust.TrustIr.BinOp.SRem";
/// `LShr : BinOp` — Trust: M6 rung 6, SHR→TRUST-IR ANCHOR relocation — trust-ir's
/// UNSIGNED (logical) right shift; grounds to the Opaque (non-axiom) `Int.shiftRight`
/// (the SAME carrier `mirsem::register_int_bitwise`'s Shr arm registers on the MirSem
/// side — see `register_int_shr` below), matching `ground_int`'s `F::Pred("Int.shiftRight",
/// [a,b])` arm (the BITWISE SHAPE LANE's registered opaque-application carrier). MIR
/// `Shr` translates onto `LShr` ONLY for a PROVABLY-UNSIGNED shifted value and amount
/// (`Int.shiftRight`'s unbounded `a / 2^n` floor denotation coincides with the machine
/// `>>` exactly on that fragment — mirrors mirsem's `SemBinOp::Shr` unsigned-only gate,
/// re-applied at the call site — see `prove::straight_line_ir_body`'s `to_ir_binop`).
/// trust-ir's SIGNED (arithmetic) shift-right — `AShr` — has floor-on-negatives
/// semantics that is NOT this denotation and stays UNMODELED here (named residue: a
/// signed `>>` fails closed on this lane too, exactly as on the MirSem lane).
pub const TRUSTIR_BINOP_LSHR: &str = "Trust.TrustIr.BinOp.LShr";
/// `And : BinOp` — Trust: M6 rung 9, ANCHOR BitAnd — trust-ir's bitwise AND
/// (`trust_ir::inst::BinOp::And`, the real variant name — NOT `BitAnd`; MIR's
/// `BinOp::BitAnd` opcode is the source shape, but the trust-ir syntax spells the
/// op `And`, mirroring how `LShr`/`AShr` are named for trust-ir's OWN split rather
/// than MIR's single `Shr`). Grounds to the Opaque (non-axiom) `Int.land` (the
/// SAME carrier `mirsem::register_int_bitwise`'s `BitAnd` arm registers on the
/// MirSem side — see `register_int_land` below), matching `ground_int`'s
/// `F::Pred("Int.land", [a,b])` arm (the BITWISE SHAPE LANE's registered
/// opaque-application carrier established for MirSem, reused here unchanged).
pub const TRUSTIR_BINOP_AND: &str = "Trust.TrustIr.BinOp.And";
pub const TRUSTIR_BINOP_REC: &str = "Trust.TrustIr.BinOp.rec";

/// `Trust.TrustIr.evalBin : Env → BinOp → Nat → Nat → Int` — the Clean
/// denotation of a binary op over two PARAMETER operands. `evalBin E op i j`
/// folds `op` (via `BinOp.rec`) to `Int.<op> (E i) (E j)`. `Env = Nat → Int`
/// is the same parameter-binding convention as `Trust.MirSem.eval`.
pub const TRUSTIR_EVAL_BIN: &str = "Trust.TrustIr.evalBin";

// ---------------------------------------------------------------------------
// STRAIGHT-LINE FRAGMENT (this increment) — the trust-ir `Operand`/`UnOp`/
// `Rvalue`/`Stmt` denotation, keyed to `trust_ir::inst` and threaded by `evalBody`.
// ---------------------------------------------------------------------------

/// `Trust.TrustIr.Operand` — the SSA operand inductive. `Var i` is an SSA value
/// reference (`trust_ir`'s `Operand`/`ValueId`, used by `Inst::Copy`); `Const c`
/// is a literal (`Inst::Const` of a `Constant::Int`); `Field paramIdx fld` (Trust:
/// field-read leaf) is a struct-FIELD READ `(*paramIdx).fld` on an immutable-reference
/// PARAMETER, modeled by REUSE of the opaque total `idxElem` selector (see
/// [`TRUSTIR_IDX_ELEM`]) — the trust-ir analogue of `mirsem::SemOperand::Field`'s reuse
/// of `idx_elem`. Every constructor is non-recursive over the prelude's axiom-free
/// `Nat`/`Int`, so `Operand`'s own axiom closure stays `⊆ {propext, Quot.sound,
/// Classical.choice}`.
pub const TRUSTIR_OPERAND: &str = "Trust.TrustIr.Operand";
pub const TRUSTIR_OPERAND_VAR: &str = "Trust.TrustIr.Operand.Var";
pub const TRUSTIR_OPERAND_CONST: &str = "Trust.TrustIr.Operand.Const";
pub const TRUSTIR_OPERAND_FIELD: &str = "Trust.TrustIr.Operand.Field";
/// Trust: ptr-spine call-arg leaf — `Index : Operand → Operand → Operand`, RECURSIVE
/// in both fields (mirrors `Trust.MirSem.Operand.Index`'s already-proven encoding —
/// `mirsem::register_operand_inductive`'s `index_ctor` — byte-for-byte, ported onto
/// `Trust.TrustIr.Operand` with trust-ir's OWN `idxElem` opaque). See
/// [`IrOperand::Index`]'s doc.
pub const TRUSTIR_OPERAND_INDEX: &str = "Trust.TrustIr.Operand.Index";
/// Trust: ptr-spine call-arg leaf — `Len : Operand → Operand`, RECURSIVE in its one
/// field. Mirrors `Trust.MirSem.Operand.Len`. See [`IrOperand::Len`]'s doc.
pub const TRUSTIR_OPERAND_LEN: &str = "Trust.TrustIr.Operand.Len";
pub const TRUSTIR_OPERAND_REC: &str = "Trust.TrustIr.Operand.rec";
/// `Trust.TrustIr.evalOperand : Env → Operand → Int` (Var i → e i; Const c → c;
/// Field paramIdx fld → idxElem (e paramIdx) (Int.ofNat fld) — Trust: field-read leaf;
/// Index s i → idxElem (eval e s) (eval e i); Len s → sliceLen (eval e s) — Trust:
/// ptr-spine call-arg leaf).
pub const TRUSTIR_EVAL_OPERAND: &str = "Trust.TrustIr.evalOperand";

/// `Trust.TrustIr.UnOp` — the unary-op inductive. `Neg` is `trust_ir::inst::UnOp::Neg`
/// (integer negation; grounds via the live `ground_int` `F::Neg` arm). `Not` is
/// `UnOp::Not` (bitwise complement; modeled by the opaque `Trust.TrustIr.bnot`, see
/// the module note — it has NO live-grounder Int arm, so its refinement is against the
/// denotation only, NOT grounder-connected).
pub const TRUSTIR_UNOP: &str = "Trust.TrustIr.UnOp";
pub const TRUSTIR_UNOP_NEG: &str = "Trust.TrustIr.UnOp.Neg";
pub const TRUSTIR_UNOP_NOT: &str = "Trust.TrustIr.UnOp.Not";
pub const TRUSTIR_UNOP_REC: &str = "Trust.TrustIr.UnOp.rec";
/// The opaque bitwise-complement selector for `UnOp::Not` (the `idx_elem` pattern:
/// `Opaque`, NOT an `Axiom`, so a term naming it carries no non-foundational axiom).
pub const TRUSTIR_BNOT: &str = "Trust.TrustIr.bnot";

/// `Trust.TrustIr.Rvalue` — the straight-line rvalue inductive:
/// `Use op | BinaryOp op a b | UnaryOp op a`. Mirrors the `trust_ir::Inst`
/// arithmetic subset (`Copy`, `BinOp`, `UnOp`).
pub const TRUSTIR_RVALUE: &str = "Trust.TrustIr.Rvalue";
pub const TRUSTIR_RVALUE_USE: &str = "Trust.TrustIr.Rvalue.Use";
pub const TRUSTIR_RVALUE_BIN: &str = "Trust.TrustIr.Rvalue.BinaryOp";
pub const TRUSTIR_RVALUE_UN: &str = "Trust.TrustIr.Rvalue.UnaryOp";
/// `Cmp (op : CmpOp) (a b : Operand) : Rvalue` — Trust: M6 rung 9, COMPARE-AS-VALUE
/// — a comparison used as a Bool-typed VALUE (not a `Switch` branch guard):
/// `_0 := Eq(_2, 0); return _0`. ADDITIVE fourth constructor, FLAT in `a`/`b` (both
/// plain `Operand`s, not recursive `Rvalue`s — unlike `Trust.MirSem.Rvalue.Cmp`'s
/// recursive design, this anchor's straight-line fragment already threads nested
/// sub-computations through genuine SSA temps via `evalBody`/`List Stmt`, so the
/// compare's own operands only ever need to be flat `Var`/`Const`/`Field` leaves —
/// see [`IrRvalue::Cmp`]'s doc). Requires `CmpOp` registered BEFORE `Rvalue`.
pub const TRUSTIR_RVALUE_CMP: &str = "Trust.TrustIr.Rvalue.Cmp";
pub const TRUSTIR_RVALUE_REC: &str = "Trust.TrustIr.Rvalue.rec";
/// `Trust.TrustIr.evalRvalue : Env → Rvalue → Int`.
pub const TRUSTIR_EVAL_RVALUE: &str = "Trust.TrustIr.evalRvalue";

/// `Trust.TrustIr.Stmt` — a single SSA assignment `Assign : Nat → Rvalue → Stmt`
/// (`_i := rvalue`). A straight-line body is a `List Stmt`.
pub const TRUSTIR_STMT: &str = "Trust.TrustIr.Stmt";
pub const TRUSTIR_STMT_ASSIGN: &str = "Trust.TrustIr.Stmt.Assign";
pub const TRUSTIR_STMT_REC: &str = "Trust.TrustIr.Stmt.rec";
/// `Trust.TrustIr.set : Env → Nat → Int → Env` — the point-wise env update.
pub const TRUSTIR_SET: &str = "Trust.TrustIr.set";
/// `Trust.TrustIr.evalBody : Env → List Stmt → Env` — the operational step of a
/// straight-line trace: left-fold the env through the assignments. The Clean
/// analogue of trust-ir's `stepBlock`/`stepN` for the assignment-only fragment.
pub const TRUSTIR_EVAL_BODY: &str = "Trust.TrustIr.evalBody";

// ---------------------------------------------------------------------------
// CONTROL-FLOW FRAGMENT (this increment) — the trust-ir `CmpOp`/`Cond`/`Term`/
// `Block`/`Cfg` denotation, keyed to trust-ir's basic-block + terminator vocabulary
// and executed by `evalCfg` (the Clean analogue of trust-ir's stepBlock-across-blocks).
// ---------------------------------------------------------------------------

/// `Trust.TrustIr.CmpOp` — the integer-comparison-op inductive used by a `Switch`
/// discriminant. Keyed to `trust_ir::inst::BinOp`'s comparison fragment
/// (`Lt|Le|Eq|Ne|Gt|Ge` — trust-ir spells these as the `ICmp` predicates; the bijection
/// is `TrustIrCmpOp::trust_ir_name`). `evalCond` grounds each to the SAME Bool term
/// `clean_ground::ground_bool` emits (`decide (Int.lt …)`, `Int.beq …`, …).
pub const TRUSTIR_CMPOP: &str = "Trust.TrustIr.CmpOp";
pub const TRUSTIR_CMPOP_LT: &str = "Trust.TrustIr.CmpOp.Lt";
pub const TRUSTIR_CMPOP_LE: &str = "Trust.TrustIr.CmpOp.Le";
pub const TRUSTIR_CMPOP_EQ: &str = "Trust.TrustIr.CmpOp.Eq";
pub const TRUSTIR_CMPOP_NE: &str = "Trust.TrustIr.CmpOp.Ne";
pub const TRUSTIR_CMPOP_GT: &str = "Trust.TrustIr.CmpOp.Gt";
pub const TRUSTIR_CMPOP_GE: &str = "Trust.TrustIr.CmpOp.Ge";
pub const TRUSTIR_CMPOP_REC: &str = "Trust.TrustIr.CmpOp.rec";

/// `Trust.TrustIr.Cond` — the branch-discriminant inductive `Cmp (op : CmpOp) (a b :
/// Operand)`. The Clean analogue of the boolean comparison temp a trust-ir `SwitchInt`
/// branches on.
pub const TRUSTIR_COND: &str = "Trust.TrustIr.Cond";
pub const TRUSTIR_COND_CMP: &str = "Trust.TrustIr.Cond.Cmp";
pub const TRUSTIR_COND_REC: &str = "Trust.TrustIr.Cond.rec";
/// `Trust.TrustIr.evalCond : Env → Cond → Bool` — grounds byte-identically to
/// `clean_ground::ground_bool` over the corresponding comparison `Formula`.
pub const TRUSTIR_EVAL_COND: &str = "Trust.TrustIr.evalCond";

/// `Trust.TrustIr.Term` — the basic-block TERMINATOR inductive, keyed to trust-ir's
/// terminator vocabulary:
///
/// ```text
/// inductive Term : Type where
///   | Goto   : Nat → Term                       -- unconditional jump to bb
///   | Switch : Cond → Nat → Nat → Term          -- 2-way bool switch: cond ? thenBB : elseBB
///   | Return : Operand → Term                   -- return the operand
/// ```
///
/// The `Switch` here is the BOOLEAN two-way form a guarded MIR return uses (`SwitchInt`
/// on a `bool` comparison temp: the FALSE arm is `elseBB`, the TRUE arm is `thenBB`).
/// The general N-way `Switch operand [(value,bb)] default` is the syntactic super-form;
/// the grounder-connected branch refinement targets this 2-way bool form because that is
/// EXACTLY the shape the live `clean_ground` grounds (`Formula::Ite`).
pub const TRUSTIR_TERM: &str = "Trust.TrustIr.Term";
pub const TRUSTIR_TERM_GOTO: &str = "Trust.TrustIr.Term.Goto";
pub const TRUSTIR_TERM_SWITCH: &str = "Trust.TrustIr.Term.Switch";
pub const TRUSTIR_TERM_RETURN: &str = "Trust.TrustIr.Term.Return";
pub const TRUSTIR_TERM_REC: &str = "Trust.TrustIr.Term.rec";

/// `Trust.TrustIr.Block` — a basic block `Blk : List Stmt → Term → Block` (an ordered
/// straight-line statement trace plus a terminator). A CFG is a `List Block`.
pub const TRUSTIR_BLOCK: &str = "Trust.TrustIr.Block";
pub const TRUSTIR_BLOCK_MK: &str = "Trust.TrustIr.Block.Blk";
pub const TRUSTIR_BLOCK_REC: &str = "Trust.TrustIr.Block.rec";
/// `Trust.TrustIr.blockStmts : Block → List Stmt` / `blockTerm : Block → Term` — the
/// block projections (a `Block.rec` fold each).
pub const TRUSTIR_BLOCK_STMTS: &str = "Trust.TrustIr.blockStmts";
pub const TRUSTIR_BLOCK_TERM: &str = "Trust.TrustIr.blockTerm";

/// `Trust.TrustIr.blockAt : Cfg → Nat → Block` — the block lookup (`List Block` indexed
/// by block-id, with an out-of-range fallback to an empty `Return (Const 0)` block, so
/// the function is TOTAL). The Clean analogue of trust-ir's block table.
pub const TRUSTIR_BLOCK_AT: &str = "Trust.TrustIr.blockAt";

/// `Trust.TrustIr.evalCfg : Env → Cfg → Nat → Nat → Int` — the CFG executor
/// `evalCfg E cfg fuel bb`: run block `bb`'s stmts (via `evalBody`), then dispatch its
/// terminator — `Goto bb' → recurse with fuel-1`; `Switch cond t e → recurse into the
/// chosen target`; `Return op → evalOperand … op`. Bounded `fuel` (acyclic/branching
/// fragment; loops are the NEXT step). The Clean analogue of trust-ir's stepBlock-
/// across-blocks (`stepN`).
pub const TRUSTIR_EVAL_CFG: &str = "Trust.TrustIr.evalCfg";

// ---------------------------------------------------------------------------
// LOOP FRAGMENT (this increment) — the trust-ir back-edge denotation. A bounded
// `while cond { body }` (a single back-edge under a guard) is the deepest fragment.
// We model the loop FUEL-INDEXED, EXACTLY MIRRORING the committed `Trust.MirSem`
// loop meta-theory (`stepLoop`/`exec_loop`/`stepPreservesInv`/`loopInvariantRule`):
// a `Nat` iteration count bounds the back-edge re-runs, the single guarded iteration
// is `stepLoop e := if evalCond e cond then evalBody e body else e` (a `Bool.rec`
// over the guard reusing the SAME `evalCond`/`evalBody` the straight-line/branch
// fragments use), and the whole loop is `stepLoop` iterated `fuel` times. This is the
// Clean analogue of trust-ir's `stepN` over a loop with a BACK-EDGE — where `evalCfg`
// (fuel-bounded, ACYCLIC only) fails closed.
// ---------------------------------------------------------------------------

/// `Trust.TrustIr.stepLoop : Env → Cond → List Stmt → Env` — ONE guarded loop
/// iteration: `λ e cond body. @Bool.rec (λ_.Env) e (evalBody e body) (evalCond e cond)`.
/// The guard is checked at the CURRENT env; on `false` the env is unchanged (the loop
/// would exit), on `true` the body is threaded once (`evalBody e body`). The trust-ir
/// analogue of `Trust.MirSem.stepLoop` (`evalCond` ↦ `eval_cond`, `evalBody` ↦ `exec`).
/// `Bool.rec`/`evalCond`/`evalBody` are prelude/Trust DEFINITIONS ⇒ no axiom.
pub const TRUSTIR_STEP_LOOP: &str = "Trust.TrustIr.stepLoop";
/// `Trust.TrustIr.execLoop : Env → Cond → List Stmt → Nat → Env` — the OPERATIONAL
/// fuel-indexed loop, FRONT-PEELing the iteration count via `Nat.rec` at an `Env → Env`
/// motive (the same fold `evalBody` uses for `List`): `execLoop e cond body 0 = e`,
/// `execLoop e cond body (succ n) = execLoop (stepLoop e cond body) cond body n`. The
/// guarded body runs ONCE at the front; the remaining fuel folds over the result. The
/// trust-ir analogue of `Trust.MirSem.exec_loop`, structural on `Nat` (a `Nat.rec`
/// fixpoint over the trip count — the Clean analogue of trust-ir's `stepN` over a
/// back-edge). Requires `stepLoop`. No non-foundational axiom.
pub const TRUSTIR_EXEC_LOOP: &str = "Trust.TrustIr.execLoop";
/// `Trust.TrustIr.stepPreservesInv` — the guarded-step INVARIANT-PRESERVATION lemma
/// `∀ (I : Env→Prop)(cond : Cond)(body : List Stmt), (∀ e, I e → evalCond e cond = true
/// → I (evalBody e body)) → ∀ e, I e → I (stepLoop e cond body)`. ONE guarded iteration
/// preserves `I`. Proof: generalised-guard `Bool.rec` case-split — the FALSE arm leaves
/// `e` unchanged so `I e` carries through; the TRUE arm invokes the preservation
/// hypothesis. The trust-ir analogue of `Trust.MirSem.stepPreservesInv`.
pub const TRUSTIR_STEP_PRESERVES_INV: &str = "Trust.TrustIr.stepPreservesInv";
/// `Trust.TrustIr.loopInvariantRule` — the UNBOUNDED-loop Hoare WHILE rule (PARTIAL
/// correctness) `∀ (I : Env→Prop)(cond : Cond)(body : List Stmt), (∀ e, I e → evalCond e
/// cond = true → I (evalBody e body)) → ∀ (n : Nat)(e : Env), I e → I (execLoop e cond
/// body n)`. The invariant `I` is maintained for an ARBITRARY iteration count `n` —
/// proven by genuine `Nat.rec` induction on `n` (base: `execLoop e 0 ≡ e`; step: the IH
/// at the STEPPED env `stepLoop e`, fed `stepPreservesInv`). PARTIAL correctness: NO
/// termination claim. `I` is a genuine `Prop` PARAMETER, so it is a real Hoare rule —
/// the trust-ir analogue of `Trust.MirSem.loopInvariantRule`, mirroring it byte-for-byte.
pub const TRUSTIR_LOOP_INVARIANT_RULE: &str = "Trust.TrustIr.loopInvariantRule";

// --- BREAK / EARLY-EXIT loop fragment (loop-breadth increment) --------------
// The break-able Hoare while-rule is the base while-rule with the GUARD SCRUTINEE swapped
// to the COMBINED guard `Bool.and (evalCond e cond) (Bool.not (evalCond e brk))` — run the
// body iff the loop guard holds AND the break-condition does NOT. At EITHER exit (guard
// false OR break true) the combined guard is false, so ONE invariant theorem certifies `I`
// at BOTH exit points. The base loop fragment (`stepLoop`/…/`loopInvariantRule`) is
// UNTOUCHED. MIRRORS `Trust.MirSem.{stepLoopBrk,exec_loopBrk,stepPreservesInvBrk,
// loopInvariantRuleBrk}` + `andLeftTrue`, byte-for-byte (scrutinee swapped, no new induction).

/// `Trust.TrustIr.andLeftTrue : ∀ (a b : Bool), Bool.and a b = true → a = true` — the
/// `Bool.and` LEFT-projection (proved by `Bool.rec` on `a`). Extracts the loop-guard's truth
/// out of the combined break-guard. The trust-ir analogue of `Trust.MirSem.andLeftTrue`.
pub const TRUSTIR_AND_LEFT_TRUE: &str = "Trust.TrustIr.andLeftTrue";
/// `Trust.TrustIr.stepLoopBrk : Env → Cond → Cond → List Stmt → Env` — ONE combined-guarded
/// iteration `λ e cond brk body. if (evalCond e cond ∧ ¬evalCond e brk) then evalBody e body
/// else e`. The trust-ir analogue of `Trust.MirSem.stepLoopBrk`.
pub const TRUSTIR_STEP_LOOP_BRK: &str = "Trust.TrustIr.stepLoopBrk";
/// `Trust.TrustIr.execLoopBrk : Env → Cond → Cond → List Stmt → Nat → Env` — the fuel-indexed
/// break-loop fixpoint (front-peel `stepLoopBrk` via `Nat.rec`). The trust-ir analogue of
/// `Trust.MirSem.exec_loopBrk`.
pub const TRUSTIR_EXEC_LOOP_BRK: &str = "Trust.TrustIr.execLoopBrk";
/// `Trust.TrustIr.stepPreservesInvBrk` — the combined-guarded-step invariant-preservation
/// lemma (the `stepPreservesInv` analogue scrutinising the combined break-guard). The
/// trust-ir analogue of `Trust.MirSem.stepPreservesInvBrk`.
pub const TRUSTIR_STEP_PRESERVES_INV_BRK: &str = "Trust.TrustIr.stepPreservesInvBrk";
/// `Trust.TrustIr.loopInvariantRuleBrk` — the BREAK / EARLY-EXIT Hoare while-rule (PARTIAL
/// correctness): `∀ I cond brk body, pres → ∀ n e, I e → I (execLoopBrk e cond brk body n)`.
/// `I` is maintained for an arbitrary number of combined-guarded steps, so it holds at the
/// env the loop is in at EITHER exit point. Proven by genuine `Nat.rec` on the fuel. The
/// trust-ir analogue of `Trust.MirSem.loopInvariantRuleBrk`.
pub const TRUSTIR_LOOP_INVARIANT_RULE_BRK: &str = "Trust.TrustIr.loopInvariantRuleBrk";

// --- NESTED-loop fragment (this increment) — the STRATIFIED outer-statement layer --
//
// The flat loop body `List Stmt` (where `Stmt = Assign`) cannot HOLD an inner loop: to
// run a dynamic inner loop to completion INSIDE the OUTER body, a body statement must be
// able to BE a loop. The ADDITIVE, kernel-empirical fix MIRRORS `Trust.MirSem`'s Step 6N
// byte-for-byte: a SELF-nested `Stmt.Loop : Cond → List Stmt → Stmt` is a NESTED inductive
// — the kernel's nested-elimination rewrites it into a MUTUAL block with an auxiliary
// `Stmt._List`, CHANGING `Stmt.rec`'s arity/motives, which BREAKS the existing `evalBody`
// (it no longer type-checks) and regresses every flat-body certificate. NON-ADDITIVE.
// Instead we add a SEPARATE outer-statement type `OStmt` that references the EXISTING flat
// `Stmt` (`List Stmt`) for the inner-loop body — so `OStmt` is NOT nested (the recursion is
// through a DIFFERENT, already-closed type), its recursor is a SIMPLE non-mutual recursor,
// and `Stmt`/`evalBody`/`Stmt.rec` stay BYTE-IDENTICAL. The inner loop reuses the EXISTING
// `execLoop`. This handles ONE level of nesting (an outer body whose statements are plain
// assignments or fully-flat inner `while` loops) — exactly the `while i<n { while j<m {…}
// i=i+1 }` shape. MIRRORS `Trust.MirSem.{OStmt,execO,stepLoopO,exec_loopO,
// stepPreservesInvO,loopInvariantRuleO}`, with `eval_cond` ↦ `evalCond`, `exec` ↦
// `evalBody`, `exec_loop` ↦ `execLoop`, `loopInvariantRule` ↦ the trust-ir while-rule.

/// `Trust.TrustIr.OStmt` — the STRATIFIED OUTER-statement inductive (two constructors, NOT
/// nested): `Assign (idx : Nat)(rv : Rvalue) : OStmt` (a plain outer assignment, same shape
/// as `Stmt.Assign`) and `Loop (cond : Cond)(body : List Stmt)(fuel : Nat) : OStmt` (a
/// fully-FLAT inner `while cond { body }` run for `fuel` guarded iterations via the EXISTING
/// `execLoop`). The `Loop` field `body : List Stmt` references the EXISTING flat statement
/// type, so `OStmt` is a plain (non-nested, non-mutual) inductive whose `OStmt.rec` is the
/// simple recursor. The trust-ir analogue of `Trust.MirSem.OStmt`.
pub const TRUSTIR_OSTMT: &str = "Trust.TrustIr.OStmt";
/// `OStmt.Assign (idx : Nat)(rv : Rvalue) : OStmt` — a plain outer assignment, executed
/// identically to `Stmt.Assign` (`set e idx (evalRvalue e rv)`).
pub const TRUSTIR_OSTMT_ASSIGN: &str = "Trust.TrustIr.OStmt.Assign";
/// `OStmt.Loop (cond : Cond)(body : List Stmt)(fuel : Nat) : OStmt` — an inner `while cond
/// { body }` loop with a FLAT body, run for `fuel` guarded iterations via the existing
/// `execLoop`. The constructor that lets the outer body run a dynamic inner loop to completion.
pub const TRUSTIR_OSTMT_LOOP: &str = "Trust.TrustIr.OStmt.Loop";
/// The auto-derived (simple, non-mutual) recursor for `OStmt`.
pub const TRUSTIR_OSTMT_REC: &str = "Trust.TrustIr.OStmt.rec";
/// `Trust.TrustIr.execO : Env → List OStmt → Env` — the OUTER statement-list executor, the
/// `evalBody`-analogue over `List OStmt`. The `Assign(i, R)` arm threads `set e i (evalRvalue
/// e R)` (identical to `evalBody`); the `Loop(cond, body, fuel)` arm threads `execLoop e cond
/// body fuel` (runs the inner loop to completion). Carries no non-foundational axiom
/// (`List.rec`/`OStmt.rec`/`set`/`evalRvalue`/`execLoop` are all defs). The trust-ir analogue
/// of `Trust.MirSem.execO`.
pub const TRUSTIR_EXEC_O: &str = "Trust.TrustIr.execO";
/// `Trust.TrustIr.stepLoopO : Env → Cond → List OStmt → Env` — ONE guarded OUTER loop
/// iteration, the `stepLoop`-analogue over `execO`: `if evalCond e cond then execO e body
/// else e`. The trust-ir analogue of `Trust.MirSem.stepLoopO`.
pub const TRUSTIR_STEP_LOOP_O: &str = "Trust.TrustIr.stepLoopO";
/// `Trust.TrustIr.execLoopO : Env → Cond → List OStmt → Nat → Env` — the fuel-indexed OUTER
/// loop fixpoint, the `execLoop`-analogue over `stepLoopO`/`execO` (front-peel via `Nat.rec`).
/// The trust-ir analogue of `Trust.MirSem.exec_loopO`.
pub const TRUSTIR_EXEC_LOOP_O: &str = "Trust.TrustIr.execLoopO";
/// `Trust.TrustIr.stepPreservesInvO` — the OUTER guarded-step invariant-preservation lemma
/// (the `stepPreservesInv`-analogue over `stepLoopO`/`execO`): one guarded outer iteration
/// preserves `I` given the `execO`-body preservation hypothesis. The trust-ir analogue of
/// `Trust.MirSem.stepPreservesInvO`.
pub const TRUSTIR_STEP_PRESERVES_INV_O: &str = "Trust.TrustIr.stepPreservesInvO";
/// `Trust.TrustIr.loopInvariantRuleO` — the OUTER Hoare WHILE rule (PARTIAL correctness over
/// `List OStmt` bodies, i.e. a loop whose body may contain an inner loop): `∀ I cond body,
/// (∀ e, I e → evalCond e cond = true → I (execO e body)) → ∀ n e, I e → I (execLoopO e cond
/// body n)`. Proven by genuine `Nat.rec` on `n`, exactly mirroring `loopInvariantRule`. The
/// trust-ir analogue of `Trust.MirSem.loopInvariantRuleO`.
pub const TRUSTIR_LOOP_INVARIANT_RULE_O: &str = "Trust.TrustIr.loopInvariantRuleO";

// --- CONDITIONAL-UPDATE (SELECT) loop fragment — the STRATIFIED select-statement layer --
//
// The flat loop body `List Stmt` (where `Stmt = Assign idx rvalue`) cannot model the
// `max_scan`-shape CONDITIONAL accumulator update `m := if i>m { i } else { m }` — the
// straight-line `Rvalue` fragment (`Use | BinaryOp | UnaryOp`) has NO conditional-select
// constructor, and adding a `Rvalue.Sel` arm is a RECURSOR-ARITY change that breaks the
// existing `evalRvalue`/`evalBody`/`execLoop` (a NON-ADDITIVE edit). The ADDITIVE,
// STRATIFIED fix MIRRORS the committed `OStmt` discipline EXACTLY: a SEPARATE outer
// statement type `SStmt` whose `Sel` constructor models the conditional update, with its
// OWN executor `execS` (over `List SStmt`) and an `iteI` analogue. The flat `Stmt` /
// `Rvalue` / `evalBody` / `evalRvalue` / `execLoop` recursors stay BYTE-IDENTICAL (`SStmt`
// is a plain non-nested inductive whose fields reuse already-closed types). MIRRORS
// `Trust.MirSem.{iteI, Rvalue.Sel}` (the conditional-update semantics) relocated onto a
// stratified statement layer rather than a `Rvalue` arm.

/// `Trust.TrustIr.iteI : Env → Cond → Int → Int → Int` — the if-then-else over ALREADY-
/// EVALUATED `Int` arms `Bool.rec (λ_.Int) f t (evalCond e c)` (`if evalCond e c then t else
/// f`). The trust-ir analogue of `Trust.MirSem.iteI`. `Bool.rec`/`evalCond` are
/// prelude/Trust definitions ⇒ no non-foundational axiom.
pub const TRUSTIR_ITE_I: &str = "Trust.TrustIr.iteI";
/// `Trust.TrustIr.SStmt` — the STRATIFIED SELECT-statement inductive (two constructors, NOT
/// a new `Rvalue` arm): `Assign (idx : Nat)(rv : Rvalue) : SStmt` (a plain assignment, same
/// shape as `Stmt.Assign`) and `Sel (idx : Nat)(c : Cond)(a b : Operand) : SStmt` (the
/// conditional update `idx := if c then a else b`). Both constructors' fields use ALREADY-
/// DEFINED types (`Nat`, `Rvalue`, `Cond`, `Operand`), so `SStmt` is a plain (non-nested,
/// non-mutual) inductive whose `SStmt.rec` is the simple recursor. The trust-ir conditional-
/// update analogue of the `OStmt` stratification.
pub const TRUSTIR_SSTMT: &str = "Trust.TrustIr.SStmt";
/// `SStmt.Assign (idx : Nat)(rv : Rvalue) : SStmt` — a plain assignment, executed identically
/// to `Stmt.Assign` (`set e idx (evalRvalue e rv)`).
pub const TRUSTIR_SSTMT_ASSIGN: &str = "Trust.TrustIr.SStmt.Assign";
/// `SStmt.Sel (idx : Nat)(c : Cond)(a b : Operand) : SStmt` — the CONDITIONAL update `idx :=
/// if c then a else b`, executed as `set e idx (iteI e c (evalOperand e a)(evalOperand e b))`.
/// The constructor that lets the loop body model `max_scan`'s `m := if i>m { i } else { m }`.
pub const TRUSTIR_SSTMT_SEL: &str = "Trust.TrustIr.SStmt.Sel";
/// The auto-derived (simple, non-mutual) recursor for `SStmt`.
pub const TRUSTIR_SSTMT_REC: &str = "Trust.TrustIr.SStmt.rec";
/// `Trust.TrustIr.execS : Env → List SStmt → Env` — the SELECT statement-list executor, the
/// `evalBody`-analogue over `List SStmt`. The `Assign(i, R)` arm threads `set e i (evalRvalue
/// e R)` (identical to `evalBody`); the `Sel(i, c, a, b)` arm threads `set e i (iteI e c
/// (evalOperand e a)(evalOperand e b))` (the conditional update). The trust-ir analogue of
/// `execO`, with the `Sel` arm grounding through `iteI`.
pub const TRUSTIR_EXEC_S: &str = "Trust.TrustIr.execS";
/// `Trust.TrustIr.stepLoopS : Env → Cond → List SStmt → Env` — ONE guarded SELECT loop
/// iteration (`if evalCond e cond then execS e body else e`), the `stepLoopO`-analogue over
/// `execS`.
pub const TRUSTIR_STEP_LOOP_S: &str = "Trust.TrustIr.stepLoopS";
/// `Trust.TrustIr.execLoopS : Env → Cond → List SStmt → Nat → Env` — the fuel-indexed SELECT
/// loop fixpoint, the `execLoopO`-analogue over `stepLoopS`/`execS`.
pub const TRUSTIR_EXEC_LOOP_S: &str = "Trust.TrustIr.execLoopS";
/// `Trust.TrustIr.stepPreservesInvS` — the SELECT guarded-step invariant-preservation lemma
/// (the `stepPreservesInvO`-analogue over `stepLoopS`/`execS`).
pub const TRUSTIR_STEP_PRESERVES_INV_S: &str = "Trust.TrustIr.stepPreservesInvS";
/// `Trust.TrustIr.loopInvariantRuleS` — the SELECT Hoare WHILE rule (PARTIAL correctness over
/// `List SStmt` bodies, i.e. a loop whose body may contain a conditional select): `∀ I cond
/// body, (∀ e, I e → evalCond e cond = true → I (execS e body)) → ∀ n e, I e → I (execLoopS e
/// cond body n)`. Proven by genuine `Nat.rec` on `n`, mirroring `loopInvariantRuleO`.
pub const TRUSTIR_LOOP_INVARIANT_RULE_S: &str = "Trust.TrustIr.loopInvariantRuleS";

// --- SLICE-INDEX (BOUNDS-GUARDED) operand fragment — the STRATIFIED operand-extension layer --
//
// The flat `Operand` (`Var | Const`) cannot model a slice-element access `s[i]` or a slice
// length `s.len()`: adding `Index`/`Len` arms to the existing `Operand` inductive is a
// RECURSOR-ARITY change that breaks the existing `evalOperand`/`evalRvalue`/`evalCond`/
// `evalBody`/`evalCfg` (mirsem.rs does extend `Operand` directly, but that is exactly the
// non-additive move forbidden for the trust-ir re-anchor). The ADDITIVE, STRATIFIED fix adds
// a SEPARATE operand-extension type `XOperand` that REFERENCES the EXISTING flat `Operand`
// for its sub-operands — so the flat `Operand`/`evalOperand` recursors stay BYTE-IDENTICAL.
// The slice element / length are modeled by the UNINTERPRETED total `idxElem`/`sliceLen`
// (the `bnot` pattern: `Opaque`, NOT `Axiom`), mirroring `Trust.MirSem.{idx_elem,slice_len}`.
// Since the LIVE `clean_ground` grounds `Select`/length to the MirSem-named opaques (which we
// must not reference for a clean re-anchor), the slice-index refinement is MODEL-ONLY (the
// `bnot`/`UnOp::Not` discipline) — genuine + fail-closed, but NOT grounder-connected.

/// `Trust.TrustIr.idxElem : Int → Int → Int` — the UNINTERPRETED total slice-element selector
/// (`Opaque`, NOT `Axiom`): `idxElem (slice-handle)(index)` is the modeled `Int` value of
/// `s[i]`. The trust-ir analogue of `Trust.MirSem.idx_elem`. A term naming it carries NO
/// non-foundational axiom.
pub const TRUSTIR_IDX_ELEM: &str = "Trust.TrustIr.idxElem";
/// `Trust.TrustIr.sliceLen : Int → Int` — the UNINTERPRETED total slice-length selector
/// (`Opaque`): `sliceLen (slice-handle)` is the modeled `Int` length of `s`. The trust-ir
/// analogue of `Trust.MirSem.slice_len`.
pub const TRUSTIR_SLICE_LEN: &str = "Trust.TrustIr.sliceLen";
/// Trust: ITER-NEXT VALUE-PATH (2026-07-21) — `Trust.MirSem.iter_region : Int → Int`, the
/// UNINTERPRETED total ENTRY-TIME remaining-region HANDLE CONSTRUCTOR (`Opaque`, NOT
/// `Axiom`, EMPTY axiom_deps — the SAME honesty tier as `idxElem`/`sliceLen`):
/// `iter_region (recv)` is the abstract `[cursor..end]` sequence of a pinned
/// `&mut core::slice::iter::Iter` at ENTRY, keyed by the receiver's Int carrier. It asserts
/// only "SOME sequence stably determined by the entry receiver", never its length or
/// elements. ENTRY-TIME-INDEXED BY RECOGNIZER DISCIPLINE ONLY: the Clean side cannot express
/// the time index, so an `iter_region(recv)` theorem is SINGLE-Env-LOCAL and must NEVER be
/// composed across a call site or an admitted receiver mutation (a chained `next()` presents
/// the SAME `recv` carrier with a DIFFERENT true region) — enforced fail-closed by
/// GATE-ITER-REGION-NO-CROSS-INSTANTIATION, never by this opaque. Lift only when a
/// post-state/primed surface re-keys the handle (`iter_region(recv, generation)`).
pub const TRUSTIR_ITER_REGION: &str = "Trust.MirSem.iter_region";
/// Trust: ITER-NEXT VALUE-PATH (2026-07-21) — `Trust.MirSem.iter_has_next : Int → Bool`, the
/// UNINTERPRETED total DISPATCH HEAD (`Opaque`, EMPTY axiom_deps): `iter_has_next (recv)` is
/// the abstract truth of "`<Iter as Iterator>::next` yields `Some`" at ENTRY. Its tie to the
/// real `ptr != end` `SwitchInt` is enforced by the recognizer, NOT asserted here — so the
/// certificate assumes NO bridge premise. SAME entry-time / non-composable discipline as
/// [`TRUSTIR_ITER_REGION`].
pub const TRUSTIR_ITER_HAS_NEXT: &str = "Trust.MirSem.iter_has_next";
/// Trust: W-PRIMED increment 1 (2026-07-22) — GATE-ITER-REGION-NO-CROSS-INSTANTIATION
/// documented lift #1 — `Trust.MirSem.iter_seq : Int → Int → Int`, the UNINTERPRETED
/// total ELEMENT FAMILY of the two-key (generation-re-keyed) primed surface
/// (`Declaration::Opaque`, NOT `Axiom`, EMPTY axiom_deps — the SAME honesty tier as
/// `idxElem`/`sliceLen`/`iter_region`/`ptrOffset`): `iter_seq recv k` is the modeled Int
/// value of the k-th element AFTER THE ENTRY CURSOR of the pinned `&mut core::slice::iter::
/// Iter` whose receiver Int carrier is `recv` — an uninterpreted total element family,
/// ABSOLUTE-indexed from entry (generation-free base). Asserts ONLY "SOME Int stably
/// determined by (recv, k)"; NO length/address/aliasing/validity content; meaningless-but-
/// total at negative k. The generation-g region head is `iter_seq recv g` BY CONVENTION OF
/// CONSUMERS, never by a law over this opaque — ABSOLUTE indexing is the axiom-killer: the
/// shift/tail law never needs stating, cross-generation composition is arithmetic on the
/// second key only. NO bridge equation to the one-arg [`TRUSTIR_ITER_REGION`] may ever be
/// declared (that resurrects the refuted elem0=elem1 composition through the old handle).
pub const TRUSTIR_ITER_SEQ: &str = "Trust.MirSem.iter_seq";
/// Trust: W-PRIMED increment 1 (2026-07-22) — `Trust.MirSem.iter_len : Int → Int`, the
/// UNINTERPRETED total ELEMENT-COUNT of the two-key primed surface (`Declaration::Opaque`,
/// EMPTY axiom_deps): the modeled total element count from ENTRY cursor to end, keyed by
/// the receiver carrier — the recv-keyed sibling of [`TRUSTIR_SLICE_LEN`] (which is
/// slice-handle-keyed and CANNOT be used here: no slice handle is in scope at `next()`'s
/// own certificate). Its tie to the caller's real slice length is NOT asserted (the NAMED
/// residue premise D-INIT). Asserts ONLY "SOME Int stably determined by recv"; NO
/// address/aliasing/validity content.
pub const TRUSTIR_ITER_LEN: &str = "Trust.MirSem.iter_len";
/// Trust: W-PRIMED increment 1 (2026-07-22) — `Trust.MirSem.iter_has_next2 : Int → Int →
/// Bool`, the DISPATCH HEAD of the two-key primed surface — a plain **Definition** (NOT
/// Opaque): `iter_has_next2 recv g := decide (Int.lt g (iter_len recv)) (Int.decLt g
/// (iter_len recv))`, i.e. BY DEFINITION `g < iter_len recv` over the SAME
/// `decide`/`Int.lt`/`Int.decLt` `SemCmpOp::Lt` combinator `guard_bool` already lowers
/// through, so the guard vocabulary is shared with `exec`/`evalCond` reductions. The
/// definitional tie carries ZERO axioms; the honest content (the compiled Option
/// discriminant tracks it) moves entirely to the D-ORIENT recognizer orientation pin — the
/// SAME trust boundary the one-arg [`TRUSTIR_ITER_HAS_NEXT`] already documents ("enforced
/// by the recognizer, NOT asserted here"). NOTE: the trailing `2` distinguishes this from
/// the one-arg [`TRUSTIR_ITER_HAS_NEXT`]; it references ONLY the two-key family
/// ([`TRUSTIR_ITER_LEN`]), never the one-arg family (F-BRIDGE census pin).
pub const TRUSTIR_ITER_HAS_NEXT2: &str = "Trust.MirSem.iter_has_next2";
/// Trust: RECORD-WITNESS increment 3 (2026-07-22) — GATE-PTR-SLOT-OPACITY(a) —
/// `Trust.TrustIr.sliceStart : Int → Int`, the UNINTERPRETED total SLICE-START HANDLE
/// CONSTRUCTOR (`Declaration::Opaque`, NOT `Axiom`, EMPTY axiom_deps — the SAME honesty
/// tier as `idxElem`/`sliceLen`/`iter_region`): `sliceStart (s)` is the abstract data
/// pointer at the START of the slice handle `s`, keyed by `s`'s Int carrier. It is a
/// FRESH opaque APPLICATION on the root (`sliceStart (e p)`), NEVER the bare root slot
/// `e p` itself — the NO-BARE-SLOT discipline: bare `e p` would make
/// `sliceLen(ptr-slot) = sliceLen(e p) = Len(s)`, a caller-reachable falsity (two
/// subslices `&arr[0..4]`, `&arr[0..8]` have bit-identical runtime start pointers but
/// lengths 4 vs 8). It asserts only "SOME Int stably determined by the slice handle",
/// NO address / aliasing / validity content.
///
/// ADDRESS-TIER NARROW-SANCTION (W-ADDR lift, 2026-07-22, supersedes the blanket clause-(c)
/// ban): the `sliceStart (s)` term and the SEPARATELY-carried raw-CFG `PtrModel` in-bounds
/// offset discharge (the reflexive `Len(s) ≤ Len(s)` bound, keyed by structural `Formula`
/// identity) MAY be jointly consumed ONLY by the sanctioned DIST-INIT consumer
/// ([`crate::clean_ground::iter_dist_init_premise_instance`]), which concludes
/// `end - start = sliceLen(s)*e` SOLELY as the consequent of `Trust.TrustIr.iterDistInit`
/// UNDER the never-discharged hypotheses hOff/hLen, cites P-ADDR-ALLOC / P-ADDR-EXTENT /
/// P-ADDR-REFINE verbatim in the claim surface, consumes the raw-CFG offset discharge ONLY in
/// its existing callee-certification role (via D2 — never re-cited as a distance/no-wrap fact),
/// and flips NO verdict/cluster/funnel bit. EVERY other joint consumption remains rejected
/// FAIL-CLOSED: the bare-slot `end = e p` reading, any address-equality-to-handle/length-
/// equality derivation, any cross-elemSize recast equality, any citation across a receiver
/// mutation (GATE-ITER-REGION untouched), any cross-handle injectivity/disjointness (aliasing
/// params may overlap one allocation) — enforced by the recognizer + the forgery probes, NEVER
/// by this opaque (env separation cannot carry the argument: `trustir_env` is not MirSem-free).
pub const TRUSTIR_SLICE_START: &str = "Trust.TrustIr.sliceStart";
/// Trust: RECORD-WITNESS increment 3 (2026-07-22) — GATE-PTR-SLOT-OPACITY(b) —
/// `Trust.TrustIr.ptrOffset : Int → Int → Int → Int`, the UNINTERPRETED total
/// POINTEE-PINNED POINTER-OFFSET (`Declaration::Opaque`, EMPTY axiom_deps): `ptrOffset
/// (base) (count) (elemSize)` is the abstract pointer `base` advanced by `count` elements
/// each of `elemSize` bytes. The `elemSize` argument is PINNED from the MIR pointer's
/// POINTEE sort, so `p.add(n)` on a `*const u8` (`elemSize = 1`) and `(p as *const u64).add(n)`
/// on a `*const u64` (`elemSize = 8`) are DISTINCT opaque applications — the value-tier
/// pointee-blind-cast overclaim (`is_pointerish` passes the recast) is DEAD. It asserts only
/// "SOME Int deterministically the offset of `base` by `count` elements of `elemSize`
/// bytes", NO address / aliasing / validity / one-past-the-end content.
///
/// ADDRESS-TIER NARROW-SANCTION (W-ADDR lift, 2026-07-22, supersedes the blanket clause-(c)
/// ban): the `ptrOffset (sliceStart s) (sliceLen s) e` record term and the raw-CFG `PtrModel`
/// discharge MAY be jointly consumed ONLY by the sanctioned DIST-INIT consumer
/// ([`crate::clean_ground::iter_dist_init_premise_instance`]), which concludes
/// `end - start = sliceLen(s)*e` SOLELY as the consequent of `Trust.TrustIr.iterDistInit`
/// UNDER the never-discharged hypotheses hOff/hLen, cites P-ADDR-ALLOC / P-ADDR-EXTENT /
/// P-ADDR-REFINE verbatim in the claim surface, consumes the raw-CFG offset discharge ONLY in
/// its existing callee-certification role (via D2 — never re-cited as a distance/no-wrap fact),
/// and flips NO verdict/cluster/funnel bit. EVERY other joint consumption remains rejected
/// FAIL-CLOSED: the bare-slot `end = e p` reading, any address-equality-to-handle/length-
/// equality derivation, any cross-elemSize recast equality, any citation across a receiver
/// mutation (GATE-ITER-REGION untouched), any cross-handle injectivity/disjointness (aliasing
/// params may overlap one allocation). SAME entry-time / value-tier discipline as
/// [`TRUSTIR_SLICE_START`].
pub const TRUSTIR_PTR_OFFSET: &str = "Trust.TrustIr.ptrOffset";
/// Trust: W-ADDR increment 1 (2026-07-22) — GATE-PTR-SLOT-OPACITY(c) NARROW-SANCTION —
/// `Trust.TrustIr.iterDistInit`, the HYPOTHESIS-CARRYING kernel theorem (the `memoAdequate`
/// pattern: `Declaration::Theorem` with EMPTY axiom_deps, proof kernel-rechecked modulo the 3
/// foundational axioms) that the sanctioned DIST-INIT consumer concludes `end − start =
/// sliceLen(s)·e` through — but ONLY as the CONSEQUENT of an undischarged conditional:
///
/// ```text
/// theorem Trust.TrustIr.iterDistInit :
///   ∀ (s e : Int),
///     (hOff : ptrOffset (sliceStart s) (sliceLen s) e = sliceStart s + sliceLen s * e) →
///     (hLen : 0 ≤ sliceLen s) →
///     ptrOffset (sliceStart s) (sliceLen s) e - sliceStart s = sliceLen s * e
/// ```
///
/// The bridge equation H-OFF (`hOff`) is a MEMORY-MODEL fact — NEVER establishable from MIR,
/// NEVER asserted — resting on the named premises P-ADDR-ALLOC / P-ADDR-EXTENT / P-ADDR-REFINE
/// (`mirsem.rs`). It lives ONLY as this theorem's undischarged hypothesis and is citable ONLY
/// entry-locally at its mint. `hOff`/`hLen` are NEVER discharged anywhere in the proof tree.
/// The kernel checks ONLY the arithmetic composition (rewrite `hOff` via `Eq.subst`, then the
/// `(a + b) − a = b` normalization — `Int.add_comm` + `Int.add_neg_cancel_right`, both
/// constructive prelude lemmas, `Int.sub` a reducible Definition). VERIFIED before landing:
/// the trustir_env kernel closes the subtraction-normalization, so the PRIMARY (hOff-rewritten)
/// statement shape is used — the `KERNEL_WITNESS` fallback is NOT needed. See
/// [`iter_dist_init_theorem_terms`] / [`iter_dist_init_theorem_axiom_residue`].
pub const TRUSTIR_ITER_DIST_INIT: &str = "Trust.TrustIr.iterDistInit";
/// `Trust.TrustIr.XOperand` — the STRATIFIED slice-operand-extension inductive (three
/// constructors, NOT new `Operand` arms): `Base (op : Operand) : XOperand` (lift a flat
/// operand), `Index (s i : Operand) : XOperand` (slice element `s[i]`), `Len (s : Operand) :
/// XOperand` (slice length `s.len()`). Every field is the ALREADY-CLOSED flat `Operand`, so
/// `XOperand` is a plain (non-nested, non-mutual) inductive whose `XOperand.rec` is the simple
/// recursor — and `Operand`/`evalOperand` stay BYTE-IDENTICAL.
pub const TRUSTIR_XOPERAND: &str = "Trust.TrustIr.XOperand";
pub const TRUSTIR_XOPERAND_BASE: &str = "Trust.TrustIr.XOperand.Base";
pub const TRUSTIR_XOPERAND_INDEX: &str = "Trust.TrustIr.XOperand.Index";
pub const TRUSTIR_XOPERAND_LEN: &str = "Trust.TrustIr.XOperand.Len";
pub const TRUSTIR_XOPERAND_REC: &str = "Trust.TrustIr.XOperand.rec";
/// `Trust.TrustIr.evalXOperand : Env → XOperand → Int` — `Base op → evalOperand e op`,
/// `Index s i → idxElem (evalOperand e s)(evalOperand e i)`, `Len s → sliceLen (evalOperand e
/// s)`. A non-dependent `XOperand.rec` fold reusing the flat `evalOperand`.
pub const TRUSTIR_EVAL_XOPERAND: &str = "Trust.TrustIr.evalXOperand";

// ---------------------------------------------------------------------------
// Small kernel-term builders (shared de-Bruijn convention with mirsem.rs)
// ---------------------------------------------------------------------------

// Trust: ADT-return leaf — widened to `pub(crate)` (bodies unchanged) so the
// sibling `trustir_adt` module can build terms in the SAME anchor vocabulary
// (`Int`/`Env`/literal) without duplicating them.
pub(crate) fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

pub(crate) fn int_ty() -> Expr {
    cst("Int")
}

fn nat_ty() -> Expr {
    cst("Nat")
}

/// `Env = Nat → Int`.
pub(crate) fn env_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), nat_ty(), int_ty())
}

fn binop_ty() -> Expr {
    cst(TRUSTIR_BINOP)
}

fn operand_ty() -> Expr {
    cst(TRUSTIR_OPERAND)
}

fn unop_ty() -> Expr {
    cst(TRUSTIR_UNOP)
}

fn rvalue_ty() -> Expr {
    cst(TRUSTIR_RVALUE)
}

fn stmt_ty() -> Expr {
    cst(TRUSTIR_STMT)
}

/// The closed `Int` literal `Expr` for `n`, BYTE-IDENTICAL to
/// `clean_ground::int_lit_to_expr` (so a `Const c` operand denotes the exact term the
/// live grounder emits for `Formula::Int(c)`).
pub(crate) fn int_lit(n: i128) -> Expr {
    // Trust: EXACT ENCODING (2026-07-24) — `Expr::nat_lit_u128` covers the FULL
    // magnitude range. The former `as u64` was `n mod 2^64`, a SILENT TRUNCATION that
    // made this map NON-INJECTIVE and caused a demonstrated LIVE FALSE ACCEPT (see
    // `clean_ground::int_lit_to_expr`). Byte-identity with the other encoders is
    // PRESERVED, and so is every existing term: `BigNat::from_limbs` normalizes a
    // trailing zero limb back to `BigNat::Small`, so `nat_lit_u128(k) == nat_lit(k)`
    // for every `k <= u64::MAX` (asserted by `int_lit_encoders_agree_and_are_exact`).
    // `Int.negSucc` carries `|n| - 1`, which fits `u128` for every `i128` (including
    // `i128::MIN`, where `-n` is not representable).
    if n >= 0 {
        Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(n.unsigned_abs()))
    } else {
        Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(n.unsigned_abs() - 1))
    }
}

/// The canonical free-variable NAME for parameter index `p` — IDENTICAL to
/// `mirsem::var_name` (`format!("p{p}")`), so the SAME `clean_ground::ground_int`
/// params convention applies. The bridge only requires `reflected_formula` and the
/// grounding `params` map to agree on this name.
fn param_name(p: u64) -> String {
    format!("p{p}")
}

// ---------------------------------------------------------------------------
// The trust-ir BinOp bijection — the structural link to the universal IR.
// ---------------------------------------------------------------------------

/// The arithmetic fragment of `trust_ir::inst::BinOp` this anchor denotes. The
/// `trust_ir_name` / `reflected_formula` maps below are the ONE-TO-ONE
/// correspondence to the universal IR; the unit test
/// `trustir_binop_names_are_canonical` checks the names are the real
/// `trust_ir::inst::BinOp` variant identifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustIrBinOp {
    /// `trust_ir::BinOp::Add`.
    Add,
    /// `trust_ir::BinOp::Sub`.
    Sub,
    /// `trust_ir::BinOp::Mul`.
    Mul,
    /// `trust_ir::BinOp::SDiv` (signed division).
    SDiv,
    /// `trust_ir::BinOp::SRem` (signed TRUNCATED remainder — Trust: witness-tier
    /// Rem arm). Grounds to the prelude's opaque `Int.mod` (`ground_int`'s
    /// `F::Rem` arm), the SAME truncated semantics as trust-ir's
    /// `semIntBinOp .SRem`. MIR `Rem` maps here for signed operands BY DEFINITION
    /// and for unsigned operands BY COINCIDENCE ON THE NONNEGATIVE FRAGMENT
    /// (SRem == URem pointwise when both operands are ≥ 0).
    SRem,
    /// `trust_ir::BinOp::LShr` (Trust: M6 rung 6, SHR→TRUST-IR ANCHOR relocation —
    /// UNSIGNED logical right shift). Grounds to the Opaque `Int.shiftRight`
    /// (registered by [`register_int_shr`]), matching `ground_int`'s
    /// `F::Pred("Int.shiftRight", [a,b])` BITWISE SHAPE LANE arm — the SAME opaque
    /// carrier `mirsem::register_int_bitwise`'s `Shr` arm registers on the MirSem
    /// side. `trust_ir::BinOp::AShr` (signed/arithmetic shift-right) is a DISTINCT
    /// variant with floor-on-negatives semantics and stays UNMODELED — a signed
    /// `>>` fails closed at admission (see `prove::straight_line_ir_body`), never
    /// mis-denoted as `LShr`.
    LShr,
    /// `trust_ir::BinOp::And` (Trust: M6 rung 9, ANCHOR BitAnd — bitwise AND; MIR's
    /// `BinOp::BitAnd` opcode maps here). Grounds to the Opaque `Int.land`
    /// (registered by [`register_int_land`]), matching `ground_int`'s
    /// `F::Pred("Int.land", [a,b])` BITWISE SHAPE LANE arm — the SAME opaque
    /// carrier `mirsem::register_int_bitwise`'s `BitAnd` arm registers on the
    /// MirSem side.
    And,
}

impl TrustIrBinOp {
    /// All seven supported ops (for the exhaustive POC).
    pub const ALL: [TrustIrBinOp; 7] = [
        TrustIrBinOp::Add,
        TrustIrBinOp::Sub,
        TrustIrBinOp::Mul,
        TrustIrBinOp::SDiv,
        TrustIrBinOp::SRem,
        TrustIrBinOp::LShr,
        TrustIrBinOp::And,
    ];

    /// The Clean constructor name — keyed to the trust-ir variant name.
    fn ctor_name(self) -> &'static str {
        match self {
            TrustIrBinOp::Add => TRUSTIR_BINOP_ADD,
            TrustIrBinOp::Sub => TRUSTIR_BINOP_SUB,
            TrustIrBinOp::Mul => TRUSTIR_BINOP_MUL,
            TrustIrBinOp::SDiv => TRUSTIR_BINOP_SDIV,
            TrustIrBinOp::SRem => TRUSTIR_BINOP_SREM,
            TrustIrBinOp::LShr => TRUSTIR_BINOP_LSHR,
            TrustIrBinOp::And => TRUSTIR_BINOP_AND,
        }
    }

    /// The bare trust-ir variant name (the bijection key).
    pub fn trust_ir_name(self) -> &'static str {
        match self {
            TrustIrBinOp::Add => "Add",
            TrustIrBinOp::Sub => "Sub",
            TrustIrBinOp::Mul => "Mul",
            TrustIrBinOp::SDiv => "SDiv",
            TrustIrBinOp::SRem => "SRem",
            TrustIrBinOp::LShr => "LShr",
            TrustIrBinOp::And => "And",
        }
    }

    /// The reflected `Formula` for `param0 OP param1` — exactly the scalar
    /// `Formula` shape `clean_ground::ground_int` consumes. Params are named
    /// `p0`/`p1` (the `var_name(0)`/`var_name(1)` convention `mirsem.rs` uses, so
    /// the SAME live grounder + params map applies), matching the env binding.
    fn reflected_formula(self) -> trust_types::Formula {
        use trust_types::{Formula as F, Sort};
        let a = Box::new(F::Var(param_name(0), Sort::Int));
        let b = Box::new(F::Var(param_name(1), Sort::Int));
        match self {
            TrustIrBinOp::Add => F::Add(a, b),
            TrustIrBinOp::Sub => F::Sub(a, b),
            TrustIrBinOp::Mul => F::Mul(a, b),
            TrustIrBinOp::SDiv => F::Div(a, b),
            // Trust: witness-tier Rem arm — EXACTLY clean_ground's `binop_formula` Rem arm.
            TrustIrBinOp::SRem => F::Rem(a, b),
            // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — the generic opaque-application
            // carrier (no direct `Formula` constructor for a shift), BYTE-IDENTICAL to
            // `mirsem::SemRvalue::Bin(SemBinOp::Shr, ..)`'s `to_formula` arm.
            TrustIrBinOp::LShr => {
                F::Pred(trust_types::Symbol::intern("Int.shiftRight"), vec![*a, *b])
            }
            // Trust: M6 rung 9, ANCHOR BitAnd — the SAME opaque-application carrier
            // discipline as `LShr`, BYTE-IDENTICAL to `mirsem::SemRvalue::Bin(
            // SemBinOp::BitAnd, ..)`'s `to_formula` arm.
            TrustIrBinOp::And => F::Pred(trust_types::Symbol::intern("Int.land"), vec![*a, *b]),
        }
    }

    /// The Clean constructor `Expr` (`Trust.TrustIr.BinOp.<Op>`).
    fn ctor_expr(self) -> Expr {
        cst(self.ctor_name())
    }
}

// ---------------------------------------------------------------------------
// The trust-ir UnOp bijection (integer fragment).
// ---------------------------------------------------------------------------

/// The integer fragment of `trust_ir::inst::UnOp` this anchor denotes:
/// `Neg` (`UnOp::Neg`) and `Not` (`UnOp::Not`). The float/popcount variants
/// (`FNeg|FAbs|FSqrt|FFloor|FCeil|FTrunc|CtPop`) are out of the straight-line
/// integer fragment and not modeled here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustIrUnOp {
    /// `trust_ir::UnOp::Neg` — integer negation. Grounder-connected: reflects to
    /// `Formula::Neg`, which the LIVE `ground_int` grounds to `Int.sub (Int.ofNat 0) x`.
    Neg,
    /// `trust_ir::UnOp::Not` — bitwise complement. The live `ground_int` has NO integer
    /// `Not` arm (`Formula::Not` is BOOL-sorted only), so `Not` is modeled with the
    /// opaque `Trust.TrustIr.bnot`; its refinement is against the trust-ir denotation,
    /// NOT grounder-connected (documented honestly).
    Not,
}

impl TrustIrUnOp {
    /// Both supported integer unary ops.
    pub const ALL: [TrustIrUnOp; 2] = [TrustIrUnOp::Neg, TrustIrUnOp::Not];

    fn ctor_name(self) -> &'static str {
        match self {
            TrustIrUnOp::Neg => TRUSTIR_UNOP_NEG,
            TrustIrUnOp::Not => TRUSTIR_UNOP_NOT,
        }
    }

    /// The bare trust-ir `UnOp` variant name (the bijection key).
    pub fn trust_ir_name(self) -> &'static str {
        match self {
            TrustIrUnOp::Neg => "Neg",
            TrustIrUnOp::Not => "Not",
        }
    }

    fn ctor_expr(self) -> Expr {
        cst(self.ctor_name())
    }

    /// `true` IFF this op's denotation matches a LIVE `ground_int` arm (so its
    /// refinement is genuinely grounder-connected). Only `Neg` qualifies.
    fn is_grounder_connected(self) -> bool {
        matches!(self, TrustIrUnOp::Neg)
    }
}

// ---------------------------------------------------------------------------
// The straight-line trust-ir AST (Rust-side) — operands, rvalues, statements.
// Each `to_*_expr` builds the CLOSED Clean term; `to_formula` builds the
// reflected `trust_types::Formula` the LIVE grounder consumes. Together they let
// the refinement RELATE the trust-ir denotation to the live grounder.
// ---------------------------------------------------------------------------

/// A straight-line trust-ir operand: an SSA value reference (`Var i`), an integer
/// literal (`Const c`), or (Trust: field-read leaf) a struct-FIELD READ (`Field
/// paramIdx fld`). Keyed to `trust_ir`'s `Operand`/`Inst::Const`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrOperand {
    /// `Var i` — the value bound at index `i` (a function parameter or an earlier
    /// SSA temp). Reflects to `Formula::Var("p{i}")`.
    Var(u64),
    /// `Const c` — an integer literal. Reflects to `Formula::Int(c)`.
    Const(i128),
    /// Trust: field-read leaf — `Field paramIdx fld` — a struct-FIELD READ
    /// `(*paramIdx).fld` on an IMMUTABLE-REFERENCE PARAMETER (`paramIdx`, e.g.
    /// `(*self).0`). Modeled by REUSE of the opaque total `idxElem` selector (see
    /// [`TRUSTIR_IDX_ELEM`]) — the trust-ir analogue of `mirsem::SemOperand::Field`'s
    /// reuse of `idx_elem`, on trust-ir's OWN opaque (independent of MirSem's — the
    /// trust-ir denotation must not reference MirSem constants). NOT grounder-connected:
    /// the LIVE shared grounder's `Formula::Select` arm hardcodes `Trust.MirSem.idx_elem`
    /// (a DIFFERENT opaque than `Trust.TrustIr.idxElem`), so `to_formula`/`live_ground_int`
    /// can never reach it — modeled genuinely via `evalOperand`'s own (new) `Field` arm and
    /// checked against the trust-ir MODEL denotation (`check_body_refinement_model`), not
    /// the live grounder. Asserts NOTHING about the field's VALUE, only that it denotes SOME
    /// Int stably determined by (paramIdx, fld) — no content claim.
    Field(u64, u64),
    /// Trust: ptr-spine call-arg leaf — `Index s i` — a SLICE-ELEMENT access `s[i]`,
    /// RECURSIVE in both fields (mirrors `mirsem::SemOperand::Index`'s already-proven
    /// Clean encoding — `Trust.MirSem.Operand.Index` — byte-for-byte: same recursive-
    /// constructor + induction-hypothesis-threading scheme, ported onto
    /// `Trust.TrustIr.Operand` with trust-ir's OWN `idxElem` opaque, never referencing
    /// `Trust.MirSem.*`). Produced by [`crate::prove::sem_call_arg_to_ir`] translating a
    /// ptr-model-resolved call-site argument (`mirsem::SemOperand::Index`) — the exact
    /// shape memchr's `One::count` passes as `start`/`end` to its certified `count_raw`
    /// callee. NOT grounder-connected (same reason as `Field`): the live grounder's
    /// `Formula::Select` arm hardcodes `Trust.MirSem.idx_elem`, a DIFFERENT opaque than
    /// `Trust.TrustIr.idxElem`, so this certifies via [`check_operand_refinement_model`],
    /// honestly MODEL-ONLY. Asserts NOTHING about the element's VALUE, only that it
    /// denotes SOME Int stably determined by (s, i) — no content claim.
    Index(Box<IrOperand>, Box<IrOperand>),
    /// Trust: ptr-spine call-arg leaf — `Len s` — a SLICE-LENGTH `s.len()`, RECURSIVE in
    /// its one field. Mirrors `Trust.MirSem.Operand.Len`. REUSES the opaque total
    /// `sliceLen` selector (see [`TRUSTIR_SLICE_LEN`]). NOT grounder-connected — same
    /// MODEL-ONLY tier as `Index`/`Field`.
    Len(Box<IrOperand>),
}

impl IrOperand {
    /// The closed `Trust.TrustIr.Operand` constructor value.
    /// (`pub(crate)` for the trust-ir CALL denotation — `trustir_call.rs` pins the
    /// per-call `callReturnInstance` at this exact constructor value.)
    pub(crate) fn to_operand_expr(&self) -> Expr {
        match self {
            IrOperand::Var(i) => Expr::app(cst(TRUSTIR_OPERAND_VAR), Expr::nat_lit(*i)),
            IrOperand::Const(c) => Expr::app(cst(TRUSTIR_OPERAND_CONST), int_lit(*c)),
            IrOperand::Field(p, fld) => {
                Expr::apps(cst(TRUSTIR_OPERAND_FIELD), [Expr::nat_lit(*p), Expr::nat_lit(*fld)])
            }
            // Trust: ptr-spine call-arg leaf.
            IrOperand::Index(s, i) => {
                Expr::apps(cst(TRUSTIR_OPERAND_INDEX), [s.to_operand_expr(), i.to_operand_expr()])
            }
            IrOperand::Len(s) => Expr::app(cst(TRUSTIR_OPERAND_LEN), s.to_operand_expr()),
        }
    }

    /// The reflected `Formula` — EXACTLY what `clean_ground::operand_to_formula`
    /// produces (`Var i → Formula::Var("p{i}", Int)`, `Const c → Formula::Int(c)`).
    /// `Field paramIdx fld` reflects to `Formula::Select(Var paramIdx, Int fld)` for
    /// documentation parity with `mirsem::SemOperand::Field::to_formula` — but this arm is
    /// NEVER live-groundable to a MATCHING term (see the variant doc): every call site that
    /// might reach it is gated by [`IrOperand::is_grounder_connected`] first.
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::{Formula as F, Sort};
        match self {
            IrOperand::Var(i) => F::Var(param_name(*i), Sort::Int),
            IrOperand::Const(c) => F::Int(*c),
            IrOperand::Field(p, fld) => F::Select(
                Box::new(F::Var(param_name(*p), Sort::Int)),
                Box::new(F::Int(i128::from(*fld))),
            ),
            // Trust: ptr-spine call-arg leaf — documentation parity with
            // `mirsem::SemOperand::Index`/`Len::to_formula` — but (like `Field`) NEVER
            // live-groundable to a MATCHING term: every call site that might reach it is
            // gated by [`IrOperand::is_grounder_connected`] first.
            IrOperand::Index(s, i) => F::Select(Box::new(s.to_formula()), Box::new(i.to_formula())),
            IrOperand::Len(s) => {
                F::Pred(trust_types::Symbol::intern(TRUSTIR_SLICE_LEN), vec![s.to_formula()])
            }
        }
    }

    /// Append this operand's referenced variable indices (first-appearance order).
    /// `Field paramIdx _` contributes `paramIdx` (the field's fixed key is not itself a
    /// bound index). Trust: ptr-spine call-arg leaf — `Index`/`Len` recurse into their
    /// sub-operand(s), contributing every distinct `Var` they transitively reference (the
    /// SAME recursive contribution `mirsem::SemOperand::Index`/`Len::var_indices` make).
    fn var_indices(&self, out: &mut Vec<u64>) {
        match self {
            IrOperand::Var(i) | IrOperand::Field(i, _) => {
                if !out.contains(i) {
                    out.push(*i);
                }
            }
            IrOperand::Const(_) => {}
            IrOperand::Index(s, i) => {
                s.var_indices(out);
                i.var_indices(out);
            }
            IrOperand::Len(s) => s.var_indices(out),
        }
    }

    /// `true` IFF this operand is live-grounder-connected (`to_formula` is
    /// live-groundable to the SAME term `evalOperand` reduces to). `Var`/`Const` always
    /// are; `Field` never is (see the variant doc) — the SAME honesty split `UnOp::Not`
    /// carries at the rvalue level. Trust: ptr-spine call-arg leaf — `Index`/`Len` are
    /// ALSO never grounder-connected, for the identical reason `Field` is not (the live
    /// grounder's `Select`/`Pred("slice_len", _)` arms hardcode the `Trust.MirSem.*`
    /// opaques, not `Trust.TrustIr.*`'s).
    /// (`pub(crate)` for Trust: THE LIFT — `prove::call_return_fully_faithful_via_trustir`'s
    /// call-arg lane branches on this to pick the grounder-connected
    /// [`check_operand_refinement`] or the MODEL-ONLY [`check_operand_refinement_model`].)
    pub(crate) fn is_grounder_connected(&self) -> bool {
        matches!(self, IrOperand::Var(_) | IrOperand::Const(_))
    }
}

/// A straight-line trust-ir rvalue: a direct use, a binary op, or a unary op over
/// operands. Keyed to the `trust_ir::Inst` arithmetic subset (`Copy`, `BinOp`, `UnOp`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrRvalue {
    /// `Use op` — `Inst::Copy`.
    Use(IrOperand),
    /// `BinaryOp op a b` — `Inst::BinOp`.
    Bin(TrustIrBinOp, IrOperand, IrOperand),
    /// `UnaryOp op a` — `Inst::UnOp`.
    Un(TrustIrUnOp, IrOperand),
    /// `Cmp op a b` — Trust: M6 rung 9, COMPARE-AS-VALUE — a comparison used as a
    /// Bool-typed 0/1 VALUE, not a branch guard. Grounds via the SAME "Rust bool is
    /// the opaque Int 0/1 carrier" idiom `bool_as_int`/`cmp_bool_expr` establish
    /// elsewhere in this crate (`mirsem::bool_as_int`, `trustir_call::cmp_bool_expr`
    /// — this anchor's OWN hermetic copy, see [`bool_as_int`]/[`cmp_bool_expr`]
    /// below), applied to the two operands' denotations. GROUNDER-CONNECTED: `Eq`/
    /// `Lt`/`Le`/`Gt`/`Ge`/`Ne` reflect to the SAME `Formula` shape
    /// `clean_ground::ground_int`'s COMPARE-AS-VALUE arm (`F::Eq(..) | F::Lt(..) |
    /// … => bool_as_int(ground_bool(f))`) already grounds, so a `Cmp` over
    /// grounder-connected operands is genuinely live-grounder-connected, not merely
    /// model-only.
    Cmp(TrustIrCmpOp, IrOperand, IrOperand),
}

impl IrRvalue {
    /// The closed `Trust.TrustIr.Rvalue` constructor value.
    fn to_rvalue_expr(&self) -> Expr {
        match self {
            IrRvalue::Use(op) => Expr::app(cst(TRUSTIR_RVALUE_USE), op.to_operand_expr()),
            IrRvalue::Bin(op, a, b) => Expr::apps(
                cst(TRUSTIR_RVALUE_BIN),
                [op.ctor_expr(), a.to_operand_expr(), b.to_operand_expr()],
            ),
            IrRvalue::Un(op, a) => {
                Expr::apps(cst(TRUSTIR_RVALUE_UN), [op.ctor_expr(), a.to_operand_expr()])
            }
            IrRvalue::Cmp(op, a, b) => Expr::apps(
                cst(TRUSTIR_RVALUE_CMP),
                [op.ctor_expr(), a.to_operand_expr(), b.to_operand_expr()],
            ),
        }
    }

    /// The reflected `Formula` for this rvalue — EXACTLY the `clean_ground`
    /// reflection. `Not` is the EXCEPTION: it has no integer-grounder formula, so it
    /// reflects to a `Pred("Trust.TrustIr.bnot", [a])` that the live grounder does
    /// NOT recognise — `live_ground_int` returns `None`, the fail-closed signal that
    /// `Not` is not grounder-connected. (Its denotation IS still proven against the
    /// trust-ir model via [`IrRvalue::denotation`].)
    fn to_formula(&self) -> trust_types::Formula {
        use trust_types::Formula as F;
        let bx = |o: &IrOperand| Box::new(o.to_formula());
        match self {
            IrRvalue::Use(op) => op.to_formula(),
            IrRvalue::Bin(TrustIrBinOp::Add, a, b) => F::Add(bx(a), bx(b)),
            IrRvalue::Bin(TrustIrBinOp::Sub, a, b) => F::Sub(bx(a), bx(b)),
            IrRvalue::Bin(TrustIrBinOp::Mul, a, b) => F::Mul(bx(a), bx(b)),
            IrRvalue::Bin(TrustIrBinOp::SDiv, a, b) => F::Div(bx(a), bx(b)),
            // Trust: witness-tier Rem arm — EXACTLY clean_ground's `binop_formula` Rem arm.
            IrRvalue::Bin(TrustIrBinOp::SRem, a, b) => F::Rem(bx(a), bx(b)),
            // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — EXACTLY clean_ground's BITWISE
            // SHAPE LANE `Pred("Int.shiftRight",_)` arm.
            IrRvalue::Bin(TrustIrBinOp::LShr, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.shiftRight"), vec![*bx(a), *bx(b)])
            }
            // Trust: M6 rung 9, ANCHOR BitAnd — EXACTLY clean_ground's BITWISE SHAPE
            // LANE `Pred("Int.land",_)` arm.
            IrRvalue::Bin(TrustIrBinOp::And, a, b) => {
                F::Pred(trust_types::Symbol::intern("Int.land"), vec![*bx(a), *bx(b)])
            }
            IrRvalue::Un(TrustIrUnOp::Neg, a) => F::Neg(bx(a)),
            // `Not` reflects to the canonical opaque-keyed Pred; the live grounder
            // declines it (no integer-Not arm), so `to_formula` is only used for the
            // grounder-connected arms. The model-side denotation uses `bnot` directly.
            IrRvalue::Un(TrustIrUnOp::Not, a) => {
                F::Pred(trust_types::Symbol::intern(TRUSTIR_BNOT), vec![a.to_formula()])
            }
            // Trust: M6 rung 9, COMPARE-AS-VALUE — the SAME comparison relation
            // `IrCond::to_formula` builds for the GUARD leaf, over the two flat
            // operands' OWN formulas — `ground_int`'s COMPARE-AS-VALUE arm grounds
            // this EXACTLY (see `IrRvalue::Cmp`'s doc).
            IrRvalue::Cmp(op, a, b) => op.to_formula(a, b),
        }
    }

    /// The trust-ir-MODEL denotation under `e_ref` — the exact `Int` term
    /// `evalRvalue E R` ι/δ-reduces to. For the grounder-connected arms this is
    /// BYTE-IDENTICAL to `ground_int(to_formula())`; for `Not` it is the opaque
    /// `bnot (evalOperand e a)` (no live-grounder counterpart). Used to build the
    /// body-refinement RHS by inlining each assigned temp.
    fn denotation(&self, e_ref: &Expr) -> Expr {
        match self {
            IrRvalue::Use(op) => operand_denotation(op, e_ref),
            IrRvalue::Bin(op, a, b) => {
                int_binop_expr(*op, operand_denotation(a, e_ref), operand_denotation(b, e_ref))
            }
            IrRvalue::Un(TrustIrUnOp::Neg, a) => Expr::apps(
                cst("Int.sub"),
                [Expr::app(cst("Int.ofNat"), Expr::nat_lit(0)), operand_denotation(a, e_ref)],
            ),
            IrRvalue::Un(TrustIrUnOp::Not, a) => {
                Expr::app(cst(TRUSTIR_BNOT), operand_denotation(a, e_ref))
            }
            // Trust: M6 rung 9, COMPARE-AS-VALUE — `bool_as_int(cmp_bool_expr(op,
            // denot a, denot b))`, this anchor's OWN hermetic port of the SAME
            // "Bool is the opaque Int 0/1 carrier" encoding `mirsem::bool_as_int`/
            // `trustir_call::bool_as_int` establish elsewhere.
            IrRvalue::Cmp(op, a, b) => bool_as_int(cmp_bool_expr(
                *op,
                operand_denotation(a, e_ref),
                operand_denotation(b, e_ref),
            )),
        }
    }

    fn var_indices(&self, out: &mut Vec<u64>) {
        match self {
            IrRvalue::Use(op) => op.var_indices(out),
            IrRvalue::Bin(_, a, b) | IrRvalue::Cmp(_, a, b) => {
                a.var_indices(out);
                b.var_indices(out);
            }
            IrRvalue::Un(_, a) => a.var_indices(out),
        }
    }

    /// `true` IFF every op in this rvalue is grounder-connected (so `to_formula` is
    /// live-groundable). A `Not` anywhere makes it model-only; Trust: field-read leaf —
    /// a `Field` operand anywhere ALSO makes it model-only (propagated through `Use`/
    /// `Bin`/`Un`, previously trivially `true` since `Var`/`Const` were the only operand
    /// forms — this is the REQUIRED soundness propagation, not a behavior change for any
    /// pre-existing `Var`/`Const`-only rvalue, which still reports `true` identically).
    fn is_grounder_connected(&self) -> bool {
        match self {
            IrRvalue::Use(op) => op.is_grounder_connected(),
            IrRvalue::Bin(_, a, b) | IrRvalue::Cmp(_, a, b) => {
                a.is_grounder_connected() && b.is_grounder_connected()
            }
            IrRvalue::Un(op, a) => op.is_grounder_connected() && a.is_grounder_connected(),
        }
    }
}

/// A straight-line SSA assignment `_idx := rvalue` (`Trust.TrustIr.Stmt.Assign`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrStmt {
    /// The assigned SSA index.
    pub idx: u64,
    /// The rvalue bound to it.
    pub rvalue: IrRvalue,
}

impl IrStmt {
    /// The closed `Trust.TrustIr.Stmt` constructor value.
    fn to_stmt_expr(&self) -> Expr {
        Expr::apps(
            cst(TRUSTIR_STMT_ASSIGN),
            [Expr::nat_lit(self.idx), self.rvalue.to_rvalue_expr()],
        )
    }
}

/// A straight-line trust-ir function body: an ordered assignment trace plus the
/// returned operand (`Inst::Return`). The Clean analogue of a single trust-ir
/// basic block with a `Return` terminator and no control flow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrBody {
    /// The (ordered) SSA assignments.
    pub stmts: Vec<IrStmt>,
    /// The returned operand index (`Inst::Return` of `_ret`); must be assigned by
    /// some statement in `stmts` for the body refinement.
    pub ret: u64,
}

impl IrBody {
    /// The closed `List Trust.TrustIr.Stmt` value (`cons s0 (cons s1 … nil)`).
    fn to_stmts_expr(&self) -> Expr {
        let nil =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), stmt_ty());
        self.stmts.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The distinct PARAMETER indices the body reads (operands whose index is NOT
    /// assigned by any statement — i.e. the function's actual inputs), in
    /// first-appearance order. These are the `Int` binders the body refinement
    /// universally quantifies over; the assigned SSA temps are NOT binders (they are
    /// inlined by the env-threading reduction).
    fn param_indices(&self) -> Vec<u64> {
        let assigned: std::collections::HashSet<u64> = self.stmts.iter().map(|s| s.idx).collect();
        let mut all = Vec::new();
        for s in &self.stmts {
            s.rvalue.var_indices(&mut all);
        }
        all.into_iter().filter(|i| !assigned.contains(i)).collect()
    }

    /// The SSA statement that assigns the returned index, if any (SSA: at most one;
    /// defensively the LAST in program order).
    fn return_stmt(&self) -> Option<&IrStmt> {
        self.stmts.iter().rev().find(|s| s.idx == self.ret)
    }

    /// `true` IFF every rvalue in the body is grounder-connected (so the inlined
    /// return formula is live-groundable). A `Not` anywhere makes the body model-only.
    fn is_grounder_connected(&self) -> bool {
        self.stmts.iter().all(|s| s.rvalue.is_grounder_connected())
    }

    /// The reflected `Formula` for the RETURNED value, INLINING each assigned SSA
    /// temp through its defining rvalue (the §6 grounding of a straight-line body
    /// substitutes `_i`'s definition wherever `_i` is read). E.g. for
    /// `_2 := a+b; _3 := _2*c; ret _3` this yields `Mul(Add(a,b), c)` — exactly the
    /// formula `clean_ground` grounds for the whole body. Returns `None` if the
    /// returned index is unassigned (not a straight-line temp body) or a referenced
    /// temp is undefined.
    fn inlined_return_formula(&self) -> Option<trust_types::Formula> {
        // Map each assigned index to its defining rvalue.
        let mut defs: std::collections::HashMap<u64, &IrRvalue> = std::collections::HashMap::new();
        for s in &self.stmts {
            defs.insert(s.idx, &s.rvalue); // later assignment wins (SSA: unique anyway)
        }
        inline_operand_formula(&IrOperand::Var(self.ret), &defs, 0)
    }

    /// Trust: M6 rung 9 — the `Expr`-level (trust-ir MODEL denotation) analogue of
    /// [`IrBody::inlined_return_formula`], for a MULTI-STATEMENT chain that is NOT
    /// grounder-connected (e.g. contains a `Field` leaf): INLINES each assigned SSA
    /// temp through its defining rvalue's OWN [`IrRvalue::denotation`], under the
    /// SAME outer parameter env `env` throughout (every leaf — `Var` of a genuine
    /// parameter, `Const`, `Field`, `Index`, `Len` — denotes an env-invariant value
    /// across the whole chain: `evalBody`'s `set`-threading only ever touches TEMP
    /// indices, which are structurally DISJOINT from parameter `Var` indices — see
    /// `straight_line_ir_body_chain`'s doc in `prove.rs` — so re-using `env`
    /// unchanged at every recursion depth is sound, exactly mirroring
    /// `inlined_return_formula`'s identical leaf-invariance argument at the
    /// `Formula` level). Sound BECAUSE `evalBody`'s reduction is a genuine
    /// SEQUENTIAL env-thread (`register_eval_body`'s `cons_case`: each `step` runs
    /// under the PRIOR step's UPDATED env), so its ι-reduction reconstructs EXACTLY
    /// this same nested term. `None` if the returned index is unassigned or a
    /// referenced temp is undefined.
    fn inlined_return_denotation(&self, env: &Expr) -> Option<Expr> {
        let mut defs: std::collections::HashMap<u64, &IrRvalue> = std::collections::HashMap::new();
        for s in &self.stmts {
            defs.insert(s.idx, &s.rvalue);
        }
        inline_operand_denotation(&IrOperand::Var(self.ret), &defs, env, 0)
    }
}

/// Recursively inline an operand's formula, expanding `Var i` to its defining
/// rvalue's inlined formula when `i` is an assigned SSA temp. `depth` guards against
/// a malformed cyclic def (straight-line SSA is acyclic; the bound is defensive).
fn inline_operand_formula(
    op: &IrOperand,
    defs: &std::collections::HashMap<u64, &IrRvalue>,
    depth: usize,
) -> Option<trust_types::Formula> {
    if depth > 64 {
        return None;
    }
    match op {
        // Trust: field-read leaf — `Field` is never truly live-groundable (see
        // `IrOperand::Field`'s doc), but this LIVE-grounder path is gated by
        // `IrBody::is_grounder_connected` at every call site that matters
        // (`body_refinement_statement`); returning its (non-live-matching) `to_formula`
        // here keeps this fold total without ever reaching a live kernel check. Trust:
        // ptr-spine call-arg leaf — `Index`/`Len` are NEVER produced inside a straight-line
        // BODY (they are call-arg-only, built by `prove::sem_call_arg_to_ir`), but this
        // match must stay exhaustive; they carry the SAME never-live-matching treatment.
        IrOperand::Const(_) | IrOperand::Field(..) | IrOperand::Index(..) | IrOperand::Len(_) => {
            Some(op.to_formula())
        }
        IrOperand::Var(i) => match defs.get(i) {
            // A read of an assigned temp: inline its definition.
            Some(rv) => inline_rvalue_formula(rv, defs, depth + 1),
            // A read of an unassigned index: a genuine function parameter.
            None => Some(op.to_formula()),
        },
    }
}

/// Inline an rvalue's formula, expanding each operand via [`inline_operand_formula`].
fn inline_rvalue_formula(
    rv: &IrRvalue,
    defs: &std::collections::HashMap<u64, &IrRvalue>,
    depth: usize,
) -> Option<trust_types::Formula> {
    use trust_types::Formula as F;
    let g = |o: &IrOperand| inline_operand_formula(o, defs, depth);
    Some(match rv {
        IrRvalue::Use(op) => g(op)?,
        IrRvalue::Bin(TrustIrBinOp::Add, a, b) => F::Add(Box::new(g(a)?), Box::new(g(b)?)),
        IrRvalue::Bin(TrustIrBinOp::Sub, a, b) => F::Sub(Box::new(g(a)?), Box::new(g(b)?)),
        IrRvalue::Bin(TrustIrBinOp::Mul, a, b) => F::Mul(Box::new(g(a)?), Box::new(g(b)?)),
        IrRvalue::Bin(TrustIrBinOp::SDiv, a, b) => F::Div(Box::new(g(a)?), Box::new(g(b)?)),
        // Trust: witness-tier Rem arm.
        IrRvalue::Bin(TrustIrBinOp::SRem, a, b) => F::Rem(Box::new(g(a)?), Box::new(g(b)?)),
        // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR.
        IrRvalue::Bin(TrustIrBinOp::LShr, a, b) => {
            F::Pred(trust_types::Symbol::intern("Int.shiftRight"), vec![g(a)?, g(b)?])
        }
        // Trust: M6 rung 9, ANCHOR BitAnd.
        IrRvalue::Bin(TrustIrBinOp::And, a, b) => {
            F::Pred(trust_types::Symbol::intern("Int.land"), vec![g(a)?, g(b)?])
        }
        IrRvalue::Un(TrustIrUnOp::Neg, a) => F::Neg(Box::new(g(a)?)),
        IrRvalue::Un(TrustIrUnOp::Not, a) => {
            F::Pred(trust_types::Symbol::intern(TRUSTIR_BNOT), vec![g(a)?])
        }
        // Trust: M6 rung 9, COMPARE-AS-VALUE — inline BOTH sides, then apply the
        // SAME `TrustIrCmpOp::to_formula`-shaped dispatch (mirrors that method's own
        // match arms exactly, sourcing `fa`/`fb` from the INLINED formulas instead
        // of `a.to_formula()`/`b.to_formula()` directly).
        IrRvalue::Cmp(op, a, b) => {
            let (fa, fb) = (Box::new(g(a)?), Box::new(g(b)?));
            match op {
                TrustIrCmpOp::Lt => F::Lt(fa, fb),
                TrustIrCmpOp::Le => F::Le(fa, fb),
                TrustIrCmpOp::Eq => F::Eq(fa, fb),
                TrustIrCmpOp::Ne => F::Not(Box::new(F::Eq(fa, fb))),
                TrustIrCmpOp::Gt => F::Gt(fa, fb),
                TrustIrCmpOp::Ge => F::Ge(fa, fb),
            }
        }
    })
}

/// Trust: M6 rung 9 — the `Expr`-level (trust-ir MODEL denotation) analogue of
/// [`inline_operand_formula`], used by [`IrBody::inlined_return_denotation`] for a
/// MULTI-STATEMENT chain that is NOT grounder-connected. `depth` guards against a
/// malformed cyclic def (defensive; straight-line SSA is acyclic).
fn inline_operand_denotation(
    op: &IrOperand,
    defs: &std::collections::HashMap<u64, &IrRvalue>,
    env: &Expr,
    depth: usize,
) -> Option<Expr> {
    if depth > 64 {
        return None;
    }
    match op {
        IrOperand::Var(i) => match defs.get(i) {
            // A read of an assigned temp: inline its definition's OWN denotation.
            Some(rv) => inline_rvalue_denotation(rv, defs, env, depth + 1),
            // A read of an unassigned index: a genuine function parameter — its
            // denotation under the OUTER env (env-invariant across the whole
            // chain — see `inlined_return_denotation`'s doc).
            None => Some(operand_denotation(op, env)),
        },
        _ => Some(operand_denotation(op, env)),
    }
}

/// Trust: M6 rung 9 — the `Expr`-level analogue of [`inline_rvalue_formula`],
/// expanding each operand via [`inline_operand_denotation`].
fn inline_rvalue_denotation(
    rv: &IrRvalue,
    defs: &std::collections::HashMap<u64, &IrRvalue>,
    env: &Expr,
    depth: usize,
) -> Option<Expr> {
    let g = |o: &IrOperand| inline_operand_denotation(o, defs, env, depth);
    Some(match rv {
        IrRvalue::Use(op) => g(op)?,
        IrRvalue::Bin(op, a, b) => int_binop_expr(*op, g(a)?, g(b)?),
        IrRvalue::Cmp(op, a, b) => bool_as_int(cmp_bool_expr(*op, g(a)?, g(b)?)),
        IrRvalue::Un(TrustIrUnOp::Neg, a) => {
            Expr::apps(cst("Int.sub"), [Expr::app(cst("Int.ofNat"), Expr::nat_lit(0)), g(a)?])
        }
        IrRvalue::Un(TrustIrUnOp::Not, a) => Expr::app(cst(TRUSTIR_BNOT), g(a)?),
    })
}

/// The `Int.<op>` head for a trust-ir `BinOp`, BYTE-IDENTICAL to `clean_ground`'s
/// `Formula::{Add,Sub,Mul,Div,Rem}` grounding (and to `evalBin`'s reduct).
fn int_binop_expr(op: TrustIrBinOp, a: Expr, b: Expr) -> Expr {
    let head = match op {
        TrustIrBinOp::Add => "Int.add",
        TrustIrBinOp::Sub => "Int.sub",
        TrustIrBinOp::Mul => "Int.mul",
        TrustIrBinOp::SDiv => "Int.div",
        // Trust: witness-tier Rem arm — the TRUNCATED `Int.mod` (ground_int's F::Rem
        // head; the SAME truncated Int.mod trust-ir's `semIntBinOp .SRem` denotes).
        TrustIrBinOp::SRem => "Int.mod",
        // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — the Opaque `Int.shiftRight` (ground_int's
        // BITWISE SHAPE LANE `Pred("Int.shiftRight",_)` head; the SAME carrier trust-ir's
        // `semIntBinOp .LShr` denotes).
        TrustIrBinOp::LShr => "Int.shiftRight",
        // Trust: M6 rung 9, ANCHOR BitAnd — the Opaque `Int.land` (ground_int's
        // BITWISE SHAPE LANE `Pred("Int.land",_)` head; the SAME carrier
        // `mirsem::register_int_bitwise`'s `BitAnd` arm registers on the MirSem
        // side).
        TrustIrBinOp::And => "Int.land",
    };
    Expr::apps(cst(head), [a, b])
}

/// Trust: M6 rung 9, COMPARE-AS-VALUE — the Bool-valued term for a comparison
/// `TrustIrCmpOp` applied to two ALREADY-BUILT Int exprs. This anchor's OWN
/// hermetic copy of the SAME idiom `mirsem::cmp_bool_expr`/`trustir_call::
/// cmp_bool_expr` establish (byte-for-byte: the SAME prelude primitives
/// `decide`/`Int.lt`/`Int.le`/`Int.beq`/`Bool.not`/`Int.decLt`/`Int.decLe`) —
/// reproduces the EXACT closed-form ground term `register_eval_cond`'s (and this
/// module's NEW `register_eval_rvalue` `cmp_case`) `CmpOp.rec` minor premises
/// reduce to for each op.
fn cmp_bool_expr(op: TrustIrCmpOp, a: Expr, b: Expr) -> Expr {
    let decide_lt = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.lt"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLt"), [x, y]),
            ],
        )
    };
    let decide_le = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.le"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLe"), [x, y]),
            ],
        )
    };
    match op {
        TrustIrCmpOp::Lt => decide_lt(a, b),
        TrustIrCmpOp::Le => decide_le(a, b),
        TrustIrCmpOp::Eq => Expr::apps(cst("Int.beq"), [a, b]),
        TrustIrCmpOp::Ne => Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [a, b])),
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED operands (matches
        // `register_eval_cond`).
        TrustIrCmpOp::Gt => decide_lt(b, a),
        TrustIrCmpOp::Ge => decide_le(b, a),
    }
}

/// Trust: M6 rung 9, COMPARE-AS-VALUE — encode a Bool-valued expr as 0/1 on the
/// `Int` carrier. This anchor's OWN hermetic copy of the SAME `Bool.rec` idiom
/// `mirsem::bool_as_int`/`trustir_call::bool_as_int` establish.
fn bool_as_int(b: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Bool"), int_ty());
    Expr::apps(bool_rec, [motive, int_lit(0), int_lit(1), b])
}

/// The trust-ir-MODEL denotation of an operand under env `e_ref`: `Var i → e i`,
/// `Const c → int_lit c`, `Field paramIdx fld → idxElem (e paramIdx) (int_lit fld)`
/// (Trust: field-read leaf) — the exact reduct of `evalOperand e (Var i)` /
/// `(Const c)` / `(Field paramIdx fld)`. Trust: ptr-spine call-arg leaf — `Index s i →
/// idxElem (denotation s)(denotation i)`, `Len s → sliceLen (denotation s)` — the exact
/// reduct of `evalOperand`'s NEW recursive `Index`/`Len` cases (each IH is exactly the
/// recursive `operand_denotation` call on that sub-operand).
fn operand_denotation(op: &IrOperand, e_ref: &Expr) -> Expr {
    match op {
        IrOperand::Var(i) => Expr::app(e_ref.clone(), Expr::nat_lit(*i)),
        IrOperand::Const(c) => int_lit(*c),
        IrOperand::Field(p, fld) => Expr::apps(
            cst(TRUSTIR_IDX_ELEM),
            [Expr::app(e_ref.clone(), Expr::nat_lit(*p)), int_lit(i128::from(*fld))],
        ),
        IrOperand::Index(s, i) => Expr::apps(
            cst(TRUSTIR_IDX_ELEM),
            [operand_denotation(s, e_ref), operand_denotation(i, e_ref)],
        ),
        IrOperand::Len(s) => Expr::app(cst(TRUSTIR_SLICE_LEN), operand_denotation(s, e_ref)),
    }
}

// ---------------------------------------------------------------------------
// The CONTROL-FLOW trust-ir AST (Rust-side) — comparison ops, branch conditions,
// terminators, blocks, CFGs. Each `to_*_expr` builds the CLOSED Clean term; the
// `inlined_return_formula` reflects the branched §6 grounding the LIVE grounder
// consumes (a `Formula::Ite`). Together they let the BRANCH refinement RELATE the
// trust-ir CFG denotation `evalCfg` to the live grounder.
// ---------------------------------------------------------------------------

/// The integer-comparison fragment of `trust_ir::inst::BinOp` (the `ICmp` predicates) a
/// branch discriminant uses. Each maps to the SAME comparison `Formula`/`ground_bool`
/// arm the live grounder consumes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustIrCmpOp {
    /// `<` — grounds to `decide (Int.lt a b)`.
    Lt,
    /// `<=` — grounds to `decide (Int.le a b)`.
    Le,
    /// `==` — grounds to `Int.beq a b`.
    Eq,
    /// `!=` — grounds to `Bool.not (Int.beq a b)`.
    Ne,
    /// `>` — grounds to the SWAPPED `decide (Int.lt b a)`.
    Gt,
    /// `>=` — grounds to the SWAPPED `decide (Int.le b a)`.
    Ge,
}

impl TrustIrCmpOp {
    /// All six comparison ops.
    pub const ALL: [TrustIrCmpOp; 6] = [
        TrustIrCmpOp::Lt,
        TrustIrCmpOp::Le,
        TrustIrCmpOp::Eq,
        TrustIrCmpOp::Ne,
        TrustIrCmpOp::Gt,
        TrustIrCmpOp::Ge,
    ];

    fn ctor_name(self) -> &'static str {
        match self {
            TrustIrCmpOp::Lt => TRUSTIR_CMPOP_LT,
            TrustIrCmpOp::Le => TRUSTIR_CMPOP_LE,
            TrustIrCmpOp::Eq => TRUSTIR_CMPOP_EQ,
            TrustIrCmpOp::Ne => TRUSTIR_CMPOP_NE,
            TrustIrCmpOp::Gt => TRUSTIR_CMPOP_GT,
            TrustIrCmpOp::Ge => TRUSTIR_CMPOP_GE,
        }
    }

    /// The bare trust-ir comparison-predicate name (the bijection key).
    pub fn trust_ir_name(self) -> &'static str {
        match self {
            TrustIrCmpOp::Lt => "Lt",
            TrustIrCmpOp::Le => "Le",
            TrustIrCmpOp::Eq => "Eq",
            TrustIrCmpOp::Ne => "Ne",
            TrustIrCmpOp::Gt => "Gt",
            TrustIrCmpOp::Ge => "Ge",
        }
    }

    fn ctor_expr(self) -> Expr {
        cst(self.ctor_name())
    }

    /// The reflected comparison `Formula` for `a OP b` — EXACTLY what `clean_ground`'s
    /// `ground_bool` consumes (`Ne` reflects to `Not(Eq(a,b))`, as `ground_bool` expects).
    fn to_formula(self, a: &IrOperand, b: &IrOperand) -> trust_types::Formula {
        use trust_types::Formula as F;
        let fa = Box::new(a.to_formula());
        let fb = Box::new(b.to_formula());
        match self {
            TrustIrCmpOp::Lt => F::Lt(fa, fb),
            TrustIrCmpOp::Le => F::Le(fa, fb),
            TrustIrCmpOp::Eq => F::Eq(fa, fb),
            TrustIrCmpOp::Ne => F::Not(Box::new(F::Eq(fa, fb))),
            TrustIrCmpOp::Gt => F::Gt(fa, fb),
            TrustIrCmpOp::Ge => F::Ge(fa, fb),
        }
    }
}

/// A branch discriminant `Cmp op a b` — the boolean comparison temp a trust-ir
/// `SwitchInt` branches on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrCond {
    /// The comparison op.
    pub op: TrustIrCmpOp,
    /// Left operand.
    pub a: IrOperand,
    /// Right operand.
    pub b: IrOperand,
}

impl IrCond {
    /// The closed `Trust.TrustIr.Cond` constructor value (`Cmp op a b`). `pub(crate)`
    /// for the BRANCHY call-arm sub-axis (`trustir_call`'s composed RHS reuses this
    /// for the SAME `evalCond E cond` guard the branch skeleton already builds).
    pub(crate) fn to_cond_expr(&self) -> Expr {
        Expr::apps(
            cst(TRUSTIR_COND_CMP),
            [self.op.ctor_expr(), self.a.to_operand_expr(), self.b.to_operand_expr()],
        )
    }

    /// The reflected comparison `Formula` (`ground_bool`-shaped).
    fn to_formula(&self) -> trust_types::Formula {
        self.op.to_formula(&self.a, &self.b)
    }

    fn var_indices(&self, out: &mut Vec<u64>) {
        self.a.var_indices(out);
        self.b.var_indices(out);
    }
}

/// A basic-block terminator: `Goto bb | Switch cond thenBB elseBB | Return op`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrTerm {
    /// `Goto bb` — unconditional jump to block `bb`.
    Goto(u64),
    /// `Switch cond thenBB elseBB` — the 2-way bool switch (TRUE → `thenBB`, FALSE →
    /// `elseBB`).
    Switch(IrCond, u64, u64),
    /// `Return op` — return the operand.
    Return(IrOperand),
    /// Trust: BRANCHY call-arm sub-axis — `CallReturn { callee_id, arg, ret_idx }`:
    /// a branch ARM terminated by a certified-callee call, whose value is the
    /// OPAQUE `callResult (Call.mk callee_id arg ret)` the single-call witness
    /// already uses (`trustir_call.rs`). `ret_idx` is a FRESH per-arm env slot
    /// (allocated exactly like an ordinary computed leaf's temp index —
    /// `prove::sem_branch_call_tree_to_ir_cfg`) standing for the callee's
    /// opaque return value.
    ///
    /// ENGINEERING NOTE (why this does NOT add a 4th `Trust.TrustIr.Term`
    /// constructor): `Term`'s registered inductive has exactly 3 constructors,
    /// and `evalCfg`'s registration (`register_eval_cfg`) hand-builds a
    /// `Term.rec` application with exactly 3 minor premises — WIDELY reused by
    /// every straight-line/branch/loop/nested-branch certificate in the
    /// codebase. Adding a literal 4th constructor would require EITHER (a)
    /// editing that shared `Term.rec` application (high blast radius: every
    /// existing registration/certificate depends on `register_eval_cfg`
    /// type-checking, and the natural 4th minor premise needs an extra
    /// "call-result oracle" parameter `evalCfg` has no room for without a
    /// signature change touching every call site), or (b) leaving it
    /// inconsistent (a registration failure). Instead, `to_term_expr` below
    /// lowers `CallReturn` to the EXISTING, UNMODIFIED `Term.Return (Operand.Var
    /// ret_idx)` — `Term`/`Term.rec`/`evalCfg`/`register_eval_cfg` are 100%
    /// UNTOUCHED, so every pre-existing certificate is byte-identical. The
    /// call's OPAQUE semantics are established SEPARATELY, by
    /// `trustir_call::check_branch_call_refinement`, which relates `evalCfg`'s
    /// (unmodified) reduction of this Return-lowered leaf to `callResult
    /// (Call.mk callee_id arg (evalOperand E (Var ret_idx)))` — sound because
    /// `callResult` is a REDUCIBLE `Call.rec` projection: `callResult (Call.mk _
    /// _ X)` ι-reduces to `X` for ANY `X`, so the wrapped and unwrapped forms are
    /// definitionally equal, not merely asserted equal.
    CallReturn { callee_id: u64, arg: IrOperand, ret_idx: u64 },
}

impl IrTerm {
    /// The closed `Trust.TrustIr.Term` constructor value.
    fn to_term_expr(&self) -> Expr {
        match self {
            IrTerm::Goto(bb) => Expr::app(cst(TRUSTIR_TERM_GOTO), Expr::nat_lit(*bb)),
            IrTerm::Switch(cond, t, e) => Expr::apps(
                cst(TRUSTIR_TERM_SWITCH),
                [cond.to_cond_expr(), Expr::nat_lit(*t), Expr::nat_lit(*e)],
            ),
            IrTerm::Return(op) => Expr::app(cst(TRUSTIR_TERM_RETURN), op.to_operand_expr()),
            // Trust: BRANCHY call-arm sub-axis — see the variant doc: lowers to the
            // EXISTING `Term.Return (Operand.Var ret_idx)`, zero new Lean decls.
            IrTerm::CallReturn { ret_idx, .. } => {
                Expr::app(cst(TRUSTIR_TERM_RETURN), IrOperand::Var(*ret_idx).to_operand_expr())
            }
        }
    }
}

/// A basic block: an ordered straight-line statement trace plus a terminator
/// (`Trust.TrustIr.Block.Blk stmts term`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrBlock {
    /// The SSA assignments executed on entry to this block.
    pub stmts: Vec<IrStmt>,
    /// The block's terminator.
    pub term: IrTerm,
}

impl IrBlock {
    /// The closed `Trust.TrustIr.Block` value (`Blk <list stmt> <term>`).
    fn to_block_expr(&self) -> Expr {
        let nil =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), stmt_ty());
        let stmts = self.stmts.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty(), s.to_stmt_expr(), tail],
            )
        });
        Expr::apps(cst(TRUSTIR_BLOCK_MK), [stmts, self.term.to_term_expr()])
    }
}

/// A control-flow graph: an ordered list of basic blocks indexed by block-id, plus the
/// entry block-id (`entry`) and a `fuel` bound for the acyclic/branching executor. The
/// Clean analogue of a trust-ir `Function`'s block table (loops are the NEXT step, so
/// `fuel` need only exceed the longest acyclic path).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrCfg {
    /// The blocks, in block-id order (`blocks[i]` is `bb_i`).
    pub blocks: Vec<IrBlock>,
    /// The entry block-id.
    pub entry: u64,
    /// The fuel bound (must exceed the longest acyclic path through the CFG).
    pub fuel: u64,
}

impl IrCfg {
    /// The closed `Trust.TrustIr.Cfg` (`List Block`) value. `pub(crate)` for the
    /// BRANCHY call-arm sub-axis (`trustir_call::check_branch_call_refinement`
    /// builds the SAME `evalCfg`-applied LHS this crate's other refinement
    /// checks do, from a different module).
    pub(crate) fn to_cfg_expr(&self) -> Expr {
        let nil =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), block_ty());
        self.blocks.iter().rev().fold(nil, |tail, blk| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [block_ty(), blk.to_block_expr(), tail],
            )
        })
    }

    /// The block at index `bb` (the Rust-side mirror of `blockAt`'s lookup).
    fn block_at(&self, bb: u64) -> Option<&IrBlock> {
        self.blocks.get(usize::try_from(bb).ok()?)
    }

    /// The distinct PARAMETER indices the CFG reads — operands referenced (in any block's
    /// stmts, terminators, or switch conditions) whose index is NOT assigned by any
    /// statement in ANY block, in first-appearance order (entry-block first). These are
    /// the `Int` binders the branch refinement universally quantifies over. `pub(crate)`
    /// for the BRANCHY call-arm sub-axis (`trustir_call`'s composition reuses this to
    /// enumerate its ∀-binders, INCLUDING each `CallReturn` leaf's `ret_idx` slot).
    pub(crate) fn param_indices(&self) -> Vec<u64> {
        let assigned: std::collections::HashSet<u64> =
            self.blocks.iter().flat_map(|b| b.stmts.iter().map(|s| s.idx)).collect();
        let mut all: Vec<u64> = Vec::new();
        // Walk in block-id order starting at the entry, then the rest, for a stable order.
        let mut order: Vec<usize> = Vec::new();
        if let Ok(e) = usize::try_from(self.entry) {
            if e < self.blocks.len() {
                order.push(e);
            }
        }
        for i in 0..self.blocks.len() {
            if !order.contains(&i) {
                order.push(i);
            }
        }
        for &i in &order {
            let blk = &self.blocks[i];
            for s in &blk.stmts {
                s.rvalue.var_indices(&mut all);
            }
            match &blk.term {
                IrTerm::Goto(_) => {}
                IrTerm::Switch(cond, _, _) => cond.var_indices(&mut all),
                IrTerm::Return(op) => op.var_indices(&mut all),
                // Trust: BRANCHY call-arm sub-axis — the call's arg AND its opaque
                // `ret_idx` slot are both "read but never assigned" free variables.
                IrTerm::CallReturn { arg, ret_idx, .. } => {
                    arg.var_indices(&mut all);
                    if !all.contains(ret_idx) {
                        all.push(*ret_idx);
                    }
                }
            }
        }
        all.into_iter().filter(|i| !assigned.contains(i)).collect()
    }

    /// The reflected §6 `Formula` for the CFG's RETURNED value, walking from `entry`
    /// through the terminators and INLINING each block's straight-line statements (the
    /// same SSA-temp substitution `IrBody::inlined_return_formula` does), producing a
    /// `Formula::Ite` at each 2-way `Switch`. For the abs-CFG this is
    /// `Ite(Lt(x,0), Neg(x), x)` — EXACTLY the formula `clean_ground` grounds for a
    /// guarded return (`ground_int`'s `F::Ite` arm). `None` (fail-closed) if a block is
    /// missing, a temp is undefined, a non-groundable op (`Not`) appears, or the walk
    /// exceeds `fuel` (a cycle — loops are the next step).
    fn inlined_return_formula(&self) -> Option<trust_types::Formula> {
        // The global SSA def map (every block's assignments; SSA ⇒ unique index).
        let mut defs: std::collections::HashMap<u64, &IrRvalue> = std::collections::HashMap::new();
        for blk in &self.blocks {
            for s in &blk.stmts {
                defs.insert(s.idx, &s.rvalue);
            }
        }
        self.walk_return_formula(self.entry, &defs, self.fuel)
    }

    /// Walk from block `bb`, inlining its terminator into a `Formula`.
    fn walk_return_formula(
        &self,
        bb: u64,
        defs: &std::collections::HashMap<u64, &IrRvalue>,
        fuel: u64,
    ) -> Option<trust_types::Formula> {
        use trust_types::Formula as F;
        if fuel == 0 {
            return None; // out of fuel — a cycle / loop (the next step), fail closed
        }
        let blk = self.block_at(bb)?;
        match &blk.term {
            IrTerm::Goto(tgt) => self.walk_return_formula(*tgt, defs, fuel - 1),
            IrTerm::Return(op) => inline_operand_formula(op, defs, 0),
            // Trust: BRANCHY call-arm sub-axis — NOT grounder-connected: there is no
            // MirSem/§6 `Formula` for an opaque call result. Fail-closed (`None`) so
            // this (UNMODIFIED) grounder-connected path never mints a false claim
            // about a call-armed CFG — it simply declines, exactly as it already
            // does for any other out-of-fragment shape.
            IrTerm::CallReturn { .. } => None,
            IrTerm::Switch(cond, then_bb, else_bb) => {
                // ground_bool only grounds COMPARISON conditions; reflect the cond.
                let cond_f = cond.to_formula();
                let then_f = self.walk_return_formula(*then_bb, defs, fuel - 1)?;
                let else_f = self.walk_return_formula(*else_bb, defs, fuel - 1)?;
                // `ground_int`'s `F::Ite` arm: TRUE arm = then, FALSE arm = else.
                Some(F::Ite(Box::new(cond_f), Box::new(then_f), Box::new(else_f)))
            }
        }
    }

    /// `true` IFF every rvalue across all blocks is grounder-connected (no `Not`), so the
    /// inlined return formula is live-groundable.
    fn is_grounder_connected(&self) -> bool {
        self.blocks.iter().all(|b| b.stmts.iter().all(|s| s.rvalue.is_grounder_connected()))
    }
}

// ---------------------------------------------------------------------------
// The LOOP trust-ir AST (Rust-side) — a bounded `while cond { body }` plus the
// invariant to instantiate the Hoare while-rule with. The Clean analogue of a
// trust-ir loop region with a single back-edge, mirroring `mirsem::SemLoopFunction`
// + its `SynthInvariant` (this anchor wires the GUARD-AWARE upper bound `i ≤ n` for
// the recognized counter loop — exactly `SynthInvariant::CounterLeBound`).
// ---------------------------------------------------------------------------

/// A SYNTHESIZED loop invariant for a recognized counter loop — the trust-ir analogue
/// of `mirsem::SynthInvariant`. The synthesizer PROPOSES the candidate; the kernel
/// VERIFIES preservation (a WRONG proposal does not type-check ⇒ fail-closed). Two forms
/// are wired for the counter loop `while i < n { i := i + 1 }`:
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrLoopInvariant {
    /// `I := λ e. Int.le (e i_idx) (e bound_idx)` — the GUARD-AWARE upper bound `i ≤ n`.
    /// Its preservation `I e → guard → I (evalBody e [i:=i+1])` reduces to
    /// `Int.le ((e i)+1) (e n)`, re-established from the `Lt` guard alone (the guard
    /// `i < n` is DEFINITIONALLY `Int.le (i+1) n`). The hypothesis `hI : i ≤ n` is
    /// genuinely UNNEEDED — the guard re-establishes the bound. Mirrors
    /// `SynthInvariant::CounterLeBound`.
    CounterLeBound { i_idx: u64, bound_idx: u64 },
    /// `I := λ e. Int.le (int_lit c) (e i_idx)` — the inductive LOWER bound `c ≤ i`. Its
    /// preservation `c ≤ i → c ≤ i + 1` USES the hypothesis genuinely (via `Int.le_trans`
    /// + `Int.le_self_add_one`), NOT the guard. Mirrors `SynthInvariant::CounterGeConst`.
    CounterGeConst { i_idx: u64, c: i128 },
    // -- LOOP-BREADTH increment: the OTHER MirSem loop classes ----------------
    /// COUNTDOWN — `I := λ e. Int.le (int_lit 0) (e i_idx)` (`0 ≤ i`) for the `while i > 0
    /// { i := i - 1 }` loop. Its preservation USES the `Gt` guard: from `0 < i` the inline
    /// `countdownGe0` derives `0 ≤ i - 1` (the reduced codomain, since the body decrements
    /// `i`). A non-zero `c` or an INCREMENT body fails closed. Mirrors
    /// `SynthInvariant::CountdownGeConst` (canonical `c = 0`). Only `c = 0` is sound; a
    /// non-zero `c` is kernel-rejected.
    CountdownGeConst { i_idx: u64, c: i128 },
    /// STRIDE — `I := λ e. Int.le (int_lit c) (e i_idx)` (`c ≤ i`) for the `while i < n
    /// { i := i + k }` loop (`k ≥ 1`). Same SHAPE as `CounterGeConst`; the stride `k` only
    /// affects the preservation proof (`Int.le_trans c i (i+k) hI (strideSelfLe k i)`, where
    /// `strideSelfLe k i : i ≤ i+k` is built per-`k` and only retypes for the ACTUAL stride —
    /// a DECREMENT body fails closed). Mirrors `SynthInvariant::StrideGeConst`.
    StrideGeConst { i_idx: u64, c: i128, k: i128 },
    /// ACCUMULATOR (lower bound) — `I := λ e. Int.le (int_lit c) (e s_idx)` (`c ≤ s`), the
    /// lower bound on the ACCUMULATOR `s` (NOT the guard counter `i`), for the MULTI-statement
    /// body `[s := s + 1; i := i + 1]`. Preserved by the SAME inductive step as the counter
    /// lower bound (`Int.le_trans` + `Int.le_self_add_one`) at the accumulator index — the
    /// `i := i+1` statement leaves `s_idx` untouched, so the body's net effect at `s_idx` is
    /// `s + 1`. Mirrors `SynthInvariant::AccumGeConst`.
    AccumGeConst { s_idx: u64, c: i128 },
    /// ACCUMULATOR (relational) — `I := λ e. (e s_idx == e i_idx) ∧ (Int.le (e i_idx) (e
    /// n_idx))` (`s == i ∧ i ≤ n`) for the lockstep body `[s := s + 1; i := i + 1]`. Its
    /// preservation is `And.intro` of (a) the RELATIONAL congruence `s == i → s+1 == i+1`
    /// (`congrArg (·+1)`), USING the hypothesis, and (b) the guard-aware upper bound `i < n →
    /// i+1 ≤ n` (`of_decide_eq_true` on the `Lt` guard). A non-lockstep `s` update (`s := s +
    /// δ`, δ ≠ 1) makes the congruence output NOT def-eq to the reduced codomain ⇒
    /// kernel-rejected. Mirrors `SynthInvariant::AccumEqCounter`.
    AccumEqCounter { s_idx: u64, i_idx: u64, n_idx: u64 },
    // -- §6 FALLBACK-9 RE-ANCHOR increment: the remaining MirSem loop classes --
    /// `≤`-GUARDED CONJOINED RANGE — `I := λ e. (Int.le (int_lit c) (e i_idx)) ∧ (Int.le (e
    /// i_idx) (Int.add (e bound_idx) (int_lit 1)))` (`c ≤ i ∧ i ≤ n+1`) for the `≤`-guarded
    /// counter loop `while i ≤ n { i := i + 1 }` (the `count_le` shape). The `Le` guard is
    /// WEAKER than `Lt`: it re-establishes only `i ≤ n+1` (NOT `i ≤ n`, FALSE after the last
    /// iteration at `i = n` where `i` becomes `n+1`). Preservation is `And.intro` of (a) the
    /// inductive lower bound `c ≤ i → c ≤ i+1` (`Int.le_trans` + `Int.le_self_add_one`, USES the
    /// hypothesis) and (b) the guard-aware upper bound `i ≤ n → i+1 ≤ n+1` (`Int.add_le_add_right`
    /// on the `Le` guard). A too-tight `i ≤ n` codomain that the `Le` guard does NOT provide is
    /// kernel-rejected. Mirrors `SynthInvariant::CounterInRangeSucc`.
    CounterInRangeSucc { i_idx: u64, c: i128, bound_idx: u64 },
    /// GENERAL RELATIONAL ACCUMULATOR SET — `I := λ e. (a₀ == i) ∧ (a₁ == i) ∧ … ∧ (aₘ == i) ∧
    /// (i ≤ n)` for the >2-local lockstep loop `while i < n { a₀:=a₀+1; …; aₘ:=aₘ+1; i:=i+1 }`
    /// (the `three`/`four`/`three_ret_b` shape). GENERALIZES the 2-var [`AccumEqCounter`] (`s ==
    /// i`) to a SET of relational equalities — a fact the 2-var relational domain cannot express.
    /// `accum_idxs` is the ORDERED accumulator env index set `[a₀, …, aₘ]` (length ≥ 1). The
    /// invariant is a NESTED right-folded `And` (a₀ outermost). Preservation is a NESTED right-
    /// folded `And.intro`: one congruence step `aₖ == i → aₖ+1 == i+1` (`congrArg (·+1)`, USES the
    /// projected hypothesis) per accumulator, capped by the guard-aware upper bound `i+1 ≤ n` from
    /// the `Lt` guard. A WRONG relational claim (`aₖ == i + δ`, δ ≠ 0, or a non-lockstep `aₖ`
    /// update) makes that conjunct's reduced codomain NOT def-eq ⇒ kernel-rejected. Mirrors
    /// `SynthInvariant::AccumEqCounterSet` (PRESERVATION is independent of which accumulator the
    /// return reads — `ret_idx` does not appear in the invariant / preservation).
    AccumEqCounterSet { accum_idxs: Vec<u64>, i_idx: u64, n_idx: u64 },
}

/// A bounded trust-ir loop function `while cond { body }` carrying the invariant to
/// instantiate the Hoare while-rule with — the trust-ir analogue of
/// `mirsem::SemLoopFunction`. For the recognized counter loop `count_to`:
/// `i := 0; while i < n { i := i + 1 }; ret i` the loop part is `cond = (i < n)`,
/// `body = [i := i + 1]`, with the `CounterLeBound { i, n }` invariant `i ≤ n`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrLoop {
    /// The loop guard `while cond { … }` (a single comparison).
    pub cond: IrCond,
    /// The loop body's ordered SSA assignment trace.
    pub body: Vec<IrStmt>,
    /// The invariant to instantiate the while-rule with.
    pub inv: IrLoopInvariant,
}

impl IrLoop {
    /// The closed `Trust.TrustIr.Cond` value for the guard.
    // Trust: visibility-only (`pub(crate)`) for the trust-ir termination port
    // (`trustir_termination.rs`) — the instance builders there must pin the
    // BYTE-IDENTICAL guard/body/invariant terms the partial-correctness witness pins.
    pub(crate) fn cond_expr(&self) -> Expr {
        self.cond.to_cond_expr()
    }

    /// The closed `List Trust.TrustIr.Stmt` value for the body.
    // Trust: visibility-only (`pub(crate)`) for the trust-ir termination port.
    pub(crate) fn body_expr(&self) -> Expr {
        let nil =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), stmt_ty());
        self.body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The invariant `I : Env → Prop` as a closed `λ (e : Env). <prop>` term. `claimed`
    /// overrides the invariant (the fail-closed hook). Under `λ e`: e = bvar(0).
    // Trust: visibility-only (`pub(crate)`) for the trust-ir termination port.
    pub(crate) fn invariant_expr(&self, claimed: Option<&IrLoopInvariant>) -> Expr {
        let bd = || BinderData::from(BinderInfo::Default);
        let inv = claimed.unwrap_or(&self.inv);
        let prop = match inv {
            IrLoopInvariant::CounterLeBound { i_idx, bound_idx } => {
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_b = Expr::app(Expr::bvar(0), Expr::nat_lit(*bound_idx));
                Expr::apps(cst("Int.le"), [e_i, e_b])
            }
            IrLoopInvariant::CounterGeConst { i_idx, c } => {
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                Expr::apps(cst("Int.le"), [int_lit(*c), e_i])
            }
            // COUNTDOWN / STRIDE / ACCUM-GE all share the lower-bound SHAPE `c ≤ <index>`;
            // only the preservation proof differs (the body shape determines the codomain).
            IrLoopInvariant::CountdownGeConst { i_idx, c }
            | IrLoopInvariant::StrideGeConst { i_idx, c, .. } => {
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                Expr::apps(cst("Int.le"), [int_lit(*c), e_i])
            }
            IrLoopInvariant::AccumGeConst { s_idx, c } => {
                let e_s = Expr::app(Expr::bvar(0), Expr::nat_lit(*s_idx));
                Expr::apps(cst("Int.le"), [int_lit(*c), e_s])
            }
            IrLoopInvariant::AccumEqCounter { s_idx, i_idx, n_idx } => {
                // I := λ e. And (@Eq Int (e s_idx) (e i_idx)) (Int.le (e i_idx) (e n_idx)).
                let e_s = Expr::app(Expr::bvar(0), Expr::nat_lit(*s_idx));
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_n = Expr::app(Expr::bvar(0), Expr::nat_lit(*n_idx));
                let eq = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [int_ty(), e_s, e_i.clone()],
                );
                let le = Expr::apps(cst("Int.le"), [e_i, e_n]);
                Expr::apps(cst("And"), [eq, le])
            }
            IrLoopInvariant::CounterInRangeSucc { i_idx, c, bound_idx } => {
                // I := λ e. And (Int.le (int_lit c) (e i_idx)) (Int.le (e i_idx) ((e bound_idx)+1)).
                let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(*i_idx));
                let e_b = Expr::app(Expr::bvar(0), Expr::nat_lit(*bound_idx));
                let b1 = Expr::apps(cst("Int.add"), [e_b, int_one()]);
                let lo = Expr::apps(cst("Int.le"), [int_lit(*c), e_i.clone()]);
                let hi = Expr::apps(cst("Int.le"), [e_i, b1]);
                Expr::apps(cst("And"), [lo, hi])
            }
            IrLoopInvariant::AccumEqCounterSet { accum_idxs, i_idx, n_idx } => {
                // I := λ e. (a₀ == i) ∧ (a₁ == i) ∧ … ∧ (aₘ == i) ∧ (i ≤ n) — a NESTED right-
                // folded `And` of the relational equalities, capped by the upper bound. BYTE-
                // IDENTICAL shape to `mirsem`'s `SynthInvariant::AccumEqCounterSet` invariant_expr.
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
                // Right-fold `aₖ == i` over the cap (iterate in REVERSE so `a₀ == i` ends OUTERMOST).
                for &a_idx in accum_idxs.iter().rev() {
                    let eq = eq_of(e_at(a_idx), e_i.clone());
                    acc = Expr::apps(cst("And"), [eq, acc]);
                }
                acc
            }
        };
        Expr::lam(bd(), env_ty(), prop)
    }
}

/// A bounded trust-ir BREAK / EARLY-EXIT loop `while cond { if brk { break } body }` — the
/// trust-ir analogue of `mirsem::SemBreakLoopFunction`. The body runs only when the COMBINED
/// guard `cond ∧ ¬brk` is true; the synthesized invariant holds at BOTH exit points (guard
/// false OR break). Today the wired invariant is the GUARD-AWARE upper bound `i ≤ n`
/// (`CounterLeBound`) for the recognized counter shape `while i < n { if brk { break } i :=
/// i + 1 }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrBreakLoop {
    /// The loop guard `while cond { … }`.
    pub cond: IrCond,
    /// The BREAK condition `if brk { break }` at the top of the body.
    pub brk: IrCond,
    /// The loop body's ordered SSA assignment trace (the part AFTER the break check).
    pub body: Vec<IrStmt>,
    /// The synthesized invariant — the guard-aware upper bound `i ≤ n` (today only
    /// `CounterLeBound` is wired for the break shape; other forms are deferred).
    pub inv: IrLoopInvariant,
}

impl IrBreakLoop {
    /// The closed `Trust.TrustIr.Cond` value for the loop guard.
    fn cond_expr(&self) -> Expr {
        self.cond.to_cond_expr()
    }

    /// The closed `Trust.TrustIr.Cond` value for the break condition.
    fn brk_expr(&self) -> Expr {
        self.brk.to_cond_expr()
    }

    /// The closed `List Trust.TrustIr.Stmt` value for the body's SSA trace.
    fn body_expr(&self) -> Expr {
        let nil =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), stmt_ty());
        self.body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The invariant `I : Env → Prop` as a closed term — reuses the SAME `IrLoop::invariant_expr`
    /// builder (so the break and non-break paths pin BYTE-IDENTICAL invariants for the same
    /// `IrLoopInvariant`). `claimed` overrides the invariant (the fail-closed hook).
    fn invariant_expr(&self, claimed: Option<&IrLoopInvariant>) -> Expr {
        let lf = IrLoop { cond: self.cond.clone(), body: self.body.clone(), inv: self.inv.clone() };
        lf.invariant_expr(claimed)
    }
}

// ---------------------------------------------------------------------------
// Step 1 — the `Trust.TrustIr.BinOp` inductive
// ---------------------------------------------------------------------------

/// Register the `Trust.TrustIr.BinOp` inductive (idempotent):
///
/// ```text
/// inductive BinOp : Type where
///   | Add  : BinOp
///   | Sub  : BinOp
///   | Mul  : BinOp
///   | SDiv : BinOp
///   | SRem : BinOp
///   | LShr : BinOp
/// ```
///
/// Six nullary constructors over `Type`; its axiom closure is `⊆ {propext,
/// Quot.sound, Classical.choice}`. The names mirror `trust_ir::inst::BinOp`.
/// `SRem` — Trust: witness-tier Rem arm — is the fifth (nullary) constructor;
/// the auto-derived recursor gains a fifth minor premise that existing
/// `Add`/`Sub`/`Mul`/`SDiv` ι-reductions ignore, so every prior certificate
/// stays def-eq. `LShr` — Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — is the sixth
/// (nullary) constructor, added the SAME additive-append way: the recursor
/// gains a sixth minor premise every prior ι-reduction ignores.
fn register_binop_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_BINOP);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let nullary = |n: &str| Constructor { name: Name::from_string(n), type_: binop_ty() };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                nullary(TRUSTIR_BINOP_ADD),
                nullary(TRUSTIR_BINOP_SUB),
                nullary(TRUSTIR_BINOP_MUL),
                nullary(TRUSTIR_BINOP_SDIV),
                // Trust: witness-tier Rem arm — the fifth (nullary) constructor.
                nullary(TRUSTIR_BINOP_SREM),
                // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — the sixth (nullary) constructor.
                nullary(TRUSTIR_BINOP_LSHR),
                // Trust: M6 rung 9, ANCHOR BitAnd — the seventh (nullary) constructor.
                nullary(TRUSTIR_BINOP_AND),
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.BinOp): {e:?}"))?;
    Ok(())
}

/// Register the Opaque `Int.shiftRight : Int → Int → Int` constant (idempotent) — the
/// SAME "opaque, total, asserts nothing about the value" honesty tier `Int.div`/
/// `Int.mod` already establish in the shared prelude, and BYTE-IDENTICAL in name/type/
/// placeholder-body discipline to `mirsem::register_int_bitwise`'s `Int.shiftRight` arm
/// (this anchor's OWN environment is built fresh from `Environment::with_prelude()`, so
/// it does not inherit MirSem's registration — this is the trust-ir anchor's own copy of
/// the SAME carrier, not a second DIFFERENT opaque). Must run before
/// `register_binop_inductive`/`register_eval_bin`/`register_eval_rvalue` so `Int.
/// shiftRight` is a resolvable constant by the time they reference it.
fn register_int_shr(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_binop_ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
    let placeholder = {
        let zero = int_lit(0);
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), zero))
    };
    env.add_decl_if_absent(Declaration::Opaque {
        name: Name::from_string("Int.shiftRight"),
        level_params: vec![],
        type_: int_binop_ty,
        value: placeholder,
    })
    .map_err(|e| format!("add_decl(Int.shiftRight): {e:?}"))?;
    Ok(())
}

/// Register the Opaque `Int.land : Int → Int → Int` constant (idempotent) — Trust: M6
/// rung 9, ANCHOR BitAnd. The SAME "opaque, total, asserts nothing about the value"
/// honesty tier `Int.div`/`Int.mod`/`Int.shiftRight` already establish, and
/// BYTE-IDENTICAL in name/type/placeholder-body discipline to [`register_int_shr`]
/// (this anchor's own copy of the SAME `Int.land` carrier
/// `mirsem::register_int_bitwise` registers on the MirSem side — this anchor's
/// environment is built fresh, so it does not inherit that registration). Must run
/// before `register_binop_inductive`/`register_eval_bin`/`register_eval_rvalue` so
/// `Int.land` is a resolvable constant by the time they reference it.
fn register_int_land(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_binop_ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
    let placeholder = {
        let zero = int_lit(0);
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), zero))
    };
    env.add_decl_if_absent(Declaration::Opaque {
        name: Name::from_string("Int.land"),
        level_params: vec![],
        type_: int_binop_ty,
        value: placeholder,
    })
    .map_err(|e| format!("add_decl(Int.land): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalBin : Env → BinOp → Nat → Nat → Int` (idempotent).
///
/// ```text
/// evalBin (e : Env) (op : BinOp) (i j : Nat) : Int :=
///   BinOp.rec (λ_:BinOp. Int)
///     (Int.add (e i) (e j))   -- Add
///     (Int.sub (e i) (e j))   -- Sub
///     (Int.mul (e i) (e j))   -- Mul
///     (Int.div (e i) (e j))   -- SDiv  (opaque Int.div; matches ground_int F::Div)
///     (Int.mod (e i) (e j))   -- SRem  (opaque Int.mod; matches ground_int F::Rem)
///     (Int.shiftRight (e i) (e j))   -- LShr  (opaque Int.shiftRight; matches
///                                        ground_int's Pred("Int.shiftRight",_) arm)
///     op
/// ```
///
/// `Int.add`/`sub`/`mul` are the prelude's reducible `Int.rec` definitions;
/// `Int.div`/`Int.mod`/`Int.shiftRight` are opaque (native-reduced/placeholder)
/// constants. NONE is an `Axiom`, so `evalBin` carries no non-foundational axiom. The
/// `Int.<op>` head and `(e i) (e j)` argument order are BYTE-IDENTICAL to what
/// `clean_ground::ground_int` emits for `Formula::{Add,Sub,Mul,Div,Rem}` / the BITWISE
/// SHAPE LANE's `Pred("Int.shiftRight",_)` arm — the `SRem` minor (Trust: witness-tier
/// Rem arm) denotes the SAME truncated `Int.mod` trust-ir's `semIntBinOp .SRem`
/// evaluates, and the `LShr` minor (Trust: M6 rung 6) the SAME `Int.shiftRight` trust-ir's
/// `semIntBinOp .LShr` evaluates, so the refinement def-eq closes by ι-reduction alone.
fn register_eval_bin(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_BIN);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);

    // evalBin : Env → BinOp → Nat → Nat → Int
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), binop_ty(), Expr::pi(bd(), nat_ty(), Expr::pi(bd(), nat_ty(), int_ty()))),
    );

    // Inside `λ(e:Env). λ(op:BinOp). λ(i:Nat). λ(j:Nat). …`:
    //   bvar(0)=j, bvar(1)=i, bvar(2)=op, bvar(3)=e.
    let e_ref = || Expr::bvar(3);
    let i_ref = || Expr::bvar(1);
    let j_ref = || Expr::bvar(0);
    // (e i) and (e j) — the parameter lookups; BYTE-IDENTICAL to the env-applied
    // binders `ground_int` emits for `Var "_1"` / `Var "_2"` under the same env.
    let ei = || Expr::app(e_ref(), i_ref());
    let ej = || Expr::app(e_ref(), j_ref());
    let int_op = |head: &str| Expr::apps(cst(head), [ei(), ej()]);

    let binop_rec =
        Expr::const_(Name::from_string(TRUSTIR_BINOP_REC), vec![Level::succ(Level::zero())]);
    let binop_motive = Expr::lam(bd(), binop_ty(), int_ty());
    // BinOp.rec.{1} motive (Add) (Sub) (Mul) (SDiv) (SRem) (LShr) op
    let dispatch = Expr::apps(
        binop_rec,
        [
            binop_motive,
            int_op("Int.add"),
            int_op("Int.sub"),
            int_op("Int.mul"),
            int_op("Int.div"),
            // Trust: witness-tier Rem arm — the fifth minor premise (Opaque `Int.mod`).
            int_op("Int.mod"),
            // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — the sixth minor premise (Opaque
            // `Int.shiftRight`).
            int_op("Int.shiftRight"),
            // Trust: M6 rung 9, ANCHOR BitAnd — the seventh minor premise (Opaque
            // `Int.land`).
            int_op("Int.land"),
            Expr::bvar(2), // op
        ],
    );
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), binop_ty(), Expr::lam(bd(), nat_ty(), Expr::lam(bd(), nat_ty(), dispatch))),
    );

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalBin): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// STRAIGHT-LINE FRAGMENT — Operand / evalOperand
// ---------------------------------------------------------------------------

/// Register `Trust.TrustIr.Operand` (idempotent):
///
/// ```text
/// inductive Operand : Type where
///   | Var   : Nat → Operand
///   | Const : Int → Operand
///   | Field : Nat → Nat → Operand      -- Trust: field-read leaf
///   | Index : Operand → Operand → Operand   -- Trust: ptr-spine call-arg leaf
///   | Len   : Operand → Operand             -- Trust: ptr-spine call-arg leaf
/// ```
///
/// `Var`/`Const`/`Field` are non-recursive over the prelude's axiom-free `Nat`/`Int`.
/// `Index`/`Len` are the ADDITIVE fourth/fifth constructors, RECURSIVE in their
/// `Operand` field(s) — mirrors `Trust.MirSem.Operand.Index`/`Len`'s already-proven
/// encoding (`mirsem::register_operand_inductive`) byte-for-byte, so the auto-derived
/// recursor threads an induction hypothesis through each field exactly like
/// `Trust.MirSem.Operand.rec` already does. Adding them does NOT change `Var`/`Const`/
/// `Field` (same constructors, same types); the recursor simply gains two more minor
/// premises that existing reductions ignore, so every prior operand certificate stays
/// def-eq. The transitive axiom closure stays `⊆ {propext, Quot.sound,
/// Classical.choice}` (the recursive fields add no axiom — `Operand` itself carries
/// none, and the auto-derived recursor is a kernel primitive, not an axiom).
fn register_operand_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_OPERAND);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let var_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OPERAND_VAR),
        type_: Expr::pi(bd(), nat_ty(), operand_ty()),
    };
    let const_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OPERAND_CONST),
        type_: Expr::pi(bd(), int_ty(), operand_ty()),
    };
    // Trust: field-read leaf — `Field (paramIdx fld : Nat) : Operand`.
    let field_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OPERAND_FIELD),
        type_: Expr::pi(bd(), nat_ty(), Expr::pi(bd(), nat_ty(), operand_ty())),
    };
    // Trust: ptr-spine call-arg leaf — `Index : Operand → Operand → Operand`, recursive
    // in BOTH fields (mirrors `mirsem::register_operand_inductive`'s `index_ctor`).
    let index_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OPERAND_INDEX),
        type_: Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), operand_ty())),
    };
    // Trust: ptr-spine call-arg leaf — `Len : Operand → Operand`, recursive in its one
    // field (mirrors `mirsem::register_operand_inductive`'s `len_ctor`).
    let len_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OPERAND_LEN),
        type_: Expr::pi(bd(), operand_ty(), operand_ty()),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![var_ctor, const_ctor, field_ctor, index_ctor, len_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Operand): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalOperand : Env → Operand → Int` (idempotent):
///
/// ```text
/// evalOperand (e : Env) : Operand → Int
///   | Var idx        => e idx
///   | Const c        => c
///   | Field paramIdx fld => idxElem (e paramIdx) (Int.ofNat fld)   -- Trust: field-read leaf
///   | Index s i      => idxElem (evalOperand e s) (evalOperand e i)  -- Trust: ptr-spine call-arg leaf
///   | Len s          => sliceLen (evalOperand e s)                  -- Trust: ptr-spine call-arg leaf
/// ```
///
/// A non-dependent `Operand.rec` fold. `Var idx → e idx` is the env application the
/// LIVE grounder denotes a `Formula::Var` to (under the grounding env); `Const c → c`
/// is the SAME closed literal `ground_int(Int c)` emits; `Field paramIdx fld` REUSES the
/// opaque total `idxElem` selector (already registered by `register_idx_elem_ir`, which
/// `trustir_env` now runs BEFORE this registration) — the trust-ir analogue of
/// `mirsem::eval`'s `Index` reuse. Trust: ptr-spine call-arg leaf — the ADDITIVE
/// `Index`/`Len` minor premises mirror `mirsem::register_eval`'s `index_case`/
/// `len_case` byte-for-byte: each recursive field binds its OWN induction hypothesis
/// (an `Int`, supplied by the recursor — with the constant `Int` motive it IS
/// `evalOperand e <field>`), so `idxElem ih_s ih_i` / `sliceLen ih_s` realize exactly
/// the equations above without re-deriving `e`. `idxElem`/`sliceLen` are
/// `Declaration::Opaque`, NOT `Axiom`s, so these arms add no non-foundational axiom
/// dependency. Requires `TRUSTIR_IDX_ELEM`/`TRUSTIR_SLICE_LEN` pre-registered.
fn register_eval_operand(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_OPERAND);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), operand_ty(), int_ty()));
    let operand_rec =
        Expr::const_(Name::from_string(TRUSTIR_OPERAND_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), operand_ty(), int_ty());
    // Var case: λ(idx : Nat). e idx — under this binder idx=bvar(0), op=bvar(1), e=bvar(2).
    let var_case = Expr::lam(bd(), nat_ty(), Expr::app(Expr::bvar(2), Expr::bvar(0)));
    // Const case: λ(c : Int). c
    let const_case = Expr::lam(bd(), int_ty(), Expr::bvar(0));
    // Trust: field-read leaf — Field case: λ(paramIdx fld : Nat). idxElem (e paramIdx)
    // (Int.ofNat fld) — under the innermost (fld) binder: fld=bvar(0), paramIdx=bvar(1),
    // op=bvar(2), e=bvar(3).
    let field_case = Expr::lam(
        bd(),
        nat_ty(),
        Expr::lam(
            bd(),
            nat_ty(),
            Expr::apps(
                cst(TRUSTIR_IDX_ELEM),
                [
                    Expr::app(Expr::bvar(3), Expr::bvar(1)),
                    Expr::app(cst("Int.ofNat"), Expr::bvar(0)),
                ],
            ),
        ),
    );
    // Trust: ptr-spine call-arg leaf — ADDITIVE Index case (the new minor premise for
    // `Index : Operand → Operand → Operand`). A recursive ctor with TWO recursive
    // fields binds the two fields THEN the two induction hypotheses (the SAME
    // `mirsem::register_eval` `index_case` convention): λ(s:Operand). λ(i:Operand).
    // λ(ih_s:Int). λ(ih_i:Int). idxElem ih_s ih_i. With the constant `Int` motive the
    // IHs ARE `evalOperand e s` / `evalOperand e i`, so the arm computes exactly
    // `idxElem (evalOperand e s) (evalOperand e i)`. de-Bruijn at the body:
    // ih_i=bvar(0), ih_s=bvar(1), i=bvar(2), s=bvar(3).
    let index_case = {
        let body = Expr::apps(cst(TRUSTIR_IDX_ELEM), [Expr::bvar(1), Expr::bvar(0)]);
        Expr::lam(
            bd(),
            operand_ty(),
            Expr::lam(
                bd(),
                operand_ty(),
                Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
            ),
        )
    };
    // Trust: ptr-spine call-arg leaf — ADDITIVE Len case (the new minor premise for
    // `Len : Operand → Operand`). One recursive field, so it binds the field THEN its
    // IH (the SAME `mirsem::register_eval` `len_case` convention): λ(s:Operand).
    // λ(ih_s:Int). sliceLen ih_s. s=bvar(1), ih_s=bvar(0).
    let len_case = {
        let body = Expr::app(cst(TRUSTIR_SLICE_LEN), Expr::bvar(0));
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), body))
    };
    // Operand.rec.{1} motive var_case const_case field_case index_case len_case op — the
    // `index_case`/`len_case` minors are APPENDED after the unchanged Var/Const/Field
    // minors, so those reductions are preserved byte-for-byte.
    let rec_app = Expr::apps(
        operand_rec,
        [motive, var_case, const_case, field_case, index_case, len_case, Expr::bvar(0)],
    );
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), operand_ty(), rec_app));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalOperand): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// STRAIGHT-LINE FRAGMENT — UnOp / bnot
// ---------------------------------------------------------------------------

/// Register `Trust.TrustIr.UnOp` (idempotent), an enumeration `Neg | Not`. Nullary
/// constructors ⇒ axiom closure `⊆ {propext, Quot.sound, Classical.choice}`.
fn register_unop_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_UNOP);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let nullary = |n: &str| Constructor { name: Name::from_string(n), type_: unop_ty() };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![nullary(TRUSTIR_UNOP_NEG), nullary(TRUSTIR_UNOP_NOT)],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.UnOp): {e:?}"))?;
    Ok(())
}

/// Register the opaque `Trust.TrustIr.bnot : Int → Int` (idempotent) — the
/// UNINTERPRETED bitwise-complement selector for `UnOp::Not`. The `idx_elem` pattern:
/// a `Declaration::Opaque` whose placeholder body the kernel never unfolds, so
/// `bnot x ≡ bnot y` IFF `x ≡ y` (a fresh uninterpreted symbol). `Opaque` is NOT a
/// `ConstantKind::Axiom`, so a term naming `bnot` gains no axiom dependency.
fn register_bnot(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_BNOT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), int_ty(), int_ty());
    let placeholder = Expr::lam(bd(), int_ty(), int_lit(0));
    env.add_decl(Declaration::Opaque { name, level_params: vec![], type_: ty, value: placeholder })
        .map_err(|e| format!("add_decl(bnot): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// STRAIGHT-LINE FRAGMENT — Rvalue / evalRvalue
// ---------------------------------------------------------------------------

/// Register `Trust.TrustIr.Rvalue` (idempotent):
///
/// ```text
/// inductive Rvalue : Type where
///   | Use      : Operand → Rvalue
///   | BinaryOp : BinOp → Operand → Operand → Rvalue
///   | UnaryOp  : UnOp  → Operand → Rvalue
///   | Cmp      : CmpOp → Operand → Operand → Rvalue   -- Trust: M6 rung 9, COMPARE-AS-VALUE
/// ```
///
/// Every field is another (non-recursive) inductive, so the recursor minors take the
/// fields with no induction hypothesis. Requires `Operand`/`BinOp`/`UnOp`/`CmpOp`
/// registered — `CmpOp` (Trust: M6 rung 9) is now registered EARLIER, before this call,
/// in `trustir_env()` (moved up from its original CONTROL-FLOW-FRAGMENT position) so its
/// name resolves here.
fn register_rvalue_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_RVALUE);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let use_ctor = Constructor {
        name: Name::from_string(TRUSTIR_RVALUE_USE),
        type_: Expr::pi(bd(), operand_ty(), rvalue_ty()),
    };
    let bin_ctor = Constructor {
        name: Name::from_string(TRUSTIR_RVALUE_BIN),
        type_: Expr::pi(
            bd(),
            binop_ty(),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), rvalue_ty())),
        ),
    };
    let un_ctor = Constructor {
        name: Name::from_string(TRUSTIR_RVALUE_UN),
        type_: Expr::pi(bd(), unop_ty(), Expr::pi(bd(), operand_ty(), rvalue_ty())),
    };
    // Trust: M6 rung 9, COMPARE-AS-VALUE — the fourth (ADDITIVE) constructor.
    let cmp_ctor = Constructor {
        name: Name::from_string(TRUSTIR_RVALUE_CMP),
        type_: Expr::pi(
            bd(),
            cmpop_ty(),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), rvalue_ty())),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![use_ctor, bin_ctor, un_ctor, cmp_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Rvalue): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalRvalue : Env → Rvalue → Int` (idempotent):
///
/// ```text
/// evalRvalue (e : Env) : Rvalue → Int
///   | Use op        => evalOperand e op
///   | BinaryOp o a b => BinOp.rec (λ_.Int) (Int.add …) (Int.sub …) (Int.mul …) (Int.div …) (Int.mod …) (Int.shiftRight …) o
///   | UnaryOp o a    => UnOp.rec  (λ_.Int) (Int.sub (Int.ofNat 0) (evalOperand e a)) (bnot (evalOperand e a)) o
/// ```
///
/// The `Add/Sub/Mul/Div/Rem` heads and `Int.sub 0 (·)` (for `Neg`) are BYTE-IDENTICAL
/// to `clean_ground::ground_int`'s arms (`Int.mod` — Trust: witness-tier Rem arm — is
/// the `SRem` minor, `ground_int`'s `F::Rem` head; `Int.shiftRight` — Trust: M6 rung 6,
/// SHR→TRUST-IR ANCHOR — is the `LShr` minor, `ground_int`'s BITWISE SHAPE LANE
/// `Pred("Int.shiftRight",_)` head); `bnot (·)` (for `Not`) is the opaque selector.
/// `evalOperand`/`BinOp.rec`/`UnOp.rec`/`Int.*`/`bnot` are all DEFINITIONS/`Opaque`, so
/// `evalRvalue` carries no non-foundational axiom.
fn register_eval_rvalue(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_RVALUE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let lvl1 = || vec![Level::succ(Level::zero())];
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), rvalue_ty(), int_ty()));

    let rvalue_rec = Expr::const_(Name::from_string(TRUSTIR_RVALUE_REC), lvl1());
    let binop_rec = Expr::const_(Name::from_string(TRUSTIR_BINOP_REC), lvl1());
    let unop_rec = Expr::const_(Name::from_string(TRUSTIR_UNOP_REC), lvl1());
    let eval_op = cst(TRUSTIR_EVAL_OPERAND);

    let motive = Expr::lam(bd(), rvalue_ty(), int_ty());

    // Use case: λ(op:Operand). evalOperand e op — op=bvar(0), rv=bvar(1), e=bvar(2).
    let use_case =
        Expr::lam(bd(), operand_ty(), Expr::apps(eval_op.clone(), [Expr::bvar(2), Expr::bvar(0)]));

    // BinaryOp case: λ(o:BinOp). λ(a:Operand). λ(b:Operand). BinOp.rec … o
    //   under the three binders: b=bvar(0), a=bvar(1), o=bvar(2), rv=bvar(3), e=bvar(4).
    let bin_case = {
        let e_ref = || Expr::bvar(4);
        let eval_a = || Expr::apps(eval_op.clone(), [e_ref(), Expr::bvar(1)]);
        let eval_b = || Expr::apps(eval_op.clone(), [e_ref(), Expr::bvar(0)]);
        let binop_motive = Expr::lam(bd(), binop_ty(), int_ty());
        let dispatch = Expr::apps(
            binop_rec,
            [
                binop_motive,
                int_binop_expr(TrustIrBinOp::Add, eval_a(), eval_b()),
                int_binop_expr(TrustIrBinOp::Sub, eval_a(), eval_b()),
                int_binop_expr(TrustIrBinOp::Mul, eval_a(), eval_b()),
                int_binop_expr(TrustIrBinOp::SDiv, eval_a(), eval_b()),
                // Trust: witness-tier Rem arm — the fifth minor premise (Opaque `Int.mod`).
                int_binop_expr(TrustIrBinOp::SRem, eval_a(), eval_b()),
                // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — the sixth minor premise (Opaque
                // `Int.shiftRight`).
                int_binop_expr(TrustIrBinOp::LShr, eval_a(), eval_b()),
                // Trust: M6 rung 9, ANCHOR BitAnd — the seventh minor premise (Opaque
                // `Int.land`).
                int_binop_expr(TrustIrBinOp::And, eval_a(), eval_b()),
                Expr::bvar(2),
            ],
        );
        Expr::lam(
            bd(),
            binop_ty(),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), dispatch)),
        )
    };

    // UnaryOp case: λ(o:UnOp). λ(a:Operand). UnOp.rec (λ_.Int) (Int.sub 0 (eval a)) (bnot (eval a)) o
    //   under the two binders: a=bvar(0), o=bvar(1), rv=bvar(2), e=bvar(3).
    let un_case = {
        let e_ref = Expr::bvar(3);
        let eval_a = Expr::apps(eval_op.clone(), [e_ref, Expr::bvar(0)]);
        let unop_motive = Expr::lam(bd(), unop_ty(), int_ty());
        let neg_case = Expr::apps(
            cst("Int.sub"),
            [Expr::app(cst("Int.ofNat"), Expr::nat_lit(0)), eval_a.clone()],
        );
        let not_case = Expr::app(cst(TRUSTIR_BNOT), eval_a);
        let dispatch = Expr::apps(unop_rec, [unop_motive, neg_case, not_case, Expr::bvar(1)]);
        Expr::lam(bd(), unop_ty(), Expr::lam(bd(), operand_ty(), dispatch))
    };

    // Trust: M6 rung 9, COMPARE-AS-VALUE — Cmp case: λ(o:CmpOp). λ(a:Operand).
    //   λ(b:Operand). bool_as_int (CmpOp.rec (λ_.Bool) <lt> <le> <eq> <ne> <gt> <ge> o),
    //   dispatching over FLAT operands `evalOperand e a`/`evalOperand e b` (not nested
    //   Rvalue induction hypotheses — see `IrRvalue::Cmp`'s doc for why the flat shape
    //   suffices here). The per-op dispatch is BYTE-IDENTICAL to
    //   `register_eval_cond`'s own `CmpOp.rec` minor premises (and to the Rust-side
    //   `cmp_bool_expr` helper, which documents reproducing this EXACT closed form);
    //   the final `bool_as_int` wrap is the SAME `Bool.rec (λ_.Int) 0 1 …` idiom this
    //   module's own `bool_as_int` builds. SAME binder shape/depth as `bin_case`
    //   (three non-recursive fields): b=bvar(0), a=bvar(1), o=bvar(2), rv=bvar(3),
    //   e=bvar(4).
    let cmp_case = {
        let e_ref = || Expr::bvar(4);
        let eval_a = || Expr::apps(eval_op.clone(), [e_ref(), Expr::bvar(1)]);
        let eval_b = || Expr::apps(eval_op.clone(), [e_ref(), Expr::bvar(0)]);
        let decide_rel = |rel: &str, dec: &str, x: Expr, y: Expr| {
            Expr::apps(
                cst("decide"),
                [Expr::apps(cst(rel), [x.clone(), y.clone()]), Expr::apps(cst(dec), [x, y])],
            )
        };
        let lt_case = decide_rel("Int.lt", "Int.decLt", eval_a(), eval_b());
        let le_case = decide_rel("Int.le", "Int.decLe", eval_a(), eval_b());
        let eq_case = Expr::apps(cst("Int.beq"), [eval_a(), eval_b()]);
        let ne_case = Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [eval_a(), eval_b()]));
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED (matches `register_eval_cond`).
        let gt_case = decide_rel("Int.lt", "Int.decLt", eval_b(), eval_a());
        let ge_case = decide_rel("Int.le", "Int.decLe", eval_b(), eval_a());
        let cmpop_motive = Expr::lam(bd(), cmpop_ty(), cst("Bool"));
        let cmpop_rec = Expr::const_(Name::from_string(TRUSTIR_CMPOP_REC), lvl1());
        let dispatch = Expr::apps(
            cmpop_rec,
            [cmpop_motive, lt_case, le_case, eq_case, ne_case, gt_case, ge_case, Expr::bvar(2)],
        );
        let bool_int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), lvl1());
        let wrapped = Expr::apps(bool_rec, [bool_int_motive, int_lit(0), int_lit(1), dispatch]);
        Expr::lam(
            bd(),
            cmpop_ty(),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), wrapped)),
        )
    };

    // Rvalue.rec.{1} motive use_case bin_case un_case cmp_case rv
    let rec_app =
        Expr::apps(rvalue_rec, [motive, use_case, bin_case, un_case, cmp_case, Expr::bvar(0)]);
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), rvalue_ty(), rec_app));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalRvalue): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// STRAIGHT-LINE FRAGMENT — Stmt / set / evalBody (the operational step)
// ---------------------------------------------------------------------------

/// Register `Trust.TrustIr.Stmt` (idempotent), the single-constructor
/// `Assign : Nat → Rvalue → Stmt`. Requires `Rvalue` registered.
fn register_stmt_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STMT);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let assign_ctor = Constructor {
        name: Name::from_string(TRUSTIR_STMT_ASSIGN),
        type_: Expr::pi(bd(), nat_ty(), Expr::pi(bd(), rvalue_ty(), stmt_ty())),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![assign_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Stmt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.set : Env → Nat → Int → Env` (idempotent), the point-wise
/// env update via `Nat.beq` + `Bool.rec` (IDENTICAL construction to `Trust.MirSem.set`):
///
/// ```text
/// set (e : Env) (i : Nat) (v : Int) : Env :=
///   fun (j : Nat) => @Bool.rec (fun _ => Int) (e j) v (Nat.beq i j)
/// ```
///
/// For literal indices `Nat.beq i i` ι-reduces to `Bool.true`, so `set e i v i`
/// reduces to `v`; `Nat.beq i j → Bool.false` for `i ≠ j` leaves `e j`. All prelude
/// definitions ⇒ no non-foundational axiom.
fn register_set(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_SET);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), nat_ty(), Expr::pi(bd(), int_ty(), env_ty())));
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let bool_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    // λ(e).λ(i).λ(v).λ(j): j=bvar(0), v=bvar(1), i=bvar(2), e=bvar(3).
    let beq = Expr::apps(cst("Nat.beq"), [Expr::bvar(2), Expr::bvar(0)]);
    let e_at_j = Expr::app(Expr::bvar(3), Expr::bvar(0));
    let dispatch = Expr::apps(bool_rec, [bool_motive, e_at_j, Expr::bvar(1), beq]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), nat_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), nat_ty(), dispatch))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(set): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalBody : Env → List Stmt → Env` (idempotent) — the
/// operational step of a straight-line trace (left-fold the env through the
/// assignments). IDENTICAL construction to `Trust.MirSem.exec`:
///
/// ```text
/// evalBody (e : Env) : List Stmt → Env :=
///   @List.rec Stmt (fun _ => Env → Env)
///     (fun e' => e')
///     (fun s rest ih e' =>
///        ih (@Stmt.rec (fun _ => Env)
///              (fun (i : Nat) (R : Rvalue) => set e' i (evalRvalue e' R)) s))
///     stmts e
/// ```
///
/// `evalBody e [Assign k R] ι-reduces to `set e k (evalRvalue e R)`, and the fold
/// threads the env LEFT-TO-RIGHT so a later statement reads the earlier `set`s. All
/// `List.rec`/`Stmt.rec`/`set`/`evalRvalue` are definitions ⇒ no non-foundational axiom.
fn register_eval_body(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_BODY);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let list_stmt =
        Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), stmt_ty());
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), list_stmt.clone(), env_ty()));

    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let stmt_rec =
        Expr::const_(Name::from_string(TRUSTIR_STMT_REC), vec![Level::succ(Level::zero())]);
    let set = cst(TRUSTIR_SET);
    let eval_rvalue = cst(TRUSTIR_EVAL_RVALUE);

    let motive = Expr::lam(bd(), list_stmt.clone(), env_to_env.clone());
    // nil case: λ(e' : Env). e'
    let nil_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // cons case: λ(s).λ(rest).λ(ih).λ(e'). ih (step e' s)
    let cons_case = {
        let stmt_motive = Expr::lam(bd(), stmt_ty(), env_ty());
        // Assign minor (under i, R binders): R=bvar(0), i=bvar(1), e'=bvar(2),
        // ih=bvar(3), rest=bvar(4), s=bvar(5).
        let assign_minor = {
            let evald = Expr::apps(eval_rvalue.clone(), [Expr::bvar(2), Expr::bvar(0)]);
            let set_app = Expr::apps(set.clone(), [Expr::bvar(2), Expr::bvar(1), evald]);
            Expr::lam(bd(), nat_ty(), Expr::lam(bd(), rvalue_ty(), set_app))
        };
        // Under λ(e'): e'=bvar(0), ih=bvar(1), rest=bvar(2), s=bvar(3).
        let step = Expr::apps(stmt_rec.clone(), [stmt_motive, assign_minor, Expr::bvar(3)]);
        let body = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            stmt_ty(),
            Expr::lam(
                bd(),
                list_stmt.clone(),
                Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), body)),
            ),
        )
    };
    // @List.rec Stmt motive nil_case cons_case stmts e — under λ(e).λ(stmts):
    //   stmts=bvar(0), e=bvar(1).
    let rec_app = Expr::apps(list_rec, [stmt_ty(), motive, nil_case, cons_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(1));
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), list_stmt, applied));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalBody): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// CONTROL-FLOW FRAGMENT — CmpOp / Cond / evalCond (the branch discriminant)
// ---------------------------------------------------------------------------

fn cmpop_ty() -> Expr {
    cst(TRUSTIR_CMPOP)
}

fn cond_ty() -> Expr {
    cst(TRUSTIR_COND)
}

fn term_ty() -> Expr {
    cst(TRUSTIR_TERM)
}

fn block_ty() -> Expr {
    cst(TRUSTIR_BLOCK)
}

/// `List Trust.TrustIr.Block` — the Cfg type.
fn cfg_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), block_ty())
}

/// `List Trust.TrustIr.Stmt` — a basic block's statement trace.
fn list_stmt_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), stmt_ty())
}

/// Register `Trust.TrustIr.CmpOp` (idempotent), the six nullary comparison ops
/// `Lt|Le|Eq|Ne|Gt|Ge`. Axiom closure `⊆ {propext, Quot.sound, Classical.choice}`.
fn register_cmpop_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_CMPOP);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let nullary = |n: &str| Constructor { name: Name::from_string(n), type_: cmpop_ty() };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                nullary(TRUSTIR_CMPOP_LT),
                nullary(TRUSTIR_CMPOP_LE),
                nullary(TRUSTIR_CMPOP_EQ),
                nullary(TRUSTIR_CMPOP_NE),
                nullary(TRUSTIR_CMPOP_GT),
                nullary(TRUSTIR_CMPOP_GE),
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.CmpOp): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.Cond` (idempotent), the single-constructor branch
/// discriminant `Cmp : CmpOp → Operand → Operand → Cond`. Requires `CmpOp`/`Operand`.
fn register_cond_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_COND);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let cmp_ctor = Constructor {
        name: Name::from_string(TRUSTIR_COND_CMP),
        type_: Expr::pi(
            bd(),
            cmpop_ty(),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), cond_ty())),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![cmp_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Cond): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalCond : Env → Cond → Bool` (idempotent):
///
/// ```text
/// evalCond (e : Env) : Cond → Bool
///   | Cmp op a b => match op with
///       | Lt => decide (Int.lt (evalOperand e a) (evalOperand e b))   -- via Int.decLt
///       | Le => decide (Int.le (evalOperand e a) (evalOperand e b))   -- via Int.decLe
///       | Eq => Int.beq (evalOperand e a) (evalOperand e b)
///       | Ne => Bool.not (Int.beq (evalOperand e a) (evalOperand e b))
///       | Gt => decide (Int.lt (evalOperand e b) (evalOperand e a))   -- SWAPPED
///       | Ge => decide (Int.le (evalOperand e b) (evalOperand e a))   -- SWAPPED
/// ```
///
/// Each arm is BYTE-IDENTICAL to `clean_ground::ground_bool`'s grounding of the matching
/// comparison `Formula` (so a `Switch`'s grounded `ite` is def-eq to `evalCfg`'s switch
/// reduction). `decide`/`Int.decLt`/`Int.decLe`/`Int.beq`/`Bool.not` are prelude
/// DEFINITIONS / native reducers — no non-foundational axiom.
fn register_eval_cond(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_COND);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let lvl1 = || vec![Level::succ(Level::zero())];
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), cond_ty(), cst("Bool")));

    let cond_rec = Expr::const_(Name::from_string(TRUSTIR_COND_REC), lvl1());
    let cmpop_rec = Expr::const_(Name::from_string(TRUSTIR_CMPOP_REC), lvl1());
    let eval_op = cst(TRUSTIR_EVAL_OPERAND);

    let motive = Expr::lam(bd(), cond_ty(), cst("Bool"));

    // Cmp case: λ(op:CmpOp). λ(a:Operand). λ(b:Operand). CmpOp.rec.{1} (λ_.Bool) … op
    //   under the three case binders: b=bvar(0), a=bvar(1), op=bvar(2), cond=bvar(3),
    //   e=bvar(4). The six nullary CmpOp minors add no binders.
    let cmp_case = {
        let e_ref = || Expr::bvar(4);
        let eval_a = || Expr::apps(eval_op.clone(), [e_ref(), Expr::bvar(1)]);
        let eval_b = || Expr::apps(eval_op.clone(), [e_ref(), Expr::bvar(0)]);
        let decide_rel = |rel: &str, dec: &str, x: Expr, y: Expr| {
            Expr::apps(
                cst("decide"),
                [Expr::apps(cst(rel), [x.clone(), y.clone()]), Expr::apps(cst(dec), [x, y])],
            )
        };
        let lt_case = decide_rel("Int.lt", "Int.decLt", eval_a(), eval_b());
        let le_case = decide_rel("Int.le", "Int.decLe", eval_a(), eval_b());
        let eq_case = Expr::apps(cst("Int.beq"), [eval_a(), eval_b()]);
        let ne_case = Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [eval_a(), eval_b()]));
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED operands (as in ground_bool).
        let gt_case = decide_rel("Int.lt", "Int.decLt", eval_b(), eval_a());
        let ge_case = decide_rel("Int.le", "Int.decLe", eval_b(), eval_a());
        let cmpop_motive = Expr::lam(bd(), cmpop_ty(), cst("Bool"));
        let dispatch = Expr::apps(
            cmpop_rec,
            [cmpop_motive, lt_case, le_case, eq_case, ne_case, gt_case, ge_case, Expr::bvar(2)],
        );
        Expr::lam(
            bd(),
            cmpop_ty(),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), dispatch)),
        )
    };

    let rec_app = Expr::apps(cond_rec, [motive, cmp_case, Expr::bvar(0)]);
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), cond_ty(), rec_app));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalCond): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// CONTROL-FLOW FRAGMENT — Term / Block / blockStmts / blockTerm / blockAt
// ---------------------------------------------------------------------------

/// Register `Trust.TrustIr.Term` (idempotent), the terminator inductive
/// `Goto : Nat → Term | Switch : Cond → Nat → Nat → Term | Return : Operand → Term`.
/// Requires `Cond`/`Operand`. Non-recursive ⇒ axiom closure `⊆` the 3 foundational.
fn register_term_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_TERM);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let goto_ctor = Constructor {
        name: Name::from_string(TRUSTIR_TERM_GOTO),
        type_: Expr::pi(bd(), nat_ty(), term_ty()),
    };
    let switch_ctor = Constructor {
        name: Name::from_string(TRUSTIR_TERM_SWITCH),
        type_: Expr::pi(
            bd(),
            cond_ty(),
            Expr::pi(bd(), nat_ty(), Expr::pi(bd(), nat_ty(), term_ty())),
        ),
    };
    let return_ctor = Constructor {
        name: Name::from_string(TRUSTIR_TERM_RETURN),
        type_: Expr::pi(bd(), operand_ty(), term_ty()),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![goto_ctor, switch_ctor, return_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Term): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.Block` (idempotent), `Blk : List Stmt → Term → Block`.
/// Requires `Stmt`/`Term`. Non-recursive ⇒ axiom closure `⊆` the 3 foundational.
fn register_block_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_BLOCK);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let blk_ctor = Constructor {
        name: Name::from_string(TRUSTIR_BLOCK_MK),
        type_: Expr::pi(bd(), list_stmt_ty(), Expr::pi(bd(), term_ty(), block_ty())),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![blk_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Block): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.blockStmts : Block → List Stmt` (idempotent) — the first
/// projection via `Block.rec` (`Blk stmts term → stmts`).
fn register_block_stmts(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_BLOCK_STMTS);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), block_ty(), list_stmt_ty());
    let block_rec =
        Expr::const_(Name::from_string(TRUSTIR_BLOCK_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), block_ty(), list_stmt_ty());
    // Blk minor: λ(stmts:List Stmt). λ(term:Term). stmts — term=bvar(0), stmts=bvar(1).
    let blk_minor = Expr::lam(bd(), list_stmt_ty(), Expr::lam(bd(), term_ty(), Expr::bvar(1)));
    // λ(b:Block). Block.rec motive blk_minor b — b=bvar(0).
    let rec_app = Expr::apps(block_rec, [motive, blk_minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), block_ty(), rec_app);
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(blockStmts): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.blockTerm : Block → Term` (idempotent) — the second
/// projection via `Block.rec` (`Blk stmts term → term`).
fn register_block_term(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_BLOCK_TERM);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), block_ty(), term_ty());
    let block_rec =
        Expr::const_(Name::from_string(TRUSTIR_BLOCK_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), block_ty(), term_ty());
    // Blk minor: λ(stmts).λ(term). term — term=bvar(0).
    let blk_minor = Expr::lam(bd(), list_stmt_ty(), Expr::lam(bd(), term_ty(), Expr::bvar(0)));
    let rec_app = Expr::apps(block_rec, [motive, blk_minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), block_ty(), rec_app);
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(blockTerm): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.blockAt : List Block → Nat → Block` (idempotent), the TOTAL
/// block lookup. IDENTICAL fold convention to a `List.rec`-indexed nth, with the
/// out-of-range / nil case falling back to the canonical empty block
/// `Blk List.nil (Return (Const 0))`:
///
/// ```text
/// blockAt : List Block → Nat → Block :=
///   @List.rec Block (fun _ => Nat → Block)
///     (fun _idx => emptyBlk)                                    -- nil ⇒ fallback
///     (fun hd tl ih idx =>
///        Nat.rec (fun _ => Block) hd (fun n _ => ih n) idx)     -- idx=0 ⇒ hd, succ n ⇒ ih n
///     blocks idx
/// ```
///
/// `emptyBlk = Blk List.nil (Return (Const 0))` is total (every CFG lookup yields a
/// block). All `List.rec`/`Nat.rec` are prelude definitions ⇒ no non-foundational axiom.
fn register_block_at(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_BLOCK_AT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let nat_to_block = Expr::pi(bd(), nat_ty(), block_ty());
    let ty = Expr::pi(bd(), cfg_ty(), Expr::pi(bd(), nat_ty(), block_ty()));

    // emptyBlk = Blk List.nil (Return (Const 0))
    let empty_blk = {
        let nil_stmt =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), stmt_ty());
        let ret0 =
            Expr::app(cst(TRUSTIR_TERM_RETURN), Expr::app(cst(TRUSTIR_OPERAND_CONST), int_lit(0)));
        Expr::apps(cst(TRUSTIR_BLOCK_MK), [nil_stmt, ret0])
    };

    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);

    let motive = Expr::lam(bd(), cfg_ty(), nat_to_block.clone());
    // nil case: λ(idx:Nat). emptyBlk — idx=bvar(0); emptyBlk is closed.
    let nil_case = Expr::lam(bd(), nat_ty(), empty_blk);
    // cons case: λ(hd:Block).λ(tl:List Block).λ(ih:Nat→Block).λ(idx:Nat).
    //   Nat.rec (λ_.Block) hd (λ(n:Nat)(_:Block). ih n) idx
    //   de-Bruijn under λ(idx): idx=bvar(0), ih=bvar(1), tl=bvar(2), hd=bvar(3).
    let cons_case = {
        let nat_motive = Expr::lam(bd(), nat_ty(), block_ty());
        // zero case: hd = bvar(3).
        let zero_case = Expr::bvar(3);
        // succ case: λ(n:Nat).λ(_:Block). ih n — under these two binders n=bvar(1),
        // and ih (lifted past n + the Block IH) = bvar(1+2)=bvar(3).
        let succ_case = Expr::lam(
            bd(),
            nat_ty(),
            Expr::lam(bd(), block_ty(), Expr::app(Expr::bvar(3), Expr::bvar(1))),
        );
        let nat_dispatch = Expr::apps(nat_rec, [nat_motive, zero_case, succ_case, Expr::bvar(0)]);
        Expr::lam(
            bd(),
            block_ty(),
            Expr::lam(
                bd(),
                cfg_ty(),
                Expr::lam(bd(), nat_to_block.clone(), Expr::lam(bd(), nat_ty(), nat_dispatch)),
            ),
        )
    };
    // @List.rec Block motive nil_case cons_case blocks idx — under λ(blocks).λ(idx):
    //   idx=bvar(0), blocks=bvar(1).
    let rec_app = Expr::apps(list_rec, [block_ty(), motive, nil_case, cons_case, Expr::bvar(1)]);
    let applied = Expr::app(rec_app, Expr::bvar(0));
    let val = Expr::lam(bd(), cfg_ty(), Expr::lam(bd(), nat_ty(), applied));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(blockAt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalCfg : Env → Cfg → Nat → Nat → Int` (idempotent) — the
/// CFG executor, the Clean analogue of trust-ir's stepBlock-across-blocks (`stepN`).
/// Defined by `Nat.rec` on FUEL (the bound for the acyclic/branching fragment; loops are
/// the NEXT step):
///
/// ```text
/// evalCfg (e0 : Env) (cfg : Cfg) (fuel : Nat) (bb0 : Nat) : Int :=
///   Nat.rec (fun _ => Env → Nat → Int)
///     (fun _e _bb => Int.ofNat 0)                          -- fuel = 0 ⇒ out of fuel
///     (fun _n ih e bb =>
///        let blk := blockAt cfg bb;
///        let e'  := evalBody e (blockStmts blk);            -- run this block's stmts
///        Term.rec (fun _ => Int)
///          (fun tgt => ih e' tgt)                           -- Goto tgt
///          (fun cond t f => Bool.rec (fun _ => Int) (ih e' f) (ih e' t) (evalCond e' cond))  -- Switch
///          (fun op => evalOperand e' op)                    -- Return op
///          (blockTerm blk))
///     fuel e0 bb0
/// ```
///
/// The motive `Env → Nat → Int` threads the POST-STMT env `e'` into successors (a `Goto`
/// chain with stmts sees the predecessor's updates), and the `Switch` arm reduces to
/// EXACTLY the `Bool.rec (λ_.Int) (else) (then) (evalCond e' cond)` term the live
/// `clean_ground::ground_int` emits for `Formula::Ite` — so the branch refinement is
/// grounder-connected. With a LITERAL fuel the `Nat.rec` fully ι-reduces. All
/// `Nat.rec`/`Term.rec`/`Bool.rec`/`blockAt`/`blockStmts`/`blockTerm`/`evalBody`/
/// `evalOperand`/`evalCond` are definitions ⇒ no non-foundational axiom.
fn register_eval_cfg(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_CFG);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let lvl1 = || vec![Level::succ(Level::zero())];

    // evalCfg : Env → Cfg → Nat → Nat → Int
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cfg_ty(), Expr::pi(bd(), nat_ty(), Expr::pi(bd(), nat_ty(), int_ty()))),
    );

    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), lvl1());
    let term_rec = Expr::const_(Name::from_string(TRUSTIR_TERM_REC), lvl1());
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), lvl1());

    // motive for the fuel-recursion: λ(_:Nat). Env → Nat → Int.
    let env_nat_int = Expr::pi(bd(), env_ty(), Expr::pi(bd(), nat_ty(), int_ty()));
    let fuel_motive = Expr::lam(bd(), nat_ty(), env_nat_int.clone());

    // zero case: λ(e:Env). λ(bb:Nat). Int.ofNat 0.
    let zero_case = Expr::lam(bd(), env_ty(), Expr::lam(bd(), nat_ty(), int_lit(0)));

    // succ case: λ(_n:Nat). λ(ih:Env→Nat→Int). λ(e:Env). λ(bb:Nat). <dispatch>.
    // de-Bruijn under the four binders: bb=bvar(0), e=bvar(1), ih=bvar(2), _n=bvar(3).
    // We reference `cfg` from the OUTER context — see the outer-binder accounting below.
    let succ_case = {
        // Inside `λ(e0).λ(cfg).λ(fuel).λ(bb0). Nat.rec … fuel e0 bb0`, the Nat.rec minor
        // premises are SEPARATE lambdas; `cfg` is NOT in scope inside them via the same
        // depth. So we build evalCfg as: λe0.λcfg.λfuel.λbb0. (Nat.rec motive zero succ fuel) e0 bb0
        // and inside `succ` the only outer free var we need is `cfg`. To keep `cfg` reachable
        // we instead close `succ`/`zero` over NOTHING outer and pass `cfg` via the body
        // referencing the outer binder by its de-Bruijn depth measured FROM the minor's body.
        //
        // The minor body sits under: [bb, e, ih, _n] (4 binders) then OUTSIDE the Nat.rec
        // application it is under [bb0, fuel, cfg, e0] (4 binders). The Nat.rec const and its
        // motive/minors are arguments at the [bb0,fuel,cfg,e0] level, so a minor's body sees
        // its own 4 binders innermost, then bb0(4), fuel(5), cfg(6), e0(7).
        let bb_ref = || Expr::bvar(0);
        let cfg_ref = || Expr::bvar(6);

        // blk := blockAt cfg bb (at the `succ_case` body depth: bb=bvar(0), cfg=bvar(6)).
        // The Term.rec scrutinee `(blockTerm blk)` lives at THIS depth; each minor below
        // re-derives its own `e'`/`blk` at its (deeper) binder depth, so we only need
        // `term` (the scrutinee) here.
        let blk = Expr::apps(cst(TRUSTIR_BLOCK_AT), [cfg_ref(), bb_ref()]);
        // blockTerm blk — the terminator we case-split on.
        let term = Expr::app(cst(TRUSTIR_BLOCK_TERM), blk.clone());

        let term_motive = Expr::lam(bd(), term_ty(), int_ty());

        // Goto minor: λ(tgt:Nat). ih e' tgt — under this binder tgt=bvar(0), and
        //   bb=bvar(1), e=bvar(2), ih=bvar(3); cfg shifts to bvar(7).
        let goto_minor = {
            let ih = Expr::bvar(3);
            let e_p = Expr::apps(
                cst(TRUSTIR_EVAL_BODY),
                [
                    Expr::bvar(2),
                    Expr::app(
                        cst(TRUSTIR_BLOCK_STMTS),
                        Expr::apps(cst(TRUSTIR_BLOCK_AT), [Expr::bvar(7), Expr::bvar(1)]),
                    ),
                ],
            );
            Expr::lam(bd(), nat_ty(), Expr::apps(ih, [e_p, Expr::bvar(0)]))
        };

        // Switch minor: λ(cond:Cond).λ(t:Nat).λ(f:Nat).
        //   Bool.rec (λ_.Int) (ih e' f) (ih e' t) (evalCond e' cond)
        //   under the three binders: f=bvar(0), t=bvar(1), cond=bvar(2), then
        //   bb=bvar(3), e=bvar(4), ih=bvar(5); cfg shifts to bvar(9).
        let switch_minor = {
            let ih = || Expr::bvar(5);
            let e_p = || {
                Expr::apps(
                    cst(TRUSTIR_EVAL_BODY),
                    [
                        Expr::bvar(4),
                        Expr::app(
                            cst(TRUSTIR_BLOCK_STMTS),
                            Expr::apps(cst(TRUSTIR_BLOCK_AT), [Expr::bvar(9), Expr::bvar(3)]),
                        ),
                    ],
                )
            };
            let cond_b = Expr::apps(cst(TRUSTIR_EVAL_COND), [e_p(), Expr::bvar(2)]);
            let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
            // Bool.rec minor order is (false, true): FALSE ↦ else (f), TRUE ↦ then (t).
            let else_v = Expr::apps(ih(), [e_p(), Expr::bvar(0)]);
            let then_v = Expr::apps(ih(), [e_p(), Expr::bvar(1)]);
            let body = Expr::apps(bool_rec.clone(), [int_motive, else_v, then_v, cond_b]);
            Expr::lam(bd(), cond_ty(), Expr::lam(bd(), nat_ty(), Expr::lam(bd(), nat_ty(), body)))
        };

        // Return minor: λ(op:Operand). evalOperand e' op — under this binder op=bvar(0),
        //   bb=bvar(1), e=bvar(2), ih=bvar(3); cfg shifts to bvar(7).
        let return_minor = {
            let e_p = Expr::apps(
                cst(TRUSTIR_EVAL_BODY),
                [
                    Expr::bvar(2),
                    Expr::app(
                        cst(TRUSTIR_BLOCK_STMTS),
                        Expr::apps(cst(TRUSTIR_BLOCK_AT), [Expr::bvar(7), Expr::bvar(1)]),
                    ),
                ],
            );
            Expr::lam(
                bd(),
                operand_ty(),
                Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [e_p, Expr::bvar(0)]),
            )
        };

        // Term.rec.{1} term_motive goto switch return (blockTerm blk)
        let dispatch =
            Expr::apps(term_rec, [term_motive, goto_minor, switch_minor, return_minor, term]);
        Expr::lam(
            bd(),
            nat_ty(),
            Expr::lam(
                bd(),
                env_nat_int.clone(),
                Expr::lam(bd(), env_ty(), Expr::lam(bd(), nat_ty(), dispatch)),
            ),
        )
    };

    // Nat.rec.{1} fuel_motive zero_case succ_case fuel — under λ(e0).λ(cfg).λ(fuel).λ(bb0):
    //   bb0=bvar(0), fuel=bvar(1), cfg=bvar(2), e0=bvar(3).
    let nat_dispatch = Expr::apps(nat_rec, [fuel_motive, zero_case, succ_case, Expr::bvar(1)]);
    // (Nat.rec … fuel) e0 bb0
    let applied = Expr::apps(nat_dispatch, [Expr::bvar(3), Expr::bvar(0)]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cfg_ty(), Expr::lam(bd(), nat_ty(), Expr::lam(bd(), nat_ty(), applied))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalCfg): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// LOOP FRAGMENT — stepLoop / execLoop (the back-edge fixpoint) + stepPreservesInv /
// loopInvariantRule (the Hoare while-rule). MIRRORS the committed `Trust.MirSem` loop
// meta-theory (`register_step_loop` / `register_exec_loop` / `register_step_preserves_inv`
// / `loop_invariant_rule_{type,proof}`) — `evalCond` ↦ `eval_cond`, `evalBody` ↦ `exec`,
// the de-Bruijn accounting is byte-identical to mirsem.rs.
// ---------------------------------------------------------------------------

/// `stepLoop`'s body = `@Bool.rec (λ_.Env) e (evalBody e body) (evalCond e cond)` at the
/// supplied refs' depth. The trust-ir analogue of `mirsem::step_loop_body`.
fn step_loop_body_ir(e_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [e_ref.clone(), cond_ref.clone()]);
    let exec_body = Expr::apps(cst(TRUSTIR_EVAL_BODY), [e_ref.clone(), body_ref.clone()]);
    // Bool.rec.{1} (λ_.Env) (false ↦ e) (true ↦ evalBody e body) (evalCond e cond)
    Expr::apps(bool_rec, [env_motive, e_ref.clone(), exec_body, guard])
}

/// `stepLoop e cond body` applied as a CONSTANT (signature `Env → Cond → List Stmt → Env`).
fn step_loop_app_ir(e_ref: Expr, cond_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_STEP_LOOP), [e_ref, cond_ref, body_ref])
}

/// `execLoop e cond body fuel` applied as a CONSTANT.
fn exec_loop_app_ir(e_ref: Expr, cond_ref: Expr, body_ref: Expr, fuel_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_EXEC_LOOP), [e_ref, cond_ref, body_ref, fuel_ref])
}

/// The `Env → Prop` predicate type — the loop-invariant signature `I : Env → Prop`
/// (the trust-ir analogue of `mirsem::env_pred_ty`).
fn env_pred_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), env_ty(), Expr::prop())
}

/// `eval_cond-style` `Eq Bool b Bool.true` proposition (the guard-true equality).
pub(crate) fn eq_bool_true(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), b, cst("Bool.true")],
    )
}

// Trust: ADT-return leaf, 3-outcome guard chain — the mirror-image `Eq Bool b
// Bool.false` proposition (the guard-FALSE hypothesis a chained guard's
// "continue to the next test" edge needs; `mirsem.rs` has its own private
// `eq_bool_false` for the loop-refinement theory, this is the SAME shape widened
// to `pub(crate)` so the sibling `trustir_adt` module can build it without
// duplicating `mirsem.rs`'s private copy or depending on that module).
pub(crate) fn eq_bool_false(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), b, cst("Bool.false")],
    )
}

/// The PRESERVATION hypothesis `∀ (e : Env), I e → evalCond e cond = true → I (evalBody e
/// body)`. The supplied refs denote `I`/`cond`/`body` at the OUTER depth (before `∀ e`);
/// the inner arrows re-lift internally. BYTE-IDENTICAL accounting to
/// `mirsem::preservation_hyp_type` (with `eval_cond` ↦ `evalCond`, `exec` ↦ `evalBody`).
fn preservation_hyp_type_ir(i_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // 1st arrow domain: I e   (e=0; refs +1)
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    // 2nd arrow domain: evalCond e cond = true   (e=1; refs +2)
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), lift(cond_ref, 2)]);
    let dom2 = eq_bool_true(guard);
    // codomain: I (evalBody e body)   (e=2; refs +3)
    let exec_body = Expr::apps(cst(TRUSTIR_EVAL_BODY), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body);
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.TrustIr.stepLoop : Env → Cond → List Stmt → Env` (idempotent) =
/// `λ e cond body. if evalCond e cond then evalBody e body else e`. See
/// [`TRUSTIR_STEP_LOOP`]. Requires `evalCond`/`evalBody`. No non-foundational axiom.
fn register_step_loop_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_LOOP);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e:Env).λ(cond:Cond).λ(body:List Stmt). step  ; depth: body=0, cond=1, e=2.
    let body = step_loop_body_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cond_ty(), Expr::lam(bd(), list_stmt.clone(), body)),
    );
    let ty =
        Expr::pi(bd(), env_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt, env_ty())));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.stepLoop): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.execLoop : Env → Cond → List Stmt → Nat → Env` (idempotent),
/// front-peeling the fuel via `Nat.rec` at an `Env → Env` motive:
///
/// ```text
/// execLoop (e : Env) (cond : Cond) (body : List Stmt) : Nat → Env :=
///   fun fuel =>
///     (@Nat.rec (fun _ => Env → Env)
///        (fun e' => e')                                     -- 0    : id transformer
///        (fun (n : Nat) (ih : Env → Env) (e' : Env) =>      -- succ : ih (stepLoop e')
///           ih (stepLoop e' cond body))
///        fuel) e
/// ```
///
/// `execLoop e cond body (succ n)` ι-reduces to `execLoop (stepLoop e cond body) cond
/// body n` (front-peel). The trust-ir analogue of `Trust.MirSem.exec_loop`. Requires
/// `stepLoop`. No non-foundational axiom.
fn register_exec_loop_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EXEC_LOOP);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ case : λ(n).λ(ih).λ(e'). ih (stepLoop e' cond body)
    //   Under `λ(e).λ(cond).λ(body).λ(fuel)` then inside λ(n)λ(ih)λ(e'):
    //   e' = bvar(0), ih = bvar(1), n = bvar(2), fuel = bvar(3), body = bvar(4),
    //   cond = bvar(5), e = bvar(6).
    let succ_case = {
        let step = step_loop_app_ir(Expr::bvar(0), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    // @Nat.rec.{1} motive zero_case succ_case fuel   (fuel = bvar(0) under the 4 binders)
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    // execLoop e cond body fuel = (Nat.rec … fuel) e    (e = bvar 3)
    let applied = Expr::app(rec_app, Expr::bvar(3));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt, Expr::pi(bd(), cst("Nat"), env_ty()))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.execLoop): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.stepPreservesInv` (idempotent) — the guarded-step
/// invariant-preservation lemma. The proof generalises the guard `evalCond e cond : Bool`
/// to a fresh `b`, case-splits (dependent `Bool.rec`), and instantiates at the real guard
/// with `Eq.refl`. BYTE-IDENTICAL structure to `mirsem::register_step_preserves_inv`.
fn register_step_preserves_inv_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_PRESERVES_INV);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();

    // ---- TYPE ----
    // ∀ (I : Env→Prop)(cond)(body), preservation → ∀ e, I e → I (stepLoop e cond body)
    let ty = {
        // inside `∀ I ∀ cond ∀ body`: body=0, cond=1, I=2.
        let pres = preservation_hyp_type_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
        // inside `∀ I ∀ cond ∀ body (pres→) ∀ e`: e=0, pres=1, body=2, cond=3, I=4.
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        // I (stepLoop e cond body): under `∀ e` + 1 arrow ⇒ e=1, pres=2, body=3, cond=4, I=5.
        let step = step_loop_app_ir(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(5), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt.clone(), after_pres)),
        )
    };

    // ---- PROOF ----
    // λ I cond body pres e hI. ghelper (eval guard) (Eq.refl Bool guard)
    // depth inside `λ I λ cond λ body λ pres λ e λ hI`: hI=0, e=1, pres=2, body=3, cond=4, I=5.
    let val = {
        let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);

        // motive_g : Bool → Prop
        //   = λ (b : Bool). (evalCond e cond = b) → I (Bool.rec (λ_.Env) e (evalBody e body) b)
        //   inside the extra `λ b`: b=0, hI=1, e=2, pres=3, body=4, cond=5, I=6.
        let motive_g = {
            let guard_b = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(2), Expr::bvar(5)]);
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            // codomain `I (Bool.rec (λ_.Env) e (evalBody e body) b)`; under `λ b` + `eq_dom →`:
            //   b=1, hI=2, e=3, pres=4, body=5, cond=6, I=7.
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(TRUSTIR_EVAL_BODY), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(7), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };

        // false_case : (evalCond e cond = false) → I (Bool.rec … e (evalBody e body) false)
        //   Bool.rec … false ι-reduces to e, codomain `I e`; proof = λ _. hI.
        let false_case = {
            let guard_f = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            // body: under `λ (_:eq_false)` ⇒ hI=1.
            Expr::lam(bd(), eq_false, Expr::bvar(1))
        };

        // true_case : (evalCond e cond = true) → I (Bool.rec … e (evalBody e body) true)
        //   Bool.rec … true ι-reduces to evalBody e body, codomain `I (evalBody e body)`;
        //   proof = λ (hg : eq). pres e hI hg.
        let true_case = {
            let guard_t = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_true = eq_bool_true(guard_t);
            // body: under `λ (hg:eq_true)` ⇒ hg=0, hI=1, e=2, pres=3.
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };

        // ghelper = @Bool.rec.{0} motive_g false_case true_case (evalCond e cond)
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);

        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(
                    bd(),
                    list_stmt.clone(),
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                        Expr::lam(
                            bd(),
                            env_ty(),
                            // hI : I e  (inside `λ I λ cond λ body λ pres λ e`: e=0, I=4)
                            Expr::lam(bd(), Expr::app(Expr::bvar(4), Expr::bvar(0)), applied),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.stepPreservesInv check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.stepPreservesInv): {e:?}"))?;
    Ok(())
}

/// The LOOP INVARIANT RULE (Hoare while-rule, PARTIAL correctness) TYPE:
/// `∀ (I : Env→Prop)(cond)(body), preservation → ∀ (n : Nat)(e : Env), I e →
///   I (execLoop e cond body n)`. `claimed_concl_pred = Some(p)` overrides the
/// conclusion's invariant predicate (fail-closed hook). The trust-ir analogue of
/// `mirsem::loop_invariant_rule_type`.
fn loop_invariant_rule_type_ir(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // inside `∀ I ∀ cond ∀ body`: body=0, cond=1, I=2.
    let pres = preservation_hyp_type_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ n e, I e → I (execLoop e cond body n)
    //   inside `∀ I ∀ cond ∀ body (pres→) ∀ n ∀ e`: e=0, n=1, pres=2, body=3, cond=4, I=5.
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(5));
        Expr::app(pred, Expr::bvar(0))
    };
    // I (execLoop e cond body n): under one more arrow ⇒ e=1, n=2, pres=3, body=4, cond=5, I=6.
    let looped = exec_loop_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(bd(), env_pred_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt, after_pres)))
}

/// The LOOP INVARIANT RULE PROOF, by genuine `Nat.rec` induction on the iteration count
/// `n` at the Prop motive `λ n. ∀ e, I e → I (execLoop e cond body n)`: BASE (`n=0`):
/// `execLoop e 0 ≡ e` ⇒ `λ e hI. hI`. STEP (`n=succ m`): front-peel
/// `execLoop e (succ m) ≡ execLoop (stepLoop e) m`, so `λ m ih e hI.
///   ih (stepLoop e) (stepPreservesInv I cond body pres e hI)` — the IH at the STEPPED
/// env, fed guarded-step preservation. The trust-ir analogue of
/// `mirsem::loop_invariant_rule_proof`.
fn loop_invariant_rule_proof_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();

    // motive : Nat → Prop = λ n. ∀ e, I e → I (execLoop e cond body n)
    //   inside `… λ pres` then `λ n` then `∀ e`: e=0, n=1, pres=2, body=3, cond=4, I=5.
    let motive = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        let looped = exec_loop_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let i_loop = Expr::app(Expr::bvar(6), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };

    // zero_case : ∀ e, I e → I (execLoop e cond body 0) ≡ I e ⇒ λ e hI. hI.
    //   inside `… λ pres λ e λ hI`: hI=0, e=1, I=5 (under `λ pres λ e`: e=0, I=4).
    let zero_case = {
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };

    // succ_case : λ (m)(ih : motive m)(e)(hI : I e).
    //   ih (stepLoop e cond body) (stepPreservesInv I cond body pres e hI)
    let succ_case = {
        // ih : motive m  (after `λ m`, before `λ ih`): inside `… λ pres λ m`: m=0, I=4. Then ∀ e.
        let ih_ty = {
            // under `∀ e`: e=0, m=1, pres=2, body=3, cond=4, I=5.
            let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
            let looped =
                exec_loop_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
            let i_loop = Expr::app(Expr::bvar(6), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        // body: inside `λ m λ ih λ e λ hI`: hI=0, e=1, ih=2, m=3, pres=4, body=5, cond=6, I=7.
        let step = step_loop_app_ir(Expr::bvar(1), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(TRUSTIR_STEP_PRESERVES_INV),
            [
                Expr::bvar(7), // I
                Expr::bvar(6), // cond
                Expr::bvar(5), // body
                Expr::bvar(4), // pres
                Expr::bvar(1), // e
                Expr::bvar(0), // hI
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        // hI : I e  (inside `λ m λ ih λ e`: e=0, I=6)
        let i_e_hi = Expr::app(Expr::bvar(6), Expr::bvar(0));
        Expr::lam(
            bd(),
            cst("Nat"), // m
            Expr::lam(
                bd(),
                ih_ty, // ih
                Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_hi, ih_app)),
            ),
        )
    };

    // λ I λ cond λ body λ pres λ n. @Nat.rec.{0} motive zero_case succ_case n
    //   (the case terms were indexed for depth UNDER `λ pres` (no `λ n`), so lift each +1).
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(
                bd(),
                list_stmt,
                Expr::lam(
                    bd(),
                    preservation_hyp_type_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

/// Register `Trust.TrustIr.loopInvariantRule` (idempotent) — the Hoare while-rule
/// (PARTIAL correctness), kernel-checked at registration. Requires
/// `stepLoop`/`execLoop`/`stepPreservesInv`. No non-foundational axiom.
fn register_loop_invariant_rule_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_LOOP_INVARIANT_RULE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_invariant_rule_type_ir(None);
    let val = loop_invariant_rule_proof_ir();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.loopInvariantRule check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.loopInvariantRule): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// BREAK / EARLY-EXIT loop fragment — andLeftTrue + stepLoopBrk / execLoopBrk /
// stepPreservesInvBrk / loopInvariantRuleBrk. MIRRORS the committed MirSem break-loop
// meta-theory byte-for-byte (`combined_brk_guard` scrutinee; `evalCond` ↦ MIRSEM_EVAL_COND,
// `evalBody` ↦ MIRSEM_EXEC). The base loop fragment is reused unchanged.
// ---------------------------------------------------------------------------

/// The TYPE of `andLeftTrue`: `∀ (a b : Bool), Eq Bool (Bool.and a b) Bool.true → Eq Bool a
/// Bool.true`. IDENTICAL to `mirsem::and_left_true_type`.
fn and_left_true_type_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let eq_bool = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), x, y],
        )
    };
    // ∀ (a : Bool)(b : Bool), (Bool.and a b = true) → (a = true) ; inside `∀ a ∀ b`: b=0, a=1.
    let band = Expr::apps(cst("Bool.and"), [Expr::bvar(1), Expr::bvar(0)]);
    let dom = eq_bool(band, cst("Bool.true"));
    let cod = eq_bool(Expr::bvar(2), cst("Bool.true")); // under the arrow: a=2.
    let arrow = Expr::pi(bd(), dom, cod);
    Expr::pi(bd(), cst("Bool"), Expr::pi(bd(), cst("Bool"), arrow))
}

/// The PROOF of `andLeftTrue` by `Bool.rec` on `a`. IDENTICAL to `mirsem::and_left_true_proof`.
fn and_left_true_proof_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let eq_bool = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), x, y],
        )
    };
    // Under `λ a λ b`: b=0, a=1. motive : λ a'. (Bool.and a' b = true) → (a' = true).
    let motive = {
        let band = Expr::apps(cst("Bool.and"), [Expr::bvar(0), Expr::bvar(1)]);
        let dom = eq_bool(band, cst("Bool.true"));
        let cod = eq_bool(Expr::bvar(1), cst("Bool.true")); // under the `dom →` arrow: a'=1.
        Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), dom, cod))
    };
    // false_minor : Bool.and false b ≡ false ⇒ dom ≡ cod ⇒ λ h. h.  (b = bvar(0))
    let false_minor = {
        let band_f = Expr::apps(cst("Bool.and"), [cst("Bool.false"), Expr::bvar(0)]);
        let dom = eq_bool(band_f, cst("Bool.true"));
        Expr::lam(bd(), dom, Expr::bvar(0))
    };
    // true_minor : cod ≡ (true = true) ⇒ λ _. Eq.refl Bool Bool.true.  (b = bvar(0))
    let true_minor = {
        let band_t = Expr::apps(cst("Bool.and"), [cst("Bool.true"), Expr::bvar(0)]);
        let dom = eq_bool(band_t, cst("Bool.true"));
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), cst("Bool.true")],
        );
        Expr::lam(bd(), dom, refl)
    };
    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(bool_rec0, [motive, false_minor, true_minor, Expr::bvar(1)]);
    Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), cst("Bool"), rec_app))
}

/// Register `Trust.TrustIr.andLeftTrue` (idempotent) — the `Bool.and` left-projection.
fn register_and_left_true_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_AND_LEFT_TRUE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = and_left_true_type_ir();
    let proof = and_left_true_proof_ir();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty).map_err(|e| format!("TrustIr.andLeftTrue check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl(TrustIr.andLeftTrue): {e:?}"))?;
    Ok(())
}

/// `andLeftTrue a b h : Eq Bool a Bool.true`.
fn and_left_true_app_ir(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_AND_LEFT_TRUE), [a, b, h])
}

/// The COMBINED break-guard `Bool` term `Bool.and (evalCond e cond) (Bool.not (evalCond e
/// brk))` at the supplied refs' depth. IDENTICAL to `mirsem::combined_brk_guard`.
fn combined_brk_guard_ir(e_ref: &Expr, cond_ref: &Expr, brk_ref: &Expr) -> Expr {
    let g_cond = Expr::apps(cst(TRUSTIR_EVAL_COND), [e_ref.clone(), cond_ref.clone()]);
    let g_brk = Expr::apps(cst(TRUSTIR_EVAL_COND), [e_ref.clone(), brk_ref.clone()]);
    let not_brk = Expr::app(cst("Bool.not"), g_brk);
    Expr::apps(cst("Bool.and"), [g_cond, not_brk])
}

/// `stepLoopBrk`'s body = `Bool.rec (λ_.Env) e (evalBody e body) <combined_brk_guard>`.
fn step_loop_brk_body_ir(e_ref: &Expr, cond_ref: &Expr, brk_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
    let guard = combined_brk_guard_ir(e_ref, cond_ref, brk_ref);
    let exec_body = Expr::apps(cst(TRUSTIR_EVAL_BODY), [e_ref.clone(), body_ref.clone()]);
    Expr::apps(bool_rec, [env_motive, e_ref.clone(), exec_body, guard])
}

/// `stepLoopBrk e cond brk body` applied as a CONSTANT.
fn step_loop_brk_app_ir(e_ref: Expr, cond_ref: Expr, brk_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_STEP_LOOP_BRK), [e_ref, cond_ref, brk_ref, body_ref])
}

/// `execLoopBrk e cond brk body fuel` applied as a CONSTANT.
fn exec_loop_brk_app_ir(e: Expr, cond: Expr, brk: Expr, body: Expr, fuel: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_EXEC_LOOP_BRK), [e, cond, brk, body, fuel])
}

/// The break PRESERVATION hypothesis `∀ e, I e → (evalCond e cond ∧ ¬evalCond e brk) = true →
/// I (evalBody e body)`. The `preservation_hyp_type_ir` analogue with the combined guard.
/// IDENTICAL accounting to `mirsem::preservation_hyp_type_brk`.
fn preservation_hyp_type_brk_ir(
    i_ref: &Expr,
    cond_ref: &Expr,
    brk_ref: &Expr,
    body_ref: &Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0)); // I e   (e=0; refs +1)
    let guard = combined_brk_guard_ir(&Expr::bvar(1), &lift(cond_ref, 2), &lift(brk_ref, 2));
    let dom2 = eq_bool_true(guard); // combined guard = true   (e=1; refs +2)
    let exec_body = Expr::apps(cst(TRUSTIR_EVAL_BODY), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body); // I (evalBody e body)   (e=2; refs +3)
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.TrustIr.stepLoopBrk : Env → Cond → Cond → List Stmt → Env` (idempotent).
/// Requires `evalCond`/`evalBody`. No non-foundational axiom.
fn register_step_loop_brk_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_LOOP_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e).λ(cond).λ(brk).λ(body). step ; depth: body=0, brk=1, cond=2, e=3.
    let body =
        step_loop_brk_body_ir(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(bd(), cond_ty(), Expr::lam(bd(), list_stmt.clone(), body)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cond_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt, env_ty()))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.stepLoopBrk): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.execLoopBrk : Env → Cond → Cond → List Stmt → Nat → Env`
/// (idempotent), front-peeling the fuel via `Nat.rec`. Requires `stepLoopBrk`.
fn register_exec_loop_brk_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EXEC_LOOP_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ: λ(n).λ(ih).λ(e'). ih (stepLoopBrk e' cond brk body)
    //   e'=0, ih=1, n=2, fuel=3, body=4, brk=5, cond=6, e=7.
    let succ_case = {
        let step = step_loop_brk_app_ir(Expr::bvar(0), Expr::bvar(6), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(4));
    // λ(e).λ(cond).λ(brk).λ(body).λ(fuel). applied
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
            ),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cond_ty(),
            Expr::pi(
                bd(),
                cond_ty(),
                Expr::pi(bd(), list_stmt, Expr::pi(bd(), cst("Nat"), env_ty())),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.execLoopBrk): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.stepPreservesInvBrk` (idempotent) — the same generalised-guard
/// `Bool.rec` case-split as `stepPreservesInv`, scrutinising the COMBINED break-guard.
/// IDENTICAL structure to `mirsem::register_step_preserves_inv_brk`.
fn register_step_preserves_inv_brk_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_PRESERVES_INV_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();

    // ---- TYPE ----
    let ty = {
        // inside `∀ I ∀ cond ∀ brk ∀ body`: body=0, brk=1, cond=2, I=3.
        let pres = preservation_hyp_type_brk_ir(
            &Expr::bvar(3),
            &Expr::bvar(2),
            &Expr::bvar(1),
            &Expr::bvar(0),
        );
        // conclusion ∀ e, I e → I (stepLoopBrk e cond brk body)
        //   inside `… (pres→) ∀ e`: e=0, pres=1, body=2, brk=3, cond=4, I=5.
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        // under one more arrow: e=1, pres=2, body=3, brk=4, cond=5, I=6.
        let step = step_loop_brk_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(6), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(
                bd(),
                cond_ty(),
                Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt.clone(), after_pres)),
            ),
        )
    };

    // ---- PROOF ----
    // λ I cond brk body pres e hI. ghelper (gG) (Eq.refl Bool (gG))
    //   inside `λ I λ cond λ brk λ body λ pres λ e λ hI`: hI=0, e=1, pres=2, body=3, brk=4, cond=5, I=6.
    let val = {
        let guard = combined_brk_guard_ir(&Expr::bvar(1), &Expr::bvar(5), &Expr::bvar(4));

        // motive_g : λ b. (gG = b) → I (Bool.rec (λ_.Env) e (evalBody e body) b)
        //   inside extra `λ b`: b=0, hI=1, e=2, pres=3, body=4, brk=5, cond=6, I=7.
        let motive_g = {
            let guard_b = combined_brk_guard_ir(&Expr::bvar(2), &Expr::bvar(6), &Expr::bvar(5));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            // codomain under `λ b` + the `eq_dom →` arrow: b=1, hI=2, e=3, pres=4, body=5, brk=6, cond=7, I=8.
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(TRUSTIR_EVAL_BODY), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(8), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };

        // false_case : (gG = false) → I (Bool.rec … false) ≡ I e ; proof = λ _. hI.
        let false_case = {
            let guard_f = combined_brk_guard_ir(&Expr::bvar(1), &Expr::bvar(5), &Expr::bvar(4));
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            Expr::lam(bd(), eq_false, Expr::bvar(1)) // returns hI
        };

        // true_case : (gG = true) → I (Bool.rec … true) ≡ I (evalBody e body) ; proof = λ hg. pres e hI hg.
        let true_case = {
            let guard_t = combined_brk_guard_ir(&Expr::bvar(1), &Expr::bvar(5), &Expr::bvar(4));
            let eq_true = eq_bool_true(guard_t);
            // body under `λ (hg:eq_true)`: hg=0, hI=1, e=2, pres=3.
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };

        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);

        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(
                    bd(),
                    cond_ty(),
                    Expr::lam(
                        bd(),
                        list_stmt.clone(),
                        Expr::lam(
                            bd(),
                            preservation_hyp_type_brk_ir(
                                &Expr::bvar(3),
                                &Expr::bvar(2),
                                &Expr::bvar(1),
                                &Expr::bvar(0),
                            ),
                            Expr::lam(
                                bd(),
                                env_ty(),
                                // hI : I e  (inside `λ I λ cond λ brk λ body λ pres λ e`:
                                //   e=0, pres=1, body=2, brk=3, cond=4, I=5)
                                Expr::lam(bd(), Expr::app(Expr::bvar(5), Expr::bvar(0)), applied),
                            ),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.stepPreservesInvBrk check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.stepPreservesInvBrk): {e:?}"))?;
    Ok(())
}

/// The break-able while-rule TYPE: `∀ I cond brk body, pres → ∀ n e, I e → I (execLoopBrk e
/// cond brk body n)`. `claimed_concl_pred` overrides the conclusion predicate (fail-closed).
/// IDENTICAL to `mirsem::loop_invariant_rule_brk_type`.
fn loop_invariant_rule_brk_type_ir(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // inside `∀ I ∀ cond ∀ brk ∀ body`: body=0, brk=1, cond=2, I=3.
    let pres = preservation_hyp_type_brk_ir(
        &Expr::bvar(3),
        &Expr::bvar(2),
        &Expr::bvar(1),
        &Expr::bvar(0),
    );
    // conclusion ∀ n e, I e → I (execLoopBrk …)
    //   inside `… (pres→) ∀ n ∀ e`: e=0, n=1, pres=2, body=3, brk=4, cond=5, I=6.
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        Expr::app(pred, Expr::bvar(0))
    };
    // under one more arrow: e=1, n=2, pres=3, body=4, brk=5, cond=6, I=7.
    let looped = exec_loop_brk_app_ir(
        Expr::bvar(1),
        Expr::bvar(6),
        Expr::bvar(5),
        Expr::bvar(4),
        Expr::bvar(2),
    );
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(7));
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(bd(), cond_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_stmt, after_pres))),
    )
}

/// The break-able while-rule PROOF, by genuine `Nat.rec` on the fuel. IDENTICAL to
/// `mirsem::loop_invariant_rule_brk_proof` (stepLoop ↦ stepLoopBrk etc.).
fn loop_invariant_rule_brk_proof_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // motive : λ n. ∀ e, I e → I (execLoopBrk e cond brk body n)
    //   inside `… λ pres λ n ∀ e`: e=0, n=1, pres=2, body=3, brk=4, cond=5, I=6.
    let motive = {
        let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
        let looped = exec_loop_brk_app_ir(
            Expr::bvar(1),
            Expr::bvar(6),
            Expr::bvar(5),
            Expr::bvar(4),
            Expr::bvar(2),
        );
        let i_loop = Expr::app(Expr::bvar(7), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };
    // zero_case : I e ⇒ λ e hI. hI.  inside `… λ pres λ e`: e=0, pres=1, body=2, brk=3, cond=4, I=5.
    let zero_case = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };
    // succ_case : λ m ih e hI. ih (stepLoopBrk e cond brk body) (stepPreservesInvBrk I cond brk body pres e hI)
    let succ_case = {
        let ih_ty = {
            // ∀ e, I e → I (execLoopBrk e cond brk body m)  inside `… λ pres λ m ∀ e`:
            //   e=0, m=1, pres=2, body=3, brk=4, cond=5, I=6.
            let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
            let looped = exec_loop_brk_app_ir(
                Expr::bvar(1),
                Expr::bvar(6),
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(2),
            );
            let i_loop = Expr::app(Expr::bvar(7), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        // body: inside `λ m λ ih λ e λ hI`: hI=0, e=1, ih=2, m=3, pres=4, body=5, brk=6, cond=7, I=8.
        let step = step_loop_brk_app_ir(Expr::bvar(1), Expr::bvar(7), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(TRUSTIR_STEP_PRESERVES_INV_BRK),
            [
                Expr::bvar(8), // I
                Expr::bvar(7), // cond
                Expr::bvar(6), // brk
                Expr::bvar(5), // body
                Expr::bvar(4), // pres
                Expr::bvar(1), // e
                Expr::bvar(0), // hI
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        let i_e_hi = Expr::app(Expr::bvar(7), Expr::bvar(0)); // inside `λ m λ ih λ e`: e=0, I=7.
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), ih_ty, Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_hi, ih_app))),
        )
    };
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(
                    bd(),
                    list_stmt,
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_brk_ir(
                            &Expr::bvar(3),
                            &Expr::bvar(2),
                            &Expr::bvar(1),
                            &Expr::bvar(0),
                        ),
                        Expr::lam(bd(), cst("Nat"), rec_applied),
                    ),
                ),
            ),
        ),
    )
}

/// Register `Trust.TrustIr.loopInvariantRuleBrk` (idempotent), kernel-checked at
/// registration. Requires `stepLoopBrk`/`execLoopBrk`/`stepPreservesInvBrk`.
fn register_loop_invariant_rule_brk_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_LOOP_INVARIANT_RULE_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_invariant_rule_brk_type_ir(None);
    let val = loop_invariant_rule_brk_proof_ir();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.loopInvariantRuleBrk check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.loopInvariantRuleBrk): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// NESTED-loop fragment — the STRATIFIED outer-statement layer `OStmt`/`execO` +
// `stepLoopO`/`execLoopO`/`stepPreservesInvO`/`loopInvariantRuleO` (the OUTER Hoare
// while-rule over `List OStmt` bodies). MIRRORS the committed `Trust.MirSem` Step-6N
// nested-loop meta-theory byte-for-byte (`register_ostmt_inductive` / `register_exec_o`
// / `register_step_loop_o` / `register_exec_loop_o` / `register_step_preserves_inv_o` /
// `loop_invariant_rule_o_{type,proof}`) — `eval_cond` ↦ `evalCond`, `exec` ↦ `evalBody`,
// `exec_loop` ↦ `execLoop`, with the de-Bruijn accounting byte-identical to mirsem.rs.
// ADDITIVE & STRATIFIED: a NEW outer-statement type `OStmt` (NOT a non-additive
// `Stmt.Loop`) + NEW `O`-suffixed defs/theorems; the flat `Stmt`/`evalBody`/`execLoop`/
// `loopInvariantRule` fragment is UNTOUCHED (byte-identical), so every flat-body and
// flat-loop certificate stays def-eq.
// ---------------------------------------------------------------------------

/// `List Trust.TrustIr.OStmt` — the outer loop-body list type.
fn list_ostmt_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), cst(TRUSTIR_OSTMT))
}

/// Register the `Trust.TrustIr.OStmt` inductive (idempotent) — the STRATIFIED OUTER
/// statement language. Two constructors:
///   `Assign (idx : Nat)(rv : Rvalue) : OStmt`                   -- a plain outer assignment
///   `Loop (cond : Cond)(body : List Stmt)(fuel : Nat) : OStmt`  -- a FLAT inner loop
/// Both fields of `Loop` use ALREADY-DEFINED types (`Cond`, the flat `List Stmt`, `Nat`),
/// so `OStmt` is a plain (NON-nested, NON-mutual) inductive — its auto-derived `OStmt.rec`
/// is the simple single-motive recursor. Requires `Cond`/`Rvalue`/`Stmt`. The trust-ir
/// analogue of `mirsem::register_ostmt_inductive`.
fn register_ostmt_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_OSTMT);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ostmt_ty = cst(TRUSTIR_OSTMT);
    let assign_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OSTMT_ASSIGN),
        type_: Expr::pi(bd(), nat_ty(), Expr::pi(bd(), rvalue_ty(), ostmt_ty.clone())),
    };
    let loop_ctor = Constructor {
        name: Name::from_string(TRUSTIR_OSTMT_LOOP),
        type_: Expr::pi(
            bd(),
            cond_ty(),
            Expr::pi(bd(), list_stmt_ty(), Expr::pi(bd(), nat_ty(), ostmt_ty.clone())),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![assign_ctor, loop_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.OStmt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.execO : Env → List OStmt → Env` (idempotent), the
/// `evalBody`-analogue over `List OStmt`:
///
/// ```text
/// execO (e : Env) : List OStmt → Env :=
///   @List.rec OStmt (fun _ => Env → Env)
///     (fun e' => e')                                            -- nil : id
///     (fun (s : OStmt) (rest : List OStmt) (ih : Env → Env) (e' : Env) =>
///        ih (@OStmt.rec (fun _ => Env)
///              (fun (i : Nat)(R : Rvalue) => set e' i (evalRvalue e' R))      -- Assign
///              (fun (c : Cond)(b : List Stmt)(f : Nat) => execLoop e' c b f)  -- Loop
///              s))
///     stmts e
/// ```
///
/// Identical env-threading fold to `evalBody`; the `Assign` arm is the SAME `set …
/// (evalRvalue …)`, the new `Loop` arm runs the inner loop to completion via the EXISTING
/// `execLoop`. Requires `OStmt`/`set`/`evalRvalue`/`execLoop`. The trust-ir analogue of
/// `mirsem::register_exec_o`. No non-foundational axiom.
fn register_exec_o(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EXEC_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ostmt_ty = cst(TRUSTIR_OSTMT);
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let list_ostmt = list_ostmt_ty();
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), list_ostmt.clone(), env_ty()));

    // @List.rec.{1,0} : levels [motiveLevel=1 (Env→Env : Sort 1), elemUniv=0].
    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    // @OStmt.rec.{1} : motive lands in Env : Type ⇒ Sort 1.
    let ostmt_rec =
        Expr::const_(Name::from_string(TRUSTIR_OSTMT_REC), vec![Level::succ(Level::zero())]);
    let set = cst(TRUSTIR_SET);
    let eval_rvalue = cst(TRUSTIR_EVAL_RVALUE);

    // motive : λ(_ : List OStmt) → (Env → Env)
    let motive = Expr::lam(bd(), list_ostmt.clone(), env_to_env.clone());
    // nil case : λ(e' : Env). e'
    let nil_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));

    // cons case : λ(s:OStmt). λ(rest:List OStmt). λ(ih:Env→Env). λ(e':Env). ih (stepO e' s)
    //   de-Bruijn at the body: e' = bvar(0), ih = bvar(1), rest = bvar(2), s = bvar(3).
    let cons_case = {
        let ostmt_motive = Expr::lam(bd(), ostmt_ty.clone(), env_ty());
        // Assign minor: λ(i:Nat). λ(R:Rvalue). set e' i (evalRvalue e' R)
        //   under i, R: R=0, i=1, e'=2 (lifted past i,R), ih=3, rest=4, s=5.
        let assign_minor = {
            let e_inner = Expr::bvar(2);
            let i_inner = Expr::bvar(1);
            let r_inner = Expr::bvar(0);
            let evald = Expr::apps(eval_rvalue.clone(), [e_inner.clone(), r_inner]);
            let set_app = Expr::apps(set.clone(), [e_inner, i_inner, evald]);
            Expr::lam(bd(), nat_ty(), Expr::lam(bd(), rvalue_ty(), set_app))
        };
        // Loop minor: λ(c:Cond). λ(b:List Stmt). λ(f:Nat). execLoop e' c b f
        //   under c, b, f: f=0, b=1, c=2, e'=3 (lifted past c,b,f), ih=4, rest=5, s=6.
        let loop_minor = {
            let e_inner = Expr::bvar(3);
            let c_inner = Expr::bvar(2);
            let b_inner = Expr::bvar(1);
            let f_inner = Expr::bvar(0);
            let looped = exec_loop_app_ir(e_inner, c_inner, b_inner, f_inner);
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(bd(), list_stmt_ty(), Expr::lam(bd(), nat_ty(), looped)),
            )
        };
        // @OStmt.rec.{1} motive assign_minor loop_minor s   (s = bvar(3) before e' binder)
        let s_ref = Expr::bvar(3);
        let step = Expr::apps(ostmt_rec, [ostmt_motive, assign_minor, loop_minor, s_ref]);
        let ih_ref = Expr::bvar(1);
        let body = Expr::app(ih_ref, step);
        Expr::lam(
            bd(),
            ostmt_ty.clone(),
            Expr::lam(
                bd(),
                list_ostmt.clone(),
                Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), body)),
            ),
        )
    };

    // @List.rec.{1,0} OStmt motive nil_case cons_case stmts e
    //   under `λ(e:Env). λ(stmts:List OStmt). …` : stmts = bvar(0), e = bvar(1).
    let rec_app =
        Expr::apps(list_rec, [ostmt_ty.clone(), motive, nil_case, cons_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(1));
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), list_ostmt, applied));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.execO): {e:?}"))?;
    Ok(())
}

/// `stepLoopO`'s body = `Bool.rec (λ_.Env) e (execO e body) (evalCond e cond)`.
fn step_loop_o_body_ir(e_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [e_ref.clone(), cond_ref.clone()]);
    let exec_body = Expr::apps(cst(TRUSTIR_EXEC_O), [e_ref.clone(), body_ref.clone()]);
    Expr::apps(bool_rec, [env_motive, e_ref.clone(), exec_body, guard])
}

/// `stepLoopO e cond body` applied as a CONSTANT (signature `Env → Cond → List OStmt → Env`).
fn step_loop_o_app_ir(e_ref: Expr, cond_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_STEP_LOOP_O), [e_ref, cond_ref, body_ref])
}

/// Register `Trust.TrustIr.stepLoopO : Env → Cond → List OStmt → Env` (idempotent) =
/// `λ e cond body. if evalCond e cond then execO e body else e`. The trust-ir analogue of
/// `mirsem::register_step_loop_o`. Requires `evalCond`/`execO`. No non-foundational axiom.
fn register_step_loop_o_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_LOOP_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let body = step_loop_o_body_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cond_ty(), Expr::lam(bd(), list_ostmt.clone(), body)),
    );
    let ty =
        Expr::pi(bd(), env_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_ostmt, env_ty())));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.stepLoopO): {e:?}"))?;
    Ok(())
}

/// `execLoopO e cond body fuel` applied as a CONSTANT to its four refs.
fn exec_loop_o_app_ir(e_ref: Expr, cond_ref: Expr, body_ref: Expr, fuel_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_EXEC_LOOP_O), [e_ref, cond_ref, body_ref, fuel_ref])
}

/// Register `Trust.TrustIr.execLoopO : Env → Cond → List OStmt → Nat → Env` (idempotent),
/// the `execLoop`-analogue over `stepLoopO`. Front-peels via `Nat.rec`. The trust-ir
/// analogue of `mirsem::register_exec_loop_o`. Requires `stepLoopO`. No non-foundational axiom.
fn register_exec_loop_o_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EXEC_LOOP_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ: λ(n)λ(ih)λ(e'). ih (stepLoopO e' cond body)
    //   e'=0, ih=1, n=2, fuel=3, body=4, cond=5, e=6.
    let succ_case = {
        let step = step_loop_o_app_ir(Expr::bvar(0), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(3));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(bd(), list_ostmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_ostmt, Expr::pi(bd(), cst("Nat"), env_ty()))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.execLoopO): {e:?}"))?;
    Ok(())
}

/// The OUTER preservation hypothesis `∀ e, I e → evalCond e cond = true → I (execO e body)`
/// — the `preservation_hyp_type_ir` analogue with `evalBody` ↦ `execO` and `List OStmt` body.
/// BYTE-IDENTICAL accounting to `mirsem::preservation_hyp_type_o`.
fn preservation_hyp_type_o_ir(i_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), lift(cond_ref, 2)]);
    let dom2 = eq_bool_true(guard);
    let exec_body = Expr::apps(cst(TRUSTIR_EXEC_O), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body);
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.TrustIr.stepPreservesInvO` (idempotent) — the OUTER guarded-step
/// invariant-preservation lemma (the `stepPreservesInv` analogue over `execO`/`stepLoopO`).
/// BYTE-IDENTICAL structure to `mirsem::register_step_preserves_inv_o`.
fn register_step_preserves_inv_o_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_PRESERVES_INV_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();

    // TYPE: ∀ I cond body, pres → ∀ e, I e → I (stepLoopO e cond body)
    let ty = {
        let pres = preservation_hyp_type_o_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        let step = step_loop_o_app_ir(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(5), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_ostmt.clone(), after_pres)),
        )
    };

    // PROOF: same generalised-guard Bool.rec case-split, with evalBody ↦ execO.
    let val = {
        let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
        let motive_g = {
            let guard_b = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(2), Expr::bvar(5)]);
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(TRUSTIR_EXEC_O), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(7), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };
        let false_case = {
            let guard_f = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            Expr::lam(bd(), eq_false, Expr::bvar(1))
        };
        let true_case = {
            let guard_t = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_true = eq_bool_true(guard_t);
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);
        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(
                    bd(),
                    list_ostmt.clone(),
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_o_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                        Expr::lam(
                            bd(),
                            env_ty(),
                            Expr::lam(bd(), Expr::app(Expr::bvar(4), Expr::bvar(0)), applied),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.stepPreservesInvO check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.stepPreservesInvO): {e:?}"))?;
    Ok(())
}

/// The OUTER Hoare while-rule TYPE: `∀ I cond body, pres → ∀ n e, I e →
/// I (execLoopO e cond body n)`. The `loop_invariant_rule_type_ir` analogue over `List
/// OStmt`. Mirrors `mirsem::loop_invariant_rule_o_type`.
fn loop_invariant_rule_o_type_ir(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let pres = preservation_hyp_type_o_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(5));
        Expr::app(pred, Expr::bvar(0))
    };
    let looped = exec_loop_o_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(bd(), env_pred_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_ostmt, after_pres)))
}

/// The OUTER Hoare while-rule PROOF, by genuine `Nat.rec` on the fuel, the
/// `loop_invariant_rule_proof_ir` analogue (evalBody ↦ execO, stepLoop ↦ stepLoopO,
/// stepPreservesInv ↦ stepPreservesInvO, execLoop ↦ execLoopO). Mirrors
/// `mirsem::loop_invariant_rule_o_proof`.
fn loop_invariant_rule_o_proof_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let motive = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        let looped = exec_loop_o_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let i_loop = Expr::app(Expr::bvar(6), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };
    let zero_case = {
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };
    let succ_case = {
        let ih_ty = {
            let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
            let looped =
                exec_loop_o_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
            let i_loop = Expr::app(Expr::bvar(6), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        let step = step_loop_o_app_ir(Expr::bvar(1), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(TRUSTIR_STEP_PRESERVES_INV_O),
            [
                Expr::bvar(7),
                Expr::bvar(6),
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(1),
                Expr::bvar(0),
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        let i_e_hi = Expr::app(Expr::bvar(6), Expr::bvar(0));
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), ih_ty, Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_hi, ih_app))),
        )
    };
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(
                bd(),
                list_ostmt,
                Expr::lam(
                    bd(),
                    preservation_hyp_type_o_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

/// Register `Trust.TrustIr.loopInvariantRuleO` (idempotent) — the OUTER Hoare while-rule
/// (PARTIAL correctness over `List OStmt` bodies), kernel-checked at registration. Requires
/// `execO`/`stepLoopO`/`execLoopO`/`stepPreservesInvO`. No non-foundational axiom. The
/// trust-ir analogue of `mirsem::register_loop_invariant_rule_o`.
fn register_loop_invariant_rule_o_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_LOOP_INVARIANT_RULE_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_invariant_rule_o_type_ir(None);
    let val = loop_invariant_rule_o_proof_ir();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.loopInvariantRuleO check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.loopInvariantRuleO): {e:?}"))?;
    Ok(())
}

// ===========================================================================
// CONDITIONAL-UPDATE (SELECT) loop fragment — the STRATIFIED `SStmt`/`execS` layer +
// `iteI` + `stepLoopS`/`execLoopS`/`stepPreservesInvS`/`loopInvariantRuleS` (the SELECT
// Hoare while-rule over `List SStmt` bodies). MIRRORS the committed OStmt nested-loop
// meta-theory byte-for-byte (`execO` ↦ `execS`, `stepLoopO` ↦ `stepLoopS`, …), with the
// `Sel` statement arm grounding through the new `iteI`. ADDITIVE & STRATIFIED: a NEW
// statement type `SStmt` (NOT a non-additive `Rvalue.Sel` arm) + NEW `S`-suffixed
// defs/theorems; the flat `Stmt`/`Rvalue`/`evalBody`/`evalRvalue`/`execLoop`/
// `loopInvariantRule` fragment is UNTOUCHED (byte-identical).
// ===========================================================================

/// `List Trust.TrustIr.SStmt` — the SELECT loop-body list type.
fn list_sstmt_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), cst(TRUSTIR_SSTMT))
}

/// Register `Trust.TrustIr.iteI : Env → Cond → Int → Int → Int` (idempotent) =
/// `λ e c t f. Bool.rec (λ_.Int) f t (evalCond e c)`. The trust-ir analogue of
/// `mirsem::register_ite_i`. Requires `evalCond`. No non-foundational axiom (`Bool.rec`/
/// `evalCond` are prelude/Trust definitions).
fn register_ite_i_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_ITE_I);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // iteI : Env → Cond → Int → Int → Int
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cond_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()))),
    );
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    // λ(e).λ(c).λ(t).λ(f). de-Bruijn: f=0, t=1, c=2, e=3.
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(3), Expr::bvar(2)]);
    // Bool.rec.{1} (λ_.Int) (false ↦ f) (true ↦ t) (evalCond e c)
    let body = Expr::apps(bool_rec, [int_motive, Expr::bvar(0), Expr::bvar(1), guard]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cond_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.iteI): {e:?}"))?;
    Ok(())
}

/// Register the `Trust.TrustIr.SStmt` inductive (idempotent) — the STRATIFIED SELECT
/// statement language. Two constructors:
///   `Assign (idx : Nat)(rv : Rvalue) : SStmt`                      -- a plain assignment
///   `Sel (idx : Nat)(c : Cond)(a b : Operand) : SStmt`             -- the conditional update
/// Both use ALREADY-DEFINED types, so `SStmt` is a plain (NON-nested, NON-mutual) inductive
/// whose auto-derived `SStmt.rec` is the simple single-motive recursor. Requires
/// `Rvalue`/`Cond`/`Operand`.
fn register_sstmt_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_SSTMT);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let sstmt_ty = cst(TRUSTIR_SSTMT);
    let assign_ctor = Constructor {
        name: Name::from_string(TRUSTIR_SSTMT_ASSIGN),
        type_: Expr::pi(bd(), nat_ty(), Expr::pi(bd(), rvalue_ty(), sstmt_ty.clone())),
    };
    // Sel : Nat → Cond → Operand → Operand → SStmt
    let sel_ctor = Constructor {
        name: Name::from_string(TRUSTIR_SSTMT_SEL),
        type_: Expr::pi(
            bd(),
            nat_ty(),
            Expr::pi(
                bd(),
                cond_ty(),
                Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), sstmt_ty.clone())),
            ),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![assign_ctor, sel_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.SStmt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.execS : Env → List SStmt → Env` (idempotent), the
/// `evalBody`-analogue over `List SStmt`:
///
/// ```text
/// execS (e : Env) : List SStmt → Env :=
///   @List.rec SStmt (fun _ => Env → Env)
///     (fun e' => e')
///     (fun (s : SStmt) (rest : List SStmt) (ih : Env → Env) (e' : Env) =>
///        ih (@SStmt.rec (fun _ => Env)
///              (fun (i : Nat)(R : Rvalue) => set e' i (evalRvalue e' R))            -- Assign
///              (fun (i : Nat)(c : Cond)(a b : Operand) =>
///                 set e' i (iteI e' c (evalOperand e' a)(evalOperand e' b)))        -- Sel
///              s))
///     stmts e
/// ```
///
/// Identical env-threading fold to `execO`; the `Assign` arm is the SAME `set …
/// (evalRvalue …)`, the new `Sel` arm threads the conditional `set … (iteI …)`. Requires
/// `SStmt`/`set`/`evalRvalue`/`evalOperand`/`iteI`. No non-foundational axiom.
fn register_exec_s(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EXEC_S);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let sstmt_ty = cst(TRUSTIR_SSTMT);
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let list_sstmt = list_sstmt_ty();
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), list_sstmt.clone(), env_ty()));

    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let sstmt_rec =
        Expr::const_(Name::from_string(TRUSTIR_SSTMT_REC), vec![Level::succ(Level::zero())]);
    let set = cst(TRUSTIR_SET);
    let eval_rvalue = cst(TRUSTIR_EVAL_RVALUE);
    let eval_operand = cst(TRUSTIR_EVAL_OPERAND);

    // motive : λ(_ : List SStmt) → (Env → Env)
    let motive = Expr::lam(bd(), list_sstmt.clone(), env_to_env.clone());
    // nil case : λ(e' : Env). e'
    let nil_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));

    // cons case : λ(s:SStmt). λ(rest:List SStmt). λ(ih:Env→Env). λ(e':Env). ih (stepS e' s)
    //   de-Bruijn at the body: e' = bvar(0), ih = bvar(1), rest = bvar(2), s = bvar(3).
    let cons_case = {
        let sstmt_motive = Expr::lam(bd(), sstmt_ty.clone(), env_ty());
        // Assign minor: λ(i:Nat). λ(R:Rvalue). set e' i (evalRvalue e' R)
        //   under i, R: R=0, i=1, e'=2 (lifted past i,R), ih=3, rest=4, s=5.
        let assign_minor = {
            let e_inner = Expr::bvar(2);
            let i_inner = Expr::bvar(1);
            let r_inner = Expr::bvar(0);
            let evald = Expr::apps(eval_rvalue.clone(), [e_inner.clone(), r_inner]);
            let set_app = Expr::apps(set.clone(), [e_inner, i_inner, evald]);
            Expr::lam(bd(), nat_ty(), Expr::lam(bd(), rvalue_ty(), set_app))
        };
        // Sel minor: λ(i:Nat). λ(c:Cond). λ(a:Operand). λ(b:Operand).
        //              set e' i (iteI e' c (evalOperand e' a)(evalOperand e' b))
        //   under i, c, a, b: b=0, a=1, c=2, i=3, e'=4 (lifted past i,c,a,b), ih=5, rest=6, s=7.
        let sel_minor = {
            let e_inner = Expr::bvar(4);
            let i_inner = Expr::bvar(3);
            let c_inner = Expr::bvar(2);
            let a_inner = Expr::bvar(1);
            let b_inner = Expr::bvar(0);
            let eval_a = Expr::apps(eval_operand.clone(), [e_inner.clone(), a_inner]);
            let eval_b = Expr::apps(eval_operand.clone(), [e_inner.clone(), b_inner]);
            let ite = Expr::apps(cst(TRUSTIR_ITE_I), [e_inner.clone(), c_inner, eval_a, eval_b]);
            let set_app = Expr::apps(set.clone(), [e_inner, i_inner, ite]);
            Expr::lam(
                bd(),
                nat_ty(),
                Expr::lam(
                    bd(),
                    cond_ty(),
                    Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), set_app)),
                ),
            )
        };
        // @SStmt.rec.{1} motive assign_minor sel_minor s   (s = bvar(3) before e' binder)
        let s_ref = Expr::bvar(3);
        let step = Expr::apps(sstmt_rec, [sstmt_motive, assign_minor, sel_minor, s_ref]);
        let ih_ref = Expr::bvar(1);
        let body = Expr::app(ih_ref, step);
        Expr::lam(
            bd(),
            sstmt_ty.clone(),
            Expr::lam(
                bd(),
                list_sstmt.clone(),
                Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), body)),
            ),
        )
    };

    // @List.rec.{1,0} SStmt motive nil_case cons_case stmts e
    let rec_app =
        Expr::apps(list_rec, [sstmt_ty.clone(), motive, nil_case, cons_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(1));
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), list_sstmt, applied));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.execS): {e:?}"))?;
    Ok(())
}

/// `stepLoopS e cond body` applied as a CONSTANT (signature `Env → Cond → List SStmt → Env`).
fn step_loop_s_app_ir(e_ref: Expr, cond_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_STEP_LOOP_S), [e_ref, cond_ref, body_ref])
}

/// Register `Trust.TrustIr.stepLoopS : Env → Cond → List SStmt → Env` (idempotent) =
/// `λ e cond body. if evalCond e cond then execS e body else e`. The `stepLoopO`-analogue
/// over `execS`. Requires `evalCond`/`execS`. No non-foundational axiom.
fn register_step_loop_s_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_LOOP_S);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_sstmt = list_sstmt_ty();
    // body = Bool.rec (λ_.Env) e (execS e body) (evalCond e cond), at e=2,cond=1,body=0.
    let body = {
        let bool_rec =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
        let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(2), Expr::bvar(1)]);
        let exec_body = Expr::apps(cst(TRUSTIR_EXEC_S), [Expr::bvar(2), Expr::bvar(0)]);
        Expr::apps(bool_rec, [env_motive, Expr::bvar(2), exec_body, guard])
    };
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cond_ty(), Expr::lam(bd(), list_sstmt.clone(), body)),
    );
    let ty =
        Expr::pi(bd(), env_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_sstmt, env_ty())));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.stepLoopS): {e:?}"))?;
    Ok(())
}

/// `execLoopS e cond body fuel` applied as a CONSTANT to its four refs.
fn exec_loop_s_app_ir(e_ref: Expr, cond_ref: Expr, body_ref: Expr, fuel_ref: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_EXEC_LOOP_S), [e_ref, cond_ref, body_ref, fuel_ref])
}

/// Register `Trust.TrustIr.execLoopS : Env → Cond → List SStmt → Nat → Env` (idempotent),
/// the `execLoopO`-analogue over `stepLoopS`. Front-peels via `Nat.rec`. Requires
/// `stepLoopS`. No non-foundational axiom.
fn register_exec_loop_s_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EXEC_LOOP_S);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_sstmt = list_sstmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ: λ(n)λ(ih)λ(e'). ih (stepLoopS e' cond body) ; e'=0, ih=1, n=2, fuel=3, body=4, cond=5, e=6.
    let succ_case = {
        let step = step_loop_s_app_ir(Expr::bvar(0), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(3));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(bd(), list_sstmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_sstmt, Expr::pi(bd(), cst("Nat"), env_ty()))),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(TrustIr.execLoopS): {e:?}"))?;
    Ok(())
}

/// The SELECT preservation hypothesis `∀ e, I e → evalCond e cond = true → I (execS e body)`
/// — the `preservation_hyp_type_o_ir` analogue with `execO` ↦ `execS` and `List SStmt` body.
fn preservation_hyp_type_s_ir(i_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), lift(cond_ref, 2)]);
    let dom2 = eq_bool_true(guard);
    let exec_body = Expr::apps(cst(TRUSTIR_EXEC_S), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body);
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.TrustIr.stepPreservesInvS` (idempotent) — the SELECT guarded-step
/// invariant-preservation lemma. BYTE-IDENTICAL structure to `register_step_preserves_inv_o_ir`
/// (`execO` ↦ `execS`, `stepLoopO` ↦ `stepLoopS`).
fn register_step_preserves_inv_s_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_STEP_PRESERVES_INV_S);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_sstmt = list_sstmt_ty();

    // TYPE: ∀ I cond body, pres → ∀ e, I e → I (stepLoopS e cond body)
    let ty = {
        let pres = preservation_hyp_type_s_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        let step = step_loop_s_app_ir(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(5), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_sstmt.clone(), after_pres)),
        )
    };

    // PROOF: same generalised-guard Bool.rec case-split, with evalBody ↦ execS.
    let val = {
        let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
        let motive_g = {
            let guard_b = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(2), Expr::bvar(5)]);
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(TRUSTIR_EXEC_S), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(7), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };
        let false_case = {
            let guard_f = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            Expr::lam(bd(), eq_false, Expr::bvar(1))
        };
        let true_case = {
            let guard_t = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_true = eq_bool_true(guard_t);
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);
        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cond_ty(),
                Expr::lam(
                    bd(),
                    list_sstmt.clone(),
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_s_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                        Expr::lam(
                            bd(),
                            env_ty(),
                            Expr::lam(bd(), Expr::app(Expr::bvar(4), Expr::bvar(0)), applied),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.stepPreservesInvS check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.stepPreservesInvS): {e:?}"))?;
    Ok(())
}

/// The SELECT Hoare while-rule TYPE: `∀ I cond body, pres → ∀ n e, I e → I (execLoopS e cond
/// body n)`. The `loop_invariant_rule_o_type_ir` analogue over `List SStmt`.
fn loop_invariant_rule_s_type_ir(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_sstmt = list_sstmt_ty();
    let pres = preservation_hyp_type_s_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(5));
        Expr::app(pred, Expr::bvar(0))
    };
    let looped = exec_loop_s_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(bd(), env_pred_ty(), Expr::pi(bd(), cond_ty(), Expr::pi(bd(), list_sstmt, after_pres)))
}

/// The SELECT Hoare while-rule PROOF, by genuine `Nat.rec` on the fuel, the
/// `loop_invariant_rule_o_proof_ir` analogue (execO ↦ execS, stepLoopO ↦ stepLoopS,
/// stepPreservesInvO ↦ stepPreservesInvS, execLoopO ↦ execLoopS).
fn loop_invariant_rule_s_proof_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_sstmt = list_sstmt_ty();
    let motive = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        let looped = exec_loop_s_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let i_loop = Expr::app(Expr::bvar(6), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };
    let zero_case = {
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };
    let succ_case = {
        let ih_ty = {
            let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
            let looped =
                exec_loop_s_app_ir(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
            let i_loop = Expr::app(Expr::bvar(6), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        let step = step_loop_s_app_ir(Expr::bvar(1), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(TRUSTIR_STEP_PRESERVES_INV_S),
            [
                Expr::bvar(7),
                Expr::bvar(6),
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(1),
                Expr::bvar(0),
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        let i_e_hi = Expr::app(Expr::bvar(6), Expr::bvar(0));
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), ih_ty, Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_hi, ih_app))),
        )
    };
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cond_ty(),
            Expr::lam(
                bd(),
                list_sstmt,
                Expr::lam(
                    bd(),
                    preservation_hyp_type_s_ir(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

/// Register `Trust.TrustIr.loopInvariantRuleS` (idempotent) — the SELECT Hoare while-rule
/// (PARTIAL correctness over `List SStmt` bodies), kernel-checked at registration. Requires
/// `execS`/`stepLoopS`/`execLoopS`/`stepPreservesInvS`. No non-foundational axiom.
fn register_loop_invariant_rule_s_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_LOOP_INVARIANT_RULE_S);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_invariant_rule_s_type_ir(None);
    let val = loop_invariant_rule_s_proof_ir();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty)
            .map_err(|e| format!("TrustIr.loopInvariantRuleS check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(TrustIr.loopInvariantRuleS): {e:?}"))?;
    Ok(())
}

// ===========================================================================
// SLICE-INDEX (BOUNDS-GUARDED) operand fragment — the STRATIFIED `XOperand`/`evalXOperand`
// layer + the opaque `idxElem`/`sliceLen` selectors. ADDITIVE & STRATIFIED: a NEW
// operand-extension type `XOperand` (NOT new `Operand` arms) referencing the EXISTING flat
// `Operand`; the flat `Operand`/`evalOperand` recursors stay BYTE-IDENTICAL. Mirrors
// `Trust.MirSem.{Operand.Index, Operand.Len, idx_elem, slice_len}` relocated onto a separate
// operand layer rather than `Operand` arms.
// ===========================================================================

/// Register `Trust.TrustIr.idxElem : Int → Int → Int` and `Trust.TrustIr.sliceLen : Int → Int`
/// (idempotent) as `Declaration::Opaque` — the UNINTERPRETED total slice selectors. The bodies
/// are type-correct placeholders the kernel NEVER unfolds (`Opaque` constants do not δ-reduce),
/// so each behaves as a fresh uninterpreted function symbol. `Opaque` is NOT `ConstantKind::
/// Axiom`, so a term referencing them gains NO axiom dependency (the `bnot` discipline).
fn register_idx_elem_ir(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    if env.get_const(&Name::from_string(TRUSTIR_IDX_ELEM)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
        let placeholder = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), int_lit(0)));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_IDX_ELEM),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(idxElem): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(TRUSTIR_SLICE_LEN)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), int_ty());
        let placeholder = Expr::lam(bd(), int_ty(), int_lit(0));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_SLICE_LEN),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(sliceLen): {e:?}"))?;
    }
    Ok(())
}

/// Trust: ITER-NEXT VALUE-PATH (2026-07-21) — register the iterator-cursor selectors
/// `Trust.MirSem.iter_region : Int → Int` and `Trust.MirSem.iter_has_next : Int → Bool`
/// (idempotent) as `Declaration::Opaque` — the UNINTERPRETED total entry-time handle
/// constructor + dispatch head the `<Iter as Iterator>::next` value witness names (see
/// [`TRUSTIR_ITER_REGION`] / [`TRUSTIR_ITER_HAS_NEXT`]). Bodies are type-correct
/// placeholders the kernel NEVER unfolds (`Opaque` constants do not δ-reduce), so each
/// behaves as a fresh uninterpreted function symbol. `Opaque` is NOT `ConstantKind::Axiom`,
/// so a term referencing them gains NO axiom dependency — modulo-3 closure preserved,
/// EXACTLY the `idxElem`/`sliceLen` precedent above.
fn register_iter_selectors_ir(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    if env.get_const(&Name::from_string(TRUSTIR_ITER_REGION)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), int_ty());
        let placeholder = Expr::lam(bd(), int_ty(), int_lit(0));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_ITER_REGION),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(iter_region): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(TRUSTIR_ITER_HAS_NEXT)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), cst("Bool"));
        // A total `Int → Bool` placeholder body (never unfolded — `Opaque`).
        let placeholder = Expr::lam(bd(), int_ty(), cst("Bool.true"));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_ITER_HAS_NEXT),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(iter_has_next): {e:?}"))?;
    }
    // Trust: W-PRIMED increment 1 (2026-07-22) — the TWO-KEY (generation-re-keyed) primed
    // surface: ONE opaque element base (`iter_seq`, ABSOLUTE-indexed so no shift/tail LAW is
    // ever needed — the axiom-killer), ONE opaque length (`iter_len`), and the DEFINITIONAL
    // dispatch head (`iter_has_next2 := g < iter_len recv`). Both opaques carry EMPTY
    // axiom_deps (the `ptrOffset`/`iter_region` precedent); `iter_has_next2` is a plain
    // Definition (axiom-free — a `decide`/`Int.lt` combinator over `iter_len`). NO law/bridge
    // over `iter_seq` or to the one-arg `iter_region` family (forbidden, axiom-shaped).
    if env.get_const(&Name::from_string(TRUSTIR_ITER_SEQ)).is_none() {
        // `Int → Int → Int` (recv-carrier, absolute element index k).
        let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
        let placeholder = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), int_lit(0)));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_ITER_SEQ),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(iter_seq): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(TRUSTIR_ITER_LEN)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), int_ty());
        let placeholder = Expr::lam(bd(), int_ty(), int_lit(0));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_ITER_LEN),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(iter_len): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(TRUSTIR_ITER_HAS_NEXT2)).is_none() {
        // `iter_has_next2 recv g := decide (Int.lt g (iter_len recv)) (Int.decLt g
        // (iter_len recv))` — the SemCmpOp::Lt combinator `guard_bool` lowers, keyed on the
        // recv-keyed `iter_len`. Under `λ recv λ g`: recv = bvar 1, g = bvar 0.
        let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), cst("Bool")));
        let iter_len_recv = Expr::app(cst(TRUSTIR_ITER_LEN), Expr::bvar(1));
        let lt = Expr::apps(cst("Int.lt"), [Expr::bvar(0), iter_len_recv.clone()]);
        let dec = Expr::apps(cst("Int.decLt"), [Expr::bvar(0), iter_len_recv]);
        let body = Expr::apps(cst("decide"), [lt, dec]);
        let value = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(TRUSTIR_ITER_HAS_NEXT2),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl(iter_has_next2): {e:?}"))?;
    }
    Ok(())
}

/// Trust: RECORD-WITNESS increment 3 (2026-07-22) — register the RECORD pointer-field
/// selectors `Trust.TrustIr.sliceStart : Int → Int` and
/// `Trust.TrustIr.ptrOffset : Int → Int → Int → Int` (idempotent) as
/// `Declaration::Opaque` — the UNINTERPRETED total slice-start handle constructor + the
/// pointee-pinned pointer offset the `into_iter`/`slice::Iter::new` RECORD witness names
/// (see [`TRUSTIR_SLICE_START`] / [`TRUSTIR_PTR_OFFSET`]). Bodies are type-correct
/// placeholders the kernel NEVER unfolds (`Opaque` constants do not δ-reduce), so each
/// behaves as a fresh uninterpreted function symbol. `Opaque` is NOT `ConstantKind::Axiom`,
/// so a term referencing them gains NO axiom dependency — modulo-3 closure preserved,
/// EXACTLY the `idxElem`/`sliceLen`/`iter_region` precedent.
fn register_ptr_selectors_ir(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    if env.get_const(&Name::from_string(TRUSTIR_SLICE_START)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), int_ty());
        let placeholder = Expr::lam(bd(), int_ty(), int_lit(0));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_SLICE_START),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(sliceStart): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(TRUSTIR_PTR_OFFSET)).is_none() {
        // `Int → Int → Int → Int` (base, count, elemSize).
        let ty = Expr::pi(
            bd(),
            int_ty(),
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty())),
        );
        let placeholder = Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), int_lit(0))),
        );
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(TRUSTIR_PTR_OFFSET),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(ptrOffset): {e:?}"))?;
    }
    Ok(())
}

/// Trust: W19 mutators inc-1 (2026-07-24) — register the FIELD-SETTER post-state
/// surface (idempotent), a sibling of [`register_idx_elem_ir`]/
/// [`register_iter_selectors_ir`], into the shared `trustir_env`:
///   * `Trust.MirSem.idx_elem_prime : Int → Int → Int → Int` — the generation-re-keyed
///     field-content base, `Declaration::Opaque` with a type-correct never-unfolded
///     placeholder body (`λλλ Int.ofNat 0`). `Opaque` is NOT an `Axiom`, so a term
///     naming it gains NO axiom dependency (the `idx_elem`/`iter_seq`/`ptrOffset`
///     precedent). It behaves as a fresh uninterpreted symbol.
///   * `Trust.MirSem.set_key_eq : Int → Int → Bool := λ k f. Int.beq k f` — the shared
///     key-guard head, a reducible `Declaration::Definition` wrapping the EXISTING
///     `Int.beq` ⇒ EMPTY `axiom_deps` (`Int.beq` is a prelude Definition, NOT an
///     `Opaque` and NOT an `Axiom`; what matters here is only that its axiom closure is
///     empty). It need not reduce (the `congrArg`
///     transport carries the guard as a hypothesis).
/// The per-certificate `set_post` Definition is registered separately, FRESH per
/// obligation, by `trustir_adt::build_field_set_env` (the `ret2`/`post2` role). NO
/// bridge law from `idx_elem_prime` to the LIVE 2-arg `idx_elem` is minted (F12-forbidden
/// cross-instantiation, deferred). Modulo-3 preserved (both closures empty).
fn register_field_set_surface_ir(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    if env.get_const(&Name::from_string(crate::mirsem::MIRSEM_IDX_ELEM_PRIME)).is_none() {
        // `Int → Int → Int → Int` (recv-handle, field-key, generation).
        let ty = Expr::pi(
            bd(),
            int_ty(),
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty())),
        );
        let placeholder = Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), int_lit(0))),
        );
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(crate::mirsem::MIRSEM_IDX_ELEM_PRIME),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(idx_elem_prime): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(crate::mirsem::MIRSEM_SET_KEY_EQ)).is_none() {
        // `set_key_eq k f := Int.beq k f` — under `λ k λ f`: k = bvar 1, f = bvar 0.
        let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), cst("Bool")));
        let body = Expr::apps(cst("Int.beq"), [Expr::bvar(1), Expr::bvar(0)]);
        let value = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(crate::mirsem::MIRSEM_SET_KEY_EQ),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl(set_key_eq): {e:?}"))?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Trust: W-ADDR increment 1 (2026-07-22) — the DIST-INIT hypothesis-carrying
// kernel theorem `Trust.TrustIr.iterDistInit` (GATE-PTR-SLOT-OPACITY(c)
// narrow-sanction, see [`TRUSTIR_ITER_DIST_INIT`]). The `memoAdequate` discipline:
// address content enters ONLY as the named hypothesis `hOff`; the kernel checks
// ONLY the arithmetic composition, and `axiom_deps` stays EMPTY (probe-pinned).
// ---------------------------------------------------------------------------

/// The `@Eq.{1} Int x y` proposition (both operands are `Int : Sort 1`).
fn eq_int_prop(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]), [
        int_ty(),
        x,
        y,
    ])
}

/// `sliceStart (bvar si)` — the abstract base address of the slice handle bound at
/// de-Bruijn index `si`.
fn dist_start(si: u32) -> Expr {
    Expr::app(cst(TRUSTIR_SLICE_START), Expr::bvar(si))
}
/// `sliceLen (bvar si)` — the abstract length of the slice handle bound at `si`.
fn dist_len(si: u32) -> Expr {
    Expr::app(cst(TRUSTIR_SLICE_LEN), Expr::bvar(si))
}
/// `sliceLen (bvar si) * (bvar ei)` — the `B` term (`sliceLen s * e`).
fn dist_b(si: u32, ei: u32) -> Expr {
    Expr::apps(cst("Int.mul"), [dist_len(si), Expr::bvar(ei)])
}
/// `ptrOffset (sliceStart (bvar si)) (sliceLen (bvar si)) (bvar ei)` — the `P` term.
fn dist_p(si: u32, ei: u32) -> Expr {
    Expr::apps(cst(TRUSTIR_PTR_OFFSET), [dist_start(si), dist_len(si), Expr::bvar(ei)])
}

/// The `hOff` hypothesis TYPE at a binder depth where `s` is `bvar si` and `e` is `bvar ei`:
/// `ptrOffset (sliceStart s) (sliceLen s) e = sliceStart s + sliceLen s * e`.
fn dist_hoff_ty(si: u32, ei: u32) -> Expr {
    eq_int_prop(dist_p(si, ei), Expr::apps(cst("Int.add"), [dist_start(si), dist_b(si, ei)]))
}
/// The `hLen` hypothesis TYPE at a binder depth where `s` is `bvar si`: `0 ≤ sliceLen s`.
fn dist_hlen_ty(si: u32) -> Expr {
    Expr::apps(cst("Int.le"), [int_lit(0), dist_len(si)])
}

/// Build `(statement, proof)` for `Trust.TrustIr.iterDistInit` (see
/// [`TRUSTIR_ITER_DIST_INIT`]). The statement is the ∀-closed conditional over `hOff`/`hLen`;
/// the proof rewrites `hOff` (`Eq.subst`) onto the pre-proven `(a + b) − a = b` normalization
/// (`Int.add_comm` ▸ `Int.add_neg_cancel_right`, `Int.sub` reducible). PRIMARY form (hOff is
/// genuinely consumed) — the pre-normalized fallback is NOT taken because the kernel closes the
/// subtraction step. Fence-safe: the ONLY fenced symbols (`sliceStart`/`ptrOffset`) live inside
/// THIS theorem's checked terms.
pub(crate) fn iter_dist_init_theorem_terms() -> (Expr, Expr) {
    let bd = || BinderData::from(BinderInfo::Default);
    let l1 = || Level::succ(Level::zero());
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let sub = |x: Expr, y: Expr| Expr::apps(cst("Int.sub"), [x, y]);
    let neg = |x: Expr| Expr::app(cst("Int.neg"), x);
    let eq_subst = |m: Expr, a: Expr, b: Expr, h: Expr, t: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq.subst"), vec![l1()]), [
            int_ty(),
            m,
            a,
            b,
            h,
            t,
        ])
    };

    // ---- STATEMENT: ∀ (s e : Int), hOff → hLen → ptrOffset(..) - sliceStart s = sliceLen s * e.
    // Binder stack (seen from the innermost consequent): hLen=0, hOff=1, e=2, s=3.
    let consequent = eq_int_prop(sub(dist_p(3, 2), dist_start(3)), dist_b(3, 2));
    let pi_hlen = Expr::pi(bd(), dist_hlen_ty(2), consequent); // hLen domain at s=2,e=1
    let pi_hoff = Expr::pi(bd(), dist_hoff_ty(1, 0), pi_hlen); // hOff domain at s=1,e=0
    let pi_e = Expr::pi(bd(), int_ty(), pi_hoff);
    let statement = Expr::pi(bd(), int_ty(), pi_e);

    // ---- PROOF: λ (s e : Int) (hOff) (hLen). <goal>. In the body: s=3, e=2, hOff=1, hLen=0.
    let a = dist_start(3);
    let b = dist_b(3, 2);
    let p = dist_p(3, 2);
    // cancel : ((B + A) + (-A)) = B          [Int.add_neg_cancel_right B A]
    let cancel = Expr::apps(cst("Int.add_neg_cancel_right"), [b.clone(), a.clone()]);
    // motive1 := λ w. (w + (-A)) = B         (A,B live one binder out → lift 1)
    let motive1 = Expr::lam(
        bd(),
        int_ty(),
        eq_int_prop(add(Expr::bvar(0), neg(a.clone().lift(1))), b.clone().lift(1)),
    );
    // add_comm B A : (B + A) = (A + B)
    let add_comm_ba = Expr::apps(cst("Int.add_comm"), [b.clone(), a.clone()]);
    // base : ((A + B) + (-A)) = B   ≡def   (Int.sub (A+B) A) = B
    let base = eq_subst(motive1, add(b.clone(), a.clone()), add(a.clone(), b.clone()), add_comm_ba, cancel);
    // motive2 := λ z. (Int.sub z A) = B      (A,B live one binder out → lift 1)
    let motive2 = Expr::lam(
        bd(),
        int_ty(),
        eq_int_prop(sub(Expr::bvar(0), a.clone().lift(1)), b.clone().lift(1)),
    );
    // Eq.symm hOff : (A + B) = P             [hOff : P = A + B, hOff = bvar 1]
    let eq_symm_hoff = Expr::apps(Expr::const_(Name::from_string("Eq.symm"), vec![l1()]), [
        int_ty(),
        p.clone(),
        add(a.clone(), b.clone()),
        Expr::bvar(1),
    ]);
    // goal : (Int.sub P A) = B   — rewrite (A+B) ↦ P in `base` via Eq.subst.
    let goal = eq_subst(motive2, add(a.clone(), b.clone()), p, eq_symm_hoff, base);

    let proof = Expr::lam(
        bd(),
        int_ty(),
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), dist_hoff_ty(1, 0), Expr::lam(bd(), dist_hlen_ty(2), goal)),
        ),
    );
    (statement, proof)
}

/// Kernel-recheck `Trust.TrustIr.iterDistInit` (E10 path): typecheck the proof against the
/// statement in a fresh `trustir_env`, register it as a `Declaration::Theorem`, and return its
/// axiom residue (EMPTY ⇒ axiom-free modulo the 3 foundational axioms). `Err` (fail-closed) on
/// any typecheck / registration failure.
pub(crate) fn iter_dist_init_theorem_axiom_residue() -> Result<Vec<String>, String> {
    let (statement, proof) = iter_dist_init_theorem_terms();
    let mut env = trustir_env()?;
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &statement).map_err(|e| format!("check_type(iterDistInit): {e:?}"))?;
    drop(tc);
    let name = Name::from_string(TRUSTIR_ITER_DIST_INIT);
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    })
    .map_err(|e| format!("add_decl(iterDistInit): {e:?}"))?;
    let residue = env.axiom_deps(&name).ok_or_else(|| "iterDistInit decl absent after add".to_string())?;
    let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
    names.sort();
    names.dedup();
    Ok(names)
}

/// True iff `Trust.TrustIr.iterDistInit` kernel-rechecks AXIOM-FREE (modulo the 3 foundational
/// axioms) — the `theorem_checked` bit the DIST-INIT recognizer records. The theorem is FIXED
/// (`∀ s e`, no per-instance data), so the recheck result is a constant: memoize it once
/// (`OnceLock`) so the recognizer's per-invocation call does not re-run the kernel each time
/// (the proven `trustir_env` memoization discipline; soundness unchanged — still a full
/// kernel typecheck, just performed once).
#[must_use]
pub(crate) fn iter_dist_init_theorem_checks() -> bool {
    static MEMO: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *MEMO.get_or_init(|| {
        matches!(iter_dist_init_theorem_axiom_residue(), Ok(residue) if residue.is_empty())
    })
}

/// The iterDistInit statement's Pi-telescope binder DOMAIN types (outermost first —
/// `[Int, Int, hOff-ty, hLen-ty]`) and the final consequent (the non-Pi body). For the
/// hypothesis-list pin (`{hOff, hLen}` exactly).
#[cfg(test)]
#[must_use]
pub(crate) fn iter_dist_init_telescope() -> (Vec<Expr>, Expr) {
    let (statement, _) = iter_dist_init_theorem_terms();
    let mut doms: Vec<Expr> = Vec::new();
    let mut cur = statement;
    loop {
        let next = match cur.kind() {
            ExprKind::Pi(_, dom, body) => {
                doms.push((**dom).clone());
                (**body).clone()
            }
            _ => break,
        };
        cur = next;
    }
    (doms, cur)
}

/// The EXPECTED `[hOff-domain, hLen-domain]` hypothesis types (byte-equal pinning target).
#[cfg(test)]
#[must_use]
pub(crate) fn iter_dist_init_expected_hypotheses() -> [Expr; 2] {
    [dist_hoff_ty(1, 0), dist_hlen_ty(2)]
}

/// The EXPECTED consequent `ptrOffset(..) - sliceStart s = sliceLen s * e` (at s=3, e=2).
#[cfg(test)]
#[must_use]
pub(crate) fn iter_dist_init_expected_consequent() -> Expr {
    eq_int_prop(
        Expr::apps(cst("Int.sub"), [dist_p(3, 2), dist_start(3)]),
        dist_b(3, 2),
    )
}

/// `Int : Sort 1` type expr — exposed so the hypothesis-list pin can byte-compare the two
/// leading `∀ (s e : Int)` binder domains.
#[cfg(test)]
#[must_use]
pub(crate) fn iter_dist_init_int_ty() -> Expr {
    int_ty()
}

#[cfg(test)]
mod w_addr_dist_init_kernel_tests {
    //! Trust: W-ADDR increment 1 — the KERNEL_WITNESS de-risk probe: `iterDistInit`
    //! kernel-rechecks AXIOM-FREE (modulo 3) with the PRIMARY (hOff-rewritten) statement.
    #[test]
    fn iter_dist_init_kernel_rechecks_axiom_free() {
        let residue = super::iter_dist_init_theorem_axiom_residue()
            .expect("iterDistInit must typecheck and register");
        assert!(residue.is_empty(), "iterDistInit must be axiom-free modulo 3, got {residue:?}");
        assert!(super::iter_dist_init_theorem_checks());
    }
}

/// `Trust.TrustIr.XOperand` type expr.
fn xoperand_ty() -> Expr {
    cst(TRUSTIR_XOPERAND)
}

/// Register the `Trust.TrustIr.XOperand` inductive (idempotent) — the STRATIFIED slice-operand
/// extension. Three constructors:
///   `Base  (op : Operand) : XOperand`         -- lift a flat operand
///   `Index (s i : Operand) : XOperand`        -- slice element `s[i]`
///   `Len   (s : Operand) : XOperand`          -- slice length `s.len()`
/// Every field is the ALREADY-CLOSED flat `Operand`, so `XOperand` is a plain (NON-nested,
/// NON-mutual) inductive whose `XOperand.rec` is the simple recursor. Requires `Operand`.
fn register_xoperand_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_XOPERAND);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let xty = xoperand_ty();
    let base_ctor = Constructor {
        name: Name::from_string(TRUSTIR_XOPERAND_BASE),
        type_: Expr::pi(bd(), operand_ty(), xty.clone()),
    };
    let index_ctor = Constructor {
        name: Name::from_string(TRUSTIR_XOPERAND_INDEX),
        type_: Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), xty.clone())),
    };
    let len_ctor = Constructor {
        name: Name::from_string(TRUSTIR_XOPERAND_LEN),
        type_: Expr::pi(bd(), operand_ty(), xty.clone()),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![base_ctor, index_ctor, len_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.XOperand): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.evalXOperand : Env → XOperand → Int` (idempotent):
///
/// ```text
/// evalXOperand (e : Env) : XOperand → Int
///   | Base op  => evalOperand e op
///   | Index s i => idxElem (evalOperand e s) (evalOperand e i)
///   | Len s     => sliceLen (evalOperand e s)
/// ```
///
/// A non-dependent `XOperand.rec` fold reusing the flat `evalOperand`. Requires
/// `XOperand`/`evalOperand`/`idxElem`/`sliceLen`. No non-foundational axiom.
fn register_eval_xoperand(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_EVAL_XOPERAND);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), xoperand_ty(), int_ty()));
    let xop_rec =
        Expr::const_(Name::from_string(TRUSTIR_XOPERAND_REC), vec![Level::succ(Level::zero())]);
    let eval_op = cst(TRUSTIR_EVAL_OPERAND);
    let motive = Expr::lam(bd(), xoperand_ty(), int_ty());

    // Base case: λ(op:Operand). evalOperand e op — op=bvar(0), xop=bvar(1), e=bvar(2).
    let base_case =
        Expr::lam(bd(), operand_ty(), Expr::apps(eval_op.clone(), [Expr::bvar(2), Expr::bvar(0)]));
    // Index case: λ(s:Operand). λ(i:Operand). idxElem (evalOperand e s)(evalOperand e i)
    //   under s, i: i=bvar(0), s=bvar(1), xop=bvar(2), e=bvar(3).
    let index_case = {
        let e_ref = Expr::bvar(3);
        let eval_s = Expr::apps(eval_op.clone(), [e_ref.clone(), Expr::bvar(1)]);
        let eval_i = Expr::apps(eval_op.clone(), [e_ref, Expr::bvar(0)]);
        let body = Expr::apps(cst(TRUSTIR_IDX_ELEM), [eval_s, eval_i]);
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), body))
    };
    // Len case: λ(s:Operand). sliceLen (evalOperand e s) — s=bvar(0), xop=bvar(1), e=bvar(2).
    let len_case = {
        let eval_s = Expr::apps(eval_op.clone(), [Expr::bvar(2), Expr::bvar(0)]);
        Expr::lam(bd(), operand_ty(), Expr::app(cst(TRUSTIR_SLICE_LEN), eval_s))
    };
    // XOperand.rec.{1} motive base_case index_case len_case xop
    let rec_app = Expr::apps(xop_rec, [motive, base_case, index_case, len_case, Expr::bvar(0)]);
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), xoperand_ty(), rec_app));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(evalXOperand): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// LOOP COUNTER-REFINEMENT (the headline) — the Hoare while-rule INSTANTIATED at a
// concrete counter loop `while i < n { i := i + 1 }` with a GENUINE guard-derived
// invariant `i ≤ n`, kernel-checked modulo 3. MIRRORS the committed
// `mirsem::loop_instance_{conclusion_type,proof}` + `counter_le_bound_preservation_proof`
// — the proof RECONSTRUCTS the certified loop fact (the invariant survives every
// iteration of the back-edge), it is NOT `Eq.refl` of a def-eq tautology, and a wrong
// invariant / non-guard bound → KernelRejected.
// ---------------------------------------------------------------------------

/// The closed `Int` literal `1` in the EXACT shape `Int.lt`'s definitional `+1` uses —
/// IDENTICAL to `mirsem::int_one`, so the reduced preservation codomain `Int.le ((e i)+1)
/// (e n)` is def-eq to the guard fact `Int.lt (e i) (e n)`.
fn int_one() -> Expr {
    Expr::app(cst("Int.ofNat"), Expr::app(cst("Nat.succ"), cst("Nat.zero")))
}

/// `of_decide_eq_true : ∀ (p : Prop)(inst : Decidable p), decide p inst = true → p` — the
/// prelude-only term (axiom-free: `Decidable.rec` / `Bool.noConfusion` / `False.elim`)
/// that converts a `decide`-shaped guard `evalCond e (i<n) = true ≡ decide (Int.lt i n)
/// (Int.decLt i n) = true` into the proof `Int.lt i n`. BYTE-IDENTICAL to
/// `mirsem::of_decide_eq_true_term`.
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port
// (`trustir_termination.rs`) — its concrete decrease proofs extract the guard fact
// with this SAME term.
pub(crate) fn of_decide_eq_true_term() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let eq_bool = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), x, y],
        )
    };
    let decide = |p: Expr, inst: Expr| Expr::apps(cst("decide"), [p, inst]);

    // motive : λ (d : Decidable p). decide p d = Bool.true → p
    //   under `λ (p:Prop) λ (inst) λ (h) λ (d:Decidable p)`: d=0, h=1, inst=2, p=3.
    let motive = {
        let d_binder_ty = Expr::apps(cst("Decidable"), [Expr::bvar(2)]);
        let dec = decide(Expr::bvar(3), Expr::bvar(0));
        let dom = eq_bool(dec, cst("Bool.true"));
        Expr::lam(bd(), d_binder_ty, Expr::pi(bd(), dom, Expr::bvar(4)))
    };
    // isFalse minor : λ (hnp : p → False) λ (he : decide p (isFalse p hnp) = true). False.elim …
    //   under `λ p λ inst λ h λ hnp λ he`: he=0, hnp=1, h=2, inst=3, p=4.
    let is_false_minor = {
        let hnp_ty = Expr::pi(bd(), Expr::bvar(2), cst("False"));
        let isfalse = Expr::apps(cst("Decidable.isFalse"), [Expr::bvar(3), Expr::bvar(0)]);
        let he_ty = eq_bool(decide(Expr::bvar(3), isfalse), cst("Bool.true"));
        let no_conf = Expr::apps(
            Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
            [cst("False"), cst("Bool.false"), cst("Bool.true"), Expr::bvar(0)],
        );
        let felim = Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [Expr::bvar(4), no_conf],
        );
        Expr::lam(bd(), hnp_ty, Expr::lam(bd(), he_ty, felim))
    };
    // isTrue minor : λ (hp : p) λ (_he : decide p (isTrue p hp) = true). hp
    //   under `λ p λ inst λ h λ hp`: hp=0, h=1, inst=2, p=3.
    let is_true_minor = {
        let hp_ty = Expr::bvar(2);
        let istrue = Expr::apps(cst("Decidable.isTrue"), [Expr::bvar(3), Expr::bvar(0)]);
        let he_ty = eq_bool(decide(Expr::bvar(3), istrue), cst("Bool.true"));
        Expr::lam(bd(), hp_ty, Expr::lam(bd(), he_ty, Expr::bvar(1)))
    };
    // @Decidable.rec.{0} p motive isFalse isTrue inst : decide p inst = true → p
    //   under `λ p λ inst λ h`: h=0, inst=1, p=2.
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]),
        [Expr::bvar(2), motive, is_false_minor, is_true_minor, Expr::bvar(1)],
    );
    // body: (Decidable.rec … inst) h  : p   — under `λ p λ inst λ h`: h=0.
    let body = Expr::app(rec_app, Expr::bvar(0));
    let h_ty = eq_bool(decide(Expr::bvar(1), Expr::bvar(0)), cst("Bool.true"));
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(bd(), Expr::apps(cst("Decidable"), [Expr::bvar(0)]), Expr::lam(bd(), h_ty, body)),
    )
}

/// The PER-FUNCTION partial-correctness conclusion TYPE for this loop, with the invariant
/// instantiated: `∀ (n : Nat)(e : Env), I e → I (execLoop e cond body n)`. `claimed`
/// overrides the invariant (fail-closed hook). Mirrors `mirsem::loop_instance_conclusion_type`.
fn loop_instance_conclusion_type_ir(lp: &IrLoop, claimed: Option<&IrLoopInvariant>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(claimed);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();
    // ∀ (n:Nat)(e:Env), I e → I (execLoop e cond body n)
    //   inside `∀ n ∀ e`: e=0, n=1. `I e`: I lifted +2.
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    //   under one more arrow ⇒ e=1, n=2; I lifted +3.
    let looped =
        exec_loop_app_ir(Expr::bvar(1), cond_expr.lift(3), body_expr.lift(3), Expr::bvar(2));
    let i_loop = Expr::app(i_expr.lift(3), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    Expr::pi(bd(), cst("Nat"), body_e)
}

/// The GUARD-AWARE upper-bound preservation PROOF for `I := λ e. Int.le (e i) (e n)` over
/// the counter body `[i := i + 1]`:
/// `λ (e : Env)(_hI : I e)(hg : evalCond e cond = true).
///    of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg`.
///
/// The codomain `I (evalBody e body)` ι-reduces to `Int.le ((e i)+1) (e n)` (the body
/// assigns only `i := i+1`; `n` is untouched). The guard `evalCond e (i<n) = true`
/// ι-reduces to `decide (Int.lt (e i)(e n)) (Int.decLt …) = true`, so
/// `of_decide_eq_true … hg : Int.lt (e i)(e n)`, which is DEFINITIONALLY `Int.le ((e i)+1)
/// (e n)` — EXACTLY the reduced codomain. This GENUINELY re-establishes the bound from the
/// guard (the hypothesis is UNNEEDED). Mirrors `mirsem::counter_le_bound_preservation_proof`.
/// A WRONG bound index (one the guard does not mention) makes `Int.lt`'s `n` ≠ the codomain's
/// bound ⇒ NOT def-eq ⇒ ill-typed ⇒ KernelRejected.
fn counter_le_bound_preservation_proof_ir(lp: &IrLoop, i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ _hI`: _hI = 0, e = 1; the guard `evalCond e cond = true`.
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ _hI λ hg`: hg = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx));
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_b]);
    let proof = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The inductive LOWER-bound preservation PROOF for `I := λ e. Int.le c (e i)` over the
/// counter body `[i := i + 1]`:
/// `λ (e : Env)(hI : I e)(_hg : evalCond e cond = true).
///    Int.le_trans c (e i) ((e i)+1) hI (Int.le_self_add_one (e i))`.
///
/// The codomain `I (evalBody e body)` ι-reduces to `Int.le c ((e i)+1)`. The proof
/// GENUINELY USES the hypothesis `hI : c ≤ e i` (transitivity through `e i ≤ (e i)+1`),
/// NOT the guard. Mirrors `mirsem::counter_ge_const_preservation_proof`. A WRONG constant
/// (e.g. `1 ≤ i`, false at `i = 0`) makes `hI`'s type ≠ what `Int.le_trans` demands ⇒
/// KernelRejected.
fn counter_ge_const_preservation_proof_ir(lp: &IrLoop, i_idx: u64, c: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let c_lit = int_lit(c);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
    // Int.le_trans c (e i) ((e i)+1) hI (Int.le_self_add_one (e i)).
    let proof =
        Expr::apps(cst("Int.le_trans"), [c_lit, e_i, i_plus_one, Expr::bvar(1), self_le_succ]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

// ---------------------------------------------------------------------------
// LOOP-BREADTH increment — the OTHER MirSem loop classes' preservation proofs +
// the small arithmetic-core helper terms they rest on (built INLINE, mirroring the
// committed `mirsem.rs` proofs byte-for-byte: `countdown_ge_const_preservation_proof`,
// `stride_ge_const_preservation_proof` + `stride_self_le_term`,
// `counter_ge_const_preservation_proof` at the accumulator index, and
// `accum_eq_counter_preservation_proof`).
// ---------------------------------------------------------------------------

/// `@Int.add_le_add_right a b hab c : Int.le (Int.add a c) (Int.add b c)` — the
/// constructive (modulo-3) prelude monotone-add lemma, applied at the concrete args.
/// IDENTICAL to `mirsem::add_le_add_right`.
fn add_le_add_right_ir(a: Expr, b: Expr, hab: Expr, c: Expr) -> Expr {
    Expr::apps(cst("Int.add_le_add_right"), [a, b, hab, c])
}

/// The INLINE proof term `countdownGe0 i hlt : Int.le 0 (Int.sub i 1)` — "if `0 < i` then
/// `0 ≤ i - 1`". `hlt : Int.lt 0 i` is DEFINITIONALLY `Int.le (Int.add 0 1) i`, so it fits
/// `Int.add_le_add_right`'s `Int.le a b` premise at `a := 0+1`, `b := i`; adding `Int.neg 1`
/// on the right of both sides yields `Int.le ((0+1)+(-1)) (i+(-1))`. The LHS reduces to
/// `Int.ofNat 0` and `Int.add i (Int.neg 1)` is DEFINITIONALLY `Int.sub i 1`, so the result
/// is def-eq to `Int.le 0 (Int.sub i 1)`. Constructive (only `Int.add_le_add_right`, mod 3).
/// IDENTICAL arithmetic core to `mirsem::countdown_ge0_proof`, inlined at `i := e_i`.
fn countdown_ge0_inline(e_i: Expr, hlt: Expr) -> Expr {
    // a := Int.add 0 1  (= the unfolded `Int.lt 0 i` lhs `0+1`).
    let a = Expr::apps(cst("Int.add"), [int_lit(0), int_one()]);
    let neg_one = Expr::app(cst("Int.neg"), int_one());
    // Int.add_le_add_right (0+1) i hlt (neg 1) : Int.le ((0+1)+(-1)) (i+(-1)) ≡ Int.le 0 (i-1).
    add_le_add_right_ir(a, e_i, hlt, neg_one)
}

/// The INLINE proof term `strideSelfLe k x : Int.le x (Int.add x (int_lit k))` — "`x ≤ x+k`"
/// for a fixed positive stride `k ≥ 1`, transporting the stuck `Int.add x 0` LHS to `x`:
/// ```text
/// raw  := Int.add_le_add_left 0 (ofNat k) (Int.ofNat_zero_le k) x : Int.le (x+0) (x+k)
/// h0   := Int.add_zero x : Eq Int (Int.add x 0) x
/// out  := @Eq.subst Int (λ y. Int.le y (x+k)) (Int.add x 0) x h0 raw : Int.le x (x+k)
/// ```
/// IDENTICAL to `mirsem::stride_self_le_term`. Requires `Int.ofNat_zero_le` (provided by
/// `init_int_ord_lemmas` in `trustir_env`).
fn stride_self_le_ir(k: i128, x: Expr) -> Expr {
    debug_assert!(k >= 1, "stride must be a positive constant");
    let bd = || BinderData::from(BinderInfo::Default);
    let k_nat = Expr::nat_lit(u64::try_from(k).unwrap_or(0));
    let zero_le_k = Expr::app(cst("Int.ofNat_zero_le"), k_nat);
    let x_plus_0 = Expr::apps(cst("Int.add"), [x.clone(), int_lit(0)]);
    let x_plus_k = Expr::apps(cst("Int.add"), [x.clone(), int_lit(k)]);
    // raw : Int.le (x+0) (x+k).
    let raw =
        Expr::apps(cst("Int.add_le_add_left"), [int_lit(0), int_lit(k), zero_le_k, x.clone()]);
    // h0 : Eq Int (Int.add x 0) x.
    let h0 = Expr::app(cst("Int.add_zero"), x.clone());
    // motive : λ (y : Int). Int.le y (x+k)   (x+k lifted by 1 under `λ y`).
    let motive = Expr::lam(
        bd(),
        int_ty(),
        Expr::apps(cst("Int.le"), [Expr::bvar(0), x_plus_k.clone().lift(1)]),
    );
    // @Eq.subst Int motive (x+0) x h0 raw : Int.le x (x+k).
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), motive, x_plus_0, x, h0, raw],
    )
}

/// The GUARD-USING COUNTDOWN preservation PROOF for `I := λ e. Int.le 0 (e i)` (`0 ≤ i`,
/// canonical `c = 0`) over the body `[i := i - 1]`, under the guard `i > 0`:
/// `λ (e)(_hI)(hg). countdownGe0 (e i) (of_decide_eq_true (Int.lt 0 (e i)) (Int.decLt …) hg)`.
///
/// The codomain `I (evalBody e [i:=i-1])` ι-reduces to `Int.le 0 (Int.sub (e i) 1)`. The
/// `Gt` guard `evalCond e (i>0) = true` is the SWAPPED `decide (Int.lt 0 (e i)) … = true`, so
/// `of_decide_eq_true … hg : Int.lt 0 (e i)`, and `countdownGe0` re-establishes `0 ≤ i-1` from
/// it — EXACTLY the reduced codomain. The lower bound is re-derived from the GUARD (`_hI`
/// unneeded). Mirrors `mirsem::countdown_ge_const_preservation_proof`. FAIL-CLOSED: a non-zero
/// `c` (codomain `Int.le c (i-1)` ≠ what `countdownGe0` proves) or an INCREMENT body (codomain
/// `Int.le 0 (i+1)` ≠ `Int.le 0 (i-1)`) ⇒ KernelRejected.
fn countdown_ge_const_preservation_proof_ir(lp: &IrLoop, i_idx: u64, c: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ _hI λ hg`: hg = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let _ = c; // only c = 0 is sound; a non-zero c is rejected by the kernel (see doc).
    // Extract `Int.lt 0 (e i)` from the SWAPPED Gt guard `decide (Int.lt 0 (e i))`.
    let zero = int_lit(0);
    let p = Expr::apps(cst("Int.lt"), [zero.clone(), e_i.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [zero, e_i.clone()]);
    let hlt = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // : 0 < e i
    let proof = countdown_ge0_inline(e_i, hlt); // : Int.le 0 (Int.sub (e i) 1)
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The STRIDE preservation PROOF for `I := λ e. Int.le c (e i)` (`c ≤ i`) over the body
/// `[i := i + k]` (`k ≥ 1`):
/// `λ (e)(hI)(_hg). Int.le_trans c (e i) ((e i)+k) hI (strideSelfLe k (e i))`.
///
/// The codomain `I (evalBody e [i:=i+k])` ι-reduces to `Int.le c (Int.add (e i) k)`. From
/// the loop-carried `hI : Int.le c (e i)` and `strideSelfLe k (e i) : Int.le (e i) ((e i)+k)`
/// (`i ≤ i+k` for the concrete positive `k`), `Int.le_trans` chains to `Int.le c ((e i)+k)` —
/// EXACTLY the reduced codomain. `k = 1` recovers the counter lower bound. Mirrors
/// `mirsem::stride_ge_const_preservation_proof`. FAIL-CLOSED: a DECREMENT body's codomain
/// `Int.le c (i-k)` ≠ `Int.le c (i+k)`, and `strideSelfLe` is built per-`k` ⇒ KernelRejected.
fn stride_ge_const_preservation_proof_ir(lp: &IrLoop, i_idx: u64, c: i128, k: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let c_lit = int_lit(c);
    let i_plus_k = Expr::apps(cst("Int.add"), [e_i.clone(), int_lit(k)]); // i + k
    let self_le = stride_self_le_ir(k, e_i.clone()); // i ≤ i+k for this fixed k ≥ 1
    let proof = Expr::apps(cst("Int.le_trans"), [c_lit, e_i, i_plus_k, Expr::bvar(1), self_le]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The RELATIONAL ACCUMULATOR preservation PROOF for `I := λ e. (e s == e i) ∧ (e i ≤ e n)`
/// over the lockstep body `[s := s + 1; i := i + 1]` under the `Lt` guard:
/// `λ (e)(hI)(hg). And.intro <s+1==i+1> <i+1≤n>
///    (congrArg (·+1) (And.left … hI)) (of_decide_eq_true (Int.lt i n) (Int.decLt …) hg)`.
///
/// The codomain `I (evalBody e body)` ι-reduces to `And ((s+1)==(i+1)) (Int.le (i+1) n)` (`n`
/// untouched). LEFT: the `Int` congruence `@congrArg Int Int (e s)(e i) (λ x. x+1) (And.left …
/// hI)` — its output `(e s)+1 == (e i)+1` def-eq matches the reduced left conjunct, USING the
/// hypothesis. RIGHT: the guard-aware upper bound from the `Lt` guard (`of_decide_eq_true …
/// hg : Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n)`). Mirrors
/// `mirsem::accum_eq_counter_preservation_proof`. FAIL-CLOSED: a non-lockstep `s` update (`s
/// := s + δ`, δ ≠ 1) makes `congrArg`'s output NOT def-eq to the reduced codomain
/// `(e s)+δ == (e i)+1` ⇒ KernelRejected.
fn accum_eq_counter_preservation_proof_ir(lp: &IrLoop, s_idx: u64, i_idx: u64, n_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_s = Expr::app(Expr::bvar(2), Expr::nat_lit(s_idx));
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let e_n = Expr::app(Expr::bvar(2), Expr::nat_lit(n_idx));
    let s_plus_one = Expr::apps(cst("Int.add"), [e_s.clone(), int_one()]);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), a, b],
        )
    };
    // The two conjunct PROPS the reduced codomain `And A B` carries.
    let prop_eq = eq_of(s_plus_one, i_plus_one); // (s+1) == (i+1)
    let prop_hi = Expr::apps(
        cst("Int.le"),
        [Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]), e_n.clone()],
    ); // i+1 ≤ n
    // hI : And (@Eq Int (e s)(e i)) (Int.le (e i)(e n)). Project the conjuncts.
    let and_eq = eq_of(e_s.clone(), e_i.clone()); // s == i
    let and_hi = Expr::apps(cst("Int.le"), [e_i.clone(), e_n.clone()]); // i ≤ n
    let h_eq = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [and_eq, and_hi, Expr::bvar(1)],
    ); // And.left … hI : s == i
    // LEFT (RELATIONAL) proof: @congrArg Int Int (e s)(e i) (λ x. Int.add x 1) h_eq.
    let add_one_fn =
        Expr::lam(bd(), int_ty(), Expr::apps(cst("Int.add"), [Expr::bvar(0), int_one()]));
    let l1 = Level::succ(Level::zero());
    let proof_eq = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [int_ty(), int_ty(), e_s, e_i.clone(), add_one_fn, h_eq],
    );
    // RIGHT (guard) proof: of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg.
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_n]);
    let proof_hi = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    // And.intro A B proof_eq proof_hi : And A B.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_eq, prop_hi, proof_eq, proof_hi],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The `≤`-GUARDED CONJOINED-RANGE preservation PROOF for `I := λ e. (c ≤ e i) ∧ (e i ≤ (e
/// n)+1)` over the body `[i := i+1]` under the `Le` guard `i ≤ n` (the `count_le` shape).
/// `And.intro` of:
///  * (LOWER) `c ≤ i → c ≤ i+1` — `Int.le_trans c (e i) ((e i)+1) (And.left … hI)
///    (Int.le_self_add_one (e i))`, USES `And.left hI`; identical to the counter lower bound.
///  * (UPPER) `i ≤ n → i+1 ≤ n+1` — extract `i ≤ n` from the `Le` guard via `of_decide_eq_true`,
///    then `Int.add_le_add_right (e i)(e n) hg 1`, the SAME `Le`-guard monotone-add step.
/// The reduced codomain is `And (Int.le c ((e i)+1)) (Int.le ((e i)+1) ((e n)+1))`. FAIL-CLOSED:
/// a too-tight `i ≤ n` upper codomain (which the `Le` guard does NOT provide) would NOT retype.
/// Mirrors `mirsem::counter_in_range_succ_preservation_proof` byte-for-byte.
fn counter_in_range_succ_preservation_proof_ir(
    lp: &IrLoop,
    i_idx: u64,
    c: i128,
    bound_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx));
    let c_lit = int_lit(c);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let b_plus_one = Expr::apps(cst("Int.add"), [e_b.clone(), int_one()]);
    // The two conjunct PROPS the reduced codomain `And A B` carries.
    let prop_lo = Expr::apps(cst("Int.le"), [c_lit.clone(), i_plus_one.clone()]); // c ≤ i+1
    let prop_hi = Expr::apps(cst("Int.le"), [i_plus_one.clone(), b_plus_one]); // i+1 ≤ n+1
    // hI : And (c ≤ e i) (e i ≤ (e n)+1). Project the conjuncts.
    let and_lo = Expr::apps(cst("Int.le"), [c_lit.clone(), e_i.clone()]); // c ≤ i
    let and_hi_b1 = Expr::apps(cst("Int.add"), [e_b.clone(), int_one()]);
    let and_hi = Expr::apps(cst("Int.le"), [e_i.clone(), and_hi_b1]); // i ≤ n+1
    let h_lo = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [and_lo.clone(), and_hi.clone(), Expr::bvar(1)],
    ); // And.left … hI : c ≤ e i
    // LOWER conjunct: Int.le_trans c (e i) ((e i)+1) h_lo (Int.le_self_add_one (e i)).
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
    let proof_lo = Expr::apps(
        cst("Int.le_trans"),
        [c_lit, e_i.clone(), i_plus_one.clone(), h_lo, self_le_succ],
    );
    // UPPER conjunct: extract `i ≤ n` from the Le guard, then add 1 on both sides.
    let p = Expr::apps(cst("Int.le"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLe"), [e_i.clone(), e_b.clone()]);
    let hg = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // : i ≤ n
    let proof_hi = add_le_add_right_ir(e_i, e_b, hg, int_one()); // : i+1 ≤ n+1
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_lo, prop_hi, proof_lo, proof_hi],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The GENERAL RELATIONAL preservation PROOF for `I := λ e. (a₀ == i) ∧ … ∧ (aₘ == i) ∧ (i ≤ n)`
/// over the >2-local lockstep body `[a₀:=a₀+1; …; aₘ:=aₘ+1; i:=i+1]` under the `Lt` guard (the
/// `three`/`four`/`three_ret_b` shape). A NESTED right-folded `And.intro`: for EACH `aₖ == i` a
/// congruence step `aₖ == i → aₖ+1 == i+1` (`@congrArg Int Int (e aₖ)(e i)(λ x. x+1) (And.left …
/// hI)`, projected from the nested `And`), capped by the guard-aware upper bound `i+1 ≤ n` from
/// the `Lt` guard (`of_decide_eq_true`). The hypothesis `hI : (a₀==i) ∧ (… ∧ (i≤n))` is projected
/// by walking `And.left` after peeling `k` `And.right`s. FAIL-CLOSED: a non-lockstep `aₖ` update
/// makes that conjunct's reduced codomain NOT def-eq to `congrArg`'s output ⇒ KernelRejected.
/// Mirrors `mirsem::accum_eq_counter_set_preservation_proof` byte-for-byte.
fn accum_eq_counter_set_preservation_proof_ir(
    lp: &IrLoop,
    accum_idxs: &[u64],
    i_idx: u64,
    n_idx: u64,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_at = |idx: u64| Expr::app(Expr::bvar(2), Expr::nat_lit(idx));
    let e_i = e_at(i_idx);
    let e_n = e_at(n_idx);
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), a, b],
        )
    };
    let add_one_fn =
        || Expr::lam(bd(), int_ty(), Expr::apps(cst("Int.add"), [Expr::bvar(0), int_one()]));
    let l1 = || Level::succ(Level::zero());

    // suffix_prop[k] = And (aₖ==i) (And (a_{k+1}==i) (… (i≤n))) ; suffix_prop[n] = (i≤n).
    let cap_le = Expr::apps(cst("Int.le"), [e_i.clone(), e_n.clone()]); // i ≤ n
    let n = accum_idxs.len();
    let mut suffix_prop = vec![cap_le.clone(); n + 1];
    suffix_prop[n] = cap_le.clone();
    for k in (0..n).rev() {
        let eqk = eq_of(e_at(accum_idxs[k]), e_i.clone());
        suffix_prop[k] = Expr::apps(cst("And"), [eqk, suffix_prop[k + 1].clone()]);
    }
    // reduced_suffix[k] = And (aₖ+1==i+1) (… (i+1≤n)) ; reduced_suffix[n] = (i+1≤n).
    let cap_le_succ = Expr::apps(cst("Int.le"), [i_plus_one.clone(), e_n.clone()]); // i+1 ≤ n
    let mut reduced_suffix = vec![cap_le_succ.clone(); n + 1];
    reduced_suffix[n] = cap_le_succ.clone();
    for k in (0..n).rev() {
        let ak1 = Expr::apps(cst("Int.add"), [e_at(accum_idxs[k]), int_one()]);
        let eqk_succ = eq_of(ak1, i_plus_one.clone());
        reduced_suffix[k] = Expr::apps(cst("And"), [eqk_succ, reduced_suffix[k + 1].clone()]);
    }

    // Collect the LEFT congruence proofs in order, advancing `h_rest`.
    let mut h_rest = Expr::bvar(1); // : suffix_prop[0] (= hI)
    let mut left_proofs: Vec<(Expr, Expr)> = Vec::with_capacity(n); // (left_proof, left_prop)
    for k in 0..n {
        let eqk_prop = eq_of(e_at(accum_idxs[k]), e_i.clone()); // aₖ == i
        let rest_prop = suffix_prop[k + 1].clone();
        // hₖ = And.left (aₖ==i) rest_prop h_rest : aₖ == i
        let hk = Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [eqk_prop.clone(), rest_prop.clone(), h_rest.clone()],
        );
        // @congrArg Int Int (e aₖ)(e i)(λ x. x+1) hₖ : aₖ+1 == i+1.
        let proof_eqk = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
            [int_ty(), int_ty(), e_at(accum_idxs[k]), e_i.clone(), add_one_fn(), hk],
        );
        let ak1 = Expr::apps(cst("Int.add"), [e_at(accum_idxs[k]), int_one()]);
        let left_prop = eq_of(ak1, i_plus_one.clone()); // aₖ+1 == i+1
        left_proofs.push((proof_eqk, left_prop));
        // advance h_rest := And.right (aₖ==i) rest_prop h_rest : rest_prop
        h_rest = Expr::apps(
            Expr::const_(Name::from_string("And.right"), vec![]),
            [eqk_prop, rest_prop, h_rest],
        );
    }

    // CAP proof: of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg : i+1 ≤ n (def-eq).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i.clone(), e_n.clone()]);
    let mut proof = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    // Fold the congruence And.intros around the cap, innermost (aₘ) first.
    for k in (0..n).rev() {
        let (left_proof, left_prop) = &left_proofs[k];
        let right_prop = reduced_suffix[k + 1].clone();
        proof = Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [left_prop.clone(), right_prop, left_proof.clone(), proof],
        );
    }
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The preservation PROOF for this loop's invariant, dispatched on the invariant form.
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — the
// per-function `loopTotalCorrect` instance feeds the SAME preservation proof the
// partial-correctness witness certifies.
pub(crate) fn loop_instance_preservation_proof_ir(lp: &IrLoop) -> Expr {
    match &lp.inv {
        IrLoopInvariant::CounterLeBound { i_idx, bound_idx } => {
            counter_le_bound_preservation_proof_ir(lp, *i_idx, *bound_idx)
        }
        IrLoopInvariant::CounterGeConst { i_idx, c } => {
            counter_ge_const_preservation_proof_ir(lp, *i_idx, *c)
        }
        // LOOP-BREADTH increment — the OTHER MirSem loop classes.
        IrLoopInvariant::CountdownGeConst { i_idx, c } => {
            countdown_ge_const_preservation_proof_ir(lp, *i_idx, *c)
        }
        IrLoopInvariant::StrideGeConst { i_idx, c, k } => {
            stride_ge_const_preservation_proof_ir(lp, *i_idx, *c, *k)
        }
        // The accumulator lower bound `c ≤ s` is preserved by EXACTLY the same inductive step
        // as the counter lower bound (`Int.le_trans` + `Int.le_self_add_one`), built at the
        // ACCUMULATOR index `s_idx`: the `i := i+1` statement leaves `s_idx` untouched
        // (`Nat.beq i_idx s_idx ≡ false`), so the multi-statement body's net effect at `s_idx`
        // is `s + 1` and the codomain reduces to `Int.le c ((e s_idx)+1)`.
        IrLoopInvariant::AccumGeConst { s_idx, c } => {
            counter_ge_const_preservation_proof_ir(lp, *s_idx, *c)
        }
        IrLoopInvariant::AccumEqCounter { s_idx, i_idx, n_idx } => {
            accum_eq_counter_preservation_proof_ir(lp, *s_idx, *i_idx, *n_idx)
        }
        // §6 FALLBACK-9 RE-ANCHOR — the `≤`-guarded conjoined range `c ≤ i ∧ i ≤ n+1`.
        IrLoopInvariant::CounterInRangeSucc { i_idx, c, bound_idx } => {
            counter_in_range_succ_preservation_proof_ir(lp, *i_idx, *c, *bound_idx)
        }
        // §6 FALLBACK-9 RE-ANCHOR — the GENERAL RELATIONAL accumulator set `(⋀ₖ aₖ==i) ∧ i ≤ n`.
        IrLoopInvariant::AccumEqCounterSet { accum_idxs, i_idx, n_idx } => {
            accum_eq_counter_set_preservation_proof_ir(lp, accum_idxs, *i_idx, *n_idx)
        }
    }
}

/// The PER-FUNCTION partial-correctness PROOF — `loopInvariantRule` APPLIED to this loop's
/// closed `(I, cond, body, preservation)`. Type-checking this APPLICATION at the
/// conclusion type IS the per-function corollary: the GENERAL while-rule, instantiated
/// here, proves THIS counter loop's invariant survives every back-edge iteration. No new
/// induction — it reuses the kernel-checked general `loopInvariantRule`. Mirrors
/// `mirsem::loop_instance_proof`.
fn loop_instance_proof_ir(lp: &IrLoop) -> Expr {
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();
    let pres = loop_instance_preservation_proof_ir(lp);
    Expr::apps(cst(TRUSTIR_LOOP_INVARIANT_RULE), [i_expr, cond_expr, body_expr, pres])
}

/// Check the COUNTER-LOOP refinement instance against the real clean-kernel, modulo 3:
/// the trust-ir Hoare while-rule `loopInvariantRule` INSTANTIATED at this loop's concrete
/// invariant, guard, body, and a GENUINE guard-derived preservation proof. `ProvenModulo3`
/// means the trust-ir loop denotation's `loopInvariantRule` — applied here — proves the
/// invariant survives every iteration of the back-edge `execLoop` fixpoint, kernel-verified
/// modulo 3. The fixpoint reconstructs the certified loop fact (it is NOT `Eq.refl` of a
/// tautology — the `succ`-case proof USES the induction hypothesis at the stepped env, and
/// the preservation USES the guard). Fail-closed for a wrong invariant.
#[must_use]
pub fn check_loop_invariant_instance(lp: &IrLoop) -> RefinementVerdict {
    check_loop_invariant_instance_inner(lp, None)
}

fn check_loop_invariant_instance_inner(
    lp: &IrLoop,
    claimed: Option<&IrLoopInvariant>,
) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = loop_instance_conclusion_type_ir(lp, claimed);
    let proof = loop_instance_proof_ir(lp);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("loop instance check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.loop_instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loop instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("loop instance decl not found".to_string()),
    }
}

/// The source postcondition shape a trust-ir loop's CERTIFIED invariant discharges at the
/// halting state — the trust-ir analogue of `mirsem::LoopPostcondition`, additionally
/// carrying the env index the return reads (`read_idx`, the SAME local the §6 via-trustir
/// gate's return-reads clause checks). Fail-closed: an `(invariant, post)` pair the
/// projection does not cover is `KernelRejected`, never silently accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrLoopPost {
    /// `ret ≤ n` — the value at `read_idx` at the halting state is ≤ the bound at
    /// `bound_idx` (discharged by a guard-aware upper conjunct `i ≤ n`, or relationally
    /// via `a == i ∧ i ≤ n`).
    RetLeBound { read_idx: u64, bound_idx: u64 },
    /// `ret ≤ n + 1` — the `≤`-guarded variant (the `count_le` shape), discharged by the
    /// conjoined-range upper conjunct `i ≤ n+1`.
    RetLeBoundSucc { read_idx: u64, bound_idx: u64 },
    /// `c ≤ ret` — discharged by an inductive lower-bound conjunct `c ≤ x` at `read_idx`.
    ConstLeRet { read_idx: u64, c: i128 },
}

/// Kernel-check (modulo 3) that this loop's TRUST-IR-CERTIFIED invariant DISCHARGES the
/// source postcondition `post` at the loop's halting state. The theorem proved is
///
///   `∀ (fuel : Nat)(e : Env), I e → P (execLoop e cond body fuel)`
///
/// — the postcondition-relevant conjunct `P` of the invariant holds at EVERY fuel point of
/// the trust-ir `execLoop` fixpoint (in particular whatever fuel the loop halts at),
/// starting from any invariant-satisfying entry env. The proof COMPOSES the SAME
/// instantiated while-rule the PRIMARY witness certifies — `loopInvariantRule I cond body
/// pres fuel e hI : I (execLoop e cond body fuel)`, with the SAME genuine guard-derived
/// preservation proof — with pure `And.left`/`And.right` conjunct projections (plus
/// `Eq.subst` for the relational classes). No new induction; a wrong invariant or
/// preservation is KernelRejected here exactly as in the invariant instance.
///
/// This is the trust-ir RELOCATION of `mirsem::check_loop_postcondition_instance` — the
/// postcondition-discharge clause the §6 via-trustir gate consumes, now keyed to the
/// trust-ir denotation (`Trust.TrustIr.execLoop`), NOT `Trust.MirSem.exec_loop`. HONEST
/// DELTA vs the MirSem discharge: that one is stated at the SYNTHESIZED-RANKING halting
/// fuel `R e` and composes `loopTotalCorrect` (partial correctness AND termination); this
/// one universally quantifies the fuel — PARTIAL correctness, covering the halting fuel
/// but NOT itself proving termination. Termination for the fully-faithful verdict is still
/// carried by the MirSem outer gate's `loop_total_correct_witness` (the acknowledged
/// MirSem residue; a trust-ir ranking/total-correctness theory is the named follow-up).
///
/// Fail-closed: a postcondition whose `read_idx`/bound/constant does not match the
/// certified invariant's conjunct is rejected BEFORE the kernel (unlisted pair) or BY the
/// kernel (ill-typed projection); a non-empty axiom residue is never `ProvenModulo3`.
#[must_use]
pub fn check_loop_postcondition_instance(lp: &IrLoop, post: IrLoopPost) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let bd = || BinderData::from(BinderInfo::Default);
    let l1 = || Level::succ(Level::zero());
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();

    // Under the proof's `λ (fuel:Nat) λ (e:Env) λ (hI : I e)`: hI = 0, e = 1, fuel = 2.
    // (The conclusion TYPE's third `Pi` binder sits at the SAME depth, so `concl_prop`
    // reads identically in both contexts — exactly as in the MirSem discharge.)
    let halt = exec_loop_app_ir(
        Expr::bvar(1),
        cond_expr.clone().lift(3),
        body_expr.clone().lift(3),
        Expr::bvar(2),
    );
    let halt_at = |idx: u64| Expr::app(halt.clone(), Expr::nat_lit(idx));
    let le = |a: Expr, b: Expr| Expr::apps(cst("Int.le"), [a, b]);
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1()]), [int_ty(), a, b])
    };
    let and_proj = |left: bool, lo: &Expr, hi: &Expr, h: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string(if left { "And.left" } else { "And.right" }), vec![]),
            [lo.clone(), hi.clone(), h],
        )
    };

    // `I halt` — the SAME instantiated while-rule the PRIMARY witness certifies, applied
    // at the quantified fuel/env/hypothesis.
    let pres = loop_instance_preservation_proof_ir(lp);
    let i_halt_proof = Expr::apps(
        cst(TRUSTIR_LOOP_INVARIANT_RULE),
        [
            i_expr.clone().lift(3),
            cond_expr.clone().lift(3),
            body_expr.clone().lift(3),
            pres.lift(3),
            Expr::bvar(2),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );

    // The postcondition Prop `P halt` + the projection PROOF from `I halt`, dispatched on
    // the (certified invariant, postcondition) pair. Every unlisted pair fails closed.
    let (concl_prop, proof_body) = match (&lp.inv, post) {
        // IDENTITY — the guard-aware upper bound IS the postcondition (`ret ≤ n`).
        (
            IrLoopInvariant::CounterLeBound { i_idx, bound_idx },
            IrLoopPost::RetLeBound { read_idx, bound_idx: pb },
        ) if read_idx == *i_idx && pb == *bound_idx => {
            (le(halt_at(*i_idx), halt_at(*bound_idx)), i_halt_proof)
        }
        // A non-positive stride has no positive-stride preservation proof — decline
        // BEFORE the proof builder (whose stride_self_le_ir debug_asserts k ≥ 1;
        // release builds fail closed in the kernel, but the pub entry point must
        // not panic in debug builds either).
        (IrLoopInvariant::StrideGeConst { k, .. }, _) if *k < 1 => {
            return RefinementVerdict::KernelRejected(
                "stride postcondition discharge requires a positive stride k ≥ 1".to_string(),
            );
        }
        // IDENTITY — the inductive lower bound IS the postcondition (`c ≤ ret`), at the
        // counter (counter/countdown/stride) index.
        (
            IrLoopInvariant::CounterGeConst { i_idx, c }
            | IrLoopInvariant::CountdownGeConst { i_idx, c }
            | IrLoopInvariant::StrideGeConst { i_idx, c, .. },
            IrLoopPost::ConstLeRet { read_idx, c: pc },
        ) if read_idx == *i_idx && pc == *c => (le(int_lit(*c), halt_at(*i_idx)), i_halt_proof),
        // IDENTITY — the accumulator lower bound at the ACCUMULATOR index.
        (
            IrLoopInvariant::AccumGeConst { s_idx, c },
            IrLoopPost::ConstLeRet { read_idx, c: pc },
        ) if read_idx == *s_idx && pc == *c => (le(int_lit(*c), halt_at(*s_idx)), i_halt_proof),
        // `≤`-GUARDED CONJOINED RANGE `c ≤ i ∧ i ≤ n+1` — project the conjunct the
        // postcondition consumes (`And.right` for `ret ≤ n+1`, `And.left` for `c ≤ ret`).
        (
            IrLoopInvariant::CounterInRangeSucc { i_idx, c, bound_idx },
            IrLoopPost::RetLeBoundSucc { read_idx, bound_idx: pb },
        ) if read_idx == *i_idx && pb == *bound_idx => {
            let conj_lo = le(int_lit(*c), halt_at(*i_idx));
            let conj_hi =
                le(halt_at(*i_idx), Expr::apps(cst("Int.add"), [halt_at(*bound_idx), int_one()]));
            (conj_hi.clone(), and_proj(false, &conj_lo, &conj_hi, i_halt_proof))
        }
        (
            IrLoopInvariant::CounterInRangeSucc { i_idx, c, bound_idx },
            IrLoopPost::ConstLeRet { read_idx, c: pc },
        ) if read_idx == *i_idx && pc == *c => {
            let conj_lo = le(int_lit(*c), halt_at(*i_idx));
            let conj_hi =
                le(halt_at(*i_idx), Expr::apps(cst("Int.add"), [halt_at(*bound_idx), int_one()]));
            (conj_lo.clone(), and_proj(true, &conj_lo, &conj_hi, i_halt_proof))
        }
        // RELATIONAL `s == i ∧ i ≤ n` — `ret ≤ n` at the ACCUMULATOR: project both
        // conjuncts, then `Eq.subst` `i ≤ n` along `i = s` to the goal `s ≤ n`. GENUINELY
        // USES the relational conjunct (the subst is impossible without `s == i`).
        (
            IrLoopInvariant::AccumEqCounter { s_idx, i_idx, n_idx },
            IrLoopPost::RetLeBound { read_idx, bound_idx: pb },
        ) if read_idx == *s_idx && pb == *n_idx => {
            let halt_s = halt_at(*s_idx);
            let halt_i = halt_at(*i_idx);
            let halt_n = halt_at(*n_idx);
            let conj_eq = eq_of(halt_s.clone(), halt_i.clone());
            let conj_le = le(halt_i.clone(), halt_n.clone());
            let h_eq = and_proj(true, &conj_eq, &conj_le, i_halt_proof.clone());
            let h_le = and_proj(false, &conj_eq, &conj_le, i_halt_proof);
            let h_eq_sym = Expr::apps(
                Expr::const_(Name::from_string("Eq.symm"), vec![l1()]),
                [int_ty(), halt_s.clone(), halt_i.clone(), h_eq],
            );
            let motive = Expr::lam(bd(), int_ty(), le(Expr::bvar(0), halt_n.clone().lift(1)));
            let proof_body = Expr::apps(
                Expr::const_(Name::from_string("Eq.subst"), vec![l1()]),
                [int_ty(), motive, halt_i, halt_s.clone(), h_eq_sym, h_le],
            );
            (le(halt_s, halt_n), proof_body)
        }
        // GENERAL RELATIONAL SET `(⋀ₖ aₖ==i) ∧ i ≤ n` — `ret ≤ n` at the RETURNED
        // accumulator: walk `And.right` to its conjunct, project it, then `Eq.subst` the
        // cap `i ≤ n` along `i = a_ret`. Mirrors the MirSem general relational discharge.
        (
            IrLoopInvariant::AccumEqCounterSet { accum_idxs, i_idx, n_idx },
            IrLoopPost::RetLeBound { read_idx, bound_idx: pb },
        ) if pb == *n_idx && accum_idxs.contains(&read_idx) => {
            let ret_pos = accum_idxs
                .iter()
                .position(|&a| a == read_idx)
                .expect("guarded by accum_idxs.contains");
            let halt_i = halt_at(*i_idx);
            let halt_n = halt_at(*n_idx);
            let halt_a_ret = halt_at(read_idx);
            // Reconstruct the nested `And` exactly as `invariant_expr` builds it (at halt),
            // so the projectors are fully applied.
            let cap_le = le(halt_i.clone(), halt_n.clone());
            let m = accum_idxs.len();
            let mut suffix_prop = vec![cap_le.clone(); m + 1];
            suffix_prop[m] = cap_le;
            for k in (0..m).rev() {
                let eqk = eq_of(halt_at(accum_idxs[k]), halt_i.clone());
                suffix_prop[k] = Expr::apps(cst("And"), [eqk, suffix_prop[k + 1].clone()]);
            }
            // h_eq_ret : halt a_ret == halt i — walk `ret_pos` `And.right`s, then `And.left`.
            let mut h_walk = i_halt_proof.clone();
            for k in 0..ret_pos {
                let eqk_prop = eq_of(halt_at(accum_idxs[k]), halt_i.clone());
                h_walk = and_proj(false, &eqk_prop, &suffix_prop[k + 1], h_walk);
            }
            let eq_ret_prop = eq_of(halt_a_ret.clone(), halt_i.clone());
            let h_eq_ret = and_proj(true, &eq_ret_prop, &suffix_prop[ret_pos + 1], h_walk);
            // h_le : halt i ≤ halt n — walk ALL `m` `And.right`s from the same base.
            let mut h_rest = i_halt_proof;
            for k in 0..m {
                let eqk_prop = eq_of(halt_at(accum_idxs[k]), halt_i.clone());
                h_rest = and_proj(false, &eqk_prop, &suffix_prop[k + 1], h_rest);
            }
            let h_eq_sym = Expr::apps(
                Expr::const_(Name::from_string("Eq.symm"), vec![l1()]),
                [int_ty(), halt_a_ret.clone(), halt_i.clone(), h_eq_ret],
            );
            let motive = Expr::lam(bd(), int_ty(), le(Expr::bvar(0), halt_n.clone().lift(1)));
            let proof_body = Expr::apps(
                Expr::const_(Name::from_string("Eq.subst"), vec![l1()]),
                [int_ty(), motive, halt_i, halt_a_ret.clone(), h_eq_sym, h_rest],
            );
            (le(halt_a_ret, halt_n), proof_body)
        }
        // Every other (invariant, postcondition) pair fails closed.
        (inv, post) => {
            return RefinementVerdict::KernelRejected(format!(
                "postcondition {post:?} does not match the trust-ir-certified invariant \
                 conjunct of {inv:?}"
            ));
        }
    };

    // Conclusion TYPE: ∀ (fuel:Nat)(e:Env), I e → P (execLoop e cond body fuel).
    //   inside `∀ fuel ∀ e`: e=0, fuel=1; `I e` lifts I by +2.
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    let concl_ty =
        Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, concl_prop)));
    // PROOF: λ (fuel:Nat) λ (e:Env) λ (hI : I e). proof_body.
    let i_e_dom = Expr::app(i_expr.lift(2), Expr::bvar(0));
    let proof = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_dom, proof_body)),
    );

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "loop postcondition instance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.loop_postcondition_instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!(
            "add loop postcondition instance: {e:?}"
        ));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "loop postcondition instance decl not found".to_string(),
        ),
    }
}

/// The canonical `count_to` counter loop `i := 0; while i < n { i := i + 1 }; ret i`
/// over env indices `i = 3`, `n = 1` (the guard `i < n` is `Lt (Var 3) (Var 1)`, the body
/// `i := i + 1` is `Assign 3 (Bin Add (Var 3) (Const 1))`), carrying the GUARD-AWARE upper
/// bound `I := λ e. Int.le (e 3) (e 1)` (`i ≤ n`) — the postcondition `ret ≤ n` consumes at
/// exit (`ret = i`, and at the halting state `i ≤ n`). The same shape `mirsem`'s
/// `loop_keep_zero_synth_le_n` certifies.
fn example_count_to_loop() -> IrLoop {
    IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![IrStmt {
            idx: 3,
            rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
        }],
        inv: IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 1 },
    }
}

/// The canonical `countdown` loop `while i > 0 { i := i - 1 }` over env index `i = 3`
/// (guard `Gt (Var 3) (Const 0)`, body `Assign 3 (Bin Sub (Var 3) (Const 1))`), carrying the
/// inductive lower bound `I := λ e. Int.le 0 (e 3)` (`0 ≤ i`). The same shape `mirsem`'s
/// `loop_countdown_function` certifies (`SynthInvariant::CountdownGeConst { i_idx: 3, c: 0 }`).
fn example_countdown_loop() -> IrLoop {
    IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(3), b: IrOperand::Const(0) },
        body: vec![IrStmt {
            idx: 3,
            rvalue: IrRvalue::Bin(TrustIrBinOp::Sub, IrOperand::Var(3), IrOperand::Const(1)),
        }],
        inv: IrLoopInvariant::CountdownGeConst { i_idx: 3, c: 0 },
    }
}

/// The canonical `stride` loop `while i < n { i := i + k }` over env indices `i = 3`,
/// `n = 1`, stride `k` (guard `Lt (Var 3) (Var 1)`, body `Assign 3 (Bin Add (Var 3) (Const
/// k))`), carrying the lower bound `I := λ e. Int.le 0 (e 3)` (`0 ≤ i`). The same shape
/// `mirsem`'s `loop_stride_function(k)` certifies (`SynthInvariant::StrideGeConst`).
fn example_stride_loop(k: i128) -> IrLoop {
    IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![IrStmt {
            idx: 3,
            rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(k)),
        }],
        inv: IrLoopInvariant::StrideGeConst { i_idx: 3, c: 0, k },
    }
}

/// The canonical `accumulator` loop `while i < n { s := s + 1; i := i + 1 }` with a
/// MULTI-statement body over env indices counter `i = 3`, accumulator `s = 4`, bound `n = 1`
/// (guard `Lt (Var 3) (Var 1)`, body `[Assign 4 (Add (Var 4) (Const 1)); Assign 3 (Add (Var
/// 3) (Const 1))]`). `inv` selects the lower bound `0 ≤ s` (`AccumGeConst`) or the relational
/// `s == i ∧ i ≤ n` (`AccumEqCounter`). The same shape `mirsem`'s `loop_accum_function`
/// certifies. The body is `[s:=s+1; i:=i+1]`: the `i:=i+1` statement leaves `s_idx` untouched.
#[cfg(test)]
fn example_accum_loop(inv: IrLoopInvariant) -> IrLoop {
    IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![
            // s := s + 1
            IrStmt {
                idx: 4,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(1)),
            },
            // i := i + 1
            IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
            },
        ],
        inv,
    }
}

/// FAIL-CLOSED probe for the counter-loop refinement: claim the upper bound `i ≤ m` for a
/// bound index `m` the guard `i < n` does NOT mention. The guard yields `Int.lt (e i)(e n)
/// ≡ Int.le ((e i)+1)(e n)`, but the claimed codomain demands `Int.le ((e i)+1)(e m)`
/// (m ≠ n) — NOT def-eq ⇒ the `of_decide_eq_true` proof is ill-typed ⇒ KernelRejected.
/// Returns `true` IFF rejected (the sound outcome) — proving the counter-loop refinement is
/// GENUINE, not `Eq.refl` of a def-eq tautology. (The honest preservation proof is built for
/// the TRUE bound `n`; checked against the wrong-bound conclusion it does not match.)
#[must_use]
pub fn trustir_loop_refinement_fail_closed() -> bool {
    let lp = example_count_to_loop();
    // The wrong invariant: `i ≤ r` where `r = 2` is NOT the guard's bound (`n = 1`).
    let wrong = IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 2 };
    // Build the conclusion AT the wrong invariant, but feed the HONEST proof (built for the
    // true `n`-bound preservation). The kernel must reject the mismatch.
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(_) => return false,
    };
    let concl_ty = loop_instance_conclusion_type_ir(&lp, Some(&wrong));
    let proof = loop_instance_proof_ir(&lp);
    let tc = TypeChecker::new(&env);
    if tc.check_type(&proof, &concl_ty).is_err() {
        return true; // rejected at type-check — fail-closed
    }
    // If it somehow type-checked, registering must still not yield a sound modulo-3 cert.
    drop(tc);
    let name = Name::from_string("Trust.TrustIr.Refinement.loop_wrong");
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    })
    .is_err()
}

/// FAIL-CLOSED probe for the COUNTDOWN refinement: claim the NON-ZERO lower bound `1 ≤ i`
/// (false at the terminal `i = 0`). The reduced codomain is `Int.le 1 (i - 1)`, but the
/// inline `countdownGe0` only proves `Int.le 0 (i - 1)` ⇒ the proof retypes against `0 ≤ i-1`,
/// NOT `1 ≤ i-1` ⇒ KernelRejected. Returns `true` IFF rejected (the sound outcome) — the
/// countdown lower bound is GENUINELY re-derived from the guard at `c = 0`, not a tautology.
#[must_use]
pub fn trustir_countdown_refinement_fail_closed() -> bool {
    let lp = IrLoop {
        inv: IrLoopInvariant::CountdownGeConst { i_idx: 3, c: 1 },
        ..example_countdown_loop()
    };
    matches!(check_loop_invariant_instance(&lp), RefinementVerdict::KernelRejected(_))
}

/// FAIL-CLOSED probe for the STRIDE refinement: claim a stride `k = 3` invariant on a loop
/// whose body actually strides `k = 1` (`i := i + 1`). The preservation proof builds
/// `strideSelfLe 3 (e i) : Int.le (e i) ((e i)+3)` and `Int.le_trans` to the codomain `Int.le
/// 0 ((e i)+3)`, but the body's reduced codomain is `Int.le 0 ((e i)+1)` (`+1` ≠ `+3`) ⇒ NOT
/// def-eq ⇒ KernelRejected. Returns `true` IFF rejected — the stride proof is built per-`k`
/// and only retypes for the ACTUAL stride.
#[must_use]
pub fn trustir_stride_refinement_fail_closed() -> bool {
    let lp = IrLoop {
        // Body strides +1, but the invariant claims a +3 stride.
        inv: IrLoopInvariant::StrideGeConst { i_idx: 3, c: 0, k: 3 },
        ..example_stride_loop(1)
    };
    matches!(check_loop_invariant_instance(&lp), RefinementVerdict::KernelRejected(_))
}

/// FAIL-CLOSED probe for the RELATIONAL ACCUMULATOR refinement: claim the lockstep relation
/// `s == i` on a loop whose accumulator body is NON-lockstep (`s := s + 2`). The `congrArg
/// (·+1)` step proves `(e s)+1 == (e i)+1`, but the body's reduced codomain is `(e s)+2 ==
/// (e i)+1` (`+2` ≠ `+1`) ⇒ NOT def-eq ⇒ KernelRejected. Returns `true` IFF rejected — the
/// relational invariant GENUINELY tracks the lockstep step (a non-lockstep update breaks it).
#[must_use]
pub fn trustir_accum_eq_refinement_fail_closed() -> bool {
    // The lockstep relation `s == i ∧ i ≤ n`, but the body bumps `s` by 2 (non-lockstep).
    let lp = IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![
            // s := s + 2  (NON-lockstep — breaks `s == i`)
            IrStmt {
                idx: 4,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(2)),
            },
            // i := i + 1
            IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
            },
        ],
        inv: IrLoopInvariant::AccumEqCounter { s_idx: 4, i_idx: 3, n_idx: 1 },
    };
    matches!(check_loop_invariant_instance(&lp), RefinementVerdict::KernelRejected(_))
}

/// The canonical `count_le` `≤`-guarded counter loop `while i ≤ n { i := i + 1 }` over env
/// indices `i = 3`, `n = 1` (guard `Le (Var 3) (Var 1)`, body `Assign 3 (Bin Add (Var 3) (Const
/// 1))`), carrying the CONJOINED range `I := λ e. (0 ≤ i) ∧ (i ≤ n+1)` (`CounterInRangeSucc`). The
/// same shape `mirsem`'s `loop_count_le_function` certifies.
fn example_count_le_loop(inv: IrLoopInvariant) -> IrLoop {
    IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Le, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![IrStmt {
            idx: 3,
            rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
        }],
        inv,
    }
}

/// The canonical `three` >2-local lockstep loop `while i < n { a:=a+1; b:=b+1; i:=i+1 }` over env
/// indices `a = 4`, `b = 5`, `i = 3`, `n = 1`, carrying the GENERAL RELATIONAL set `I := λ e. (a
/// == i) ∧ (b == i) ∧ (i ≤ n)` (`AccumEqCounterSet { accum_idxs: [4,5], i:3, n:1 }`). The same
/// shape `mirsem`'s `loop_three_function` certifies.
#[cfg(test)]
fn example_three_loop(inv: IrLoopInvariant) -> IrLoop {
    IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![
            IrStmt {
                idx: 4,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(1)),
            },
            IrStmt {
                idx: 5,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(5), IrOperand::Const(1)),
            },
            IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
            },
        ],
        inv,
    }
}

/// FAIL-CLOSED probe for the `≤`-GUARDED CONJOINED-RANGE refinement: claim the too-tight UPPER
/// bound `i ≤ n` (NOT `i ≤ n+1`) on a `≤`-guarded loop. After the last iteration (`i = n`) the
/// body makes `i = n+1`, so the reduced UPPER codomain `Int.le (i+1) n` is NOT what the `Le`
/// guard's `Int.add_le_add_right` proof establishes (it proves `i+1 ≤ n+1`) ⇒ NOT def-eq ⇒
/// KernelRejected. Returns `true` IFF rejected (the sound outcome) — the `i ≤ n+1` bound is the
/// GENUINELY-correct one a `≤` guard re-establishes, not `i ≤ n`.
#[must_use]
pub fn trustir_counter_in_range_succ_refinement_fail_closed() -> bool {
    // The WRONG too-tight upper bound: project `CounterInRange { i ≤ n }` onto a `≤`-guarded loop.
    let wrong = IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 1 };
    let lp =
        example_count_le_loop(IrLoopInvariant::CounterInRangeSucc { i_idx: 3, c: 0, bound_idx: 1 });
    // Build the conclusion AT the wrong (too-tight) invariant, feed the HONEST `i ≤ n+1` proof.
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(_) => return false,
    };
    let concl_ty = loop_instance_conclusion_type_ir(&lp, Some(&wrong));
    let proof = loop_instance_proof_ir(&lp);
    let tc = TypeChecker::new(&env);
    if tc.check_type(&proof, &concl_ty).is_err() {
        return true; // rejected at type-check — fail-closed
    }
    drop(tc);
    let name = Name::from_string("Trust.TrustIr.Refinement.count_le_wrong");
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    })
    .is_err()
}

/// FAIL-CLOSED probe for the GENERAL RELATIONAL ACCUMULATOR-SET refinement: claim the lockstep
/// set `a == i ∧ b == i` on a loop whose SECOND accumulator `b` is NON-lockstep (`b := b + 2`).
/// The `congrArg (·+1)` step for `b` proves `(e b)+1 == (e i)+1`, but the body's reduced codomain
/// at `b` is `(e b)+2 == (e i)+1` (`+2` ≠ `+1`) ⇒ NOT def-eq ⇒ KernelRejected. Returns `true` IFF
/// rejected — the general relational invariant GENUINELY tracks EVERY accumulator's lockstep step
/// (a single non-lockstep update among the set breaks it).
#[must_use]
pub fn trustir_accum_eq_counter_set_refinement_fail_closed() -> bool {
    let lp = IrLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        body: vec![
            IrStmt {
                idx: 4,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(1)),
            },
            // b := b + 2  (NON-lockstep — breaks `b == i`)
            IrStmt {
                idx: 5,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(5), IrOperand::Const(2)),
            },
            IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
            },
        ],
        inv: IrLoopInvariant::AccumEqCounterSet { accum_idxs: vec![4, 5], i_idx: 3, n_idx: 1 },
    };
    matches!(check_loop_invariant_instance(&lp), RefinementVerdict::KernelRejected(_))
}

// ---------------------------------------------------------------------------
// BREAK / EARLY-EXIT loop REFINEMENT — `loopInvariantRuleBrk` INSTANTIATED at a concrete
// early-exit counter loop `while i < n { if brk { break } i := i + 1 }`, invariant `i ≤ n`,
// kernel-checked modulo 3. MIRRORS the committed `mirsem::{break_le_bound_preservation_proof,
// break_loop_conclusion_type, break_loop_proof, check_break_loop_instance}` (renamed `check_trustir_break_loop_instance` to avoid the MirSem export collision).
// ---------------------------------------------------------------------------

/// The break PRESERVATION PROOF for the synthesized upper-bound invariant `I := λ e. e[i] ≤
/// e[n]` under the COMBINED guard `cond ∧ ¬brk`:
/// `λ (e)(_hI)(hcomb). of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …)
///    (andLeftTrue (evalCond e cond) (Bool.not (evalCond e brk)) hcomb)`.
///
/// `andLeftTrue` projects `evalCond e cond = true` out of the combined guard, and then the
/// proof is IDENTICAL to the non-break `CounterLeBound` proof: `of_decide_eq_true` turns
/// `evalCond e (i<n) = true` into `Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n)` — EXACTLY the
/// reduced codomain `I (evalBody e [i:=i+1])`. The break-condition's truth (the RIGHT
/// component) is genuinely UNNEEDED for `i ≤ n`. Mirrors `mirsem::break_le_bound_preservation_proof`.
/// FAIL-CLOSED: a WRONG bound (one the guard does not mention) makes the codomain differ ⇒
/// `of_decide_eq_true` does not retype ⇒ KernelRejected.
fn break_le_bound_preservation_proof_ir(blp: &IrBreakLoop, i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = blp.invariant_expr(None);
    let cond_expr = blp.cond_expr();
    let brk_expr = blp.brk_expr();
    // inside `λ e`: e = 0; `I e` for the hypothesis binder.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ _hI`: _hI = 0, e = 1; the COMBINED guard `(cond ∧ ¬brk) = true`.
    let comb = combined_brk_guard_ir(
        &Expr::bvar(1),
        &cond_expr.clone().lift(2),
        &brk_expr.clone().lift(2),
    );
    let comb_eq = eq_bool_true(comb);
    // inside `λ e λ _hI λ hcomb`: hcomb = 0, _hI = 1, e = 2.
    let e_i = Expr::app(Expr::bvar(2), Expr::nat_lit(i_idx));
    let e_b = Expr::app(Expr::bvar(2), Expr::nat_lit(bound_idx));
    // The two Bool components of the combined guard at this depth.
    let g_cond = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(2), cond_expr.lift(3)]);
    let g_brk = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(2), brk_expr.lift(3)]);
    let not_brk = Expr::app(cst("Bool.not"), g_brk);
    // hg := andLeftTrue (evalCond e cond) (Bool.not (evalCond e brk)) hcomb : evalCond e cond = true.
    let hg = and_left_true_app_ir(g_cond, not_brk, Expr::bvar(0));
    // of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg : Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n).
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_b.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_b]);
    let proof = Expr::apps(of_decide_eq_true_term(), [p, inst, hg]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), comb_eq, proof)))
}

/// The break preservation PROOF for this loop, dispatched on the invariant form (today only
/// the guard-aware upper bound `CounterLeBound` is wired for the break shape).
fn break_loop_preservation_proof_ir(blp: &IrBreakLoop) -> Expr {
    match blp.inv {
        IrLoopInvariant::CounterLeBound { i_idx, bound_idx } => {
            break_le_bound_preservation_proof_ir(blp, i_idx, bound_idx)
        }
        // Other invariant forms are DEFERRED for the break shape; build the upper-bound proof
        // anyway so the kernel rejects (fail-closed) rather than silently accepting.
        _ => break_le_bound_preservation_proof_ir(blp, 0, 0),
    }
}

/// The PER-FUNCTION break-loop CONCLUSION TYPE — `loopInvariantRuleBrk` SPECIALIZED at this
/// loop's `(I, cond, brk, body)`: `∀ (n : Nat)(e : Env), I e → I (execLoopBrk e cond brk body
/// n)`. The invariant holds at the env reached after `n` combined-guarded steps — i.e. at
/// EITHER exit point. `claimed` overrides the invariant (fail-closed hook). Mirrors
/// `mirsem::break_loop_conclusion_type`.
fn break_loop_conclusion_type_ir(blp: &IrBreakLoop, claimed: Option<&IrLoopInvariant>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = blp.invariant_expr(claimed);
    let cond_expr = blp.cond_expr();
    let brk_expr = blp.brk_expr();
    let body_expr = blp.body_expr();
    // ∀ (n e), I e → I (execLoopBrk e cond brk body n)
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    let looped = exec_loop_brk_app_ir(
        Expr::bvar(1),
        cond_expr.lift(3),
        brk_expr.lift(3),
        body_expr.lift(3),
        Expr::bvar(2),
    );
    let i_loop = Expr::app(i_expr.lift(3), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    Expr::pi(bd(), cst("Nat"), body_e)
}

/// The PER-FUNCTION break-loop PROOF — `loopInvariantRuleBrk I cond brk body <pres>`. Mirrors
/// `mirsem::break_loop_proof`.
fn break_loop_proof_ir(blp: &IrBreakLoop) -> Expr {
    let i_expr = blp.invariant_expr(None);
    let cond_expr = blp.cond_expr();
    let brk_expr = blp.brk_expr();
    let body_expr = blp.body_expr();
    let pres = break_loop_preservation_proof_ir(blp);
    Expr::apps(cst(TRUSTIR_LOOP_INVARIANT_RULE_BRK), [i_expr, cond_expr, brk_expr, body_expr, pres])
}

/// Check the BREAK-LOOP refinement instance against the real clean-kernel, modulo 3: the
/// trust-ir break-able Hoare while-rule `loopInvariantRuleBrk` INSTANTIATED at this loop's
/// concrete `(I, cond, brk, body)` and fed a combined-guard preservation proof.
/// `ProvenModulo3` means the invariant `i ≤ n` holds at the env reached after an arbitrary
/// number of combined-guarded steps — hence at BOTH exit points (guard-false AND break) —
/// kernel-verified modulo 3. Fail-closed for a wrong invariant.
#[must_use]
pub fn check_trustir_break_loop_instance(blp: &IrBreakLoop) -> RefinementVerdict {
    check_trustir_break_loop_instance_inner(blp, None)
}

fn check_trustir_break_loop_instance_inner(
    blp: &IrBreakLoop,
    claimed: Option<&IrLoopInvariant>,
) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = break_loop_conclusion_type_ir(blp, claimed);
    let proof = break_loop_proof_ir(blp);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("break loop check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.break_loop_instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add break loop instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("break loop instance decl not found".to_string()),
    }
}

/// The canonical `count_to_break` early-exit loop `while i < n { if brk_cond { break }; i :=
/// i + 1 }` over env indices `i = 3`, `n = 1`, break-condition `Eq (Var 3) (Var 5)` (`i ==
/// stop`, env index 5), carrying the GUARD-AWARE upper bound `I := λ e. Int.le (e 3) (e 1)`
/// (`i ≤ n`). The same shape `mirsem`'s break-loop certifies — the invariant holds at BOTH
/// the guard-false exit (`i ≥ n`) AND the break exit (`i == stop`).
fn example_count_to_break_loop() -> IrBreakLoop {
    IrBreakLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
        brk: IrCond { op: TrustIrCmpOp::Eq, a: IrOperand::Var(3), b: IrOperand::Var(5) },
        body: vec![IrStmt {
            idx: 3,
            rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
        }],
        inv: IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 1 },
    }
}

/// FAIL-CLOSED probe for the BREAK-loop refinement: claim the upper bound `i ≤ r` for a bound
/// index `r` the loop guard `i < n` does NOT mention. The combined guard's loop-component
/// (extracted via `andLeftTrue`) yields `Int.lt (e i)(e n) ≡ Int.le ((e i)+1)(e n)`, but the
/// claimed codomain demands `Int.le ((e i)+1)(e r)` (r ≠ n) — NOT def-eq ⇒ the
/// `of_decide_eq_true` proof is ill-typed against the wrong-bound conclusion ⇒ KernelRejected.
/// Returns `true` IFF rejected (the sound outcome) — the break-loop refinement is GENUINE
/// (the loop-guard component is load-bearing, the break component genuinely unneeded).
#[must_use]
pub fn trustir_break_loop_refinement_fail_closed() -> bool {
    let blp = example_count_to_break_loop();
    // The wrong invariant: `i ≤ r` where `r = 2` is NOT the guard's bound (`n = 1`).
    let wrong = IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 2 };
    // Build the conclusion AT the wrong invariant, feed the HONEST proof (built for `n`).
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(_) => return false,
    };
    let concl_ty = break_loop_conclusion_type_ir(&blp, Some(&wrong));
    let proof = break_loop_proof_ir(&blp);
    let tc = TypeChecker::new(&env);
    if tc.check_type(&proof, &concl_ty).is_err() {
        return true; // rejected at type-check — fail-closed
    }
    drop(tc);
    let name = Name::from_string("Trust.TrustIr.Refinement.break_loop_wrong");
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: concl_ty, value: proof })
        .is_err()
}

// ---------------------------------------------------------------------------
// NESTED-loop REFINEMENT — the OUTER while-rule `loopInvariantRuleO` INSTANTIATED at a
// concrete `while cond_outer { <reset?>; <inner while-loop>; counter += 1 }` whose OUTER
// invariant is preserved across the COMPLETED inner loop. MIRRORS the committed
// `mirsem::{SemNestedLoopFunction, nested_inner_*, nested_outer_preservation_proof,
// nested_loop_conclusion_type, nested_loop_proof, check_nested_loop_instance,
// nested_loop_witness}` byte-for-byte (renamed `check_trustir_nested_loop_instance` to
// avoid the MirSem export collision). Two outer-invariant CLASSES, both mirroring MirSem:
//   (1) UNTOUCHED-LOCAL  `I := λ e. e[t] = c`  — neither loop nor the counter writes `t`;
//       the inner loop's untouched-local preservation (`loopInvariantRule` at `Ir := λ e'.
//       e'[t] = e[t]`) bridged to `hI` via `Eq.trans`.
//   (2) MONOTONE         `I := λ e. c ≤ e[s]`  — the inner loop WRITES `s` but monotonically
//       (`s := s+1`); the inner loop's OWN lower-bound invariant is fed `hI` directly.
// The OUTER body is a `List OStmt` = `[ <OStmt.Assign reset>* ; OStmt.Loop cond_inner
// inner_body fuel ; OStmt.Assign counter (counter+1) ]` — the inner loop EMBEDDED as an
// `OStmt.Loop` region, exactly as MirSem does. The fixpoint reconstructs the certified fact
// (the outer invariant survives every outer iteration, EACH running the inner loop to
// completion), it is NOT `Eq.refl` of a tautology, and a wrong outer invariant → KernelRejected.
// ---------------------------------------------------------------------------

/// The OUTER-invariant CLASS for a nested loop — the trust-ir analogue of the two MirSem
/// nested-loop function families (`SemNestedLoopFunction` for the untouched-local case,
/// `SemMonotoneNestedLoopFunction` for the monotone case). The synthesizer PROPOSES the
/// class; the kernel VERIFIES preservation across the COMPLETED inner loop (a wrong proposal
/// does not type-check ⇒ fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrNestedInvariant {
    /// UNTOUCHED-LOCAL `I := λ e. @Eq Int (e t_idx) (int_lit t_const)` (`t == c`). Neither the
    /// inner body NOR the outer counter-assignment writes `t_idx`, so the invariant survives
    /// both loops. The OUTER preservation composes the INNER `loopInvariantRule` at `Ir := λ
    /// e'. e'[t] = e[t]` (preserved DEFINITIONALLY, since `inner_body` never writes `t`) with
    /// `Eq.trans` to `hI`. Mirrors `mirsem::SemNestedLoopFunction`.
    UntouchedLocal { t_idx: u64, t_const: i128 },
    /// MONOTONE `I := λ e. Int.le (int_lit c) (e s_idx)` (`c ≤ s`). The inner body WRITES `s_idx`
    /// but MONOTONICALLY (`s := s + 1`), so `c ≤ s` survives the inner loop by the inner loop's
    /// OWN lower-bound invariant (`Int.le_trans` + `Int.le_self_add_one`), fed `hI` directly (no
    /// `Eq.refl`/`Eq.trans` — `I` and `Ir` are the SAME predicate). The outer counter increment
    /// leaves `s` untouched. Mirrors `mirsem::SemMonotoneNestedLoopFunction`.
    Monotone { s_idx: u64, c: i128 },
}

/// A CONCRETE trust-ir nested-loop function: an OUTER `while cond_outer { [reset]*; <inner
/// while-loop>; counter += 1 }` whose OUTER invariant (a [`IrNestedInvariant`]) is preserved
/// across the completed inner loop. The inner loop is the flat `while cond_inner { inner_body
/// }` (a `List Stmt`, reusing the EXISTING flat `execLoop`). The trust-ir analogue of
/// `mirsem::SemNestedLoopFunction` / `SemMonotoneNestedLoopFunction` (unified by the invariant
/// class). The OUTER body embeds the inner loop as an `OStmt.Loop` region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrNestedLoop {
    /// The OUTER loop guard.
    pub cond_outer: IrCond,
    /// The INNER loop guard.
    pub cond_inner: IrCond,
    /// Optional outer-body RESET assignments executed BEFORE the inner loop each outer
    /// iteration (e.g. `j := 0`). Each must NOT write the OUTER-invariant variable. Empty for
    /// the bare MirSem shape; `[j := 0]` for the `while i<n { j:=0; while j<m {j+=1}; i+=1 }`
    /// shape the task names.
    pub resets: Vec<IrStmt>,
    /// The INNER loop body (flat `List Stmt`).
    pub inner_body: Vec<IrStmt>,
    /// The OUTER counter local (`counter += 1` in the outer body, AFTER the inner loop).
    pub counter_idx: u64,
    /// The OUTER invariant class.
    pub inv: IrNestedInvariant,
}

impl IrNestedLoop {
    /// Whether the INNER loop body assigns local `idx` (the inner write-set membership).
    #[must_use]
    fn inner_assigns(&self, idx: u64) -> bool {
        self.inner_body.iter().any(|s| s.idx == idx)
    }

    /// Whether any RESET assignment writes local `idx`.
    fn reset_assigns(&self, idx: u64) -> bool {
        self.resets.iter().any(|s| s.idx == idx)
    }

    /// The closed `List Trust.TrustIr.Stmt` value for the INNER loop body.
    fn inner_body_list_expr(&self) -> Expr {
        let nil =
            Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), stmt_ty());
        self.inner_body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [stmt_ty(), s.to_stmt_expr(), tail],
            )
        })
    }

    /// The OUTER guard as a closed `Cond`.
    fn cond_outer_expr(&self) -> Expr {
        self.cond_outer.to_cond_expr()
    }

    /// The OUTER body as a closed `List OStmt`, with the inner loop's fuel taken from the
    /// de Bruijn ref `fuel_ref` (a free `Nat` variable bound OUTSIDE this term):
    /// `[ OStmt.Assign reset ]* ++ [ OStmt.Loop cond_inner inner_body fuel ;
    ///    OStmt.Assign counter (counter+1) ]`. Mirrors `mirsem::*::outer_body_list_expr`.
    fn outer_body_list_expr(&self, fuel_ref: Expr) -> Expr {
        let ostmt_ty = cst(TRUSTIR_OSTMT);
        // OStmt.Loop cond_inner inner_body fuel
        let loop_stmt = Expr::apps(
            cst(TRUSTIR_OSTMT_LOOP),
            [self.cond_inner.to_cond_expr(), self.inner_body_list_expr(), fuel_ref],
        );
        // OStmt.Assign counter (BinaryOp Add (Var counter) (Const 1))
        let inc_rv =
            IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(self.counter_idx), IrOperand::Const(1));
        let assign_stmt = Expr::apps(
            cst(TRUSTIR_OSTMT_ASSIGN),
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
        // tail: cons loop_stmt (cons assign_stmt nil)
        let tail = cons(loop_stmt, cons(assign_stmt, nil));
        // prepend the reset OStmt.Assign statements (in program order).
        self.resets.iter().rev().fold(tail, |acc, s| {
            let reset_stmt = Expr::apps(
                cst(TRUSTIR_OSTMT_ASSIGN),
                [Expr::nat_lit(s.idx), s.rvalue.to_rvalue_expr()],
            );
            cons(reset_stmt, acc)
        })
    }

    /// The OUTER invariant `I : Env → Prop` as a closed `λ (e : Env). <prop>` term.
    /// `claimed` overrides the invariant (the fail-closed hook). Under `λ e`: e = bvar(0).
    fn invariant_expr(&self, claimed: Option<&IrNestedInvariant>) -> Expr {
        let bd = || BinderData::from(BinderInfo::Default);
        let inv = claimed.unwrap_or(&self.inv);
        let prop = match inv {
            IrNestedInvariant::UntouchedLocal { t_idx, t_const } => {
                let e_at = Expr::app(Expr::bvar(0), Expr::nat_lit(*t_idx));
                Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [int_ty(), e_at, int_lit(*t_const)],
                )
            }
            IrNestedInvariant::Monotone { s_idx, c } => {
                let e_s = Expr::app(Expr::bvar(0), Expr::nat_lit(*s_idx));
                Expr::apps(cst("Int.le"), [int_lit(*c), e_s])
            }
        };
        Expr::lam(bd(), env_ty(), prop)
    }

    /// The CLOSED `Env` term `execO`'s threading produces for the reset prefix `[Assign i0 r0;
    /// …]` applied to `e_ref`: `set (… (set e_ref i0 (evalRvalue e_ref r0)) …) iN (evalRvalue …
    /// rN)`. This is EXACTLY what the `Assign` arm of `execO` left-folds before the inner-loop
    /// `Loop` arm runs (`execO` threads `set e' i (evalRvalue e' R)` for each `Assign`). For an
    /// empty reset list it is `e_ref` unchanged — the bare MirSem shape. The inner loop in the
    /// outer-preservation proof must be applied at THIS post-reset env (def-eq to `e_ref` at any
    /// index the resets do not write).
    fn apply_resets_env(&self, e_ref: &Expr) -> Expr {
        self.resets.iter().fold(e_ref.clone(), |acc, s| {
            let v = Expr::apps(cst(TRUSTIR_EVAL_RVALUE), [acc.clone(), s.rvalue.to_rvalue_expr()]);
            Expr::apps(cst(TRUSTIR_SET), [acc, Expr::nat_lit(s.idx), v])
        })
    }
}

/// The INNER UNTOUCHED-LOCAL invariant `Ir := λ (e' : Env). @Eq Int (e' t_idx) (e t_idx)`,
/// built so that the OUTER env `e` is the de Bruijn ref `e_ref` (it sits OUTSIDE the `λ e'`
/// this introduces, so callers pass `e_ref` at the depth BEFORE `λ e'`). Used by the inner
/// `loopInvariantRule` instance — it states the inner loop keeps `t_idx` equal to whatever it
/// was in the OUTER env `e`. Mirrors `mirsem::nested_inner_invariant_expr`.
fn nested_inner_invariant_expr_ir(t_idx: u64, e_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `λ (e' : Env)`: e' = bvar(0); e_ref lifted by 1.
    let e_prime_at = Expr::app(Expr::bvar(0), Expr::nat_lit(t_idx));
    let e_at = Expr::app(e_ref.clone().lift(1), Expr::nat_lit(t_idx));
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [int_ty(), e_prime_at, e_at],
    );
    Expr::lam(bd(), env_ty(), eq)
}

/// The INNER UNTOUCHED-LOCAL preservation proof `∀ e', Ir e' → evalCond e' cond_inner = true
/// → Ir (evalBody e' inner_body)`. Because `inner_body` never writes `t_idx`, the codomain
/// `Ir (evalBody e' inner_body) ≡ Eq Int (e' t_idx) (e t_idx) ≡ Ir e'` is def-eq to the
/// hypothesis, so the proof is `λ e' hr _hg. hr`. `e_ref` is the OUTER env, at the depth
/// BEFORE this builder's binders. FAIL-CLOSED: if `inner_body` DID write `t_idx`, `(evalBody
/// e' inner_body) t_idx` would not ι-reduce to `e' t_idx`, so the codomain would differ from
/// `Ir e'` and `hr` would be ill-typed ⇒ KernelRejected. Mirrors
/// `mirsem::nested_inner_preservation_proof`.
fn nested_inner_preservation_proof_ir(nlf: &IrNestedLoop, t_idx: u64, e_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let ir = nested_inner_invariant_expr_ir(t_idx, e_ref);
    let cond_inner = nlf.cond_inner.to_cond_expr();
    // inside `λ e'`: e' = bvar(0); Ir lifted +1 for `Ir e'`.
    let ir_e = Expr::app(ir.clone().lift(1), Expr::bvar(0));
    // inside `λ e' λ hr`: hr = 0, e' = 1; the guard `evalCond e' cond_inner = true`.
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_inner.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e' λ hr λ _hg`: hr = 1 ⇒ return hr.
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), ir_e, Expr::lam(bd(), guard_eq, Expr::bvar(1))))
}

/// The INNER MONOTONE lower-bound preservation proof `∀ e', Ir e' → evalCond e' cond_inner =
/// true → Ir (evalBody e' inner_body)` for `Ir := λ e'. c ≤ e'[s_idx]`, over the inner body
/// that INCREMENTS `s_idx` by `+1`:
/// `λ (e')(hr)(_hg). Int.le_trans c (e' s) ((e' s)+1) hr (Int.le_self_add_one (e' s))`.
///
/// The codomain `Ir (evalBody e' inner_body)` ι-reduces to `Int.le c ((e' s_idx)+1)` (the
/// `j:=j+1` companion statement leaves `s_idx` untouched). From `hr : c ≤ e' s` and
/// `Int.le_self_add_one (e' s) : (e' s) ≤ (e' s)+1`, `Int.le_trans` chains to `c ≤ (e' s)+1`
/// — EXACTLY the reduced codomain. GENUINELY USES the carried hypothesis. FAIL-CLOSED: a
/// DECREMENT inner body gives codomain `c ≤ (e' s)-1`, NOT def-eq to the `Int.le_self_add_one`
/// output ⇒ KernelRejected. Mirrors `mirsem::monotone_inner_preservation_proof`.
fn nested_monotone_inner_preservation_proof_ir(nlf: &IrNestedLoop, s_idx: u64, c: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let ir = nlf.invariant_expr(Some(&IrNestedInvariant::Monotone { s_idx, c }));
    let cond_inner = nlf.cond_inner.to_cond_expr();
    // inside `λ e'`: e' = 0; `Ir e'` for the hypothesis binder.
    let ir_e = Expr::app(ir.clone().lift(1), Expr::bvar(0));
    // inside `λ e' λ hr`: hr = 0, e' = 1; the guard `evalCond e' cond_inner = true`.
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_inner.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e' λ hr λ _hg`: _hg = 0, hr = 1, e' = 2.
    let e_s = Expr::app(Expr::bvar(2), Expr::nat_lit(s_idx)); // e' s_idx
    let c_lit = int_lit(c);
    let s_plus_one = Expr::apps(cst("Int.add"), [e_s.clone(), int_one()]);
    let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_s.clone());
    let proof =
        Expr::apps(cst("Int.le_trans"), [c_lit, e_s, s_plus_one, Expr::bvar(1), self_le_succ]);
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), ir_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The OUTER preservation proof `∀ e, I e → evalCond e cond_outer = true → I (execO e
/// outer_body)` for the nested loop. The `outer_body` runs any resets, the inner loop
/// (symbolic fuel ref `fuel_ref`, bound OUTSIDE this term), then the counter increment.
/// Dispatched on the invariant class. `fuel_ref` is at the depth BEFORE the `λ e λ hI λ _hg`
/// this builder introduces. Mirrors `mirsem::{nested_outer_preservation_proof,
/// monotone_outer_preservation_proof}`.
fn nested_outer_preservation_proof_ir(nlf: &IrNestedLoop, fuel_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = nlf.invariant_expr(None);
    let cond_outer = nlf.cond_outer_expr();
    // inside `λ e`: e = bvar(0); I lifted +1 for `I e`.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    // inside `λ e λ hI`: hI = 0, e = 1; the guard `evalCond e cond_outer = true`.
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_outer.lift(2)]);
    let guard_eq = eq_bool_true(guard);
    // inside `λ e λ hI λ _hg`: _hg = 0, hI = 1, e = 2. `fuel_ref` lifted +3.
    let e_ref = Expr::bvar(2);
    let fuel = fuel_ref.clone().lift(3);
    let cond_inner = nlf.cond_inner.to_cond_expr();
    let inner_body = nlf.inner_body_list_expr();
    // The POST-RESET env `execO` threads before the inner-loop `Loop` arm runs: `set (… e i0
    // v0 …)`. For the bare MirSem shape (no resets) this is `e` itself. The inner loop runs on
    // THIS env, and its value at the invariant index is DEF-EQ to `e`'s (resets write other
    // indices), so the `Eq.refl`/`hI` base inhabits the inner invariant at the reset env.
    let reset_env = nlf.apply_resets_env(&e_ref);

    let body = match nlf.inv {
        IrNestedInvariant::UntouchedLocal { t_idx, t_const } => {
            let t_lit_e = Expr::app(e_ref.clone(), Expr::nat_lit(t_idx)); // e t_idx
            // execLoop reset_env cond_inner inner_body fuel  (the inner-loop result env).
            let inner_result = exec_loop_app_ir(
                reset_env.clone(),
                cond_inner.clone(),
                inner_body.clone(),
                fuel.clone(),
            );
            let inner_result_at_t = Expr::app(inner_result, Expr::nat_lit(t_idx)); // (execLoop …) t_idx
            // Ir := λ e'. Eq Int (e' t_idx) (e t_idx)   (e = bvar(2) — the OUTER env).
            let ir = nested_inner_invariant_expr_ir(t_idx, &e_ref);
            // inner_pres : ∀ e', Ir e' → guard_inner → Ir (evalBody e' inner_body)
            let inner_pres = nested_inner_preservation_proof_ir(nlf, t_idx, &e_ref);
            // Eq.refl Int (e t_idx) : Ir reset_env   (Ir reset_env ≡ Eq Int (reset_env t_idx)
            //   (e t_idx), and reset_env t_idx ≡ e t_idx since resets don't write t_idx).
            let eq_refl =
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
            let refl_ir_e = Expr::apps(eq_refl, [int_ty(), t_lit_e.clone()]);
            // inner_keeps := loopInvariantRule Ir cond_inner inner_body inner_pres fuel reset_env
            //   refl : Ir (execLoop reset_env …) ≡ Eq Int ((execLoop reset_env …) t_idx) (e t_idx).
            let inner_keeps = Expr::apps(
                cst(TRUSTIR_LOOP_INVARIANT_RULE),
                [ir, cond_inner, inner_body, inner_pres, fuel, reset_env, refl_ir_e],
            );
            // hI : Eq Int (e t_idx) (int_lit t_const)  (hI = bvar(1)).
            let h_i = Expr::bvar(1);
            // Eq.trans Int ((execLoop reset_env …) t_idx) (e t_idx) (int_lit t_const) inner_keeps hI
            //   : Eq Int ((execLoop reset_env …) t_idx) (int_lit t_const) — def-eq to
            //   `I (execO e outer_body)` (execO threads the resets then the inner loop then the
            //   outer Assign, which leaves t_idx; the inner loop runs on reset_env).
            let eq_trans =
                Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]);
            Expr::apps(
                eq_trans,
                [int_ty(), inner_result_at_t, t_lit_e, int_lit(t_const), inner_keeps, h_i],
            )
        }
        IrNestedInvariant::Monotone { s_idx, c } => {
            // Ir := λ e'. Int.le c (e' s_idx) — the SAME predicate as `I` (closed; does NOT
            // reference the outer `e`).
            let ir = nlf.invariant_expr(Some(&IrNestedInvariant::Monotone { s_idx, c }));
            // inner_pres : ∀ e', Ir e' → guard_inner → Ir (evalBody e' inner_body)
            let inner_pres = nested_monotone_inner_preservation_proof_ir(nlf, s_idx, c);
            // inner_keeps := loopInvariantRule Ir cond_inner inner_body inner_pres fuel reset_env hI
            //   : Ir (execLoop reset_env cond_inner inner_body fuel) ≡ Int.le c ((execLoop …) s_idx)
            //   — DEF-EQ to the outer codomain. hI : I e ≡ Int.le c (e s_idx) inhabits `Ir reset_env`
            //   ≡ Int.le c (reset_env s_idx) by def-eq (resets don't write s_idx). Fed DIRECTLY.
            Expr::apps(
                cst(TRUSTIR_LOOP_INVARIANT_RULE),
                [ir, cond_inner, inner_body, inner_pres, fuel, reset_env, Expr::bvar(1)],
            )
        }
    };
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, body)))
}

/// The PER-FUNCTION nested-loop CONCLUSION TYPE — `loopInvariantRuleO` SPECIALIZED at the
/// function's `(I, cond_outer, outer_body(fuel))`, universally quantified over the inner fuel
/// `f`: `∀ (f n : Nat)(e : Env), I e → I (execLoopO e cond_outer (outer_body f) n)`. `claimed`
/// overrides the invariant (fail-closed hook). Mirrors `mirsem::nested_loop_conclusion_type`.
fn nested_loop_conclusion_type_ir(nlf: &IrNestedLoop, claimed: Option<&IrNestedInvariant>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = nlf.invariant_expr(claimed);
    let cond_outer = nlf.cond_outer_expr();
    // ∀ (f : Nat). [ ∀ (n : Nat)(e : Env), I e → I (execLoopO e cond_outer (outer_body f) n) ]
    // inside `∀ f ∀ n ∀ e`: e=0, n=1, f=2.
    let i_e = Expr::app(i_expr.clone().lift(3), Expr::bvar(0));
    // under one more arrow: e=1, n=2, f=3.
    let outer_body = nlf.outer_body_list_expr(Expr::bvar(3));
    let looped = exec_loop_o_app_ir(Expr::bvar(1), cond_outer.lift(4), outer_body, Expr::bvar(2));
    let i_loop = Expr::app(i_expr.lift(4), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    Expr::pi(bd(), cst("Nat"), body_n)
}

/// The PER-FUNCTION nested-loop PROOF — `λ (f : Nat). loopInvariantRuleO I cond_outer
/// (outer_body f) <outer_pres f>`. Type-checking it at the conclusion type IS the nested-loop
/// corollary: the OUTER while-rule, instantiated here with an OUTER preservation proof that
/// runs the inner loop to completion (via the inner `loopInvariantRule`), proves the outer
/// invariant survives every outer iteration. Mirrors `mirsem::nested_loop_proof`.
fn nested_loop_proof_ir(nlf: &IrNestedLoop) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = nlf.invariant_expr(None);
    let cond_outer = nlf.cond_outer_expr();
    // inside `λ (f : Nat)`: f = bvar(0).
    let outer_body = nlf.outer_body_list_expr(Expr::bvar(0));
    let outer_pres = nested_outer_preservation_proof_ir(nlf, &Expr::bvar(0));
    let inst = Expr::apps(
        cst(TRUSTIR_LOOP_INVARIANT_RULE_O),
        [i_expr.lift(1), cond_outer.lift(1), outer_body, outer_pres],
    );
    Expr::lam(bd(), cst("Nat"), inst)
}

/// Check the NESTED-LOOP refinement instance against the real clean-kernel, modulo 3: the
/// trust-ir OUTER Hoare while-rule `loopInvariantRuleO` INSTANTIATED at this nested loop's
/// concrete `(I, cond_outer, outer_body)` and fed an OUTER preservation proof that runs the
/// inner loop to completion. `ProvenModulo3` means the outer invariant survives an arbitrary
/// outer iteration count, EACH of whose iterations runs the inner loop to completion (the
/// inner loop's preservation is composed in), kernel-verified modulo 3. The OUTER fixpoint
/// `execLoopO` (a `Nat.rec` over the outer trip count whose body threads through the inner
/// `execLoop` fixpoint) RECONSTRUCTS the certified fact — it is NOT `Eq.refl` of a tautology.
/// Fail-closed for a wrong outer invariant.
#[must_use]
pub fn check_trustir_nested_loop_instance(nlf: &IrNestedLoop) -> RefinementVerdict {
    check_trustir_nested_loop_instance_inner(nlf, None)
}

fn check_trustir_nested_loop_instance_inner(
    nlf: &IrNestedLoop,
    claimed: Option<&IrNestedInvariant>,
) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = nested_loop_conclusion_type_ir(nlf, claimed);
    let proof = nested_loop_proof_ir(nlf);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("nested loop check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.nested_loop_instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add nested loop instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => {
            RefinementVerdict::KernelRejected("nested loop instance decl not found".to_string())
        }
    }
}

/// Mint a modulo-3 nested-loop verdict for `nlf` IFF the per-function instance kernel-checks
/// AND the soundness guard passes. Fail-closed (returns a `KernelRejected` describing the
/// guard violation, never silently accepting): for the UNTOUCHED-LOCAL class the OUTER counter
/// must DIFFER from `t_idx` AND neither the inner body NOR a reset may write `t_idx`; for the
/// MONOTONE class the OUTER counter must DIFFER from `s_idx` AND the inner body MUST actually
/// write `s_idx` (else it is not the monotone-modifies-outer shape). Mirrors the soundness
/// guards in `mirsem::{nested_loop_witness, monotone_nested_loop_witness}`.
#[must_use]
pub fn trustir_nested_loop_witness(nlf: &IrNestedLoop) -> RefinementVerdict {
    match nlf.inv {
        IrNestedInvariant::UntouchedLocal { t_idx, .. } => {
            if nlf.counter_idx == t_idx || nlf.inner_assigns(t_idx) || nlf.reset_assigns(t_idx) {
                return RefinementVerdict::KernelRejected(format!(
                    "untouched-local invariant over a WRITTEN local {t_idx} (counter/inner/reset)"
                ));
            }
        }
        IrNestedInvariant::Monotone { s_idx, .. } => {
            if nlf.counter_idx == s_idx || !nlf.inner_assigns(s_idx) {
                return RefinementVerdict::KernelRejected(format!(
                    "monotone invariant: counter≡s {s_idx} or inner loop does not write s"
                ));
            }
        }
    }
    check_trustir_nested_loop_instance(nlf)
}

// ===========================================================================
// CONDITIONAL-UPDATE (max_scan) WITNESS — the SELECT Hoare while-rule INSTANTIATED at a
// concrete `max_scan` loop `while i < n { m := if i>m { i } else { m }; i := i+1 }` with the
// GENUINE conjoined invariant `0 ≤ m ∧ 0 ≤ i`, kernel-checked modulo 3. MIRRORS the committed
// `mirsem::cond_update` proof: preservation across the conditional select is a `Bool.rec`
// CASE-SPLIT over the update guard — and a wrong invariant (e.g. `0 ≤ m` that ignores the
// then-arm `m := i`) is KernelRejected.
// ===========================================================================

/// A trust-ir SELECT loop body statement — either a plain assignment or a conditional
/// select. The `max_scan` body is `[Sel(m, i>m, i, m); Assign(i, i+1)]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrSStmt {
    /// `idx := rvalue` — a plain assignment (same shape as `IrStmt`).
    Assign(u64, IrRvalue),
    /// `idx := if cond then a else b` — the conditional select.
    Sel(u64, IrCond, IrOperand, IrOperand),
}

impl IrSStmt {
    /// The closed `Trust.TrustIr.SStmt` constructor value.
    fn to_sstmt_expr(&self) -> Expr {
        match self {
            IrSStmt::Assign(idx, rv) => {
                Expr::apps(cst(TRUSTIR_SSTMT_ASSIGN), [Expr::nat_lit(*idx), rv.to_rvalue_expr()])
            }
            IrSStmt::Sel(idx, c, a, b) => Expr::apps(
                cst(TRUSTIR_SSTMT_SEL),
                [Expr::nat_lit(*idx), c.to_cond_expr(), a.to_operand_expr(), b.to_operand_expr()],
            ),
        }
    }
}

/// A trust-ir CONDITIONAL-UPDATE loop `while cond { body }` with a `List SStmt` body,
/// carrying the conjoined invariant `0 ≤ m ∧ 0 ≤ i` — the trust-ir analogue of the `max_scan`
/// `SynthInvariant::CondUpdateGeConst { m_idx, c: 0, i_idx, n_idx }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrCondUpdateLoop {
    /// The loop guard `while cond { … }` (a single comparison, `i < n`).
    pub cond: IrCond,
    /// The select body's ordered statement trace.
    pub body: Vec<IrSStmt>,
    /// The conditionally-updated accumulator env index `m`.
    pub m_idx: u64,
    /// The lower-bound constant (`0` for the tractable interval case).
    pub c: i128,
    /// The counter env index `i`.
    pub i_idx: u64,
}

impl IrCondUpdateLoop {
    // Trust: visibility-only (`pub(crate)`) for the trust-ir termination port
    // (`trustir_termination.rs`) — the S-layer `loopTotalCorrectS` instance pins the
    // BYTE-IDENTICAL guard/body/invariant terms the partial-correctness witness pins.
    pub(crate) fn cond_expr(&self) -> Expr {
        self.cond.to_cond_expr()
    }

    /// The closed `List Trust.TrustIr.SStmt` body value.
    // Trust: visibility-only (`pub(crate)`) for the trust-ir termination port.
    pub(crate) fn body_expr(&self) -> Expr {
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            cst(TRUSTIR_SSTMT),
        );
        self.body.iter().rev().fold(nil, |tail, s| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [cst(TRUSTIR_SSTMT), s.to_sstmt_expr(), tail],
            )
        })
    }

    /// The conjoined invariant `I := λ e. And (Int.le c (e m)) (Int.le c (e i))` (`c ≤ m ∧ c ≤
    /// i`). `claimed` overrides it (the fail-closed hook). Under `λ e`: e = bvar(0).
    // Trust: visibility-only (`pub(crate)`) for the trust-ir termination port.
    pub(crate) fn invariant_expr(&self, claimed: Option<&Expr>) -> Expr {
        if let Some(e) = claimed {
            return e.clone();
        }
        let bd = || BinderData::from(BinderInfo::Default);
        let e_m = Expr::app(Expr::bvar(0), Expr::nat_lit(self.m_idx));
        let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(self.i_idx));
        let lo_m = Expr::apps(cst("Int.le"), [int_lit(self.c), e_m]);
        let lo_i = Expr::apps(cst("Int.le"), [int_lit(self.c), e_i]);
        let prop = Expr::apps(cst("And"), [lo_m, lo_i]);
        Expr::lam(bd(), env_ty(), prop)
    }
}

/// The SELECT Hoare while-rule CONCLUSION type for a cond-update loop: `∀ (n:Nat)(e:Env), I e →
/// I (execLoopS e cond body n)`. The `loop_instance_conclusion_type_ir` analogue over `execLoopS`.
fn cond_update_conclusion_type_ir(lp: &IrCondUpdateLoop, claimed: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(claimed);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    let looped =
        exec_loop_s_app_ir(Expr::bvar(1), cond_expr.lift(3), body_expr.lift(3), Expr::bvar(2));
    let i_loop = Expr::app(i_expr.lift(3), looped);
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    Expr::pi(bd(), cst("Nat"), body_e)
}

/// Build the GENUINE preservation proof for `max_scan`'s `0 ≤ m ∧ 0 ≤ i` over the SELECT body
/// `[Sel(m, i>m, i, m); Assign(i, i+1)]`. The codomain `I (execS e body)` ι-reduces to
/// `And (Int.le c (iteI e (i>m) (e i)(e m))) (Int.le c (Int.add (e i) 1))` (the select sets
/// `m`, then `i := i+1` leaves `m` untouched). The proof is `And.intro` of:
///  * (LEFT — `c ≤ iteI …`) a `Bool.rec` CASE-SPLIT over the update guard `evalCond e (i>m)`:
///    the TRUE arm reduces `iteI` to `e i` and discharges `c ≤ e i` from `And.right hI`; the
///    FALSE arm reduces `iteI` to `e m` and discharges `c ≤ e m` from `And.left hI`. BOTH arms
///    USE the hypothesis — a then-arm claim that ignores `m := i` (e.g. supplying `And.left hI`
///    `: c ≤ m` where the reduced codomain needs `c ≤ i`) is NOT def-eq ⇒ KernelRejected.
///  * (RIGHT — `c ≤ i+1`) `Int.le_trans c (e i) ((e i)+1) (And.right hI)(Int.le_self_add_one)`,
///    USING the hypothesis (identical to the counter lower bound).
/// `lp.c` MUST be `0` (the tractable interval case wired here; `Int.le_self_add_one` /
/// `Int.le_trans` are the prelude order lemmas).
// Trust: visibility-only (`pub(crate)`) for the trust-ir termination port — the S-layer
// `loopTotalCorrectS` instance feeds the SAME preservation proof the partial-correctness
// witness certifies.
pub(crate) fn cond_update_preservation_proof_ir(lp: &IrCondUpdateLoop) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let m_idx = lp.m_idx;
    let i_idx = lp.i_idx;
    let c_lit = int_lit(lp.c);
    // The select's update guard `i > m` ≡ `Cmp Gt (Var i)(Var m)`.
    let upd_cond =
        IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(i_idx), b: IrOperand::Var(m_idx) };

    // The preservation hypothesis `pres` binder type (matches `preservation_hyp_type_s_ir`'s
    // outer shape — but here we build the proof term `λ e λ hI λ hg . …`).
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
    let guard_eq = eq_bool_true(guard);

    // The proof body sits under `λ e λ hI λ hg`: hg = 0, hI = 1, e = 2.
    let e_at = |idx: u64, depth_bvar: u32| Expr::app(Expr::bvar(depth_bvar), Expr::nat_lit(idx));
    let e_m = e_at(m_idx, 2);
    let e_i = e_at(i_idx, 2);

    // hI : And (c ≤ e m) (c ≤ e i). Build the shared proposition types and
    // project `c ≤ e i` for the right-hand proof. The Bool-rec branches below
    // rebuild both projections at their additional binder depth.
    let and_lo_m = Expr::apps(cst("Int.le"), [c_lit.clone(), e_m.clone()]);
    let and_lo_i = Expr::apps(cst("Int.le"), [c_lit.clone(), e_i.clone()]);
    let h_i = Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [and_lo_m, and_lo_i, Expr::bvar(1)],
    ); // : c ≤ e i

    // The `iteI e (i>m) (e i)(e m)` term (the reduced `execS`-set of `m`), at the `λ e λ hI λ hg`
    // depth (e = 2).
    let ite_term = Expr::apps(
        cst(TRUSTIR_ITE_I),
        [Expr::bvar(2), upd_cond.to_cond_expr(), e_i.clone(), e_m.clone()],
    );
    // The LEFT conjunct prop the reduced codomain carries: `Int.le c (iteI …)`.
    let prop_left = Expr::apps(cst("Int.le"), [c_lit.clone(), ite_term.clone()]);
    // The RIGHT conjunct prop: `Int.le c ((e i)+1)`.
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_one()]);
    let prop_right = Expr::apps(cst("Int.le"), [c_lit.clone(), i_plus_one.clone()]);

    // -- LEFT proof: case-split `g := evalCond e (i>m)` via a generalised `Bool.rec`. --
    // iteI e (i>m) (e i)(e m) ≡ Bool.rec (λ_.Int) (e m) (e i) g. We prove `Int.le c (Bool.rec …
    // g)` by `Bool.rec` on `g` with the self-referential motive
    //   motive_g := λ(b:Bool). evalCond e (i>m) = b → Int.le c (Bool.rec (λ_.Int)(e m)(e i) b)
    // (the `stepPreservesInvO` discipline). The FALSE arm discharges `c ≤ e m` (h_m); the TRUE
    // arm discharges `c ≤ e i` (h_i). Both USE the hypothesis.
    let upd_guard_at = |depth_bvar: u32| {
        Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(depth_bvar), upd_cond.to_cond_expr()])
    };
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    let bool_rec_int =
        || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let proof_left = {
        // motive_g := λ(b:Bool). Pi(eq_dom, cod). Under `λ e λ hI λ hg λ b`: b=0, hg=1, hI=2, e=3
        // for `eq_dom`. The `cod` sits UNDER the `Pi(eq_dom, ·)` binder, so EVERYTHING shifts +1
        // there: the eq-binder=0, b=1, hg=2, hI=3, e=4.
        let motive_g = {
            // eq_dom (directly under `λ b`): evalCond e (i>m) = b   (b = bvar(0), e = bvar(3))
            let g_b = upd_guard_at(3);
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_b, Expr::bvar(0)],
            );
            // cod (under `λ b` AND `Pi(eq_dom)`): Int.le c (Bool.rec (λ_.Int) (e m)(e i) b)
            //   e = bvar(4), b = bvar(1).
            let e_m4 = e_at(m_idx, 4);
            let e_i4 = e_at(i_idx, 4);
            let body_b =
                Expr::apps(bool_rec_int(), [int_motive.clone(), e_m4, e_i4, Expr::bvar(1)]);
            let cod = Expr::apps(cst("Int.le"), [c_lit.clone(), body_b]);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };
        // false_case : λ(_he : evalCond e (i>m) = Bool.false). h_m  (the bvar refs all shift +1)
        let false_case = {
            let g_f = upd_guard_at(2); // e shifted +1 under the new `_he` binder ⇒ e = bvar(2)
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_f, cst("Bool.false")],
            );
            // h_m at this depth: e=2 still? Under `λ _he` the original e(2)→3, hI(1)→2. So h_m must
            // be rebuilt at e=3, hI=2.
            let e_m3 = e_at(m_idx, 3);
            let e_i3 = e_at(i_idx, 3);
            let and_lo_m3 = Expr::apps(cst("Int.le"), [c_lit.clone(), e_m3.clone()]);
            let and_lo_i3 = Expr::apps(cst("Int.le"), [c_lit.clone(), e_i3]);
            let h_m3 = Expr::apps(
                Expr::const_(Name::from_string("And.left"), vec![]),
                [and_lo_m3, and_lo_i3, Expr::bvar(2)],
            );
            Expr::lam(bd(), eq_false, h_m3)
        };
        // true_case : λ(_he : evalCond e (i>m) = Bool.true). h_i  (e=3, hI=2 under `λ _he`)
        let true_case = {
            let g_t = upd_guard_at(2);
            let eq_true = eq_bool_true(g_t);
            let e_m3 = e_at(m_idx, 3);
            let e_i3 = e_at(i_idx, 3);
            let and_lo_m3 = Expr::apps(cst("Int.le"), [c_lit.clone(), e_m3]);
            let and_lo_i3 = Expr::apps(cst("Int.le"), [c_lit.clone(), e_i3.clone()]);
            let h_i3 = Expr::apps(
                Expr::const_(Name::from_string("And.right"), vec![]),
                [and_lo_m3, and_lo_i3, Expr::bvar(2)],
            );
            Expr::lam(bd(), eq_true, h_i3)
        };
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let g = upd_guard_at(2); // at `λ e λ hI λ hg` depth, e = 2
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, g.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), g]);
        Expr::app(ghelper, refl)
    };

    // -- RIGHT proof: Int.le_trans c (e i) ((e i)+1) h_i (Int.le_self_add_one (e i)). --
    let proof_right = {
        let self_le_succ = Expr::app(cst("Int.le_self_add_one"), e_i.clone());
        Expr::apps(
            cst("Int.le_trans"),
            [c_lit.clone(), e_i.clone(), i_plus_one.clone(), h_i, self_le_succ],
        )
    };

    // And.intro prop_left prop_right proof_left proof_right.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [prop_left, prop_right, proof_left, proof_right],
    );
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, proof)))
}

/// The PER-FUNCTION partial-correctness PROOF — `loopInvariantRuleS` APPLIED to this cond-update
/// loop's closed `(I, cond, body, preservation)`. Mirrors `loop_instance_proof_ir` over `execS`.
fn cond_update_instance_proof_ir(lp: &IrCondUpdateLoop) -> Expr {
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();
    let pres = cond_update_preservation_proof_ir(lp);
    Expr::apps(cst(TRUSTIR_LOOP_INVARIANT_RULE_S), [i_expr, cond_expr, body_expr, pres])
}

fn check_cond_update_loop_instance_inner(
    lp: &IrCondUpdateLoop,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let concl_ty = cond_update_conclusion_type_ir(lp, claimed);
    let proof = cond_update_instance_proof_ir(lp);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "cond-update instance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.cond_update_instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add cond-update instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => {
            RefinementVerdict::KernelRejected("cond-update instance decl not found".to_string())
        }
    }
}

/// Check the CONDITIONAL-UPDATE (max_scan) refinement instance against the real clean-kernel,
/// modulo 3: the trust-ir SELECT Hoare while-rule `loopInvariantRuleS` INSTANTIATED at the
/// `max_scan` conjoined invariant `0 ≤ m ∧ 0 ≤ i`, guard `i < n`, the `Sel`-bodied select loop,
/// and a GENUINE preservation proof whose LEFT conjunct case-splits the update guard. GENUINE +
/// fail-closed: a wrong invariant (one whose then-arm codomain the hypothesis does not prove) is
/// KernelRejected. Soundness guard: the body's first statement MUST be the `Sel` at `m_idx`, the
/// second the `i := i+1` increment, `c = 0`, and `i_idx ≠ m_idx`.
#[must_use]
pub fn check_cond_update_loop_instance(lp: &IrCondUpdateLoop) -> RefinementVerdict {
    // SOUNDNESS GUARD (mirrors `trustir_nested_loop_witness`): the body must be EXACTLY the
    // recognized cond-update shape so the hard-coded preservation proof is sound.
    if lp.c != 0 {
        return RefinementVerdict::KernelRejected(format!(
            "cond-update: only the tractable interval case c = 0 is wired (got {})",
            lp.c
        ));
    }
    if lp.i_idx == lp.m_idx {
        return RefinementVerdict::KernelRejected("cond-update: counter ≡ accumulator".to_string());
    }
    let ok_sel = matches!(
        lp.body.first(),
        Some(IrSStmt::Sel(idx, cond, IrOperand::Var(a), IrOperand::Var(b)))
            if *idx == lp.m_idx
            && cond.op == TrustIrCmpOp::Gt
            && *a == lp.i_idx && cond.a == IrOperand::Var(lp.i_idx)
            && *b == lp.m_idx && cond.b == IrOperand::Var(lp.m_idx)
    );
    let ok_inc = matches!(
        lp.body.get(1),
        Some(IrSStmt::Assign(idx, IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(a), IrOperand::Const(1))))
            if *idx == lp.i_idx && *a == lp.i_idx
    );
    if lp.body.len() != 2 || !ok_sel || !ok_inc {
        return RefinementVerdict::KernelRejected(
            "cond-update: body is not the recognized `m := Sel(i>m) i m; i := i+1` shape"
                .to_string(),
        );
    }
    check_cond_update_loop_instance_inner(lp, None)
}

/// Kernel-check (modulo 3) that the cond-update loop's TRUST-IR-CERTIFIED conjoined
/// invariant `c ≤ m ∧ c ≤ i` DISCHARGES the source postcondition `c ≤ ret` (the return
/// reads `m`) at the halting state — the SELECT-layer analogue of
/// [`check_loop_postcondition_instance`], Seam C of the via-trustir de-MirSem-ing. The
/// theorem proved is
///
///   `∀ (fuel : Nat)(e : Env), I e → Int.le c (execLoopS e cond body fuel m_idx)`
///
/// — `And.left` projected out of the SAME instantiated SELECT while-rule the PRIMARY
/// witness certifies (`loopInvariantRuleS I cond body pres fuel e hI`). No new induction;
/// PARTIAL correctness (termination stays on the MirSem `loop_total_correct_witness` — the
/// acknowledged residue). Fail-closed: only `ConstLeRet` at the accumulator `m_idx` with
/// the certified constant is accepted; everything else declines or is KernelRejected.
///
/// NOTE: the PRIMARY witness's shape guard (`c == 0`, `i_idx != m_idx`, the exact `Sel`
/// body — see [`check_cond_update_loop_instance`]) is deliberately NOT re-applied here:
/// this instance is a standalone conditional theorem (`I e → …`), true and kernel-checked
/// for ANY shape it type-checks on, and the §6 caller only reaches it AFTER the guarded
/// primary witness passed.
#[must_use]
pub fn check_cond_update_postcondition_instance(
    lp: &IrCondUpdateLoop,
    post: IrLoopPost,
) -> RefinementVerdict {
    // Only `c ≤ ret` at the conditionally-updated accumulator is discharged.
    let IrLoopPost::ConstLeRet { read_idx, c: pc } = post else {
        return RefinementVerdict::KernelRejected(
            "the cond-update invariant discharges only `c ≤ ret`".to_string(),
        );
    };
    if read_idx != lp.m_idx || pc != lp.c {
        return RefinementVerdict::KernelRejected(
            "postcondition read index / constant does not match the certified cond-update \
             invariant"
                .to_string(),
        );
    }
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();

    // Under `λ (fuel:Nat) λ (e:Env) λ (hI : I e)`: hI = 0, e = 1, fuel = 2.
    let halt = exec_loop_s_app_ir(
        Expr::bvar(1),
        cond_expr.clone().lift(3),
        body_expr.clone().lift(3),
        Expr::bvar(2),
    );
    let halt_m = Expr::app(halt.clone(), Expr::nat_lit(lp.m_idx));
    let halt_i = Expr::app(halt, Expr::nat_lit(lp.i_idx));
    let conj_m = Expr::apps(cst("Int.le"), [int_lit(lp.c), halt_m]); // c ≤ halt m
    let conj_i = Expr::apps(cst("Int.le"), [int_lit(lp.c), halt_i]); // c ≤ halt i

    // `I halt` — the SAME instantiated SELECT while-rule the PRIMARY witness certifies.
    let i_halt_proof = Expr::apps(
        cond_update_instance_proof_ir(lp).lift(3),
        [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
    );
    // `And.left (c ≤ halt m) (c ≤ halt i) (I halt) : c ≤ halt m` — the postcondition.
    let proof_body = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [conj_m.clone(), conj_i, i_halt_proof],
    );

    // Conclusion TYPE: ∀ (fuel:Nat)(e:Env), I e → c ≤ (execLoopS e cond body fuel) m.
    let i_e = Expr::app(i_expr.clone().lift(2), Expr::bvar(0));
    let concl_ty =
        Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, conj_m)));
    let i_e_dom = Expr::app(i_expr.lift(2), Expr::bvar(0));
    let proof = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_dom, proof_body)),
    );

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "cond-update postcondition instance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.cond_update_postcondition_instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!(
            "add cond-update postcondition instance: {e:?}"
        ));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "cond-update postcondition instance decl not found".to_string(),
        ),
    }
}

/// The canonical `max_scan` cond-update loop `while i < n { m := if i>m { i } else { m }; i :=
/// i+1 }` over env indices `i`, `m`, `n` — the same shape `mirsem`'s `CondUpdateGeConst`
/// certifies. The invariant is `0 ≤ m ∧ 0 ≤ i`.
#[cfg(test)]
fn example_max_scan_loop(i_idx: u64, m_idx: u64, n_idx: u64) -> IrCondUpdateLoop {
    IrCondUpdateLoop {
        cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(i_idx), b: IrOperand::Var(n_idx) },
        body: vec![
            IrSStmt::Sel(
                m_idx,
                IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(i_idx), b: IrOperand::Var(m_idx) },
                IrOperand::Var(i_idx),
                IrOperand::Var(m_idx),
            ),
            IrSStmt::Assign(
                i_idx,
                IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(i_idx), IrOperand::Const(1)),
            ),
        ],
        m_idx,
        c: 0,
        i_idx,
    }
}

// ===========================================================================
// SLICE-INDEX (guarded_index) WITNESS — the BOUNDS-GUARD refinement. `guarded_index` is
// `if i < s.len() { s[i] } else { 0 }`. The return is MODELED as the conditional select
// `iteI (i < sliceLen s) (idxElem s i) 0`. The GENUINE bounds-guard refinement proves: UNDER
// the guard `evalCond e (i < sliceLen s) = true`, the select reduces to the in-bounds element
// `idxElem (e s)(e i)` (the `Bool.rec` TRUE arm). A wrong claim (guard true → result is the
// `0` else-arm) is KernelRejected. MODEL-ONLY (the `bnot`/`UnOp::Not` discipline): the live
// `clean_ground` grounds slice access to the MirSem-named opaques, which a clean re-anchor must
// not cite — so the refinement is against the trust-ir `idxElem`/`sliceLen` denotation.
// ===========================================================================

/// A trust-ir bounds-guarded slice-index return `if i < s.len() { s[i] } else { dflt }` — the
/// trust-ir analogue of `guarded_index`. `s_idx`/`i_idx` are the slice / index env indices; the
/// guard is `i < sliceLen s` and the in-bounds value is `idxElem s i`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrGuardedIndex {
    /// The slice (handle) env index `s`.
    pub s_idx: u64,
    /// The index env index `i`.
    pub i_idx: u64,
    /// The else-arm default (`0` for `guarded_index`).
    pub dflt: i128,
}

impl IrGuardedIndex {
    /// The bounds-guard `Bool` term `decide (Int.lt (e i)(sliceLen (e s)))` — the trust-ir
    /// model of the live `evalCond`-style guard, reusing the `decide`/`Int.decLt` shape.
    fn guard_bool(&self, e_depth_bvar: u32) -> Expr {
        let e_i = Expr::app(Expr::bvar(e_depth_bvar), Expr::nat_lit(self.i_idx));
        let e_s = Expr::app(Expr::bvar(e_depth_bvar), Expr::nat_lit(self.s_idx));
        let len = Expr::app(cst(TRUSTIR_SLICE_LEN), e_s);
        let p = Expr::apps(cst("Int.lt"), [e_i.clone(), len.clone()]);
        let inst = Expr::apps(cst("Int.decLt"), [e_i, len]);
        Expr::apps(cst("decide"), [p, inst])
    }

    /// The in-bounds element term `idxElem (e s)(e i)`.
    fn elem_term(&self, e_depth_bvar: u32) -> Expr {
        let e_s = Expr::app(Expr::bvar(e_depth_bvar), Expr::nat_lit(self.s_idx));
        let e_i = Expr::app(Expr::bvar(e_depth_bvar), Expr::nat_lit(self.i_idx));
        Expr::apps(cst(TRUSTIR_IDX_ELEM), [e_s, e_i])
    }
}

/// The GENUINE bounds-guard refinement statement, MODEL-ONLY: `∀ (e : Env), guard e = true →
/// evalXOperand-select e = idxElem (e s)(e i)`, where the select is the `Bool.rec`-driven
/// `if (i < sliceLen s) then idxElem s i else dflt`. Built so the TRUE arm reduces to the
/// element. The hypothesis `guard e = true` is GENUINELY USED (it is what `Bool.rec`'s TRUE
/// minor consumes). A wrong RHS (e.g. `dflt`) is NOT def-eq to the reduced TRUE arm ⇒ rejected.
fn guarded_index_refinement(gi: &IrGuardedIndex, claimed_rhs: Option<&Expr>) -> (Expr, Expr) {
    let bd = || BinderData::from(BinderInfo::Default);
    // The select `Bool.rec (λ_.Int) dflt (idxElem s i) (guard)` — the trust-ir model of the
    // guarded return. Under `λ e λ hg`: hg = 0, e = 1.
    let select_at = |e_bvar: u32| {
        let bool_rec =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let dflt = int_lit(gi.dflt);
        let elem = gi.elem_term(e_bvar);
        let guard = gi.guard_bool(e_bvar);
        Expr::apps(bool_rec, [int_motive, dflt, elem, guard])
    };

    // STATEMENT: ∀ (e : Env), guard e = true → select = idxElem (e s)(e i).
    let statement = {
        // Under `λ e`: e = 0. guard e = true.
        let guard0 = gi.guard_bool(0);
        let guard_eq = eq_bool_true(guard0);
        // Under `λ e λ hg`: hg = 0, e = 1. select = idxElem (e s)(e i).
        let lhs = select_at(1);
        let rhs = claimed_rhs.cloned().unwrap_or_else(|| gi.elem_term(1));
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), lhs, rhs],
        );
        Expr::pi(bd(), env_ty(), Expr::pi(bd(), guard_eq, eq))
    };

    // PROOF (genuine, uses the guard hypothesis): TRANSPORT the select's scrutinee from `guard`
    // to `Bool.true` via `congrArg` over the guard equality `hg`, then ι-reduce. Concretely:
    //   congrArg (λ x:Bool. Bool.rec (λ_.Int) dflt elem x) hg
    //     : (Bool.rec … guard) = (Bool.rec … Bool.true)
    // and the RHS `Bool.rec … Bool.true` ι-reduces to `elem` (the TRUE minor), so the term has
    // type `select = elem` — EXACTLY the statement codomain. This GENUINELY USES `hg`: with a
    // FALSE guard the transport target would be `Bool.rec … Bool.false ≡ dflt ≠ elem`, so a wrong
    // (else-arm `dflt`) claim is NOT def-eq ⇒ KernelRejected. Under `λ e λ hg`: hg = 0, e = 1.
    let proof = {
        // f := λ (x : Bool). Bool.rec (λ_.Int) dflt elem x  — under `λ e λ hg λ x`: x=0, hg=1,
        // e=2, so `elem`/`dflt` use depth 2 (the `λ x` adds ONE binder over the `λ e λ hg`
        // depth-2 context).
        let f = {
            let bool_rec =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
            let select_x = Expr::apps(
                bool_rec,
                [int_motive, int_lit(gi.dflt), gi.elem_term(2), Expr::bvar(0)],
            );
            Expr::lam(bd(), cst("Bool"), select_x)
        };
        // @congrArg.{1,1} Bool Int guard Bool.true f hg : (Bool.rec … guard) = (Bool.rec … true).
        //   Under `λ e λ hg`: guard = guard_bool(1), hg = bvar(0).
        let l1 = Level::succ(Level::zero());
        let g = gi.guard_bool(1);
        let congr = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            [cst("Bool"), int_ty(), g, cst("Bool.true"), f, Expr::bvar(0)],
        );
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), eq_bool_true(gi.guard_bool(0)), congr))
    };
    let _ = select_at; // (select term inlined in the statement above)
    (statement, proof)
}

/// Check the BOUNDS-GUARD refinement for a `guarded_index`-shape return against the real
/// clean-kernel, modulo 3. GENUINE + MODEL-ONLY: under the bounds guard `i < sliceLen s`, the
/// guarded select reduces to the in-bounds element `idxElem (e s)(e i)`; the proof case-splits
/// the guard (`Bool.rec`) and USES the guard hypothesis (TRUE arm). Fail-closed: a wrong RHS
/// (the `dflt` else-arm) is NOT def-eq to the reduced TRUE arm ⇒ KernelRejected.
#[must_use]
pub fn check_guarded_index_refinement(gi: &IrGuardedIndex) -> RefinementVerdict {
    if gi.s_idx == gi.i_idx {
        return RefinementVerdict::KernelRejected("guarded-index: slice ≡ index".to_string());
    }
    let (statement, proof) = guarded_index_refinement(gi, None);
    check_refinement_decl(
        "Trust.TrustIr.Refinement.guarded_index_bounds",
        Some(statement),
        Some(proof),
    )
}

/// The canonical `guarded_index` return `if i < s.len() { s[i] } else { 0 }` over env indices
/// `s`, `i`.
#[cfg(test)]
fn example_guarded_index(s_idx: u64, i_idx: u64) -> IrGuardedIndex {
    IrGuardedIndex { s_idx, i_idx, dflt: 0 }
}

/// A trust-ir bounds-guarded CONSTANT-index slice return `if s.len() > k { s[k] } else
/// { dflt }` (equivalently `if k < s.len() { … }`) — the `clamp_idx` shape, the LAST
/// MirSem-fallback shape the 2026-07-02 fallback census found (`IrGuardedIndex` requires a
/// Var index; a literal `k` fail-closed). The guard is `k < sliceLen s` and the in-bounds
/// value is `idxElem s k`, with `k` a LITERAL (`int_lit`), not an env read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IrGuardedConstIndex {
    /// The slice (handle) env index `s`.
    pub s_idx: u64,
    /// The LITERAL index `k` (must be ≥ 0; a negative literal index declines).
    pub k: i128,
    /// The else-arm default.
    pub dflt: i128,
}

impl IrGuardedConstIndex {
    /// The bounds-guard `Bool` term `decide (Int.lt k (sliceLen (e s)))`.
    fn guard_bool(&self, e_depth_bvar: u32) -> Expr {
        let k = int_lit(self.k);
        let e_s = Expr::app(Expr::bvar(e_depth_bvar), Expr::nat_lit(self.s_idx));
        let len = Expr::app(cst(TRUSTIR_SLICE_LEN), e_s);
        let p = Expr::apps(cst("Int.lt"), [k.clone(), len.clone()]);
        let inst = Expr::apps(cst("Int.decLt"), [k, len]);
        Expr::apps(cst("decide"), [p, inst])
    }

    /// The in-bounds element term `idxElem (e s) k`.
    fn elem_term(&self, e_depth_bvar: u32) -> Expr {
        let e_s = Expr::app(Expr::bvar(e_depth_bvar), Expr::nat_lit(self.s_idx));
        Expr::apps(cst(TRUSTIR_IDX_ELEM), [e_s, int_lit(self.k)])
    }
}

/// The CONSTANT-index bounds-guard refinement — the [`guarded_index_refinement`] statement
/// and proof with the index a LITERAL `k`: `∀ (e : Env), decide (k < sliceLen (e s)) = true
/// → (if guard then idxElem s k else dflt) = idxElem (e s) k`. Same genuine `congrArg`
/// guard-transport proof (the hypothesis is what `Bool.rec`'s TRUE minor consumes); a wrong
/// RHS (the `dflt` else-arm) is NOT def-eq ⇒ KernelRejected.
fn guarded_const_index_refinement(
    gk: &IrGuardedConstIndex,
    claimed_rhs: Option<&Expr>,
) -> (Expr, Expr) {
    let bd = || BinderData::from(BinderInfo::Default);
    let statement = {
        let guard0 = gk.guard_bool(0);
        let guard_eq = eq_bool_true(guard0);
        let lhs = {
            let bool_rec =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
            Expr::apps(bool_rec, [int_motive, int_lit(gk.dflt), gk.elem_term(1), gk.guard_bool(1)])
        };
        let rhs = claimed_rhs.cloned().unwrap_or_else(|| gk.elem_term(1));
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), lhs, rhs],
        );
        Expr::pi(bd(), env_ty(), Expr::pi(bd(), guard_eq, eq))
    };
    let proof = {
        let f = {
            let bool_rec =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
            let select_x = Expr::apps(
                bool_rec,
                [int_motive, int_lit(gk.dflt), gk.elem_term(2), Expr::bvar(0)],
            );
            Expr::lam(bd(), cst("Bool"), select_x)
        };
        let l1 = Level::succ(Level::zero());
        let g = gk.guard_bool(1);
        let congr = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            [cst("Bool"), int_ty(), g, cst("Bool.true"), f, Expr::bvar(0)],
        );
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), eq_bool_true(gk.guard_bool(0)), congr))
    };
    (statement, proof)
}

/// Check the CONSTANT-index bounds-guard refinement (`clamp_idx`) against the real
/// clean-kernel, modulo 3. Fail-closed: a NEGATIVE literal index declines (a slice index is
/// a `usize`; a negative `k` means the recognizer mis-read the shape), and a wrong RHS is
/// KernelRejected exactly as in the Var-index witness.
#[must_use]
pub fn check_guarded_const_index_refinement(gk: &IrGuardedConstIndex) -> RefinementVerdict {
    if gk.k < 0 {
        return RefinementVerdict::KernelRejected(
            "guarded-const-index: negative literal index".to_string(),
        );
    }
    let (statement, proof) = guarded_const_index_refinement(gk, None);
    check_refinement_decl(
        "Trust.TrustIr.Refinement.guarded_const_index_bounds",
        Some(statement),
        Some(proof),
    )
}

/// The canonical UNTOUCHED-LOCAL nested loop the task names:
/// ```text
/// fn nested(n) { let mut t = 0; let mut i = 0;
///   while i < n { let mut j = 0; while j < m { j = j + 1; } i = i + 1; } t }
/// ```
/// Env layout: `Var 0 = n`, `Var 1 = m`, `Var 2 = t`, `Var 3 = i`, `Var 4 = j`. OUTER guard
/// `i < n` = Cmp Lt (Var 3) (Var 0); reset `j := 0`; INNER guard `j < m` = Cmp Lt (Var 4) (Var
/// 1); inner body `j := j+1`; outer counter `i` (Var 3); untouched local `t` (Var 2, = 0). The
/// same shape `mirsem`'s `nested_keep_zero_function` certifies, EXTENDED with the `j := 0`
/// reset (the task's example) — the reset writes `j` (Var 4), NOT the untouched local `t`.
fn example_nested_keep_zero_loop() -> IrNestedLoop {
    IrNestedLoop {
        cond_outer: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(0) },
        cond_inner: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(4), b: IrOperand::Var(1) },
        resets: vec![IrStmt {
            idx: 4, // j := 0
            rvalue: IrRvalue::Use(IrOperand::Const(0)),
        }],
        inner_body: vec![IrStmt {
            idx: 4, // j := j + 1
            rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(1)),
        }],
        counter_idx: 3, // i
        inv: IrNestedInvariant::UntouchedLocal { t_idx: 2, t_const: 0 },
    }
}

/// The canonical MONOTONE nested loop (inner loop MODIFIES the outer-invariant variable):
/// ```text
/// fn sum2d(n) { let mut s = 0; let mut i = 0;
///   while i < n { let mut j = 0; while j < m { s = s + 1; j = j + 1; } i = i + 1; } s }
/// ```
/// Env: `Var 0 = n`, `Var 1 = m`, `Var 2 = s`, `Var 3 = i`, `Var 4 = j`. Inner body `[s := s+1;
/// j := j+1]`; accumulator `s` (Var 2); outer counter `i` (Var 3); lower bound `0 ≤ s`. The
/// same shape `mirsem`'s `sum2d_monotone_function` certifies.
fn example_sum2d_monotone_loop() -> IrNestedLoop {
    IrNestedLoop {
        cond_outer: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(0) },
        cond_inner: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(4), b: IrOperand::Var(1) },
        resets: vec![IrStmt {
            idx: 4, // j := 0
            rvalue: IrRvalue::Use(IrOperand::Const(0)),
        }],
        inner_body: vec![
            // s := s + 1
            IrStmt {
                idx: 2,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(2), IrOperand::Const(1)),
            },
            // j := j + 1
            IrStmt {
                idx: 4,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(1)),
            },
        ],
        counter_idx: 3, // i
        inv: IrNestedInvariant::Monotone { s_idx: 2, c: 0 },
    }
}

/// FAIL-CLOSED probe for the UNTOUCHED-LOCAL nested-loop refinement: claim the invariant pins
/// `t_idx = 4` — but the INNER body `j := j+1` (AND the reset `j := 0`) DOES write local 4. The
/// OUTER preservation's inner `loopInvariantRule` proof is built at `Ir := λ e'. e'[4] = e[4]`,
/// whose codomain `Ir (evalBody e' [j:=j+1])` ι-reduces to `Eq Int ((e' 4)+1) (e 4)` — NOT
/// def-eq to the hypothesis `Eq Int (e' 4) (e 4)`, so `λ e' hr _. hr` is ill-typed ⇒
/// KernelRejected. Returns `true` IFF rejected (the sound outcome) — proving the nested
/// fixpoint GENUINELY reconstructs the certified fact, not `Eq.refl` of a tautology.
#[must_use]
pub fn trustir_nested_loop_refinement_fail_closed() -> bool {
    // Bypass the witness soundness guard; ask the KERNEL directly with the wrong invariant.
    let nlf = example_nested_keep_zero_loop();
    let wrong = IrNestedInvariant::UntouchedLocal { t_idx: 4, t_const: 0 };
    let nlf_wrong = IrNestedLoop { inv: wrong, ..nlf };
    matches!(check_trustir_nested_loop_instance(&nlf_wrong), RefinementVerdict::KernelRejected(_))
}

/// FAIL-CLOSED probe for the MONOTONE nested-loop refinement: claim the lower bound `0 ≤ s`
/// on a loop whose inner body DECREMENTS `s` (`s := s - 1`). The inner preservation builds
/// `Int.le_trans 0 (e' s) ((e' s)+1) hr (Int.le_self_add_one (e' s))` (codomain `0 ≤ (e' s)+1`),
/// but the body's reduced codomain is `0 ≤ (e' s)-1` (`-1` ≠ `+1`) ⇒ NOT def-eq ⇒
/// KernelRejected. Returns `true` IFF rejected — the monotone proof retypes only for an actual
/// non-decreasing inner update. Mirrors `mirsem`'s monotone decrement fail-closed.
#[must_use]
pub fn trustir_monotone_nested_loop_refinement_fail_closed() -> bool {
    let base = example_sum2d_monotone_loop();
    let nlf = IrNestedLoop {
        inner_body: vec![
            // s := s - 1  (DECREMENT — breaks the monotone lower bound `0 ≤ s`)
            IrStmt {
                idx: 2,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Sub, IrOperand::Var(2), IrOperand::Const(1)),
            },
            // j := j + 1
            IrStmt {
                idx: 4,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(4), IrOperand::Const(1)),
            },
        ],
        ..base
    };
    matches!(check_trustir_nested_loop_instance(&nlf), RefinementVerdict::KernelRejected(_))
}

/// Build the full trust-ir anchor environment: prelude + the BinOp POC + the
/// straight-line `Operand`/`UnOp`/`Rvalue`/`Stmt` family + their evaluators + the
/// CONTROL-FLOW `CmpOp`/`Cond`/`Term`/`Block`/`Cfg` family + the LOOP fragment
/// (`stepLoop`/`execLoop`/`stepPreservesInv`/`loopInvariantRule`).
pub fn trustir_env() -> Result<Environment, String> {
    // Trust (perf): fixed VC-independent prelude, previously rebuilt per VC.
    // Memoize once (OnceLock) + hand out an Arc-backed clone — the proven
    // `certification_env` pattern; soundness unchanged (byte-identical clone,
    // every real VC term still fully kernel-checked).
    static MEMO: std::sync::OnceLock<Result<Environment, String>> = std::sync::OnceLock::new();
    MEMO.get_or_init(trustir_env_uncached).clone()
}

fn trustir_env_uncached() -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    // Trust: RE-ANCHOR loop-breadth increment — the constructive Int-order lemma suite
    // (`Int.le_trans`/`Int.le_self_add_one`/`Int.add_le_add_right`/`Int.add_le_add_left`/
    // `Int.ofNat_zero_le`, all `Declaration::Theorem` with EMPTY domain-axiom closure, so the
    // anchor stays ⊆ the 3 foundational axioms). The COUNTER class already only needed
    // `Int.le_trans`/`Int.le_self_add_one` (in `with_prelude`); the OTHER loop classes
    // (countdown's `Int.add_le_add_right`, stride's `Int.ofNat_zero_le`/`Int.add_le_add_left`)
    // need this idempotent init. Mirrors `mirsem.rs`'s `init_int_ord_lemmas()` call for the
    // same lemmas. Idempotent: re-init is a no-op.
    env.init_int_ord_lemmas().map_err(|e| format!("init_int_ord_lemmas: {e:?}"))?;
    // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — registered FIRST (before any decl that
    // might reference the name) so `Int.shiftRight` is a resolvable constant by the
    // time `register_eval_bin`/`register_eval_rvalue` syntactically reference it.
    // Mirrors `mirsem::mirsem_env`'s `register_int_bitwise`-first ordering.
    register_int_shr(&mut env)?;
    // Trust: M6 rung 9, ANCHOR BitAnd — registered alongside `Int.shiftRight`, same
    // reasoning: `Int.land` must be resolvable before `register_eval_bin`/
    // `register_eval_rvalue` reference it.
    register_int_land(&mut env)?;
    // POC scalar BinOp anchor.
    register_binop_inductive(&mut env)?;
    register_eval_bin(&mut env)?;
    // Trust: field-read leaf — `Trust.TrustIr.idxElem`/`sliceLen` are registered HERE
    // (moved earlier than their original position in the SLICE-INDEX fragment below) so
    // `register_eval_operand`'s NEW `Field` arm (which references `TRUSTIR_IDX_ELEM`) can
    // resolve the constant. `register_idx_elem_ir` is idempotent and depends on nothing but
    // the prelude's `Int`, so moving it earlier is order-safe; its LATER call site (the
    // SLICE-INDEX fragment, for `XOperand`) is now a no-op re-registration.
    register_idx_elem_ir(&mut env)?;
    // Trust: ITER-NEXT VALUE-PATH — the iterator-cursor opaques (`iter_region`/
    // `iter_has_next`), registered alongside `idxElem`/`sliceLen` so the
    // `<Iter as Iterator>::next` value witness (`trustir_adt::sem_operand_to_expr` /
    // `cond_bool`) can resolve them. Idempotent; modulo-3 preserved (both `Opaque`).
    register_iter_selectors_ir(&mut env)?;
    // Trust: RECORD-WITNESS increment 3 — the RECORD pointer-field selectors
    // (`sliceStart`/`ptrOffset`), registered alongside `idxElem`/`sliceLen`/`iter_region`
    // so the `into_iter`/`slice::Iter::new` record witness (`trustir_adt::struct_field_expr`)
    // can resolve them. Idempotent; modulo-3 preserved (both `Opaque`, empty axiom_deps).
    register_ptr_selectors_ir(&mut env)?;
    // Trust: W19 mutators inc-1 — the FIELD-SETTER post-state surface
    // (`idx_elem_prime`/`set_key_eq`), registered alongside `idxElem`/`iter_seq`/
    // `sliceStart` so the field-setter T-SET/T-FRAME witness
    // (`trustir_adt::build_field_set_obligation`) can resolve them. Idempotent;
    // modulo-3 preserved (`idx_elem_prime` Opaque, `set_key_eq` axiom-free Definition).
    register_field_set_surface_ir(&mut env)?;
    // Straight-line fragment.
    register_operand_inductive(&mut env)?;
    register_eval_operand(&mut env)?;
    register_unop_inductive(&mut env)?;
    register_bnot(&mut env)?;
    // Trust: M6 rung 9, COMPARE-AS-VALUE — `CmpOp` MOVED here (earlier than its
    // original CONTROL-FLOW-FRAGMENT position below) so the NEW `Rvalue.Cmp`
    // constructor (`register_rvalue_inductive`) can reference `Trust.TrustIr.CmpOp`.
    // `register_cmpop_inductive` is idempotent, so its ORIGINAL later call site
    // (still present in the control-flow fragment below, unchanged) is now a
    // no-op re-registration — additive reorder only, mirrors how
    // `mirsem::MIRSEM_RVALUE_CMP`'s own doc names this EXACT same reordering
    // requirement ("the `Cond`/`eval_cond`/`iteI` decls to register BEFORE
    // `Rvalue`").
    register_cmpop_inductive(&mut env)?;
    register_rvalue_inductive(&mut env)?;
    register_eval_rvalue(&mut env)?;
    register_stmt_inductive(&mut env)?;
    register_set(&mut env)?;
    register_eval_body(&mut env)?;
    // Control-flow fragment (this increment) — branch discriminant + blocks + CFG.
    register_cmpop_inductive(&mut env)?;
    register_cond_inductive(&mut env)?;
    register_eval_cond(&mut env)?;
    register_term_inductive(&mut env)?;
    register_block_inductive(&mut env)?;
    register_block_stmts(&mut env)?;
    register_block_term(&mut env)?;
    register_block_at(&mut env)?;
    register_eval_cfg(&mut env)?;
    // Loop fragment (this increment) — the back-edge fixpoint + the Hoare while-rule.
    register_step_loop_ir(&mut env)?;
    register_exec_loop_ir(&mut env)?;
    register_step_preserves_inv_ir(&mut env)?;
    register_loop_invariant_rule_ir(&mut env)?;
    // BREAK / EARLY-EXIT loop fragment (loop-breadth increment) — the combined-guard
    // while-rule (`stepLoopBrk`/`execLoopBrk`/`stepPreservesInvBrk`/`loopInvariantRuleBrk`)
    // + the `Bool.and` left-projection `andLeftTrue`. The base loop fragment is reused
    // unchanged; only the guard scrutinee is swapped to `cond ∧ ¬brk`.
    register_and_left_true_ir(&mut env)?;
    register_step_loop_brk_ir(&mut env)?;
    register_exec_loop_brk_ir(&mut env)?;
    register_step_preserves_inv_brk_ir(&mut env)?;
    register_loop_invariant_rule_brk_ir(&mut env)?;
    // NESTED loop fragment (this increment) — the STRATIFIED outer-statement layer. The flat
    // loop fragment (`stepLoop`/`execLoop`/`loopInvariantRule`) is reused UNCHANGED for the
    // INNER loop; the NEW `OStmt`/`execO`/`stepLoopO`/`execLoopO`/`stepPreservesInvO`/
    // `loopInvariantRuleO` family is the OUTER loop over a `List OStmt` body whose `Loop` arm
    // embeds the inner loop. Registration order MIRRORS `mirsem::nested_loop_env`.
    register_ostmt_inductive(&mut env)?;
    register_exec_o(&mut env)?;
    register_step_loop_o_ir(&mut env)?;
    register_exec_loop_o_ir(&mut env)?;
    register_step_preserves_inv_o_ir(&mut env)?;
    register_loop_invariant_rule_o_ir(&mut env)?;
    // CONDITIONAL-UPDATE (SELECT) loop fragment (last-2 increment) — the STRATIFIED SStmt
    // select-statement layer + `iteI`. The flat `Stmt`/`Rvalue`/`evalBody`/`evalRvalue`/
    // `execLoop` fragment is reused UNCHANGED; the NEW `SStmt`/`execS`/`stepLoopS`/`execLoopS`/
    // `stepPreservesInvS`/`loopInvariantRuleS` family is the SELECT loop over a `List SStmt`
    // body whose `Sel` arm grounds through `iteI`. Closes the `max_scan` CondUpdateGeConst class.
    register_ite_i_ir(&mut env)?;
    register_sstmt_inductive(&mut env)?;
    register_exec_s(&mut env)?;
    register_step_loop_s_ir(&mut env)?;
    register_exec_loop_s_ir(&mut env)?;
    register_step_preserves_inv_s_ir(&mut env)?;
    register_loop_invariant_rule_s_ir(&mut env)?;
    // SLICE-INDEX (BOUNDS-GUARDED) operand fragment (last-2 increment) — the STRATIFIED
    // XOperand operand-extension layer + the opaque `idxElem`/`sliceLen` selectors. The flat
    // `Operand`/`evalOperand` fragment is reused UNCHANGED; `XOperand`/`evalXOperand` model the
    // slice element / length. Closes the `guarded_index` Index/Len class (MODEL-ONLY).
    register_idx_elem_ir(&mut env)?;
    register_xoperand_inductive(&mut env)?;
    register_eval_xoperand(&mut env)?;
    Ok(env)
}

// ---------------------------------------------------------------------------
// Anchor self-audit (parallel to `pin_mirsem_anchor`)
// ---------------------------------------------------------------------------

/// Verdict on registering the trust-ir anchor: do the inductive AND `evalBin`
/// both rest on ⊆ the 3 foundational axioms?
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnchorVerdict {
    /// Anchor pinned; both rest on ⊆ {propext, Quot.sound, Classical.choice}.
    Modulo3,
    /// A declaration carries non-foundational axioms (residue listed).
    Residue(Vec<String>),
    /// The kernel rejected a declaration (a soundness bug if hit).
    KernelRejected(String),
}

/// Pin the trust-ir anchor and audit its axiom closure via the kernel's own
/// `axiom_deps`.
#[must_use]
pub fn pin_trustir_anchor() -> AnchorVerdict {
    let env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [
        // POC scalar BinOp anchor.
        TRUSTIR_BINOP,
        TRUSTIR_BINOP_REC,
        TRUSTIR_EVAL_BIN,
        // Straight-line fragment (this increment).
        TRUSTIR_OPERAND,
        TRUSTIR_OPERAND_REC,
        TRUSTIR_EVAL_OPERAND,
        TRUSTIR_UNOP,
        TRUSTIR_UNOP_REC,
        TRUSTIR_BNOT,
        TRUSTIR_RVALUE,
        TRUSTIR_RVALUE_REC,
        TRUSTIR_EVAL_RVALUE,
        TRUSTIR_STMT,
        TRUSTIR_STMT_REC,
        TRUSTIR_SET,
        TRUSTIR_EVAL_BODY,
        // Control-flow fragment (this increment) — branch discriminant + blocks + CFG.
        TRUSTIR_CMPOP,
        TRUSTIR_CMPOP_REC,
        TRUSTIR_COND,
        TRUSTIR_COND_REC,
        TRUSTIR_EVAL_COND,
        TRUSTIR_TERM,
        TRUSTIR_TERM_REC,
        TRUSTIR_BLOCK,
        TRUSTIR_BLOCK_REC,
        TRUSTIR_BLOCK_STMTS,
        TRUSTIR_BLOCK_TERM,
        TRUSTIR_BLOCK_AT,
        TRUSTIR_EVAL_CFG,
        // Loop fragment (this increment) — back-edge fixpoint + Hoare while-rule.
        TRUSTIR_STEP_LOOP,
        TRUSTIR_EXEC_LOOP,
        TRUSTIR_STEP_PRESERVES_INV,
        TRUSTIR_LOOP_INVARIANT_RULE,
        // BREAK / EARLY-EXIT loop fragment (loop-breadth increment).
        TRUSTIR_AND_LEFT_TRUE,
        TRUSTIR_STEP_LOOP_BRK,
        TRUSTIR_EXEC_LOOP_BRK,
        TRUSTIR_STEP_PRESERVES_INV_BRK,
        TRUSTIR_LOOP_INVARIANT_RULE_BRK,
        // NESTED loop fragment (this increment) — the STRATIFIED OStmt outer-statement layer.
        TRUSTIR_EXEC_O,
        TRUSTIR_STEP_LOOP_O,
        TRUSTIR_EXEC_LOOP_O,
        TRUSTIR_STEP_PRESERVES_INV_O,
        TRUSTIR_LOOP_INVARIANT_RULE_O,
        // CONDITIONAL-UPDATE (SELECT) loop fragment (last-2 increment) — the STRATIFIED SStmt layer.
        TRUSTIR_ITE_I,
        TRUSTIR_EXEC_S,
        TRUSTIR_STEP_LOOP_S,
        TRUSTIR_EXEC_LOOP_S,
        TRUSTIR_STEP_PRESERVES_INV_S,
        TRUSTIR_LOOP_INVARIANT_RULE_S,
        // SLICE-INDEX (BOUNDS-GUARDED) operand fragment (last-2 increment) — the STRATIFIED XOperand layer.
        TRUSTIR_EVAL_XOPERAND,
        // RECORD-WITNESS increment 3 — the pointee-pinned record pointer-field selectors.
        TRUSTIR_SLICE_START,
        TRUSTIR_PTR_OFFSET,
    ] {
        match env.axiom_deps(&Name::from_string(n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return AnchorVerdict::Residue(names);
            }
            None => return AnchorVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    AnchorVerdict::Modulo3
}

// ---------------------------------------------------------------------------
// The REFINEMENT: evalBin (trust-ir denotation) = live ground_int (reflection)
// ---------------------------------------------------------------------------

/// The verdict of checking the trust-ir refinement for one op.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefinementVerdict {
    /// PROVEN modulo 3: `∀ a b. evalBin E op 0 1 = ground_int(<a OP b>)`
    /// kernel-checks and its axiom closure ⊆ the 3 foundational axioms.
    ProvenModulo3,
    /// Type-checks, but depends on these non-foundational axioms.
    Residue(Vec<String>),
    /// The kernel rejected the refinement proof (the fail-closed outcome for a
    /// wrong claim; a soundness bug for a true one).
    KernelRejected(String),
}

/// The total `Env` binding param-index 0 ↦ `bvar(a)` and every successor index
/// ↦ `bvar(b)`:
///
/// ```text
/// λ (k : Nat). Nat.rec.{1} (λ_:Nat. Int) a (λ (_ : Nat) (_ : Int). b) k
/// ```
///
/// For the two-param POC this binds exactly the slots the reflection references
/// (`_1` = index 0 ↦ a, `_2` = index 1 ↦ b). `a`/`b` are de-Bruijn indices into
/// the OUTER context (the `∀ (a b : Int)` binders); inside `evalBin`'s reduct
/// the env applies to literal `0`/`1`, so the LHS reduces to `Int.<op> a b`.
fn binder_env(a: u32, b: u32) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), nat_ty(), int_ty());
    // succ case: λ(_ : Nat)(_ : Int). b   — b lifted past k + the two succ
    // binders = b + 3.
    let succ_case = Expr::lam(bd(), nat_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(b + 3)));
    // zero case: a lifted past k = a + 1.
    let zero_case = Expr::bvar(a + 1);
    let body = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    Expr::lam(bd(), nat_ty(), body)
}

/// Build the refinement *theorem statement* for op `OP`, as a kernel type:
///
/// ```text
/// ∀ (a b : Int), Trust.TrustIr.evalBin E OP 0 1 = ground_int(<a OP b>)
/// ```
///
/// where `E = binder_env 1 0` (under the two `Int` binders a=bvar(1), b=bvar(0)),
/// `0`/`1` are the `Nat` parameter indices, and the RHS is the LIVE
/// `ground_int(OP.reflected_formula(), {_1 ↦ E 0, _2 ↦ E 1})`. `evalBin E OP 0 1`
/// δ/ι-reduces to `Int.<op> (E 0) (E 1)` — the SAME term `ground_int` emits for
/// `Var "_1"`/`Var "_2"` bound to `E 0`/`E 1` — so the two sides are def-eq.
/// `claimed_op = Some(other)` overrides the RHS op (the fail-closed test).
fn refinement_statement(op: TrustIrBinOp, claimed_op: Option<TrustIrBinOp>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `∀ (a b : Int)`: a = bvar(1), b = bvar(0).
    let env = binder_env(1, 0);
    // Param map: `p0 ↦ bvar(1)` (=a), `p1 ↦ bvar(0)` (=b) — the SAME bare de-Bruijn
    // binders the LIVE grounder emits for `Formula::Var`, IDENTICAL to
    // `mirsem::grounding_params`. `evalBin E OP 0 1` reduces to `Int.<op> (E 0)
    // (E 1)`, and `binder_env 1 0` makes `E 0 → bvar(1)`, `E 1 → bvar(0)` — the
    // same binders — so LHS and RHS are def-eq.
    let mut params: HashMap<String, Expr> = HashMap::new();
    params.insert(param_name(0), Expr::bvar(1));
    params.insert(param_name(1), Expr::bvar(0));

    // LHS: evalBin E OP 0 1
    let lhs = Expr::apps(
        cst(TRUSTIR_EVAL_BIN),
        [env, op.ctor_expr(), Expr::nat_lit(0), Expr::nat_lit(1)],
    );
    // RHS: ground_int of the (possibly overridden) reflected formula.
    let rhs_op = claimed_op.unwrap_or(op);
    let rhs = ground_int(&rhs_op.reflected_formula(), &params)?;

    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    // ∀ (a b : Int), body
    let body = Expr::pi(bd(), int_ty(), body); // binds b
    let body = Expr::pi(bd(), int_ty(), body); // binds a
    Some(body)
}

/// Build the refinement *proof term*: `λ (a b : Int). @Eq.refl Int (ground_int(<a OP b>))`.
/// `evalBin E OP 0 1` reduces to the grounded term, so reflexivity AT the grounded
/// term inhabits the equality. (The proof always uses the TRUE op — when a wrong
/// `claimed_op` is supplied to the statement, this refl proof has the true type and
/// will NOT match the wrong statement, so the kernel rejects it. That is the
/// fail-closed mechanism.)
fn refinement_proof(op: TrustIrBinOp) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut params: HashMap<String, Expr> = HashMap::new();
    params.insert(param_name(0), Expr::bvar(1));
    params.insert(param_name(1), Expr::bvar(0));
    let rhs = ground_int(&op.reflected_formula(), &params)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    let refl = Expr::lam(bd(), int_ty(), refl); // λ b
    let refl = Expr::lam(bd(), int_ty(), refl); // λ a
    Some(refl)
}

/// Check the trust-ir refinement for one op against the REAL clean-kernel:
/// register the anchor, build the GROUNDER-CONNECTED statement and the
/// reflexivity proof, `check_type`, register, and audit the axiom closure.
///
/// `ProvenModulo3` means: the term the LIVE `clean_ground::ground_int` grounds
/// `param0 OP param1` to is EXACTLY what the trust-ir-keyed Clean denotation
/// `evalBin` evaluates the op to — kernel-verified modulo 3. The faithfulness is
/// now stated RELATIVE TO a denotation of trust-ir's universal `BinOp` syntax,
/// not the bespoke `Trust.MirSem`.
#[must_use]
pub fn check_trustir_refinement(op: TrustIrBinOp) -> RefinementVerdict {
    check_trustir_refinement_inner(op, None)
}

fn check_trustir_refinement_inner(
    op: TrustIrBinOp,
    claimed_op: Option<TrustIrBinOp>,
) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let Some(statement) = refinement_statement(op, claimed_op) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this op's reflected formula".to_string(),
        );
    };
    let Some(proof) = refinement_proof(op) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this op's reflected formula".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.binop_adequacy");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// FAIL-CLOSED probe: claim that `Add` refines the `Sub` grounding. The refl proof
/// has the `Add`-grounded type (`Int.add a b`) but the statement demands the
/// `Sub` grounding (`Int.sub a b`), so the kernel MUST reject. Returns `true`
/// IFF the kernel rejected (the sound outcome).
#[must_use]
pub fn trustir_refinement_fail_closed() -> bool {
    matches!(
        check_trustir_refinement_inner(TrustIrBinOp::Add, Some(TrustIrBinOp::Sub)),
        RefinementVerdict::KernelRejected(_)
    )
}

// ---------------------------------------------------------------------------
// STRAIGHT-LINE REFINEMENT — the grounder bridge for operand / rvalue / body.
//
// The reconciliation (identical to `mirsem.rs`'s GROUNDER-CONNECTED bridge): the LIVE
// grounder maps `Formula::Var(name)` to a BARE de-Bruijn binder, while `evalOperand e
// (Var i)` ι-reduces to the ENV APPLICATION `e i`. We reconcile by supplying a SPECIFIC
// `e` — a `Trust.TrustIr.set`-chain over the referenced PARAMETER indices so that `e p_i`
// ι-reduces to EXACTLY the `i`-th `Int` binder (the SAME binder `ground_int` emits for
// `Var name`). Then both sides are def-eq by reflexivity. This is NOT papering over the
// mismatch — it pins the precise `e` under which the trust-ir evaluator and the live
// grounder denote the same Int.
// ---------------------------------------------------------------------------

/// A closed base env `fun (_ : Nat) => Int.ofNat 0` (the floor the `set`-chain overwrites).
fn base_env_expr() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    Expr::lam(bd(), nat_ty(), int_lit(0))
}

/// The env `e` binding each `indices[i]` to `binder_of(i)`, via a
/// `Trust.TrustIr.set`-chain over the closed base env. Because the indices are DISTINCT,
/// `e p_i` ι-reduces (through the `set`-chain, `Nat.beq p_j p_i → true` only at j=i) to
/// `binder_of(i)`.
fn grounding_env_expr(indices: &[u64], binder_of: &dyn Fn(usize) -> Expr) -> Expr {
    let mut e = base_env_expr();
    for (i, p) in indices.iter().enumerate() {
        e = Expr::apps(cst(TRUSTIR_SET), [e, Expr::nat_lit(*p), binder_of(i)]);
    }
    e
}

/// The de-Bruijn grounding `params` map for the LIVE grounder over `indices`, under
/// `indices.len()` leading `Int` binders. FIRST-bound variable is the OUTERMOST binder
/// (highest de-Bruijn index) — IDENTICAL to `mirsem::grounding_params`. `param_name(p_i)`
/// maps to `bvar(n-1-i)`, the same binder `grounding_env_expr` writes at `p_i`.
fn grounding_params(indices: &[u64]) -> HashMap<String, Expr> {
    let n = indices.len();
    let mut m = HashMap::new();
    for (i, p) in indices.iter().enumerate() {
        m.insert(param_name(*p), Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    }
    m
}

/// Live-ground a reflected `Formula` through `clean_ground::ground_int` under the
/// de-Bruijn binders for `indices`. `None` (fail closed) if the live grounder declines
/// the formula (outside the grounded fragment, e.g. a `Not`).
fn live_ground_int(f: &trust_types::Formula, indices: &[u64]) -> Option<Expr> {
    ground_int(f, &grounding_params(indices))
}

/// The grounding env over `indices`, mapping `indices[i]` to the de-Bruijn binder
/// `bvar(n-1-i)` (the convention `grounding_params` uses). `pub(crate)` for the
/// BRANCHY call-arm sub-axis (`trustir_call::check_branch_call_refinement` binds
/// the SAME `∀`-env convention over its params PLUS each call arm's `ret_idx`).
pub(crate) fn refinement_env(indices: &[u64]) -> Expr {
    let n = indices.len();
    grounding_env_expr(indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)))
}

// --- OPERAND refinement (`evalOperand`) ------------------------------------

/// Build the operand refinement statement, GROUNDER-CONNECTED:
///
/// ```text
/// ∀ (x_0 … x_{n-1} : Int), evalOperand E op = ground_int(op.to_formula())
/// ```
///
/// `E` binds each referenced var index to its binder; `evalOperand E (Var p_i)`
/// ι-reduces to `x_i`, the SAME binder `ground_int` emits. A `Const c` carries no
/// binder: both sides are the closed literal. `claimed` overrides the RHS (fail-closed).
fn operand_refinement_statement(op: &IrOperand, claimed: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    op.var_indices(&mut indices);
    let n = indices.len();
    let env = refinement_env(&indices);
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [env, op.to_operand_expr()]);
    let rhs = match claimed {
        Some(e) => e.clone(),
        None => live_ground_int(&op.to_formula(), &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    Some(body)
}

fn operand_refinement_proof(op: &IrOperand) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    op.var_indices(&mut indices);
    let n = indices.len();
    let rhs = live_ground_int(&op.to_formula(), &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the OPERAND refinement `evalOperand E op = ground_int(op.to_formula())`
/// against the real clean-kernel, modulo 3. Grounder-connected for every operand
/// (`Var`/`Const`).
#[must_use]
pub fn check_operand_refinement(op: &IrOperand) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.operand_adequacy",
        operand_refinement_statement(op, None),
        operand_refinement_proof(op),
    )
}

// --- OPERAND refinement, MODEL-ONLY (Trust: THE LIFT) ----------------------

/// Build the MODEL-ONLY operand refinement statement (Trust: THE LIFT): `∀ x⃗,
/// evalOperand E op = operand_denotation(op, E)`. Unlike
/// [`operand_refinement_statement`], the RHS is the trust-ir-MODEL denotation
/// ([`operand_denotation`] — the SAME term [`IrRvalue::denotation`]'s `Use` arm
/// draws on), NOT the live grounder — used for a `Field` operand, whose
/// `Formula::Select` reflection the LIVE shared grounder resolves to a DIFFERENT
/// opaque (`Trust.MirSem.idx_elem`, not `Trust.TrustIr.idxElem` — see
/// [`IrOperand::Field`]'s doc). `evalOperand E op` ι-reduces to that exact model
/// term, so the proof is reflexivity; a WRONG model RHS still fails closed.
fn operand_model_statement(op: &IrOperand, claimed: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    op.var_indices(&mut indices);
    let n = indices.len();
    let env = refinement_env(&indices);
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [env, op.to_operand_expr()]);
    let denot_env =
        grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let rhs = claimed.cloned().unwrap_or_else(|| operand_denotation(op, &denot_env));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    body
}

fn operand_model_proof(op: &IrOperand) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    op.var_indices(&mut indices);
    let n = indices.len();
    let denot_env =
        grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let rhs = operand_denotation(op, &denot_env);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    refl
}

/// MODEL-ONLY operand refinement (Trust: THE LIFT): `evalOperand E op =
/// operand_denotation(op, E)` (the trust-ir model term, NOT the live grounder). For
/// a `Field` operand this is the strongest statement available (no
/// `Trust.TrustIr.idxElem`-connected live-grounder arm). Still genuine (relates
/// `evalOperand` to the model `idxElem` term, fail-closed) but NOT
/// grounder-connected — the SAME honesty tier [`check_rvalue_refinement_model`] /
/// [`check_body_refinement_model`] already carry for a `Field`/`Not` operand
/// elsewhere. Used as the fallback witness in the call-arg lane
/// (`prove::call_return_fully_faithful_via_trustir`) when an arg is a `Field`
/// operand (`IrOperand::is_grounder_connected() == false`); every `Var`/`Const`
/// arg still certifies via the GROUNDER-CONNECTED [`check_operand_refinement`],
/// unchanged.
#[must_use]
pub fn check_operand_refinement_model(op: &IrOperand) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.operand_model",
        Some(operand_model_statement(op, None)),
        Some(operand_model_proof(op)),
    )
}

// --- RVALUE refinement (`evalRvalue`) --------------------------------------

/// Build the rvalue refinement statement, GROUNDER-CONNECTED for the grounder-backed
/// arms (`Use`/`BinaryOp`/`UnaryOp Neg`):
///
/// ```text
/// ∀ x⃗, evalRvalue E R = ground_int(R.to_formula())
/// ```
///
/// `None` when the live grounder declines `R.to_formula()` (e.g. a `UnaryOp Not`,
/// which has no integer-grounder arm — see [`check_rvalue_refinement_model`]).
fn rvalue_refinement_statement(rv: &IrRvalue, claimed: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    rv.var_indices(&mut indices);
    let n = indices.len();
    let env = refinement_env(&indices);
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_RVALUE), [env, rv.to_rvalue_expr()]);
    let rhs = match claimed {
        Some(e) => e.clone(),
        None => live_ground_int(&rv.to_formula(), &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    Some(body)
}

fn rvalue_refinement_proof(rv: &IrRvalue) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    rv.var_indices(&mut indices);
    let n = indices.len();
    let rhs = live_ground_int(&rv.to_formula(), &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the RVALUE refinement against the live grounder, modulo 3. GROUNDER-CONNECTED:
/// the RHS is the EXACT term `clean_ground::ground_int` emits for `R.to_formula()`.
/// Fail-closed (`KernelRejected`) for an rvalue the live grounder declines (a `Not`,
/// whose model-only refinement is [`check_rvalue_refinement_model`]).
#[must_use]
pub fn check_rvalue_refinement(rv: &IrRvalue) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.rvalue_adequacy",
        rvalue_refinement_statement(rv, None),
        rvalue_refinement_proof(rv),
    )
}

/// Build the MODEL-ONLY rvalue refinement statement: `∀ x⃗, evalRvalue E R = R.denotation`.
/// Unlike [`rvalue_refinement_statement`], the RHS is the trust-ir-MODEL denotation
/// (`IrRvalue::denotation`), NOT the live grounder — used for `UnaryOp Not`, whose
/// `bnot` has no live-grounder counterpart. `evalRvalue E R` ι-reduces to that exact
/// model term, so the proof is reflexivity; a WRONG model RHS still fails closed.
fn rvalue_model_statement(rv: &IrRvalue, claimed: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    rv.var_indices(&mut indices);
    let n = indices.len();
    let env = refinement_env(&indices);
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_RVALUE), [env, rv.to_rvalue_expr()]);
    let denot_env =
        grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let rhs = claimed.cloned().unwrap_or_else(|| rv.denotation(&denot_env));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    body
}

fn rvalue_model_proof(rv: &IrRvalue) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    rv.var_indices(&mut indices);
    let n = indices.len();
    let denot_env =
        grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let rhs = rv.denotation(&denot_env);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    refl
}

/// MODEL-ONLY rvalue refinement: `evalRvalue E R = R.denotation` (the trust-ir model
/// term, NOT the live grounder). For `UnaryOp Not` this is the strongest statement
/// available (no integer `Not` live-grounder arm). Still genuine (relates `evalRvalue`
/// to the model `bnot` term, fail-closed) but NOT grounder-connected.
#[must_use]
pub fn check_rvalue_refinement_model(rv: &IrRvalue) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.rvalue_model",
        Some(rvalue_model_statement(rv, None)),
        Some(rvalue_model_proof(rv)),
    )
}

// --- BODY refinement (`evalBody` — the straight-line statement sequence) ----

/// Build the BODY refinement statement, GROUNDER-CONNECTED:
///
/// ```text
/// ∀ (x_0 … x_{n-1} : Int),
///   evalOperand (evalBody E stmts) (Var ret) = ground_int(<inlined return formula>)
/// ```
///
/// `E` binds each function PARAMETER index to its binder; `evalBody E stmts` threads
/// the env through the SSA assignments (each `set`s its temp to `evalRvalue`), and the
/// final `evalOperand … (Var ret)` looks up the returned temp — which ι-reduces
/// (through the `set`-chain and the nested `evalRvalue`s) to the nested `Int.<op>` tree
/// the live grounder independently emits for the INLINED return formula
/// (`IrBody::inlined_return_formula`). The two sides are the same nested term, def-eq.
/// `None` if the returned index is unassigned or a referenced temp is undefined, or the
/// live grounder declines the inlined formula (e.g. the body contains a `Not`).
fn body_refinement_statement(body: &IrBody, claimed: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    // Must return an ASSIGNED temp (a genuine straight-line body), else there is no
    // env-threading content to relate.
    body.return_stmt()?;
    // GROUNDER-CONNECTED gate: a body with a non-groundable op (`Not`) has no live
    // grounder RHS — fail closed here rather than via the grounder declining later.
    if !body.is_grounder_connected() {
        return None;
    }
    let indices = body.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    // evalBody E stmts
    let threaded = Expr::apps(cst(TRUSTIR_EVAL_BODY), [env, body.to_stmts_expr()]);
    // evalOperand (evalBody E stmts) (Var ret)
    let ret_operand = IrOperand::Var(body.ret).to_operand_expr();
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [threaded, ret_operand]);
    let rhs = match claimed {
        Some(e) => e.clone(),
        None => live_ground_int(&body.inlined_return_formula()?, &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut stmt = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        stmt = Expr::pi(bd(), int_ty(), stmt);
    }
    Some(stmt)
}

fn body_refinement_proof(body: &IrBody) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    body.return_stmt()?;
    let indices = body.param_indices();
    let n = indices.len();
    let rhs = live_ground_int(&body.inlined_return_formula()?, &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the BODY refinement for a straight-line trust-ir body against the live
/// grounder, modulo 3. GENUINE + GROUNDER-CONNECTED: the LHS runs the SSA trace through
/// the trust-ir operational step `evalBody` (threading the env, `set`ting each temp to
/// its `evalRvalue`), and the RHS is the LIVE `ground_int` of the inlined return
/// formula. They are equal because `evalBody`'s env-threading reduction reconstructs
/// exactly the nested term the §6 grounder produces. Fail-closed for a body with an
/// unassigned return, an undefined temp, or a non-groundable op (`Not`).
#[must_use]
pub fn check_body_refinement(body: &IrBody) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.body_adequacy",
        body_refinement_statement(body, None),
        body_refinement_proof(body),
    )
}

// --- BODY refinement, MODEL-ONLY (Trust: field-read leaf) --------------------

/// The MODEL-ONLY body-refinement statement (Trust: field-read leaf): relates
/// `evalBody`'s reduct DIRECTLY to the return statement's own `IrRvalue::denotation`
/// (the trust-ir MODEL term), bypassing `clean_ground`/`live_ground_int` entirely. Used
/// when the body is NOT live-grounder-connected (contains a `Field` operand — see
/// [`IrOperand::Field`]'s doc). Scoped to the single-statement straight-line bodies
/// `straight_line_ir_body` builds (every shape it produces collapses to ONE `_ret :=
/// rvalue` statement, so relating `evalBody`'s reduct to THAT statement's own
/// denotation is exact — no multi-statement SSA inlining is needed here).
fn body_model_refinement_statement(body: &IrBody) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let ret_stmt = body.return_stmt()?;
    let indices = body.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    let threaded = Expr::apps(cst(TRUSTIR_EVAL_BODY), [env.clone(), body.to_stmts_expr()]);
    let ret_operand = IrOperand::Var(body.ret).to_operand_expr();
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [threaded, ret_operand]);
    let rhs = ret_stmt.rvalue.denotation(&env);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut stmt = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        stmt = Expr::pi(bd(), int_ty(), stmt);
    }
    Some(stmt)
}

fn body_model_refinement_proof(body: &IrBody) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let ret_stmt = body.return_stmt()?;
    let indices = body.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    let rhs = ret_stmt.rvalue.denotation(&env);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the MODEL-ONLY BODY refinement (Trust: field-read leaf) for a straight-line
/// trust-ir body against the trust-ir MODEL denotation, modulo 3 — the SAME honesty
/// tier as `check_rvalue_refinement_model` (`UnaryOp Not`): GENUINE (the LHS runs the
/// SAME `evalBody` operational step; the RHS is the Rust-computed MODEL term
/// `IrRvalue::denotation`, BYTE-IDENTICAL to what `evalRvalue`/`evalOperand` reduce to —
/// so the `Eq.refl` proof is a real kernel reduction, not a dressed-up tautology),
/// fail-closed (`None`/`KernelRejected` on an unassigned return), but NOT
/// grounder-connected — it does not relate the trust-ir denotation to the LIVE
/// `clean_ground::ground_int` the §6 VC/reflection pipeline actually emits (unreachable
/// for a `Field` operand: `ground_int`'s `Formula::Select` arm hardcodes
/// `Trust.MirSem.idx_elem`, a DIFFERENT opaque than `Trust.TrustIr.idxElem` — see
/// [`IrOperand::Field`]'s doc). Used as the FALLBACK witness in
/// `straight_line_fully_faithful_via_trustir` when [`check_body_refinement`] declines
/// (i.e. exactly when the body contains a `Field` operand — every pre-existing
/// grounder-connected shape still certifies via `check_body_refinement` alone; this
/// fallback is never exercised for them).
#[must_use]
pub fn check_body_refinement_model(body: &IrBody) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.body_model",
        body_model_refinement_statement(body),
        body_model_refinement_proof(body),
    )
}

// --- BODY refinement, MULTI-STATEMENT MODEL-ONLY (Trust: M6 rung 9) --------------

/// The MULTI-STATEMENT MODEL-ONLY body-refinement statement (Trust: M6 rung 9,
/// ANCHOR BitAnd + COMPARE-AS-VALUE): the genuine multi-statement generalization of
/// [`body_model_refinement_statement`] (which is scoped — by its own doc — to the
/// SINGLE-statement bodies `straight_line_ir_body` builds). Relates `evalBody`'s
/// reduct to the FULLY-INLINED trust-ir MODEL denotation
/// ([`IrBody::inlined_return_denotation`]) rather than the single return
/// statement's own `denotation` — needed for a genuine SSA CHAIN (`_2 :=
/// (*self).0; _3 := Shr(_2,N); _4 := And(_3,1); _0 := Eq(_4,1)`, `ExprMeta::
/// {has_fvar,has_level_param}`'s shape), where the returned statement's rvalue
/// references an EARLIER temp (`_4`), not a bare parameter — `evalBody`'s
/// reduction is a genuine SEQUENTIAL env-thread (see `register_eval_body`'s
/// `cons_case`: each `step` runs under the PRIOR step's UPDATED env), so its
/// ι-reduction reconstructs EXACTLY the inlined term. Used when
/// [`body_refinement_statement`] declines (the body is not grounder-connected —
/// contains a `Field` leaf) FOR a multi-statement chain
/// [`straight_line_ir_body_chain`] builds (`prove.rs`).
fn body_model_chain_refinement_statement(body: &IrBody, claimed: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    body.return_stmt()?;
    let indices = body.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    let threaded = Expr::apps(cst(TRUSTIR_EVAL_BODY), [env.clone(), body.to_stmts_expr()]);
    let ret_operand = IrOperand::Var(body.ret).to_operand_expr();
    let lhs = Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [threaded, ret_operand]);
    let rhs = match claimed {
        Some(e) => e.clone(),
        None => body.inlined_return_denotation(&env)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut stmt = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        stmt = Expr::pi(bd(), int_ty(), stmt);
    }
    Some(stmt)
}

fn body_model_chain_refinement_proof(body: &IrBody) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    body.return_stmt()?;
    let indices = body.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    let rhs = body.inlined_return_denotation(&env)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the MULTI-STATEMENT MODEL-ONLY BODY refinement (Trust: M6 rung 9) against
/// the trust-ir MODEL denotation, modulo 3 — the genuine multi-statement
/// generalization of [`check_body_refinement_model`]. GENUINE (the LHS runs the
/// SAME `evalBody` operational step over the ACTUAL multi-statement SSA trace; the
/// RHS is the Rust-computed FULLY-INLINED MODEL term
/// [`IrBody::inlined_return_denotation`], provably — not merely claimed — equal to
/// it, so the `Eq.refl` proof is a real kernel reduction), fail-closed
/// (`None`/`KernelRejected` on an unassigned return or an undefined referenced
/// temp), but NOT grounder-connected.
#[must_use]
pub fn check_body_refinement_model_chain(body: &IrBody) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.body_model_chain",
        body_model_chain_refinement_statement(body, None),
        body_model_chain_refinement_proof(body),
    )
}

/// Shared kernel-check driver: register the anchor env, `check_type` the proof against
/// the statement, register the theorem, and audit its axiom closure via the kernel's
/// own `axiom_deps`. `None` statement/proof (the live grounder declined the formula)
/// is fail-closed `KernelRejected`.
fn check_refinement_decl(
    decl_name: &str,
    statement: Option<Expr>,
    proof: Option<Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let (Some(statement), Some(proof)) = (statement, proof) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this formula (outside the grounded fragment)".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string(decl_name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// FAIL-CLOSED probe for the BODY refinement: claim the straight-line body
/// `_2 := a+b; _3 := _2*c; ret _3` grounds to the WRONG inlined formula
/// (`Add(Add(a,b), c)` instead of `Mul(Add(a,b), c)`). The reflexivity proof has the
/// TRUE (`Mul`) type, so the kernel MUST reject the wrong statement. Returns `true` IFF
/// rejected (the sound outcome) — proving the body refinement is GENUINE, not `Eq.refl`
/// of a tautology.
#[must_use]
pub fn trustir_body_refinement_fail_closed() -> bool {
    use trust_types::Formula as F;
    let body = example_body_2_3();
    let indices = body.param_indices();
    // The WRONG inlined formula: Add where the true body is Mul.
    let a = Box::new(F::Var(param_name(0), trust_types::Sort::Int));
    let b = Box::new(F::Var(param_name(1), trust_types::Sort::Int));
    let c = Box::new(F::Var(param_name(4), trust_types::Sort::Int));
    let wrong = F::Add(Box::new(F::Add(a, b)), c);
    let Some(wrong_rhs) = live_ground_int(&wrong, &indices) else {
        return false; // grounder declined the wrong formula — inconclusive, treat as not-rejected
    };
    let statement = body_refinement_statement(&body, Some(&wrong_rhs));
    let proof = body_refinement_proof(&body);
    matches!(
        check_refinement_decl("Trust.TrustIr.Refinement.body_wrong", statement, proof),
        RefinementVerdict::KernelRejected(_)
    )
}

/// The canonical example straight-line body `_2 := a + b; _3 := _2 * c; ret _3` over
/// parameters `a=_0`, `b=_1`, `c=_4` (distinct indices; `_2`/`_3` are SSA temps). Its
/// inlined return formula is `Mul(Add(a, b), c)`.
fn example_body_2_3() -> IrBody {
    IrBody {
        stmts: vec![
            IrStmt {
                idx: 2,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(0), IrOperand::Var(1)),
            },
            IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Mul, IrOperand::Var(2), IrOperand::Var(4)),
            },
        ],
        ret: 3,
    }
}

// ---------------------------------------------------------------------------
// CONTROL-FLOW (BRANCH) REFINEMENT — evalCfg (trust-ir CFG denotation) = live
// ground_int of the branched §6 formula.
//
// The headline of this increment: for a BRANCHING straight-line function (the abs-shape
// `bb0: switch x<0 → bb1 else bb2; bb1: ret -x; bb2: ret x`) prove, modulo 3:
//
//   ∀ x⃗, evalCfg E cfg fuel entry = ground_int(<Ite(Lt(x,0), Neg(x), x)>)
//
// GENUINE + GROUNDER-CONNECTED: the LHS runs the CFG through the trust-ir control-flow
// step `evalCfg` (Nat.rec on fuel → Term.rec dispatch → Bool.rec on the switch), and its
// ι/δ-reduction reconstructs EXACTLY the `Bool.rec (λ_.Int) (g else) (g then)
// (ground_bool cond)` tree the LIVE `clean_ground::ground_int` independently emits for the
// branched `Formula::Ite`. The cfg-fold RECONSTRUCTS the branched ground; it is NOT
// `Eq.refl` of a tautology — a WRONG branch target/value/formula is REJECTED by the
// kernel (`trustir_branch_refinement_fail_closed`).
// ---------------------------------------------------------------------------

/// Build the BRANCH refinement statement, GROUNDER-CONNECTED:
///
/// ```text
/// ∀ (x_0 … x_{n-1} : Int),
///   evalCfg E cfg fuel entry = ground_int(<inlined branched Ite formula>)
/// ```
///
/// `E` binds each CFG PARAMETER index to its binder; `evalCfg E cfg fuel entry` executes
/// the CFG (the literal `fuel`/`entry` drive the `Nat.rec`/lookup to full reduction), and
/// its switch reduces to the `Bool.rec` ite the live grounder emits for the branched
/// `Formula::Ite` (`IrCfg::inlined_return_formula`). `None` (fail-closed) if a block is
/// missing, a temp undefined, the CFG has a non-groundable op (`Not`), the walk exceeds
/// `fuel` (a cycle), or the live grounder declines the inlined formula. `claimed`
/// overrides the RHS (the fail-closed probe).
fn branch_refinement_statement(cfg: &IrCfg, claimed: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    if !cfg.is_grounder_connected() {
        return None;
    }
    let indices = cfg.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    // evalCfg E cfg fuel entry
    let lhs = Expr::apps(
        cst(TRUSTIR_EVAL_CFG),
        [env, cfg.to_cfg_expr(), Expr::nat_lit(cfg.fuel), Expr::nat_lit(cfg.entry)],
    );
    let rhs = match claimed {
        Some(e) => e.clone(),
        None => live_ground_int(&cfg.inlined_return_formula()?, &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut stmt = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        stmt = Expr::pi(bd(), int_ty(), stmt);
    }
    Some(stmt)
}

fn branch_refinement_proof(cfg: &IrCfg) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    if !cfg.is_grounder_connected() {
        return None;
    }
    let indices = cfg.param_indices();
    let n = indices.len();
    let rhs = live_ground_int(&cfg.inlined_return_formula()?, &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the BRANCH refinement for a branching trust-ir CFG against the live grounder,
/// modulo 3. GENUINE + GROUNDER-CONNECTED: the LHS runs the CFG through the trust-ir
/// control-flow step `evalCfg` (Nat.rec on fuel, Term.rec dispatch, Bool.rec on the
/// switch), and the RHS is the LIVE `ground_int` of the inlined branched `Ite` formula.
/// They are equal because `evalCfg`'s cfg-fold reconstructs exactly the nested
/// `Bool.rec` ite the §6 grounder produces. Fail-closed for a CFG the grounder declines.
#[must_use]
pub fn check_branch_refinement(cfg: &IrCfg) -> RefinementVerdict {
    check_refinement_decl(
        "Trust.TrustIr.Refinement.branch_adequacy",
        branch_refinement_statement(cfg, None),
        branch_refinement_proof(cfg),
    )
}

/// The canonical `abs` CFG over parameter `x = _0`:
///
/// ```text
/// bb0:  switch (x < 0) → bb1 (then) else bb2 (else)
/// bb1:  _1 := Neg x;  Return _1        -- the then arm: -x
/// bb2:  Return x                       -- the else arm: x
/// ```
///
/// Its inlined return formula is `Ite(Lt(x,0), Neg(x), x)`. (`fuel = 3` exceeds the
/// longest acyclic path bb0→bb1/bb2, two edges.)
fn example_abs_cfg() -> IrCfg {
    IrCfg {
        blocks: vec![
            // bb0: switch x<0 → bb1 else bb2
            IrBlock {
                stmts: vec![],
                term: IrTerm::Switch(
                    IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(0), b: IrOperand::Const(0) },
                    1,
                    2,
                ),
            },
            // bb1 (then): _1 := Neg x; Return _1
            IrBlock {
                stmts: vec![IrStmt {
                    idx: 1,
                    rvalue: IrRvalue::Un(TrustIrUnOp::Neg, IrOperand::Var(0)),
                }],
                term: IrTerm::Return(IrOperand::Var(1)),
            },
            // bb2 (else): Return x
            IrBlock { stmts: vec![], term: IrTerm::Return(IrOperand::Var(0)) },
        ],
        entry: 0,
        fuel: 3,
    }
}

/// The `sign` CFG over parameter `x = _0` — a NESTED (3-arm) branch exercising a `Switch`
/// whose else arm is itself a `Switch`:
///
/// ```text
/// bb0:  switch (x < 0) → bb1 (ret -1) else bb2
/// bb1:  Return (Const -1)
/// bb2:  switch (x > 0) → bb3 (ret 1) else bb4 (ret 0)
/// bb3:  Return (Const 1)
/// bb4:  Return (Const 0)
/// ```
///
/// Inlined: `Ite(Lt(x,0), -1, Ite(Gt(x,0), 1, 0))`. (`fuel = 5` exceeds the longest
/// acyclic path bb0→bb2→bb3/bb4, three edges.) Test-only (exercised by
/// `trustir_branch_refinement_sign_nested_modulo3`).
#[cfg(test)]
fn example_sign_cfg() -> IrCfg {
    IrCfg {
        blocks: vec![
            IrBlock {
                stmts: vec![],
                term: IrTerm::Switch(
                    IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(0), b: IrOperand::Const(0) },
                    1,
                    2,
                ),
            },
            IrBlock { stmts: vec![], term: IrTerm::Return(IrOperand::Const(-1)) },
            IrBlock {
                stmts: vec![],
                term: IrTerm::Switch(
                    IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(0), b: IrOperand::Const(0) },
                    3,
                    4,
                ),
            },
            IrBlock { stmts: vec![], term: IrTerm::Return(IrOperand::Const(1)) },
            IrBlock { stmts: vec![], term: IrTerm::Return(IrOperand::Const(0)) },
        ],
        entry: 0,
        fuel: 5,
    }
}

/// FAIL-CLOSED probe for the BRANCH refinement: claim the abs CFG grounds to the WRONG
/// branched formula — the arms SWAPPED (`Ite(Lt(x,0), x, Neg(x))`, i.e. the then/else
/// targets reversed). The reflexivity proof has the TRUE (`Neg`-then) type, so the kernel
/// MUST reject the wrong (swapped-arm) statement. Returns `true` IFF rejected (the sound
/// outcome) — proving the branch refinement is GENUINE, the cfg-fold actually reconstructs
/// the branched ground (and a wrong branch target/value would NOT prove).
#[must_use]
pub fn trustir_branch_refinement_fail_closed() -> bool {
    use trust_types::Formula as F;
    let cfg = example_abs_cfg();
    let indices = cfg.param_indices();
    // The WRONG branched formula: arms swapped (then ↔ else) relative to the true CFG.
    let x = || Box::new(F::Var(param_name(0), trust_types::Sort::Int));
    let cond = F::Lt(x(), Box::new(F::Int(0)));
    let neg_x = F::Neg(x());
    // True is Ite(cond, Neg x, x); the WRONG swaps the arms: Ite(cond, x, Neg x).
    let wrong = F::Ite(
        Box::new(cond),
        Box::new(F::Var(param_name(0), trust_types::Sort::Int)),
        Box::new(neg_x),
    );
    let Some(wrong_rhs) = live_ground_int(&wrong, &indices) else {
        return false; // grounder declined the wrong formula — inconclusive
    };
    let statement = branch_refinement_statement(&cfg, Some(&wrong_rhs));
    let proof = branch_refinement_proof(&cfg);
    matches!(
        check_refinement_decl("Trust.TrustIr.Refinement.branch_wrong", statement, proof),
        RefinementVerdict::KernelRejected(_)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The anchor itself rests on ⊆ the 3 foundational axioms.
    #[test]
    fn trustir_anchor_is_modulo3() {
        assert_eq!(pin_trustir_anchor(), AnchorVerdict::Modulo3);
    }

    /// Every supported op's refinement kernel-checks modulo 3 — the trust-ir
    /// denotation agrees with the live grounder.
    #[test]
    fn trustir_refinement_all_ops_modulo3() {
        for op in TrustIrBinOp::ALL {
            assert_eq!(
                check_trustir_refinement(op),
                RefinementVerdict::ProvenModulo3,
                "op {op:?} ({}) did not prove modulo 3",
                op.trust_ir_name(),
            );
        }
    }

    /// The GENUINENESS check: a wrong refinement (Add claimed to ground as Sub)
    /// is REJECTED by the kernel. Not `Eq.refl` of a tautology.
    #[test]
    fn trustir_refinement_is_fail_closed() {
        assert!(
            trustir_refinement_fail_closed(),
            "WRONG refinement (Add≟Sub-grounding) was NOT rejected — soundness hole",
        );
    }

    /// The bijection sanity: our six `TrustIrBinOp` names are exactly the
    /// arithmetic-fragment names of `trust_ir::inst::BinOp`. We cannot depend on
    /// the trust-ir crate here (trust-clean has no such dep), so we assert the
    /// names are the canonical Rust variant identifiers — the structural link the
    /// re-anchor rests on. (A full re-anchor would import `trust_ir::BinOp` and
    /// `match` exhaustively; noted as the next step.) `SRem` — Trust: witness-tier
    /// Rem arm — is keyed to trust-ir's SIGNED (truncated) remainder variant: MIR
    /// `Rem` on signed operands IS SRem semantics by definition, and on unsigned
    /// operands the values are nonnegative, where SRem == URem pointwise — the
    /// honest unsigned story (`URem` itself stays unmapped; a genuinely
    /// wrapping-width unsigned story would need the bitvector fragment). `LShr` —
    /// Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — is keyed to trust-ir's UNSIGNED
    /// (logical) shift-right variant; the SIGNED sibling `AShr` (floor-on-negatives
    /// arithmetic shift) is a DISTINCT real `trust_ir::inst::BinOp` variant that
    /// stays unmapped here (honest — see `TrustIrBinOp::LShr`'s doc).
    #[test]
    fn trustir_binop_names_are_canonical() {
        let names: Vec<&str> = TrustIrBinOp::ALL.iter().map(|o| o.trust_ir_name()).collect();
        assert_eq!(names, vec!["Add", "Sub", "Mul", "SDiv", "SRem", "LShr", "And"]);
        // The Clean constructor names embed the same identifiers.
        for op in TrustIrBinOp::ALL {
            assert!(op.ctor_name().ends_with(op.trust_ir_name()));
        }
    }

    /// Trust: witness-tier Rem arm — the SREM-specific FAIL-CLOSED probe: claiming
    /// that `SRem` refines the `SDiv` grounding (rem denoted as division — two
    /// DISTINCT Opaque prelude heads, `Int.mod` vs `Int.div`) MUST be kernel-
    /// rejected. Pins that the new arm's refinement def-eq is a real semantic
    /// gate over the opaque heads, not a tautology.
    #[test]
    fn trustir_srem_refinement_is_fail_closed_against_sdiv() {
        assert!(
            matches!(
                check_trustir_refinement_inner(TrustIrBinOp::SRem, Some(TrustIrBinOp::SDiv)),
                RefinementVerdict::KernelRejected(_)
            ),
            "WRONG refinement (SRem≟SDiv-grounding) was NOT rejected — soundness hole",
        );
        // And the converse direction (SDiv claimed as the SRem grounding).
        assert!(
            matches!(
                check_trustir_refinement_inner(TrustIrBinOp::SDiv, Some(TrustIrBinOp::SRem)),
                RefinementVerdict::KernelRejected(_)
            ),
            "WRONG refinement (SDiv≟SRem-grounding) was NOT rejected — soundness hole",
        );
    }

    /// Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — the LSHR-specific FAIL-CLOSED probe:
    /// claiming that `LShr` refines the `SDiv` grounding (shift denoted as division —
    /// two DISTINCT Opaque prelude heads, `Int.shiftRight` vs `Int.div`) MUST be
    /// kernel-rejected, both directions. Pins that the new arm's refinement def-eq is
    /// a real semantic gate over the opaque heads, not a tautology — the SAME
    /// genuineness check `trustir_srem_refinement_is_fail_closed_against_sdiv` runs
    /// for `SRem`.
    #[test]
    fn trustir_lshr_refinement_is_fail_closed_against_sdiv() {
        assert!(
            matches!(
                check_trustir_refinement_inner(TrustIrBinOp::LShr, Some(TrustIrBinOp::SDiv)),
                RefinementVerdict::KernelRejected(_)
            ),
            "WRONG refinement (LShr≟SDiv-grounding) was NOT rejected — soundness hole",
        );
        assert!(
            matches!(
                check_trustir_refinement_inner(TrustIrBinOp::SDiv, Some(TrustIrBinOp::LShr)),
                RefinementVerdict::KernelRejected(_)
            ),
            "WRONG refinement (SDiv≟LShr-grounding) was NOT rejected — soundness hole",
        );
    }

    /// Trust: M6 rung 9, ANCHOR BitAnd — the AND-specific FAIL-CLOSED probe: claiming
    /// that `And` refines the `SDiv` grounding (bitwise-and denoted as division — two
    /// DISTINCT Opaque prelude heads, `Int.land` vs `Int.div`) MUST be kernel-rejected,
    /// both directions. Pins that the new arm's refinement def-eq is a real semantic
    /// gate over the opaque heads, not a tautology — the SAME genuineness check the
    /// `SRem`/`LShr` probes run.
    #[test]
    fn trustir_and_refinement_is_fail_closed_against_sdiv() {
        assert!(
            matches!(
                check_trustir_refinement_inner(TrustIrBinOp::And, Some(TrustIrBinOp::SDiv)),
                RefinementVerdict::KernelRejected(_)
            ),
            "WRONG refinement (And≟SDiv-grounding) was NOT rejected — soundness hole",
        );
        assert!(
            matches!(
                check_trustir_refinement_inner(TrustIrBinOp::SDiv, Some(TrustIrBinOp::And)),
                RefinementVerdict::KernelRejected(_)
            ),
            "WRONG refinement (SDiv≟And-grounding) was NOT rejected — soundness hole",
        );
    }

    // -----------------------------------------------------------------------
    // STRAIGHT-LINE FRAGMENT tests (this increment)
    // -----------------------------------------------------------------------

    /// The UnOp bijection: the two integer-fragment `TrustIrUnOp` names are the real
    /// `trust_ir::inst::UnOp` variant identifiers, and the Clean constructor names embed
    /// them.
    #[test]
    fn trustir_unop_names_are_canonical() {
        let names: Vec<&str> = TrustIrUnOp::ALL.iter().map(|o| o.trust_ir_name()).collect();
        assert_eq!(names, vec!["Neg", "Not"]);
        for op in TrustIrUnOp::ALL {
            assert!(op.ctor_name().ends_with(op.trust_ir_name()));
        }
    }

    /// OPERAND refinement: a `Var` and a `Const` both kernel-check modulo 3 against the
    /// live grounder.
    #[test]
    fn trustir_operand_refinement_modulo3() {
        assert_eq!(
            check_operand_refinement(&IrOperand::Var(0)),
            RefinementVerdict::ProvenModulo3,
            "Var operand refinement did not prove modulo 3",
        );
        assert_eq!(
            check_operand_refinement(&IrOperand::Const(7)),
            RefinementVerdict::ProvenModulo3,
            "Const operand refinement did not prove modulo 3",
        );
        assert_eq!(
            check_operand_refinement(&IrOperand::Const(-3)),
            RefinementVerdict::ProvenModulo3,
            "negative Const operand refinement did not prove modulo 3",
        );
    }

    /// RVALUE refinement: `Use`, every `BinaryOp`, and `UnaryOp Neg` are GROUNDER-
    /// CONNECTED and kernel-check modulo 3.
    #[test]
    fn trustir_rvalue_refinement_grounder_connected_modulo3() {
        let cases: Vec<IrRvalue> = vec![
            IrRvalue::Use(IrOperand::Var(0)),
            IrRvalue::Use(IrOperand::Const(5)),
            IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Bin(TrustIrBinOp::Sub, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Bin(TrustIrBinOp::Mul, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Bin(TrustIrBinOp::SDiv, IrOperand::Var(0), IrOperand::Var(1)),
            // Trust: witness-tier Rem arm — grounder-connected via ground_int's F::Rem.
            IrRvalue::Bin(TrustIrBinOp::SRem, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Bin(TrustIrBinOp::SRem, IrOperand::Var(0), IrOperand::Const(3)),
            IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(0), IrOperand::Const(1)),
            IrRvalue::Un(TrustIrUnOp::Neg, IrOperand::Var(0)),
            // Trust: M6 rung 9, ANCHOR BitAnd — grounder-connected via ground_int's
            // BITWISE SHAPE LANE `F::Pred("Int.land",_)` arm.
            IrRvalue::Bin(TrustIrBinOp::And, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Bin(TrustIrBinOp::And, IrOperand::Var(0), IrOperand::Const(1)),
            // Trust: M6 rung 9, COMPARE-AS-VALUE — every `Cmp` op is grounder-connected
            // via ground_int's COMPARE-AS-VALUE arm (`F::Eq/Lt/Le/Gt/Ge/Not(Eq) =>
            // bool_as_int(ground_bool(f))`).
            IrRvalue::Cmp(TrustIrCmpOp::Eq, IrOperand::Var(0), IrOperand::Const(1)),
            IrRvalue::Cmp(TrustIrCmpOp::Ne, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Cmp(TrustIrCmpOp::Lt, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Cmp(TrustIrCmpOp::Le, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Cmp(TrustIrCmpOp::Gt, IrOperand::Var(0), IrOperand::Var(1)),
            IrRvalue::Cmp(TrustIrCmpOp::Ge, IrOperand::Var(0), IrOperand::Var(1)),
        ];
        for rv in cases {
            assert!(rv.is_grounder_connected());
            assert_eq!(
                check_rvalue_refinement(&rv),
                RefinementVerdict::ProvenModulo3,
                "grounder-connected rvalue {rv:?} did not prove modulo 3",
            );
        }
    }

    /// `UnaryOp Not` is NOT grounder-connected (the live grounder has no integer-Not
    /// arm): the grounder-connected check fails closed, but the MODEL-ONLY refinement
    /// against `bnot` proves modulo 3.
    #[test]
    fn trustir_rvalue_not_is_model_only_modulo3() {
        let not_rv = IrRvalue::Un(TrustIrUnOp::Not, IrOperand::Var(0));
        assert!(!not_rv.is_grounder_connected());
        // Grounder-connected path declines (fail-closed: no live integer-Not arm).
        assert!(matches!(check_rvalue_refinement(&not_rv), RefinementVerdict::KernelRejected(_)));
        // Model-only path proves modulo 3 against the opaque `bnot`.
        assert_eq!(
            check_rvalue_refinement_model(&not_rv),
            RefinementVerdict::ProvenModulo3,
            "model-only Not refinement did not prove modulo 3",
        );
    }

    /// BODY refinement (the headline): the 2-statement straight-line body
    /// `_2 := a+b; _3 := _2*c; ret _3` kernel-checks modulo 3 — the trust-ir
    /// operational step `evalBody` threads the env through the SSA trace and its
    /// reduction matches the LIVE grounder's inlined `Mul(Add(a,b),c)`.
    #[test]
    fn trustir_body_refinement_modulo3() {
        let body = example_body_2_3();
        assert_eq!(
            check_body_refinement(&body),
            RefinementVerdict::ProvenModulo3,
            "2-statement straight-line body refinement did not prove modulo 3",
        );
    }

    /// A 3-statement straight-line body `_2 := a+b; _3 := _2*c; _5 := _3 - a; ret _5`
    /// (inlined: `Sub(Mul(Add(a,b),c), a)`) also kernel-checks modulo 3 — deeper
    /// env-threading.
    #[test]
    fn trustir_body_refinement_three_stmts_modulo3() {
        let body = IrBody {
            stmts: vec![
                IrStmt {
                    idx: 2,
                    rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(0), IrOperand::Var(1)),
                },
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(TrustIrBinOp::Mul, IrOperand::Var(2), IrOperand::Var(4)),
                },
                IrStmt {
                    idx: 5,
                    rvalue: IrRvalue::Bin(TrustIrBinOp::Sub, IrOperand::Var(3), IrOperand::Var(0)),
                },
            ],
            ret: 5,
        };
        assert_eq!(
            check_body_refinement(&body),
            RefinementVerdict::ProvenModulo3,
            "3-statement straight-line body refinement did not prove modulo 3",
        );
    }

    /// Trust: M6 rung 9, ANCHOR BitAnd + COMPARE-AS-VALUE — a genuine multi-statement
    /// `And`-then-`Cmp` chain over PARAMETERS ONLY (no field leaf): `_3 := And(p1, p2);
    /// _0 := Eq(_3, p4)` (inlined: `Eq(And(p1,p2), p4)`) is FULLY grounder-connected
    /// and kernel-checks modulo 3 via the GENERIC (already multi-statement-capable)
    /// [`check_body_refinement`] — confirming the new `And`/`Cmp` machinery composes
    /// through genuine SSA env-threading, not merely as isolated single-statement arms.
    /// Parameter indices `1`/`2`/`4` are chosen DISJOINT from the assigned set `{0, 3}`
    /// (`0` is the RETURN statement's own index — reusing it as a bare parameter
    /// reference would collide with `defs`' assigned-temp lookup and mis-inline as a
    /// self-reference; `param_indices()`'s `!assigned.contains(i)` filter is exactly
    /// the invariant this disjointness respects).
    #[test]
    fn trustir_body_refinement_and_then_cmp_chain_modulo3() {
        let body = IrBody {
            stmts: vec![
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(TrustIrBinOp::And, IrOperand::Var(1), IrOperand::Var(2)),
                },
                IrStmt {
                    idx: 0,
                    rvalue: IrRvalue::Cmp(TrustIrCmpOp::Eq, IrOperand::Var(3), IrOperand::Var(4)),
                },
            ],
            ret: 0,
        };
        assert!(body.is_grounder_connected());
        assert_eq!(
            check_body_refinement(&body),
            RefinementVerdict::ProvenModulo3,
            "And-then-Cmp chain body refinement did not prove modulo 3",
        );
    }

    /// Trust: M6 rung 9 — the `ExprMeta::{has_fvar,has_level_param}`-class shape:
    /// `_2 := (*self).0; _3 := Shr(_2, N); _4 := And(_3, 1); _0 := Eq(_4, 1)`
    /// (a Field leaf, an unsigned `Shr`, an `And`, then a `Cmp`) is NOT
    /// grounder-connected (the `Field` leaf has no live-grounder-connected
    /// `Trust.TrustIr.idxElem` arm), but the MULTI-STATEMENT MODEL-ONLY refinement
    /// [`check_body_refinement_model_chain`] proves modulo 3 — the genuine
    /// multi-statement generalization this M6 rung 9 residue closes.
    #[test]
    fn trustir_body_refinement_model_chain_bit_test_modulo3() {
        let body = IrBody {
            stmts: vec![
                IrStmt { idx: 2, rvalue: IrRvalue::Use(IrOperand::Field(0, 0)) },
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::LShr,
                        IrOperand::Var(2),
                        IrOperand::Const(40),
                    ),
                },
                IrStmt {
                    idx: 4,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::And,
                        IrOperand::Var(3),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 0,
                    rvalue: IrRvalue::Cmp(TrustIrCmpOp::Eq, IrOperand::Var(4), IrOperand::Const(1)),
                },
            ],
            ret: 0,
        };
        assert!(!body.is_grounder_connected());
        assert!(matches!(check_body_refinement(&body), RefinementVerdict::KernelRejected(_)));
        assert_eq!(
            check_body_refinement_model_chain(&body),
            RefinementVerdict::ProvenModulo3,
            "bit-test chain (Field, Shr, And, Cmp) model-only refinement did not prove modulo 3",
        );
    }

    /// The MULTI-STATEMENT MODEL-ONLY GENUINENESS check: a WRONG inlined denotation
    /// (claiming the `And`-then-`Cmp` chain's value equals a bare `Const(0)`) is
    /// REJECTED by the kernel — [`check_body_refinement_model_chain`] is NOT `Eq.refl`
    /// of a tautology.
    #[test]
    fn trustir_body_refinement_model_chain_is_fail_closed() {
        let body = IrBody {
            stmts: vec![
                IrStmt { idx: 2, rvalue: IrRvalue::Use(IrOperand::Field(0, 0)) },
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::And,
                        IrOperand::Var(2),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 0,
                    rvalue: IrRvalue::Cmp(TrustIrCmpOp::Eq, IrOperand::Var(3), IrOperand::Const(1)),
                },
            ],
            ret: 0,
        };
        let wrong_rhs = int_lit(0);
        let statement = body_model_chain_refinement_statement(&body, Some(&wrong_rhs))
            .expect("statement should build");
        let Some(proof) = body_model_chain_refinement_proof(&body) else {
            panic!("proof should build");
        };
        let verdict = check_refinement_decl(
            "Trust.TrustIr.Refinement.body_model_chain_wrong_probe",
            Some(statement),
            Some(proof),
        );
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "WRONG chain denotation (claimed Const(0)) was NOT rejected — soundness hole",
        );
    }

    /// The BODY GENUINENESS check: a wrong inlined formula (Add where the body is Mul)
    /// is REJECTED by the kernel — the body refinement is NOT `Eq.refl` of a tautology.
    #[test]
    fn trustir_body_refinement_is_fail_closed() {
        assert!(
            trustir_body_refinement_fail_closed(),
            "WRONG body grounding (Mul body claimed to ground as Add) was NOT rejected — \
             soundness hole",
        );
    }

    /// A body whose returned index is UNASSIGNED (no straight-line content) fails closed.
    #[test]
    fn trustir_body_unassigned_return_fail_closed() {
        let body = IrBody {
            stmts: vec![IrStmt { idx: 2, rvalue: IrRvalue::Use(IrOperand::Var(0)) }],
            ret: 9, // never assigned
        };
        assert!(matches!(check_body_refinement(&body), RefinementVerdict::KernelRejected(_)));
    }

    /// `axiom_closure` assertion: the body refinement theorem's transitive axiom
    /// closure is a SUBSET of the 3 foundational axioms — no 4th axiom — verified
    /// against `crate::axioms::FOUNDATIONAL_AXIOMS` directly (belt-and-suspenders on
    /// top of the kernel's own `axiom_deps` verdict).
    #[test]
    fn trustir_body_refinement_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        let body = example_body_2_3();
        let mut env = trustir_env().expect("trustir_env");
        let statement = body_refinement_statement(&body, None).expect("statement");
        let proof = body_refinement_proof(&body).expect("proof");
        let name = Name::from_string("Trust.TrustIr.Refinement.body_axiom_closure_test");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .expect("add body theorem");
        let residue = env.axiom_deps(&name).expect("axiom_deps");
        let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
        for ax in &closure {
            assert!(
                FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                "non-foundational axiom in body refinement closure: {ax}",
            );
        }
        // The residue verdict (axioms BEYOND the foundational three) must be empty.
        assert!(residue.is_empty(), "expected modulo-3 closure, got residue {closure:?}");
    }

    // -----------------------------------------------------------------------
    // CONTROL-FLOW FRAGMENT tests (this increment) — blocks / Switch / branch
    // -----------------------------------------------------------------------

    /// The CmpOp bijection: the six comparison-fragment `TrustIrCmpOp` names are the
    /// real trust-ir `ICmp` predicate identifiers, and the Clean constructor names embed
    /// them.
    #[test]
    fn trustir_cmpop_names_are_canonical() {
        let names: Vec<&str> = TrustIrCmpOp::ALL.iter().map(|o| o.trust_ir_name()).collect();
        assert_eq!(names, vec!["Lt", "Le", "Eq", "Ne", "Gt", "Ge"]);
        for op in TrustIrCmpOp::ALL {
            assert!(op.ctor_name().ends_with(op.trust_ir_name()));
        }
    }

    /// BRANCH refinement (the headline): the abs CFG
    /// `bb0: switch x<0 → bb1 else bb2; bb1: ret -x; bb2: ret x` kernel-checks modulo 3 —
    /// the trust-ir control-flow step `evalCfg` folds the CFG (Nat.rec on fuel, Term.rec
    /// dispatch, Bool.rec on the switch) and its reduction matches the LIVE grounder's
    /// branched `Ite(Lt(x,0), Neg(x), x)`.
    #[test]
    fn trustir_branch_refinement_abs_modulo3() {
        let cfg = example_abs_cfg();
        assert_eq!(
            check_branch_refinement(&cfg),
            RefinementVerdict::ProvenModulo3,
            "abs branch refinement did not prove modulo 3",
        );
    }

    /// A NESTED (3-arm) branch — the `sign` CFG, whose else arm is itself a `Switch` —
    /// also kernel-checks modulo 3, exercising the nested `Bool.rec`/`Ite` reduction:
    /// `Ite(Lt(x,0), -1, Ite(Gt(x,0), 1, 0))`.
    #[test]
    fn trustir_branch_refinement_sign_nested_modulo3() {
        let cfg = example_sign_cfg();
        assert_eq!(
            check_branch_refinement(&cfg),
            RefinementVerdict::ProvenModulo3,
            "nested sign branch refinement did not prove modulo 3",
        );
    }

    /// The BRANCH GENUINENESS check: a wrong branched formula (the then/else arms swapped)
    /// is REJECTED by the kernel — the branch refinement is NOT `Eq.refl` of a tautology;
    /// the cfg-fold genuinely reconstructs the branched ground, and a wrong branch
    /// target/value would not prove.
    #[test]
    fn trustir_branch_refinement_is_fail_closed() {
        assert!(
            trustir_branch_refinement_fail_closed(),
            "WRONG branch grounding (then/else arms swapped) was NOT rejected — soundness hole",
        );
    }

    /// A `Goto` chain that threads block statements: `bb0: _2 := a+b; Goto bb1;
    /// bb1: _3 := _2*c; Return _3` (inlined `Mul(Add(a,b), c)`) kernel-checks modulo 3 —
    /// the `Goto` arm threads the POST-STMT env into the successor block, so the env-
    /// threading reduction reconstructs the SAME nested term the straight-line body does.
    #[test]
    fn trustir_branch_refinement_goto_chain_modulo3() {
        let cfg = IrCfg {
            blocks: vec![
                IrBlock {
                    stmts: vec![IrStmt {
                        idx: 2,
                        rvalue: IrRvalue::Bin(
                            TrustIrBinOp::Add,
                            IrOperand::Var(0),
                            IrOperand::Var(1),
                        ),
                    }],
                    term: IrTerm::Goto(1),
                },
                IrBlock {
                    stmts: vec![IrStmt {
                        idx: 3,
                        rvalue: IrRvalue::Bin(
                            TrustIrBinOp::Mul,
                            IrOperand::Var(2),
                            IrOperand::Var(4),
                        ),
                    }],
                    term: IrTerm::Return(IrOperand::Var(3)),
                },
            ],
            entry: 0,
            fuel: 3,
        };
        assert_eq!(
            check_branch_refinement(&cfg),
            RefinementVerdict::ProvenModulo3,
            "Goto-chain branch refinement did not prove modulo 3",
        );
    }

    /// A CFG whose acyclic walk EXCEEDS its fuel (a cycle bb0→bb0 — the loop fragment, the
    /// NEXT step) fails closed: `inlined_return_formula` runs out of fuel and declines.
    #[test]
    fn trustir_branch_refinement_cyclic_fuel_exhaust_fail_closed() {
        let cfg = IrCfg {
            blocks: vec![IrBlock { stmts: vec![], term: IrTerm::Goto(0) }], // self-loop
            entry: 0,
            fuel: 4,
        };
        assert!(matches!(check_branch_refinement(&cfg), RefinementVerdict::KernelRejected(_)));
    }

    /// `axiom_closure ⊆ FOUNDATIONAL` assertion for the BRANCH refinement: the abs branch
    /// theorem's transitive axiom closure is a SUBSET of the 3 foundational axioms — NO
    /// 4th axiom — verified against `crate::axioms::FOUNDATIONAL_AXIOMS` directly (belt-
    /// and-suspenders on the kernel's own `axiom_deps`).
    #[test]
    fn trustir_branch_refinement_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        let cfg = example_abs_cfg();
        let mut env = trustir_env().expect("trustir_env");
        let statement = branch_refinement_statement(&cfg, None).expect("statement");
        let proof = branch_refinement_proof(&cfg).expect("proof");
        let name = Name::from_string("Trust.TrustIr.Refinement.branch_axiom_closure_test");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .expect("add branch theorem");
        let residue = env.axiom_deps(&name).expect("axiom_deps");
        let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
        for ax in &closure {
            assert!(
                FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                "non-foundational axiom in branch refinement closure: {ax}",
            );
        }
        assert!(residue.is_empty(), "expected modulo-3 closure, got residue {closure:?}");
    }

    // -----------------------------------------------------------------------
    // LOOP FRAGMENT tests (this increment) — back-edge fixpoint + Hoare while-rule
    // + the COUNTER-LOOP refinement (`count_to`, invariant `i ≤ n`)
    // -----------------------------------------------------------------------

    /// The trust-ir loop meta-theory (`stepLoop`/`execLoop`/`stepPreservesInv`/
    /// `loopInvariantRule`) is registered AND rests on ⊆ the 3 foundational axioms — the
    /// anchor audit (extended to the loop fragment) is Modulo3. `register_loop_invariant_rule_ir`
    /// also `check_type`s the Hoare while-rule proof at registration (a genuine `Nat.rec`
    /// induction over the back-edge fixpoint, NOT `Eq.refl`).
    #[test]
    fn trustir_loop_anchor_is_modulo3() {
        assert_eq!(pin_trustir_anchor(), AnchorVerdict::Modulo3);
    }

    /// COUNTER-LOOP REFINEMENT (the headline): the `count_to` loop
    /// `i := 0; while i < n { i := i + 1 }; ret i` — the trust-ir Hoare while-rule
    /// INSTANTIATED at the GUARD-AWARE invariant `I := λ e. e[3] ≤ e[1]` (`i ≤ n`), with a
    /// GENUINE guard-derived preservation proof (`of_decide_eq_true (Int.lt i n) … hg`, where
    /// the guard `i < n` is DEFINITIONALLY `Int.le (i+1) n` — the reduced codomain
    /// `I (evalBody e [i:=i+1])`), kernel-checks the per-function partial-correctness instance
    ///   ∀ n e, I e → I (execLoop e (i<n) [i:=i+1] n)
    /// modulo exactly 3. The back-edge fixpoint `execLoop` (a `Nat.rec` over the trip count)
    /// RECONSTRUCTS the certified loop fact — the invariant survives every iteration.
    #[test]
    fn trustir_loop_refinement_count_to_modulo3() {
        let lp = example_count_to_loop();
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "count_to (i≤n) loop refinement did not prove modulo 3",
        );
    }

    /// The INDUCTIVE LOWER bound `0 ≤ i` for the same counter loop also kernel-checks modulo
    /// 3 — its preservation `0 ≤ i → 0 ≤ i+1` GENUINELY USES the loop-carried hypothesis (via
    /// `Int.le_trans` + `Int.le_self_add_one`), the COMPLEMENT of the guard-using upper bound.
    #[test]
    fn trustir_loop_refinement_lower_bound_modulo3() {
        let lp = IrLoop {
            inv: IrLoopInvariant::CounterGeConst { i_idx: 3, c: 0 },
            ..example_count_to_loop()
        };
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "count_to (0≤i) lower-bound loop refinement did not prove modulo 3",
        );
    }

    /// INVARIANT PRESERVATION across the back-edge: the conclusion is the loop-invariant
    /// rule's `∀ n e, I e → I (execLoop e cond body n)` — `I` is maintained for an ARBITRARY
    /// trip count `n` (the `Nat.rec` front-peel of the fixpoint), which is exactly invariant
    /// preservation per iteration composed over the loop. GENUINENESS: the instance's type IS
    /// `loopInvariantRule` at the concrete `i ≤ n`, distinct from the lower bound `0 ≤ i`.
    #[test]
    fn trustir_loop_invariant_preservation_is_about_the_bound() {
        let lp = example_count_to_loop();
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        let real = loop_instance_conclusion_type_ir(&lp, None);
        let proof = loop_instance_proof_ir(&lp);
        let inferred = tc.infer_type(&proof).expect("the loop instance proof has a type");
        assert!(
            tc.is_def_eq(&inferred, &real),
            "the loop instance's type MUST be loopInvariantRule at `i ≤ n`",
        );
        // The upper bound `i ≤ n` is a DIFFERENT statement from the lower bound `0 ≤ i`.
        let lower = IrLoop {
            inv: IrLoopInvariant::CounterGeConst { i_idx: 3, c: 0 },
            ..example_count_to_loop()
        };
        let lower_ty = loop_instance_conclusion_type_ir(&lower, None);
        assert!(
            !tc.is_def_eq(&real, &lower_ty),
            "the upper bound `i ≤ n` ≠ the lower bound `0 ≤ i` as a statement",
        );
    }

    /// The LOOP GENUINENESS check: a wrong invariant (the upper bound `i ≤ r` against a bound
    /// index `r` the guard `i < n` does NOT mention) is REJECTED by the kernel — the
    /// counter-loop refinement is NOT `Eq.refl` of a def-eq tautology; the guard genuinely
    /// re-establishes the bound, and a non-guard bound would not prove.
    #[test]
    fn trustir_loop_refinement_is_fail_closed() {
        assert!(
            trustir_loop_refinement_fail_closed(),
            "WRONG loop invariant (`i ≤ r`, r not the guard bound) was NOT rejected — \
             soundness hole",
        );
    }

    /// A non-decreasing / non-preserved invariant fails closed: claim `5 ≤ i` (the lower
    /// bound at constant 5) on a loop whose `i` starts unconstrained — preservation
    /// `5 ≤ i → 5 ≤ i+1` IS provable (monotone), so to exercise NON-preservation we instead
    /// claim the upper bound `i ≤ n` against the UNTOUCHED local index 2 (`r`, not the guard
    /// bound 1) — its preservation codomain `Int.le (i+1)(e 2)` is NOT def-eq to the guard
    /// fact `Int.le (i+1)(e 1)` ⇒ KernelRejected (the same fail-closed mechanism, a distinct
    /// wrong index).
    #[test]
    fn trustir_loop_wrong_invariant_fails_closed() {
        let lp = IrLoop {
            inv: IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 2 },
            ..example_count_to_loop()
        };
        assert!(
            matches!(check_loop_invariant_instance(&lp), RefinementVerdict::KernelRejected(_)),
            "a synthesized upper bound against a non-guard bound MUST be kernel-rejected",
        );
    }

    // ---- LOOP-POSTCONDITION DISCHARGE on the trust-ir denotation (Seam A of the ----
    // ---- MirSem de-internalization: the via-trustir gate's clause (c) relocation) ----

    /// POSTCONDITION DISCHARGE (the headline): the `count_to` postcondition `ret ≤ n` is
    /// kernel-discharged BY the trust-ir-certified upper bound at the halting state —
    /// `∀ fuel e, I e → Int.le (execLoop … fuel 3) (execLoop … fuel 1)` — composing the
    /// SAME instantiated while-rule with the identity projection, modulo exactly 3.
    #[test]
    fn trustir_loop_postcondition_count_to_ret_le_n_modulo3() {
        let lp = example_count_to_loop();
        assert_eq!(
            check_loop_postcondition_instance(
                &lp,
                IrLoopPost::RetLeBound { read_idx: 3, bound_idx: 1 },
            ),
            RefinementVerdict::ProvenModulo3,
            "count_to `ret ≤ n` postcondition discharge did not prove modulo 3",
        );
    }

    /// The countdown lower bound `0 ≤ i` discharges `0 ≤ ret` at the halting state.
    #[test]
    fn trustir_loop_postcondition_countdown_const_le_ret_modulo3() {
        let lp = example_countdown_loop();
        assert_eq!(
            check_loop_postcondition_instance(&lp, IrLoopPost::ConstLeRet { read_idx: 3, c: 0 },),
            RefinementVerdict::ProvenModulo3,
            "countdown `0 ≤ ret` postcondition discharge did not prove modulo 3",
        );
    }

    /// RELATIONAL discharge: `s == i ∧ i ≤ n` discharges the STRONGER `ret ≤ n` at the
    /// ACCUMULATOR — the `Eq.subst` along `i = s` is impossible without the relational
    /// conjunct, so this genuinely uses it (not a bare interval projection).
    #[test]
    fn trustir_loop_postcondition_relational_accum_modulo3() {
        let lp =
            example_accum_loop(IrLoopInvariant::AccumEqCounter { s_idx: 4, i_idx: 3, n_idx: 1 });
        assert_eq!(
            check_loop_postcondition_instance(
                &lp,
                IrLoopPost::RetLeBound { read_idx: 4, bound_idx: 1 },
            ),
            RefinementVerdict::ProvenModulo3,
            "relational accumulator `ret ≤ n` postcondition discharge did not prove modulo 3",
        );
    }

    /// `≤`-GUARDED discharge: the conjoined range `c ≤ i ∧ i ≤ n+1` discharges `ret ≤ n+1`
    /// (`And.right`) — the `count_le` shape.
    #[test]
    fn trustir_loop_postcondition_count_le_succ_modulo3() {
        let lp = example_count_le_loop(IrLoopInvariant::CounterInRangeSucc {
            i_idx: 3,
            c: 0,
            bound_idx: 1,
        });
        assert_eq!(
            check_loop_postcondition_instance(
                &lp,
                IrLoopPost::RetLeBoundSucc { read_idx: 3, bound_idx: 1 },
            ),
            RefinementVerdict::ProvenModulo3,
            "`≤`-guarded `ret ≤ n+1` postcondition discharge did not prove modulo 3",
        );
    }

    /// GENERAL RELATIONAL SET discharge at the SECOND accumulator (`three_ret_b`): the
    /// projection walks the nested `And` to the returned accumulator's conjunct.
    #[test]
    fn trustir_loop_postcondition_set_second_accum_modulo3() {
        let lp = example_three_loop(IrLoopInvariant::AccumEqCounterSet {
            accum_idxs: vec![4, 5],
            i_idx: 3,
            n_idx: 1,
        });
        assert_eq!(
            check_loop_postcondition_instance(
                &lp,
                IrLoopPost::RetLeBound { read_idx: 5, bound_idx: 1 },
            ),
            RefinementVerdict::ProvenModulo3,
            "general relational set `ret_b ≤ n` postcondition discharge did not prove modulo 3",
        );
    }

    /// FAIL-CLOSED (pair mismatch): a postcondition at a bound/index the certified
    /// invariant does not pin is rejected — `ret ≤ r` (r=2, not the guard bound) against
    /// the `i ≤ n` invariant, a lower-bound post against an upper-bound invariant, and a
    /// wrong read index all decline.
    #[test]
    fn trustir_loop_postcondition_mismatch_fails_closed() {
        let lp = example_count_to_loop();
        for post in [
            IrLoopPost::RetLeBound { read_idx: 3, bound_idx: 2 }, // wrong bound
            IrLoopPost::RetLeBound { read_idx: 1, bound_idx: 1 }, // wrong read index
            IrLoopPost::ConstLeRet { read_idx: 3, c: 0 },         // wrong conjunct class
            IrLoopPost::RetLeBoundSucc { read_idx: 3, bound_idx: 1 }, // wrong succ-ness
        ] {
            assert!(
                matches!(
                    check_loop_postcondition_instance(&lp, post),
                    RefinementVerdict::KernelRejected(_)
                ),
                "mismatched postcondition {post:?} MUST be rejected",
            );
        }
    }

    /// FAIL-CLOSED (kernel): a LYING invariant cannot launder a postcondition — claim
    /// `i ≤ r` at the untouched local `r = 2` (not the guard bound) so the Rust-side pair
    /// MATCHES (`ret ≤ r` at the same index), but the preservation proof inside the
    /// composed while-rule does not type-check ⇒ KernelRejected. The discharge is only as
    /// strong as the kernel-certified invariant it projects from.
    #[test]
    fn trustir_loop_postcondition_lying_invariant_fails_closed() {
        let lp = IrLoop {
            inv: IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 2 },
            ..example_count_to_loop()
        };
        assert!(
            matches!(
                check_loop_postcondition_instance(
                    &lp,
                    IrLoopPost::RetLeBound { read_idx: 3, bound_idx: 2 },
                ),
                RefinementVerdict::KernelRejected(_)
            ),
            "a lying invariant's postcondition discharge MUST be kernel-rejected",
        );
    }

    /// CONSTANT-index guarded slice (`clamp_idx` — the last measured MirSem-fallback
    /// shape): under `k < sliceLen s` the select reduces to `idxElem s k`, modulo 3;
    /// a wrong RHS (the `dflt` else-arm) is KernelRejected (the guard transport is
    /// genuine); a negative literal index declines fail-closed.
    #[test]
    fn trustir_guarded_const_index_modulo3_and_fail_closed() {
        let gk = IrGuardedConstIndex { s_idx: 0, k: 3, dflt: 0 };
        assert_eq!(
            check_guarded_const_index_refinement(&gk),
            RefinementVerdict::ProvenModulo3,
            "the const-index bounds-guard refinement must prove modulo 3",
        );
        // Wrong RHS: claim the guard-true result is the ELSE arm `dflt` — the congrArg
        // transport lands on the TRUE minor `idxElem s k`, NOT def-eq to `dflt`.
        let (stmt, proof) = {
            let wrong_rhs = int_lit(0);
            guarded_const_index_refinement(&gk, Some(&wrong_rhs))
        };
        assert!(
            matches!(
                check_refinement_decl(
                    "Trust.TrustIr.Refinement.guarded_const_index_wrong",
                    Some(stmt),
                    Some(proof),
                ),
                RefinementVerdict::KernelRejected(_)
            ),
            "a guard-true ⇒ else-arm claim MUST be kernel-rejected",
        );
        // Negative literal index: fail-closed decline.
        assert!(
            matches!(
                check_guarded_const_index_refinement(&IrGuardedConstIndex {
                    s_idx: 0,
                    k: -1,
                    dflt: 0,
                }),
                RefinementVerdict::KernelRejected(_)
            ),
            "a negative literal index MUST decline",
        );
    }

    /// COND-UPDATE (Seam C) discharge: `0 ≤ m ∧ 0 ≤ i` discharges `0 ≤ ret` at the
    /// conditionally-updated accumulator `m` on the SELECT layer (`And.left` of the
    /// `loopInvariantRuleS` instance at the `execLoopS` halting state), modulo 3 — and
    /// mismatched postconditions (wrong index / constant / class) fail closed.
    #[test]
    fn trustir_cond_update_postcondition_modulo3_and_fail_closed() {
        let lp = example_max_scan_loop(3, 4, 1);
        assert_eq!(
            check_cond_update_postcondition_instance(
                &lp,
                IrLoopPost::ConstLeRet { read_idx: 4, c: 0 },
            ),
            RefinementVerdict::ProvenModulo3,
            "cond-update `0 ≤ ret` postcondition discharge did not prove modulo 3",
        );
        for post in [
            IrLoopPost::ConstLeRet { read_idx: 3, c: 0 }, // counter, not the accumulator
            IrLoopPost::ConstLeRet { read_idx: 4, c: 1 }, // wrong constant
            IrLoopPost::RetLeBound { read_idx: 4, bound_idx: 1 }, // wrong conjunct class
        ] {
            assert!(
                matches!(
                    check_cond_update_postcondition_instance(&lp, post),
                    RefinementVerdict::KernelRejected(_)
                ),
                "mismatched cond-update postcondition {post:?} MUST be rejected",
            );
        }
    }

    /// `axiom_closure ⊆ FOUNDATIONAL` for the COUNTER-LOOP refinement: the `count_to`
    /// instance's transitive axiom closure is a SUBSET of the 3 foundational axioms — NO 4th
    /// axiom — verified against `crate::axioms::FOUNDATIONAL_AXIOMS` directly. The preservation
    /// uses only `of_decide_eq_true` (axiom-free: `Decidable.rec`/`Bool.noConfusion`/`False.elim`)
    /// and the def-eq `Int.lt ≡ Int.le (·+1) ·`; the rule itself is a `Nat.rec` induction.
    #[test]
    fn trustir_loop_refinement_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        let lp = example_count_to_loop();
        let mut env = trustir_env().expect("trustir_env");
        let concl_ty = loop_instance_conclusion_type_ir(&lp, None);
        let proof = loop_instance_proof_ir(&lp);
        {
            let tc = TypeChecker::new(&env);
            tc.check_type(&proof, &concl_ty).expect("count_to instance type-checks");
        }
        let name = Name::from_string("Trust.TrustIr.Refinement.loop_axiom_closure_test");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: concl_ty,
            value: proof,
        })
        .expect("add loop instance theorem");
        let residue = env.axiom_deps(&name).expect("axiom_deps");
        let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
        for ax in &closure {
            assert!(
                FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                "non-foundational axiom in loop refinement closure: {ax}",
            );
        }
        assert!(residue.is_empty(), "expected modulo-3 closure, got residue {closure:?}");
    }

    /// GENUINENESS (NOT `Eq.refl` on def-equal terms): a TRIVIAL preservation proof
    /// `λ e hI _hg. hI` — which would suffice if `I (evalBody e [i:=i+1])` were def-eq to
    /// `I e` — is REJECTED by the kernel for the `i ≤ n` invariant. The codomain
    /// `I (evalBody e body)` ι-reduces to `Int.le ((e i)+1) (e n)`, which is NOT def-eq to
    /// the hypothesis `I e ≡ Int.le (e i) (e n)` (the counter genuinely advances). So the
    /// guard-derived `of_decide_eq_true` step is GENUINELY REQUIRED — the loop refinement
    /// reconstructs the certified fact through the back-edge, it is not a tautology.
    #[test]
    fn trustir_loop_trivial_preservation_is_rejected() {
        let bd = || BinderData::from(BinderInfo::Default);
        let lp = example_count_to_loop();
        let env = trustir_env().expect("trustir_env");
        // The TRIVIAL (wrong) preservation `λ e hI _hg. hI` at the i≤n invariant.
        let i_expr = lp.invariant_expr(None);
        let cond_expr = lp.cond_expr();
        let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0)); // I e
        let guard = Expr::apps(cst(TRUSTIR_EVAL_COND), [Expr::bvar(1), cond_expr.lift(2)]);
        let guard_eq = eq_bool_true(guard);
        // λ e λ hI λ _hg. hI   (inside the three binders hI = bvar(1)).
        let trivial_pres = Expr::lam(
            bd(),
            env_ty(),
            Expr::lam(bd(), i_e, Expr::lam(bd(), guard_eq, Expr::bvar(1))),
        );
        // The preservation hypothesis TYPE the while-rule demands.
        let pres_ty = preservation_hyp_type_ir(&i_expr, &cond_expr, &lp.body_expr());
        let tc = TypeChecker::new(&env);
        assert!(
            tc.check_type(&trivial_pres, &pres_ty).is_err(),
            "a trivial guard-ignoring preservation `λ e hI _hg. hI` MUST be rejected for `i ≤ n` \
             — the codomain `i+1 ≤ n` is NOT def-eq to the hypothesis `i ≤ n` (genuineness)",
        );
    }

    // -----------------------------------------------------------------------
    // LOOP-BREADTH increment — the OTHER MirSem loop classes (countdown, stride,
    // accumulator lower bound, accumulator relational), each mirroring the named
    // MirSem rule, kernel-checked modulo 3 + fail-closed.
    // -----------------------------------------------------------------------

    /// Shared helper: the count_to/countdown/stride/accum instance's transitive axiom closure
    /// is a SUBSET of the 3 foundational axioms (NO 4th axiom), verified against
    /// `crate::axioms::FOUNDATIONAL_AXIOMS` directly (belt-and-suspenders on `axiom_deps`).
    fn assert_loop_instance_modulo3_axiom_closure(lp: &IrLoop, decl: &str) {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        let mut env = trustir_env().expect("trustir_env");
        let concl_ty = loop_instance_conclusion_type_ir(lp, None);
        let proof = loop_instance_proof_ir(lp);
        {
            let tc = TypeChecker::new(&env);
            tc.check_type(&proof, &concl_ty).expect("loop instance type-checks");
        }
        let name = Name::from_string(decl);
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: concl_ty,
            value: proof,
        })
        .expect("add loop instance theorem");
        let residue = env.axiom_deps(&name).expect("axiom_deps");
        let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
        for ax in &closure {
            assert!(
                FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                "non-foundational axiom in {decl} closure: {ax}",
            );
        }
        assert!(residue.is_empty(), "expected modulo-3 closure, got residue {closure:?}");
    }

    // ---- COUNTDOWN (`CountdownGeConst`, `while i > 0 { i := i - 1 }`, `0 ≤ i`) ----

    /// COUNTDOWN refinement: the `while i > 0 { i := i - 1 }` loop instantiated at the lower
    /// bound `I := λ e. 0 ≤ e[3]`, with a GENUINE guard-using preservation (inline
    /// `countdownGe0`: from `0 < i` derive `0 ≤ i - 1`, the body's reduced codomain), kernel-
    /// checks the partial-correctness instance `∀ n e, I e → I (execLoop e (i>0) [i:=i-1] n)`
    /// modulo exactly 3. Mirrors `mirsem::countdown_ge_const_preservation_proof`.
    #[test]
    fn trustir_loop_refinement_countdown_modulo3() {
        let lp = example_countdown_loop();
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "countdown (0≤i) loop refinement did not prove modulo 3",
        );
    }

    /// COUNTDOWN GENUINENESS: a NON-ZERO lower bound `1 ≤ i` (false at the terminal `i = 0`)
    /// is REJECTED — `countdownGe0` proves only `0 ≤ i-1`, not `1 ≤ i-1`. Not a tautology.
    #[test]
    fn trustir_loop_countdown_is_fail_closed() {
        assert!(
            trustir_countdown_refinement_fail_closed(),
            "WRONG countdown lower bound (`1 ≤ i`, non-zero const) was NOT rejected — \
             soundness hole",
        );
    }

    /// COUNTDOWN `axiom_closure ⊆ FOUNDATIONAL`: the instance rests on ⊆ the 3 axioms.
    #[test]
    fn trustir_loop_countdown_axiom_closure_subset_of_three() {
        assert_loop_instance_modulo3_axiom_closure(
            &example_countdown_loop(),
            "Trust.TrustIr.Refinement.countdown_axiom_closure_test",
        );
    }

    // ---- STRIDE (`StrideGeConst`, `while i < n { i := i + k }`, `0 ≤ i`) ----

    /// STRIDE refinement: the `while i < n { i := i + k }` loop instantiated at the lower
    /// bound `I := λ e. 0 ≤ e[3]`, with a per-`k` preservation (`Int.le_trans 0 i (i+k) hI
    /// (strideSelfLe k i)`) that GENUINELY USES the carried hypothesis, kernel-checks modulo 3
    /// for strides `k ∈ {2, 3, 5}`. Mirrors `mirsem::stride_ge_const_preservation_proof`.
    #[test]
    fn trustir_loop_refinement_stride_modulo3() {
        for k in [2_i128, 3, 5] {
            let lp = example_stride_loop(k);
            assert_eq!(
                check_loop_invariant_instance(&lp),
                RefinementVerdict::ProvenModulo3,
                "stride (k={k}) loop refinement did not prove modulo 3",
            );
        }
    }

    /// STRIDE GENUINENESS: a `k = 3` invariant on a `k = 1` body is REJECTED — `strideSelfLe 3`
    /// yields codomain `0 ≤ i+3` but the body reduces to `0 ≤ i+1`. The stride is load-bearing.
    #[test]
    fn trustir_loop_stride_is_fail_closed() {
        assert!(
            trustir_stride_refinement_fail_closed(),
            "WRONG stride (k=3 invariant on a k=1 body) was NOT rejected — soundness hole",
        );
    }

    /// STRIDE `axiom_closure ⊆ FOUNDATIONAL` (at `k = 3`).
    #[test]
    fn trustir_loop_stride_axiom_closure_subset_of_three() {
        assert_loop_instance_modulo3_axiom_closure(
            &example_stride_loop(3),
            "Trust.TrustIr.Refinement.stride_axiom_closure_test",
        );
    }

    // ---- ACCUMULATOR lower bound (`AccumGeConst`, `[s:=s+1; i:=i+1]`, `0 ≤ s`) ----

    /// ACCUMULATOR (lower bound) refinement: the MULTI-statement body `[s := s+1; i := i+1]`
    /// loop instantiated at the lower bound `I := λ e. 0 ≤ e[4]` (the ACCUMULATOR `s`, NOT the
    /// counter), with the SAME inductive preservation as the counter lower bound built at the
    /// accumulator index (the `i:=i+1` statement leaves `s` untouched, so the net body effect
    /// at `s` is `s+1`), kernel-checks modulo 3. Mirrors `mirsem::AccumGeConst` preservation.
    #[test]
    fn trustir_loop_refinement_accum_ge_modulo3() {
        let lp = example_accum_loop(IrLoopInvariant::AccumGeConst { s_idx: 4, c: 0 });
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "accumulator (0≤s) lower-bound loop refinement did not prove modulo 3",
        );
    }

    /// ACCUMULATOR (lower bound) `axiom_closure ⊆ FOUNDATIONAL`.
    #[test]
    fn trustir_loop_accum_ge_axiom_closure_subset_of_three() {
        assert_loop_instance_modulo3_axiom_closure(
            &example_accum_loop(IrLoopInvariant::AccumGeConst { s_idx: 4, c: 0 }),
            "Trust.TrustIr.Refinement.accum_ge_axiom_closure_test",
        );
    }

    // ---- ACCUMULATOR relational (`AccumEqCounter`, `[s:=s+1; i:=i+1]`, `s == i ∧ i ≤ n`) ----

    /// ACCUMULATOR (relational) refinement: the lockstep body `[s := s+1; i := i+1]` loop
    /// instantiated at the RELATIONAL invariant `I := λ e. (e[4] == e[3]) ∧ (e[3] ≤ e[1])`
    /// (`s == i ∧ i ≤ n`), with an `And.intro` preservation — the LEFT conjunct the `congrArg
    /// (·+1)` congruence `s == i → s+1 == i+1` (USING the hypothesis), the RIGHT conjunct the
    /// guard-aware `i < n → i+1 ≤ n` — kernel-checks modulo 3. Mirrors
    /// `mirsem::accum_eq_counter_preservation_proof`.
    #[test]
    fn trustir_loop_refinement_accum_eq_modulo3() {
        let lp =
            example_accum_loop(IrLoopInvariant::AccumEqCounter { s_idx: 4, i_idx: 3, n_idx: 1 });
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "accumulator (s==i ∧ i≤n) relational loop refinement did not prove modulo 3",
        );
    }

    /// ACCUMULATOR (relational) GENUINENESS: a NON-lockstep `s := s + 2` body breaks `s == i`
    /// — the `congrArg (·+1)` step proves `s+1 == i+1` but the codomain reduces to `s+2 == i+1`
    /// ⇒ REJECTED. The relational equality is GENUINE (tracks the lockstep step).
    #[test]
    fn trustir_loop_accum_eq_is_fail_closed() {
        assert!(
            trustir_accum_eq_refinement_fail_closed(),
            "WRONG accumulator relation (`s == i` on an `s := s+2` non-lockstep body) was NOT \
             rejected — soundness hole",
        );
    }

    /// ACCUMULATOR (relational) `axiom_closure ⊆ FOUNDATIONAL`.
    #[test]
    fn trustir_loop_accum_eq_axiom_closure_subset_of_three() {
        assert_loop_instance_modulo3_axiom_closure(
            &example_accum_loop(IrLoopInvariant::AccumEqCounter { s_idx: 4, i_idx: 3, n_idx: 1 }),
            "Trust.TrustIr.Refinement.accum_eq_axiom_closure_test",
        );
    }

    // ---- §6 FALLBACK-9: `≤`-guarded CONJOINED range (`CounterInRangeSucc`, `count_le`) ----

    /// `count_le` refinement: the `≤`-guarded loop `while i ≤ n { i := i + 1 }` instantiated at
    /// the CONJOINED range `I := λ e. (0 ≤ e[3]) ∧ (e[3] ≤ e[1]+1)` (`0 ≤ i ∧ i ≤ n+1`), with an
    /// `And.intro` preservation — the LOWER conjunct via `Int.le_trans` + `Int.le_self_add_one`,
    /// the UPPER conjunct via `Int.add_le_add_right` on the `Le` guard (`i ≤ n → i+1 ≤ n+1`) —
    /// kernel-checks modulo 3. Mirrors `mirsem::counter_in_range_succ_preservation_proof`.
    #[test]
    fn trustir_loop_refinement_count_le_modulo3() {
        let lp = example_count_le_loop(IrLoopInvariant::CounterInRangeSucc {
            i_idx: 3,
            c: 0,
            bound_idx: 1,
        });
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "`≤`-guarded conjoined-range (0≤i ∧ i≤n+1) loop refinement did not prove modulo 3",
        );
    }

    /// `count_le` GENUINENESS: claiming the too-tight `i ≤ n` upper bound on a `≤`-guarded loop is
    /// REJECTED (the `Le` guard re-establishes only `i ≤ n+1`, not `i ≤ n`). Fail-closed.
    #[test]
    fn trustir_loop_count_le_is_fail_closed() {
        assert!(
            trustir_counter_in_range_succ_refinement_fail_closed(),
            "WRONG too-tight upper bound (`i ≤ n` on a `≤`-guarded loop) was NOT rejected — \
             soundness hole",
        );
    }

    /// `count_le` `axiom_closure ⊆ FOUNDATIONAL`.
    #[test]
    fn trustir_loop_count_le_axiom_closure_subset_of_three() {
        assert_loop_instance_modulo3_axiom_closure(
            &example_count_le_loop(IrLoopInvariant::CounterInRangeSucc {
                i_idx: 3,
                c: 0,
                bound_idx: 1,
            }),
            "Trust.TrustIr.Refinement.count_le_axiom_closure_test",
        );
    }

    // ---- §6 FALLBACK-9: GENERAL RELATIONAL set (`AccumEqCounterSet`, `three`/`four`) ----

    /// `three` refinement: the >2-local lockstep loop `while i < n { a:=a+1; b:=b+1; i:=i+1 }`
    /// instantiated at the GENERAL RELATIONAL set `I := λ e. (a==i) ∧ (b==i) ∧ (i ≤ n)`, with a
    /// NESTED right-folded `And.intro` preservation — one `congrArg (·+1)` congruence per
    /// accumulator (`aₖ == i → aₖ+1 == i+1`, projected from the nested `And`) capped by the
    /// guard-aware `i+1 ≤ n` — kernel-checks modulo 3. Mirrors
    /// `mirsem::accum_eq_counter_set_preservation_proof`.
    #[test]
    fn trustir_loop_refinement_accum_eq_set_modulo3() {
        let lp = example_three_loop(IrLoopInvariant::AccumEqCounterSet {
            accum_idxs: vec![4, 5],
            i_idx: 3,
            n_idx: 1,
        });
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "general relational accumulator-set (a==i ∧ b==i ∧ i≤n) loop refinement did not prove \
             modulo 3",
        );
    }

    /// `four` refinement: THREE accumulators (one more congruence conjunct) also kernel-checks
    /// modulo 3 — the general path scales to a wider relational set.
    #[test]
    fn trustir_loop_refinement_accum_eq_set_four_modulo3() {
        let lp = IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![
                IrStmt {
                    idx: 4,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(4),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 5,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(5),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 6,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(6),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(3),
                        IrOperand::Const(1),
                    ),
                },
            ],
            inv: IrLoopInvariant::AccumEqCounterSet {
                accum_idxs: vec![4, 5, 6],
                i_idx: 3,
                n_idx: 1,
            },
        };
        assert_eq!(
            check_loop_invariant_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "4-local general relational accumulator-set loop refinement did not prove modulo 3",
        );
    }

    /// GENERAL RELATIONAL set GENUINENESS: a NON-lockstep `b := b + 2` among the set breaks
    /// `b == i` — the per-accumulator `congrArg (·+1)` step proves `b+1 == i+1` but the codomain
    /// reduces to `b+2 == i+1` ⇒ REJECTED. The relational set is GENUINE (tracks EVERY lockstep).
    #[test]
    fn trustir_loop_accum_eq_set_is_fail_closed() {
        assert!(
            trustir_accum_eq_counter_set_refinement_fail_closed(),
            "WRONG relational set (`b == i` on a `b := b+2` non-lockstep body) was NOT rejected — \
             soundness hole",
        );
    }

    /// GENERAL RELATIONAL set `axiom_closure ⊆ FOUNDATIONAL`.
    #[test]
    fn trustir_loop_accum_eq_set_axiom_closure_subset_of_three() {
        assert_loop_instance_modulo3_axiom_closure(
            &example_three_loop(IrLoopInvariant::AccumEqCounterSet {
                accum_idxs: vec![4, 5],
                i_idx: 3,
                n_idx: 1,
            }),
            "Trust.TrustIr.Refinement.accum_eq_set_axiom_closure_test",
        );
    }

    /// The new loop classes' invariants are DISTINCT statements (not collapsed): the countdown
    /// `0 ≤ i` differs from the stride `0 ≤ i` only by index/SHAPE coincidence (both lower
    /// bounds), but the accumulator relational `s == i ∧ i ≤ n` is a strictly richer `And`
    /// statement than any single lower bound — confirming the relational class adds content.
    #[test]
    fn trustir_loop_accum_eq_is_richer_than_lower_bound() {
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        let accum_eq =
            example_accum_loop(IrLoopInvariant::AccumEqCounter { s_idx: 4, i_idx: 3, n_idx: 1 });
        let accum_ge = example_accum_loop(IrLoopInvariant::AccumGeConst { s_idx: 4, c: 0 });
        let eq_ty = loop_instance_conclusion_type_ir(&accum_eq, None);
        let ge_ty = loop_instance_conclusion_type_ir(&accum_ge, None);
        assert!(
            !tc.is_def_eq(&eq_ty, &ge_ty),
            "the relational `s == i ∧ i ≤ n` MUST be a DIFFERENT statement from `0 ≤ s`",
        );
    }

    // ---- BREAK / EARLY-EXIT (`loopInvariantRuleBrk`, `while i<n { if brk {break} i:=i+1 }`) ----

    /// BREAK refinement: the early-exit `while i < n { if i==stop { break }; i := i + 1 }` loop
    /// instantiated at the guard-aware upper bound `I := λ e. e[3] ≤ e[1]` (`i ≤ n`) via the
    /// combined-guard while-rule `loopInvariantRuleBrk`, with a preservation that extracts the
    /// loop-guard component from the combined guard `cond ∧ ¬brk` (`andLeftTrue`) and then
    /// re-establishes `i+1 ≤ n` from `i < n` (`of_decide_eq_true`), kernel-checks the instance
    ///   ∀ n e, I e → I (execLoopBrk e (i<n) (i==stop) [i:=i+1] n)
    /// modulo exactly 3 — the invariant holds at BOTH the guard-false exit AND the break exit.
    #[test]
    fn trustir_break_loop_refinement_modulo3() {
        let blp = example_count_to_break_loop();
        assert_eq!(
            check_trustir_break_loop_instance(&blp),
            RefinementVerdict::ProvenModulo3,
            "count_to_break (i≤n) break-loop refinement did not prove modulo 3",
        );
    }

    /// BREAK GENUINENESS: a wrong bound `i ≤ r` (r not the loop guard's bound) is REJECTED —
    /// the `of_decide_eq_true` proof (built for the true bound `n`) does not retype against the
    /// wrong-bound conclusion. The loop-guard component is load-bearing; the break component is
    /// genuinely unneeded. NOT `Eq.refl` of a tautology.
    #[test]
    fn trustir_break_loop_is_fail_closed() {
        assert!(
            trustir_break_loop_refinement_fail_closed(),
            "WRONG break-loop bound (`i ≤ r`, r not the guard bound) was NOT rejected — \
             soundness hole",
        );
    }

    /// BREAK `axiom_closure ⊆ FOUNDATIONAL`: the break-loop instance (and the underlying
    /// `andLeftTrue`/`stepPreservesInvBrk`/`loopInvariantRuleBrk`) rests on ⊆ the 3 axioms.
    #[test]
    fn trustir_break_loop_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        let blp = example_count_to_break_loop();
        let mut env = trustir_env().expect("trustir_env");
        let concl_ty = break_loop_conclusion_type_ir(&blp, None);
        let proof = break_loop_proof_ir(&blp);
        {
            let tc = TypeChecker::new(&env);
            tc.check_type(&proof, &concl_ty).expect("break-loop instance type-checks");
        }
        let name = Name::from_string("Trust.TrustIr.Refinement.break_loop_axiom_closure_test");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: concl_ty,
            value: proof,
        })
        .expect("add break-loop instance theorem");
        let residue = env.axiom_deps(&name).expect("axiom_deps");
        let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
        for ax in &closure {
            assert!(
                FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                "non-foundational axiom in break-loop refinement closure: {ax}",
            );
        }
        assert!(residue.is_empty(), "expected modulo-3 closure, got residue {closure:?}");
    }

    /// BREAK GENUINENESS (the combined guard is genuinely combined): the break-loop conclusion
    /// at `i ≤ n` is a DIFFERENT statement from the NON-break counter-loop conclusion at the
    /// same invariant — `execLoopBrk e cond brk body n` (combined-guarded) is NOT def-eq to
    /// `execLoop e cond body n` (single-guarded), so the break class genuinely adds the
    /// early-exit semantics (the body runs only while `cond ∧ ¬brk`).
    #[test]
    fn trustir_break_loop_is_distinct_from_plain_loop() {
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        let blp = example_count_to_break_loop();
        let plain = example_count_to_loop();
        let brk_ty = break_loop_conclusion_type_ir(&blp, None);
        let plain_ty = loop_instance_conclusion_type_ir(&plain, None);
        assert!(
            !tc.is_def_eq(&brk_ty, &plain_ty),
            "the break-loop conclusion (execLoopBrk, combined guard) MUST differ from the \
             plain-loop conclusion (execLoop, single guard) — the break component is real",
        );
    }

    // -----------------------------------------------------------------------
    // NESTED LOOP tests (this increment) — the STRATIFIED OStmt layer + the OUTER
    // while-rule `loopInvariantRuleO`, instantiated at the `while i<n { j:=0; while
    // j<m {j+=1}; i+=1 }` shape over BOTH outer-invariant classes (untouched-local
    // `t==0`, monotone `0≤s`), kernel-checked modulo 3 + fail-closed. Mirrors the
    // committed MirSem Step-6N/6NM nested-loop tests.
    // -----------------------------------------------------------------------

    /// The trust-ir nested-loop meta-theory (`OStmt`/`execO`/`stepLoopO`/`execLoopO`/
    /// `stepPreservesInvO`/`loopInvariantRuleO`) is registered AND rests on ⊆ the 3 foundational
    /// axioms — the anchor audit (extended to the nested fragment) is Modulo3.
    /// `register_loop_invariant_rule_o_ir` also `check_type`s the OUTER Hoare while-rule proof
    /// at registration (a genuine `Nat.rec` induction over the OUTER fixpoint, NOT `Eq.refl`).
    #[test]
    fn trustir_nested_loop_anchor_is_modulo3() {
        assert_eq!(pin_trustir_anchor(), AnchorVerdict::Modulo3);
    }

    /// ADDITIVITY / STRATIFICATION GUARANTEE: registering the OStmt nested layer leaves the FLAT
    /// `evalBody`/`Stmt`/`execLoop`/`loopInvariantRule` fragment BYTE-IDENTICAL — the nested
    /// env's `evalBody` value is def-eq to the flat env's (the new `OStmt` type is SEPARATE, NOT
    /// a non-additive `Stmt.Loop`). Confirms the stratified design preserves every flat-body
    /// and flat-loop certificate.
    #[test]
    fn trustir_nested_layer_keeps_flat_fragment_byte_identical() {
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        // The flat counter loop still proves at `i ≤ n` after the OStmt layer is registered.
        let lp = example_count_to_loop();
        let real = loop_instance_conclusion_type_ir(&lp, None);
        let proof = loop_instance_proof_ir(&lp);
        let inferred = tc.infer_type(&proof).expect("flat loop instance proof has a type");
        assert!(
            tc.is_def_eq(&inferred, &real),
            "the FLAT loop fragment must stay def-eq after the STRATIFIED OStmt layer (additive)",
        );
        // `evalBody` (flat) and `execO` (outer) are DISTINCT constants — the layer is stratified.
        assert!(env.get_const(&Name::from_string(TRUSTIR_EVAL_BODY)).is_some(), "evalBody present");
        assert!(env.get_const(&Name::from_string(TRUSTIR_EXEC_O)).is_some(), "execO present");
        assert!(
            env.get_inductive(&Name::from_string(TRUSTIR_OSTMT)).is_some(),
            "the SEPARATE OStmt inductive is present (stratified, not a Stmt.Loop)",
        );
    }

    /// NESTED-LOOP REFINEMENT (the headline) — UNTOUCHED-LOCAL class: the `while i < n { j := 0;
    /// while j < m { j := j + 1 }; i := i + 1 }` loop instantiated at the OUTER invariant
    /// `I := λ e. e[2] = 0` (`t == 0`), outer guard `i < n`, outer body `[j:=0; Loop(j<m,
    /// [j:=j+1], f); Assign(i, i+1)]`, fed an OUTER preservation that RUNS THE INNER LOOP TO
    /// COMPLETION (composing the inner `loopInvariantRule` at `Ir := λ e'. e'[2] = e[2]`),
    /// kernel-checks the per-function partial-correctness instance
    ///   ∀ f n e, I e → I (execLoopO e (i<n) (body f) n)
    /// modulo exactly 3 — the nested-loop synthesis frontier, closed for this shape. The OUTER
    /// fixpoint reconstructs the certified fact through the COMPLETED inner loop.
    #[test]
    fn trustir_nested_loop_refinement_untouched_modulo3() {
        let nlf = example_nested_keep_zero_loop();
        assert_eq!(
            check_trustir_nested_loop_instance(&nlf),
            RefinementVerdict::ProvenModulo3,
            "nested keep-zero (t==0) loop refinement did not prove modulo 3",
        );
    }

    /// NESTED-LOOP REFINEMENT — MONOTONE class (inner loop MODIFIES the outer-invariant
    /// variable): the `while i < n { j := 0; while j < m { s := s+1; j := j+1 }; i := i+1 }` loop
    /// instantiated at the lower bound `I := λ e. 0 ≤ e[2]` (`0 ≤ s`), fed an OUTER preservation
    /// that composes the inner loop's OWN lower-bound invariant (`Int.le_trans` +
    /// `Int.le_self_add_one`, `hI` fed DIRECTLY — `I ≡ Ir`), kernel-checks modulo 3. The inner
    /// loop increments `s` monotonically, so `0 ≤ s` survives the completed inner run.
    #[test]
    fn trustir_nested_loop_refinement_monotone_modulo3() {
        let nlf = example_sum2d_monotone_loop();
        assert_eq!(
            check_trustir_nested_loop_instance(&nlf),
            RefinementVerdict::ProvenModulo3,
            "sum2d monotone (0≤s) nested loop refinement did not prove modulo 3",
        );
    }

    /// The nested-loop WITNESS mints a modulo-3 verdict for both classes (passing the soundness
    /// guard AND the kernel check).
    #[test]
    fn trustir_nested_loop_witness_both_classes_modulo3() {
        assert_eq!(
            trustir_nested_loop_witness(&example_nested_keep_zero_loop()),
            RefinementVerdict::ProvenModulo3,
            "untouched-local witness must mint modulo 3",
        );
        assert_eq!(
            trustir_nested_loop_witness(&example_sum2d_monotone_loop()),
            RefinementVerdict::ProvenModulo3,
            "monotone witness must mint modulo 3",
        );
    }

    /// The NESTED GENUINENESS check (UNTOUCHED-LOCAL): a wrong invariant pinning a local the
    /// INNER loop WRITES (`t_idx = 4`, which `j:=j+1`/`j:=0` write) is REJECTED by the kernel —
    /// the inner `loopInvariantRule` proof's codomain `(e'[4]+1) = e[4]` is not def-eq to the
    /// hypothesis `e'[4] = e[4]`. NOT `Eq.refl` of a tautology; the nested fixpoint genuinely
    /// reconstructs the untouched-local fact.
    #[test]
    fn trustir_nested_loop_untouched_is_fail_closed() {
        assert!(
            trustir_nested_loop_refinement_fail_closed(),
            "WRONG nested invariant (t over a local the inner loop writes) was NOT rejected — \
             soundness hole",
        );
    }

    /// The NESTED GENUINENESS check (MONOTONE): a DECREMENT inner body (`s := s - 1`) breaks the
    /// monotone lower bound `0 ≤ s` — the inner preservation's `Int.le_self_add_one` codomain
    /// `0 ≤ (e' s)+1` differs from the body's reduced `0 ≤ (e' s)-1` ⇒ REJECTED. The monotone
    /// composition is GENUINE (only a non-decreasing inner update retypes).
    #[test]
    fn trustir_nested_loop_monotone_is_fail_closed() {
        assert!(
            trustir_monotone_nested_loop_refinement_fail_closed(),
            "WRONG monotone nested body (`s := s-1` decrement) was NOT rejected — soundness hole",
        );
    }

    /// The nested WITNESS soundness guard fails closed BEFORE the kernel: claiming the untouched
    /// invariant over the OUTER counter (`t_idx = counter_idx = 3`, which `Assign(i,i+1)` writes)
    /// or over a local the inner loop writes never even attempts the check; and the monotone
    /// witness rejects when the counter ≡ accumulator or the inner loop does not write `s`.
    #[test]
    fn trustir_nested_loop_witness_soundness_guards_fail_closed() {
        let over_counter = IrNestedLoop {
            inv: IrNestedInvariant::UntouchedLocal { t_idx: 3, t_const: 0 }, // = counter_idx
            ..example_nested_keep_zero_loop()
        };
        assert!(
            matches!(
                trustir_nested_loop_witness(&over_counter),
                RefinementVerdict::KernelRejected(_)
            ),
            "untouched invariant over the OUTER counter MUST be guard-rejected",
        );
        // Monotone over a non-written accumulator: pin `s_idx = 9` (inner body writes 2 and 4).
        let monotone_no_write = IrNestedLoop {
            inv: IrNestedInvariant::Monotone { s_idx: 9, c: 0 },
            ..example_sum2d_monotone_loop()
        };
        assert!(
            matches!(
                trustir_nested_loop_witness(&monotone_no_write),
                RefinementVerdict::KernelRejected(_)
            ),
            "monotone invariant over a local the inner loop does NOT write MUST be guard-rejected",
        );
    }

    /// `axiom_closure ⊆ FOUNDATIONAL` for the NESTED-LOOP refinement (BOTH classes): the
    /// per-function instance's transitive axiom closure is a SUBSET of the 3 foundational axioms
    /// — NO 4th axiom — verified against `crate::axioms::FOUNDATIONAL_AXIOMS` directly. The proof
    /// applies the kernel-checked `loopInvariantRuleO`/`loopInvariantRule` to closed terms plus
    /// def-eq/`Eq.trans`/`Int.le_trans` preservation; all modulo 3.
    #[test]
    fn trustir_nested_loop_refinement_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        for (nlf, decl) in [
            (
                example_nested_keep_zero_loop(),
                "Trust.TrustIr.Refinement.nested_untouched_axiom_closure_test",
            ),
            (
                example_sum2d_monotone_loop(),
                "Trust.TrustIr.Refinement.nested_monotone_axiom_closure_test",
            ),
        ] {
            let mut env = trustir_env().expect("trustir_env");
            let concl_ty = nested_loop_conclusion_type_ir(&nlf, None);
            let proof = nested_loop_proof_ir(&nlf);
            {
                let tc = TypeChecker::new(&env);
                tc.check_type(&proof, &concl_ty).expect("nested instance type-checks");
            }
            let name = Name::from_string(decl);
            env.add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: concl_ty,
                value: proof,
            })
            .expect("add nested instance theorem");
            let residue = env.axiom_deps(&name).expect("axiom_deps");
            let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
            for ax in &closure {
                assert!(
                    FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                    "non-foundational axiom in {decl} closure: {ax}",
                );
            }
            assert!(residue.is_empty(), "expected modulo-3 closure for {decl}, got {closure:?}");
        }
    }

    /// DEPTH GATE (> 20): the nested certificate is UNIVERSALLY quantified over BOTH the inner
    /// fuel `f` AND the outer iteration count `n`, so it is depth-UNBOUNDED by construction. We
    /// confirm that by INSTANTIATING the proven `∀ f n e, I e → I (execLoopO e cond_outer
    /// (outer_body f) n)` at CONCRETE deep `f = 25` and `n = 25` (both > 20) and an arbitrary
    /// env, then kernel-checking the resulting CLOSED specialization. A passing check means the
    /// outer invariant `t == 0` survives an outer loop of depth 25, EACH of whose iterations runs
    /// the inner loop for 25 guarded steps — a depth-25 nested run, fully faithful, modulo 3.
    #[test]
    fn trustir_nested_loop_depth_gt_20_fully_faithful() {
        let nlf = example_nested_keep_zero_loop();
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        // The general ∀f∀n∀e proof.
        let proof = nested_loop_proof_ir(&nlf);
        let general_ty = tc.infer_type(&proof).expect("nested proof has a type");
        // Specialize at f = 25, n = 25, e = the all-zero env `λ (_:Nat). Int.ofNat 0`.
        let bd = || BinderData::from(BinderInfo::Default);
        let f25 = Expr::nat_lit(25);
        let n25 = Expr::nat_lit(25);
        let zero_env = Expr::lam(bd(), nat_ty(), Expr::app(cst("Int.ofNat"), Expr::nat_lit(0)));
        // I e at the zero env: `Eq Int ((λ_.0) 2) (Int.ofNat 0)` — provable by `Eq.refl`.
        let i_at_zero = Expr::app(nlf.invariant_expr(None), zero_env.clone());
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [int_ty(), Expr::app(cst("Int.ofNat"), Expr::nat_lit(0))],
        );
        // proof f25 n25 zero_env (refl : I zero_env) : I (execLoopO zero_env … 25).
        let specialized = Expr::apps(proof, [f25, n25, zero_env, refl]);
        let _ = general_ty;
        let _ = i_at_zero;
        // The specialized closed term must type-check (a depth-25 nested run), modulo 3.
        let inferred = tc.infer_type(&specialized);
        assert!(
            inferred.is_ok(),
            "the depth-25 (>20) nested specialization must kernel-check: {inferred:?}",
        );
    }

    /// GENUINENESS (NOT collapsed): the nested OUTER conclusion (`execLoopO`, a `List OStmt`
    /// body whose `Loop` arm threads the inner `execLoop`) is a DIFFERENT statement from the FLAT
    /// counter-loop conclusion (`execLoop`, a `List Stmt` body), so the nested class genuinely
    /// adds the embedded-inner-loop semantics — the stratified `OStmt` layer is load-bearing.
    #[test]
    fn trustir_nested_loop_is_distinct_from_flat_loop() {
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        let nlf = example_nested_keep_zero_loop();
        let plain = example_count_to_loop();
        let nested_ty = nested_loop_conclusion_type_ir(&nlf, None);
        let flat_ty = loop_instance_conclusion_type_ir(&plain, None);
        assert!(
            !tc.is_def_eq(&nested_ty, &flat_ty),
            "the nested conclusion (execLoopO, List OStmt) MUST differ from the flat-loop \
             conclusion (execLoop, List Stmt) — the embedded inner loop is real",
        );
    }

    // === LAST-2 increment — CONDITIONAL-UPDATE (max_scan) + SLICE-INDEX (guarded_index) ===

    /// ADDITIVITY / STRATIFICATION GUARANTEE for BOTH last-2 layers: registering the SStmt
    /// SELECT layer and the XOperand slice layer leaves the FLAT `evalBody`/`Stmt`/`execLoop`/
    /// `loopInvariantRule` AND `evalOperand`/`Operand` fragments BYTE-IDENTICAL — the flat
    /// counter-loop instance still type-checks def-eq, and the flat operand fold is unchanged.
    /// Confirms the new `SStmt`/`XOperand` types are SEPARATE (not new `Rvalue`/`Operand` arms).
    #[test]
    fn trustir_last2_layers_keep_flat_fragment_byte_identical() {
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        // The flat counter loop still proves at `i ≤ n` after the SStmt/XOperand layers.
        let lp = example_count_to_loop();
        let real = loop_instance_conclusion_type_ir(&lp, None);
        let proof = loop_instance_proof_ir(&lp);
        let inferred = tc.infer_type(&proof).expect("flat loop instance proof has a type");
        assert!(
            tc.is_def_eq(&inferred, &real),
            "the FLAT loop fragment must stay def-eq after the STRATIFIED SStmt/XOperand layers",
        );
        // `evalBody`/`evalOperand` (flat) and `execS`/`evalXOperand` (new) are DISTINCT constants.
        assert!(env.get_const(&Name::from_string(TRUSTIR_EVAL_BODY)).is_some(), "evalBody present");
        assert!(
            env.get_const(&Name::from_string(TRUSTIR_EVAL_OPERAND)).is_some(),
            "evalOperand present"
        );
        assert!(env.get_const(&Name::from_string(TRUSTIR_EXEC_S)).is_some(), "execS present");
        assert!(
            env.get_const(&Name::from_string(TRUSTIR_EVAL_XOPERAND)).is_some(),
            "evalXOperand present",
        );
        // The SEPARATE inductives are present (stratified, not flat arms).
        assert!(
            env.get_inductive(&Name::from_string(TRUSTIR_SSTMT)).is_some(),
            "the SEPARATE SStmt inductive is present (stratified, not a Rvalue.Sel arm)",
        );
        assert!(
            env.get_inductive(&Name::from_string(TRUSTIR_XOPERAND)).is_some(),
            "the SEPARATE XOperand inductive is present (stratified, not an Operand.Index arm)",
        );
    }

    /// The CONDITIONAL-UPDATE (max_scan) SELECT loop instance `while i<n { m := if i>m { i } else
    /// { m }; i := i+1 }` instantiated at the conjoined invariant `0 ≤ m ∧ 0 ≤ i`, kernel-checks
    /// modulo 3 — the `loopInvariantRuleS` SELECT while-rule applied at this concrete loop, whose
    /// LEFT-conjunct preservation case-splits the update guard (`Bool.rec`) and uses BOTH
    /// hypothesis conjuncts. Env indices: i = 3, m = 2, n = 1.
    #[test]
    fn trustir_cond_update_max_scan_modulo3() {
        let lp = example_max_scan_loop(3, 2, 1);
        assert_eq!(
            check_cond_update_loop_instance(&lp),
            RefinementVerdict::ProvenModulo3,
            "max_scan conditional-update (0≤m ∧ 0≤i) SELECT loop refinement did not prove modulo 3",
        );
    }

    /// GENUINENESS / FAIL-CLOSED (cond-update): a WRONG invariant — claiming `1 ≤ m ∧ 1 ≤ i`
    /// (false at the `0` init) — does NOT prove. The conclusion type is built at the wrong
    /// invariant but the proof's `Int.le_self_add_one`/case-split codomains target `0 ≤ …`, so the
    /// proof is NOT def-eq to the wrong conclusion ⇒ KernelRejected. NOT `Eq.refl` of a tautology.
    #[test]
    fn trustir_cond_update_is_fail_closed() {
        let lp = example_max_scan_loop(3, 2, 1);
        let wrong = IrCondUpdateLoop { c: 1, ..lp };
        assert!(
            matches!(check_cond_update_loop_instance(&wrong), RefinementVerdict::KernelRejected(_)),
            "a WRONG cond-update invariant (1 ≤ m ∧ 1 ≤ i, false at init 0) was NOT rejected",
        );
    }

    /// SOUNDNESS GUARD (cond-update): a body that is NOT the recognized `m := Sel(i>m) i m; i :=
    /// i+1` shape (here: a plain `m := m` first stmt instead of the select) is guard-rejected
    /// BEFORE the kernel — the hard-coded preservation proof only applies to the recognized shape.
    #[test]
    fn trustir_cond_update_soundness_guard_fail_closed() {
        let lp = example_max_scan_loop(3, 2, 1);
        let mut bad = lp.clone();
        bad.body[0] = IrSStmt::Assign(2, IrRvalue::Use(IrOperand::Var(2))); // m := m (not a Sel)
        assert!(
            matches!(check_cond_update_loop_instance(&bad), RefinementVerdict::KernelRejected(_)),
            "a non-Sel cond-update body MUST be guard-rejected before the kernel",
        );
    }

    /// The BOUNDS-GUARD (guarded_index) refinement `if i < s.len() { s[i] } else { 0 }`:
    /// under the guard `i < sliceLen s = true`, the modeled select reduces to the in-bounds
    /// element `idxElem (e s)(e i)`, kernel-checked modulo 3 — the proof case-splits the guard
    /// (`Bool.rec`) and USES the guard hypothesis (TRUE arm; FALSE arm discharged by
    /// `Bool.noConfusion`/`False.elim`). MODEL-ONLY (trust-ir `idxElem`/`sliceLen` denotation).
    /// Env indices: s = 0, i = 1.
    #[test]
    fn trustir_guarded_index_bounds_refinement_modulo3() {
        let gi = example_guarded_index(0, 1);
        assert_eq!(
            check_guarded_index_refinement(&gi),
            RefinementVerdict::ProvenModulo3,
            "guarded_index bounds-guard refinement did not prove modulo 3",
        );
    }

    /// GENUINENESS / FAIL-CLOSED (guarded-index): a WRONG RHS — claiming the guarded select
    /// reduces (under the guard) to the `0` ELSE-arm default instead of the element — does NOT
    /// prove. The TRUE arm of the `Bool.rec` reduces to `idxElem s i`, NOT `0`, so the proof is
    /// not def-eq to the wrong statement ⇒ KernelRejected. Confirms the guard is load-bearing.
    #[test]
    fn trustir_guarded_index_is_fail_closed() {
        let gi = example_guarded_index(0, 1);
        // Build the statement with a WRONG RHS (the `0` default) and the genuine proof; they must
        // NOT type-check together.
        let wrong_rhs = int_lit(gi.dflt);
        let (wrong_stmt, _) = guarded_index_refinement(&gi, Some(&wrong_rhs));
        let (_, proof) = guarded_index_refinement(&gi, None);
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        assert!(
            tc.check_type(&proof, &wrong_stmt).is_err(),
            "the genuine proof must NOT type-check the WRONG (else-arm `0`) bounds claim",
        );
    }

    /// SOUNDNESS GUARD (guarded-index): the slice and index env indices must differ.
    #[test]
    fn trustir_guarded_index_soundness_guard_fail_closed() {
        let degenerate = IrGuardedIndex { s_idx: 0, i_idx: 0, dflt: 0 };
        assert!(
            matches!(
                check_guarded_index_refinement(&degenerate),
                RefinementVerdict::KernelRejected(_)
            ),
            "slice ≡ index MUST be guard-rejected",
        );
    }

    /// The cond-update + guarded-index witnesses each rest on ⊆ the 3 FOUNDATIONAL axioms — NO
    /// 4th axiom — verified against `crate::axioms::FOUNDATIONAL_AXIOMS` directly. The opaque
    /// `idxElem`/`sliceLen` selectors are `Declaration::Opaque` (NOT axioms), so they add no
    /// non-foundational dependency.
    #[test]
    fn trustir_last2_witnesses_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        // cond-update.
        {
            let lp = example_max_scan_loop(3, 2, 1);
            let mut env = trustir_env().expect("trustir_env");
            let concl_ty = cond_update_conclusion_type_ir(&lp, None);
            let proof = cond_update_instance_proof_ir(&lp);
            {
                let tc = TypeChecker::new(&env);
                tc.check_type(&proof, &concl_ty).expect("cond-update instance type-checks");
            }
            let name = Name::from_string("Trust.TrustIr.Refinement.cond_update_axiom_closure_test");
            env.add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: concl_ty,
                value: proof,
            })
            .expect("add cond-update axiom-closure decl");
            let residue = env.axiom_deps(&name).expect("cond-update closure");
            let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
            for ax in &closure {
                assert!(
                    FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                    "cond-update closure has a NON-foundational axiom: {ax}",
                );
            }
            assert!(residue.is_empty(), "expected modulo-3 cond-update closure, got {closure:?}");
        }
        // guarded-index.
        {
            let gi = example_guarded_index(0, 1);
            let mut env = trustir_env().expect("trustir_env");
            let (statement, proof) = guarded_index_refinement(&gi, None);
            {
                let tc = TypeChecker::new(&env);
                tc.check_type(&proof, &statement).expect("guarded-index refinement type-checks");
            }
            let name =
                Name::from_string("Trust.TrustIr.Refinement.guarded_index_axiom_closure_test");
            env.add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: statement,
                value: proof,
            })
            .expect("add guarded-index axiom-closure decl");
            let residue = env.axiom_deps(&name).expect("guarded-index closure");
            let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
            for ax in &closure {
                assert!(
                    FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                    "guarded-index closure has a NON-foundational axiom: {ax}",
                );
            }
            assert!(residue.is_empty(), "expected modulo-3 guarded-index closure, got {closure:?}");
        }
    }

    // =======================================================================
    // Trust: ptr-spine call-arg leaf — `IrOperand::Index`/`IrOperand::Len` (the
    // memchr `One::count` residue closure). Mirrors the `Field`/THE LIFT coverage:
    // MODEL-ONLY refinement (`check_operand_refinement_model`), never grounder-
    // connected, ⊆ the 3 foundational axioms, fail-closed on a wrong claim.
    // =======================================================================

    /// POSITIVE — the three call-arg shapes `One::count` actually passes
    /// (`start = Index(Var 1, Const 0)`, `end = Index(Var 1, Len(Var 1))`, and the
    /// bare `Len(Var 1)` sub-term standalone) each certify MODEL-ONLY modulo 3, and
    /// none is grounder-connected — the SAME honesty split `Field` carries.
    #[test]
    fn trustir_index_len_call_arg_operand_model_refinement_proven_modulo_3() {
        let start = IrOperand::Index(Box::new(IrOperand::Var(1)), Box::new(IrOperand::Const(0)));
        assert!(
            !start.is_grounder_connected(),
            "an `Index` operand must NOT be grounder-connected (same reason as `Field`)"
        );
        assert_eq!(
            check_operand_refinement_model(&start),
            RefinementVerdict::ProvenModulo3,
            "`Index(Var 1, Const 0)` (the `start` ptr-model base) must prove modulo 3"
        );

        // The exact NESTED shape `One::count` passes as `end`: `Index(Var 1, Len(Var 1))`.
        let end = IrOperand::Index(
            Box::new(IrOperand::Var(1)),
            Box::new(IrOperand::Len(Box::new(IrOperand::Var(1)))),
        );
        assert!(
            !end.is_grounder_connected(),
            "a nested `Index(.., Len(..))` must not be grounder-connected"
        );
        assert_eq!(
            check_operand_refinement_model(&end),
            RefinementVerdict::ProvenModulo3,
            "`Index(Var 1, Len(Var 1))` (the `end` ptr-model offset-by-length) must prove \
             modulo 3 — the recursor's induction hypothesis threads through BOTH levels"
        );

        let len = IrOperand::Len(Box::new(IrOperand::Var(1)));
        assert!(!len.is_grounder_connected(), "a `Len` operand must not be grounder-connected");
        assert_eq!(
            check_operand_refinement_model(&len),
            RefinementVerdict::ProvenModulo3,
            "`Len(Var 1)` must prove modulo 3"
        );
    }

    /// NEGATIVE CONTROL — a WRONG claimed denotation for an `Index` operand (an
    /// arbitrary literal instead of `idxElem (e 1) 0`) does NOT type-check against the
    /// genuine proof. Mirrors `trustir_guarded_index_is_fail_closed`'s pattern at the
    /// call-arg operand-model layer: `check_operand_refinement_model` reuses the SAME
    /// opaque `idxElem`, so a wrong claimed value fails closed (`KernelRejected`).
    #[test]
    fn trustir_index_operand_model_wrong_claim_is_fail_closed() {
        let op = IrOperand::Index(Box::new(IrOperand::Var(1)), Box::new(IrOperand::Const(0)));
        let wrong_rhs = int_lit(999); // NOT `idxElem (e 1) 0`.
        let wrong_stmt = operand_model_statement(&op, Some(&wrong_rhs));
        let proof = operand_model_proof(&op);
        let env = trustir_env().expect("trustir_env");
        let tc = TypeChecker::new(&env);
        assert!(
            tc.check_type(&proof, &wrong_stmt).is_err(),
            "the genuine proof must NOT type-check a wrong Index-arg denotation claim",
        );
    }

    /// The `Index`/`Len` operand-model witnesses rest on ⊆ the 3 FOUNDATIONAL axioms —
    /// NO 4th axiom — verified against `crate::axioms::FOUNDATIONAL_AXIOMS` directly,
    /// the SAME direct-closure discipline `trustir_last2_witnesses_axiom_closure_
    /// subset_of_three` applies to the cond-update/guarded-index witnesses.
    #[test]
    fn trustir_index_len_call_arg_axiom_closure_subset_of_three() {
        use crate::axioms::FOUNDATIONAL_AXIOMS;
        let op = IrOperand::Index(
            Box::new(IrOperand::Var(1)),
            Box::new(IrOperand::Len(Box::new(IrOperand::Var(1)))),
        );
        let mut env = trustir_env().expect("trustir_env");
        let statement = operand_model_statement(&op, None);
        let proof = operand_model_proof(&op);
        {
            let tc = TypeChecker::new(&env);
            tc.check_type(&proof, &statement)
                .expect("Index/Len operand-model refinement type-checks");
        }
        let name =
            Name::from_string("Trust.TrustIr.Refinement.index_len_call_arg_axiom_closure_test");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .expect("add Index/Len call-arg axiom-closure decl");
        let residue = env.axiom_deps(&name).expect("Index/Len call-arg closure");
        let closure: Vec<String> = residue.iter().map(ToString::to_string).collect();
        for ax in &closure {
            assert!(
                FOUNDATIONAL_AXIOMS.contains(&ax.as_str()),
                "Index/Len call-arg closure has a NON-foundational axiom: {ax}",
            );
        }
        assert!(
            residue.is_empty(),
            "expected modulo-3 Index/Len call-arg closure, got {closure:?}"
        );
    }
}
