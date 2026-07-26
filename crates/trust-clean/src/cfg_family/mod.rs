// Trust: M4 v0 — the general bounded-CFG induction framework
// (reports/m4-general-cfg-induction-framework-design-2026-07-07.md).
//
// A `CfgFamilySpec` (~20-40 lines, `spec.rs`) is compiled by an UNTRUSTED
// `TracePlanner` (`plan.rs`) into a visit trace, statically envelope-checked
// (`envelope.rs`, E1-E9 — refuse-to-generate, never watchdog), rendered into
// Lean by the `LeanEmitter` (`emit.rs`, templates T0-T4/T8, T5-C0), and run
// through the SAME kernel-checking discipline every hand-written bridge arm
// uses (`gate.rs`'s `run_generated_family`, wired into
// `trustir_bridge.rs::run_bridge_gate` via [`GENERATED_FAMILIES`]).
//
// v0 SCOPE (design §7): `Return`-terminated single-block families, T0-T4/T8,
// C0 composition only. `GENERATED_FAMILIES` below registers the family that
// mechanically regenerates the hand-written stepblock arm
// (`trustir_bridge.rs`'s `STEPBLOCK_*` — see `git show 2421e0cd55`):
// `gen_block_add_sym`, `_2 := _0 + _1; return _2` with symbolic `v_l`/`v_r`.
// `gen_block_add` (the same shape at GROUND operands) is a second,
// independent v0 family — the framework's first proof that ISN'T just a
// twin of an existing hand-written arm.
//
// M4.1 (reports/m4-v0-cfg-family-generator-landed-2026-07-08.md residue 1):
// multi-visit `Br`-chain families. `plan.rs`/`emit.rs` structurally
// supported the shape, but 3 real gaps blocked any registered family from
// exercising it end-to-end: no function ever EMITTED the `{prefix}_state{k}`
// defs `pre_state_expr` reads by name for k > 1 (`emit.rs::render_state_defs`,
// new); `render_composed` was hardcoded to exactly one visit
// (`debug_assert_eq!(plan.visits.len(), 1, …)`, now a genuine N-visit
// `And.intro` fold per design §3 T5-C0); and `render_probes` indexed
// `plan.visits[0]` and `unreachable!()`d on a non-terminal shape (now
// derives from `plan.visits.last()`, plus a new T8-rule-2-generalized
// successor-pc-mutation probe for the `Br` visits). All three are fixed in
// `emit.rs`; `gen_block_chain2`/`gen_block_chain3` below are the first
// families to actually run a k > 1 trace through the real kernel-checking
// gate. `gen_block_add`/`gen_block_add_sym` (single-visit) are untouched by
// any of this — same generated Lean, same gate behavior.

pub mod emit;
pub mod envelope;
pub mod gate;
pub mod plan;
pub mod spec;

use spec::{
    ArgSpec, BinOpLit, BlockSpec, CfgFamilySpec, ClaimSpec, ComposeLevel, InstSpec, ModeSlice,
    TermSpec, TyLit, ValueLit,
};

/// GROUND mode: `_2 := 3i8 + 4i8; return _2`. A plain `rfl` family (T1/T2) —
/// no `bridge_add` citation needed, since both operands are concrete. Not a
/// twin of any hand-written arm; demonstrates the framework's independent
/// value (a new theorem, not just a regeneration).
pub const GEN_BLOCK_ADD: CfgFamilySpec = CfgFamilySpec {
    name: "gen_block_add",
    blocks: &[BlockSpec {
        params: &[(0, TyLit::I8), (1, TyLit::I8)],
        insts: &[InstSpec::BinOp { op: BinOpLit::Add, ty: TyLit::I8, lhs: 0, rhs: 1 }],
        dests: &[2],
        term: TermSpec::Return(&[2]),
    }],
    entry: 0,
    entry_args: &[
        ArgSpec::Ground(ValueLit::Int { width: 8, value: 3 }),
        ArgSpec::Ground(ValueLit::Int { width: 8, value: 4 }),
    ],
    claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
    mode: ModeSlice::AllModes,
};

/// SYMBOLIC mode: `_2 := v_l + v_r; return _2`, `v_l v_r : Int` at `I8`. The
/// v0 MECHANICAL-REGENERATION TARGET — same fixture shape, entry types, and
/// final claim as `trustir_bridge.rs`'s hand-written
/// `evalBlockAddReturn`/`evalCfgAddReturn`/`bridge_stepblock_add_return`
/// (`STEPBLOCK_ARMS`, `git show 2421e0cd55`). Generated via `stepNWithContext`
/// + explicit `bodyResultDests` (design's canonical-evaluator rule) where the
/// hand-written arm used bare `stepN` + an explicit `.bind` — a LEGITIMATE
/// shape difference (design §6 tier (b): alpha-equivalence via elaboration,
/// not byte-identity). See the landing report's diff.
pub const GEN_BLOCK_ADD_SYM: CfgFamilySpec = CfgFamilySpec {
    name: "gen_block_add_sym",
    blocks: &[BlockSpec {
        params: &[(0, TyLit::I8), (1, TyLit::I8)],
        insts: &[InstSpec::BinOp { op: BinOpLit::Add, ty: TyLit::I8, lhs: 0, rhs: 1 }],
        dests: &[2],
        term: TermSpec::Return(&[2]),
    }],
    entry: 0,
    entry_args: &[
        ArgSpec::Symbolic { ident: "v_l", ty: TyLit::I8 },
        ArgSpec::Symbolic { ident: "v_r", ty: TyLit::I8 },
    ],
    claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
    mode: ModeSlice::AllModes,
};

/// M4.1 MULTI-VISIT #1: a 2-block straight-line `Br` chain, ALL-GROUND
/// operands (the design's "symbolic-tail-fuel" regime — regime 2 of the
/// design §1 table: ground VALUES, symbolic FUEL `∀ f`; not to be confused
/// with regime 1's symbolic-VALUE chain+connect split, which
/// `gen_block_add_sym` already exercises at a single visit and which
/// `plan.rs` itself flags as unexercised across a `Br` boundary). Shape:
/// `bb0: _2 := 3i8 + 4i8; br bb1(_2, _0)` -> `bb1: _5 := _3 - _4; return _5`
/// — 2 instruction-bearing visits (`GroundRflNonTerminal` then
/// `GroundRflTerminal`), each ≤1 block/≤1 instruction (E4), well within the
/// K_MAX = 6 visit budget (E3). Block-param ids (`3`/`4` on bb1) are chosen
/// to match what a REAL fresh-id counter would allocate after bb0's own 3
/// ids (0, 1, 2) — the same realism convention `STEPBRANCH_BODY_FIXTURES_SRC`
/// documents for its own bb1/bb2. `ModeSlice::FullOnly` (like DATALOOP):
/// this is the expensive multi-visit exercise, not the fast Spot lane.
pub const GEN_BLOCK_CHAIN2: CfgFamilySpec = CfgFamilySpec {
    name: "gen_block_chain2",
    blocks: &[
        BlockSpec {
            params: &[(0, TyLit::I8), (1, TyLit::I8)],
            insts: &[InstSpec::BinOp { op: BinOpLit::Add, ty: TyLit::I8, lhs: 0, rhs: 1 }],
            dests: &[2],
            // bb0 = 3 + 4 = 7; branch to bb1 with (the computed sum, bb0's
            // own param 0) so bb1's two incoming values are genuinely
            // distinct ground literals (7, 3).
            term: TermSpec::Br { target: 1, args: &[2, 0] },
        },
        BlockSpec {
            params: &[(3, TyLit::I8), (4, TyLit::I8)],
            insts: &[InstSpec::BinOp { op: BinOpLit::Sub, ty: TyLit::I8, lhs: 3, rhs: 4 }],
            dests: &[5],
            // bb1 = 7 - 3 = 4.
            term: TermSpec::Return(&[5]),
        },
    ],
    entry: 0,
    entry_args: &[
        ArgSpec::Ground(ValueLit::Int { width: 8, value: 3 }),
        ArgSpec::Ground(ValueLit::Int { width: 8, value: 4 }),
    ],
    claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
    mode: ModeSlice::FullOnly,
};

/// M4.1 MULTI-VISIT #2: a 3-block straight-line `Br` chain — the same
/// ground/symbolic-tail-fuel regime as [`GEN_BLOCK_CHAIN2`], one visit
/// deeper (3 instruction-bearing visits: `GroundRflNonTerminal` x2 then
/// `GroundRflTerminal`), still well inside K_MAX = 6. Shape:
/// `bb0: _2 := 2i8 + 3i8; br bb1(_2, _0)` (5, 2) ->
/// `bb1: _5 := _3 * _4; br bb2(_5, _3)` (10, 5) ->
/// `bb2: _8 := _6 - _7; return _8` (= 5). Registered per the mission's "a
/// 3-visit chain if (1) is cheap" — the per-visit cost model (design §2,
/// ~20s/visit) puts a 3rd visit well within the same order of magnitude as
/// [`GEN_BLOCK_CHAIN2`]'s 2, so it is cheap relative to the K_MAX = 6
/// envelope, not free in absolute wall-clock time. `ModeSlice::FullOnly`.
pub const GEN_BLOCK_CHAIN3: CfgFamilySpec = CfgFamilySpec {
    name: "gen_block_chain3",
    blocks: &[
        BlockSpec {
            params: &[(0, TyLit::I8), (1, TyLit::I8)],
            insts: &[InstSpec::BinOp { op: BinOpLit::Add, ty: TyLit::I8, lhs: 0, rhs: 1 }],
            dests: &[2],
            term: TermSpec::Br { target: 1, args: &[2, 0] },
        },
        BlockSpec {
            params: &[(3, TyLit::I8), (4, TyLit::I8)],
            insts: &[InstSpec::BinOp { op: BinOpLit::Mul, ty: TyLit::I8, lhs: 3, rhs: 4 }],
            dests: &[5],
            // bb1's own dest (5) and bb1's own first param (3) — both
            // bb1-LOCAL ids; a block's Br args can only cite ITS OWN params
            // or ITS OWN instruction's dest (plan.rs's `resolve`), never an
            // earlier block's raw param directly.
            term: TermSpec::Br { target: 2, args: &[5, 3] },
        },
        BlockSpec {
            params: &[(6, TyLit::I8), (7, TyLit::I8)],
            insts: &[InstSpec::BinOp { op: BinOpLit::Sub, ty: TyLit::I8, lhs: 6, rhs: 7 }],
            dests: &[8],
            term: TermSpec::Return(&[8]),
        },
    ],
    entry: 0,
    entry_args: &[
        ArgSpec::Ground(ValueLit::Int { width: 8, value: 2 }),
        ArgSpec::Ground(ValueLit::Int { width: 8, value: 3 }),
    ],
    claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
    mode: ModeSlice::FullOnly,
};

/// The registry. `trustir_bridge.rs::run_bridge_gate` calls
/// `gate::run_generated_family` once per entry (design §2's ONE call site,
/// replacing a new copy-pasted block per family).
pub const GENERATED_FAMILIES: &[CfgFamilySpec] =
    &[GEN_BLOCK_ADD, GEN_BLOCK_ADD_SYM, GEN_BLOCK_CHAIN2, GEN_BLOCK_CHAIN3];
