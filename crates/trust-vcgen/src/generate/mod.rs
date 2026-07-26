// trust_vcgen/generate.rs: Core verification condition generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{
    AggregateKind, AssertMessage, BinOp, BlockId, ConstValue, ContractKind, ContractMetadata,
    Formula, GuardCondition, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement,
    Symbol, Terminator, Ty, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

use crate::abstract_interp;

use crate::{
    contracts, ffi_summary, ffi_vcgen, guards, hardened, memory_ordering, operand_to_formula,
    place_to_var_name, rvalue_safety, sep_engine, spec_parser, termination, unsafe_verify,
};

/// Cap on the number of case-split branches a single relation may expand into
/// during `eliminate_term_ites`. A term with more `Ite`-cases than this is left
/// un-lifted (fail-open) rather than risk an exponential blowup — verdict-
/// preserving, since the backend then sees exactly the formula it does today.
const ITE_ELIM_CASE_CAP: usize = 64;

/// Build a map from block ID to accumulated path assumptions.
///
/// Path assumptions include:
/// 1. **Semantic assert-passed guards:** When a CheckedBinaryOp + Assert passes,
///    the no-overflow range constraint (e.g., hi >= lo for unsigned CheckedSub)
///    and the result definition (_N.0 = lhs op rhs) are propagated to successors.
/// 2. **Dataflow definitions:** Each assignment statement (e.g., `_4 = _3.0`,
///    `_5 = _4 / 2`) is converted to an equality constraint so the solver knows
///    intermediate locals are not free variables.
///
/// Uses BFS from the entry block, accumulating assumptions along the way.
/// Only forward propagation within the same path — assumptions respect
/// control flow.
// The canonical in-tree VC generator uses this guard-accumulation semantics
// to maintain correctness on safe-midpoint-style tests that rely on
// assert-passed dataflow (e.g., hi >= lo after CheckedSub passes).
/// Block-count budget above which `build_semantic_guard_map` returns an empty
/// map (verifier-perf). Far above any ordinary function; catches only the
/// pathologically-large kernel functions whose datatype-field block-defs blow up
/// the BFS+versioning cost. Dropping the guards is sound (it only weakens
/// PROVEs), so an oversized function fails closed, never false-proves.
///
/// 2026-07: all three caps raised 2× (blocks 800 → 1600, stmts 4000 → 8000, work
/// 200k → 400k). The per-function place-type/Sort memo (lib.rs `place_memo`)
/// collapsed the dominant per-statement VC-gen cost — the O(places × statements)
/// re-materialization of each place's declared `Ty`/`Sort` — to ONE computation
/// per distinct place, so a big-but-benign straight-line certifier (~600 lines /
/// 72 `?`-branches, ny-cert's `crown_deep::certify_impl` shape, over the old
/// 800-block cap) is now affordable to admit. The gate is NOT removed: the
/// dynamic `gen_work` meter (lib.rs `MAX_GENERATION_WORK_BUDGET`) still bounds
/// type-clone work and the hard wall-clock watchdog still bounds total time,
/// both fail-closed, for anything the larger static caps admit.
const MAX_SEMANTIC_GUARD_BLOCKS: usize = 1600;

/// Total-statement budget companion to `MAX_SEMANTIC_GUARD_BLOCKS` (2026-07:
/// raised 2× with it; see that constant's doc).
const MAX_SEMANTIC_GUARD_STMTS: usize = 8000;

/// Combined WORK budget for `build_semantic_guard_map`, measured as the
/// PER-BLOCK sum `Σ_b stmts_b × max(agg_operands_b, 1)`. The BFS versions each
/// block-def (one per aggregate field) at establish points via the
/// statement-version oracle, whose per-query cost is bounded by the statements
/// and aggregate operands OF THE QUERIED BLOCK — so a block only pays for its
/// own density, and a function's cost is the sum of its blocks' local products.
/// A previous model used the GLOBAL triple product
/// `blocks × total_stmts × total_agg_operands`, tuned on the 1-block kernel
/// shape where it coincides with the per-block sum; on many-small-blocks
/// builders (aterm-spec's `ty_model!` constructors: ~220 blocks × ~5 stmts ×
/// ~3 operands) it over-estimated real work by 500-2000× and fail-closed 73
/// functions that the CHC/PDR lane proves outright
/// (`reports/vcgen-budget-cost-model-2026-07-06.md`). The kernel outliers this
/// cap exists for (the `def_eq`/`inductive_builder`/`fmt`/`clone` cluster over
/// a recursive `Expr`/`Level`) concentrate their datatype-field aggregate
/// operands in FEW blocks, so for them the per-block sum ≈ the old product and
/// they still gate. Sized above ordinary functions (a typical ~30-block ×
/// ~150-stmt × few-operand function sums to a few hundred); only the
/// aggregate-dense outliers exceed it. (2026-07: raised 2× with the block/stmt
/// caps; see `MAX_SEMANTIC_GUARD_BLOCKS` — the place-type/Sort memo makes the
/// larger caps affordable, and the dynamic meter + wall-clock watchdog remain
/// the fail-closed backstops.)
const MAX_SEMANTIC_GUARD_WORK: usize = 400_000;

/// The bound operands of a slice-index Range-family aggregate, with enough shape
/// to build the exact panic condition `s[range]` carries. RangeInclusive (`a..=b`,
/// `+1`/overflow subtlety) and RangeFull (`..`, never panics) are intentionally
/// excluded — they are handled soundly elsewhere.
enum RangeFamilyOperands<'a> {
    /// `a..b` (`std::ops::Range`): panics when `start > end` OR `end > len`.
    Exclusive(&'a Operand, &'a Operand),
    /// `..b` (`std::ops::RangeTo`): panics when `end > len`.
    To(&'a Operand),
    /// `a..` (`std::ops::RangeFrom`): panics when `start > len`.
    From(&'a Operand),
}

/// Cap on the const-set summary cardinality: a helper whose return set is
/// larger (a big lookup table) records NO set summary — its min/max still flow
/// through the two bound summaries — so the call-site disjunction
/// `dest == c1 ∨ … ∨ dest == ck` stays small in every downstream VC.
const RETURN_CONST_SET_MAX: usize = 8;

/// Trust (derived trivial-setter summary): the exact post-call effect of a
/// TRIVIAL SETTER callee — a local fn whose ENTIRE body is the single store
/// `*p = <src>; return` through a `&mut`-integer parameter `p`. The mut-referent
/// sibling of the const-return summaries above: computed once per crate
/// ([`compute_trivial_setter_summaries`]), attached to the invocation's
/// [`crate::CalleeSummaryContext`], and consumed at call sites by
/// `build_semantic_guard_map` — a call `set(&mut a, v)` licenses the
/// staleness-versioned fact `a == v` on the success continuation, so a
/// downstream obligation over the written-through local (`assert!(a == v)`)
/// discharges instead of reading a havoc.
///
/// SOUNDNESS — the recognizer IS the proof: unlike an `#[ensures]` (a CLAIM the
/// callee must separately prove, gated by `callee_postcondition_proved`), this
/// postcondition is established syntactically by the recognized body itself.
/// [`function_trivial_setter`] admits ONLY a body whose every terminator is a
/// bare `Goto`/`Return` on one straight entry→return chain (no branch, no call,
/// no drop, no assert, no unwind source — a single store of an integer cannot
/// panic) and whose ONLY value write is the store `*p = <src>` of a whole
/// parameter or an in-range constant. Every completed call therefore stores
/// exactly `<src>` into `*p` and touches nothing else — the summary holds for
/// EVERY input on EVERY call, independent of the callee's own proof verdict.
/// Anything else fails closed to no summary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetterSummary {
    /// Declared parameter count — the call-site arity gate (a same-name callee
    /// reached with a different arity mints nothing).
    pub param_count: usize,
    /// 1-based MIR local index of the `&mut Int` parameter written through.
    pub ptr_param: usize,
    /// `(width, signed)` of the pointee integer type — cross-checked against
    /// the caller's borrow target so a mismatched binding can never misapply.
    pub pointee: (u32, bool),
    /// What the callee stores through `p`.
    pub src: SetterSrc,
}

/// The stored value of a [`SetterSummary`]: another parameter (1-based MIR
/// local index) or a pointee-range integer constant. Anything else — a computed
/// value, a projected read, a second store — fails the recognizer closed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetterSrc {
    Param(usize),
    Const(i128),
}

/// Trust (return-discriminant summary): the provable shape of the DISCRIMINANT
/// a local callee RETURNS when its return type is a MODELED flattened std
/// `Option`/`Result` (the `__tag` shape from `lower_enum_adt` — the same type
/// gate the unwrap panic-freedom lane keys on). Computed once per crate
/// ([`compute_return_disc_summaries`], mirroring the const-return machinery)
/// and consumed by the unwrap lane's SUMMARY-pinned receiver shape: a call
/// `let r = callee(a, b); r.unwrap()` gets the refutation body
/// `tag_expr(a, b) == PANIC_TAG` instead of the fail-closed UnsupportedMir row.
///
/// SOUNDNESS: the recorded shape holds for EVERY execution of the callee that
/// RETURNS — all return paths are accounted (the recognizers fail closed with
/// `None` on any construction channel they cannot see), and a PANICKING callee
/// path never returns, so a claim about the RETURNED tag is vacuous there (the
/// same argument `function_return_const_sites` documents; the call-site fact is
/// only ever conjoined onto the call's success continuation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnDiscSummary {
    /// The callee's flattened std enum def-path (`core::result::Result` /
    /// `core::option::Option` / the `std::` aliases) — cross-checked against
    /// the receiver's enum at the use site so a summary can never be applied
    /// to a receiver of a DIFFERENT enum (whose tag values may disagree).
    pub enum_name: String,
    /// The callee's formal parameter names (locals `_1..=_arg_count` under the
    /// callee's own `place_to_var_name`), in declaration order — the
    /// substitution keys for the guard-conditioned `cond`.
    pub params: Vec<String>,
    pub cases: ReturnDiscCases,
}

/// The two provable grades of [`ReturnDiscSummary`]; anything else fails
/// closed to no summary at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnDiscCases {
    /// Every reachable return site constructs the SAME variant (e.g. a helper
    /// that always returns `Ok(..)`): `tag == that variant's discriminant`.
    Unconditional { tag: i128 },
    /// The `Rat::new` shape: ONE dominating entry switch over `cond` (a
    /// comparison over the callee's never-written parameters) splits the two
    /// straight-line return arms, each constructing a distinct fixed variant:
    /// `tag == ite(cond(params), then_tag, else_tag)`.
    GuardConditioned { cond: Formula, then_tag: i128, else_tag: i128 },
}

/// Trust (INFERRED CONTRACT, bool-pred summary): the automatically-derived
/// contract of a local guard helper — `fn my_check(o: &Option<u32>) -> bool
/// { o.is_some() }` summarizes as `ret ⇔ (tag(*o) REL pred_tag)`. The fifth
/// member of the inferred-summary family (upper/lower/const-set/disc), with
/// the same keying and threading discipline. This is what replaces the
/// per-std-function allowlist for USER guard helpers: the contract is derived
/// from the BODY by a fail-closed structural proof, never trusted by name —
/// if the body changes, the summary changes; if the body is not provably a
/// pure tag predicate, nothing is recorded.
///
/// Stored STRUCTURED (not as a `Formula` over param names) because the fact
/// is about a REF param's POINTEE: callee-side its tag variable is the
/// compound `o*.0`-style spelling that whole-name substitution cannot rebind.
/// The consumer instead re-emits the fact over the CALLER's tag term resolved
/// through the borrow chain — byte-identical in shape to the probe-call
/// emission, so the observer-gate CONNECTED argument transfers verbatim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReturnBoolPredKind {
    /// `ret == true  ⇔  (tag REL pred_tag)` — the full biconditional (a pure tag
    /// predicate: is_some/matches!/discriminant switch with both arms const).
    Iff,
    /// `ret == true  ⇒  (tag REL pred_tag)` — one-directional (a payload-guarded
    /// predicate: `matches!(o, Some(x) if *x > 5)` returns true ONLY for Some,
    /// but false does not imply None). Sufficient to PROVE `if check(o){o.unwrap()}`
    /// (the positive guard), but CANNOT refute the inverse guard (stays fail-closed).
    ImpliesTrue,
    /// `ret == false  ⇒  (tag REL pred_tag)` — the mirror; proves the INVERSE
    /// guard `if check(o){} else { o.unwrap() }`.
    ImpliesFalse,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnBoolPredSummary {
    /// The pointee's flattened std enum def-path (use-site cross-check).
    pub enum_name: String,
    /// Formal parameter names (arity check; increment-2 substitution).
    pub params: Vec<String>,
    /// 1-based local index of the `&Enum`/`&Struct` param the predicate reads.
    pub pred_param: usize,
    /// The predicate's SUBJECT within the param's pointee: `None` = the whole
    /// pointee (`&Enum` param); `Some(i)` = field `i` of the pointee (`&Struct`
    /// param, `fn is_ready(&self) -> bool { self.field_i.is_some() }`). The tag
    /// term is minted over the projected place `(*param).i`.
    pub pred_field: Option<usize>,
    /// The strength of the ret↔tag relationship (biconditional or one-directional).
    pub kind: ReturnBoolPredKind,
    /// `ret == true ⇔/⇒ tag(pointee) REL pred_tag` (per `kind`).
    pub pred_tag: i128,
    /// REL is `==` (true) or `!=` (false).
    pub pred_is_eq: bool,
    /// All declared variant tags (the range fact domain).
    pub variants: Vec<i128>,
}

/// Facts from DOWNWARD induction variables: a local `i` initialized to a stable
/// slice length `B` (= `s.len()`) and updated ONLY by self-decrements
/// (`i = CheckedSub(i, c).0`, `c >= 1`) satisfies the loop invariant `i <= B`, so
/// each decrement RESULT `_t.0 = i - c` is `< B` UNCONDITIONALLY in the
/// mathematical-integer model (`i <= B`, `c >= 1` ⟹ `i - c <= B - 1 < B`; and on a
/// would-be underflow `i - c` is negative `< B`). The fact is keyed to the FRESH
/// per-decrement temp `_t.0` — which the loop-variable reassignment does not clobber
/// — so it reaches a `s[i]` access AFTER the decrement and discharges its bound.
/// This proves the ubiquitous reverse loop `let mut i = s.len(); while i > 0 { i -= 1;
/// … s[i] … }`, whose guard `i > 0` does not bound `i` above (only the init does).
///
/// SOUNDNESS rests on the downward-only analysis: `i <= B` holds iff the ONLY writes
/// to `i` are the single stable init and self-decrements. Any other write (an
/// increment, a call dest, a non-decrement rvalue, a second init) disqualifies `i`,
/// so the fact is never emitted on a non-monotone variable.
struct DownwardVar {
    /// The induction local (`i`/`hi`).
    local: usize,
    /// Its stable upper bound `B` (= `s.len()`).
    bound: Formula,
    /// Each self-decrement (`_t.0 = i - c`): `(result_local _t, constant c)`.
    decrements: Vec<(usize, i128)>,
    /// Trust (countdown-loop piece): `Some(LEN)` iff the var has EXACTLY ONE
    /// init and it is the integer constant `LEN` (the position-counting
    /// precondition of [`build_countdown_trip_facts`] — a multi-init or
    /// symbolic bound cannot justify `i = LEN - c*k` at the k-th decrement).
    single_const_init: Option<i128>,
}

/// The two emission forms of the countdown analysis (§ banner above):
///   * `global` — result-temp bounds `_t.0 >= LEN - c*T`, conjoined onto every
///     VC (the fresh temp survives the loop-carried reassignment and reaches
///     the downstream index/add obligations through the block-def chain);
///   * `per_block` — PRE-VALUE bounds `i >= LEN - c*(T-1)` at the decrement
///     block itself, the form that directly contradicts the CheckedSub
///     underflow violation (which is expressed on the pre-value version, not
///     the result temp). SOUNDNESS OF THE BARE NAME: emitted ONLY when the
///     decrement block contains NO store of the cursor, so every in-block
///     version of `i` equals its block-entry value — a same-block store would
///     let the version rename bind the POST-store value (off by `c`: a false
///     proof), so such blocks fall back to the global form only.
#[derive(Default)]
struct CountdownFacts {
    global: Vec<Formula>,
    per_block: FxHashMap<BlockId, Vec<Formula>>,
}

/// A fully-qualified (guard, companion) pair for the countdown analysis —
/// gates 4-7's output, computed PER candidate guard so a rejected companion
/// (e.g. the `size_of::<Self>() > 1` conjunct's call-dest temp in the itoa
/// macro loop condition) falls through to the next dominating candidate.
struct CountdownCompanionQual {
    gb: usize,
    t_false: usize,
    x: usize,
    m: u128,
    d_loop: u128,
    c_guard: i128,
    trips: u32,
    div_sites: Vec<(usize, u128)>,
    opaque_def_blocks: FxHashSet<usize>,
    /// The zero-trip witness source: the companion's single init is this
    /// UNWRITTEN parameter (`x = p`, `p` never written, `p != x`).
    zero_trip_src: Option<usize>,
}

// ======================================================================
// Slice-chunking iterator yield facts (`for w in s.windows(n)` / `s.chunks(n)`)
// ======================================================================
//
// `<[T]>::windows(n)` yields sub-slices of EXACTLY length `n`; `<[T]>::chunks(n)`
// yields sub-slices of length in `[1, n]` (every chunk is non-empty, the last may
// be short). So an index `w[k]` / `c[k]` into a yielded slice is bounded by the
// yielded slice's modeled length — `len == n` for windows, `1 <= len <= n` for
// chunks. Emitting that fact discharges the `w[0]/w[1]`/`c[0]` bounds obligations,
// making the ubiquitous sliding-window / chunked-processing idioms PROVE instead
// of being false-refuted (the yielded sub-slice's length is otherwise havoc'd).
// Mirrors the range yield fact, but constrains the yielded SLICE's `__slice_len`
// rather than an index value. Soundness: in the loop body a sub-slice WAS yielded,
// so windows ⇒ exactly n (an under-length tail yields None), chunks ⇒ in [1, n].
#[derive(Clone, Copy)]
enum SliceIterKind {
    /// `windows(n)`/`chunks_exact(n)`/`rchunks_exact(n)`: every yielded sub-slice
    /// has length EXACTLY `n` (the *_exact chunkers drop the short remainder).
    ExactLen,
    /// `chunks(n)`/`rchunks(n)`: every yielded sub-slice has length in `[1, n]`.
    Chunks,
}

/// Trust (inferred contract): the SUBJECT whose discriminant tag a guard
/// helper's contract constrains at a call site — a whole pinned pointee
/// (`&Enum` param, keyed by its origin LOCAL) or a field of it (`&Struct`
/// param, keyed by the field PLACE `(*base).field`). The observer gates and the
/// unwrap refutation cite the same subject so a field guard connects only to
/// that field's unwrap, never an unrelated one.
#[derive(Clone, PartialEq)]
enum InferredSubject {
    Local(usize),
    Field(Place),
}

/// Conservative per-allocation element-count ceiling for the unbounded-allocation
/// obligation (#nia-oom / availability). A single bulk allocation above ~2^28
/// elements is treated as an availability hazard unless proven smaller — sized
/// to clear legitimate content-derived allocations while flagging untrusted or
/// unbounded sizes (matches AY's own `MAX_DIMACS_VARS = 1 << 28` backstop).
const UNBOUNDED_ALLOC_ELEM_CEILING: i128 = 1 << 28;

/// Per-allocation BYTE budget (256 MiB), mirroring the trust-ir interpreter's
/// default `mem_budget`. Used to TIGHTEN the element-count ceiling for the one
/// MIR allocation whose element type is recoverable — `vec![x; n]` / `from_elem`,
/// where the element VALUE is a real typed operand (with_capacity/reserve/resize/
/// collect erase T to u8 via RawVec, so byte size is unrecoverable there; that is
/// handled at the trust-ir layer in `trust_ir::alloc_bound`). Applied ONLY to a
/// SYMBOLIC count, so a constant multi-byte allocation that already cleared the
/// element ceiling stays green and never becomes a false ground hard error.
const UNBOUNDED_ALLOC_BYTE_CEILING: i128 = 256 * 1024 * 1024;

/// `isize::MAX` in bytes on a 64-bit target. A `Vec` / `RawVec` allocation whose
/// `count * size_of::<T>()` REACHES this byte total panics with "capacity overflow"
/// at runtime (RawVec hard-caps every allocation at `isize::MAX` bytes, BEFORE the
/// availability budget matters) — a real, credited memory-safety panic. The
/// `UNBOUNDED_ALLOC_ELEM_CEILING` (count-only) obligation does NOT catch it: a
/// MULTI-BYTE element makes `count * stride` overflow `isize::MAX` while `count`
/// itself stays far below `2^28` (e.g. `Vec::<[u8; 1<<40]>::with_capacity(n)` with
/// `n < 2^27`). Trust's targets are 64-bit; on a 32-bit target the true limit is
/// smaller, so over-approximating with the 64-bit value flags only MORE (sound).
const ALLOC_CAPACITY_OVERFLOW_BYTES: i128 = (1 << 63) - 1;

/// The kind of overflowing arithmetic hidden inside a recognized `Terminator::Call`.
#[derive(Clone, Copy)]
enum OverflowCall {
    /// `base.pow(exp)` — exponentiation, modeled conservatively.
    Pow,
    /// `unchecked_{add,sub,mul}(a, b)` — UB on overflow; the inner `+`/`-`/`*`.
    Unchecked(BinOp),
}

/// The shape of a recognized slice-method panic obligation. Like [`divzero_call`]
/// for division, these library methods lower to a `Terminator::Call` that carries
/// no caller-visible `Projection::Index` (so the rvalue-safety bounds path never
/// sees them) yet panic at runtime on an out-of-range argument — a false PROVE
/// without this recognizer. Each variant names the 0-based MIR `args` index of the
/// length-relative argument(s); the receiver slice lowers to arg 0.
enum SliceMethodPanic {
    /// `s.split_at(mid)` / `split_at_mut(mid)`: PANICS when `mid > len`. The
    /// split point `mid` is arg 1. Obligation: `mid <= len` (failure `mid > len`).
    SplitAt { mid_idx: usize },
    /// `s.chunks(n)` / `windows(n)` / `chunks_exact(n)` (and the `_mut`/`r`*
    /// variants): PANIC when `n == 0`. The chunk size `n` is arg 1. Obligation:
    /// `n != 0` (failure `n == 0`) — identical to the `step_by` non-zero shape,
    /// so it carries the same `DivisionByZero` tag the `!= 0` obligation uses.
    NonZeroArg { n_idx: usize },
    /// `s.swap(i, j)`: PANICS when `i >= len || j >= len`. The indices are args
    /// 1 and 2. Obligation: both `< len` (failure `i >= len OR j >= len`).
    SwapIndices { i_idx: usize, j_idx: usize },
    /// `s[a..b]` / `s[..b]` / `s[a..]` — a `Range`/`RangeTo`/`RangeFrom` slice
    /// index, lowered to `<[T] as Index<R>>::index(s, range)`. The bounds check
    /// lives INSIDE the opaque stdlib `index`, so the rvalue-bounds path never
    /// sees it (unlike scalar `s[i]`'s MIR `Assert(Lt(i, Len))`). Without this the
    /// range index is reported vacuously safe — a false PROVE for an unchecked
    /// end/start. `slice_method_panic_body` finds the slice receiver (modeled
    /// `len`) and the range argument by SCANNING the call operands (robust to the
    /// `Index::index(slice, range)` order) and traces the range aggregate to the
    /// precise `start > end ∨ end > len` (exclusive) / `end > len` (To) /
    /// `start > len` (From) failure. RangeFull is skipped (never panics);
    /// RangeInclusive fails closed (the `+1` is not modeled here).
    RangeIndex,
    /// `v.remove(i)`/`v.swap_remove(i)` (panic `i >= len`) and `v.insert(i, x)` (panic
    /// `i > len`) on an OWNED `Vec` — a `&mut self` resize method whose bounds check
    /// lives inside the opaque stdlib impl, so nothing was emitted before and an
    /// unguarded `v.remove(i)` was reported vacuously safe (a pillar-1 FALSE-ACCEPT).
    /// `insert` widens the bound to `i <= len` (append at `i == len` is legal).
    /// Vec-discriminated in the body so Option/bool-returning
    /// `HashMap`/`BTreeMap`/`VecDeque`/`HashSet::remove`/`insert` (never panic) and the
    /// byte-boundary-panicking `String::remove`/`insert` are NOT matched. Index is arg 1.
    VecPanicMethod { index_idx: usize, insert: bool },
}

enum LocalDef<'a> {
    Rvalue(&'a Rvalue),
    Call { callee: &'a str, args: &'a [Operand] },
}

/// Linear comparison shapes recognized by the BV guard translation.
#[derive(Clone, Copy)]
enum BvGuardCmp {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

struct V2FloatOverflowContext<'a> {
    func: &'a VerifiableFunction,
    block: &'a trust_types::BasicBlock,
    span: &'a SourceSpan,
    stmt_index: usize,
    /// F6: callee interval summaries for the discharge tracer (`None` keeps the
    /// summary arm inert — fail-closed).
    summaries: Option<&'a crate::modular::SummaryDatabase>,
}

/// Fuel-bounded recursion depth for the float interval tracer (`float_range`).
const FLOAT_EXP_BOUND_FUEL: u32 = 32;

/// Max nesting for the struct-leaf walk (`Mat4 -> cols -> [Vec4;4] -> field`
/// is depth 3); a deeper aggregate simply stops contributing overrides.
const FLOAT_STRUCT_LEAF_DEPTH: u32 = 6;

/// Longest array whose f64 elements are enumerated for per-field overrides.
const FLOAT_STRUCT_LEAF_ARRAY_LIMIT: u64 = 16;

// ---------------------------------------------------------------------------
// F0/F1 — the signed-interval float tracer (`float_range`) and its consumers.
// ---------------------------------------------------------------------------
/// NaN discipline a [`float_range`] result promises.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FloatNanMode {
    /// `Some((lo, hi))` ⇒ the value is ALWAYS finite, inside `[lo, hi]`, and
    /// never NaN — whenever the function's gated preconditions and the
    /// dominating guards of the reading block hold. Required by every consumer
    /// that EVALUATES a comparison on the value (F5 precondition dominance, F6
    /// summary derivation): a NaN makes every IEEE ordering false, so an
    /// interval claim without NaN-freedom proves no comparison.
    Forbid,
    /// `Some((lo, hi))` ⇒ the value is NaN, OR finite inside `[lo, hi]` — in
    /// particular this op chain never CREATES a ±inf from finite inputs. The
    /// legacy `float_exp_bound` contract (`f64::clamp` passes a NaN self
    /// through; sin/cos of ±inf is NaN; every arithmetic combination of a NaN
    /// is NaN). Sufficient for the overflow-to-infinity discharge: a NaN
    /// result is not an overflow TO INFINITY. One inherited caveat: the
    /// f32→f64 widening arm PROPAGATES an already-infinite f32 input — that is
    /// not a fresh overflow of the traced chain (the witness this mode
    /// discharges constrains finite-operand overflow), but it is why `Forbid`
    /// rejects that arm outright.
    NanOrBounded,
}

/// Recursion work budget for one [`FloatRangeCtx`]. The multi-def HULL makes
/// the def walk a DAG (defs × operands × depth), so the linear `fuel` alone
/// does not bound the node count; the budget does, fail-closed. SHARED across
/// nested callee-trace contexts (F6b), so the whole interprocedural trace —
/// not each nesting level — is bounded by this one budget.
const FLOAT_RANGE_WORK: u32 = 4096;

/// F6b: maximum interprocedural nesting of context-sensitive callee traces
/// (`float_callee_trace_range`). Small by design: the a3d-shaped chains are
/// 2–3 constructors/combinators deep, and each level multiplies trace work.
/// Refusal past the limit is `None` (fail-closed).
const FLOAT_INTERPROC_DEPTH: usize = 3;

/// Shared per-function context for [`float_range`]: the dominating path-guard
/// map is built lazily ONCE and the per-block INTERSECTED fact set memoized
/// (mirroring `v2_bv_mul_dominating_guard_constraints`, which rebuilds the map
/// per multiply — one tracer call tree may consult many blocks).
struct FloatRangeCtx<'a> {
    func: &'a VerifiableFunction,
    /// F6: callee interval summaries. `None` on every legacy path — the
    /// call-dest arm then simply never fires (fail-closed).
    summaries: Option<&'a crate::modular::SummaryDatabase>,
    /// F6b (context-sensitive callee tracing): CALLER-proved intervals for
    /// this function's formals, keyed by formal local index — the caller's
    /// proven `float_range` of the actual at ONE specific call site. An
    /// override is an ENTRY fact under exactly the contract-fact discipline:
    /// it is consulted ONLY where a `contract_range` entry fact would be
    /// (a defless — hence never-written, never-aliased — formal read), so a
    /// reassigned/aliased parameter can never consume it. Values are
    /// `FloatNanMode::Forbid`-strength (finite, ordered), matching the claim
    /// `contract_range` makes for a gated precondition. Empty on every
    /// non-callee-trace context.
    param_overrides: FxHashMap<usize, (f64, f64)>,
    /// F6b (STRUCT-argument tracing): CALLER-proved intervals for the SCALAR
    /// FIELD LEAVES of this function's struct/vector formals, keyed by the
    /// callee-side rendered place name (`place_to_var_name` + index
    /// canonicalization — e.g. `"self.0"`, `"m.0[0].1"`). A scalar
    /// `param_override` cannot bound `Vec3::add`'s `self.0` when the caller
    /// passed a whole `Vec3`; this per-field map carries the callsite-specific
    /// interval of the ACTUAL's corresponding field (`self_min.0`), letting a
    /// matrix/vector CHAIN (`center = min.add(max).scale(0.5)` — every a3d
    /// residual) discharge against the callee's own contract requirement. Same
    /// ENTRY-fact discipline as `param_overrides`; empty off the callee-trace.
    param_field_overrides: FxHashMap<String, (f64, f64)>,
    guard_map: std::cell::OnceCell<FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>>>,
    guard_facts: std::cell::RefCell<FxHashMap<BlockId, std::rc::Rc<Vec<Formula>>>>,
    alias_names: std::cell::RefCell<FxHashMap<usize, std::rc::Rc<Vec<String>>>>,
    /// Work budget — SHARED (one `Rc`) with every nested callee-trace context
    /// spawned from this one, so interprocedural fan-out cannot multiply it.
    work: std::rc::Rc<std::cell::Cell<u32>>,
    /// F6b recursion cut: the stack of callee names whose bodies are being
    /// traced right now, shared across nesting. Doubles as the depth gauge
    /// (`len() >= FLOAT_INTERPROC_DEPTH` refuses) and the cycle guard (a
    /// callee already on the stack refuses — direct or mutual recursion has
    /// no closed form here).
    visiting_callees: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
    /// F6b trace memo — SUCCESSFUL callee-trace results, shared (one `Rc`)
    /// across every nested context of one top-level tracer invocation. The
    /// same (call block, callee, args, suffix) query recurs massively in
    /// wide callers (`mul_mat4`: 16 dot callsites × 16 precondition
    /// conjuncts each re-tracing the same four `row(..)` results), and the
    /// un-memoized recomputation exhausted the shared work budget mid-
    /// function — later callsites then refused NOT for any semantic reason
    /// but because the meter died (a completeness cliff). ONLY `Some`
    /// results are cached: a successful trace's own depth/cycle checks
    /// passed during computation, so its enclosure is context-independent;
    /// a refusal may be stack-dependent (deeper nesting, mid-cycle) and is
    /// NEVER cached (fail-closed recomputation).
    trace_memo: std::rc::Rc<std::cell::RefCell<FxHashMap<(BlockId, String, String, String), (f64, f64)>>>,
}

impl<'a> FloatRangeCtx<'a> {
    fn new(
        func: &'a VerifiableFunction,
        summaries: Option<&'a crate::modular::SummaryDatabase>,
    ) -> Self {
        Self {
            func,
            summaries,
            param_overrides: FxHashMap::default(),
            param_field_overrides: FxHashMap::default(),
            guard_map: std::cell::OnceCell::new(),
            guard_facts: std::cell::RefCell::new(FxHashMap::default()),
            alias_names: std::cell::RefCell::new(FxHashMap::default()),
            work: std::rc::Rc::new(std::cell::Cell::new(FLOAT_RANGE_WORK)),
            trace_memo: std::rc::Rc::new(std::cell::RefCell::new(FxHashMap::default())),
            visiting_callees: std::rc::Rc::new(std::cell::RefCell::new(Vec::new())),
        }
    }

    /// F6b: a context for tracing INSIDE a callee's extracted body, carrying
    /// the caller-derived formal overrides and SHARING the caller context's
    /// work budget and callee-visiting stack (the guard/alias caches are
    /// per-function and start fresh).
    fn for_callee(
        parent: &FloatRangeCtx<'a>,
        func: &'a VerifiableFunction,
        param_overrides: FxHashMap<usize, (f64, f64)>,
        param_field_overrides: FxHashMap<String, (f64, f64)>,
    ) -> Self {
        Self {
            func,
            summaries: parent.summaries,
            param_overrides,
            param_field_overrides,
            guard_map: std::cell::OnceCell::new(),
            guard_facts: std::cell::RefCell::new(FxHashMap::default()),
            alias_names: std::cell::RefCell::new(FxHashMap::default()),
            work: std::rc::Rc::clone(&parent.work),
            visiting_callees: std::rc::Rc::clone(&parent.visiting_callees),
            trace_memo: std::rc::Rc::clone(&parent.trace_memo),
        }
    }

    /// Spend one unit of the work budget; `None` (fail-closed) once exhausted.
    fn spend(&self) -> Option<()> {
        let left = self.work.get();
        if left == 0 {
            return None;
        }
        self.work.set(left - 1);
        Some(())
    }

    /// F6b: the validated caller-proved interval for formal `local`, or `None`.
    /// The map is only ever keyed by formals, but the parameter check is
    /// repeated here (fail-closed against any future mis-keyed producer), and
    /// the interval shape is re-validated exactly like
    /// `float_summary_result_range` re-validates a stored summary interval.
    fn param_override(&self, local: usize) -> Option<(f64, f64)> {
        if local < 1 || local > self.func.body.arg_count {
            return None;
        }
        let (lo, hi) = *self.param_overrides.get(&local)?;
        (lo.is_finite() && hi.is_finite() && lo <= hi).then_some((lo, hi))
    }

    /// F6b: the caller-proved interval for a PROJECTED formal-field read (a leaf
    /// of a struct/vector formal), keyed by the callee-side rendered place name.
    /// Only a place ROOTED at a formal parameter is looked up (the map is keyed
    /// by formal-rooted names the binder produced); the interval is re-validated
    /// like `param_override`.
    fn param_field_override(&self, place: &Place) -> Option<(f64, f64)> {
        if place.local < 1 || place.local > self.func.body.arg_count {
            return None;
        }
        let name =
            canonicalize_contract_index_segments(&crate::place_to_var_name(self.func, place));
        let (lo, hi) = *self.param_field_overrides.get(&name)?;
        (lo.is_finite() && hi.is_finite() && lo <= hi).then_some((lo, hi))
    }

    /// The guard facts present on EVERY enumerated path into `block_id` — the
    /// BV-mul lane's dominance criterion verbatim: per-block saturation records
    /// one unguarded path (empty intersection), cap-overflow degrades the whole
    /// map to unguarded paths, and a block missing from the map has no
    /// enumerated path at all (no facts). Memoized per block.
    fn dominating_facts(&self, block_id: BlockId) -> std::rc::Rc<Vec<Formula>> {
        if let Some(facts) = self.guard_facts.borrow().get(&block_id) {
            return std::rc::Rc::clone(facts);
        }
        let map = self.guard_map.get_or_init(|| v2_build_path_guard_map(self.func));
        let facts: Vec<Formula> = map
            .get(&block_id)
            .map(|paths| {
                let resolved: Vec<Vec<Formula>> = paths
                    .iter()
                    .map(|gs| {
                        gs.iter().map(|(_, g)| guards::guard_to_formula(self.func, g)).collect()
                    })
                    .collect();
                match resolved.split_first() {
                    None => Vec::new(),
                    Some((first, rest)) => first
                        .iter()
                        .filter(|fact| rest.iter().all(|path| path.contains(fact)))
                        .cloned()
                        .collect(),
                }
            })
            .unwrap_or_default();
        let facts = std::rc::Rc::new(facts);
        self.guard_facts.borrow_mut().insert(block_id, std::rc::Rc::clone(&facts));
        facts
    }

    /// The var names a dominating guard fact about the PLAIN local `place` may
    /// be spelled under: the place's own name, plus every SINGLE-def copy temp
    /// of it (`_4 = copy len` — the resolved guard compares `_4` while the op
    /// reads `len`; the temp's one def pins its value to `len`'s, and the
    /// caller has already required `len` itself value-stable). Memoized.
    fn guard_alias_names(&self, place: &Place) -> std::rc::Rc<Vec<String>> {
        if let Some(names) = self.alias_names.borrow().get(&place.local) {
            return std::rc::Rc::clone(names);
        }
        let mut names = vec![crate::place_to_var_name(self.func, place)];
        for decl in &self.func.body.locals {
            let l = decl.index;
            if l == place.local {
                continue;
            }
            // A parameter's entry value is an invisible extra def — its one
            // visible `Use(copy place)` def does NOT pin its value at every
            // read (same discipline as the tracer's whole-local arm).
            if l >= 1 && l <= self.func.body.arg_count {
                continue;
            }
            let Some(defs) = float_whole_local_defs(self.func, l) else { continue };
            if defs.len() != 1 {
                continue;
            }
            let FloatLocalDef::Rvalue {
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } = &defs[0]
            else {
                continue;
            };
            if src.local == place.local && src.projections.is_empty() {
                names.push(crate::place_to_var_name(self.func, &Place::local(l)));
            }
        }
        let names = std::rc::Rc::new(names);
        self.alias_names.borrow_mut().insert(place.local, std::rc::Rc::clone(&names));
        names
    }
}

/// A whole-local def of a traced local: an `Assign` rvalue or a `Call` dest,
/// paired with its defining block — the def's operands are READ at that block,
/// so ITS dominating guards are the ones that constrain them.
enum FloatLocalDef<'a> {
    Rvalue { block: BlockId, rvalue: &'a Rvalue },
    Call { block: BlockId, callee: &'a str, args: &'a [Operand] },
}

/// Discharge margin for the interval lane: `2^1020` (biased exponent field
/// 1020 + 1023 = 2043), an 8× headroom under `f64::MAX ≈ 2^1024`. Result
/// endpoints inside `±2^1020` provably cannot round to ±inf.
const FLOAT_OVERFLOW_DISCHARGE_MARGIN: f64 = f64::from_bits(0x7FB0_0000_0000_0000);

/// Tiny-addend bound for the one-sided Add/Sub discharge: `2^970 =
/// ulp(f64::MAX) / 2` (biased exponent field 970 + 1023 = 1993). For FINITE
/// `a`, `b` with `|b| < 2^970`: `|a ± b| <= |a| + |b| < MAX + 2^970`, which is
/// EXACTLY the round-to-infinity boundary under round-to-nearest (values
/// strictly below `MAX + ulp(MAX)/2` round to at most MAX; at the boundary the
/// tie goes to inf because MAX's significand is odd) — so the op cannot CREATE
/// an infinity, whatever the other FINITE operand is. A non-finite other
/// operand PROPAGATES (NaN→NaN, ±inf→±inf), which the finite-operand witness
/// this discharges does not model as an overflow of THIS op. This is why
/// `x + 0.05` needs no bound on `x`, while `x + 1e300` (2^996 ≥ 2^970)
/// correctly keeps its obligation (the round-10 one-sided false-proof shape).
const FLOAT_ADD_TINY_OPERAND_BOUND: f64 = f64::from_bits(0x7C90_0000_0000_0000);

/// Retired block-granularity reaching-def oracle retained as a test witness for
/// the statement-granular production versioning.
#[cfg(test)]
pub(crate) struct VersionCtx {
    per_block: FxHashMap<BlockId, FxHashMap<String, std::collections::BTreeSet<i64>>>,
}

#[cfg(test)]
impl VersionCtx {
    pub(crate) fn build(func: &VerifiableFunction) -> Self {
        VersionCtx { per_block: reaching_def_versions(func) }
    }

    /// `#token` suffix for `name` at `block`'s OUT-point, or `None` when the
    /// version is exactly `{-1}` (entry/unversioned) — so unversioned names stay
    /// byte-identical when the naming flip lands (mirrors `ArrayVersionCtx`).
    pub(crate) fn version_token(&self, block: BlockId, name: &str) -> Option<String> {
        let s = self.per_block.get(&block)?.get(name)?;
        if *s == std::collections::BTreeSet::from([-1i64]) {
            return None;
        }
        Some(
            s.iter()
                .map(|w| if *w < 0 { "e".to_string() } else { w.to_string() })
                .collect::<Vec<_>>()
                .join("_"),
        )
    }

    /// OVERLAP-AWARE staleness query (S2b): is a fact whose sole free var is `name`
    /// stale at `block`? True iff some TRACKED name that OVERLAPS `name`
    /// (prefix-ancestor / descendant / index-alias via `place_names_overlap`) has a
    /// non-entry reaching-def version at `block`.
    ///
    /// This closes the projection gap the shadow audit surfaced: the oracle tracks
    /// whole gen-set names (`s`), but the kill drops a fact about `s.0` via overlap
    /// with a write to `s`. Because the kill's drop set IS the tracked-names with a
    /// non-entry version (the proven base parity) and both sides use the SAME
    /// `place_names_overlap`, this query is drop-equivalent to the kill for ANY
    /// `name`, tracked or not — so a versioned read of `s.0` is renamed away exactly
    /// when the kill would drop the fact.
    pub(crate) fn is_versioned_query(&self, block: BlockId, name: &str) -> bool {
        let entry_only = std::collections::BTreeSet::from([-1i64]);
        let Some(vers) = self.per_block.get(&block) else { return false };
        vers.iter().any(|(tracked, vset)| *vset != entry_only && place_names_overlap(tracked, name))
    }
}

/// Per-block ENTRY reaching-def versions (the IN-sets of the reaching-def
/// dataflow — version BEFORE any of the block's own writes). The inter-block part
/// of the statement-granular version; within a block it is overridden by
/// `writes_until`.
/// The entry-set sentinel for a name whose reaching value at a block entry is the
/// function-ENTRY/parameter value (the inter-block analogue of `version_token_at`
/// returning `None`). Cannot collide with a real OUT token (those start with `s`).
pub(crate) const ENTRY_VERSION_SENTINEL: &str = "e";

/// Statement-granular version oracle: the version of a place name at a precise
/// `(block, stmt_idx)` program point, distinguishing reads that straddle a
/// same-block write.
pub(crate) struct StmtVersionCtx {
    entry: FxHashMap<BlockId, FxHashMap<String, std::collections::BTreeSet<String>>>,
}

impl StmtVersionCtx {
    pub(crate) fn build(func: &VerifiableFunction) -> Self {
        StmtVersionCtx { entry: block_entry_versions(func) }
    }

    /// `#token` for `name` read at `(block, stmt_idx)`, or `None` when the value
    /// there is the entry/parameter value (so unversioned names stay byte-identical
    /// on the flip). A same-block write in `stmts[..stmt_idx]` versions it; a write
    /// LATER in the block does NOT (the block-level oracle gets this wrong).
    pub(crate) fn version_token_at(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> Option<String> {
        // Trust (lane-A CSE): id==index invariant (held by direct `blocks[id.0]`
        // indexing elsewhere) lets the linear find be an O(1) indexed lookup. The
        // `.filter(|b| b.id == block)` keeps it BEHAVIORALLY IDENTICAL — same
        // `Option<&BasicBlock>`, same `None` were the invariant ever violated.
        let bb = func.body.blocks.get(block.0).filter(|b| b.id == block)?;
        // In-block write before the read point wins (the live value at stmt_idx).
        // Trust #soundness (callee-write false-accept sweep): the gate is
        // OVERLAP-aware, matching the `stmt_writes_name` token search below — the
        // old exact-name `.contains(name)` let an overlapping statement write
        // (whole-place `s = ..` before a field read `s.v`; a havoc of `r` before
        // a pointee read `r*`) pass the search yet be gated out here, silently
        // falling through to the entry map with the write invisible.
        if writes_until(func, bb, stmt_idx).iter().any(|w| place_names_overlap(w, name)) {
            // P-A: the LATEST single statement < stmt_idx that ITSELF writes an
            // overlap of `name` gives a point-distinct token. Test each statement
            // directly (`stmt_writes_name`), NOT the cumulative `writes_until` delta —
            // that delta is nonzero only at the FIRST write, so two same-block writes
            // (and def-then-deref-havoc) collapsed to one token, defeating the
            // statement-granular distinction the oracle exists to provide.
            let j = (0..stmt_idx.min(bb.stmts.len()))
                .rev()
                .find(|&k| stmt_writes_name(func, bb, k, name));
            return Some(match j {
                Some(k) => format!("s{}_{k}", block.0),
                None => format!("s{}_pre", block.0), // entry-block param havoc, no stmt
            });
        }
        // Else the inter-block reaching set at block entry. The tokens are already
        // statement-granular `s{pred}_{k}` strings (`e` = entry/param value).
        //
        // Trust #soundness (callee-write false-accept sweep — THE CORE FIX): the
        // lookup is an OVERLAP UNION, not an exact-key get. The confirmed silent
        // false-accept: `if *r < 1000 { bump(r); t = *r + 1 }` where `bump` sets
        // `*r = u32::MAX` — the Call havocs the BASE name "r" (entry map of the
        // successor holds {"r" -> {s1_t}}), but the post-call READ spells "r*";
        // the exact-key get missed it, both `*r` reads stayed the SAME bare SMT
        // var, and the guard bound falsely transferred across the call (verified
        // "1 proved" yet panics at runtime). With the overlap union, the
        // entry-versioned base "r" versions the pointee read to `r*#s1_t`,
        // name-disjoint from the pre-call bare guard read — the transfer is
        // severed. Deterministic per (block, name): the BTreeSet-sorted join
        // gives two post-call reads at the same block ONE shared token, so a
        // post-call guard still discharges a post-call use (no over-splitting).
        // An all-entry union stays `None` (bare, never-havoced parameter reads
        // stay byte-identical). A MIXED union keeps the entry sentinel IN the
        // join (`e_s1_t`): a partially-entry-valued read has a DIFFERENT
        // reaching-value set than a definitely-post-write read (`s1_t`), and
        // collapsing the two names would assert a false cross-path equality.
        let em = self.entry.get(&block)?;
        let mut toks: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for (k, s) in em {
            if place_names_overlap(k, name) {
                toks.extend(s.iter().cloned());
            }
        }
        if toks.is_empty()
            || toks == std::collections::BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()])
        {
            return None;
        }
        Some(toks.iter().cloned().collect::<Vec<_>>().join("_"))
    }

    /// Overlap-aware staleness at a precise point: is a fact whose sole free var is
    /// `name` stale at `(block, stmt_idx)`? True iff some name written in
    /// `stmts[..stmt_idx]` OR entry-versioned overlaps `name`.
    #[cfg(test)]
    pub(crate) fn is_versioned_stale_at(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> bool {
        let entry_only = std::collections::BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()]);
        // Trust (lane-A CSE): id==index invariant → O(1) indexed lookup; the
        // `.filter` preserves the exact `None`-on-violation behavior of the find.
        let Some(bb) = func.body.blocks.get(block.0).filter(|b| b.id == block) else {
            return false;
        };
        let mut redefined = writes_until(func, bb, stmt_idx);
        if let Some(em) = self.entry.get(&block) {
            redefined.extend(em.iter().filter(|(_, v)| **v != entry_only).map(|(k, _)| k.clone()));
        }
        redefined.iter().any(|n| place_names_overlap(n, name))
    }
}

/// Which modeled std wrapper enum a return-slot aggregate constructs. The two
/// differ in how their MACHINE variant order maps onto the spec parser's MODEL
/// discriminant convention — see [`std_enum_model_discr`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StdEnumReturn {
    Option,
    Result,
}

thread_local! {
    /// Def-path of the function whose contract VCs are currently being
    /// generated — set by the lane entry so the `func`-less helpers can prefix
    /// their debug lines. Only ever written under the debug gate.
    static LENWITNESS_DBG_FN: std::cell::RefCell<String> =
        const { std::cell::RefCell::new(String::new()) };
}

/// One diagnostic line, `LENWITNESS: [<def_path>] <fact>`, only when the env
/// gate is set. Takes an explicit def-path (helpers that hold `func` pass
/// `&func.def_path`; the two `func`-less helpers pass `&lenwitness_dbg_fn()`).
macro_rules! lenwitness_dbg {
    ($who:expr, $($arg:tt)*) => {
        if lenwitness_debug() {
            // Named args so the expansion never trips `clippy::uninlined_format_args`
            // regardless of the `$who` expression passed by the call site.
            eprintln!("LENWITNESS: [{who}] {msg}", who = $who, msg = format!($($arg)*));
        }
    };
}

// ======================================================================
// Len-witness return grounding (b62): `_0_value.<i>.<j>…_len` model terms
// ======================================================================
//
// The F5 matches!-guard lowering emits `#[ensures]` predicates over the
// payload-component LENGTH terms the spec parser mints for
// `result.unwrap().<i>.<j>.len()` — `_0_value.<i>.<j>_len` (`Sort::Int`) — and
// the spec-model split in `generate_v2_contract_vcs_impl` routes any
// postcondition referencing them to the fail-closed SpecModelUngrounded
// Unknown, because NO body fact grounds them (the ny-cert crown/crown_deep
// producer well-formedness rows: `!matches!(r, Ok(c) if c.entailment.premises
// .len() != c.entailment.multipliers.len())`).
//
// This lane grounds EXACTLY the equal-length idiom those contracts state — a
// PAIR of length terms compared for (in)equality — and nothing else:
//
//  * WHICH pairs (the coverage gate, `len_pair_coverage`): only pairs of
//    parseable `_0_value.<path>_len` names whose EVERY occurrence across EVERY
//    declared postcondition sits inside an `Eq(len_a, len_b)` atom (the parser
//    lowers `!=` to `Not(Eq(..))`, so both polarities reduce to `Eq` atoms).
//    A length term used in ANY other position (an arithmetic bound, a
//    comparison against a constant …) keeps the whole pair UNCREDITED, so a
//    partially-constrained length can never turn today's honest Unknown into a
//    refutable VC minted over an under-constrained encoding (the P6
//    Unknown→FAILED hazard).
//
//  * WHAT is emitted (the pins, `len_witness_path_pins`): per RETURN PATH
//    whose `_0` resolves to the payload-variant in-body aggregate
//    (`Ok(move src)` / `Some(move src)` — the same `resolve_enum_return_…`
//    walk the discr pin uses), the equality fact
//    `Eq(_0_value.<a>_len, _0_value.<b>_len)` — derived ONLY from the MIR
//    construction chain, never from the contract — plus, when the equality
//    was established by a length GUARD, the individual witness pins
//    `Eq(_0_value.<a>_len, <len-call dest>)`. Two derivations:
//      (1) GUARD lane (`dominating_len_equality_guard`): a `SwitchInt` on
//          `Eq/Ne(<len of component a>, <len of component b>)` whose
//          EQUALITY edge dominates the aggregate block (structural
//          `reachable_avoiding` dominance, mirroring `push_guarded_bound`)
//          while the inequality edge cannot reach it — the ny-side
//          fail-closed guard `if c.…premises.len() != c.…multipliers.len()
//          { return Err(..) }` before `Ok(c)`. Each compared length local is
//          the unique dest of a `Vec::len` call whose receiver borrows the
//          component PLACE (`operand_is_len_of_place`), and every place root
//          is `place_source_is_stable` — so the compared lengths equal the
//          returned component lengths.
//      (2) CONSTRUCTION lane (`paired_push_equal_lengths`): both components
//          trace through single-def positional aggregates to leaf `Vec`
//          locals created EMPTY, mutated ONLY by `Vec::push`
//          (`vec_created_empty` / `vec_mut_borrows_only_feed_push` — the
//          push-guard lane's discipline), whose pushes are 1:1
//          CHAIN-COUPLED (each push of one leaf is followed, through
//          single-successor/single-predecessor blocks that never touch
//          either leaf, by exactly one push of the other) — so the two
//          lengths are equal at every block outside a pair interior, in
//          particular at the aggregate construction.
//
//  * EVERY-RETURN-PATH discipline (the gate, `len_witness_credited_pairs`):
//    a pair is credited — i.e. its names removed from the ungrounded set so
//    the postcondition reaches the refutable body-aware lane — ONLY when
//    every Return path either constructs the EMPTY variant in-body (the
//    length terms have no denotation there; leaving them free on that path
//    is sound — a free var only adds SAT/refutability, never manufactures a
//    proof) or yields the pins above. One unresolvable path fails the whole
//    pair closed, exactly like the discr gate.
//
// SOUNDNESS (no false-PROVE): every emitted fact is TRUE of the actual
// returned value on its return path — the guard lane's lengths are unique
// stable len-call results over stable places compared on a dominating
// equality edge, and the construction lane's counts are equal on every
// execution by the chain-coupling argument. A FALSE postcondition (e.g.
// `ensures` that the lengths DIFFER over an equal-by-construction body)
// stays refutable: the pins constrain the terms to their genuine values.
/// A parsed `_0_value.<i>.<j>…_len` spec-model name: the exact var name the
/// parser mints plus the positional payload-component field path. Only paths
/// STRICTLY under the payload parse (`_0_value_len` — a bare-payload length —
/// stays fail-closed, matching the compiler lowering's strict-projection gate).
#[derive(Clone, Debug, PartialEq, Eq)]
struct LenModelVar {
    name: String,
    path: Vec<usize>,
}

// ======================================================================
// Ordering/sign-witness return grounding (b62 F4): `_0_value.__trust_ok_<i>`
// pair terms + the `_0_value_sign` term
// ======================================================================
//
// The F4 `matches!`-guard lowering emits `#[ensures]` predicates over the
// payload-pair terms the spec parser mints for `Ok((d, c))` tuple binds
// (`_0_value.__trust_ok_0/1`) and over the payload sign term it mints for
// `result.unwrap().is_positive()` (`_0_value_sign`) — the ny-cert selfcheck /
// branch shapes, whose payloads are `Rat`: a Copy u32 ARENA HANDLE whose
// ordering lives behind `<Rat as PartialOrd>` through a thread-local arena.
// An Int reading of the handle bits is MEANINGLESS, so this lane NEVER
// re-encodes the handle ints. Instead it grounds the contract atoms on the
// BOOL results of the body's OWN comparison calls — the same functions the
// runtime-checked `ensures` fallback would execute on the same values:
//
//  * WHICH terms (the coverage gates, `ordering_pair_coverage` /
//    `sign_var_covered`): a pair of `_0_value.__trust_ok_<i>` names is
//    covered only when EVERY occurrence of BOTH names across EVERY declared
//    postcondition sits inside an ordering atom `Lt/Le/Gt/Ge/Eq(a, b)`
//    BETWEEN the two names (no constants, no arithmetic); `_0_value_sign` is
//    covered only when its every occurrence sits in an ordering atom against
//    the LITERAL 0. Any other occurrence keeps the term UNCREDITED, so a
//    partially-constrained term can never turn today's honest Unknown into a
//    refutable VC minted over an under-constrained encoding (the P6
//    Unknown→FAILED hazard) — and no atom shape that could import Int
//    DISCRETENESS (`x > 0 ⟹ x >= 1` needs an `x >= 1`-shaped atom) is
//    admissible: with atoms restricted to orderings between the two pair
//    vars / one sign var vs 0, every consistent total-order outcome is
//    realizable over the Int sort, so Int-validity coincides with
//    total-order validity for the emitted VCs.
//
//  * WHAT is emitted (`ordering_witness_path_pins`): per RETURN PATH whose
//    `_0` resolves to the payload-variant in-body aggregate (the SAME
//    `resolve_enum_return_aggregate_with_block` walk the discr/len pins
//    use), ONE ordering fact over the model terms, derived from a DOMINATING
//    WITNESS GUARD (`dominating_ordering_witness_guard`): a `SwitchInt` on a
//    bool whose EVERY whole-local def (statement or call dest — one
//    unrecognized def fails the guard closed) is an allowlisted witness
//    call, reached through projection-free stable `Use` hops and
//    polarity-flipping `Not` hops:
//      - pair lane: `<{component ty} as std/core::cmp::PartialOrd>::{lt,le,
//        gt,ge}` whose two args resolve (ref-target / stable Use hops) to
//        the two components' candidate places (`component_candidate_places`
//        — every root `place_source_is_stable`, so no mutation can intervene
//        between the witness call and the return: the compared values ARE
//        the returned values);
//      - sign lane: the payload type's OWN inherent `is_positive` /
//        `is_negative` / `is_zero` on the payload's candidate places.
//    Each def's true-edge outcome set (subset of {Lt, Eq, Gt} — e.g.
//    `le` true ⇒ {Lt, Eq}; on the guard's false edge the COMPLEMENT, taken
//    PER DEF before the union so a mixed-def bool can only WEAKEN) is
//    unioned across defs; the edge that dominates the aggregate (structural
//    `reachable_avoiding` dominance — the other edge must not reach it,
//    mirroring `dominating_len_equality_guard`) contributes the joined set,
//    rendered as one atom (`OrderFacts::to_formula`: {Lt}→Lt … {Lt,Gt}→¬Eq;
//    the full set is uninformative and the EMPTY set would pin `false` — a
//    vacuous-UNSAT false-PROVE — both fail closed). Emitting at most ONE
//    fact per credited item keeps the pins mutually consistent by
//    construction.
//
//  * EVERY-RETURN-PATH discipline (`ordering_witness_credited_items`):
//    credited only when every Return path either constructs the EMPTY
//    variant in-body (the payload terms have no denotation there; leaving
//    them free is sound — a free var only adds refutability) or yields the
//    guard-derived fact. One unresolvable path fails the item closed,
//    exactly like the discr and len gates. The gate and the pin loop share
//    the per-path resolver, so a credited term can never reach a refutable
//    VC unpinned.
//
// SOUNDNESS (the pure-witness assumption, F5 `Vec::len`-purity class): the
// contract atoms denote the comparison FUNCTIONS the runtime-checked ensures
// fallback would execute (`PartialOrd` operators / the inherent sign
// predicates on the SAME values — operand-place identity + stability close
// the value channel). The lane assumes those functions are deterministic in
// their arguments within an execution and mutually coherent (`lt`/`le`/`gt`/
// `ge` derived from one `partial_cmp`; `a == b ⟹ partial_cmp == Equal` — the
// documented PartialOrd law backing the {Lt}∪{Gt} ⟹ ¬Eq join the branch
// direction-guard uses; sign trichotomy — the spec parser's OWN `{base}_sign`
// convention). For ny-cert's `Rat` these hold by the append-only interning
// arena (the `try_borrow`/`val` fail-safe arms are unreachable for the
// non-reentrant thread-local arena — same assumption class, documented
// there). All required inferences (Le⇒¬Gt, Lt/Gt⇒¬Eq, sign≤0⇒¬(sign>0)) are
// valid in EVERY total order — no Int-discreteness leak (see the coverage
// gate above). A FALSE postcondition stays refutable: the single pinned atom
// is TRUE of the actual returned values on that path, never credited.
/// A parsed `_0_value.__trust_ok_<i>` spec-model name: the tuple-bind payload
/// component var the compiler's `matches!(r, Ok((d, c)) if ..)` lowering
/// mints. Any other shape (a trailing `.field`, non-numeric index, other
/// bases) keeps today's fail-closed routing.
#[derive(Clone, Debug, PartialEq, Eq)]
struct OkPairModelVar {
    name: String,
    index: usize,
}

/// The set of total-order outcomes a witness edge admits for an ordered term
/// pair `(a, b)` (or for `(sign, 0)`): a subset of {Lt, Eq, Gt}.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OrderFacts {
    lt: bool,
    eq: bool,
    gt: bool,
}

impl OrderFacts {
    const LT: Self = Self { lt: true, eq: false, gt: false };
    const EQ: Self = Self { lt: false, eq: true, gt: false };
    const GT: Self = Self { lt: false, eq: false, gt: true };
    const LE: Self = Self { lt: true, eq: true, gt: false };
    const GE: Self = Self { lt: false, eq: true, gt: true };

    /// The other edge of the same witness: the outcome was NOT in `self`.
    fn complement(self) -> Self {
        Self { lt: !self.lt, eq: !self.eq, gt: !self.gt }
    }

    /// Join over multiple reaching defs: the outcome is admitted by SOME def,
    /// so the union is the only sound combination (an intersection would
    /// STRENGTHEN a fact beyond what the executed def establishes).
    fn union(self, other: Self) -> Self {
        Self { lt: self.lt || other.lt, eq: self.eq || other.eq, gt: self.gt || other.gt }
    }

    /// The same fact with the pair order swapped (`lt(b, a)` admits `(a, b)`
    /// Gt): mirror Lt and Gt, keep Eq.
    fn mirrored(self) -> Self {
        Self { lt: self.gt, eq: self.eq, gt: self.lt }
    }

    /// Neither FULL (no information — a `Bool(true)` pin) nor EMPTY (a
    /// `false` pin — the vacuous-UNSAT false-PROVE hazard).
    fn is_informative(self) -> bool {
        let count = usize::from(self.lt) + usize::from(self.eq) + usize::from(self.gt);
        count >= 1 && count <= 2
    }

    /// Render as ONE ordering atom over `lhs`/`rhs`. `None` for the FULL set
    /// (no information — a `Bool(true)` pin would credit nothing) and for the
    /// EMPTY set (pinning `false` would make the VC vacuously UNSAT — a
    /// false-PROVE; the empty set means the guard edge is contradictory,
    /// which must fail closed, never prove).
    fn to_formula(self, lhs: Formula, rhs: Formula) -> Option<Formula> {
        let (lhs, rhs) = (Box::new(lhs), Box::new(rhs));
        match (self.lt, self.eq, self.gt) {
            (true, false, false) => Some(Formula::Lt(lhs, rhs)),
            (false, true, false) => Some(Formula::Eq(lhs, rhs)),
            (false, false, true) => Some(Formula::Gt(lhs, rhs)),
            (true, true, false) => Some(Formula::Le(lhs, rhs)),
            (false, true, true) => Some(Formula::Ge(lhs, rhs)),
            (true, false, true) => Some(Formula::Not(Box::new(Formula::Eq(lhs, rhs)))),
            _ => None,
        }
    }
}

/// The witness TARGET a guard must establish facts about: the ordered
/// component pair, or the payload sign. Carries the component type name (the
/// callee allowlist key) and the stability-checked candidate places.
enum OrdWitnessTarget<'a> {
    Pair { ty_name: &'a str, cand_a: &'a [Place], cand_b: &'a [Place] },
    Sign { ty_name: &'a str, cands: &'a [Place] },
}

/// One whole-local def site: a statement rvalue or a call terminator.
enum F4LocalDef<'a> {
    Rv(&'a Rvalue),
    Call { callee: &'a str, args: &'a [Operand] },
}

/// One credited F4 item: a `__trust_ok` pair or the payload sign term.
#[derive(Clone, Debug, PartialEq, Eq)]
enum OrdWitnessItem {
    Pair(OkPairModelVar, OkPairModelVar),
    Sign(String),
}

impl OrdWitnessItem {
    fn model_names(&self) -> Vec<String> {
        match self {
            Self::Pair(a, b) => vec![a.name.clone(), b.name.clone()],
            Self::Sign(n) => vec![n.clone()],
        }
    }
}

// Every type, const, `impl`, textually-scoped macro and import the VC families
// share stays here: the families are descendant modules, so they keep access to
// private fields, private consts and this macro without any visibility change.
// Each family is re-exported flat, so `generate::<name>` resolves exactly as it
// did when this module was a single file.
mod call_facts;
mod ite;
mod int_conversion;
mod semantic_guard;
mod iterator_yield;
mod callee_summaries;
mod value_facts;
mod induction;
mod loop_bounds;
mod container_len;
mod entry;
mod unsupported;
mod unwrap_panic;
mod slice_conversion;
mod discharge;
mod callsite;
mod safety;
mod alloc_bounds;
mod panic_calls;
mod alloc_vcs;
mod type_ranges;
mod overflow_vc;
mod assert_refutation;
mod block_defs;
mod checked_vcs;
mod float_range;
mod float_overflow;
mod path_defs;
mod witness_grounding;
mod contract_vcs;

use call_facts::*;
use ite::*;
use int_conversion::*;
pub(crate) use semantic_guard::*;
use iterator_yield::*;
pub use callee_summaries::*;
pub(crate) use value_facts::*;
use induction::*;
use loop_bounds::*;
pub(crate) use container_len::*;
pub use entry::*;
pub(crate) use unsupported::*;
pub(crate) use unwrap_panic::*;
use slice_conversion::*;
pub use discharge::*;
pub use callsite::*;
pub use safety::*;
pub(crate) use alloc_bounds::*;
pub(crate) use panic_calls::*;
pub(crate) use alloc_vcs::*;
pub(crate) use type_ranges::*;
pub(crate) use overflow_vc::*;
pub use assert_refutation::*;
pub(crate) use block_defs::*;
pub(crate) use checked_vcs::*;
pub use float_range::*;
use float_overflow::*;
pub(crate) use path_defs::*;
use witness_grounding::*;
use contract_vcs::*;

#[cfg(test)]
mod clamp_upper_bound_tests;
#[cfg(test)]
mod recursion_decreases_production_variant_tests;
#[cfg(test)]
mod call_arg_fact_token_tests;
#[cfg(test)]
mod summary_callsite_tests;
#[cfg(test)]
mod v2_path_guard_tests;
#[cfg(test)]
mod contract_field_bound_tests;
#[cfg(test)]
mod float_range_tests;
#[cfg(test)]
mod bounds_const_suppression_tests;
#[cfg(test)]
mod round14_stability_tests;
#[cfg(test)]
mod return_projection_pin_tests;
#[cfg(test)]
mod return_pin_dedup_tests;
// PtrMetadata over a slice/str/array fat pointer is its length, which
// `slice_len_formula` models deterministically — so `collect_rvalue_unsupported`
// must NOT emit a spurious `Rvalue::UnaryOp(PtrMetadata)` UnsupportedMir
// obligation for those operands (that wedged the ubiquitous
// `if i < s.len() { s[i] }` idiom). For genuinely unmodelable metadata
// (raw-pointer provenance, `dyn` vtable) it must still fail closed. These tests
// pin both halves of that contract on the exact function the fix lives in. Plain
// `#[cfg(test)]` because `unsupported_mir_vcs` is part of the canonical pipeline.
#[cfg(test)]
mod result_return_grounding_tests;
#[cfg(test)]
mod machine_faithful_contract_lane_tests;
#[cfg(test)]
mod len_witness_grounding_tests;
#[cfg(test)]
mod ordering_witness_grounding_tests;
#[cfg(test)]
mod ptr_metadata_tests;
// a `SwitchInt` join followed by a guard
// (`let m = if a < b { a } else { b }; if m < 1000 { m + 1 }`) used to false-FAIL
// the guarded overflow VC: the path-definition BFS weakened the join to `true`,
// so the dominating fact `c == (m < 1000)` was dropped from the guarded successor
// block and the guard `c == true` could no longer constrain `m`. These tests pin
// the dataflow contract directly on `v2_build_path_definition_map`:
//   (a) the comparison `c == (m < 1000)` established at the join SURVIVES into the
//       guarded successor (intersection of all incoming paths);
//   (b) the path-specific BARE copies `m == a` / `m == b` are NOT asserted
//       unconditionally downstream (soundness — they hold on only one arm); the
// UNCONDITIONAL merged `m == Ite(..)` MAY propagate, since it is
//       true on every path through the dominating join — only a bare non-Ite def of
//       `m` would be a stale-leak soundness hole;
//   (c) the #18 branch-merge invariant `m == Ite(..)` is still attached to the
//       JOIN block's own hypotheses (no regression of the merged-local recovery).
#[cfg(test)]
mod path_definition_map_tests;
#[cfg(test)]
mod capture_avoiding_tests;
#[cfg(test)]
mod ord_method_tests;
// ======================================================================
// Integer try_from/try_into + unwrap_or result modeling (tests)
// ======================================================================
#[cfg(test)]
mod int_wrapping_neg_tests;
// ======================================================================
// Const-return summaries: lower/upper bound + exact const set (tests)
// ======================================================================
#[cfg(test)]
mod return_const_summary_tests;
#[cfg(test)]
mod trivial_setter_summary_tests;
#[cfg(test)]
mod int_try_from_unwrap_or_tests;
#[cfg(test)]
mod unbounded_alloc_tests;
// Trust: arithmetic hidden INSIDE a library/intrinsic Call (`i32::pow`,
// `unchecked_{add,sub,mul}`) lowers to a `Terminator::Call`, never a
// caller-visible `Rvalue::BinaryOp`/`Assert(Overflow)`, so the BinaryOp/Assert
// overflow arms never see it and the op was reported vacuously safe. These
// tests pin the recognizer added to `generate_v2_safety_vcs` (block 1c): an
// unguarded overflowing call FIRES an ArithmeticOverflow obligation; a safe /
// guarded variant produces NONE (or an obligation the conjoined precondition
// discharges). Mirrors the `unbounded_alloc_tests` MIR-by-hand style.
#[cfg(test)]
mod overflow_call_tests;
// Division/remainder-by-zero hidden inside a library Call (block `1d` of
// `generate_v2_safety_vcs`). `a.checked_div(b)` / `checked_rem` / `div_euclid` /
// `rem_euclid` and `Iterator::step_by(n)` lower to a `Terminator::Call`, never a
// caller-visible `Rvalue::BinaryOp(Div|Rem)`, so the div/rem arms never saw them
// and an unguarded zero divisor was reported vacuously safe — a false PROVE.
// These tests pin the recognizer: an unguarded dynamic divisor FIRES a
// `DivisionByZero` / `RemainderByZero` obligation; a const-nonzero / guarded /
// float / ordinary-call variant produces NONE (or an obligation the conjoined
// `b != 0` guard discharges). Mirrors the `overflow_call_tests` MIR-by-hand style.
#[cfg(test)]
mod divzero_call_tests;
// Unit tests for the slice-method panic recognizer (block 1e of
// `generate_v2_safety_vcs`). `s.split_at(mid)` (panic `mid > len`), the zero-size
// `s.chunks(n)`/`windows(n)`/`chunks_exact(n)` forms (panic `n == 0`), and
// `s.swap(i, j)` (panic `i >= len || j >= len`) lower to a `Terminator::Call` that
// carries NO caller-visible `Projection::Index`, so the rvalue-safety bounds path
// never saw them and an out-of-range argument was reported vacuously safe — a
// false PROVE. These tests pin the recognizer: an unguarded bad argument FIRES the
// SliceBoundsCheck / DivisionByZero obligation; a const-safe / guarded / unrelated
// call produces NONE (or an obligation the conjoined guard discharges). Mirrors the
// `divzero_call_tests` MIR-by-hand style.
#[cfg(test)]
mod slice_method_panic_tests;
// Unit tests for the STRUCT-FIELD Vec length-identity key (place-keyed coll_len,
// 2026-07-08). A length guard on `self.history` and an index into `self.history`
// each reach the container through a FRESH reborrow temp (`_t = &((*self).history)`),
// so the pre-fix LOCAL-keyed identity minted two disconnected per-temp vars and the
// guard could never discharge the bound — `if self.history.is_empty() { return }
// … self.history[self.history.len() - 1]` FALSE-REFUTED despite being safe. The
// place key (`base_collection_place_unique` → `coll_len(self*.0)`) unifies the
// guard side (`owned_container_len_var`), the index-bound side
// (`collection_abstract_len_with_base_opts`), and the `.len()` tie
// (`slice_last_some_nonempty_definitions`). The negatives pin the FAIL-CLOSED
// constructions: a guard on the WRONG FIELD mints a DIFFERENT var (fields are
// distinct because the key is the full projected place), and a `&mut self` root
// declines the field key entirely (per-temp vars that never unify).
#[cfg(test)]
mod field_vec_len_key_tests;
#[cfg(test)]
mod push_guard_elem_len_tests;
/// Cast VC model: value-preserving WIDENING casts into a 128-bit target.
///
/// Covers the `u32 as u128` (and friends) widening that previously returned
/// UNKNOWN ("target integer range is not representable by the cast VC model"),
/// plus the adversarial guarantee that the widening fact never vacuously proves
/// a genuinely-overflowing 128-bit arithmetic safe.
#[cfg(test)]
mod widening_cast_128_tests;
/// REM-bounded BV multiply: `(a % 100) * (b % 50)` is provably in-range
/// (product <= 99*49 = 4851 << u32::MAX), yet the BV mul lane's fresh operand
/// vars carried NO mod bound — the solver fabricated an internally inconsistent
/// counterexample (`a = 0, b = 0` next to `bv_lhs = u32::MAX`) and FALSE-REFUTED
/// provably-safe code. `v2_bv_rem_constraints` renders `r < C` onto the fresh
/// BV vars; these tests pin the constraint presence and the refutability floor.
#[cfg(test)]
mod bv_rem_mul_tests;
/// 128-bit signed CheckedBinaryOp (add/sub) overflow and i128 negation overflow.
///
/// Pre-fix: the Int-path overflow builder fail-closed `signed && width >= 128` to
/// UNKNOWN on the (false) premise that `i128::MAX` is the solver's integer ceiling.
/// In fact the `Sort::Int` theory is unbounded BigInt (ay lowers `Formula::Int`/`UInt`
/// via `Expr::int_const(impl Into<BigInt>)`), so `result < i128::MIN ∨ result > i128::MAX`
/// is SAT exactly when a real i128 add/sub overflows. The guard is now narrowed to MUL
/// only (nonlinear / NIA), keeping signed-128 mul fail-closed.
///
/// Each test also includes its ADVERSARIAL guardrail: a genuinely-overflowing i128
/// witness must SATISFY the violation formula (so the solver can still refute it),
/// while a safe in-range input must NOT — the new model is the exact overflow
/// predicate, never weaker (no false-PROVE).
#[cfg(test)]
mod signed_128_overflow_tests;
#[cfg(test)]
mod widening_mul_tests;
// SOUNDNESS (hunt-15 Class B): `postcondition_references_mutated_param` must flag a
// param mutated through a `&mut`/`&raw mut` borrow (not just a whole-local reassign),
// so a bare `#[ensures(move |r| *r == a)]` over `let p=&mut a; *p=..; a` fail-closes
// instead of vacuously proving against the entry snapshot.
#[cfg(test)]
mod postcondition_mutated_param_tests;
// Trust (task #77): `v2_bv_guard_constraint` now renders a dominating range guard as a
// BV bound up to width 128 (was width<=64), so guarded signed-128 add/sub can prove.
#[cfg(test)]
mod bv_guard_constraint_width128_tests;
// Trust (hunt-15 Class D): `is_known_panicking_method` recognizes Option/Result
// unwrap/expect (which surface as Unknown so the default headline stays honest),
// and ONLY those — not the total `unwrap_or*` nor unrelated methods.
#[cfg(test)]
mod known_panicking_method_tests;
// ── verifier-perf: mid-generation VC-WORK budget tests ──────────────────────
//
// These exercise the thread-local generation work meter (`crate::gen_work`) and the
// wholesale fail-closed degrade. Tests install an explicit thread-local budget,
// so proof behavior never depends on process-global environment state.
#[cfg(test)]
mod gen_work_budget_tests;
// Trust: piece #7a — folds + freshen-list soundness for the const-generic
// `ConstValue::ConstParam` value.
#[cfg(test)]
mod const_param_fold_tests;
// Trust (unwrap panic-freedom, dominated-safe): the two recognized pinning
// shapes — guard-pinned (`if r.is_ok() { r.unwrap() }` / a match-arm dominating
// discriminant switch) and construction-pinned (`let x = Ok(v); … x.unwrap()`)
// — replace the fail-closed `Call::unwrap::panic-freedom-unverified`
// UnsupportedMir row with a SOLVABLE refutation VC; everything outside the
// shape keeps the row (fail-closed, never silently dropped).
#[cfg(test)]
mod unwrap_panic_freedom_tests;
// Trust (return-discriminant summary): the callee-summary recognizer
// (`function_return_disc_summary` — UNCONDITIONAL / GUARD-CONDITIONED, both
// fail-closed) and its use site — the unwrap panic-freedom lane's
// SUMMARY-pinned call-result receiver (`let r = Rat::new(n, d); r.unwrap()`).
#[cfg(test)]
mod return_disc_summary_tests;
#[cfg(test)]
mod ite_elimination_tests;
// Trust (countdown-loop piece): the division-countdown trip theorem — the
// exactly-tight T/K tables (an off-by-one DOWN in T is a false proof; the u64
// quad loop runs EXACTLY 5 times, consuming a 20-byte buffer to offset 0) and
// the builder's soundness gates, each pinned on REAL MIR extracted with
// `-Ztrust-dump=mir:<dir>` from the trap shape it kills.
#[cfg(test)]
mod countdown_trip_tests;
#[cfg(test)]
mod immutable_read_value_tie_tests;
#[cfg(test)]
mod const_param_range_tests;
#[cfg(test)]
mod vec_index_dest_value_tie_tests;
#[cfg(test)]
mod per_arg_havoc_refinement_tests;
// ======================================================================
// Float bit-reinterpretation call models: `f64::to_bits`/`from_bits` and the
// f32 siblings. Task #66 (completeness half): restore the correlation between a
// `let bits = v.to_bits()` integer local and the float's IEEE bitvector so the
// `f64_next_up_compat` shape (`bits - 1` guarded by `v != 0.0`) becomes PROVABLE
// instead of falsely refuted. See `float_bits_call_dest_fact`.
// ======================================================================
#[cfg(test)]
mod float_bits_call_model_tests;
