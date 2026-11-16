// trust_vcgen/generate.rs: Core verification condition generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, AssertMessage, BinOp, BlockId, ConstValue, ContractKind, ContractMetadata,
    Formula, GuardCondition, ObligationRecord, ObligationWrapper, Operand, PathGuardTerm, Place,
    Projection, Rvalue, Sort, SourceSpan, Statement, Symbol, Terminator, Ty, VcKind,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

use crate::{
    abstract_interp, contracts, ffi_summary, ffi_vcgen, guards, hardened, memory_ordering,
    operand_to_formula, place_to_var_name, rvalue_safety, sep_engine, spec_parser, termination,
    unsafe_verify,
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
/// block-def (one per aggregate field) at establish points — a block pays for its
/// own density — and so a function's cost is the sum of its blocks' local products.
///
/// RE-JUSTIFIED 2026-09-28 (WS-E, the SSA statement-version oracle). The cost model
/// above used to rest on the version oracle's per-query cost being "bounded by the
/// statements and aggregate operands OF THE QUERIED BLOCK" (the retired
/// `writes_until` prefix extraction). That query is now O(log), so the oracle is not
/// what these three caps bound any more. What still is super-linear is the BFS
/// itself: every block STORES, and re-versions, the whole guard list accumulated
/// along its first path — Θ(blocks × path depth) facts. Measured with deterministic
/// counts (`version_ssa_scaling_tests::measure_semantic_guard_map`, the caps not
/// reached): `locals_chain` stores 14,840 / 59,120 / 236,000 / 943,040 facts at
/// 114 / 226 / 450 / 898 blocks (4x per doubling), and the back-edge ladder makes
/// 241 / 993 / 4,033 / 16,257 version queries at 16 / 32 / 64 / 128 blocks. The caps
/// therefore stay until the threaded facts are hash-consed persistent sets (WS-E
/// step 6), and are to be deleted in that commit, with the measurement showing it.
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
#[derive(Clone, Copy)]
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
///
/// Trust (2026-10-08, review of ALLOC-BYTE-1): this is a VALUE threshold, and
/// it is still one. It is a disjunct of every counted allocation row, including
/// the rows whose capacity term is already the exact panic line, so for a 1-byte
/// element it is a 256 MiB byte line by another name, and it decides the verdict
/// of a constant count past it (`Vec::<u64>::with_capacity(300_000_000)` is
/// reported; `Box::<[u64; 1 << 37]>::new` is not). It is kept, and recorded as
/// OPEN policy debt (docs/OPEN_ISSUES.md D102). A counted allocation whose
/// element size is unknown now keeps a visible Unknown, apart from a literal
/// zero request; this count threshold cannot establish byte capacity for a
/// generic `T` or an unsized destination. Known layouts retain their separate
/// capacity term. Removing this availability threshold is a distinct change.
const UNBOUNDED_ALLOC_ELEM_CEILING: i128 = 1 << 28;

// There is NO per-allocation BYTE budget for an element of more than one byte:
// the 256 MiB `UNBOUNDED_ALLOC_BYTE_CEILING` that stood here — a copy of
// trust-ir's `alloc_bound::ALLOC_BYTE_BUDGET`, failing a symbolic multi-byte
// allocation whose `stride * count` might reach 256 MiB and a single value of
// 256 MiB or more — was deleted 2026-10-08 (ALLOC-BYTE-1, after trust-ir's
// dda53e12; the owner, 2026-09-29: "delete the 256 MiB number; the lint
// reports only allocations whose size is not provably bounded"; docs/OWNER_RULINGS.md OW-29). It was deleted
// together with the two fixes that make it unnecessary, because it had been
// guarding two real panics nothing else charged:
//
//   * the TARGET'S object limit. The byte line is now `isize::MAX` at the
//     compilation target's pointer width (`alloc_bounds::AllocTarget`, from the
//     compiler-supplied `VcgenContext::with_target_pointer_bits`), not the 64-bit
//     value: on a 32-bit target `Vec::<[u8; 65536]>::with_capacity(n as usize)`
//     over a `u16` panics from `n = 32768`, and only the 256 MiB atom refused it;
//   * a LIVE receiver. `reserve` / `reserve_exact` / `extend_reserve`, a counted
//     `extend` and a counted `collect_into` add their count to what the receiver
//     already holds (RawVec asks for `(len + additional) * stride`). Their rows
//     now charge the receiver too (`AllocTarget::live_receiver_items`): one live
//     element of `MaybeUninit<[u8; 1 << 35]>` plus `reserve(n)` with
//     `n < 2^28` panics "capacity overflow", and only the 256 MiB atom refused it.

/// `isize::MAX` in bytes on a 64-bit target — the 64-bit arm of
/// `alloc_bounds::AllocTarget`'s object limit, and nothing else. A `Vec` /
/// `RawVec` allocation whose `count * size_of::<T>()` REACHES the target's
/// `isize::MAX` panics with "capacity overflow" at runtime (RawVec hard-caps every
/// allocation at `isize::MAX` bytes) — a real, credited memory-safety panic. The
/// `UNBOUNDED_ALLOC_ELEM_CEILING` (count-only) obligation does NOT catch it: a
/// MULTI-BYTE element makes `count * stride` overflow `isize::MAX` while `count`
/// itself stays far below `2^28` (e.g. `Vec::<[u8; 1<<40]>::with_capacity(n)` with
/// `n < 2^27`). It is NOT the line on a narrower target: a LARGER failure
/// threshold flags FEWER allocations, so judging a 32-bit target at this value
/// would prove allocations that panic there (the pre-2026-10-08 comment here said
/// the opposite, and was wrong).
const ALLOC_CAPACITY_OVERFLOW_BYTES: i128 = (1 << 63) - 1;

/// The kind of overflowing arithmetic hidden inside a recognized `Terminator::Call`.
#[derive(Clone, Copy)]
enum OverflowCall {
    /// `base.pow(exp)` on core's primitive integers — exponentiation, modeled
    /// exactly (`v2_overflow_call_body`); minted only for the authenticated
    /// `core::num::<impl iN/uN>::pow` (`alloc_bounds::overflow_arith_call`).
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
    /// Trust (2026-09-25, F5): `BTreeMap::range(r)` / `BTreeSet::range(r)` PANICS
    /// when `r`'s start is greater than its end (or both are equal and
    /// excluded). The range is arg 1. See `panic_calls::btree_range_panic_body`.
    BTreeRange { range_idx: usize },
    /// Trust (2026-09-25, std-range-family): a std collection method that checks a
    /// caller `RangeBounds<usize>` with `slice::range(r, ..len)` — `Vec::splice`,
    /// `Vec::extract_if`, `VecDeque::range`/`range_mut`, `String::drain`/
    /// `replace_range`/`extend_from_within`. The range is arg `range_idx`. See
    /// `collection_range::collection_range_panic_body`.
    ///
    /// `range_is_full` records that the method's range type parameter is
    /// `RangeFull` — `..` reaches MIR as a typeless zero-sized constant.
    CollectionRange {
        range_idx: usize,
        owner: collection_range::RangeMethodOwner,
        range_is_full: bool,
    },
    /// Trust (2026-09-25, std-range-family): `Vec::insert_mut(i, x)` /
    /// `VecDeque::insert_mut(i, x)` (panic `i > len`) — a RESIZING method, so no
    /// stable length can discharge its index: fail-honest, like
    /// [`SliceMethodPanic::VecPanicMethod`].
    ResizingIndexArg { idx: usize },
    /// Trust (2026-09-25, std-range-family): `String::split_off(at)` (panic
    /// `at > len` or `at` not a char boundary) and `String::truncate(n)` (panic
    /// `n <= len` and `n` not a char boundary). Char boundaries are not modeled.
    CharBoundaryArg { idx: usize, truncate: bool },
    /// Trust (2026-09-25, std-range-family): `<[T]>::repeat(n)` — "capacity
    /// overflow" when `len * n` overflows, computed inside the library. The
    /// sibling of `str::repeat`'s `str-repeat-capacity-overflow` row.
    SliceRepeat { n_idx: usize },
    /// Trust (2026-09-25, std-range-family): `VecDeque::swap(i, j)` — panics when
    /// `i >= len || j >= len`, over the deque's length (the slice
    /// [`SliceMethodPanic::SwapIndices`] body finds no slice length on a deque
    /// receiver and emitted nothing).
    DequeSwap { i_idx: usize, j_idx: usize },
    /// Trust (2026-09-25, std-range-family): `<[T]>::as_chunks::<N>` /
    /// `as_chunks_mut` / `as_rchunks` / `as_rchunks_mut` / `array_windows::<N>` —
    /// `assert!(N != 0)`. `nonzero` records that the instantiation renders a
    /// nonzero integer literal; anything else (`0`, a generic `N`) is charged.
    ConstChunkSize { nonzero: bool },
    /// Trust (2026-09-25, std-range-family): `Vec<[T; N]>::into_flattened` —
    /// "vec len overflow" when `T` is zero-sized and `len * N` overflows.
    VecIntoFlattened,
}

enum LocalDef<'a> {
    Rvalue(&'a Rvalue),
    Call { callee: &'a str, args: &'a [Operand] },
}

/// Linear comparison shapes recognized by the BV guard translation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
/// is depth 3); a deeper aggregate simply stops contributing overrides. A
/// bound on TYPE nesting (program text), not on any array length: a leaf is
/// resolved from the one chain a read names (`float_leaf_chain`).
const FLOAT_STRUCT_LEAF_DEPTH: u32 = 6;

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

/// The F6b trace memo key: (call block, callee, `Debug` of the args, `Debug` of
/// the suffix), all in ONE context's function-local names (see
/// `FloatRangeCtx::trace_memo`).
type TraceMemoKey = (BlockId, String, String, String);

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
    /// canonicalization — e.g. `"self.0"`, `"m.0[0].1"`) and resolved when a
    /// leaf is read (`FieldOverrideSource`). A scalar `param_override` cannot
    /// bound `Vec3::add`'s `self.0` when the caller passed a whole `Vec3`; this
    /// source carries the callsite-specific interval of the ACTUAL's
    /// corresponding field (`self_min.0`), letting a matrix/vector CHAIN
    /// (`center = min.add(max).scale(0.5)` — every a3d residual) discharge
    /// against the callee's own contract requirement. Same ENTRY-fact
    /// discipline as `param_overrides`: a formal the body writes or lends
    /// write-capably (any field) gets no leaf override — the binder in
    /// `float_callee_trace_range` binds none and `param_field_override`
    /// refuses one (F6B-FIELD-OVERRIDE-UNSTABLE-1). `None` off the
    /// callee-trace.
    param_field_source: Option<&'a FieldOverrideSource<'a>>,
    /// The SHARED per-function path-guard map (`guard_map_for`), held by `Rc` so
    /// a ctx built per float binop borrows it instead of rebuilding it.
    guard_map: std::cell::OnceCell<std::rc::Rc<PathGuardMap>>,
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
    /// F6b trace memo — SUCCESSFUL callee-trace results of THIS context only.
    /// The same (call block, callee, args, suffix) query recurs massively in
    /// wide callers (`mul_mat4`: 16 dot callsites × 16 precondition
    /// conjuncts each re-tracing the same four `row(..)` results), and the
    /// un-memoized recomputation exhausted the shared work budget mid-
    /// function — later callsites then refused NOT for any semantic reason
    /// but because the meter died (a completeness cliff).
    ///
    /// The key is spelled in this context's own function-local names (a block
    /// id, the `Debug` of operands naming its locals) and names none of the
    /// facts the context traces under, so an entry is exact only inside the
    /// context that made it, where `func`, `param_overrides` and
    /// `param_field_source` are fixed. Every context — the root and each
    /// `for_callee` one — therefore starts with its OWN empty memo
    /// (F6B-TRACE-MEMO-KEY-1, 2026-10-06: one memo `Rc`-shared from the root
    /// into every nested context let `outer(y)`, `y` unbounded, read the
    /// `[2, 2]` an earlier `outer(x)` trace had cached for the identical key
    /// of `outer`'s own `inner(copy _1)`; a caller's root-level
    /// `inner(copy _1)` at `bb0` collided the same way). A hit returns before
    /// the depth/cycle cut and the precondition re-establishment of
    /// `float_callee_trace_range`, which is sound only because the entry was
    /// made under the same context facts. ONLY `Some` results are cached: what
    /// still varies within one context (the `visiting` set, fuel, the shared
    /// callee stack and work budget) can only turn a trace into a refusal, and
    /// a refusal is NEVER cached (fail-closed recomputation).
    trace_memo: std::cell::RefCell<FxHashMap<TraceMemoKey, (f64, f64)>>,
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
            param_field_source: None,
            guard_map: std::cell::OnceCell::new(),
            guard_facts: std::cell::RefCell::new(FxHashMap::default()),
            alias_names: std::cell::RefCell::new(FxHashMap::default()),
            work: std::rc::Rc::new(std::cell::Cell::new(FLOAT_RANGE_WORK)),
            trace_memo: std::cell::RefCell::new(FxHashMap::default()),
            visiting_callees: std::rc::Rc::new(std::cell::RefCell::new(Vec::new())),
        }
    }

    /// F6b: a context for tracing INSIDE a callee's extracted body, carrying
    /// the caller-derived formal overrides and SHARING the caller context's
    /// work budget and callee-visiting stack. The guard/alias caches are
    /// per-function and the trace memo is per-context; all start fresh.
    fn for_callee(
        parent: &FloatRangeCtx<'a>,
        func: &'a VerifiableFunction,
        param_overrides: FxHashMap<usize, (f64, f64)>,
        param_field_source: Option<&'a FieldOverrideSource<'a>>,
    ) -> Self {
        Self {
            func,
            summaries: parent.summaries,
            param_overrides,
            param_field_source,
            guard_map: std::cell::OnceCell::new(),
            guard_facts: std::cell::RefCell::new(FxHashMap::default()),
            alias_names: std::cell::RefCell::new(FxHashMap::default()),
            work: std::rc::Rc::clone(&parent.work),
            visiting_callees: std::rc::Rc::clone(&parent.visiting_callees),
            // NEVER the parent's memo: its keys name the parent's blocks and
            // locals, under the parent's facts (F6B-TRACE-MEMO-KEY-1).
            trace_memo: std::cell::RefCell::new(FxHashMap::default()),
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
    ///
    /// The interval is the caller's value of the actual, an ENTRY fact, so it is
    /// returned only under `contract_range`'s license: the formal is never
    /// written or lent write-capably anywhere in the body
    /// (`param_place_is_entry_stable`) and the read does not go through a raw
    /// pointer (`place_reads_through_raw_ptr`). The binder in
    /// `float_callee_trace_range` already binds no actual for such a formal;
    /// this repeats the gate at the one lookup every reader goes through
    /// (F6B-FIELD-OVERRIDE-UNSTABLE-1, 2026-10-06: `fn bump(mut p: P) -> f64
    /// { p.a = 1e300; p.a }` was traced as returning the caller's `p.a`).
    fn param_field_override(&self, place: &Place) -> Option<(f64, f64)> {
        if place.local < 1 || place.local > self.func.body.arg_count {
            return None;
        }
        let source = self.param_field_source?;
        if !source.has_actual(place.local)
            || !param_place_is_entry_stable(self.func, place.local)
            || place_reads_through_raw_ptr(self.func, place)
        {
            return None;
        }
        let name =
            float_range::canonicalize_contract_index_segments_owned(crate::place_to_var_name(self.func, place));
        let (lo, hi) = source.resolve(self.func, place, name)?;
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
        let func_addr = std::ptr::from_ref(self.func) as usize;
        let scope_id = callee_write_set::current_scope_id();
        if !crate::fn_memo::is_disabled() && !trust_types::verify_budget::exhausted_readonly() {
            let shared_hit = FUNC_ANALYSIS_MEMO.with(|memo| {
                memo.borrow()
                    .iter()
                    .rev()
                    .find(|frame| frame.func_addr == func_addr)
                    .and_then(|frame| frame.float_guard_facts.get(&(block_id, scope_id)).cloned())
            });
            if let Some(facts) = shared_hit {
                self.guard_facts.borrow_mut().insert(block_id, std::rc::Rc::clone(&facts));
                return facts;
            }
        }
        // The SHARED per-function memo, not a ctx-local build. `FloatRangeCtx` is
        // constructed fresh PER FLOAT BINOP (`v2_float_binop_cannot_overflow_at`),
        // so a ctx-local `OnceCell` rebuilt the whole path-guard map once per
        // arithmetic statement — the walk that reached a 137.8 GB peak footprint
        // on tla-cli (2026-09-10). `guard_map_for` calls the same builder and
        // returns the same value; it just does it once per function.
        let map = self.guard_map.get_or_init(|| guard_map_for(self.func));
        let facts: Vec<Formula> = match map.get(&block_id) {
            None => Vec::new(),
            Some(paths) if paths.is_empty() || paths.iter().any(Vec::is_empty) => Vec::new(),
            Some(paths) => {
                // BUDGET POLL, per GUARD (not per path): a block carries up to
                // `MAX_PATHS_PER_BLOCK` = 64 enumerated paths and each guard on
                // one costs a `guards::guard_to_formula` resolution, which walks
                // the defining block looking for the comparison's latest
                // definition — so resolution alone is 64 x |path| whole-block
                // scans with nothing bounding it in TIME. Written as explicit
                // loops because a poll inside the `.map()` closures cannot
                // return from this function (the `entry_version_gen_sets`
                // lesson in `path_defs.rs`).
                //
                // The degradation is the empty fact vector — byte-identical to
                // what this function already returns for a block absent from the
                // map, and to what per-block saturation and cap-overflow already
                // hand back as "one unguarded path". `float_guard_bounds` reads
                // an empty set as NO dominating bound and returns `(None, None)`,
                // so the interval lane is left wider: dropping guard hypotheses
                // turns a PROVE into a FAIL, never a FAIL into a PROVE. The
                // degraded vector is deliberately NOT written to `guard_facts`
                // — a budget refusal is budget-state dependent, so it is
                // recomputed (and immediately re-refused, the counter having
                // stuck at zero) rather than cached, the same discipline
                // `trace_memo` states for a refused callee trace.
                let mut resolved: Vec<Vec<Formula>> = Vec::with_capacity(paths.len());
                let mut edge_cache: FxHashMap<(BlockId, u8, u128), (&GuardCondition, Formula)> =
                    FxHashMap::default();
                let use_edge_cache = paths.len() > 1;
                for gs in paths {
                    let mut path: Vec<Formula> = Vec::with_capacity(gs.len());
                    for (src, g) in gs {
                        if trust_types::verify_budget::budget_exhausted() {
                            return std::rc::Rc::new(Vec::new());
                        }
                        let edge_key =
                            use_edge_cache.then(|| safety::guard_cache_key(*src, g)).flatten();
                        if let Some(key) = edge_key
                            && let Some((cached_g, cached_f)) = edge_cache.get(&key)
                            && safety::guard_condition_eq(cached_g, g)
                        {
                            path.push(cached_f.clone());
                            continue;
                        }
                        let f = guards::guard_to_formula(self.func, g);
                        if let Some(key) = edge_key {
                            edge_cache.entry(key).or_insert_with(|| (g, f.clone()));
                        }
                        path.push(f);
                    }
                    resolved.push(path);
                }
                let mut iter = resolved.into_iter();
                match iter.next() {
                    None => Vec::new(),
                    Some(first) if iter.as_slice().is_empty() => first,
                    Some(first) => {
                        let rest = iter.as_slice();
                        // BUDGET POLL, per (candidate fact, remaining path)
                        // pair: `contains` is a DEEP structural `Formula`
                        // compare, so this intersection is up to 63 x |first|
                        // whole-tree comparisons and a poll at the path level
                        // above cannot interrupt one pass of it. Short-circuits
                        // exactly where `rest.iter().all(..)` did, so the
                        // surviving set is unchanged on the non-exhausted path.
                        let mut kept: Vec<Formula> = Vec::new();
                        for fact in first {
                            let mut on_every_path = true;
                            for path in rest {
                                if trust_types::verify_budget::budget_exhausted() {
                                    return std::rc::Rc::new(Vec::new());
                                }
                                if !path.contains(&fact) {
                                    on_every_path = false;
                                    break;
                                }
                            }
                            if on_every_path {
                                kept.push(fact);
                            }
                        }
                        kept
                    }
                }
            }
        };
        let facts = std::rc::Rc::new(facts);
        self.guard_facts.borrow_mut().insert(block_id, std::rc::Rc::clone(&facts));
        if !crate::fn_memo::is_disabled() && !trust_types::verify_budget::exhausted_readonly() {
            FUNC_ANALYSIS_MEMO.with(|memo| {
                if let Some(frame) = memo
                    .borrow_mut()
                    .iter_mut()
                    .rev()
                    .find(|frame| frame.func_addr == func_addr)
                {
                    frame.float_guard_facts.insert((block_id, scope_id), std::rc::Rc::clone(&facts));
                }
            });
        }
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
        let func_addr = std::ptr::from_ref(self.func) as usize;
        if !crate::fn_memo::is_disabled() && !trust_types::verify_budget::exhausted_readonly() {
            let shared_hit = FUNC_ANALYSIS_MEMO.with(|memo| {
                memo.borrow()
                    .iter()
                    .rev()
                    .find(|frame| frame.func_addr == func_addr)
                    .and_then(|frame| frame.float_alias_names.get(&place.local).cloned())
            });
            if let Some(names) = shared_hit {
                self.alias_names.borrow_mut().insert(place.local, std::rc::Rc::clone(&names));
                return names;
            }
        }
        let mut names = vec![crate::place_to_var_name(self.func, place)];
        for decl in &self.func.body.locals {
            // BUDGET POLL, per LOCAL: `float_whole_local_defs` below is a
            // whole-BODY walk (every block, every statement, plus each
            // terminator) run once per declared local, so this loop is
            // O(locals x body) with nothing bounding it in time — the same
            // shape as the `entry_version_gen_sets` per-block poll over
            // `block_written_names`.
            //
            // The degradation is the alias list accumulated SO FAR. It is
            // seeded with the place's own name before the loop, so an early
            // return is always a non-empty but strictly SMALLER alias set, and
            // `float_guard_bounds` uses this list only to decide which
            // dominating facts are ABOUT this place — a name it does not
            // contain makes the fact be skipped. Fewer aliases therefore mean
            // fewer guard bounds and a wider interval: PROVE turns into FAIL,
            // never FAIL into PROVE. A partial list is not memoized, for the
            // reason `dominating_facts` gives above.
            if trust_types::verify_budget::budget_exhausted() {
                return std::rc::Rc::new(names);
            }
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
        if !crate::fn_memo::is_disabled() && !trust_types::verify_budget::exhausted_readonly() {
            FUNC_ANALYSIS_MEMO.with(|memo| {
                if let Some(frame) = memo
                    .borrow_mut()
                    .iter_mut()
                    .rev()
                    .find(|frame| frame.func_addr == func_addr)
                {
                    frame.float_alias_names.insert(place.local, std::rc::Rc::clone(&names));
                }
            });
        }
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

/// `2^exp` as an exact `f64`, for the width-parametric thresholds below.
const fn pow2_f64(exp: i32) -> f64 {
    f64::from_bits(((exp + 1023) as u64) << 52)
}

/// The discharge margin for an operation of this IEEE width, expressed in `f64`
/// because the interval tracer reasons at `f64` and every binary32 value is a
/// binary64 value exactly.
///
/// The f64 figure above is `2^1020`, an 8x headroom under `f64::MAX ~ 2^1024`.
/// The SAME derivation at binary32 gives `2^125` under `f32::MAX ~ 2^128`.
/// Using the f64 figure for a binary32 operation is the FALSE PROOF this exists
/// to prevent: `2^1020` is astronomically above `f32::MAX`, so an f32 result
/// "inside the margin" can be infinity.
///
/// `None` for any other width — fail closed, no discharge.
pub(super) const fn float_overflow_discharge_margin(width: u32) -> Option<f64> {
    match width {
        64 => Some(FLOAT_OVERFLOW_DISCHARGE_MARGIN),
        32 => Some(pow2_f64(125)),
        _ => None,
    }
}

/// The tiny-addend bound for an operation of this IEEE width: `ulp(MAX) / 2`,
/// the round-to-infinity boundary argued out above.
///
/// f64: `ulp(MAX) = 2^(1023 - 52) = 2^971`, so the bound is `2^970`.
/// binary32: `ulp(MAX) = 2^(127 - 23) = 2^104`, so the bound is `2^103`.
///
/// `None` for any other width — fail closed, no discharge.
pub(super) const fn float_add_tiny_operand_bound(width: u32) -> Option<f64> {
    match width {
        64 => Some(FLOAT_ADD_TINY_OPERAND_BOUND),
        32 => Some(pow2_f64(103)),
        _ => None,
    }
}

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

    /// REBIND-AWARE staleness query (S2b): is a fact whose sole free var is `name`
    /// stale at `block`? True iff some TRACKED name that REBINDS `name` — the
    /// directional [`path_defs::write_rebinds`]: prefix-ancestor / descendant /
    /// index-alias (`place_names_overlap`) plus the `[_l]` index-segment channel —
    /// has a non-entry reaching-def version at `block`.
    ///
    /// This closes the projection gap the shadow audit surfaced: the oracle tracks
    /// whole gen-set names (`s`), but the kill drops a fact about `s.0` via overlap
    /// with a write to `s`. The kill's drop set IS the tracked names with a non-entry
    /// version (the proven base parity), so this query is drop-equivalent to the kill
    /// for ANY `name`, tracked or not — a versioned read of `s.0` is renamed away
    /// exactly when the kill would drop the fact.
    ///
    /// AMENDED (merge, 2026-09-18): the two sides no longer run the SAME predicate,
    /// so the equivalence above is now claimed only up to that difference. This query
    /// tests `write_rebinds`; the kill (`formula_survives_redefs` →
    /// `formula_mentions_redef`) tests the WIDER `dest_write_rebinds`, which adds
    /// `write_covers_derived_slice_len`. The kill can therefore drop a fact about
    /// `s__slice_len` on a write of `s` that this query calls unversioned. `VersionCtx`
    /// is `#[cfg(test)]` — a retired witness read only by
    /// `path_defs::shadow_parity_disagreements_overlap` — so the gap is a parity-audit
    /// question, not a production renaming one; production reads go through
    /// [`StmtVersionCtx::version_token_at`], whose gate already tests
    /// `dest_write_rebinds`.
    pub(crate) fn is_versioned_query(&self, block: BlockId, name: &str) -> bool {
        let entry_only = std::collections::BTreeSet::from([-1i64]);
        let Some(vers) = self.per_block.get(&block) else { return false };
        vers.iter().any(|(tracked, vset)| *vset != entry_only && write_rebinds(tracked, name))
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

/// Token PREFIX for a pinned in-place-update read whose entry-denotation the
/// full-graph mint gate could NOT establish (`full_graph_union_is_entry_only`
/// false at the minting block): the read is stamped `#pre_s{block}_{k}` instead
/// of `#e`. A fresh, block-local, NEVER-TIEABLE spelling — `entry_sentinel_ties`
/// matches the token `e` exactly — so it still prevents the `x#t == f(x#t)`
/// recurrence without ever asserting the pre-write value is the entry value.
/// Distinct by construction from real establish tokens (`s{b}_{k}`), the phantom
/// entry-havoc token (`s{b}_pre`), mixed joins (`e_s{b}_t`), the loop
/// transition havoc prefix (`e45_`), and the TINV unwind havoc prefix (`tinvu_`,
/// `crate::TINV_UNWIND_HAVOC_TOKEN_PREFIX`).
pub(crate) const PRE_WRITE_SENTINEL_PREFIX: &str = "pre";

/// Statement-granular version oracle: the version of a place name at a precise
/// `(block, stmt_idx)` program point, distinguishing reads that straddle a
/// same-block write.
///
/// Built once per body (memoized per function; see [`stmt_versions_for`] and
/// `crate::havoc_memo::version_oracle`) from two linear-size indexes:
///
///  * the per-block WRITE index ([`block_writes::FnWrites`]) — the intra-block arm:
///    the latest writing statement before the read, the `writes_until` gate and the
///    `s{b}_pre` phantom, each by lookup;
///  * the inter-block SSA oracle ([`version_ssa::VersionSsa`]) — the reaching-version
///    sets at block entry, resolved on demand over the dominator tree.
///
/// Every answer is byte-identical to the retired dense-map oracle (two whole-CFG
/// fixpoints, `Θ(blocks × names)` `String` maps, a step cap and budget polls), which is
/// kept in `legacy_version_oracle` as a differential: under `cfg(test)` (and the
/// `version-oracle-differential` feature) every query is answered by both and asserted
/// equal.
pub(crate) struct StmtVersionCtx {
    ssa: version_ssa::VersionSsa,
    /// Declared local names containing `'#'` (empty in normal Rust bodies), precomputed
    /// once per oracle so `#`-minted SSA/sentinel collision checks stay `O(1)`.
    hash_local_names: FxHashSet<String>,
    /// Memo for [`Self::ever_versioned`], keyed by name. Trust (2026-09-30,
    /// stale-read seal): the answer is a pure function of `func` and the name, so
    /// caching it cannot change which answer a caller sees.
    ever_versioned_memo: std::cell::RefCell<FxHashMap<String, bool>>,
    /// Memo for [`Self::versioned_block_defs_at_point`], keyed by
    /// `(block.id.0, block_key(block), block.stmts.len(), end)`.
    versioned_block_defs_memo: std::cell::RefCell<
        FxHashMap<(usize, usize, usize, usize), std::rc::Rc<block_defs::VersionedBlockDefs>>,
    >,
    /// Memo for [`Self::terminator_kill`], keyed by
    /// `(block.id.0, block as *const _ as usize, callee_write_set::current_scope_id())`.
    terminator_kill_memo:
        std::cell::RefCell<FxHashMap<(usize, usize, u64), std::rc::Rc<TerminatorKillData>>>,
    /// Memo for [`Self::prepared_block_outflow`], keyed by
    /// `(block.id.0, block as *const _ as usize)`.
    block_outflow_memo:
        std::cell::RefCell<FxHashMap<(usize, usize), std::rc::Rc<path_defs::PreparedBlockOutflow>>>,
    /// Memo for [`Self::spelled_guard_paths_for`], keyed by
    /// `(at, canonical_ptr, canonical_len, callee_write_set::current_scope_id())`.
    spelled_guard_paths_memo:
        std::cell::RefCell<FxHashMap<(BlockId, usize, usize, u64), std::rc::Rc<Vec<Vec<Formula>>>>>,
    #[cfg(any(test, feature = "version-oracle-differential"))]
    legacy: Option<legacy_version_oracle::LegacyStmtVersions>,
}

impl StmtVersionCtx {
    /// Build (or reuse) this function's version oracle.
    ///
    /// Memoized per function behind `crate::havoc_memo::version_oracle` (inert
    /// outside a `gen_work` scope). The oracle's answers are a pure function of
    /// `func`; its lazily-filled join memo changes only how often a set is computed,
    /// never which set, so sharing one `Rc` among every site is observationally
    /// identical to each building its own.
    pub(crate) fn build(func: &VerifiableFunction) -> std::rc::Rc<Self> {
        crate::havoc_memo::version_oracle(func, || {
            let ssa = version_ssa::VersionSsa::build(func);
            let mut hash_local_names = FxHashSet::default();
            for decl in &func.body.locals {
                if let Some(name) = decl.name.as_deref()
                    && name.contains('#')
                {
                    hash_local_names.insert(name.to_owned());
                }
            }
            // No differential for an oracle built after a budget trip: it fails closed
            // on purpose where the retired one answered from whatever its polls let
            // through (see `FnWrites::built_after_trip`).
            #[cfg(any(test, feature = "version-oracle-differential"))]
            let legacy = (legacy_version_oracle::differential_enabled()
                && !ssa.writes().built_after_trip())
            .then(|| legacy_version_oracle::LegacyStmtVersions::build(func))
            .filter(legacy_version_oracle::LegacyStmtVersions::converged);
            StmtVersionCtx {
                ssa,
                hash_local_names,
                ever_versioned_memo: std::cell::RefCell::new(FxHashMap::default()),
                versioned_block_defs_memo: std::cell::RefCell::new(FxHashMap::default()),
                terminator_kill_memo: std::cell::RefCell::new(FxHashMap::default()),
                block_outflow_memo: std::cell::RefCell::new(FxHashMap::default()),
                spelled_guard_paths_memo: std::cell::RefCell::new(FxHashMap::default()),
                #[cfg(any(test, feature = "version-oracle-differential"))]
                legacy,
            }
        })
    }

    /// Whether any declared local in `func.body.locals` carries `'#'` in its name.
    #[inline]
    pub(crate) fn has_any_hash_local(&self) -> bool {
        !self.hash_local_names.is_empty()
    }

    /// Whether `minted` (which contains `'#'`) collides with a declared local name.
    #[inline]
    pub(crate) fn has_hash_local_named(&self, minted: &str) -> bool {
        !self.hash_local_names.is_empty() && self.hash_local_names.contains(minted)
    }

    #[cfg(any(test, feature = "version-oracle-differential"))]
    pub(super) fn has_legacy(&self) -> bool {
        self.legacy.is_some()
    }

    pub(super) fn spelled_guard_paths_for(
        &self,
        func: &VerifiableFunction,
        at: BlockId,
        guard_paths: &[Vec<(BlockId, GuardCondition)>],
    ) -> Option<(std::rc::Rc<Vec<Vec<Formula>>>, usize, usize)> {
        let cacheable = !crate::fn_memo::is_disabled()
            && !trust_types::verify_budget::exhausted_readonly()
            && !self.ssa.writes().built_after_trip();
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let cacheable =
            cacheable && !(self.legacy.is_some() && legacy_version_oracle::legacy_answers());
        if !cacheable {
            return None;
        }
        let addr = std::ptr::from_ref(func) as usize;
        let canonical_map = FUNC_ANALYSIS_MEMO.with(|memo| {
            memo.borrow()
                .last()
                .filter(|frame| frame.func_addr == addr)
                .and_then(|frame| frame.guard_map.clone())
        })?;
        let canonical = canonical_map.get(&at)?;
        let canon_slice = canonical.as_slice();
        let elem_size = std::mem::size_of::<Vec<(BlockId, GuardCondition)>>();
        if elem_size == 0 || guard_paths.len() > canon_slice.len() {
            return None;
        }
        let canon_ptr = canon_slice.as_ptr() as usize;
        let sub_ptr = guard_paths.as_ptr() as usize;
        if sub_ptr < canon_ptr || (sub_ptr - canon_ptr) % elem_size != 0 {
            return None;
        }
        let start_idx = (sub_ptr - canon_ptr) / elem_size;
        if !canon_slice
            .get(start_idx..start_idx + guard_paths.len())
            .is_some_and(|s| std::ptr::eq(s, guard_paths))
        {
            return None;
        }
        let key = (
            at,
            canon_ptr,
            canon_slice.len(),
            callee_write_set::current_scope_id(),
        );
        if let Some(hit) = self.spelled_guard_paths_memo.borrow().get(&key).cloned() {
            return Some((hit, start_idx, guard_paths.len()));
        }
        let computed = std::rc::Rc::new(safety::spell_guard_paths_uncached(
            func,
            self,
            at,
            canon_slice,
        ));
        if !trust_types::verify_budget::exhausted_readonly() {
            self.spelled_guard_paths_memo
                .borrow_mut()
                .insert(key, std::rc::Rc::clone(&computed));
        }
        Some((computed, start_idx, guard_paths.len()))
    }

    pub(super) fn prepared_block_outflow(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> Option<std::rc::Rc<path_defs::PreparedBlockOutflow>> {
        let cacheable = !crate::fn_memo::is_disabled()
            && !trust_types::verify_budget::exhausted_readonly()
            && !self.ssa.writes().built_after_trip()
            && func.body.blocks.get(block.id.0).is_some_and(|b| std::ptr::eq(b, block));
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let cacheable =
            cacheable && !(self.legacy.is_some() && legacy_version_oracle::legacy_answers());
        if !cacheable {
            return None;
        }
        let key = (block.id.0, std::ptr::from_ref(block) as usize);
        if let Some(hit) = self.block_outflow_memo.borrow().get(&key).cloned() {
            return Some(hit);
        }
        let built = std::rc::Rc::new(path_defs::PreparedBlockOutflow::default());
        self.block_outflow_memo.borrow_mut().insert(key, std::rc::Rc::clone(&built));
        Some(built)
    }

    pub(crate) fn versioned_block_defs_at_point(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        end: usize,
    ) -> std::rc::Rc<block_defs::VersionedBlockDefs> {
        let end = end.min(block.stmts.len());
        let cacheable = !crate::fn_memo::is_disabled()
            && !trust_types::verify_budget::exhausted_readonly()
            && !self.ssa.writes().built_after_trip();
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let cacheable =
            cacheable && !(self.legacy.is_some() && legacy_version_oracle::legacy_answers());
        let key = (block.id.0, crate::havoc_memo::block_key(block), block.stmts.len(), end);
        if cacheable
            && let Some(hit) = self.versioned_block_defs_memo.borrow().get(&key).cloned()
        {
            return hit;
        }
        let computed =
            std::rc::Rc::new(block_defs::VersionedBlockDefs::compute(self, func, block, end));
        if cacheable && !trust_types::verify_budget::exhausted_readonly() {
            self.versioned_block_defs_memo
                .borrow_mut()
                .insert(key, std::rc::Rc::clone(&computed));
        }
        computed
    }

    pub(super) fn block_entry_kill_rebinds(&self, b: usize, read: &str) -> bool {
        let writes = self.ssa.writes();
        let Some(bw) = writes.block(b) else {
            return true;
        };
        bw.stmt_explicit_dest_rebinds(&writes.names, read)
            || (bw.any_opaque_store() && writes.havoc_dest_rebinds(read))
            || (bw.gen_all() && writes.all_dest_rebinds(read))
    }

    pub(super) fn first_writer_before(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        end: usize,
        name: &str,
    ) -> Option<usize> {
        let clamped = end.min(block.stmts.len());
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if self.legacy.is_some() && legacy_version_oracle::legacy_answers() {
            return (0..clamped).find(|&j| stmt_writes_name(func, block, j, name));
        }
        if self.ssa.writes().built_after_trip()
            || !func.body.blocks.get(block.id.0).is_some_and(|b| std::ptr::eq(b, block))
        {
            return (0..clamped).find(|&j| stmt_writes_name(func, block, j, name));
        }
        let fast =
            self.ssa.writes().first_writer_before(block.id.0, clamped, name).map(|w| w as usize);
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if self.legacy.is_some() {
            let slow = (0..clamped).find(|&j| stmt_writes_name(func, block, j, name));
            assert_eq!(
                fast, slow,
                "first_writer_before differential mismatch in {} bb{} end={clamped} for `{name}`",
                func.name, block.id.0
            );
        }
        fast
    }

    /// `#token` for `name` read at `(block, stmt_idx)`, or `None` when the value
    /// there is the entry/parameter value (so unversioned names stay byte-identical
    /// on the flip). A same-block write in `stmts[..stmt_idx]` versions it; a write
    /// LATER in the block does NOT (the block-level oracle gets this wrong).
    ///
    /// THE INTRA-BLOCK ARM, and why its order is safe. The retired arm tested the
    /// `writes_until(block, stmt_idx)` GATE first — does some name written in
    /// `stmts[..stmt_idx]` `dest_write_rebinds` `name` — and only then searched the
    /// statements for the latest one that itself writes `name` (`stmt_writes_name`),
    /// minting `s{b}_{k}`. The search is answered first here, and that is the same
    /// function: every case `stmt_writes_name` accepts puts the written name into
    /// `writes_until` under a relation `dest_write_rebinds` contains (an `Assign` /
    /// `Deinit` destination under `dest_write_rebinds` itself; the index fallback
    /// under `write_rebinds`; an opaque store's havoc names, which
    /// `deref_store_havoc_names_over` adds with the same confinement filter, under
    /// `write_rebinds`; a `SetDiscriminant` place and a `CopyNonOverlapping`'s names,
    /// which `extend_with_assigned_place_dests` adds, under `write_rebinds`), so a
    /// found writer implies the gate. When there is no writer the gate decides, as
    /// before, between the fail-closed phantom `s{b}_pre` and the fall-through:
    ///
    /// Trust #soundness (2026-08-26): the gate admits EXACTLY what the per-statement
    /// search admits under `dest_write_rebinds` — a write of `p` versions the DERIVED
    /// `p__slice_len` read at the same statement (`p = &raw const *sb; (*p)[2]` used
    /// to keep the pre-reassignment length and proved an out-of-bounds index).
    ///
    /// Trust #false-refutation (2026-09-21, WRITE-THEN-READ on a `&mut [T]`): when the
    /// gate fired ONLY through the derived `__slice_len` channel of an opaque store's
    /// havoc names (nothing in `writes_until` `write_rebinds` the name), the search is
    /// right and the read falls through to the inter-block set — the value at the read
    /// IS the block-entry value. Every other gate-without-writer case keeps the
    /// phantom, which `flip_matches_kill_stmt` pins (4 disagreements on
    /// `sem_stale_blockdef` caught a broader fall-through). `TRUST_VERSION_GATE_TRACE`
    /// prints every name reaching the fall-through.
    pub(crate) fn version_token_at(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> Option<String> {
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(legacy) = &self.legacy
            && legacy_version_oracle::legacy_answers()
        {
            return legacy.version_token_at(func, block, stmt_idx, name);
        }
        let token = self.version_token_at_ssa(func, block, stmt_idx, name);
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(legacy) = &self.legacy {
            let expected = legacy.version_token_at(func, block, stmt_idx, name);
            assert_eq!(
                token, expected,
                "version oracle differential: `{name}` at {block:?}[{stmt_idx}] of `{}`",
                func.def_path
            );
        }
        token
    }

    /// Trust (2026-09-30, stale-read seal — root cause of the `vac` false proofs):
    /// true iff SOME program point of `func` versions `name`, i.e. some block `b`
    /// has `version_token_at(b, b.stmts.len(), name)` set. Probing each block's
    /// END is enough: a point with a token implies its block's end has one (a
    /// later in-block write only moves the token, never erases it).
    ///
    /// When this is FALSE a bare `name` stays bare under EVERY whole-formula
    /// rename, so a bare read of it needs no seal. When it is TRUE a bare read
    /// left in a formula stamped at one point can be RE-STAMPED by a later rename
    /// at another point with a post-write token — the stale re-stamp that turned
    /// `s.f#s0_0 == !s.f` into the unsatisfiable `s.f#s0_0 == !s.f#s0_0`
    /// ([`super::path_defs::seal_bare_reads`] closes it).
    ///
    /// Fails closed (answers TRUE — seal more) when the write index was built
    /// after the verify budget tripped: its gen-sets can be short, so "no block
    /// versions it" is not evidence there. Memoized per function (this oracle is).
    pub(crate) fn ever_versioned(&self, func: &VerifiableFunction, name: &str) -> bool {
        if self.ssa.writes().built_after_trip() {
            return true;
        }
        if let Some(&hit) = self.ever_versioned_memo.borrow().get(name) {
            return hit;
        }
        let versioned = func
            .body
            .blocks
            .iter()
            .any(|b| self.version_token_at(func, b.id, b.stmts.len(), name).is_some());
        self.ever_versioned_memo.borrow_mut().insert(name.to_string(), versioned);
        versioned
    }

    /// Trust (2026-10-16, S2): every `name#token` symbol a formula of `func` uses
    /// for a LOOP-CARRIED JOIN — the value of a tracked name at the entry of a loop
    /// header that is a pseudo-def of it (step 0 of `version_ssa`'s resolution,
    /// [`version_ssa::VersionSsa::loop_header_join_names`]). The token is the
    /// generator's own spelling of a read at the header's entry
    /// (`version_token_at(h, 0, name)`), so it matches the symbols in the VCs byte
    /// for byte (`i#s0_0_s23_0`). Such a symbol has a back-edge operand and no
    /// defining equation: only its type range and monotone bounds constrain it, so a
    /// model over it is a model of the formula, not of any iteration.
    ///
    /// Each symbol maps to its loop header's block index.
    ///
    /// `None` when the answer is not exact (an oracle built after a budget trip) or
    /// exceeds `max_queries` (header × name) queries — the caller fails closed.
    pub(crate) fn loop_carried_join_symbols(
        &self,
        func: &VerifiableFunction,
        max_queries: usize,
    ) -> Option<FxHashMap<String, usize>> {
        let cfg = self.ssa.cfg();
        let headers: Vec<usize> =
            (0..cfg.n_blocks()).filter(|&b| cfg.is_loop_header(b as u32)).collect();
        let mut out = FxHashMap::default();
        if headers.is_empty() {
            return Some(out);
        }
        if headers.len().saturating_mul(self.ssa.name_count()) > max_queries {
            return None;
        }
        for h in headers {
            for name in self.ssa.loop_header_join_names(h)? {
                if let Some(token) = self.version_token_at(func, BlockId(h), 0, &name) {
                    out.insert(format!("{name}#{token}"), h);
                }
            }
        }
        Some(out)
    }

    fn version_token_at_ssa(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> Option<String> {
        // Trust (lane-A CSE): the id==index invariant, filtered exactly as before.
        func.body.blocks.get(block.0).filter(|b| b.id == block)?;
        let writes = self.ssa.writes();
        if let Some(k) = writes.last_writer_before(block.0, stmt_idx, name) {
            return Some(format!("s{}_{k}", block.0));
        }
        let (gate_dest, gate_plain) = writes.gate(func, block.0, stmt_idx, name);
        if gate_dest {
            if gate_plain {
                return Some(format!("s{}_pre", block.0));
            }
            static VERSION_GATE_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *VERSION_GATE_TRACE
                .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_VERSION_GATE_TRACE"))
            {
                eprintln!(
                    "[VERSION_GATE] fall-through: fn={} block={} stmt={stmt_idx} name={name}",
                    func.name, block.0,
                );
            }
        }
        // Else the inter-block reaching set at block entry: the union over every
        // tracked name that `write_rebinds` `name` (an OVERLAP union, not an exact-key
        // get — the callee-write false-accept sweep: a call havocs the base `r`, the
        // read spells `r*`), spelled `None` when it is empty or exactly `{e}` (bare,
        // never-rewritten reads stay byte-identical) and otherwise as the sorted
        // `_`-joined token list — a MIXED union keeps `e` in the join (`e_s1_t`),
        // because a partially-entry-valued read denotes a different value than a
        // definitely-post-write one. The union ranges over DIFFERENT tracked names, so
        // a joined token can carry components from several of them; the guarantee
        // that makes that sound — THE DEF'S WRITE IS THE LAST WRITE OF EVERY UNION
        // COMPONENT ON EVERY PATH into the successor — is carried by the kills
        // (`thread_own_defs_in_statement_order`, `extract_block_definitions_until_impl`)
        // and by a correct name for the def's destination (`referent_fold::is_stable`).
        self.ssa.inter_block_token(block.0, name)
    }

    /// The SSA [`version_ssa::ValueId`] `name` denotes when read at `(block, stmt_idx)`,
    /// or `None` when it cannot be named exactly.
    ///
    /// The statement-granular twin of [`Self::version_token_at`], with the same two
    /// arms: a same-block writer in `stmts[..stmt_idx]` names its own statement; with
    /// none, the block-entry value ([`version_ssa::VersionSsa::entry_value_id`]). Where
    /// the token oracle mints a phantom (`s{b}_pre`) or falls through on the derived
    /// `__slice_len` channel, this answers `None` — there is no single value to name.
    ///
    /// Read the contract on [`version_ssa::ValueId`] before comparing two of these:
    /// equality means "the same value" only between a point and a point it DOMINATES.
    pub(crate) fn value_id_at(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> Option<version_ssa::ValueId> {
        func.body.blocks.get(block.0).filter(|b| b.id == block)?;
        let writes = self.ssa.writes();
        if let Some(k) = writes.last_writer_before(block.0, stmt_idx, name) {
            return Some(version_ssa::ValueId::Def { block: block.0 as u32, stmt: k });
        }
        if writes.gate(func, block.0, stmt_idx, name).0 {
            return None;
        }
        self.ssa.entry_value_id(block.0, name)
    }

    /// [`Self::value_id_at`], answering a read two or more tracked names rebind too
    /// ([`version_ssa::VersionSsa::entry_value_id_grouped`]; its doc has the argument).
    /// Trust (2026-10-17, gate RCA precision T3): asked only by the path-guard spelling
    /// (`guard_value_spelling`); the same-block arms are [`Self::value_id_at`]'s.
    pub(crate) fn value_id_at_grouped(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        stmt_idx: usize,
        name: &str,
    ) -> Option<version_ssa::ValueId> {
        func.body.blocks.get(block.0).filter(|b| b.id == block)?;
        let writes = self.ssa.writes();
        if let Some(k) = writes.last_writer_before(block.0, stmt_idx, name) {
            return Some(version_ssa::ValueId::Def { block: block.0 as u32, stmt: k });
        }
        if writes.gate(func, block.0, stmt_idx, name).0 {
            return None;
        }
        self.ssa.entry_value_id_grouped(block.0, name)
    }

    /// The CFG index the oracle resolves over: the dominator tree of the full
    /// (unwind-inclusive) block graph, augmented with the virtual entry `E` and root `R`.
    pub(crate) fn cfg(&self) -> &cfg_index::CfgIndex {
        self.ssa.cfg()
    }

    /// True iff `block`'s entry-version map TRACKS a name overlapping `name` with a
    /// non-empty reaching set.
    ///
    /// Where it does NOT, [`Self::version_token_at`]'s `None` does not mean "the
    /// entry value": a block unreachable from bb0 across full-graph edges has no
    /// reaching set, and a never-written name is simply untracked. A caller that
    /// reads a bare (or `#e`) spelling AS the entry value must consult this first.
    #[cfg(test)]
    pub(crate) fn entry_map_covers(&self, block: BlockId, name: &str) -> bool {
        let covers = self.ssa.covers(block.0, name);
        if let Some(legacy) = &self.legacy {
            assert_eq!(
                covers,
                legacy.entry_map_covers(block, name),
                "entry_map_covers differential"
            );
        }
        covers
    }

    /// THE `#e` MINT GATE's oracle: true iff EVERY runtime path into `block` —
    /// normal or unwind — delivers `name`'s function-ENTRY value, i.e. the
    /// UNWIND-INCLUSIVE reaching-version union at `block`'s entry is exactly
    /// `{e}`. Same overlap-union lookup as `version_token_at`'s inter-block arm:
    /// `{e}` is seeded only at bb0 and any gen replaces it, so with unwind edges IN
    /// the predecessor relation an exactly-`{e}` union means no writer of `name` on
    /// ANY path into the block.
    ///
    /// Fails closed two ways, each toward "not entry" (no `#e` mint):
    ///  * `block` is unreachable from bb0 across full-graph edges (empty union);
    ///  * ANY overlapping tracked name contributes a non-`e` token.
    ///
    ///  * the oracle's write index was built after the ambient verify budget
    ///    tripped (`FnWrites::built_after_trip`): its gen-sets come from a polled
    ///    extraction that returns FEWER names on a trip, so an exactly-`{e}` union
    ///    there is not evidence that no writer exists. (The retired form's third way,
    ///    "the full-graph fixpoint hit its step cap", is gone with the fixpoint.)
    pub(crate) fn full_graph_union_is_entry_only(&self, block: BlockId, name: &str) -> bool {
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(legacy) = &self.legacy
            && legacy_version_oracle::legacy_answers()
        {
            return legacy.full_graph_union_is_entry_only(block, name);
        }
        let entry_only = self.ssa.union_is_entry_only(block.0, name);
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(legacy) = &self.legacy {
            assert_eq!(
                entry_only,
                legacy.full_graph_union_is_entry_only(block, name),
                "full_graph_union_is_entry_only differential: `{name}` at {block:?}"
            );
        }
        entry_only
    }

    /// THE STATEMENT-PREFIX KILL, probed: whether some name of
    /// `writes_until(block, point)` — or, when `block_havoc`, of the block's
    /// opaque-store havoc list — `dest_write_rebinds` `name`. Exactly the membership
    /// test `formula_survives_redefs` applies to every free mention against that set
    /// (`v2_live_path_defs_at_point`), answered by the write index.
    pub(crate) fn prefix_kill_rebinds(
        &self,
        func: &VerifiableFunction,
        block: BlockId,
        point: usize,
        name: &str,
        block_havoc: bool,
    ) -> bool {
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if self.legacy.is_some() && legacy_version_oracle::legacy_answers() {
            let bb = &func.body.blocks[block.0];
            let set = writes_until_uncached(func, bb, point);
            return set.iter().any(|n| dest_write_rebinds(n, name))
                || (block_havoc
                    && deref_store_havoc_names(func, bb).iter().any(|n| write_rebinds(n, name)));
        }
        let writes = self.ssa.writes();
        // Trust (2026-09-29): the CONSERVATIVE whole-block havoc — it also covers
        // opaque stores at or after `point`, which cannot change the value read at
        // `point` — is judged with the PLAIN relation a havoc base name carries
        // (`WriteIndex::havoc_rebinds`), not the destination relation: an element
        // store through `s: &mut [u8]` does not write `s__slice_len`. Dest mode here
        // severed every length tie of a row in a block that stores through its slice,
        // and the store half of `digits[i] -= 1` — whose OWN store is the only opaque
        // store of its block, at the row's point — was refuted at
        // `digits__slice_len = 0` beside `_6__slice_len = 1`
        // (tests/false_refutation_shapes_realmir.rs). A store BEFORE `point` is still
        // judged by `gate` exactly as before.
        (block_havoc && writes.havoc_rebinds(name)) || writes.gate(func, block.0, point, name).0
    }

    /// THE TERMINATOR KILL of `block`: the kill set `terminator_def_names(func, block)`,
    /// prepared for many `formula_survives_redefs` tests. When the terminator havocs
    /// the whole-function list — unrefined, or refined per call (a few names dropped,
    /// a few added) — that list is probed through the write index's ONE shared havoc
    /// index instead of being copied and re-indexed per block (a Call/Drop terminator
    /// in a body with many pointer locals — every call of `ever-init-many-locals` —
    /// used to cost the whole list per block per pass).
    pub(crate) fn terminator_kill(
        &self,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
    ) -> TerminatorKill<'_> {
        let writes = self.ssa.writes();
        let cacheable = !crate::fn_memo::is_disabled()
            && !trust_types::verify_budget::exhausted_readonly()
            && !writes.built_after_trip()
            && func.body.blocks.get(block.id.0).is_some_and(|b| std::ptr::eq(b, block));
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let cacheable = cacheable
            && !differential_enabled()
            && !(self.legacy.is_some() && legacy_version_oracle::legacy_answers());
        let key = (
            block.id.0,
            std::ptr::from_ref(block) as usize,
            callee_write_set::current_scope_id(),
        );
        if cacheable
            && let Some(data) = self.terminator_kill_memo.borrow().get(&key).cloned()
        {
            return TerminatorKill { writes, data };
        }
        let term = terminator_def_names_structured(func, block);
        let mut names: Vec<String> = Vec::new();
        // The havoc-list names this terminator drops, as text (the split reference of
        // `survives_havoc_plain`'s differential).
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let diff_enabled = differential_enabled();
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let mut removed_text: Vec<String> = Vec::new();
        let havoc = match &term.havoc {
            TermHavoc::None => None,
            TermHavoc::Function => Some(Vec::new()),
            TermHavoc::Refined(delta) => {
                let in_h = |n: &str| writes.in_havoc_text(n);
                names.extend(delta.added(&in_h));
                let removed_names = delta.removed(&in_h);
                #[cfg(any(test, feature = "version-oracle-differential"))]
                if diff_enabled {
                    removed_text.extend(removed_names.iter().map(|n| n.to_string()));
                }
                let mut removed: Vec<rebind_index::NameId> =
                    removed_names.iter().filter_map(|n| writes.name_id(n)).collect();
                removed.sort_unstable();
                Some(removed)
            }
            TermHavoc::Escape(e) => {
                #[cfg(any(test, feature = "version-oracle-differential"))]
                if diff_enabled {
                    removed_text.extend(e.dropped.iter().cloned());
                }
                let mut removed: Vec<rebind_index::NameId> =
                    e.dropped.iter().filter_map(|n| writes.name_id(n)).collect();
                removed.sort_unstable();
                Some(removed)
            }
        };
        for e in &term.extra {
            let (TermExtra::Push(n) | TermExtra::PushIfAbsent(n)) = e;
            names.push(n.clone());
        }
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let reference: FxHashSet<String> = if diff_enabled {
            terminator_def_names(func, block).into_iter().collect()
        } else {
            FxHashSet::default()
        };
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let reference_havoc: Vec<String> = if diff_enabled && havoc.is_some() {
            path_defs::function_havoc_names(func)
                .iter()
                .filter(|n| !removed_text.contains(n))
                .cloned()
                .collect()
        } else {
            Vec::new()
        };
        #[cfg(any(test, feature = "version-oracle-differential"))]
        let reference_extra = if diff_enabled { names.clone() } else { Vec::new() };
        let data = std::rc::Rc::new(TerminatorKillData {
            empty: havoc.is_none() && names.is_empty(),
            havoc,
            extra: KillSet::new(&names),
            #[cfg(any(test, feature = "version-oracle-differential"))]
            reference,
            #[cfg(any(test, feature = "version-oracle-differential"))]
            reference_havoc,
            #[cfg(any(test, feature = "version-oracle-differential"))]
            reference_extra,
        });
        if cacheable && !trust_types::verify_budget::exhausted_readonly() {
            self.terminator_kill_memo.borrow_mut().insert(key, std::rc::Rc::clone(&data));
        }
        TerminatorKill { writes, data }
    }

    /// THE MAY-REASSIGNED KILL, probed: whether some name of the retired
    /// `v2_may_reassigned_per_block(func)[block]` set `dest_write_rebinds` `name` —
    /// i.e. whether a fact mentioning `name` is killed at `block` by a write on some
    /// path into it or by the block's own statements. See
    /// `version_ssa::VersionSsa::may_reassigned_rebinds`.
    pub(crate) fn may_reassigned_rebinds(&self, block: BlockId, name: &str) -> bool {
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(legacy) = &self.legacy
            && legacy_version_oracle::legacy_answers()
        {
            return legacy.may_reassigned_rebinds(block, name);
        }
        let rebinds = self.ssa.may_reassigned_rebinds(block.0, name);
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if let Some(legacy) = &self.legacy {
            assert_eq!(
                rebinds,
                legacy.may_reassigned_rebinds(block, name),
                "may-reassigned differential: `{name}` at {block:?}"
            );
        }
        rebinds
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
        let Some(bb) = func.body.blocks.get(block.0).filter(|b| b.id == block) else {
            return false;
        };
        let stale = writes_until(func, bb, stmt_idx).iter().any(|n| write_rebinds(n, name))
            || self.ssa.has_non_entry_rebinder(block.0, name);
        if let Some(legacy) = &self.legacy {
            assert_eq!(
                stale,
                legacy.is_versioned_stale_at(func, block, stmt_idx, name),
                "is_versioned_stale_at differential"
            );
        }
        stale
    }

    /// The inter-block SSA oracle (parity tests).
    #[cfg(test)]
    pub(crate) fn ssa(&self) -> &version_ssa::VersionSsa {
        &self.ssa
    }
}

struct TerminatorKillData {
    /// When the terminator havocs the whole-function list: the names of it the
    /// refinement dropped (sorted; empty when unrefined).
    havoc: Option<Vec<rebind_index::NameId>>,
    /// Every other name of the set.
    extra: KillSet,
    empty: bool,
    #[cfg(any(test, feature = "version-oracle-differential"))]
    reference: FxHashSet<String>,
    /// The havoc-list part of `reference` (the whole-function list minus the names
    /// the refinement dropped), judged under the plain relation by
    /// [`TerminatorKill::survives_havoc_plain`]'s differential.
    #[cfg(any(test, feature = "version-oracle-differential"))]
    reference_havoc: Vec<String>,
    /// Every other name of `reference` (refinement additions, destination and
    /// stored-pointee extras), judged under the destination relation.
    #[cfg(any(test, feature = "version-oracle-differential"))]
    reference_extra: Vec<String>,
}

/// A terminator's kill set (see [`StmtVersionCtx::terminator_kill`]).
pub(crate) struct TerminatorKill<'a> {
    /// The oracle's write index (its shared whole-function havoc index).
    writes: &'a block_writes::FnWrites,
    data: std::rc::Rc<TerminatorKillData>,
}

impl TerminatorKill<'_> {
    pub(crate) fn is_empty(&self) -> bool {
        self.data.empty
    }

    /// `formula_survives_redefs(f, terminator_def_names(func, block))`.
    pub(crate) fn survives(&self, f: &Formula) -> bool {
        let survives = self.data.empty
            || formula_survives_redefs_by(f, &mut |n| {
                self.data.extra.kills(n)
                    || self.data.havoc.as_ref().is_some_and(|removed| {
                        if removed.is_empty() {
                            self.writes.havoc_dest_rebinds(n)
                        } else {
                            self.writes.havoc_dest_rebinds_except(n, removed)
                        }
                    })
            });
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if differential_enabled() {
            assert_eq!(
                survives,
                formula_survives_redefs(f, &self.data.reference),
                "TerminatorKill differential on {f:?}"
            );
        }
        survives
    }

    /// [`Self::survives`] with the whole-function HAVOC LIST judged under the PLAIN
    /// relation (`write_rebinds`) a havoc base name carries, and every other name —
    /// the call destination and its `__slice_len` twin, a refinement's added
    /// callee-write paths, the stored-pointee names, an unlocatable terminator's
    /// every-local names — still under the destination relation.
    ///
    /// Trust (2026-10-10, SLICE-LEN-CALL-HAVOC-1). The opaque deref-store havoc moved
    /// to the plain relation on 2026-09-29 ([`path_defs::KillSet::havoc`], whose doc
    /// states the premise); the path-definition fixpoint's TERMINATOR kill kept the
    /// destination relation because no fixture distinguished it. One does now: a
    /// slice pattern behind an or-pattern of string literals
    /// (`match (name, args) { ("a" | "b", [x, y]) => .. }`) tests
    /// `PtrMetadata(&raw const (*_13)) == 2` in bb0 through the raw temp `_6`, then
    /// calls `<str as PartialEq>::eq` before the arm. `_6: *const [i64]` is a
    /// mutable-pointer local, so its BASE name is on the havoc list, and the
    /// destination relation read it as a write of `_6__slice_len` — the pointer's
    /// own length metadata, which lives in `_6`'s slot and which no callee can
    /// write without a slot-write channel. The tie `_6__slice_len == _13__slice_len`
    /// and `_7 == _6__slice_len` died at the call, and the arm's `[0 of 2]` read was
    /// refuted at `_16__slice_len = 0` beside `PtrMetadata == 2`
    /// (tla-shapes-families `cvw.rs:474`).
    ///
    /// SOUNDNESS: the premise of [`path_defs::KillSet::havoc`], unchanged: every
    /// pointer that can write a local's slot comes from a slot-write channel
    /// (`own_storage_write_borrow`), and each such local is a
    /// `mutably_borrowed_havoc_names` member whose `__slice_len` twin is on the list
    /// EXPLICITLY, so the plain relation still kills it. Everything reachable
    /// THROUGH a havoc base (`p*`, `p*[_i]`, `p*__slice_len`, `p.f*`) overlaps it
    /// under the plain relation too. Names that denote WRITTEN memory rather than a
    /// pointer base — the destination, the refinement's callee-write paths, the
    /// stored-pointee names — are in `extra` and keep the derived channel.
    pub(crate) fn survives_havoc_plain(&self, f: &Formula) -> bool {
        let survives = self.data.empty
            || formula_survives_redefs_by(f, &mut |n| {
                self.data.extra.kills(n)
                    || self.data.havoc.as_ref().is_some_and(|removed| {
                        if removed.is_empty() {
                            self.writes.havoc_rebinds(n)
                        } else {
                            self.writes.havoc_rebinds_except(n, removed)
                        }
                    })
            });
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if differential_enabled() {
            let reference = formula_survives_redefs_by(f, &mut |n| {
                self.data.reference_extra.iter().any(|w| path_defs::dest_write_rebinds(w, n))
                    || self.data.reference_havoc.iter().any(|w| path_defs::write_rebinds(w, n))
            });
            assert_eq!(survives, reference, "TerminatorKill plain-havoc differential on {f:?}");
        }
        survives
    }
}

/// The per-block path-guard map produced by
/// [`safety::v2_build_path_guard_map`]: for each block, the list of enumerated
/// incoming paths, each a list of `(source block, guard)` pairs.
pub(crate) type PathGuardMap = FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>>;

thread_local! {
    /// Per-function memo frames for the current thread, innermost LAST.
    ///
    /// A STACK rather than a single slot because generation nests: a callee's
    /// body is analyzed inside a caller's generation (`FloatRangeCtx::for_callee`,
    /// `callsite_replay`'s `func_view`, `with_tail_calls_expanded`'s `Cow`
    /// clone). Only the innermost frame is ever consulted, so a nested analysis
    /// of a DIFFERENT body can never be served the outer body's answer — it
    /// simply misses and rebuilds.
    static FUNC_ANALYSIS_MEMO: std::cell::RefCell<Vec<FuncAnalysisFrame>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

struct FuncAnalysisFrame {
    /// Identity of the `VerifiableFunction` this frame memoizes. Sound as an
    /// identity key ONLY because [`FuncAnalysisScope`] holds a live shared
    /// borrow of that function for the frame's whole lifetime: the storage
    /// cannot be freed and reused underneath it, so no other live
    /// `VerifiableFunction` can share the address.
    func_addr: usize,
    /// The address of that function's `body` (pinned by the same borrow).
    body_addr: usize,
    stmt_versions: Option<std::rc::Rc<StmtVersionCtx>>,
    guard_map: Option<std::rc::Rc<PathGuardMap>>,
    path_guard_analysis: Option<std::rc::Rc<safety::PathGuardAnalysis>>,
    path_definition_map: Option<(u64, std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>)>,
    semantic_guard_maps: Vec<((u64, u64), std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>)>,
    row_global_facts: Option<std::rc::Rc<RowGlobalFacts>>,
    range_yield_guards: Option<(u64, std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>)>,
    enumerate_yield_guards: Option<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>>,
    slice_iter_yield_guards: Option<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>>,
    downward_vars: Option<std::rc::Rc<Vec<DownwardVar>>>,
    countdown_facts: Option<std::rc::Rc<CountdownFacts>>,
    primitive_decimal_len_guards: Option<(usize, std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>)>,
    unwrap_panic_vcs: Option<(u64, std::rc::Rc<Vec<(BlockId, VerificationCondition)>>)>,
    write_index: Option<std::rc::Rc<crate::local_defs::LocalWriteIndex>>,
    /// [`crate::guards::unstable_locals`], built on first use.
    unstable_locals: Option<std::rc::Rc<Vec<bool>>>,
    /// [`dominating_facts::DominatingFacts`], built on first use.
    dominating_facts: Option<std::rc::Rc<dominating_facts::DominatingFacts>>,
    /// [`SafetyTerminatorPresence`], built on first use.
    terminator_presence: Option<SafetyTerminatorPresence>,
    /// [`loop_bounds::count_back_edges`], built on first use.
    back_edge_count: Option<usize>,
    /// [`loop_bounds::has_unmodelable_write_uncached`], built on first use.
    has_unmodelable_write: Option<bool>,
    /// [`trust_types::loop_nest::LoopNest::of`], built on first use.
    loop_nest: Option<Option<std::rc::Rc<trust_types::loop_nest::LoopNest>>>,
    /// [`semantic_guard::func_exceeds_vcgen_budget`], built on first use when tracing is off.
    exceeds_vcgen_budget: Option<bool>,
    /// [`crate::enum_entry::has_enum_parameter_uncached`], built on first use.
    enum_entry_has_enum_param: Option<bool>,
    /// [`crate::enum_entry::pure_body_non_call_uncached`], built on first use.
    enum_entry_pure_body_non_call: Option<Option<bool>>,
    /// [`crate::elem_sizes::elem_size_binding_digest`], built on first use.
    elem_size_binding_digest: Option<Option<String>>,
    /// [`crate::primitive_decimal_strings::body_digest`], built on first use.
    primitive_decimal_body_digest: Option<Option<String>>,
    /// [`trust_types::VerifiableBody::contains_memory_image`], built on first use.
    body_contains_memory_image: Option<bool>,
    /// Whether [`crate::validate_function_uncached`] succeeded (`Ok(())`), built on first use.
    validate_function_ok: Option<bool>,
    /// Whether [`trust_types::VerifiableBody::opaque_values_need_placement`] holds for
    /// `func.body`, built on first use (or seeded to `Some(false)` on a placed view).
    opaque_values_need_placement: Option<bool>,
    /// Whether `func` declares any named 128-bit integer parameter (`1..=arg_count`),
    /// built on first use.
    has_wide_int_param: Option<bool>,
    /// [`sep_engine::has_unsafe_patterns_uncached`], built on first use.
    has_sep_unsafe_patterns: Option<bool>,
    /// [`crate::func_has_no_join_uncached`], built on first use.
    has_no_join: Option<bool>,
    /// [`path_defs::func_has_pointer_laundering_uncached`], built on first use.
    has_pointer_laundering: Option<bool>,
    /// [`path_defs::func_has_writable_pointer_laundering_uncached`], built on first use.
    has_writable_pointer_laundering: Option<bool>,
    /// [`path_defs::index_locals_uncached`], built on first use.
    index_locals: Option<std::rc::Rc<Vec<bool>>>,
    /// [`guards::block_predecessors_uncached`], built on first use.
    block_predecessors: Option<std::rc::Rc<Vec<Vec<BlockId>>>>,
    /// [`guards::block_predecessor_edges_uncached`], built on first use.
    block_predecessor_edges: Option<std::rc::Rc<Vec<Vec<BlockId>>>>,
    /// [`FloatRangeCtx::dominating_facts`], keyed by `(block_id, scope_id)`.
    float_guard_facts: FxHashMap<(BlockId, u64), std::rc::Rc<Vec<Formula>>>,
    /// [`FloatRangeCtx::guard_alias_names`], keyed by `local`.
    float_alias_names: FxHashMap<usize, std::rc::Rc<Vec<String>>>,
}

/// Per-function memo for the two whole-CFG analyses that are PURE FUNCTIONS of
/// `func` and were previously rebuilt at EVERY obligation point:
/// [`StmtVersionCtx::build`] (two whole-CFG dataflow fixpoints) and
/// [`safety::v2_build_path_guard_map`] (the path-enumeration walk).
///
/// # Why the memo cannot go stale
///
/// The scope HOLDS `&'f VerifiableFunction`. That shared borrow is live for the
/// scope's whole lifetime, so no `&mut VerifiableFunction` to the same value can
/// exist while a memoized result derived from it is reachable — the mutating
/// entry points (`contracts::bind_compiler_loop_contracts` and
/// `bind_compiler_loop_contract_bundle`, the only ones in this crate) do not
/// compile against a borrowed `func`. Invalidation is discharged by the borrow
/// checker, not by a comment. The same borrow is what licenses the address as an
/// identity key: the storage is pinned live for exactly as long as the key is
/// used.
///
/// # Why a scope and not a threaded parameter
///
/// A threaded `&FuncGuardCache` was implemented first and is strictly nicer, but
/// reaching the hot consumers needs the parameter carried through 19 call sites
/// across `safety`, `checked_vcs`, `overflow_vc`, `block_defs` and `path_defs` —
/// each an edit to a verdict-bearing signature. This is the same RAII +
/// `thread_local!` shape the crate already uses for exactly this reason
/// (`VcgenContextGuard`, and `FAITHFUL_SCALARS` in `trust-mir-extract`), and the
/// borrow above keeps the lifetime and the invalidation rule visible in the type.
///
/// # Fail-safe by construction
///
/// A MISS costs only time: the analysis is rebuilt exactly as before. There is
/// no path on which a miss produces a different answer, because the memoized
/// value is the same pure function of the same `func`.
#[must_use]
pub(crate) struct FuncAnalysisScope<'f> {
    /// The borrow that forbids mutation for this scope's lifetime. Never read —
    /// its job is to exist.
    _func: &'f VerifiableFunction,
    /// Stack depth this scope owns, so `Drop` truncates exactly its own frame
    /// even under an unwind or an out-of-order drop.
    depth: usize,
    _thread_affine: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl<'f> FuncAnalysisScope<'f> {
    pub(crate) fn enter(func: &'f VerifiableFunction) -> Self {
        let depth = FUNC_ANALYSIS_MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            memo.push(FuncAnalysisFrame {
                func_addr: std::ptr::from_ref(func) as usize,
                body_addr: std::ptr::from_ref(&func.body) as usize,
                stmt_versions: None,
                guard_map: None,
                path_guard_analysis: None,
                path_definition_map: None,
                semantic_guard_maps: Vec::new(),
                row_global_facts: None,
                range_yield_guards: None,
                enumerate_yield_guards: None,
                slice_iter_yield_guards: None,
                downward_vars: None,
                countdown_facts: None,
                primitive_decimal_len_guards: None,
                unwrap_panic_vcs: None,
                write_index: None,
                unstable_locals: None,
                dominating_facts: None,
                terminator_presence: None,
                back_edge_count: None,
                has_unmodelable_write: None,
                loop_nest: None,
                exceeds_vcgen_budget: None,
                enum_entry_has_enum_param: None,
                enum_entry_pure_body_non_call: None,
                elem_size_binding_digest: None,
                primitive_decimal_body_digest: None,
                body_contains_memory_image: None,
                validate_function_ok: None,
                opaque_values_need_placement: None,
                has_wide_int_param: None,
                has_sep_unsafe_patterns: None,
                has_no_join: None,
                has_pointer_laundering: None,
                has_writable_pointer_laundering: None,
                index_locals: None,
                block_predecessors: None,
                block_predecessor_edges: None,
                float_guard_facts: FxHashMap::default(),
                float_alias_names: FxHashMap::default(),
            });
            memo.len()
        });
        FuncAnalysisScope { _func: func, depth, _thread_affine: std::marker::PhantomData }
    }

    pub(crate) fn enter_placed(func: &'f VerifiableFunction) -> Self {
        let scope = Self::enter(func);
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo.borrow_mut().last_mut() {
                frame.opaque_values_need_placement = Some(false);
            }
        });
        scope
    }

    pub(crate) fn enter_if_unbound(func: &'f VerifiableFunction) -> Option<Self> {
        let func_addr = std::ptr::from_ref(func) as usize;
        let body_addr = std::ptr::from_ref(&func.body) as usize;
        let bound = FUNC_ANALYSIS_MEMO.with(|memo| {
            memo.borrow()
                .last()
                .is_some_and(|frame| frame.func_addr == func_addr && frame.body_addr == body_addr)
        });
        (!bound).then(|| Self::enter(func))
    }

    pub(crate) fn enter_placed_if_unbound(func: &'f VerifiableFunction) -> Option<Self> {
        let func_addr = std::ptr::from_ref(func) as usize;
        let body_addr = std::ptr::from_ref(&func.body) as usize;
        let bound = FUNC_ANALYSIS_MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            if let Some(frame) = memo
                .last_mut()
                .filter(|frame| frame.func_addr == func_addr && frame.body_addr == body_addr)
            {
                frame.opaque_values_need_placement = Some(false);
                true
            } else {
                false
            }
        });
        (!bound).then(|| Self::enter_placed(func))
    }
}

impl Drop for FuncAnalysisScope<'_> {
    fn drop(&mut self) {
        FUNC_ANALYSIS_MEMO.with(|memo| memo.borrow_mut().truncate(self.depth - 1));
    }
}

/// The per-local write index of `body` (`local_defs::LocalWriteIndex`), memoized for
/// the innermost [`FuncAnalysisScope`] whose function OWNS `body` — `None` for any
/// other body (a callee's, a derived clone's), which then takes the whole-body walk.
/// Keyed on the body's address, which the scope's borrow pins for exactly as long as
/// the frame lives.
pub(crate) fn local_write_index_for(
    body: &trust_types::VerifiableBody,
) -> Option<std::rc::Rc<crate::local_defs::LocalWriteIndex>> {
    let addr = std::ptr::from_ref(body) as usize;
    let (hit, owned) = FUNC_ANALYSIS_MEMO.with(|memo| {
        let memo = memo.borrow();
        match memo.iter().rev().find(|frame| frame.body_addr == addr) {
            Some(frame) => (frame.write_index.clone(), true),
            None => (None, false),
        }
    });
    if !owned {
        return None;
    }
    if let Some(hit) = hit {
        return Some(hit);
    }
    let built = std::rc::Rc::new(crate::local_defs::LocalWriteIndex::build(body));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.write_index = Some(std::rc::Rc::clone(&built));
        }
    });
    Some(built)
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SafetyTerminatorPresence {
    pub(crate) has_call: bool,
    pub(crate) has_tail_call: bool,
    pub(crate) has_atomic_call: bool,
    pub(crate) has_bare_dest_call: bool,
    pub(crate) has_iterator_next_call: bool,
    pub(crate) has_str_search_item_call: bool,
    pub(crate) has_position_call: bool,
    pub(crate) has_count_call: bool,
    pub(crate) has_str_find_call: bool,
    pub(crate) has_std_scalar_index_call: bool,
    pub(crate) has_vec_sole_resize_call: bool,
    pub(crate) has_switch_int: bool,
    pub(crate) has_assert: bool,
    pub(crate) has_bounds_check_assert: bool,
    pub(crate) has_overflow_assert: bool,
    pub(crate) has_overflow_neg_assert: bool,
    pub(crate) has_divrem_zero_assert: bool,
    pub(crate) has_opaque: bool,
    pub(crate) has_drop: bool,
    pub(crate) has_back_edge: bool,
}

impl SafetyTerminatorPresence {
    fn of(body: &trust_types::VerifiableBody) -> Self {
        let mut p = Self::default();
        for block in &body.blocks {
            if !p.has_back_edge {
                crate::loop_analysis::for_each_successor(&block.terminator, |succ| {
                    if succ.0 <= block.id.0 {
                        p.has_back_edge = true;
                    }
                });
            }
            match &block.terminator {
                Terminator::SwitchInt { .. } => {
                    p.has_switch_int = true;
                }
                Terminator::Assert { msg, .. } => {
                    p.has_assert = true;
                    match msg {
                        AssertMessage::BoundsCheck => {
                            p.has_bounds_check_assert = true;
                        }
                        AssertMessage::Overflow(_) => {
                            p.has_overflow_assert = true;
                        }
                        AssertMessage::OverflowNeg => {
                            p.has_overflow_neg_assert = true;
                        }
                        AssertMessage::DivisionByZero | AssertMessage::RemainderByZero => {
                            p.has_divrem_zero_assert = true;
                        }
                        _ => {}
                    }
                }
                Terminator::Opaque { .. } => {
                    p.has_opaque = true;
                }
                Terminator::Drop { .. } => {
                    p.has_drop = true;
                }
                Terminator::TailCall { atomic, .. } => {
                    p.has_tail_call = true;
                    if atomic.is_some() {
                        p.has_atomic_call = true;
                    }
                }
                term @ Terminator::Call { func: callee, args, dest, target, atomic, .. } => {
                    p.has_call = true;
                    if atomic.is_some() {
                        p.has_atomic_call = true;
                    }
                    if !p.has_vec_sole_resize_call
                        && !args.is_empty()
                        && (callee.starts_with("alloc::vec::") || callee.starts_with("std::vec::"))
                        && matches!(method_tail(callee), "remove" | "swap_remove" | "insert")
                    {
                        p.has_vec_sole_resize_call = true;
                    }
                    if !p.has_str_search_item_call
                        && str_offset::terminator_is_str_search_call(term)
                    {
                        p.has_str_search_item_call = true;
                    }
                    if dest.projections.is_empty() {
                        p.has_bare_dest_call = true;
                        match method_tail(callee) {
                            "next" => {
                                if !p.has_iterator_next_call
                                    && args.len() == 1
                                    && iterator_yield::callee_is_iterator_next(callee)
                                {
                                    p.has_iterator_next_call = true;
                                }
                            }
                            "position" | "rposition" => {
                                if !p.has_position_call
                                    && container_len::callee_is_slice_iter_position(callee)
                                {
                                    p.has_position_call = true;
                                }
                            }
                            "count" => {
                                if !p.has_count_call
                                    && target.is_some()
                                    && !trust_types::path_has_unauthenticated_crate_stamp(callee)
                                    && iterator_yield::vc_callee_is_std_iter_trait_method(
                                        callee, "Iterator", "count",
                                    )
                                {
                                    p.has_count_call = true;
                                }
                            }
                            "find" | "rfind" => {
                                if !p.has_str_find_call
                                    && iterator_yield::callee_is_std_str_find(callee)
                                {
                                    p.has_str_find_call = true;
                                }
                            }
                            "index" => {
                                if !p.has_std_scalar_index_call
                                    && args.len() >= 2
                                    && unwrap_panic::is_std_scalar_index_call(callee)
                                {
                                    p.has_std_scalar_index_call = true;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        p
    }
}

/// Single-pass terminator summary of `body`, memoized on the innermost
/// [`FuncAnalysisScope`] bound to `body`.
pub(crate) fn terminator_presence_for_body(
    body: &trust_types::VerifiableBody,
) -> SafetyTerminatorPresence {
    let addr = std::ptr::from_ref(body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.terminator_presence)
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = SafetyTerminatorPresence::of(body);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.terminator_presence = Some(built);
        }
    });
    built
}

/// Single-pass terminator summary of `func.body`, memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn terminator_presence_for(func: &VerifiableFunction) -> SafetyTerminatorPresence {
    terminator_presence_for_body(&func.body)
}

/// Cached [`SafetyTerminatorPresence`] when the innermost [`FuncAnalysisScope`] owns
/// `body` (building on first use), or `None` outside a matching scope.
pub(crate) fn cached_terminator_presence_for_body(
    body: &trust_types::VerifiableBody,
) -> Option<SafetyTerminatorPresence> {
    let addr = std::ptr::from_ref(body) as usize;
    let (hit, owned) = FUNC_ANALYSIS_MEMO.with(|memo| {
        let memo = memo.borrow();
        match memo.iter().rev().find(|frame| frame.body_addr == addr) {
            Some(frame) => (frame.terminator_presence, true),
            None => (None, false),
        }
    });
    if !owned {
        return None;
    }
    if let Some(hit) = hit {
        return Some(hit);
    }
    let built = SafetyTerminatorPresence::of(body);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.terminator_presence = Some(built);
        }
    });
    Some(built)
}

/// Distinct loop-header count ([`loop_bounds::count_back_edges`]), memoized on the
/// innermost [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn back_edge_count_for(func: &VerifiableFunction) -> usize {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.back_edge_count)
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = loop_bounds::count_back_edges_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.back_edge_count = Some(built);
        }
    });
    built
}

/// [`loop_bounds::has_unmodelable_write_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn has_unmodelable_write_for(func: &VerifiableFunction) -> bool {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.has_unmodelable_write)
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = loop_bounds::has_unmodelable_write_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.has_unmodelable_write = Some(built);
        }
    });
    built
}

/// [`trust_types::loop_nest::LoopNest::of`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn loop_nest_for(
    func: &VerifiableFunction,
) -> Option<std::rc::Rc<trust_types::loop_nest::LoopNest>> {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.loop_nest.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = trust_types::loop_nest::LoopNest::of(&func.body).map(std::rc::Rc::new);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.loop_nest = Some(built.clone());
        }
    });
    built
}

/// [`crate::enum_entry::has_enum_parameter_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn enum_entry_has_enum_parameter_for(func: &VerifiableFunction) -> bool {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.enum_entry_has_enum_param)
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = crate::enum_entry::has_enum_parameter_uncached(func);
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.body_addr == addr)
            {
                frame.enum_entry_has_enum_param = Some(built);
            }
        });
    }
    built
}

/// [`crate::enum_entry::pure_body_non_call_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn enum_entry_pure_body_non_call_for(func: &VerifiableFunction) -> Option<bool> {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.enum_entry_pure_body_non_call)
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = crate::enum_entry::pure_body_non_call_uncached(func);
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.body_addr == addr)
            {
                frame.enum_entry_pure_body_non_call = Some(built);
            }
        });
    }
    built
}

/// [`trust_types::VerifiableBody::contains_memory_image`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `body`.
pub(crate) fn body_contains_memory_image_for_body(body: &trust_types::VerifiableBody) -> bool {
    let addr = std::ptr::from_ref(body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.body_contains_memory_image)
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = body.contains_memory_image();
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.body_contains_memory_image = Some(built);
        }
    });
    built
}

/// [`trust_types::VerifiableBody::contains_memory_image`] for `func.body`, memoized on
/// the innermost [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn body_contains_memory_image_for(func: &VerifiableFunction) -> bool {
    body_contains_memory_image_for_body(&func.body)
}

/// [`crate::validate_function`] with `Ok(())` memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn validate_function_cached(
    func: &VerifiableFunction,
) -> Result<(), crate::VcgenError> {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.validate_function_ok)
    });
    if hit == Some(true) {
        #[cfg(test)]
        if differential_enabled() {
            assert!(
                crate::validate_function_uncached(func).is_ok(),
                "validate_function_cached disagrees with validate_function_uncached for {}",
                func.name
            );
        }
        return Ok(());
    }
    let res = crate::validate_function_uncached(func);
    let ok = res.is_ok();
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.validate_function_ok = Some(ok);
            if ok {
                frame.body_contains_memory_image = Some(false);
            }
        }
    });
    res
}

/// [`trust_types::VerifiableFunction::with_placed_opaque_values`] with the
/// `opaque_values_need_placement == false` fast path memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn with_placed_opaque_values_cached(
    func: &VerifiableFunction,
) -> std::borrow::Cow<'_, VerifiableFunction> {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.opaque_values_need_placement)
    });
    if hit == Some(false) {
        #[cfg(test)]
        if differential_enabled() {
            assert!(
                !func.body.opaque_values_need_placement(),
                "with_placed_opaque_values_cached disagrees with opaque_values_need_placement for {}",
                func.name
            );
        }
        return std::borrow::Cow::Borrowed(func);
    }
    let placed = func.with_placed_opaque_values();
    let needed = matches!(placed, std::borrow::Cow::Owned(_));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.opaque_values_need_placement = Some(needed);
        }
    });
    placed
}

/// [`trust_types::VerifiableFunction::with_tail_calls_expanded`] fast-pathed through
/// [`cached_terminator_presence_for_body`] when a [`FuncAnalysisScope`] is bound to
/// `func.body` and `!tp.has_tail_call`.
pub(crate) fn with_tail_calls_expanded_cached(
    func: &VerifiableFunction,
) -> std::borrow::Cow<'_, VerifiableFunction> {
    if let Some(tp) = cached_terminator_presence_for_body(&func.body)
        && !tp.has_tail_call
    {
        #[cfg(test)]
        if differential_enabled() {
            assert!(
                matches!(func.with_tail_calls_expanded(), std::borrow::Cow::Borrowed(_)),
                "with_tail_calls_expanded_cached disagrees with with_tail_calls_expanded for {}",
                func.name
            );
        }
        return std::borrow::Cow::Borrowed(func);
    }
    func.with_tail_calls_expanded()
}

pub(crate) fn body_has_wide_int_param_uncached(func: &VerifiableFunction) -> bool {
    if func.body.arg_count == 0 {
        return false;
    }
    let locals_slice = if func
        .body
        .locals
        .get(func.body.arg_count)
        .is_some_and(|d| d.index == func.body.arg_count)
        && func.body.locals[..=func.body.arg_count]
            .iter()
            .enumerate()
            .all(|(i, d)| d.index == i)
    {
        &func.body.locals[1..=func.body.arg_count]
    } else {
        &func.body.locals[..]
    };
    locals_slice.iter().any(|decl| {
        decl.index >= 1
            && decl.index <= func.body.arg_count
            && decl.name.is_some()
            && matches!(&decl.ty, Ty::Int { width, .. } if *width > 64 && *width <= 128)
    })
}

/// Whether `func` declares any named 128-bit integer parameter (`1..=arg_count`),
/// memoized on the innermost [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn body_has_wide_int_param_for(func: &VerifiableFunction) -> bool {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.has_wide_int_param)
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                hit,
                body_has_wide_int_param_uncached(func),
                "body_has_wide_int_param_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = body_has_wide_int_param_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.has_wide_int_param = Some(built);
        }
    });
    built
}

/// [`sep_engine::has_unsafe_patterns_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn has_sep_unsafe_patterns_for(func: &VerifiableFunction) -> bool {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.has_sep_unsafe_patterns)
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                hit,
                sep_engine::has_unsafe_patterns_uncached(func),
                "has_sep_unsafe_patterns_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = sep_engine::has_unsafe_patterns_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.has_sep_unsafe_patterns = Some(built);
        }
    });
    built
}

/// [`crate::func_has_no_join_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn func_has_no_join_for(func: &VerifiableFunction) -> bool {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.has_no_join)
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                hit,
                crate::func_has_no_join_uncached(func),
                "func_has_no_join_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = crate::func_has_no_join_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.has_no_join = Some(built);
        }
    });
    built
}

/// [`path_defs::func_has_pointer_laundering_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body` when `!crate::fn_memo::is_disabled()`.
pub(crate) fn func_has_pointer_laundering_for(func: &VerifiableFunction) -> bool {
    if crate::fn_memo::is_disabled() {
        return path_defs::func_has_pointer_laundering_uncached(func);
    }
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.has_pointer_laundering)
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                hit,
                path_defs::func_has_pointer_laundering_uncached(func),
                "func_has_pointer_laundering_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = path_defs::func_has_pointer_laundering_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.has_pointer_laundering = Some(built);
            if !built {
                frame.has_writable_pointer_laundering = Some(false);
            }
        }
    });
    built
}

/// [`path_defs::func_has_writable_pointer_laundering_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body` when `!crate::fn_memo::is_disabled()`.
pub(crate) fn func_has_writable_pointer_laundering_for(func: &VerifiableFunction) -> bool {
    if crate::fn_memo::is_disabled() {
        return path_defs::func_has_writable_pointer_laundering_uncached(func);
    }
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.has_writable_pointer_laundering)
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                hit,
                path_defs::func_has_writable_pointer_laundering_uncached(func),
                "func_has_writable_pointer_laundering_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = path_defs::func_has_writable_pointer_laundering_uncached(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.has_writable_pointer_laundering = Some(built);
        }
    });
    built
}

/// [`path_defs::index_locals_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body` when `!crate::fn_memo::is_disabled()`.
pub(crate) fn index_locals_for(func: &VerifiableFunction) -> Option<std::rc::Rc<Vec<bool>>> {
    if crate::fn_memo::is_disabled() {
        return None;
    }
    let addr = std::ptr::from_ref(&func.body) as usize;
    let (hit, owned) = FUNC_ANALYSIS_MEMO.with(|memo| {
        let memo = memo.borrow();
        match memo.iter().rev().find(|frame| frame.body_addr == addr) {
            Some(frame) => (frame.index_locals.clone(), true),
            None => (None, false),
        }
    });
    if !owned {
        return None;
    }
    if let Some(hit) = hit {
        return Some(hit);
    }
    let built = std::rc::Rc::new(path_defs::index_locals_uncached(func));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.index_locals = Some(std::rc::Rc::clone(&built));
        }
    });
    Some(built)
}

/// [`guards::block_predecessors_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body` when `!crate::fn_memo::is_disabled()`.
pub(crate) fn block_predecessors_rc_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<Vec<Vec<BlockId>>> {
    if crate::fn_memo::is_disabled() {
        return std::rc::Rc::new(guards::block_predecessors_uncached(func));
    }
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.block_predecessors.clone())
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                *hit,
                guards::block_predecessors_uncached(func),
                "block_predecessors_rc_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = std::rc::Rc::new(guards::block_predecessors_uncached(func));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.block_predecessors = Some(std::rc::Rc::clone(&built));
        }
    });
    built
}

/// [`guards::block_predecessor_edges_uncached`], memoized on the innermost
/// [`FuncAnalysisScope`] bound to `func.body` when `!crate::fn_memo::is_disabled()`.
pub(crate) fn block_predecessor_edges_rc_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<Vec<Vec<BlockId>>> {
    if crate::fn_memo::is_disabled() {
        return std::rc::Rc::new(guards::block_predecessor_edges_uncached(func));
    }
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.block_predecessor_edges.clone())
    });
    if let Some(hit) = hit {
        #[cfg(test)]
        if differential_enabled() {
            assert_eq!(
                *hit,
                guards::block_predecessor_edges_uncached(func),
                "block_predecessor_edges_rc_for disagrees with uncached scan for {}",
                func.name
            );
        }
        return hit;
    }
    let built = std::rc::Rc::new(guards::block_predecessor_edges_uncached(func));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.block_predecessor_edges = Some(std::rc::Rc::clone(&built));
        }
    });
    built
}

fn empty_block_fact_map() -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    thread_local! {
        static EMPTY: std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> =
            std::rc::Rc::new(FxHashMap::default());
    }
    EMPTY.with(std::rc::Rc::clone)
}

fn empty_unwrap_panic_vcs() -> std::rc::Rc<Vec<(BlockId, VerificationCondition)>> {
    thread_local! {
        static EMPTY: std::rc::Rc<Vec<(BlockId, VerificationCondition)>> =
            std::rc::Rc::new(Vec::new());
    }
    EMPTY.with(std::rc::Rc::clone)
}

fn empty_countdown_facts() -> std::rc::Rc<CountdownFacts> {
    thread_local! {
        static EMPTY: std::rc::Rc<CountdownFacts> =
            std::rc::Rc::new(CountdownFacts::default());
    }
    EMPTY.with(std::rc::Rc::clone)
}

/// [`crate::guards::unstable_locals`] for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function — `None` outside one (the caller
/// then scans, as it always did).
pub(crate) fn unstable_locals_for(func: &VerifiableFunction) -> Option<std::rc::Rc<Vec<bool>>> {
    let addr = std::ptr::from_ref(func) as usize;
    let (hit, owned) = FUNC_ANALYSIS_MEMO.with(|memo| {
        let memo = memo.borrow();
        match memo.iter().rev().find(|frame| frame.func_addr == addr) {
            Some(frame) => (frame.unstable_locals.clone(), true),
            None => (None, false),
        }
    });
    if !owned {
        return None;
    }
    if let Some(hit) = hit {
        return Some(hit);
    }
    let built = std::rc::Rc::new(crate::guards::unstable_locals(func));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.func_addr == addr)
        {
            frame.unstable_locals = Some(std::rc::Rc::clone(&built));
        }
    });
    Some(built)
}

/// The per-function dominating guard-fact index ([`dominating_facts::DominatingFacts`])
/// for `func`, memoized exactly like [`stmt_versions_for`]. Outside a matching scope it
/// is built per call: the same answer, at the cost of a build.
pub(crate) fn dominating_facts_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<dominating_facts::DominatingFacts> {
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.dominating_facts.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(dominating_facts::DominatingFacts::build(func));
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.func_addr == addr)
        {
            frame.dominating_facts = Some(std::rc::Rc::clone(&built));
        }
    });
    built
}

/// See [`dominating_facts::unmined_guard_bounds`].
pub(crate) fn unmined_guard_bounds(func: &VerifiableFunction) -> Vec<String> {
    dominating_facts::unmined_guard_bounds(func)
}

pub(super) fn stmt_versions_if_cached(
    func: &VerifiableFunction,
) -> Option<std::rc::Rc<StmtVersionCtx>> {
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.stmt_versions.clone())
    });
    if hit.is_some() {
        return hit;
    }
    crate::havoc_memo::cached_version_oracle(func)
}

/// The statement-version oracle for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function. Falls back to building it
/// (today's behaviour) when there is no matching scope.
pub(crate) fn stmt_versions_for(func: &VerifiableFunction) -> std::rc::Rc<StmtVersionCtx> {
    if let Some(hit) = stmt_versions_if_cached(func) {
        return hit;
    }
    let addr = std::ptr::from_ref(func) as usize;
    // Built OUTSIDE the `RefCell` borrow: the analysis is deep code and must be
    // free to re-enter this module without tripping a borrow panic.
    // NOT `Rc::new(..)`: on this base `StmtVersionCtx::build` ALREADY returns an
    // `Rc<Self>`, because it is itself memoized behind `havoc_memo::version_oracle`
    // (which is inert outside a `gen_work` scope). This memo is therefore a second
    // layer over that one for the statement-version half, and the sole novel layer
    // for the guard-map half below.
    let built = StmtVersionCtx::build(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.func_addr == addr)
        {
            frame.stmt_versions = Some(std::rc::Rc::clone(&built));
        }
    });
    built
}

/// Trust (W4/spine-derives-unreachable): the block population over which arm 1b
/// (`safety.rs`) mints TERMINATOR VCs — the keys of the path-guard map, i.e.
/// the blocks the guard walk reached from the entry. Exposed so a second
/// producer that must agree with this one on the `Unreachable` obligation
/// ENUMERATION (the trust-ir spine, via
/// `trust_types::terminator_obligations`) can take the same reachability gate
/// as an INPUT instead of re-deriving a walk that carries budgets and collapse
/// modes. This is analysis-output disclosure, not proof authority: a caller
/// holding this set can only mint obligations this producer also mints.
#[must_use]
pub fn terminator_vc_block_set(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    guard_map_for(func).keys().copied().collect()
}

/// The full path-guard analysis for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function unless an ambient
/// verification budget trip cut the walk short.
pub(crate) fn path_guard_analysis_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<safety::PathGuardAnalysis> {
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.path_guard_analysis.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(safety::v2_analyze_path_guards(func));
    if built.collapse != safety::PathGuardCollapse::BudgetTripped
        && !trust_types::verify_budget::exhausted_readonly()
    {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.path_guard_analysis = Some(std::rc::Rc::clone(&built));
                frame.guard_map = Some(std::rc::Rc::clone(&built.paths));
            }
        });
    }
    built
}

/// The path-guard map for `func`, memoized exactly like [`stmt_versions_for`].
pub(crate) fn guard_map_for(func: &VerifiableFunction) -> std::rc::Rc<PathGuardMap> {
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.guard_map.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    std::rc::Rc::clone(&path_guard_analysis_for(func).paths)
}

/// The cross-block path-definition map for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function and keyed by the active
/// [`callee_write_set`] scope id.
pub(crate) fn path_definition_map_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    let addr = std::ptr::from_ref(func) as usize;
    let scope_id = callee_write_set::current_scope_id();
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.path_definition_map.as_ref())
            .filter(|(cached_scope_id, _)| *cached_scope_id == scope_id)
            .map(|(_, map)| std::rc::Rc::clone(map))
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(path_defs::v2_build_path_definition_map(func));
    if !trust_types::verify_budget::exhausted_readonly() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.path_definition_map = Some((scope_id, std::rc::Rc::clone(&built)));
            }
        });
    }
    built
}

/// The per-block semantic guard map for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function and keyed by the active
/// summary-injection revision (`0` when `summaries` is `None`, empty, or matches no
/// returning call in `func`) and [`callee_write_set`] scope id.
pub(crate) fn semantic_guard_map_for(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    let addr = std::ptr::from_ref(func) as usize;
    let scope_id = callee_write_set::current_scope_id();
    let raw_rev = summaries
        .filter(|s| !s.is_empty())
        .map_or(0, crate::modular::SummaryDatabase::revision);
    let raw_key = (raw_rev, scope_id);
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| {
                frame
                    .semantic_guard_maps
                    .iter()
                    .find(|(k, _)| *k == raw_key)
                    .map(|(_, map)| std::rc::Rc::clone(map))
            })
    });
    if let Some(hit) = hit {
        return hit;
    }
    let summary_rev = if raw_rev != 0
        && terminator_presence_for(func).has_call
        && let Some(s) = summaries
        && func.body.blocks.iter().any(|b| {
            matches!(
                &b.terminator,
                Terminator::Call { func: call_name, target: Some(_), .. }
                    if s.get(call_name).is_some_and(summary_may_inject_postcondition)
            )
        })
    {
        raw_rev
    } else {
        0
    };
    let key = (summary_rev, scope_id);
    if key != raw_key {
        let fallback_hit = FUNC_ANALYSIS_MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            let frame = memo.iter_mut().rev().find(|frame| frame.func_addr == addr)?;
            let map = frame
                .semantic_guard_maps
                .iter()
                .find(|(k, _)| *k == key)
                .map(|(_, map)| std::rc::Rc::clone(map))?;
            if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
                frame.semantic_guard_maps.push((raw_key, std::rc::Rc::clone(&map)));
            }
            Some(map)
        });
        if let Some(hit) = fallback_hit {
            return hit;
        }
    }
    let built = std::rc::Rc::new(match summaries.filter(|_| summary_rev != 0) {
        Some(s) => semantic_guard::build_semantic_guard_map_with_summaries(func, s),
        None => semantic_guard::build_semantic_guard_map(func),
    });
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.semantic_guard_maps.push((key, std::rc::Rc::clone(&built)));
                if raw_key != key {
                    frame.semantic_guard_maps.push((raw_key, std::rc::Rc::clone(&built)));
                }
            }
        });
    }
    built
}

/// The function-wide invariant fact bundle for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function.
pub(crate) fn row_global_facts_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<RowGlobalFacts> {
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.row_global_facts.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(RowGlobalFacts::for_function(func));
    if !trust_types::verify_budget::exhausted_readonly() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.row_global_facts = Some(std::rc::Rc::clone(&built));
            }
        });
    }
    built
}

/// The range-iterator yield guard map for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function and keyed by the active
/// [`callee_write_set`] scope id.
pub(crate) fn range_yield_guards_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    if !terminator_presence_for(func).has_iterator_next_call
        && crate::adapter_yield_premises_for(&func.def_path).is_empty()
    {
        return empty_block_fact_map();
    }
    let addr = std::ptr::from_ref(func) as usize;
    let scope_id = callee_write_set::current_scope_id();
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.range_yield_guards.as_ref())
            .filter(|(cached_scope_id, _)| *cached_scope_id == scope_id)
            .map(|(_, map)| std::rc::Rc::clone(map))
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(build_range_yield_guard_map(func));
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.range_yield_guards = Some((scope_id, std::rc::Rc::clone(&built)));
            }
        });
    }
    built
}

/// The enumerate-iterator yield guard map for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function.
pub(crate) fn enumerate_yield_guards_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    if !terminator_presence_for(func).has_iterator_next_call {
        return empty_block_fact_map();
    }
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.enumerate_yield_guards.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(build_enumerate_yield_guard_map(func));
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.enumerate_yield_guards = Some(std::rc::Rc::clone(&built));
            }
        });
    }
    built
}

/// The slice-chunking yield guard map for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function.
pub(crate) fn slice_iter_yield_guards_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    if !terminator_presence_for(func).has_iterator_next_call
        && crate::adapter_yield_premises_for(&func.def_path).is_empty()
    {
        return empty_block_fact_map();
    }
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.slice_iter_yield_guards.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(build_slice_iter_yield_guard_map(func));
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.slice_iter_yield_guards = Some(std::rc::Rc::clone(&built));
            }
        });
    }
    built
}

/// The unwrap/abs panic-freedom VCs for `func` paired with their origin blocks,
/// memoized for the innermost [`FuncAnalysisScope`] bound to the same function
/// and keyed by the active [`callee_write_set`] scope id.
pub(crate) fn unwrap_panic_vcs_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<Vec<(BlockId, VerificationCondition)>> {
    if !terminator_presence_for(func).has_call {
        return empty_unwrap_panic_vcs();
    }
    let addr = std::ptr::from_ref(func) as usize;
    let scope_id = callee_write_set::current_scope_id();
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.unwrap_panic_vcs.as_ref())
            .filter(|(cached_scope_id, _)| *cached_scope_id == scope_id)
            .map(|(_, vcs)| std::rc::Rc::clone(vcs))
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(unwrap_panic::unwrap_panic_freedom_vcs_with_blocks(func));
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.unwrap_panic_vcs = Some((scope_id, std::rc::Rc::clone(&built)));
            }
        });
    }
    built
}

/// The downward induction variables for `func`, memoized for the innermost
/// [`FuncAnalysisScope`] bound to the same function.
pub(crate) fn downward_induction_vars_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<Vec<DownwardVar>> {
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.downward_vars.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = std::rc::Rc::new(induction::downward_induction_vars(func));
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.downward_vars = Some(std::rc::Rc::clone(&built));
            }
        });
    }
    built
}

/// The global and per-block countdown trip facts for `func`, memoized for the
/// innermost [`FuncAnalysisScope`] bound to the same function.
pub(crate) fn countdown_facts_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<CountdownFacts> {
    if !terminator_presence_for(func).has_switch_int {
        return empty_countdown_facts();
    }
    let addr = std::ptr::from_ref(func) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.countdown_facts.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let dvars = downward_induction_vars_for(func);
    let built = std::rc::Rc::new(induction::countdown_trip_analysis(func, Some(&dvars)));
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.countdown_facts = Some(std::rc::Rc::clone(&built));
            }
        });
    }
    built
}

/// [`crate::elem_sizes::elem_size_binding_digest`] for `func`, memoized on the
/// innermost [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn elem_size_binding_digest_for(func: &VerifiableFunction) -> Option<String> {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.elem_size_binding_digest.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = crate::elem_sizes::elem_size_binding_digest(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.elem_size_binding_digest = Some(built.clone());
        }
    });
    built
}

/// [`crate::primitive_decimal_strings::body_digest`] for `func`, memoized on the
/// innermost [`FuncAnalysisScope`] bound to `func.body`.
pub(crate) fn primitive_decimal_body_digest_for(func: &VerifiableFunction) -> Option<String> {
    let addr = std::ptr::from_ref(&func.body) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.body_addr == addr)
            .and_then(|frame| frame.primitive_decimal_body_digest.clone())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let built = crate::primitive_decimal_strings::body_digest(func);
    FUNC_ANALYSIS_MEMO.with(|memo| {
        if let Some(frame) = memo
            .borrow_mut()
            .iter_mut()
            .rev()
            .find(|frame| frame.body_addr == addr)
        {
            frame.primitive_decimal_body_digest = Some(built.clone());
        }
    });
    built
}

/// The per-block primitive decimal formatting length bounds for `func`, memoized
/// for the innermost [`FuncAnalysisScope`] bound to the same function and keyed by
/// the active `PrimitiveDecimalStringTable` address.
pub(crate) fn primitive_decimal_len_guards_for(
    func: &VerifiableFunction,
) -> std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>> {
    if !terminator_presence_for(func).has_call {
        return empty_block_fact_map();
    }
    let Some(table) = crate::inherited_primitive_decimal_strings(&func.def_path) else {
        return empty_block_fact_map();
    };
    let addr = std::ptr::from_ref(func) as usize;
    let table_addr = std::sync::Arc::as_ptr(&table) as usize;
    let hit = FUNC_ANALYSIS_MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .rev()
            .find(|frame| frame.func_addr == addr)
            .and_then(|frame| frame.primitive_decimal_len_guards.as_ref())
            .filter(|(cached_table_addr, _)| *cached_table_addr == table_addr)
            .map(|(_, map)| std::rc::Rc::clone(map))
    });
    if let Some(hit) = hit {
        return hit;
    }
    if !table.matches_body(func) {
        return empty_block_fact_map();
    }
    let built = std::rc::Rc::new(
        primitive_decimal_len::build_primitive_decimal_len_guard_map_with_table(func, &table),
    );
    if !trust_types::verify_budget::exhausted_readonly() && !crate::gen_work_tripped() {
        FUNC_ANALYSIS_MEMO.with(|memo| {
            if let Some(frame) = memo
                .borrow_mut()
                .iter_mut()
                .rev()
                .find(|frame| frame.func_addr == addr)
            {
                frame.primitive_decimal_len_guards =
                    Some((table_addr, std::rc::Rc::clone(&built)));
            }
        });
    }
    built
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
// Len-witness return grounding (b62): `_0__value.<i>.<j>…__len` model terms
// ======================================================================
//
// The F5 matches!-guard lowering emits `#[ensures]` predicates over the
// payload-component LENGTH terms the spec parser mints for
// `result.unwrap().<i>.<j>.len()` — `_0__value.<i>.<j>__len` (`Sort::Int`) — and
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
//    parseable `_0__value.<path>__len` names whose EVERY occurrence across EVERY
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
//    `Eq(_0__value.<a>__len, _0__value.<b>__len)` — derived ONLY from the MIR
//    construction chain, never from the contract — plus, when the equality
//    was established by a length GUARD, the individual witness pins
//    `Eq(_0__value.<a>__len, <len-call dest>)`. Two derivations:
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
/// A parsed `_0__value.<i>.<j>…__len` spec-model name: the exact var name the
/// parser mints plus the positional payload-component field path. Only paths
/// STRICTLY under the payload parse (`_0__value__len` — a bare-payload length —
/// stays fail-closed, matching the compiler lowering's strict-projection gate).
#[derive(Clone, Debug, PartialEq, Eq)]
struct LenModelVar {
    name: String,
    path: Vec<usize>,
}

// ======================================================================
// Ordering/sign-witness return grounding (b62 F4): `_0__value.__trust_ok_<i>`
// pair terms + the `_0__value__sign` term (the sign half RETIRED and the pair half
// GATED on 2026-10-05, ORD-WITNESS-CONSISTENT-1: see the amendment at the end of
// this banner)
// ======================================================================
//
// The F4 `matches!`-guard lowering emits `#[ensures]` predicates over the
// payload-pair terms the spec parser mints for `Ok((d, c))` tuple binds
// (`_0__value.__trust_ok_0/1`) and over the payload sign term it mints for
// `result.unwrap().is_positive()` (`_0__value__sign`) — the ny-cert selfcheck /
// branch shapes, whose payloads are `Rat`: a Copy u32 ARENA HANDLE whose
// ordering lives behind `<Rat as PartialOrd>` through a thread-local arena.
// An Int reading of the handle bits is MEANINGLESS, so this lane NEVER
// re-encodes the handle ints. Instead it grounds the contract atoms on the
// BOOL results of the body's OWN comparison calls — the same functions the
// runtime-checked `ensures` fallback would execute on the same values:
//
//  * WHICH terms (the coverage gates, `ordering_pair_coverage` /
//    `sign_var_covered`): a pair of `_0__value.__trust_ok_<i>` names is
//    covered only when EVERY occurrence of BOTH names across EVERY declared
//    postcondition sits inside an ordering atom `Lt/Le/Gt/Ge/Eq(a, b)`
//    BETWEEN the two names (no constants, no arithmetic); `_0__value__sign` is
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
//
// AMENDED 2026-10-05 (ORD-WITNESS-CONSISTENT-1) — THE ASSUMPTION ABOVE WAS NOT
// CHECKED, AND IT IS FALSE OF SAFE RUST. Nothing enforces the `PartialOrd`
// laws or a sign trichotomy: an impl whose `le` and `gt` both answer `true`
// is valid Rust, and `pick(a, b) { if !(a <= b) { return Err } Ok((a, b)) }`
// had `!matches!(r, Ok((d, c)) if d > c)` reported PROVED under certify (three
// rows, ay-in-process) on the stage 1 of `76a6ea45b2`, while
// `pick(Odd(1), Odd(2))` returned `Ok` with `d > c` true at run time. Two
// changes, both refusals:
//  * the PAIR lane credits a guard only on a payload type the COMPILER found
//    order-consistent (`crate::is_order_consistent_adt`, filled by
//    `trust_verify::order_consistent_adts`: builtin-derived `PartialEq`,
//    `PartialOrd` and any `Ord`, over integer/`bool`/`char` fields or such
//    types, nothing generic). A builtin derive cannot be written by the user,
//    and its operators are the core defaults over one pure `partial_cmp` that
//    is total on those fields, so the {Lt, Eq, Gt} reading is exact. MEASURED
//    on the same stage 1: the comparison of such a type never reaches this
//    lane today, because the extractor already rewrites a provably-total
//    derived comparison to `TRUST_TOTAL_CLONE_SENTINEL`
//    (`apply_total_partial_ord_sentinel`); the gate is what a future identity-
//    carrying spelling of that call must pass, not a live credit;
//  * the SIGN lane is retired (`_0__value__sign` stays ungrounded).
// The capability cost is ny-cert's four `Rat` contracts (a hand-written `Ord`
// over an arena): recorded in docs/DECISION_QUEUE.md (ORD-WITNESS-CONSISTENT-1).
/// A parsed `_0__value.__trust_ok_<i>` spec-model name: the tuple-bind payload
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
/// component pair. Carries the component type name (the callee allowlist key)
/// and the stability-checked candidate places. (The payload-SIGN target was
/// retired by ORD-WITNESS-CONSISTENT-1; see `witness_grounding`.)
enum OrdWitnessTarget<'a> {
    Pair { ty_name: &'a str, cand_a: &'a [Place], cand_b: &'a [Place] },
}

/// One whole-local def site: a statement rvalue or a call terminator.
enum F4LocalDef<'a> {
    Rv(&'a Rvalue),
    Call { callee: &'a str, args: &'a [Operand] },
}

/// One credited F4 item: a `__trust_ok` pair. (The payload sign term is no
/// longer credited: ORD-WITNESS-CONSISTENT-1.)
#[derive(Clone, Debug, PartialEq, Eq)]
enum OrdWitnessItem {
    Pair(OkPairModelVar, OkPairModelVar),
}

impl OrdWitnessItem {
    fn model_names(&self) -> Vec<String> {
        let Self::Pair(a, b) = self;
        vec![a.name.clone(), b.name.clone()]
    }
}

// Every type, const, `impl`, textually-scoped macro and import the VC families
// share stays here: the families are descendant modules, so they keep access to
// private fields, private consts and this macro without any visibility change.
// Each family is re-exported flat, so `generate::<name>` resolves exactly as it
// did when this module was a single file.
mod call_facts;
// Trust (std-intrinsics lane): EXACT bitvector semantics for the body-less
// rustc arithmetic/bit intrinsics, replacing the boolean "cannot panic" model
// with a definition. Its own module because it is the only place in this crate
// that ADDS facts to the hypothesis set — see its header for the soundness
// discipline that follows from that.
// Trust (D2 tier 1, 2026-09-24): the ADAPTER_YIELD modeled fact, closure side.
mod adapter_yield;
mod alloc_bounds;
mod alloc_len;
mod alloc_vcs;
// Trust (2026-10-15, TRUST-KI-1015-1): the lengths of the two halves core's
// `[T]::as_chunks::<N>` family returns, as post-return path definitions of the call.
mod as_chunks_len;
mod assert_refutation;
mod block_defs;
mod bmc_reduction;
mod callee_summaries;
pub(crate) mod callee_write_set;
mod callsite;
mod callsite_replay;
mod checked_vcs;
pub(crate) mod collection_range;
mod container_len;
mod contract_vcs;
mod discharge;
mod entry;
mod entry_hypothesis;
mod ffi_buffer_extent;
mod float_overflow;
mod float_range;
mod havoc_decline;
// `build_int_abs_facts`' checked-argument spelling needs the op's overflow assert
// (WRAPPING-SUB-AND-INTERVAL-NEG-1 sibling).
#[cfg(test)]
mod int_abs_fact_tests;
mod primitive_decimal_len;
// Trust (2026-10-16, S3): the generic refutation scope asks the same question.
pub(crate) use havoc_decline::{HAVOC_DECLINE_KIND, PayloadSources, UnmodelledValues};
mod constructor_return;
mod induction;
// Trust (D5-B): kernel-checked body-inferred return equalities (candidate side).
mod inferred_return;
mod int_conversion;
mod intrinsic_semantics;
mod ite;
mod iterator_yield;
mod loop_bounds;
mod source_entry;
// Trust (2026-09-25, std-numeric-family): the std numeric methods that panic on a
// caller-supplied argument value (clamp bounds, ilog/isqrt domains, radix,
// next_power_of_two/next_multiple_of, Duration/Instant arithmetic).
mod numeric_panic;
// The name-level half of `numeric_panic`, which the compiler consults for a
// sysroot fn item handed over as a type argument.
#[cfg(test)]
mod numeric_panic_tests;
// Trust (T3 C05): the production generation's overflow-check origins, the
// proven-overflow-check elision seam's join table.
mod overflow_origins;
// Trust (T3 L4, C08): block-def recipes, and the block-def rows that join a context as
// Spine rows.
mod recipes;
// T3 L4 (C08): recipes, their keys and the sink's Spine rows.
#[cfg(test)]
mod recipes_tests;
// Trust (T3 L4, C08s): the production generation's row sink, which runs the per-row
// passes as each row joins and interns the rows into the caller's context.
mod row_sink;
// T3 L4 (C08s): the sink's per-row passes against the whole-list passes they replace.
#[cfg(test)]
mod row_sink_tests;
// Trust (W32-PRIMINT-PIN-1, 2026-10-06): `numeric_panic`'s rows at a pointer-sized
// (`usize`/`isize`) owner on 16-, 32- and 64-bit carriers, and their fail-closed
// refusal when the width is unresolved.
#[cfg(test)]
mod numeric_panic_ptr_width_tests;
mod overflow_vc;
// Trust (2026-10-01): dominating `var CMP const` guard facts, built once per function.
mod dominating_facts;
// Trust (2026-10-07, PATH-GUARD-VALUE-1): a path guard is spelled by the SSA value its
// subject holds at the guard, not by the subject's reaching-definition set.
mod guard_value_spelling;
mod panic_calls;
mod path_defs;
// TINV-21: the lemma-root pointer backstop (`type_invariant::obligations::lemma_param_root`).
pub(crate) use path_defs::local_pointee_may_escape;
pub use path_defs::noalias_premise_would_fire;
mod per_path_refute;
mod range_bound_use;
// Trust (2026-10-15, TRUST-KI-1015-1): the result length of a std range index and of
// `[T]::split_at`, as post-return path definitions of the call.
mod range_index_len;
// The statement-version oracle's indexes (see `StmtVersionCtx`).
mod block_writes;
pub(crate) mod cfg_index;
pub(crate) mod rebind_index;
mod version_ssa;
// The retired dense-map oracle, kept as the differential.
#[cfg(any(test, feature = "version-oracle-differential"))]
mod legacy_version_oracle;
/// Whether the test-time cross-checks (the retired-oracle differential and the
/// scan-vs-index assertions of the kill and place-name tables) run on this thread.
/// Off inside `legacy_version_oracle::without_differential`, which the scaling and
/// measurement harnesses use so they time the production code path.
#[cfg(any(test, feature = "version-oracle-differential"))]
pub(crate) use legacy_version_oracle::differential_enabled;
// Trust (TRUST-10): field-read return summaries (`len`/`is_empty` getters).
mod return_field_summary;
mod safety;
mod semantic_guard;
mod slice_conversion;
mod slice_len_licence;
mod str_offset;
pub(crate) mod tinv_rows;
mod type_ranges;
// TINV step 10.2: the tagged use-site facts of a published type invariant (not yet
// conjoined; step 10.3 wires them into the safety walk).
pub(crate) mod type_invariant_facts;
mod unsupported;
mod unwrap_panic;
mod value_facts;
// Trust (VEC-INSERT, 2026-09-25): the pre-mutation region of a `Vec` base, and the
// index precondition of `Vec::{remove, swap_remove, insert}` over it.
mod vec_region;
// Trust (VEC-LEN-LOOP-1, 2026-10-07): the length of a std `Vec` nothing between its
// read and an index can change, tied at each std index call (loop-head precision).
mod vec_len_invariant;
mod witness_grounding;
// Trust (coroutine resume-state contract): the refutation-lane prover for the
// compiler-inserted `ResumedAfter*` executor-protocol sentinels. Deliberately a
// module of its own — see its header.
pub(crate) mod coroutine_sentinel;

pub(crate) use adapter_yield::{AdapterPremiseFamily, extend_with_adapter_premise_facts};
pub use adapter_yield::{AdapterYieldFact, ClosureAdapterPremise};
pub(crate) use alloc_bounds::*;
pub(crate) use alloc_len::*;
pub(crate) use alloc_vcs::*;
pub use assert_refutation::*;
pub(crate) use block_defs::*;
pub use bmc_reduction::*;
// LEN-KEY-1: std's inherent `len` by its DefId key, for `guards`' `_len == coll_len` tie.
pub(crate) use call_facts::body_mentions_opaque_scalar;
pub(crate) use call_facts::callee_key_is_std_inherent_len;
// The one call-fact reader `crate::const_expr` needs outside `generate`.
pub(crate) use call_facts::lossless_int_conversion_arg;
// TINV step 8 (`type_invariant::candidate`): its constant pool reads `clamp`/`min`/`max`
// constants only through the NAME-ANCHOR-2 gate, and literal operands through the same
// reader the loop-bound lane uses.
pub(crate) use call_facts::primitive_int_ord_method;
use call_facts::*;
pub use callee_summaries::*;
pub use callsite::*;
pub use callsite_replay::*;
pub(crate) use checked_vcs::*;
pub use constructor_return::{
    ConstructorReturnCandidate, ConstructorReturnSummary, infer_constructor_return_candidate,
    intern_constructor_return_rows,
};
pub(crate) use container_len::*;
use contract_vcs::*;
pub use discharge::*;
pub use entry::*;
use entry_hypothesis::*;
use float_overflow::*;
pub use float_range::*;
use induction::*;
pub(crate) use inferred_return::EntryBindings;
pub use inferred_return::{
    INFERRED_RETURN_MAX_NODES, InferredReturn, InferredReturnCall, infer_return_candidate,
    infer_return_candidate_rows, infer_return_candidate_with_calls_rows,
    inferred_enum_return_check_vcs, inferred_return_check_vcs,
    return_dependency_body_within_budget,
};
use int_conversion::*;
use intrinsic_semantics::*;
use ite::*;
pub(crate) use iterator_yield::inclusive_range_yield_set_only_values;
use iterator_yield::*;
pub(crate) use loop_bounds::operand_const_int;
use loop_bounds::*;
use overflow_origins::{
    EmittedRow, KeepOrigins, PendingOriginRow, PendingOrigins, RowInventory, RowOrigins,
};
pub use overflow_origins::{OriginRow, OriginSite, OverflowOrigins};
pub(crate) use overflow_vc::*;
pub(crate) use panic_calls::*;
pub(crate) use path_defs::*;
pub use per_path_refute::{
    generate_per_path_assert_refutation_vcs, generate_per_path_assert_refutation_vcs_with_context,
};
pub use recipes::{RecipeCounts, SpineDecline, recipe_counts};
pub use return_field_summary::*;
use row_sink::{RowSink, SepFacts, SinkOutput, checked_ids, work_budget_refusal};
// Nothing in `safety` is public since T3 C05 deleted `overflow_vc_block_origins`.
use safety::*;
pub(crate) use semantic_guard::*;
use slice_conversion::*;
use slice_len_licence::*;
pub(crate) use str_offset::*;
pub(crate) use type_ranges::*;
pub(crate) use unsupported::*;
// Trust (2026-10-06, ABS-NAME-1): the emitter's own signed-`abs` recognizer, for
// trust-clean's negation-subject gate (re-exported at the crate root).
pub use unwrap_panic::is_signed_abs_call;
pub(crate) use unwrap_panic::*;
pub(crate) use value_facts::*;
pub(crate) use vec_region::*;
pub use vec_region::{vec_mutator_charge_rows, vec_mutator_charged_blocks};
use witness_grounding::*;

#[cfg(test)]
mod assert_refutation_coverage_tests;
#[cfg(test)]
mod coroutine_sentinel_tests;
// verifier-perf (2026-09-16): `StmtVersionCtx`'s root index and token memo
// answer exactly as the full scan does.
#[cfg(test)]
mod version_oracle_index_tests;
#[cfg(test)]
mod version_ssa_families;
// The dominator index against the textbook definitions (a module the SSA oracle's
// first commit wrote but never declared, so it had never run).
#[cfg(test)]
mod cfg_index_tests;
#[cfg(test)]
mod dominating_facts_scaling_tests;
#[cfg(test)]
mod version_ssa_parity_tests;
#[cfg(test)]
mod version_ssa_random_tests;
#[cfg(test)]
mod version_ssa_scaling_tests;
// T3 L4 (C06): the per-function VC context's spine against this crate's block-def rule.
#[cfg(test)]
mod vc_context_spine_tests;
// D15: the joined-token spelling's partition identity, collision fallback and linear
// bytes.
#[cfg(test)]
mod version_ssa_spelling_tests;
// Trust (coroutine resume-state contract): the same lane against the REAL
// compiler-extracted resume body of the falsification fixture, not a synthetic
// one. See the file header for why that distinction is load-bearing.
#[cfg(test)]
mod clamp_upper_bound_tests;
#[cfg(test)]
mod coroutine_sentinel_real_mir_tests;
// Trust (false-obligation lane): safe vs. unsafe intrinsics — the missing-SAFETY
// demand AND (since the 2026-08-28 split) the SEP-ALLOC ROW SET, pinned in both
// directions. `has_intrinsic_unsafe_surface` no longer gates the sep engine; the
// row-set tests here assert on `generate_vcs` output rather than on that
// predicate, because the predicate-only form was blind — it passed both with the
// row set fixed and with the defect re-introduced. Lives here rather than in
// `unsafe_verify::tests` because the gate it must pin is `pub(super)` to this
// module.
#[cfg(test)]
mod safe_intrinsic_lint_tests;
// Trust (false-obligation lane): the compiler's modular-arithmetic certificate —
// `intrinsics::wrapping_add` vs. a plain `+` in the identical extracted shape.
#[cfg(test)]
mod modular_arith_certificate_tests;
// Trust (width-soundness): overflow rows for widthless-constant operands must be
// built at the VALIDATED destination width, never a fabricated i64 — the
// `_0: i8 = Add(100, 100)` false-PROVE regression.
#[cfg(test)]
mod overflow_width_tests;
// Trust (std-intrinsics lane): the EXHAUSTIVE width-8 differential against the
// real Rust operations, plus the recognizer-strictness and vacuity checks. This
// is the module that makes the added facts auditable — see its header.
#[cfg(test)]
mod call_arg_fact_token_tests;
#[cfg(test)]
mod intrinsic_semantics_tests;
#[cfg(test)]
mod recursion_decreases_production_variant_tests;
#[cfg(test)]
mod summary_callsite_tests;
// census-vcgen-hang (2026-10-02): a batch of owned-`Vec` index row replays under one
// `RowReplayScope` returns the rows unscoped replays return and builds the oracle once.
#[cfg(test)]
mod row_replay_scope_tests;
// R1 harvest (2026-10-19): the call-site producers' `EntryScope` builds their
// whole-body analyses independent of the call sites and changes no row.
#[cfg(test)]
mod entry_scope_tests;
// The terminator-fact channel's TIME AXIS: `version_terminator_dest_fact` retimes
// every variable whose base name is the subject's, so an ARGUMENT that renders to
// that name would be read at the post-call token — `result > n` injected as
// `n#s0_t > n#s0_t`, and the sibling value producers' `dest == f(arg)` as the
// fixpoint `d == f(d)`. Only the guarded branch's ANTECEDENT refused it until
// 2026-08-31; `terminator_args_read_name` now refuses the whole batch, with the
// same conjunct on the ADMIT gate. Latent when found (0 of 105,703 corpus call
// sites present the shape), zero measured cost — see the file header.
#[cfg(test)]
mod summary_dest_retiming_tests;
// Callsite L0 replay (refutation-only): the substitution filter's
// caller-scoped-only invariant and the composed-candidate producer's
// fail-closed gates (sentinels, residual callee locals, σ-fresh vars,
// missing extracted body, self-recursion).
#[cfg(test)]
mod callsite_replay_tests;
// PANIC-SKIP-ANCHOR-1 (2026-10-05): a call's arguments leave the fail-closed
// `UnsupportedMir` collector only at a stamped sysroot panic entry with no
// continuation, never because the callee's rendering looks like one.
#[cfg(test)]
mod panic_skip_anchor_tests;
// The FAIL-CLOSED half of the unfolded-constant-bound fold: the refusals no
// compiled fixture can carry (`1i64 << 64` is a compile error, `-(1i64 << 63)`
// always panics), pinned on the resolver's own inputs.
#[cfg(test)]
mod const_expr_bound_tests;
#[cfg(test)]
mod contract_field_bound_tests;
#[cfg(test)]
mod v2_path_guard_tests;
// The two path-guard COLLAPSE modes and the anti-vacuity guard on the fixtures
// that exercise them.
#[cfg(test)]
mod path_guard_collapse_tests;
// `FuncAnalysisScope` equivalence/identity-binding, and the ambient-budget polls:
// the memoization must be verdict-neutral, and a budget trip must only ever
// REMOVE hypotheses.
#[cfg(test)]
mod func_analysis_memo_tests;
// A `bool` contract clause could never equal the re-parse of its own source
// text, because `parse_spec_expr` has no type environment and defaults every
// leaf to `Sort::Int`. That minted a duplicate ill-sorted postcondition VC and
// denied the clause its `source_contract_index`.
#[cfg(test)]
mod clause_sort_match_tests;
// A postcondition over a `&mut`-parameter place is versioned at the RETURN
// block, where a multi-predecessor exit gives it the reaching-def JOIN token
// (`self*.0.0#e_s1_0`) that no pin or block def ever spells. The join name was
// FREE, so an early-return body's clause AND its exact negation were both
// "refuted" — identical verdicts for P and !P.
#[cfg(test)]
mod bounds_const_index_tests;
// The rvalue lane's native-`BoundsCheck` suppression is EXACT-BINDING (cond
// resolved in the assert's own block, index identity, length correspondence,
// sole-entry success edge), never bare target identity — the same discipline
// the Overflow/OverflowNeg and Div/Rem lanes carry. These tests pin both
// directions: the unrelated row emits, the exactly-bound row stays suppressed.
#[cfg(test)]
mod bounds_exact_binding_tests;
// The load/store index lane's same-block slice-length ties at a row's use point
// (`v2_live_slice_len_ties_at_point`): live ties kept, stale ones never reach the row.
#[cfg(test)]
mod early_return_postcondition_tests;
#[cfg(test)]
mod slice_len_ties_at_point_tests;
// Two-language battery blocker a7: a Return-block predecessor reached by SEVERAL
// guard paths was emitted as ONE `Or`-shaped row, and that row — alone among the
// rows of the same clause — got no trust-mc PDR receipt, so the source-clause
// catalog refused a clause whose every body row read `Proved`. One row per
// enumerated path distributes the path-guard conjunct (and no more than that —
// the shared tail is spine-sensitive, so a per-path row can be strictly more
// PROVABLE than the merged row's corresponding disjunct, never more credulous;
// see `contract_vcs::generate_v2_contract_vcs_impl`). These tests pin the
// flatness, the path coverage, the one-path-false twin, the dropped-`requires`
// carve-out and the cap; the SATISFIABILITY canary for a clause false on exactly
// one of three paths lives in `early_return_postcondition_tests`, which owns the
// exhaustive oracle.
#[cfg(test)]
mod per_path_postcondition_tests;
// The RETURN-SLOT twin of the join-token defect above (probe f53): an
// Eq-shaped `ensures result == …` over an `&&`-diamond body was negated at the
// Return block's MERGED `_0` token while the pin carried the predecessor's
// single token. These regressions require the clause to read that final value
// without using its own equality, or any historical value, as a binding pin.
#[cfg(test)]
mod return_slot_join_version_tests;
// P4 (hunter Finding 1, 2026-09-30): the transitive return pin pins only the
// definition of `_L` that REACHES `_0 = copy _L`.
#[cfg(test)]
mod transitive_return_pin_reach_tests;
// The AGGREGATE-FIELD twin of the two defects above, and the one still OPEN: a
// clause over a FIELD of the returned struct, whose source local is written in
// two select arms. The clause is negated at `_0.0#s3_0` while the field pin
// carries `_0.0`, and the merge pin ties the former to the reaching-def join
// `c#s1_0_s2_0` that no arm defines -- `is_return_slot_name` matches neither
// `_0.0` nor `_0.0#tok`, and `return_edge_merge_pins` covers only
// &mut-parameter places. Its one test is #[ignore]d with the diagnosis.
#[cfg(test)]
mod aggregate_field_join_version_tests;
#[cfg(test)]
mod float_range_tests;
#[cfg(test)]
mod return_pin_dedup_tests;
#[cfg(test)]
mod return_projection_pin_tests;
#[cfg(test)]
mod round14_stability_tests;
#[cfg(test)]
mod trait_object_unsize_cast_tests;
// PtrMetadata over a slice/str/array fat pointer is its length, which
// `slice_len_formula` models deterministically — so `collect_rvalue_unsupported`
// must NOT emit a spurious `Rvalue::UnaryOp(PtrMetadata)` UnsupportedMir
// obligation for those operands (that wedged the ubiquitous
// `if i < s.len() { s[i] }` idiom). For genuinely unmodelable metadata
// (raw-pointer provenance, `dyn` vtable) it must still fail closed. These tests
// pin both halves of that contract on the exact function the fix lives in. Plain
// `#[cfg(test)]` because `unsupported_mir_vcs` is part of the canonical pipeline.
#[cfg(test)]
mod len_witness_grounding_tests;
// A flattened nested-loop index bound is global, so its checked-result
// consumer must have one stable bare-name value. These tests pin the merged
// local, reassigned-parameter, and mutable-alias false-proof boundaries.
#[cfg(test)]
mod loop_bounds_tests;
// The conduit allow-list under which the `for`-loop iterator tracers readmit the
// alias channel (`iterator_yield::iterator_origin_def`), pinned one refusal at a time.
#[cfg(test)]
mod iterator_origin_gate_tests;
#[cfg(test)]
mod machine_faithful_contract_lane_tests;
#[cfg(test)]
mod ordering_witness_grounding_tests;
#[cfg(test)]
mod ptr_metadata_tests;
#[cfg(test)]
mod result_return_grounding_tests;
#[cfg(test)]
mod return_walk_preservation_tests;
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
// Trust (2026-08-20): the bare-`Rvalue::BinaryOp` wrapping value model — the
// -O / overflow-checks-off form — pinned encoding-identical to the
// marker-authenticated wrapping-call model, plus the false-prove control that
// the old unbounded `dest == a + b` def failed. See the module header.
#[cfg(test)]
mod wrapping_binop_defs_tests;
// Trust (2026-10-05, NEG-WRAP-OFF-1): the bare-`Rvalue::UnaryOp(Neg)` sibling — the
// wrap-exact block def, the interval and value-set clamps, and the solver-backed
// false-prove control on the checks-off `abs_like` body. See the module header.
#[cfg(test)]
mod bare_neg_wrap_tests;
// The bounded-collect grant's two authenticators, measured on real
// `-Ztrust-dump=mir` bundles rather than hand-built doubles:
//   * `trusted_root_spoof_iter_producer_tests` — the CALLEE-path half, on the
//     `--crate-name alloc` impersonation the extractor had already stamped;
//   * `authenticated_std_iter_chain_tests` — the crate-free adaptor forgery that
//     needs no impersonation at all, plus the real production chains whose sound
//     bounded-source recovery must survive both authenticators;
//   * `no_std_sysroot_impersonation_tests` — the `#![no_std]` graph in which the
//     impersonator is UNIQUE, so the duplicate-crate-name rule never stamped it
//     and both authenticators were handed a bare `std::` root. That is the case
//     the producer-side IDENTITY rule exists for.
#[cfg(test)]
mod authenticated_std_iter_chain_tests;
#[cfg(test)]
mod bounded_source_value_tests;
#[cfg(test)]
mod capture_avoiding_tests;
#[cfg(test)]
mod discriminant_cse_license_tests;
#[cfg(test)]
mod no_std_sysroot_impersonation_tests;
#[cfg(test)]
mod ord_method_tests;
// NAME-ANCHOR-2: an `Ord::min`/`max`/`clamp` fact needs a primitive integer
// `Self`, not only std's trait path. Pinned on real extracted MIR.
#[cfg(test)]
mod ord_self_type_tests;
#[cfg(test)]
mod refute3_rangefrom_tests;
#[cfg(test)]
mod slot_write_channel_tests;
#[cfg(test)]
mod trusted_root_spoof_iter_producer_tests;
// ======================================================================
// Integer try_from/try_into + unwrap_or result modeling (tests)
// ======================================================================
#[cfg(test)]
mod int_wrapping_neg_tests;
// ======================================================================
// Clean-origin WrappingBinOp summary: the encoding pin against the
// extractor's own wrapping model (tests)
// ======================================================================
#[cfg(test)]
mod clean_origin_wrapping_summary_tests;
// ======================================================================
// Clean-origin definitional grounding in the assert-refutation lane:
// identity-keyed call-result definitions, both verdict directions (tests)
// ======================================================================
#[cfg(test)]
mod clean_origin_refute_grounding_tests;
// ======================================================================
// Postcondition composition slice 2: a preconditioned callee's `ensures`
// rides at a call site UNDER its own `requires` (tests)
// ======================================================================
#[cfg(test)]
mod guarded_postcondition_tests;
// ======================================================================
// Const-return summaries: lower/upper bound + exact const set (tests)
// ======================================================================
#[cfg(test)]
mod int_try_from_unwrap_or_tests;
#[cfg(test)]
mod return_const_summary_tests;
// Trust (SUMMARY-NAME-COLLIDE-1): a body-derived summary key two bodies share
// summarizes nothing, in any lane.
#[cfg(test)]
mod alloc_len_adt_tests;
#[cfg(test)]
mod body_summary_key_collision_tests;
#[cfg(test)]
mod trivial_setter_summary_tests;
// Trust (2026-10-08): ALLOC-RECEIVER-1 / ALLOC-WIDTH-1 — the live receiver and the
// target's object limit, the two panics the deleted 256 MiB budget was guarding.
#[cfg(test)]
mod alloc_width_receiver_tests;
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
/// REM-bounded BV multiply: `(a % 100) * (b % 50)` is provably in-range
/// (product <= 99*49 = 4851 << u32::MAX), yet the BV mul lane's fresh operand
/// vars carried NO mod bound — the solver fabricated an internally inconsistent
/// counterexample (`a = 0, b = 0` next to `bv_lhs = u32::MAX`) and FALSE-REFUTED
/// provably-safe code. `v2_bv_rem_constraints` renders `r < C` onto the fresh
/// BV vars; these tests pin the constraint presence and the refutability floor.
#[cfg(test)]
mod bv_rem_mul_tests;
#[cfg(test)]
mod field_vec_len_key_tests;
#[cfg(test)]
mod len_of_place_anchor_tests;
// IDX-TIE-1, second consumer: the nested-index LENGTH tie names std's
// `Index<usize>` on a std container. Pinned on real extracted MIR.
#[cfg(test)]
mod index_len_tie_anchor_tests;
// OWNED-VEC-NAME-1: an owned std `Vec`/`String` is named by its exact std path,
// never by the last segment of its type name. Pinned on real extracted MIR.
#[cfg(test)]
mod owned_container_name_anchor_tests;
#[cfg(test)]
mod push_guard_elem_len_tests;
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
pub(crate) mod signed_128_overflow_tests;
/// Cast VC model: value-preserving WIDENING casts into a 128-bit target.
///
/// Covers the `u32 as u128` (and friends) widening that previously returned
/// UNKNOWN ("target integer range is not representable by the cast VC model"),
/// plus the adversarial guarantee that the widening fact never vacuously proves
/// a genuinely-overflowing 128-bit arithmetic safe.
#[cfg(test)]
mod widening_cast_128_tests;
#[cfg(test)]
mod widening_mul_tests;
#[cfg(test)]
mod zst_len_bound_tests;
// Trust (NEGATIVE-LENGTH class): `conjoin_length_nonneg_bounds` must attach
// `0 <= len` to the canonical `__slice_len` symbol (and its SSA-versioned
// spellings) for EVERY element type, ZSTs included; must never attach the
// pointer-width `len <= isize::MAX` half, the only direction that could hide a
// real length overflow; and must never introduce a free variable.
#[cfg(test)]
mod length_nonneg_facts_tests;
// SOUNDNESS (hunt-15 Class B): `postcondition_references_mutated_param` must flag a
// param mutated through a `&mut`/`&raw mut` borrow (not just a whole-local reassign),
// so a bare `#[ensures(move |r| *r == a)]` over `let p=&mut a; *p=..; a` fail-closes
// instead of vacuously proving against the entry snapshot.
#[cfg(test)]
mod postcondition_mutated_param_tests;
// Trust (out-parameter postcondition): an `ensures` over a place written
// THROUGH a `&mut` parameter (`*x`, `(*self).0`) must be pinned to the stored
// value. The deref store is not a block-def establish point (the pointer is an
// opaque parameter), so without the explicit pin the pointee stays free and the
// clause is decided by havoc — TRUE and FALSE twins both "refuted".
#[cfg(test)]
mod mut_ref_postcondition_tests;
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
// Trust (T3 C05): the production generation's origin inventory: each row's own block
// through the sort, the emitted rows byte for byte, and complete-or-no-table.
#[cfg(test)]
mod overflow_origins_tests;
// The ENUM VARIANT PAYLOAD range fact: resolution-layer pins for the shapes a
// verdict cannot see. The verdict matrix is `tests/enum_payload_range.rs`.
#[cfg(test)]
mod enum_payload_range_tests;
// Trust (UNINHABITED MATCH ARM, false REFUTATION): `inhabited_enum_variant_tag_set`
// drops the tag of a variant whose payload is PROVABLY uninhabited, so the dead
// `Err` arm of a `Result<u8, Infallible>` match stops being accused. Every `true`
// deletes a tag from a globally published premise, so the tests' "must decline"
// half — `[T; 0]`, a fieldless struct, a union, anything behind a pointer, an
// unresolved generic, an un-migrated `adt_kind: None` — is the load-bearing half.
#[cfg(test)]
mod uninhabited_variant_tests;
// Trust (never-typed divergence): an `Opaque` terminator answers
// `LocalWrite::Unlocatable` for EVERY local, which deleted the dest-keyed enum
// tag-range fact for every `Discriminant` read in the body and left an
// exhaustive match's shared `otherwise -> Unreachable` REFUTED — 2962 of the
// 4734 refuted rows on the ay-dpll graph at seal 30. The decline half (a live
// `otherwise` arm stays live; a non-call `Opaque` stays fail-closed) is the
// load-bearing half.
#[cfg(test)]
mod never_call_opaque_poison_tests;
// Trust: piece #7a — folds + freshen-list soundness for the const-generic
// `ConstValue::ConstParam` value; since CONSTPARAM-SIGMA-FRESHEN-1 also the σ
// path end to end (the caller's `K` is one term, a callee's `K` never meets it).
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
// Trust (R20 Front A): the index-panicking container-mutator recognizer must
// key on the RECEIVER path, never on text inside a turbofish generic-argument
// group (`serde_json::Map::<std::string::String, …>::insert` is TOTAL).
#[cfg(test)]
mod container_mutator_path_tests;
// Trust (W4 fix round 1, 2026-09-25): the `binary_search` result facts are seeded
// only over a result local with ONE definition, and a whole write of the local
// kills a fact over its downcast payload (`@` is a projection separator).
#[cfg(test)]
mod vec_region_bsearch_tests;
// Trust (W4 fix round 3, 2026-09-29): the region's definition-block exemption covers
// the DEFINITION, not a two-phase `&mut` reservation the same block leaves open for a
// later block (probe v2p01: a len read inside `v.truncate(..)`'s argument stated `L0`
// at the pre-truncate length).
#[cfg(test)]
mod vec_region_twophase_tests;
// Trust (MUTREF-VEC-LEN-GUARD-REFUTE-1 / VEC-REGION-JOIN-SEED-1, 2026-10-12): the region
// facts are minted for a mutator-free `&mut Vec` parameter (`if !v.is_empty() { v.len() -
// 1 }` proves), never at a return target another edge enters (`let n = if c { v.len() }
// else { 100 }` states no `n == L0`), and never past a resize (`clear`, `truncate`, an
// opaque `f(v)`). Pinned on real extracted MIR.
#[cfg(test)]
mod vec_region_no_mutator_tests;
// Trust (2026-10-15, DECISION_QUEUE D101): an `&mut Vec` parameter is a region root only
// when no other parameter could reach its pointee (the region assumed `noalias` silently).
// Pinned on real extracted MIR.
#[cfg(test)]
mod vec_region_param_alias_tests;
// Trust (return-discriminant summary): the callee-summary recognizer
// (`function_return_disc_summary` — UNCONDITIONAL / GUARD-CONDITIONED, both
// fail-closed) and its use site — the unwrap panic-freedom lane's
// SUMMARY-pinned call-result receiver (`let r = Rat::new(n, d); r.unwrap()`).
#[cfg(test)]
mod ite_elimination_tests;
#[cfg(test)]
mod return_disc_summary_tests;
// Trust (countdown-loop piece): the division-countdown trip theorem — the
// exactly-tight T/K tables (an off-by-one DOWN in T is a false proof; the u64
// quad loop runs EXACTLY 5 times, consuming a 20-byte buffer to offset 0) and
// the builder's soundness gates, each pinned on REAL MIR extracted with
// `-Ztrust-dump=mir:<dir>` from the trap shape it kills.
#[cfg(test)]
mod const_param_range_tests;
#[cfg(test)]
mod countdown_trip_tests;
// The loop-guard underflow certificate of a downward-var decrement (relational
// `lo < hi` guards, guard freshness, second decrements, parameter cursors), each
// pinned on REAL MIR from the probe it closes or wins (TWO-POINTER-FALSE-REFUTE).
#[cfg(test)]
mod downward_guard_tests;
#[cfg(test)]
mod element_read_congruence_tests;
#[cfg(test)]
mod per_arg_havoc_refinement_tests;
// TINV P1 on real MIR (2026-10-06): calls whose arguments grant no write channel.
#[cfg(test)]
mod escape_havoc_tests;
#[cfg(test)]
mod no_write_call_args_tests;
#[cfg(test)]
mod vec_index_dest_value_tie_tests;
// STD-RECEIVER-ANCHOR-1: the length-benign `&mut` receiver is std's own `Index`/
// `IndexMut` on a std container, and the `?` re-wrap is the keyed `Try::branch`.
// Pinned on real extracted MIR.
#[cfg(test)]
mod std_receiver_anchor_tests;
// ======================================================================
// Float bit-reinterpretation call models: `f64::to_bits`/`from_bits` and the
// f32 siblings. Task #66 (completeness half): restore the correlation between a
// `let bits = v.to_bits()` integer local and the float's IEEE bitvector so the
// `f64_next_up_compat` shape (`bits - 1` guarded by `v != 0.0`) becomes PROVABLE
// instead of falsely refuted. See `float_bits_call_dest_fact`.
// ======================================================================
#[cfg(test)]
mod float_bits_call_model_tests;
// The postcondition lane assembles its VC over an entry state the assumption
// gate left UNCONSTRAINED whenever it dropped the authored `requires`, so a TRUE
// postcondition is "refuted" at an entry state the precondition forbids and the
// verifier mints `verified_counterexample = true` against correct code. The
// third silent-weakening tripwire fails such a row closed to the visible
// unsupported shape — but only on an EXHIBITED model, so a provable row and a
// genuinely-refutable one are both untouched.
#[cfg(test)]
mod entry_hypothesis_tests;
// INTRINSIC-RESIDUAL-1: a 128-bit integer parameter's type range, which the extractor
// does not attach, is stated by the generator (`missing_param_type_range_facts`).
#[cfg(test)]
mod param_type_range_facts_tests;

#[cfg(test)]
mod postcondition_type_range_tests;
// The premise the CONSUMER-SIDE clause of `entry_sentinel_tie_is_sound` is dead
// under: `v2_terminator_targets` ⊆ the path-def fixpoint's enqueue set, so a
// consumer's mandatory v2 in-edge is always intersected in. Nothing else in the
// suite notices when that stops holding.
#[cfg(test)]
mod entry_sentinel_tie_subsumption_tests;

// Trust (postcondition composition — the key-collision trust boundary): the
// injection lane matches a callee by its RENDERED NAME and `modular::
// FunctionSummary` carries no identity at all, so the "one name, one callee"
// obligation is entirely the producer's. These tests pin the mechanism and
// enumerate what does NOT discriminate (`CalleeIdentity`, `param_types`, the
// destination type) so none of them is later mistaken for a defence.
#[cfg(test)]
mod summary_key_collision_tests;
// The merged-local vacuity class: a global fact keyed on a local the program can
// REDEFINE binds that local's terminal version exactly and empties the violating
// path. These rows reach the two recognizers whose contracts only an in-crate test
// can name — `is_nonzero_get_call`'s definition-path match and
// `checked_result_field0_consumer`'s uniqueness bail.
#[cfg(test)]
mod merged_local_vacuity_tests;
// The parameter-entry-def budget: a parameter is defined at ENTRY, invisibly to a
// `body.blocks` def scan, so its explicit-def budget is ZERO and every other local's
// is one. Held at the predicate because a wrong budget is only visible at a verdict
// when some producer happens to key that local.
#[cfg(test)]
mod param_entry_gate_tests;
// ENC-DEFECTS 13b (salvage reconciliation 2026-09-28): the gates of
// `path_defs::frozen_shared_reborrow_roots`, asked directly on real MIR, and its
// composition with the TRUST-10 sibling `callee_write_set::refine_shared_reborrow_havoc`
// in `terminator_def_names`. Lives here because the function is `pub(super)`.
#[cfg(test)]
mod enc_defects_13b_gate_tests;
// TINV step 0(a) (docs/design/2026-10-04-type-invariant-tinv.md, gate G14): a
// `&mut self` pointee field read before any write binds the ENTRY version, and a
// read after `self.k = ..` binds a fresh one. An entry type-invariant fact keyed on
// the bare name is sound only while both hold. `stmt_versions_for` is `pub(crate)`.
#[cfg(test)]
mod tinv_entry_rename_tests;
// TINV step 10.1: the type-invariant assumption tag passes the version-token grammar
// (every rename, seal and tie helper, and a whole generation) byte for byte.
#[cfg(test)]
mod tinv_assume_tag_tests;
// TINV 10.3-LEN: an entry fact's length terms are re-versioned by a `&mut` call on the
// field or a store to it (landed before any use-site fact).
#[cfg(test)]
mod tinv_len_versioning_tests;
// TINV step 10.3: the use-site facts conjoined into real rows, end to end.
#[cfg(test)]
mod tinv_use_site_tests;

/// Trust (2026-09-19): the NAME-ONLY members of the "this callee panics on a
/// caller-supplied value" family, re-exported for the COMPILER's
/// vanilla-sysroot tolerance.
///
/// WHY THE TOLERANCE NEEDS THEM. That class admits a sysroot callee at
/// foundational types because "its panic, if any, is std's own DEFINED behaviour
/// reacting to the environment". A panic on an out-of-range index or a too-small
/// buffer is NOT that — it is a Rust safety obligation about the caller's own
/// value, and the class already carves out the division family for exactly this
/// reason (`is_panicking_primitive_int_div_method`, consulted the same way).
///
/// These rows are ALSO emitted by `unsupported.rs` on the CALLER's MIR, but that
/// lane only sees calls in a body vcgen analyses — measured 2026-09-19, a call
/// inside a BUNDLED core member (`char::encode_utf8_raw`, reached through core's
/// own `fmt::Write::write_char`) is invisible to it. Consulting the same
/// predicates from the tolerance covers the bundled case without duplicating the
/// name lists.
///
/// Name-only by construction: `is_bounds_panicking_slice_mutator` is NOT here
/// because it needs the function and its arguments, which the tolerance does not
/// have.
///
/// `VecDeque`'s caller-value members and `char::encode_utf16` are deliberately NOT
/// here — see [`callee_is_root_call_caller_value_panic`] for why they are asked only
/// of the ROOT body's own call sites.
pub fn callee_is_known_caller_value_panic(callee: &str) -> bool {
    unwrap_panic::is_index_panicking_container_mutator(callee)
        || unwrap_panic::is_buffer_panicking_char_encoder(callee)
}

/// Trust (2026-10-01, review rounds 29 and 30): whether the integer fold row
/// (`generate/safety.rs`, `1c-fold`) recognizes `callee` as `Iterator::sum` or
/// `Iterator::product` — the spelling the extractor renders for the call site. The
/// compiler grants such a call as charged only when this answers true, so a spelling
/// vcgen's parse misses (a `'>'` char const generic or a source path with `<`/`>`
/// in a callable's rendering) leaves the call ungranted, bundled and refused,
/// instead of uncharged.
pub fn callee_is_charged_integer_fold(callee: &str) -> bool {
    alloc_bounds::iterator_integer_fold_call(callee).is_some()
}

/// Trust (W4 fix round 1, 2026-09-25): the "panics on a caller-supplied value"
/// callees asked of ROOT call sites only — first the members of std's `VecDeque`
/// that no call-site lane charges
/// (`unwrap_panic::is_caller_value_panicking_deque_method`: `insert`, `split_off`,
/// `rotate_*`, `drain`, …), for the compiler's tolerance to ask of the ROOT body's
/// own call sites ONLY.
///
/// THE DEFECT: the index-mutator recognizer excludes `collections::` wholesale, so
/// an unguarded `d.insert(i, 0)` was admitted as "std's own defined behaviour" and
/// panicked at runtime (probe r08; measured on `0.10.0+gc2e3daed7`).
///
/// NOT HERE (reconciled with 92e7829ca5, W4 salvage 2026-09-28): `swap`, `range`,
/// `range_mut`, `insert_mut` and `d[i]`/`d[i] = x`, wherever main's `collection_range`
/// recognizer names the call. It charges each at the call site, precisely over a
/// stable deque length, so a guard discharges it; withholding the tolerance by NAME
/// would refuse every such call, guarded or not (it regressed
/// `policy_b/std_index_range_panics_charged.rs`). Their refusal when unguarded is that
/// charge row. A spelling that recognizer declines keeps this carve-out.
///
/// WHY ROOT CALL SITES ONLY, NOT THE BUNDLE WALK. The tolerance keys its ledger on
/// the callee NAME and consults it for std-internal call sites too, and std calls
/// these members with its OWN, already-validated arguments: `swap_remove_back` is
/// `if index < len && index != len - 1 { self.swap(index, len - 1) }; self.pop_back()`.
/// Asked there, the carve-out refused the TOTAL `swap_remove_back`/`swap_remove_front`
/// — measured when this predicate first sat in [`callee_is_known_caller_value_panic`]:
/// both went from rc=0 to rc=1 ("NOT-VANILLA callee=`VecDeque::<u32>::swap`" from the
/// bundle walk). A root call site is the user's own value by construction. The
/// bundled case the shared carve-out exists for — a std member FORWARDING a user
/// value into one of these — has no instance among the stable foundational-type
/// `VecDeque` API: every public entry that reaches one of these panics is itself in
/// the list, or is one of the members `collection_range` charges at the root call
/// (`swap`, `range`, `range_mut`, `insert_mut`, `Index`/`IndexMut`), and the rest
/// take a closure or a user type and are not vanilla at all. The fail-closed
/// `Call::<m>::panic-freedom-unverified` row `unsupported.rs` mints on the root MIR
/// is the second, independent refusal of every root call — except a std
/// `VecDeque::drain` over `..`, `0..`, `..0` or `0..0`
/// (`collection_range::std_vec_drain_range_cannot_panic`), which gets no row
/// because its one range check (`slice::range(r, ..len)`) cannot fail; tolerating
/// that call here admits no panic.
///
/// Trust (UTF8-ENCODE-UTF16-SHORTBUF-1, 2026-10-05): and `char::encode_utf16` /
/// `encode_utf16_raw` (`unwrap_panic::is_buffer_panicking_char_utf16_encoder`), which
/// panic on a caller buffer shorter than the character's UTF-16 length. Root call
/// sites only for the same reason: core's `EncodeUtf16::next` and `wtf8` call them
/// with a two-unit buffer of their own, so asking the bundle walk would refuse the
/// total `s.encode_utf16().count()`. MEASURED before (stage 1 of `dc15b882f6`):
/// the root ledger admitted `core::char::methods::<impl char>::encode_utf16` as
/// `vanilla=true`, and `c.encode_utf16(&mut [0u16; 1])` built rc=0 and panicked.
/// `unsupported.rs` mints the second, independent refusal on the root MIR.
pub fn callee_is_root_call_caller_value_panic(callee: &str) -> bool {
    unwrap_panic::is_caller_value_panicking_deque_method(callee)
        || unwrap_panic::is_buffer_panicking_char_utf16_encoder(callee)
}

/// Trust (2026-09-25): does a call to `callee` (rendered as at a call site) fall
/// in a panic family vcgen charges AT THE CALL SITE — `unwrap`/`expect`, signed
/// `abs`, the slice-method panics, the caller-value families above, and the
/// bounds-panicking slice mutators? NAME-ONLY and conservative (no receiver
/// gating): the compiler asks it of a sysroot function ITEM handed to a callee as
/// a TYPE ARGUMENT, which runs inside that callee where no call-site recognizer
/// looks. The item is admitted only where a DIRECT call to it would have been
/// charged nothing.
///
/// Trust (2026-10-06, ROTATE-ITEM-NAME-1): with one owner check. The
/// bounds-panicking mutator arm (the last one: `rotate_left`/`rotate_right`,
/// `split_off`, `drain`, ...) is for the slice, `Vec`, `String` and `VecDeque`
/// members, and it used to answer `true` for core's TOTAL integer
/// `core::num::<impl u32>::rotate_left` too, so `v.iter().copied().fold(1u32,
/// u32::rotate_left)` was refused under the DEFAULT policy ("an unresolved indirect
/// call keeps the function fail-closed") while `fold(1u32, u32::wrapping_shl)`, the
/// same signature on the same owner, and the closure twin `|a, b| a.rotate_left(b)`
/// were admitted (measured on the stage 1 of `4ccd862830`; a verify-off build prints
/// 64). The arm now skips core's authenticated primitive-integer inherent
/// (`numeric_panic::int_inherent`: a `core::num::<impl iN/uN>::` owner under a
/// sysroot root that carries no `__trust_crate@` stamp). No other name in that arm
/// exists as an integer inherent, so only the two integer rotates leave the union,
/// and both are `intrinsics::rotate_left/right(self, n)`, which cannot panic. A
/// stamped or user spelling (`mycrate::num::<impl u32>::rotate_left`) fails
/// `int_inherent` and stays in; so do `NonZero`/`Wrapping`/`Saturating`'s rotates (an
/// over-refusal of total items, kept). This change makes the union answer `false`
/// for two spellings it used to refuse, so it GRANTS, and the grant is anchored on
/// `int_inherent`'s sysroot-root check.
///
/// Trust (W4 HASHMAP r3, 2026-09-29): and the ALLOCATION lane's call-site charges
/// ([`callee_is_call_site_allocation_sink`]) — the capacity-overflow panics of
/// `with_capacity`, `reserve`, `collect`, `from_iter`, `extend`, `unzip`,
/// `collect_into`, ... are exactly such charges. MEASURED on the redo's r2
/// (`b9288112d`): `Some(n).map(HashSet::<u64>::with_capacity)`, `Result::map`,
/// `Option::map_or_else(HashSet::new, HashSet::with_capacity)`, `Iterator::map`, an
/// `impl Fn` returning the item, and `Option::map(HashSet::from_iter)` /
/// `map(Iterator::collect::<HashMap<_, _>>)` built rc=0 and panicked "Hash table
/// capacity overflow" (15 probes); their `Vec` twins built rc=0 on main too.
///
/// Trust (W4 ITER-HOF fix round 4, 2026-10-02): and the two NUMERIC call-site
/// producers the union had left out, so it now names every family a direct call is
/// charged by: `panic_calls::divzero_call` (`div_euclid`, `div_ceil`, `rem_euclid`
/// — a zero divisor — and `step_by(0)`) and `alloc_bounds::overflow_arith_call`
/// (`pow`, which overflows under the CALLER's overflow checks:
/// `#[rustc_inherit_overflow_checks]`); since 2026-10-06 the union reads their
/// name-only twins (`divzero_call_name_only`, `overflow_arith_call_name_only`),
/// whose answers are the ones measured here. `numeric_panic` deliberately leaves
/// exactly these to them ("`div_euclid`/`rem_euclid`/`div_ceil` (the zero divisor)
/// stay with `divzero_call`"), so a sysroot item from either family was charged
/// nothing.
/// MEASURED (adversarial probes q07/q08 of `w4-salvage/probes/T5-iterhof-fix8`, and
/// the same verdict on stage 1 of origin/main `a3be88bbde` without W4):
/// `v.iter().copied().reduce(u32::div_ceil)`, `fold(7, u32::div_ceil)`,
/// `fold(2, u32::pow)`, `reduce(u32::pow)` and `fold(2i32, i32::pow)` built rc=0 with
/// no row (a `native-verification-gap` only) and panicked ("attempt to divide by
/// zero", "attempt to exponentiate with overflow"), while every DIRECT call
/// (`a.div_ceil(b)`, `a.pow(b)`) and every closure twin was refused. Unsigned
/// `div_euclid`/`rem_euclid` items were already refused, through the bridge's
/// division list (`is_panicking_primitive_int_div_method`), which has no `div_ceil`
/// and no `pow`. The integer division OPERATORS handed as items
/// (`fold(7u32, core::ops::Div::div)`, `Rem::rem`, by value or by reference, and the
/// `Wrapping`/`Saturating` impls) were the same hole, measured the same way; they are
/// `numeric_panic::is_int_division_operator_callee`. So were the integer `sum`/`product`
/// folds handed as items (`map(Iterator::sum::<u32>)`), which a direct call pays as an
/// `iterator-fold-overflow` row: `alloc_bounds::iterator_fold_item_may_overflow`. A
/// `true` here only withholds the vanilla admission of an item.
///
/// Trust (W4 ITER-HOF fix round 6, 2026-10-03): and the integer OVERFLOW-checked
/// operators by REFERENCE (`v.iter().fold(0u32, core::ops::Add::add)` is
/// `<u32 as Add<&u32>>::add`; `map(core::ops::Neg::neg)` over `&i32`; `Shl<&u32>`):
/// a direct call to one is the ruled foundational-member class, charged a
/// runtime-checked row the default policy reports and `certify` refuses, so it is
/// not "charged nothing". MEASURED: the item spellings built rc=0 under `certify`
/// too, with no row, and panicked verify-off. They are
/// `numeric_panic::is_int_overflow_operator_callee` (which also matches the by-value
/// spellings `is_numeric_value_panic_callee` already names).
///
/// Trust (W4 ITER-HOF landing round, 2026-10-03): the `Box`/`Rc`/`Arc` uninitialized
/// and zeroed SLICE constructors (`map(Box::<[u64]>::new_uninit_slice)`) are now in the
/// allocation arm, because `bulk_alloc_call` charges them at a direct call; before, no
/// lane did, and the review's probes built every spelling rc=0 and panicked "capacity
/// overflow". A DIVERGING item (`std::panic::panic_any`) is not this union's to name —
/// a rendered name carries no return type — and the compiler withholds every `-> !`
/// item before asking it (`foreign_fn_item_type_arg_is_accounted`). The union is still
/// a DENY-list: an item that panics on a caller value and that no family names is
/// admitted (docs/KNOWN_HAZARDS.md, the W4 ITER-HOF residual).
pub fn callee_has_call_site_panic_family(callee: &str) -> bool {
    let tail = alloc_bounds::method_tail(callee);
    if (matches!(tail, "unwrap" | "expect" | "unwrap_err" | "expect_err")
        && (callee.contains("Option") || callee.contains("Result")))
        || callee_is_call_site_allocation_sink(callee)
        // Trust (2026-10-06, DIVZERO-NAME-1): the name-only view, as for `pow` and
        // `abs` below. `divzero_call` now mints its row only for core's
        // authenticated `div_euclid`/`div_ceil`/`rem_euclid` and std's
        // `Iterator::step_by`; this deny-list keeps its wider answer.
        || panic_calls::divzero_call_name_only(callee).is_some()
        // Trust (2026-10-06): the name-only view. `overflow_arith_call` now mints
        // `pow`'s row only for core's authenticated primitive-integer `pow`; this
        // deny-list keeps its wider answer (a `Some` only withholds an admission).
        || alloc_bounds::overflow_arith_call_name_only(callee).is_some()
        || (matches!(tail, "sum" | "product")
            && alloc_bounds::iterator_fold_item_may_overflow(callee))
        // Trust (2026-10-06, ABS-NAME-1): the name-only view, as for `pow` above.
        // `abs`'s row is minted only for core's signed-integer `abs`
        // (`is_signed_abs_mint`, authenticated or behind one leading extractor stamp);
        // this deny-list keeps its wider answer.
        || (tail == "abs"
            && (callee.contains("core::num::") || callee.contains("std::num::")))
        // Trust (2026-10-11, SLICE-ZERO-SIZE-NAME-1): the name-only view, as for
        // `div_ceil` above. `slice_method_panic` now mints its `split_at`/`chunks*`/
        // `windows`/`swap` rows only for a sysroot-rooted callee; this deny-list
        // keeps its wider answer.
        || SliceMethodPanic::classify_name_only_with_tail(callee, tail).is_some()
        || (matches!(
            tail,
            "remove" | "insert" | "swap_remove" | "insert_str" | "encode_utf8" | "encode_utf8_raw"
        ) && callee_is_known_caller_value_panic(callee))
        || (matches!(
            tail,
            "drain"
                | "splice"
                | "extract_if"
                | "extend_from_within"
                | "prepend_from_within"
                | "insert"
                | "split_off"
                | "rotate_left"
                | "rotate_right"
                | "swap"
                | "range"
                | "range_mut"
                | "insert_mut"
                | "encode_utf16"
                | "encode_utf16_raw"
        ) && callee_is_root_call_caller_value_panic(callee))
    {
        return true;
    }
    let numeric = numeric_panic::NumericCallee::for_authenticated(callee, tail);
    numeric.is_int_division_operator()
        || numeric.is_int_overflow_operator()
        // Trust (2026-09-25, std-numeric-family): `iter.map(u32::ilog2)`,
        // `opt.map(char::from_digit ..)` — a numeric method whose panic is an
        // argument value, handed over as an ITEM, runs where no call-site row
        // can be minted.
        || numeric.is_value_panic_callee()
        // Trust (2026-10-06, ROTATE-ITEM-NAME-1): not core's own integer inherent,
        // whose `rotate_left`/`rotate_right` are total (see the doc above).
        || (matches!(
            tail,
            "rotate_left"
                | "rotate_right"
                | "split_off"
                | "drain"
                | "copy_within"
                | "select_nth_unstable"
                | "select_nth_unstable_by"
                | "select_nth_unstable_by_key"
                | "extend_from_within"
        ) && numeric.int_inherent().is_none())
}

/// Trust (VEC-AS-SLICE, 2026-09-25): the exact identity of the row the `1e` arm of
/// the safety pipeline emits for the OWNED-`Vec` SCALAR index call (`v[i]`,
/// `<Vec<T> as Index<usize>>::index(&v, i)`, and its `index_mut` twin) that
/// terminates `block_id` — its kind and its recorded obligation BODY, normalized
/// exactly as the pipeline's final pass normalizes it.
///
/// The compiler's bundled-member Assert gate asks this, per call site, before it
/// credits the bounds `Assert` inside std's `<usize as SliceIndex<[T]>>::index`
/// (reached only through `Vec`'s forwarding `Index` impl) to that row: the row must
/// exist in the root's public inventory under this exact identity, so a row
/// dropped or rewritten between producer and inventory refuses instead of
/// silently leaving the member `Assert` charged to nobody.
///
/// `Some` only for the two shapes that row can take: the real bounds obligation
/// (`VcKind::SliceBoundsCheck`, body `i >= coll_len(base)`) and its fail-honest
/// `UnsupportedMir { kind: "container-index-unstable-len" }` backstop (body
/// `Bool(true)`, never provable). Everything else — a range index, a map index, a
/// receiver the producer does not recognize as an owned `Vec` — is `None`, and the
/// caller must refuse.
pub fn owned_vec_scalar_index_row(
    func: &VerifiableFunction,
    block_id: BlockId,
) -> Option<(VcKind, Formula)> {
    let block = func
        .body
        .blocks
        .get(block_id.0)
        .filter(|block| block.id == block_id)
        .or_else(|| func.body.blocks.iter().find(|block| block.id == block_id))?;
    let Terminator::Call { func: callee, args, .. } = &block.terminator else {
        return None;
    };
    let panic = slice_method_panic(callee)?;
    // Trust (CONST-RANGE-INDEX-1, 2026-10-06): a range index is the `1e` arm's own
    // answer (`range_index_range_operand`), which also sees a constant range the
    // callee's instantiation names.
    if !matches!(panic, SliceMethodPanic::RangeIndex)
        || range_index_range_operand(func, callee, args).is_some()
        || !args.iter().any(|arg| operand_is_scalar_usize_index(func, arg))
    {
        return None;
    }
    let (violation, kind) = slice_method_panic_body(
        func,
        &panic,
        callee,
        args,
        callee.contains("__trust_str_index"),
        block,
    )?;
    let unsupported = match &kind {
        VcKind::SliceBoundsCheck => false,
        VcKind::UnsupportedMir { kind: name, .. } if name == "container-index-unstable-len" => true,
        _ => return None,
    };
    // Mirror the `1e` arm: a scalar index renames the violation at the block terminal
    // (`v2_formula_with_block_defs_recorded`'s `body`), and the final pass normalizes
    // every row except an `UnsupportedMir` one.
    let sv = stmt_versions_for(func);
    let body = version_rename_owned_at(violation, &sv, func, block.id, block.stmts.len());
    let body = if unsupported { body } else { normalize_ssa_version_tokens_owned(func, body) };
    Some((kind, body))
}

/// Trust (2026-10-02, census-vcgen-hang): one VC-generation memo scope held across a
/// BATCH of [`owned_vec_scalar_index_row`] replays of ONE function.
///
/// WHY. A replay builds its row with the full block-defs builder, which asks the
/// function's statement-version oracle (`havoc_memo::version_oracle`: a dominator
/// index, a write index and the SSA oracle over the WHOLE body) and the whole-body
/// analyses of `fn_memo` / `place_memo`. Those are memoized only inside a VC-gen
/// scope, and the compiler's `Vec`-forwarder gate (`charge_vec_index_forwarders`)
/// replays one row per root call site of a forwarder OUTSIDE any scope, so every
/// site rebuilt the whole-function oracle: O(sites x body), after generation itself
/// had built it once. On aterm-census `lock_order::run_lock_order_census` (1114
/// blocks, 24 `Vec` index sites; trust main 123f22d176, opt-level 2 + debug
/// assertions) the replay ran for minutes past the function's 120 s budget, all of
/// it inside native bundle construction, where the budget is only checked before and
/// after. Held across the batch, the oracle and the analyses are built once.
///
/// WHY IT CHANGES NO ROW. This is `gen_work::enter_unmetered`, the scope the
/// overflow-elision join-table replay used until T3 C05: memos live, work meter OFF for
/// the scope's whole extent. Every memoized value is a pure function of the function
/// (keyed on its identity: address, locals buffer, name) and of its key, so a replay
/// under the scope returns the bytes an unscoped replay returns; and with the meter
/// off no degraded leaf can be produced, exactly as for an unscoped call, which never
/// meters. `row_replay_scope_tests` pins both halves: identical rows, one oracle.
///
/// THE HOLDER'S CONTRACT. Query only functions that stay borrowed for the scope's
/// whole extent (the identity key relies on an address that cannot be reused while
/// they are alive), and drop the scope on the thread that entered it (it is not
/// `Send`).
#[must_use = "the memo scope lasts only while the guard is held"]
pub struct RowReplayScope {
    _scope: crate::gen_work::UnmeteredGuard,
    _not_send: std::marker::PhantomData<*const ()>,
}

/// Enter a [`RowReplayScope`]; hold the guard across the batch of replays.
pub fn row_replay_scope() -> RowReplayScope {
    RowReplayScope {
        _scope: crate::gen_work_scope_unmetered(),
        _not_send: std::marker::PhantomData,
    }
}

/// Trust (2026-10-19, R1 harvest): the memo scopes of a public VC-generation entry that
/// has NO work meter of its own — the call-site precondition producers
/// ([`generate_callsite_precondition_vcs`], its `_attributed` twin), the call-site L0
/// replay's caller assembly and the `Vec`-mutator charge gates. Opened on the function
/// VIEW the entry's analyses read (the arithmetic-safe clone, when there is one), held
/// for the rest of the entry.
///
/// WHY. Those entries ran OUTSIDE every scope when the compiler called them directly,
/// and outside a scope every whole-body analysis is rebuilt per ask: `place_memo`'s
/// local-name table per minted name, `fn_memo`'s laundered alias roots and shared-cell
/// borrows per havoc list, and, with no [`FuncAnalysisScope`], the path-guard map and
/// the statement-version oracle per lookup. The R1 harvest
/// (`trust_verify::try_harvest_flip`) asks the attributed producer once per (callee,
/// caller). Sampled on the `ty` bin under trust 4e95b2c82cee, R1 ran past 1 h 40 min
/// at 13.5 GB with the thread wholly under that producer's
/// `build_semantic_guard_map_impl`: of 7983 samples, 4904 in `LocalNameTable::of` via
/// `place_memo::local_names` and 5290 in `write_havocs_function_list` ->
/// `fn_memo::laundered_alias_roots` (inclusive counts; the two overlap).
///
/// WHY IT CHANGES NO OBLIGATION BELOW A BUDGET. The work half is
/// `gen_work::enter_joined`: nested in a generation it is a depth increment, so the
/// entry is charged to the enclosing meter and to no other; outermost it is the
/// unmetered scope, under which nothing trips, as nothing trips unscoped. The memo half
/// returns, for every query, the value an uncached computation returns (each is a pure
/// function of the body and its key, bound to the function's identity, and the view
/// stays borrowed for the scope's whole extent). The analysis frame is reused when the
/// innermost one is already bound to this very function, so an entry nested in a scope
/// of its own function shares that scope's analyses rather than rebuilding them in a
/// fresh frame. `entry_scope_tests` pins both halves below every budget: byte-identical
/// rows with and without the scope, and analyses whose builds do not grow with the call
/// sites.
///
/// AT A BUDGET IT CAN CHANGE A ROW, in one direction only: the scope can only LOWER the
/// work two budgets see, and both count it deterministically.
/// * The `gen_work` meter. A place query charges it even on a memo hit
///   (`place_memo::HIT_COST`), and nested in the per-body lane
///   (`discharge::generate_vcs_with_discharge_and_summaries_configured_impl`, whose
///   metered scope opens no [`FuncAnalysisScope`]) the new analysis frame removes the
///   per-lookup rebuilds of the path-guard map and the statement-version oracle, and
///   with them their place queries.
/// * The ambient `verify_budget` step counter. The guard-map walk polls
///   `budget_exhausted` once per step (`safety::v2_analyze_path_guards`), and R1, the
///   per-body lane up to its checkpoint (`trust_verify::preprocessing_budget_exceeded`)
///   and the StepBy and L0 gates all run under an installed step budget, so fewer
///   rebuilds are fewer steps spent.
///
/// So a function or a harvest that used to trip can now finish: the per-body inventory
/// goes from the wholesale budget verdict (one synthetic `Unknown` row, or a located
/// error in a fail-closed lane) to real rows, and an R1 attribution that used to be
/// discarded (`trust_verify::r1_budget_tripped`) is now minted. That is sound (fewer
/// trips, and every added row is an obligation a solver still decides, never a PROVE
/// without one), but it is not byte-identical to the rows before the scope: a consumer
/// recheck is not judged by a byte diff against trust 4e95b2c82cee.
///
/// THE HOLDER'S CONTRACT is `enter_joined`'s: run no METERED entry inside the scope
/// (one nested there neither resets nor meters); the L0 replay generates its callee's
/// VCs before it opens one.
#[must_use = "the memo scope lasts only while the guard is held"]
pub(crate) struct EntryScope<'f> {
    // Declared first, so dropped first: the analysis frame goes before the work scope.
    _analysis: Option<FuncAnalysisScope<'f>>,
    _work: Option<crate::gen_work::JoinedGuard>,
}

impl<'f> EntryScope<'f> {
    pub(crate) fn enter_analysis_if_unbound(
        func: &'f VerifiableFunction,
    ) -> Option<FuncAnalysisScope<'f>> {
        #[cfg(test)]
        if ENTRY_SCOPE_DISABLED.with(std::cell::Cell::get) {
            return None;
        }
        FuncAnalysisScope::enter_if_unbound(func)
    }

    pub(crate) fn enter(func: &'f VerifiableFunction) -> Self {
        #[cfg(test)]
        if ENTRY_SCOPE_DISABLED.with(std::cell::Cell::get) {
            return EntryScope { _analysis: None, _work: None };
        }
        let work = crate::gen_work_scope_joined();
        let (func_addr, body_addr) =
            (std::ptr::from_ref(func) as usize, std::ptr::from_ref(&func.body) as usize);
        let bound = FUNC_ANALYSIS_MEMO.with(|memo| {
            memo.borrow()
                .last()
                .is_some_and(|frame| frame.func_addr == func_addr && frame.body_addr == body_addr)
        });
        let analysis = (!bound).then(|| FuncAnalysisScope::enter(func));
        EntryScope { _analysis: analysis, _work: Some(work) }
    }
}

#[cfg(test)]
thread_local! {
    /// Test seam: when set, [`EntryScope::enter`] opens nothing, so an entry runs as
    /// it did before it had a scope — the negative control of the scope's work tests.
    static ENTRY_SCOPE_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `f` with [`EntryScope`] disabled on this thread (restored on return or unwind).
#[cfg(test)]
pub(crate) fn without_entry_scope<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            ENTRY_SCOPE_DISABLED.with(|slot| slot.set(self.0));
        }
    }
    let _restore = Restore(ENTRY_SCOPE_DISABLED.with(|slot| slot.replace(true)));
    f()
}

#[cfg(test)]
mod primitive_decimal_len_tests;
