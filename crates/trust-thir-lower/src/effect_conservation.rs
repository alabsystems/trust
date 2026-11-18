//! Trust (2026-10-01): THE EFFECT-CONSERVATION GATE for the direct THIR -> trust-ir lane, and
//! the D28 abstraction tags (docs/DECISION_QUEUE.md D28, docs/KNOWN_HAZARDS.md "effect
//! conservation").
//!
//! # Why this exists
//!
//! Three producer lanes shipped a lowered, spliced, strict-clean, codegen-licensed body with an
//! effect of the program missing: the wave-ER `for` summary (`for fd in lo..hi { close(fd) }` ->
//! `ret`), the opaque `()` / Option-discriminant field lanes (a field store's right-hand side —
//! calls and whole loops — never lowered) and drop elision (no `Inst::Drop`, so a destructor never
//! runs). Each was found by a person reading IR. The crate-seam differential SAW the dropped calls
//! (a "callee-set asymmetry") and classed them as a coverage-only skip; strict reads only the tag
//! list; the codegen license is structural. Nothing compared the EFFECTS of a body with the
//! program's. This module does, with rustc's own built MIR as the oracle (R-2: MIR is a test
//! oracle, never a production input — this reads it, it never feeds it anywhere).
//!
//! # The rule
//!
//! A direct-lane body is CONSERVED iff
//!
//! 1. every effect in its MIR census is PAIRED with an effect in its trust-ir census (or is a
//!    call to a callee on the audited [`Equivalence`] list, which is effect-free and panic-free
//!    by construction, so no effect is lost when the producer computes its value another way — or
//!    an `asm!` with no template, no operand and `options(noreturn)`, which is UB to reach),
//! 2. its trust-ir carries no VALUE ABSTRACTION (D28): no `undef`, no opaque placeholder lane
//!    (an enum the body holds BY VALUE anywhere — a local, a tuple, a struct literal, a slot, an
//!    array element — that the producer collapses to a lone `bool`/`()`; a touch of a degraded
//!    struct profile — `()` / discriminant-`bool` placeholder fields —; a union or
//!    enum-parameter lane; an enum value spelled as a lone `bool`/`()`; see [`Abstractions`]),
//!    no elided drop,
//! 3. and the function crate assembly spliced for it has the same effect shape as the per-body
//!    function the census read (the splice must not add or remove an effect).
//!
//! Anything the matcher cannot pair is a MISMATCH, never a skip. A body that is not conserved is
//! REFUSED by every consumer that would treat it as the program:
//!
//! * codegen — the F1 handoff (`AssembledCrateModuleForCodegen::exact_body`) withdraws it, and the
//!   published-module lane refuses it by name (`[effect-not-conserved]`);
//! * `-Ztrust-ir-lower=strict` — an error naming every tag (`rustc_mir_build::
//!   trust_ir_crate_finalize`);
//! * probe channel C — `not-conserved(<kinds>)` / `abstracted(<lanes>)`, counted distinctly.
//!
//! Verification consumers may still READ an abstracted body, but only by naming the tags they
//! accept ([`admit_for_verification`] in process; the `<crate>.effect-conservation.json` sidecar
//! beside a dump for out-of-process readers such as aterm's temporal extractor). That is D28, as
//! taken 2026-10-01: abstracted => tagged, never codegen, never strict; reversible by a revert.
//!
//! # Typed closure adapters
//!
//! Source bodies keep the MIR/census rule above. A generated FnOnce adapter
//! has no Rust DefIndex or MIR body and receives no fabricated source verdict.
//! Its separate context witness requires the exact MakeClosure/Call/Return
//! protocol, a source constructor owner, and its real source target. Both
//! source rows must be independently conserved and licensed, and the observed
//! frame and complete signatures must agree. The protocol constructs values
//! without accessing memory and calls that target exactly once, preserving
//! capture order and pointer identity. Extra effects are not the protocol.
//! Sidecars disclose this derived owner/body basis; source scorecards, strict
//! source counts and proof grades never receive synthetic adapter rows.
//!
//! # The census, precisely
//!
//! MIR side ([`mir_census`], the built body the `mir_built` provider returns — the exact body the
//! hook's differentials compare against), over the blocks reachable from `START_BLOCK` along real
//! edges (`FalseEdge`/`FalseUnwind` imaginary edges and cleanup blocks are not followed: trust-ir
//! has no unwind path and D20 binds postconditions to normal returns):
//!
//! * `Call`/`TailCall` — callee identity is the `FnDef` the operand spells (plus, for a `Fn*`
//!   trait call on a closure or fn item, that closure/fn), or INDIRECT for any other operand;
//! * `Store(root)` — an `Assign`, `SetDiscriminant` or `CopyNonOverlapping` whose target is reached
//!   through a pointer that ESCAPES the body: a pointer parameter (`Arg(i)`), a `static` (or
//!   thread-local) address, or a pointer loaded from memory (`Indirect`). A write through a
//!   reference to one of the body's own locals, or through a fresh `Box::new*` allocation, is not
//!   an effect and is not counted; a `Box` parameter or `Box::from_raw` box is a pointer like any
//!   other. A call whose destination is such a place counts as a store too;
//! * `Assert` — a panic check (bounds, overflow, shift amount, division by zero), classed;
//! * `Drop` — a `Drop` terminator (MIR building schedules one only for a type that needs dropping)
//!   that is not dead by construction ([`drop_is_live`]): a drop of a local every path has moved
//!   from, of a direct field every path has moved from, or of a destructor-less struct/tuple whose
//!   every field that needs dropping every path has moved from runs no destructor, as drop
//!   elaboration would find (a closure, and a coroutine body's drop of its OWN env, drop only their
//!   upvars, judged the same way); anything else — through a pointer, an enum, a type with its own
//!   `Drop`, a coroutine VALUE, a deeper partial move — is kept, conservatively; each live drop
//!   records whether its glue may run a destructor beyond releasing memory
//!   ([`drop_runs_destructor`]);
//! * `Asm` (`InlineAsm`) and `Yield`;
//! * every enum type the body holds by value ([`MirCensus::enum_types`]), for the abstraction
//!   reading above.
//!
//! trust-ir side ([`ir_census`], `functions[0]` of the body's own per-body module, reachable
//! blocks): `Call`/`Invoke` (identity from the producer's callee ledger, `CalleeRef::site_def_id`
//! and `def_id`; a callee with no ledger row is UNLEDGERED), `CallIndirect`, `Store`/`AtomicStore`/
//! `AtomicRMW`/`CmpXchg`/`MemCopy`/`MemSet` classed by the pointer's root (a parameter, a global, a
//! loaded pointer, or this body's own `Alloca`/`HeapAlloc`, which is not an effect), `Drop`,
//! `CoroSuspend`, `DialectOp` (counted as asm), `Assert` (classed by its proof annotation).
//! Pairing:
//!
//! * a MIR direct call pairs with a trust-ir call of the same site — the same `FnDef` AND the
//!   same generic args, when both sides can spell them ([`call_admits`]: a trait method's
//!   `FnDef` is shared by every impl) — or, for a site either side cannot spell, the same
//!   `DefId`; effectful calls are matched before audited-equivalence ones ([`match_calls`]);
//! * a MIR indirect call pairs with a trust-ir `CallIndirect` or an unledgered call;
//! * a MIR store with root `Arg(i)` pairs with a trust-ir store through parameter `i` (when the
//!   two parameter counts differ, parameters pair as one pool); `Static` and `Indirect` pair with
//!   a trust-ir `Global` or `Indirect` store;
//! * drops, asm and yields pair by count; panic checks by count within their class.
//!
//! Extra trust-ir effects are not a mismatch here (the differentials judge them); only a MISSING
//! effect is.
//!
//! # What it does not see
//!
//! A WRONG value stored by a faithful store (the differentials' job), a panic check's
//! CONDITION (only its presence is paired), effect ORDER (the `DerefMut` chain order hazard),
//! effects inside a callee (each body is checked on its own), a write through a fresh
//! `Box::new*` allocation the body returns (a value, not an effect), and const/static initializer
//! bodies' calls (CTFE: no runtime effect; their value abstractions are still tagged). Symbolic
//! bodies (value-less placeholders) are refused by the splice already and are not re-tagged
//! here.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

mod closure_adapters;
mod exact_store;
pub mod retained;
pub mod thir_source;
mod store_root_facts;

use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    self, AssertKind, BasicBlock, Body, Local, Location, NonDivergingIntrinsic, Operand, Place,
    PlaceRef, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use rustc_span::def_id::{DefId, DefIndex, LocalDefId};
use trust_ir::{
    BlockId, Constant, FuncId, Function, Inst, Module, ProofAnnotation, StructId, Ty, ValueId,
};

use crate::SiteArg;

// ---------------------------------------------------------------------------------------------
// The census vocabulary. TyCtxt-free, so the matcher is unit-testable.
// ---------------------------------------------------------------------------------------------

/// Where a MIR store's memory lives, as far as it matters for an effect: memory the CALLER can
/// see. A store to the body's own locals is not recorded at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemRoot {
    /// Through pointer parameter `i` (0-based over the body's arguments).
    Arg(u32),
    /// Through a `static` / thread-local address.
    Static,
    /// Through a pointer loaded from memory, returned by a call, or otherwise untraced.
    Indirect,
}

/// The audited, named reason a MIR call may stay unpaired: the callee is effect-free and
/// panic-free, so a producer that computes its result without the call loses no effect. Each
/// variant names the exact callee class [`audited_equivalence`] admits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Equivalence {
    /// An intrinsic on [`PURE_INTRINSICS`] (a value computation: no memory write, no I/O, no
    /// panic). `transmute` is the common one (the producer lowers it to a cast).
    PureIntrinsic,
    /// `<[T]>::len` (lang item `slice_len_fn`): reads the fat pointer's metadata.
    SliceLen,
    /// `IntoIterator::into_iter` on an integer `Range`/`RangeInclusive` (returns its argument).
    RangeIntoIter,
    /// `Iterator::next` on an integer `Range`/`RangeInclusive` the body owns (the wave-FR range
    /// lane lowers the loop as integer arithmetic): writes only that local iterator.
    RangeNext,
    /// `Option::is_some` / `Option::is_none`: reads the discriminant.
    OptionDiscriminant,
    /// `Try::branch` on `Option`/`Result` (the `?` operator's test): moves the payload.
    TryBranch,
    /// `FromResidual::from_residual` building the `?` operator's early return: for `Option`
    /// (`None`), and for `Result` only when the residual's error type IS the return's error
    /// type (the identity `From`). A converting `From::from` is user code and is not listed.
    TryResidual,
    /// `PartialEq::eq` / `ne` on a primitive scalar, `()`, `str`, or a slice / array of
    /// primitive scalars: the std comparison (a string-pattern `match` is lowered byte-wise).
    /// Also the exact source-owned real core `ptr::eq` over two thin pointers,
    /// recognized by the SAME version/signature/target guard as its lowering.
    BuiltinEq,
    /// Core's `From<bool>` for primitive integers: exactly the total cast `b as Self`.
    BoolFromInteger,
    /// A `format_args!` CONSTRUCTOR — an inherent `new*` / `from_str` of `fmt::Arguments` or
    /// `fmt::rt::Argument` (lang items `format_arguments` / `format_argument`): it only packs
    /// references into a struct. The call that formats (`_print`, `write_fmt`, `panic_fmt`) is
    /// NOT on the list and must be paired.
    FormatArguments,
}

impl Equivalence {
    pub fn name(self) -> &'static str {
        match self {
            Equivalence::PureIntrinsic => "pure-intrinsic",
            Equivalence::SliceLen => "slice-len",
            Equivalence::RangeIntoIter => "range-into-iter",
            Equivalence::RangeNext => "range-next",
            Equivalence::OptionDiscriminant => "option-discriminant",
            Equivalence::TryBranch => "try-branch",
            Equivalence::TryResidual => "try-residual",
            Equivalence::BuiltinEq => "builtin-eq",
            Equivalence::BoolFromInteger => "bool-from-integer",
            Equivalence::FormatArguments => "format-arguments",
        }
    }
}

/// Intrinsics whose call is a pure value computation: no write through any pointer, no I/O, no
/// panic, no divergence. Anything not listed is treated as an effect and must be paired. The
/// `unchecked_*`/`exact_div` family is UB on a bad input, but UB is not an observable effect the
/// census tracks (the differentials and the verifier own it).
pub const PURE_INTRINSICS: &[&str] = &[
    "transmute",
    "transmute_unchecked",
    "size_of",
    "align_of",
    "min_align_of",
    "size_of_val",
    "align_of_val",
    "min_align_of_val",
    "needs_drop",
    "type_id",
    "type_name",
    "black_box",
    "assume",
    "likely",
    "unlikely",
    "cold_path",
    "ub_checks",
    "discriminant_value",
    "ctpop",
    "ctlz",
    "cttz",
    "ctlz_nonzero",
    "cttz_nonzero",
    "bswap",
    "bitreverse",
    "rotate_left",
    "rotate_right",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "add_with_overflow",
    "sub_with_overflow",
    "mul_with_overflow",
    "saturating_add",
    "saturating_sub",
    "unchecked_add",
    "unchecked_sub",
    "unchecked_mul",
    "unchecked_div",
    "unchecked_rem",
    "unchecked_shl",
    "unchecked_shr",
    "exact_div",
    "three_way_compare",
    "ptr_mask",
    "ptr_metadata",
    "aggregate_raw_ptr",
    "offset",
    "arith_offset",
];

/// The class of a panic check: what a MIR `Assert` terminator checks, and what the trust-ir
/// `Assert` the producer emits for it is annotated with (the `ProofAnnotation` both front ends
/// attach). A check pairs only with a check of its own class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AssertClass {
    /// `BoundsCheck` / `in_bounds`.
    Bounds,
    /// `Overflow(Add|Sub|Mul|Div|Rem)`, `OverflowNeg` / `no_overflow`.
    Overflow,
    /// `Overflow(Shl|Shr)` / `shift_in_range`.
    Shift,
    /// `DivisionByZero`, `RemainderByZero` / `div_nonzero`.
    DivZero,
    /// Any other check (none is built today: the rest are inserted by later passes); on the
    /// trust-ir side, an `Assert` with none of the four annotations.
    Other,
}

impl AssertClass {
    fn of_mir<O>(msg: &AssertKind<O>) -> AssertClass {
        match msg {
            AssertKind::BoundsCheck { .. } => AssertClass::Bounds,
            AssertKind::Overflow(mir::BinOp::Shl | mir::BinOp::Shr, ..) => AssertClass::Shift,
            AssertKind::Overflow(..) | AssertKind::OverflowNeg(_) => AssertClass::Overflow,
            AssertKind::DivisionByZero(_) | AssertKind::RemainderByZero(_) => AssertClass::DivZero,
            _ => AssertClass::Other,
        }
    }

    pub(crate) fn of_ir(proofs: &[ProofAnnotation]) -> AssertClass {
        for p in proofs {
            match p {
                ProofAnnotation::InBounds => return AssertClass::Bounds,
                ProofAnnotation::NoOverflow => return AssertClass::Overflow,
                ProofAnnotation::ShiftInRange => return AssertClass::Shift,
                ProofAnnotation::DivNonZero => return AssertClass::DivZero,
                _ => {}
            }
        }
        AssertClass::Other
    }

    /// The check, with its article: "a bounds check", "an overflow check".
    pub fn name(self) -> &'static str {
        match self {
            AssertClass::Bounds => "a bounds check",
            AssertClass::Overflow => "an overflow check",
            AssertClass::Shift => "a shift-amount check",
            AssertClass::DivZero => "a division-by-zero check",
            AssertClass::Other => "a panic check",
        }
    }
}

/// One effect of the MIR oracle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MirEffectKind<Identity = DefId, Site = Vec<SiteArg>> {
    /// A direct call. `ids` is every identity a faithful trust-ir call may carry for it: the
    /// `FnDef` the MIR operand spells first, then (for a `Fn*` trait call on a closure / fn item)
    /// that closure / fn. `site_args` is the operand's generic args in the producer's own
    /// lifetime-free encoding (`crate::encode_site_args`; `None` when it cannot spell them), so a
    /// trait-method call pairs only with a call at the SAME receiver and arguments — `<Foo as
    /// PartialEq>::eq` and `<str as PartialEq>::eq` share a `FnDef` and are different calls.
    /// `equivalence` is set when the callee is on the audited list. `enum_result` / `enum_args`:
    /// the call's destination / each argument is an enum with a value ([`is_valued_enum`]).
    Call {
        ids: Vec<Identity>,
        site_args: Option<Site>,
        equivalence: Option<Equivalence>,
        enum_result: bool,
        enum_args: Vec<bool>,
    },
    /// A call through a non-constant operand (a fn pointer, a closure value via a pointer).
    IndirectCall,
    Store(MemRoot),
    /// A live drop. `destructor`: its drop glue may run code beyond releasing memory — a `Drop`
    /// impl other than `Box`/`Vec`/`String`'s, or a type the census cannot see through (a
    /// generic, a trait object, a coroutine) ([`drop_runs_destructor`]).
    Drop {
        destructor: bool,
    },
    /// A panic check (`Assert` terminator): the program panics here when the check fails. A
    /// body whose trust-ir dropped it continues where the program stops.
    Assert(AssertClass),
    /// Inline asm. `empty_noreturn`: an `asm!` with NO template piece, NO operand and
    /// `options(noreturn)` — reaching it is undefined behaviour (it falls through at once) and it
    /// emits no instruction, so the producer's `unreachable` for it (wave-ASM, the audited arm in
    /// `lower_expr`) loses nothing in a UB-free execution. Any other asm must be paired.
    Asm {
        empty_noreturn: bool,
    },
    Yield,
}

#[derive(Clone, Debug)]
pub struct MirEffect<Identity = DefId, Site = Vec<SiteArg>, Location = Span> {
    pub kind: MirEffectKind<Identity, Site>,
    pub span: Location,
}

/// The MIR oracle's census of one body.
#[derive(Clone, Debug)]
pub struct MirCensus<
    Identity = DefId,
    Site = Vec<SiteArg>,
    Location = Span,
    Oracle = crate::drop_oracle::OracleDrop,
> {
    pub effects: Vec<MirEffect<Identity, Site, Location>>,
    /// The body's argument count (`Body::arg_count`), for store-root pairing.
    pub arg_count: u32,
    /// Per argument, and for the return place: is rustc's type an enum with a value
    /// ([`is_valued_enum`])? A lone `bool`/`()` in that position on the trust-ir side is then a
    /// placeholder for it.
    pub arg_enum: Vec<bool>,
    pub ret_enum: bool,
    /// Every escaping store (the `Store` effects, in order) with what rustc says it writes.
    pub store_values: Vec<(MemRoot, StoreValue)>,
    /// Store-only exact entry-argument copies, keyed by the original effect
    /// ordinal. Only an existing `Store(Indirect)` can be refined; private-store
    /// decisions and call equivalences remain coarse; placeholder-value checks
    /// use this same exact store correspondence.
    /// This input is retained explicitly in rmeta evidence schema 4.
    pub exact_store_args: BTreeMap<usize, u32>,
    /// The `type_id_hash` of every ENUM type this body holds BY VALUE somewhere: in its
    /// signature, in a value it reads or writes at any place, or in an aggregate whose field
    /// offsets or element stride an address computation uses (`(*p).1` steps into `*p`;
    /// [`PlaceTypes`]), looking through struct / tuple / array / slice / closure fields but never
    /// through a pointer. A place only borrowed (`&*o`, the caller's pointer passed on) holds
    /// nothing. Judged at finalize against every enum type the producer collapsed to a
    /// placeholder ([`ProducerBody::collapsed_enums`]): an enum the body holds is then spelled
    /// by the placeholder in its trust-ir, whichever position it sits in — a tuple, a struct
    /// literal, a stack slot, an array stride (D28).
    pub enum_types: BTreeSet<u128>,
    /// Trust (step 2 increment 4b): THE DROP ORACLE — every reachable normal-path `Drop` of the
    /// built body, elaborated exactly as rustc's `ElaborateDrops` will (`drop_oracle.rs`), with
    /// whether its glue may run a destructor ([`drop_runs_destructor`]). `None` when the oracle
    /// cannot run on this body (an unrevealed opaque, a coroutine); the drop leg then falls back
    /// to the by-count pairing of [`MirEffectKind::Drop`] and refuses any producer drop.
    pub drop_oracle: Option<Vec<(Oracle, bool)>>,
    /// The blocks of the `Drop` terminators this census's own init analysis found dead by
    /// construction ([`drop_is_live`] false). Cross-checked against the oracle: a drop the
    /// census calls dead and the oracle calls live is a census inconsistency (fail-closed).
    pub drop_dead_blocks: BTreeSet<u32>,
}

// Empty collections impose no Default requirement on their element types.
// The source lane retains its original Rustc identities, spans and oracle;
// retained metadata uses stable identities and its own ordinal vocabulary.
impl<Identity, Site, Location, Oracle> Default for MirCensus<Identity, Site, Location, Oracle> {
    fn default() -> Self {
        Self {
            effects: Vec::new(),
            arg_count: 0,
            arg_enum: Vec::new(),
            ret_enum: false,
            store_values: Vec::new(),
            exact_store_args: BTreeMap::new(),
            enum_types: BTreeSet::new(),
            drop_oracle: None,
            drop_dead_blocks: BTreeSet::new(),
        }
    }
}

/// What an escaping MIR store writes, by rustc's type of the place written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreValue {
    /// An enum with a value ([`is_valued_enum`]).
    ValuedEnum,
    /// A `bool` or `()`.
    BoolOrUnit,
    Other,
}

/// Where a trust-ir store's pointer comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IrRoot {
    Arg(u32),
    Global,
    Indirect,
    /// The body's own `Alloca` / fresh `HeapAlloc`: not an effect.
    Local,
}

/// One effect of the trust-ir side. The source location is carried for diagnostics only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IrEffectKind<Identity = DefId, Site = Vec<SiteArg>> {
    /// A direct call (`Call`/`Invoke`) with its ledger identities (site, then resolved).
    /// `site`: the MIR spelling the producer recorded for it (`CalleeRef::site_def_id` and
    /// `site_args`), when its args were encodable. `placeholder_result`: the call's result is a
    /// lone `bool` or `()` (the type the producer observed the site bind, `CalleeRef::ret_ty`,
    /// or the callee's declared result when the module carries the callee).
    /// `placeholder_params`: per ARGUMENT, is the value passed a `bool` or `()` (its type in
    /// this function)?
    Call {
        ids: Vec<Identity>,
        site: Option<(Identity, Site)>,
        placeholder_result: bool,
        placeholder_params: Vec<bool>,
    },
    /// A direct call to a function the ledger has no row for.
    UnledgeredCall,
    IndirectCall,
    Store(IrRoot),
    Drop,
    Asm,
    Suspend,
    /// A trust-ir `Assert`, classed by its proof annotation.
    Assert(AssertClass),
}

/// The value abstractions a body carries (D28). Counts, not booleans, so a report can say how
/// much of the body is a model. Where each reading comes from, precisely:
///
/// * `undefs` — the emitted trust-ir alone;
/// * `degraded_struct_touches` — the emitted trust-ir's instructions, typed with a struct the
///   producer's `rmw_degraded_structs` ledger names (written where the degraded profile is
///   minted);
/// * `union_lane`, `enum_param_lane` — the producer's own ledgers, written where each lane is
///   minted;
/// * `placeholder_values` — the emitted signature / call values against the MIR oracle's types;
/// * `collapsed_enum_values` — the MIR oracle's by-value enum types against the producer's
///   collapse ledger (`opaque_lane_tys`, written at the one `map_ty` arm that collapses).
///
/// The ledgers are read only where they are written at the mint, so a lane cannot be taken
/// without its entry; and the collapse ledger only names TYPES, which the oracle's own types
/// then place in the body. Deliberately NOT `Lowered::opaque_collapse`: that is the producer's
/// measurement flag, and it over-approximates — a discarded registration probe can set it while
/// every struct the body actually uses is faithful (measured: `trust_ir_lower_ptr_field_read.rs`'s
/// `x.r` reads carry the flag with `struct R { r: ptr @0, n: u32 @8 }` in the module). Nor "a
/// layout-less struct": a huge-array struct or a coroutine environment is registered without a
/// layout and is faithful.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Abstractions {
    pub undefs: usize,
    /// Instructions touching a struct the producer registered as a DEGRADED profile — one whose
    /// `Vec`/`String`/data-enum fields are `()` placeholders and whose non-pure `Option` fields
    /// are their discriminant `bool` (`LowerCx::rmw_degraded_structs`, the `struct_ty_rmw_opaque`
    /// build: the opaque `()` lane and the Option-discriminant lane).
    pub degraded_struct_touches: usize,
    /// The body carries a union placeholder lane (`Lowered::union_lane`, recorded where the
    /// producer mints it: `register_union_lane` / `register_union_value_lane`).
    pub union_lane: bool,
    /// The body carries an enum-parameter placeholder lane (`Lowered::enum_param_lane`,
    /// recorded where the producer mints it).
    pub enum_param_lane: bool,
    /// A parameter, the return value, or a call result that rustc types as an enum with a value
    /// is a lone `bool`/`()` here: a declined enum collapsed to its discriminant or to nothing
    /// (`map_ty`'s enum floor; the Option-discriminant lane in value position). Filled by
    /// [`placeholder_values`], which needs the MIR census.
    pub placeholder_values: usize,
    /// Enum types this body holds by value ([`MirCensus::enum_types`]) that the producer
    /// collapses to a lone `bool`/`()` placeholder ([`ProducerBody::collapsed_enums`], session
    /// wide). Filled at finalize. This is the position-independent reading of the
    /// Option-discriminant and opaque-`()` lanes: wherever such a value sits — a tuple, a struct
    /// literal, a stack slot passed by reference, an array element — the trust-ir spells it
    /// with fewer bytes than the program has.
    pub collapsed_enum_values: usize,
}

impl Abstractions {
    pub fn opaque_lane(&self) -> bool {
        self.degraded_struct_touches > 0
            || self.placeholder_values > 0
            || self.collapsed_enum_values > 0
    }
}

/// The two placeholder lanes the producer ledgers at their mint, handed to [`ir_census`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LedgeredLanes {
    pub union_lane: bool,
    pub enum_param_lane: bool,
}

/// The effect SHAPE of a trust-ir function, ledger-free: what the splice-consistency check
/// compares between the per-body function and the function crate assembly emitted for it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EffectShape {
    pub direct_calls: usize,
    pub indirect_calls: usize,
    pub escaping_stores: usize,
    pub drops: usize,
    pub undefs: usize,
    pub asm: usize,
    pub suspends: usize,
    pub asserts: usize,
}

/// The trust-ir side's census of one body. `PartialEq`: the template extraction check compares a
/// template's skolem census with its judged one (step 6.5.1, `rmeta_entry::build_template`).
#[derive(Clone, Debug, PartialEq)]
pub struct IrCensus<Identity = DefId, Site = Vec<SiteArg>> {
    pub effects: Vec<IrEffectKind<Identity, Site>>,
    pub param_count: u32,
    pub abstractions: Abstractions,
    pub shape: EffectShape,
    /// Per entry parameter, and for the result: is it a lone `bool`/`()`?
    pub param_placeholder: Vec<bool>,
    pub ret_placeholder: bool,
    /// The root of every escaping store whose value is a `bool` or `()`.
    pub placeholder_stores: Vec<IrRoot>,
}

impl<Identity, Site> Default for IrCensus<Identity, Site> {
    fn default() -> Self {
        Self {
            effects: Vec::new(),
            param_count: 0,
            abstractions: Abstractions::default(),
            shape: EffectShape::default(),
            param_placeholder: Vec::new(),
            ret_placeholder: false,
            placeholder_stores: Vec::new(),
        }
    }
}

/// What a finding is about. Every [`Tag`] has exactly one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TagKind {
    /// An effect of the MIR census the trust-ir does not carry.
    NotConserved(Effect),
    /// A value abstraction (D28).
    Abstracted(Lane),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Effect {
    Call,
    IndirectCall,
    Store,
    Asm,
    Yield,
    /// A panic check (`Assert`) of the MIR the trust-ir does not carry.
    Assert,
    /// Trust (step 2 increment 4b): the body carries a drop the program does not perform (a
    /// drop the drop oracle has no counterpart for: an extra, misplaced or wrongly styled drop),
    /// or its `Inst::Drop`s are not the ones the producer recorded emitting. An ELIDED drop is
    /// [`Lane::Drop`] (`abstracted(drop)`), as before.
    Drop,
    /// The assembled function's effect shape differs from the per-body function's.
    Splice,
    /// The census itself is missing or inconsistent (fail-closed).
    Census,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lane {
    /// A live MIR drop the trust-ir does not carry.
    Drop,
    /// Beside `Drop`: an elided drop whose glue may run a DESTRUCTOR — code beyond releasing
    /// memory (a `Drop` impl other than `Box`/`Vec`/`String`'s: a guard's unlock, an fd's close;
    /// or a type the census cannot see through). A reader that models only memory may accept
    /// `drop`; it must not accept this one without modelling the destructor.
    Destructor,
    Undef,
    /// An enum collapsed to a lone `bool` (the Option-discriminant lane) or `()` (the opaque
    /// lane), in value position or inside a struct / tuple / slot, or a degraded struct profile.
    OpaqueLane,
    /// A union placeholder lane (a union field or value spelled `()`).
    UnionLane,
    /// A bare-type-parameter placeholder field inside an enum (spelled `()`).
    EnumParamLane,
}

impl Effect {
    pub fn name(self) -> &'static str {
        match self {
            Effect::Call => "call",
            Effect::IndirectCall => "indirect-call",
            Effect::Store => "store",
            Effect::Asm => "asm",
            Effect::Yield => "yield",
            Effect::Assert => "assert",
            Effect::Drop => "drop",
            Effect::Splice => "splice",
            Effect::Census => "census",
        }
    }
}

impl Lane {
    pub fn name(self) -> &'static str {
        match self {
            Lane::Drop => "drop",
            Lane::Destructor => "destructor",
            Lane::Undef => "undef",
            Lane::OpaqueLane => "opaque-lane",
            Lane::UnionLane => "union-lane",
            Lane::EnumParamLane => "enum-param-lane",
        }
    }
}

impl TagKind {
    /// The short class label: `not-conserved(call)`, `abstracted(drop)`. This is the spelling
    /// channel C, the sidecar and a consumer's acceptance list use.
    pub fn label(self) -> String {
        match self {
            TagKind::NotConserved(e) => format!("not-conserved({})", e.name()),
            TagKind::Abstracted(l) => format!("abstracted({})", l.name()),
        }
    }

    /// Parse a [`TagKind::label`] back. `None` for anything else, so an acceptance list with a
    /// typo accepts nothing.
    pub fn from_label(label: &str) -> Option<TagKind> {
        const EFFECTS: [Effect; 9] = [
            Effect::Call,
            Effect::IndirectCall,
            Effect::Store,
            Effect::Asm,
            Effect::Yield,
            Effect::Assert,
            Effect::Drop,
            Effect::Splice,
            Effect::Census,
        ];
        const LANES: [Lane; 6] = [
            Lane::Drop,
            Lane::Destructor,
            Lane::Undef,
            Lane::OpaqueLane,
            Lane::UnionLane,
            Lane::EnumParamLane,
        ];
        EFFECTS
            .into_iter()
            .map(TagKind::NotConserved)
            .chain(LANES.into_iter().map(TagKind::Abstracted))
            .find(|k| k.label() == label)
    }
}

/// One finding: what, and where (a rendered site such as "`close` at p7.rs:6:13").
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tag {
    pub kind: TagKind,
    pub site: String,
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let head = match self.kind {
            TagKind::NotConserved(e) => format!("EffectNotConserved({}", e.name()),
            TagKind::Abstracted(l) => format!("Abstracted({}", l.name()),
        };
        if self.site.is_empty() {
            write!(f, "{head})")
        } else {
            write!(f, "{head}, {})", self.site)
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The matcher. Pure.
// ---------------------------------------------------------------------------------------------

/// An unpaired MIR effect: which effect (index into `MirCensus::effects`) and its tag kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unpaired {
    pub mir_index: usize,
    pub kind: TagKind,
}

/// May the trust-ir call `ir_call` stand for the MIR call `mir_call`?
///
/// * When both sides spell the site's generic args (the MIR operand's, and the producer's
///   recorded `site_args`) and the trust-ir site is the MIR `FnDef`: exactly when the args are
///   equal. A trait method's `FnDef` is shared by every impl (`<Foo as PartialEq>::eq` and
///   `<str as PartialEq>::eq`), so the receiver lives in the args, and a `DefId` alone would let
///   an exempt `str` comparison stand for a lost user `eq`.
/// * Otherwise (a generic site, a closure / reify / havoc admission the producer records
///   without a site, a `Fn*` call the producer lowers as a direct call of the closure): any
///   shared identity, except that two fully-spelled sites with different `FnDef`s pair only
///   through the closure / fn item a `Fn*` call carries.
fn call_admits<Identity: Eq, Site: Eq>(
    mir_call: &MirEffectKind<Identity, Site>,
    ir_call: &IrEffectKind<Identity, Site>,
) -> bool {
    let MirEffectKind::Call { ids, site_args, .. } = mir_call else { return false };
    let IrEffectKind::Call { ids: irs, site, .. } = ir_call else { return false };
    if let (Some(margs), Some((site_def, iargs))) = (site_args, site) {
        if ids.first() == Some(site_def) {
            return margs == iargs;
        }
        let carried = ids.get(1..).unwrap_or(&[]);
        return irs.iter().any(|d| carried.contains(d));
    }
    irs.iter().any(|d| ids.contains(d))
}

/// The call pairing: for each trust-ir effect, the MIR call it is paired with. A MAXIMUM
/// matching (Kuhn's augmenting paths) over [`call_admits`], so that a MIR call with two
/// admissible identities (a `Fn*` call: the trait method and the closure) cannot take the only
/// trust-ir call another MIR call could pair with. Calls with NO audited equivalence are matched
/// first: an augmenting path never unmatches a MIR call, so the effectful calls get a maximum
/// matching of their own, and an exempt call (which may stay unpaired) only takes what is left —
/// it can never cost an effectful call its partner.
fn match_calls<Identity: Eq, Site: Eq, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
    ir: &IrCensus<Identity, Site>,
) -> Vec<Option<usize>> {
    let admits =
        |mi: usize, ii: usize| -> bool { call_admits(&mir.effects[mi].kind, &ir.effects[ii]) };
    fn augment(
        mi: usize,
        admits: &dyn Fn(usize, usize) -> bool,
        owner: &mut Vec<Option<usize>>,
        seen: &mut Vec<bool>,
    ) -> bool {
        for ii in 0..owner.len() {
            if seen[ii] || !admits(mi, ii) {
                continue;
            }
            seen[ii] = true;
            let current = owner[ii];
            if current.is_none_or(|other| augment(other, admits, owner, seen)) {
                owner[ii] = Some(mi);
                return true;
            }
        }
        false
    }
    let mut owner: Vec<Option<usize>> = vec![None; ir.effects.len()];
    for exempt_pass in [false, true] {
        for (mi, e) in mir.effects.iter().enumerate() {
            if let MirEffectKind::Call { equivalence, .. } = &e.kind {
                if equivalence.is_some() == exempt_pass {
                    let mut seen = vec![false; ir.effects.len()];
                    augment(mi, &admits, &mut owner, &mut seen);
                }
            }
        }
    }
    owner
}

fn unpaired_equivalences<Identity: Eq, Site: Eq, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
    ir: &IrCensus<Identity, Site>,
) -> BTreeMap<&'static str, usize> {
    let owner = match_calls(mir, ir);
    let paired: BTreeSet<usize> = owner.iter().flatten().copied().collect();
    let mut equivalences = BTreeMap::new();
    for (mi, e) in mir.effects.iter().enumerate() {
        if let MirEffectKind::Call { equivalence: Some(eq), .. } = &e.kind {
            if !paired.contains(&mi) {
                *equivalences.entry(eq.name()).or_insert(0) += 1;
            }
        }
    }
    equivalences
}

/// Does a MIR store root correspond to a trust-ir store root? The store pairing's rule
/// ([`unpaired_effects`]): parameter `i` to parameter `i` (any parameter when the two lists do not
/// line up), a static or loaded pointer to a global or loaded pointer.
fn roots_correspond(mir_root: MemRoot, ir_root: IrRoot, pool_args: bool) -> bool {
    match (mir_root, ir_root) {
        (MemRoot::Arg(i), IrRoot::Arg(j)) => pool_args || i == j,
        (MemRoot::Static | MemRoot::Indirect, IrRoot::Global | IrRoot::Indirect) => true,
        _ => false,
    }
}

// `store_values` is ordered like Store effects. Exact facts use that SAME
// effect ordinal in both conservation and enum-placeholder checks. A malformed
// association cannot gain precision or authorize an argument-root match.
fn exact_store_values_bound<Identity, Site, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
) -> bool {
    let roots: Vec<_> = mir
        .effects
        .iter()
        .filter_map(|effect| match effect.kind {
            MirEffectKind::Store(root) => Some(root),
            _ => None,
        })
        .collect();
    roots.len() == mir.store_values.len()
        && roots.iter().zip(&mir.store_values).all(|(root, (value_root, _))| root == value_root)
}

fn store_roots_correspond<Identity, Site, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
    ir: &IrCensus<Identity, Site>,
    exact_values_bound: bool,
    effect: usize,
    root: MemRoot,
    ir_root: IrRoot,
) -> bool {
    if let Some(&argument) = mir.exact_store_args.get(&effect) {
        return root == MemRoot::Indirect
            && exact_values_bound
            && exact_store::corresponds(
                argument,
                mir.arg_count,
                ir.param_count,
                match ir_root {
                    IrRoot::Arg(i) => Some(i),
                    _ => None,
                },
            );
    }
    roots_correspond(root, ir_root, mir.arg_count != ir.param_count)
}

/// How many values rustc types as an enum with a value are a lone `bool`/`()` placeholder in the
/// trust-ir (the Option-discriminant lane and `map_ty`'s enum floor in VALUE position):
///
/// * a parameter (when the two parameter lists line up) and the result;
/// * the result and each argument of every PAIRED call (positionally when the argument lists
///   line up; otherwise any enum argument against any `bool`/`()` parameter counts once);
/// * an escaping `bool`/`()` store to a root the program writes an enum to and never a
///   `bool`/`()` — `*slot = None` stored as one `false` byte.
pub fn placeholder_values<Identity: Eq, Site: Eq, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
    ir: &IrCensus<Identity, Site>,
) -> usize {
    let mut n = 0;
    if mir.arg_enum.len() == ir.param_placeholder.len() {
        n += mir.arg_enum.iter().zip(&ir.param_placeholder).filter(|(e, p)| **e && **p).count();
    }
    n += usize::from(mir.ret_enum && ir.ret_placeholder);
    for (ii, o) in match_calls(mir, ir).iter().enumerate() {
        let Some(mi) = o else { continue };
        let MirEffectKind::Call { enum_result, enum_args, .. } = &mir.effects[*mi].kind else {
            continue;
        };
        let IrEffectKind::Call { placeholder_result, placeholder_params, .. } = &ir.effects[ii]
        else {
            continue;
        };
        n += usize::from(*enum_result && *placeholder_result);
        if enum_args.len() == placeholder_params.len() {
            n += enum_args.iter().zip(placeholder_params).filter(|(e, p)| **e && **p).count();
        } else {
            n += usize::from(enum_args.iter().any(|e| *e) && placeholder_params.iter().any(|p| *p));
        }
    }
    let store_effects: Vec<usize> = mir
        .effects
        .iter()
        .enumerate()
        .filter_map(|(i, effect)| matches!(effect.kind, MirEffectKind::Store(_)).then_some(i))
        .collect();
    let exact_values_bound = mir.exact_store_args.is_empty() || exact_store_values_bound(mir);
    for &r in &ir.placeholder_stores {
        let written = |want: StoreValue| {
            mir.store_values.iter().enumerate().any(|(ordinal, (root, value))| {
                *value == want
                    && match store_effects.get(ordinal) {
                        Some(&effect) => {
                            store_roots_correspond(mir, ir, exact_values_bound, effect, *root, r)
                        }
                        // Preserve the legacy coarse diagnostic for fixture/old
                        // censuses that carry store values without store effects.
                        None => roots_correspond(*root, r, mir.arg_count != ir.param_count),
                    }
            })
        };
        n += usize::from(written(StoreValue::ValuedEnum) && !written(StoreValue::BoolOrUnit));
    }
    n
}

/// Pair every MIR effect with a trust-ir effect. Returns the MIR effects left unpaired, in MIR
/// order. Extra trust-ir effects are not reported (see the module doc).

pub fn unpaired_effects<Identity: Eq, Site: Eq, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
    ir: &IrCensus<Identity, Site>,
) -> Vec<Unpaired> {
    let mut used = vec![false; ir.effects.len()];
    let mut out = Vec::new();

    // Direct calls by identity: a MAXIMUM matching ([`match_calls`]).
    let owner = match_calls(mir, ir);
    let calls: Vec<usize> = mir
        .effects
        .iter()
        .enumerate()
        .filter(|(_, e)| matches!(e.kind, MirEffectKind::Call { .. }))
        .map(|(mi, _)| mi)
        .collect();
    let mut paired_calls = BTreeSet::new();
    for (ii, o) in owner.iter().enumerate() {
        if let Some(mi) = o {
            used[ii] = true;
            paired_calls.insert(*mi);
        }
    }
    for &mi in &calls {
        let MirEffectKind::Call { equivalence, .. } = &mir.effects[mi].kind else { continue };
        if !paired_calls.contains(&mi) && equivalence.is_none() {
            out.push(Unpaired { mir_index: mi, kind: TagKind::NotConserved(Effect::Call) });
        }
    }
    // Indirect calls: a trust-ir `CallIndirect` first, then an unledgered direct call.
    for (mi, e) in mir.effects.iter().enumerate() {
        if e.kind != MirEffectKind::IndirectCall {
            continue;
        }
        let pick = |want: &dyn Fn(&IrEffectKind<Identity, Site>) -> bool, used: &[bool]| {
            ir.effects.iter().enumerate().position(|(ii, ie)| !used[ii] && want(ie))
        };
        let hit = pick(&|ie| *ie == IrEffectKind::IndirectCall, &used)
            .or_else(|| pick(&|ie| *ie == IrEffectKind::UnledgeredCall, &used));
        match hit {
            Some(ii) => used[ii] = true,
            None => out.push(Unpaired {
                mir_index: mi,
                kind: TagKind::NotConserved(Effect::IndirectCall),
            }),
        }
    }
    // Stores by root.
    let exact_values_bound = mir.exact_store_args.is_empty() || exact_store_values_bound(mir);
    for (mi, e) in mir.effects.iter().enumerate() {
        let MirEffectKind::Store(root) = e.kind else { continue };
        let accepts = |ie: &IrEffectKind<Identity, Site>| -> bool {
            matches!(ie, IrEffectKind::Store(r) if store_roots_correspond(mir, ir, exact_values_bound, mi, root, *r))
        };
        let hit = ir.effects.iter().enumerate().position(|(ii, ie)| !used[ii] && accepts(ie));
        match hit {
            Some(ii) => used[ii] = true,
            None => {
                out.push(Unpaired { mir_index: mi, kind: TagKind::NotConserved(Effect::Store) })
            }
        }
    }
    // Drops, asm, yields: by count; panic checks: by count within their class.
    let mut unpaired_drop = false;
    for (mi, e) in mir.effects.iter().enumerate() {
        let (want, kind) = match &e.kind {
            MirEffectKind::Drop { .. } => (IrEffectKind::Drop, TagKind::Abstracted(Lane::Drop)),
            MirEffectKind::Asm { .. } => (IrEffectKind::Asm, TagKind::NotConserved(Effect::Asm)),
            MirEffectKind::Yield => (IrEffectKind::Suspend, TagKind::NotConserved(Effect::Yield)),
            MirEffectKind::Assert(class) => {
                (IrEffectKind::Assert(*class), TagKind::NotConserved(Effect::Assert))
            }
            _ => continue,
        };
        let hit = ir.effects.iter().enumerate().position(|(ii, ie)| !used[ii] && *ie == want);
        match hit {
            Some(ii) => used[ii] = true,
            None if matches!(e.kind, MirEffectKind::Asm { empty_noreturn: true }) => {}
            None => {
                unpaired_drop |= matches!(e.kind, MirEffectKind::Drop { .. });
                out.push(Unpaired { mir_index: mi, kind })
            }
        }
    }
    // An elided drop whose glue may run a destructor. trust-ir's `Drop` does not name the
    // program's type, so WHICH drop is missing is unknown: when any is, and any live drop of the
    // body runs a destructor, the missing one may be that one.
    if unpaired_drop {
        if let Some(mi) = mir
            .effects
            .iter()
            .position(|e| matches!(e.kind, MirEffectKind::Drop { destructor: true }))
        {
            out.push(Unpaired { mir_index: mi, kind: TagKind::Abstracted(Lane::Destructor) });
        }
    }
    out.sort_by_key(|u| u.mir_index);
    out
}

/// The abstraction tag kinds a census carries (D28), in a fixed order.
pub fn abstraction_kinds(a: &Abstractions) -> Vec<TagKind> {
    let mut out = Vec::new();
    if a.undefs > 0 {
        out.push(TagKind::Abstracted(Lane::Undef));
    }
    if a.opaque_lane() {
        out.push(TagKind::Abstracted(Lane::OpaqueLane));
    }
    if a.union_lane {
        out.push(TagKind::Abstracted(Lane::UnionLane));
    }
    if a.enum_param_lane {
        out.push(TagKind::Abstracted(Lane::EnumParamLane));
    }
    out
}

// ---------------------------------------------------------------------------------------------
// The drop leg (step 2 increment 4b). Pure.
// ---------------------------------------------------------------------------------------------

/// One drop of either side, as the drop leg compares it.
pub use crate::drops::DropKey;

/// The drop leg's finding for one body. Every list indexes the side it names.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DropComparison {
    /// Live drops of the oracle the producer's claim lacks (elided): `abstracted(drop)`.
    pub missing: Vec<usize>,
    /// Drops the producer claims that the oracle has no counterpart for (extra, misplaced or
    /// wrongly styled): `not-conserved(drop)`.
    pub extra: Vec<usize>,
    /// `(recorded, carried)`: the producer recorded emitting `recorded` drops and the module
    /// carries `carried` `Inst::Drop`s. A mismatch is `not-conserved(drop)`.
    pub ledger: Option<(usize, usize)>,
}

/// Compare the oracle's live drops with the producer's claim, as MULTISETS of [`DropKey`]
/// (identity, type, span, style): "the same places dropped at the same points" (design §3.5).
/// With no claim the producer emitted nothing, and every oracle drop is missing.
pub fn compare_drops<Key: PartialEq>(
    oracle: &[Key],
    claim: Option<(&[Key], usize)>,
    carried: usize,
) -> DropComparison {
    let mut out = DropComparison::default();
    let (claimed, recorded) = claim.unwrap_or((&[], 0));
    let mut used = vec![false; claimed.len()];
    for (i, k) in oracle.iter().enumerate() {
        match claimed.iter().enumerate().position(|(j, c)| !used[j] && c == k) {
            Some(j) => used[j] = true,
            None => out.missing.push(i),
        }
    }
    out.extra = used.iter().enumerate().filter(|(_, u)| !**u).map(|(j, _)| j).collect();
    if recorded != carried {
        out.ledger = Some((recorded, carried));
    }
    out
}

// ---------------------------------------------------------------------------------------------
// The trust-ir census.
// ---------------------------------------------------------------------------------------------

/// Blocks of `f` reachable from its entry along terminator edges, by position.
pub(crate) fn ir_reachable(f: &Function) -> Vec<bool> {
    let index: HashMap<BlockId, usize> =
        f.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    let mut seen = vec![false; f.blocks.len()];
    let Some(&start) = index.get(&f.entry) else { return seen };
    let mut stack = vec![start];
    while let Some(i) = stack.pop() {
        if std::mem::replace(&mut seen[i], true) {
            continue;
        }
        for node in &f.blocks[i].body {
            for t in ir_targets(&node.inst) {
                if let Some(&j) = index.get(&t) {
                    stack.push(j);
                }
            }
        }
    }
    seen
}

fn ir_targets(inst: &Inst) -> Vec<BlockId> {
    match inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr { then_target, else_target, .. } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut v = vec![*default];
            v.extend(cases.iter().map(|c| c.target));
            v
        }
        Inst::Invoke { normal_dest, unwind_dest, .. } => vec![*normal_dest, *unwind_dest],
        _ => Vec::new(),
    }
}

/// The incoming arguments of every block parameter, from every branch in `f`.
fn ir_block_arg_sources(f: &Function) -> HashMap<ValueId, Vec<ValueId>> {
    let params: HashMap<BlockId, Vec<ValueId>> =
        f.blocks.iter().map(|b| (b.id, b.params.iter().map(|(v, _)| *v).collect())).collect();
    let mut out: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    let mut bind = |target: &BlockId, args: &[ValueId]| {
        if let Some(ps) = params.get(target) {
            for (p, a) in ps.iter().zip(args) {
                out.entry(*p).or_default().push(*a);
            }
        }
    };
    for node in f.blocks.iter().flat_map(|b| b.body.iter()) {
        match &node.inst {
            Inst::Br { target, args } => bind(target, args),
            Inst::CondBr { then_target, then_args, else_target, else_args, .. } => {
                bind(then_target, then_args);
                bind(else_target, else_args);
            }
            Inst::Switch { default, default_args, cases, .. } => {
                bind(default, default_args);
                for c in cases {
                    bind(&c.target, &c.args);
                }
            }
            Inst::Invoke { normal_dest, normal_args, .. } => bind(normal_dest, normal_args),
            _ => {}
        }
    }
    out
}

/// The pointer ROOT of every value of `f` (see [`IrRoot`]), by a monotone fixpoint over a flat
/// lattice: unknown < {Arg(i), Global, Local, Indirect}; two different roots join to Indirect.
pub(crate) fn ir_roots(f: &Function) -> HashMap<ValueId, IrRoot> {
    fn join(a: Option<IrRoot>, b: IrRoot) -> IrRoot {
        match a {
            None => b,
            Some(x) if x == b => x,
            Some(_) => IrRoot::Indirect,
        }
    }
    let mut roots: HashMap<ValueId, IrRoot> = HashMap::new();
    if let Some(entry) = f.blocks.iter().find(|b| b.id == f.entry) {
        for (i, (v, _)) in entry.params.iter().enumerate() {
            roots.insert(*v, IrRoot::Arg(i as u32));
        }
    }
    let incoming = ir_block_arg_sources(f);
    let entry_params: BTreeSet<ValueId> = f
        .blocks
        .iter()
        .find(|b| b.id == f.entry)
        .map(|b| b.params.iter().map(|(v, _)| *v).collect())
        .unwrap_or_default();
    // Bounded: every value can change at most twice (unknown -> root -> Indirect).
    for _ in 0..(2 * f.blocks.iter().map(|b| b.body.len() + b.params.len()).sum::<usize>() + 2) {
        let mut changed = false;
        let mut set = |roots: &mut HashMap<ValueId, IrRoot>, v: ValueId, r: IrRoot| {
            let new = join(roots.get(&v).copied(), r);
            if roots.get(&v) != Some(&new) {
                roots.insert(v, new);
                changed = true;
            }
        };
        for b in &f.blocks {
            for (p, _) in &b.params {
                if entry_params.contains(p) {
                    continue;
                }
                for src in incoming.get(p).map(Vec::as_slice).unwrap_or(&[]) {
                    if let Some(r) = roots.get(src).copied() {
                        set(&mut roots, *p, r);
                    }
                }
            }
            for node in &b.body {
                let Some(&res) = node.results.first() else { continue };
                let from = |v: &ValueId, roots: &HashMap<ValueId, IrRoot>| roots.get(v).copied();
                let r = match &node.inst {
                    Inst::GEP { base, .. } => from(base, &roots),
                    Inst::Copy { operand, .. } | Inst::Cast { operand, .. } => {
                        from(operand, &roots)
                    }
                    Inst::Borrow { ptr } | Inst::BorrowMut { ptr } | Inst::PtrData { ptr, .. } => {
                        from(ptr, &roots)
                    }
                    Inst::PtrFromParts { data, .. } => from(data, &roots),
                    Inst::ExtractField { aggregate, .. } => match from(aggregate, &roots) {
                        Some(IrRoot::Arg(i)) => Some(IrRoot::Arg(i)),
                        Some(_) => Some(IrRoot::Indirect),
                        None => None,
                    },
                    Inst::Select { then_val, else_val, .. } => {
                        match (from(then_val, &roots), from(else_val, &roots)) {
                            (Some(a), Some(b)) => Some(join(Some(a), b)),
                            (Some(a), None) | (None, Some(a)) => Some(a),
                            (None, None) => None,
                        }
                    }
                    Inst::GlobalAddr { .. } => Some(IrRoot::Global),
                    Inst::Alloca { .. } | Inst::HeapAlloc { .. } => Some(IrRoot::Local),
                    _ => Some(IrRoot::Indirect),
                };
                if let Some(r) = r {
                    set(&mut roots, res, r);
                }
            }
        }
        if !changed {
            break;
        }
    }
    roots
}

/// One callee row of the producer's ledger, as the census reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LedgerRow<Identity = DefId, Site = Vec<SiteArg>> {
    /// The identities a MIR call may pair through: the site `DefId`, then the resolved one.
    pub ids: Vec<Identity>,
    /// The site `DefId` and its encoded generic args, when the producer could encode them.
    pub site: Option<(Identity, Site)>,
}

impl<Identity, Site> Default for LedgerRow<Identity, Site> {
    fn default() -> Self {
        Self { ids: Vec::new(), site: None }
    }
}

impl LedgerRow {
    /// A row with identities only (no encodable site).
    pub fn ids(ids: Vec<DefId>) -> LedgerRow {
        LedgerRow { ids, site: None }
    }
}

/// The trust-ir census of `f`, a function of `module`. `ledger` maps a callee `FuncId` to the
/// identities the producer recorded for it, and `callee_returns` to the result type it observed
/// the call sites bind (`CalleeRef::ret_ty`: a per-body module carries no callee declaration);
/// `degraded` is the producer's set of degraded struct profiles (`LowerCx::rmw_degraded_structs`);
/// `lanes` says the lowering took a union or enum-parameter placeholder lane.
pub fn ir_census(
    module: &Module,
    f: &Function,
    ledger: &BTreeMap<FuncId, LedgerRow>,
    callee_returns: &BTreeMap<FuncId, Ty>,
    degraded: &BTreeSet<StructId>,
    lanes: LedgeredLanes,
) -> IrCensus {
    ir_census_with_identities(module, f, ledger, callee_returns, degraded, lanes)
}

/// The same census over independent identity/site representations. The local
/// wrapper above preserves its Rustc-typed API; a metadata reader supplies only
/// decoded stable identities and never invents DefIds or source spans.
pub fn ir_census_with_identities<Identity: Clone, Site: Clone>(
    module: &Module,
    f: &Function,
    ledger: &BTreeMap<FuncId, LedgerRow<Identity, Site>>,
    callee_returns: &BTreeMap<FuncId, Ty>,
    degraded: &BTreeSet<StructId>,
    lanes: LedgeredLanes,
) -> IrCensus<Identity, Site> {
    let reachable = ir_reachable(f);
    let roots = ir_roots(f);
    let entry_params: Vec<&Ty> = f
        .blocks
        .iter()
        .find(|b| b.id == f.entry)
        .map(|b| b.params.iter().map(|(_, t)| t).collect())
        .unwrap_or_default();
    let placeholder = |t: &Ty| matches!(t, Ty::Bool | Ty::Unit);
    let lone_placeholder = |tys: &[Ty]| -> bool { matches!(tys, [t] if placeholder(t)) };
    let ret_placeholder =
        module.func_types.get(f.ty.as_usize()).is_some_and(|ft| lone_placeholder(&ft.returns));
    let degraded_ty = |ty: &Ty| matches!(ty, Ty::Struct(sid) if degraded.contains(sid));
    let callee_returns_placeholder = |callee: &FuncId| -> bool {
        match callee_returns.get(callee) {
            Some(t) => placeholder(t),
            None => module
                .function_by_id(*callee)
                .filter(|g| g.id != f.id)
                .and_then(|g| module.func_types.get(g.ty.as_usize()))
                .is_some_and(|ft| lone_placeholder(&ft.returns)),
        }
    };
    // Every value's type: block parameters and each instruction's declared results.
    let mut value_ty: HashMap<ValueId, Ty> = HashMap::new();
    for b in &f.blocks {
        for (v, t) in &b.params {
            value_ty.insert(*v, t.clone());
        }
        for node in &b.body {
            for (v, t) in node.results.iter().zip(node.result_tys(module)) {
                value_ty.insert(*v, t);
            }
        }
    }
    let root_of = |v: &ValueId| roots.get(v).copied().unwrap_or(IrRoot::Indirect);
    let mut census = IrCensus {
        param_count: entry_params.len() as u32,
        param_placeholder: entry_params.iter().map(|t| placeholder(t)).collect(),
        ret_placeholder,
        abstractions: Abstractions {
            union_lane: lanes.union_lane,
            enum_param_lane: lanes.enum_param_lane,
            ..Abstractions::default()
        },
        ..IrCensus::default()
    };
    for (bi, b) in f.blocks.iter().enumerate() {
        if !reachable[bi] {
            continue;
        }
        for node in &b.body {
            let store = |ptr: &ValueId| IrEffectKind::Store(root_of(ptr));
            let effect = match &node.inst {
                Inst::Call { callee, args, .. } | Inst::Invoke { callee, args, .. } => {
                    census.shape.direct_calls += 1;
                    Some(match ledger.get(callee) {
                        Some(row) => IrEffectKind::Call {
                            ids: row.ids.clone(),
                            site: row.site.clone(),
                            placeholder_result: callee_returns_placeholder(callee),
                            placeholder_params: args
                                .iter()
                                .map(|a| value_ty.get(a).is_some_and(placeholder))
                                .collect(),
                        },
                        None => IrEffectKind::UnledgeredCall,
                    })
                }
                Inst::SeqMap { .. } => {
                    census.shape.direct_calls += 1;
                    Some(IrEffectKind::UnledgeredCall)
                }
                Inst::CallIndirect { .. } => {
                    census.shape.indirect_calls += 1;
                    Some(IrEffectKind::IndirectCall)
                }
                Inst::Store { ptr, .. }
                | Inst::AtomicStore { ptr, .. }
                | Inst::AtomicRMW { ptr, .. }
                | Inst::CmpXchg { ptr, .. } => Some(store(ptr)),
                Inst::MemCopy { dst, .. } | Inst::MemSet { dst, .. } => Some(store(dst)),
                Inst::Drop { .. } => {
                    census.shape.drops += 1;
                    Some(IrEffectKind::Drop)
                }
                Inst::CoroSuspend { .. } => {
                    census.shape.suspends += 1;
                    Some(IrEffectKind::Suspend)
                }
                Inst::DialectOp(_) => {
                    census.shape.asm += 1;
                    Some(IrEffectKind::Asm)
                }
                Inst::Assert { .. } => {
                    census.shape.asserts += 1;
                    Some(IrEffectKind::Assert(AssertClass::of_ir(&node.proofs)))
                }
                _ => None,
            };
            if let Some(IrEffectKind::Store(r)) = &effect {
                if *r != IrRoot::Local {
                    census.shape.escaping_stores += 1;
                    if matches!(&node.inst, Inst::Store { ty, .. } if placeholder(ty)) {
                        census.placeholder_stores.push(*r);
                    }
                }
            }
            if let Some(e) = effect {
                census.effects.push(e);
            }
            match &node.inst {
                Inst::Undef { ty } => {
                    census.abstractions.undefs += 1;
                    census.shape.undefs += 1;
                    census.abstractions.degraded_struct_touches += usize::from(degraded_ty(ty));
                }
                Inst::Load { ty, .. }
                | Inst::Store { ty, .. }
                | Inst::InsertField { ty, .. }
                | Inst::ExtractField { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::Alloca { ty, .. } => {
                    census.abstractions.degraded_struct_touches += usize::from(degraded_ty(ty));
                }
                _ => {}
            }
        }
    }
    census
}

/// The ledger-free effect shape of `f` (its census with no identities).
pub fn ir_shape(module: &Module, f: &Function) -> EffectShape {
    ir_census(
        module,
        f,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
        LedgeredLanes::default(),
    )
    .shape
}

// ---------------------------------------------------------------------------------------------
// The MIR census (needs a TyCtxt).
// ---------------------------------------------------------------------------------------------

/// Calls whose destination type is uninhabited: their return edge is dead. The built body still
/// carries it — `LintAndRemoveUninhabited`, the first pass of the `mir_built` provider, removes it
/// right after this census is taken — so the census follows the same rule that pass applies
/// (inhabitedness as the calling module sees it), or the code after `panic!()` would count.
fn uninhabited_returns<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> BTreeSet<BasicBlock> {
    let Some(def_id) = body.source.def_id().as_local() else { return BTreeSet::new() };
    let parent_module = tcx.parent_module_from_def_id(def_id);
    let typing_env = body.typing_env(tcx);
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(bb, data)| match &data.terminator.as_ref()?.kind {
            TerminatorKind::Call { target: Some(_), destination, .. } => {
                let ty = destination.ty(&body.local_decls, tcx).ty;
                (!ty.is_inhabited_from(tcx, parent_module, typing_env)).then_some(bb)
            }
            _ => None,
        })
        .collect()
}

/// The REAL successors of `bb`: imaginary `FalseEdge`/`FalseUnwind` targets and the dead return
/// edge of a call into an uninhabited type are not followed, nor is any cleanup block.
fn real_successors(
    body: &Body<'_>,
    bb: BasicBlock,
    no_return: &BTreeSet<BasicBlock>,
) -> Vec<BasicBlock> {
    let Some(term) = &body.basic_blocks[bb].terminator else { return Vec::new() };
    let succs: Vec<BasicBlock> = match &term.kind {
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        TerminatorKind::Call { .. } if no_return.contains(&bb) => Vec::new(),
        other => other.successors().collect(),
    };
    succs.into_iter().filter(|s| !body.basic_blocks[*s].is_cleanup).collect()
}

/// Blocks reachable from `START_BLOCK` along REAL edges ([`real_successors`]).
fn mir_reachable(body: &Body<'_>, no_return: &BTreeSet<BasicBlock>) -> Vec<bool> {
    let n = body.basic_blocks.len();
    let mut seen = vec![false; n];
    let mut stack = vec![mir::START_BLOCK];
    while let Some(bb) = stack.pop() {
        if body.basic_blocks[bb].is_cleanup || std::mem::replace(&mut seen[bb.as_usize()], true) {
            continue;
        }
        stack.extend(real_successors(body, bb, no_return));
    }
    seen
}

/// The pointer root of every local, by a monotone fixpoint over the body's direct-local
/// assignments. `None` (never assigned a pointer value) reads as `Indirect` at a use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LocalRoot {
    /// The address of this body's own memory (a local, or a by-value argument's own copy).
    Local,
    Mem(MemRoot),
}

struct MirRoots {
    roots: HashMap<Local, LocalRoot>,
}

/// Is `func` a constructor that returns a FRESH `Box` — an inherent `Box::new*` (`new`,
/// `new_uninit`, `new_zeroed`, `new_in`, …)? Its allocation is this body's own memory (e.g.
/// `vec![x]` writes `x` into `Box::new_uninit()`'s allocation before handing the box to
/// `box_assume_init_into_vec_unsafe`): a write through it becomes visible only when the box
/// itself is passed or stored, and that is a paired call or store. Every OTHER box is a pointer
/// like any other — a `Box` parameter is the caller's allocation, `Box::from_raw(p)` is `p`'s —
/// and a write through it is an effect.
fn is_fresh_box_constructor<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Some((def_id, _)) = func.const_fn_def() else { return false };
    tcx.opt_item_name(def_id).is_some_and(|n| n.as_str().starts_with("new"))
        && tcx.inherent_impl_of_assoc(def_id).is_some_and(|imp| {
            matches!(
                tcx.type_of(imp).instantiate_identity().skip_normalization().kind(),
                ty::Adt(adt, _) if adt.is_box()
            )
        })
}

impl MirRoots {
    fn compute<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> MirRoots {
        fn join(a: Option<LocalRoot>, b: LocalRoot) -> LocalRoot {
            match a {
                None => b,
                Some(x) if x == b => x,
                Some(_) => LocalRoot::Mem(MemRoot::Indirect),
            }
        }
        let mut roots: HashMap<Local, LocalRoot> = HashMap::new();
        for (i, arg) in body.args_iter().enumerate() {
            roots.insert(arg, LocalRoot::Mem(MemRoot::Arg(i as u32)));
        }
        // Bounded: each local changes at most twice.
        for _ in 0..(2 * body.local_decls.len() + 2) {
            let mut changed = false;
            for data in body.basic_blocks.iter() {
                for stmt in &data.statements {
                    let StatementKind::Assign(assign) = &stmt.kind else { continue };
                    let (place, rv) = &**assign;
                    // An argument reassigned in the body joins its incoming root with the new one.
                    if !place.projection.is_empty() {
                        continue;
                    }
                    let r = Self::rvalue_root(tcx, rv, &roots, body.arg_count);
                    let new = join(roots.get(&place.local).copied(), r);
                    if roots.get(&place.local) != Some(&new) {
                        roots.insert(place.local, new);
                        changed = true;
                    }
                }
                let call_destination = match data.terminator.as_ref().map(|t| &t.kind) {
                    Some(TerminatorKind::Call { func, destination, .. }) => {
                        Some((func, destination))
                    }
                    _ => None,
                };
                if let Some((func, destination)) =
                    call_destination.filter(|(_, d)| d.projection.is_empty())
                {
                    // A fresh `Box` is the body's own allocation; any other call result is a
                    // pointer the body did not make.
                    let root = if is_fresh_box_constructor(tcx, func) {
                        LocalRoot::Local
                    } else {
                        LocalRoot::Mem(MemRoot::Indirect)
                    };
                    let new = join(roots.get(&destination.local).copied(), root);
                    if roots.get(&destination.local) != Some(&new) {
                        roots.insert(destination.local, new);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        MirRoots { roots }
    }

    /// The root of a pointer VALUE read from `place` (an operand), or of the address `place`
    /// denotes (`address == true`, for `&place`).
    fn place_root(
        place: &Place<'_>,
        roots: &HashMap<Local, LocalRoot>,
        arg_count: usize,
        address: bool,
    ) -> LocalRoot {
        let is_arg = |l: Local| l.as_usize() >= 1 && l.as_usize() <= arg_count;
        let last_deref = place.projection.iter().rposition(|p| matches!(p, ProjectionElem::Deref));
        if address {
            // `&place`: the memory `place` names.
            return match last_deref {
                None => LocalRoot::Local,
                Some(d) => Self::deref_base_root(place, d, roots, arg_count),
            };
        }
        // A pointer value read out of `place`.
        if place.projection.is_empty() {
            return roots.get(&place.local).copied().unwrap_or(LocalRoot::Mem(MemRoot::Indirect));
        }
        if last_deref.is_some() {
            return LocalRoot::Mem(MemRoot::Indirect);
        }
        if is_arg(place.local) {
            // A pointer field of a by-value argument aggregate: the caller's pointer.
            return LocalRoot::Mem(MemRoot::Arg((place.local.as_usize() - 1) as u32));
        }
        LocalRoot::Mem(MemRoot::Indirect)
    }

    /// The root of the memory `*base` addresses, where `base` is `place` up to (excluding) its
    /// projection element `d`, a `Deref`.
    fn deref_base_root(
        place: &Place<'_>,
        d: usize,
        roots: &HashMap<Local, LocalRoot>,
        arg_count: usize,
    ) -> LocalRoot {
        let is_arg = |l: Local| l.as_usize() >= 1 && l.as_usize() <= arg_count;
        let base = &place.projection[..d];
        if base.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            return LocalRoot::Mem(MemRoot::Indirect);
        }
        if base.is_empty() {
            return roots.get(&place.local).copied().unwrap_or(LocalRoot::Mem(MemRoot::Indirect));
        }
        if is_arg(place.local) {
            return LocalRoot::Mem(MemRoot::Arg((place.local.as_usize() - 1) as u32));
        }
        LocalRoot::Mem(MemRoot::Indirect)
    }

    fn operand_root<'tcx>(
        tcx: TyCtxt<'tcx>,
        op: &Operand<'tcx>,
        roots: &HashMap<Local, LocalRoot>,
        arg_count: usize,
    ) -> LocalRoot {
        match op {
            Operand::Copy(p) | Operand::Move(p) => Self::place_root(p, roots, arg_count, false),
            Operand::Constant(c) if c.check_static_ptr(tcx).is_some() => {
                LocalRoot::Mem(MemRoot::Static)
            }
            _ => LocalRoot::Mem(MemRoot::Indirect),
        }
    }

    fn rvalue_root<'tcx>(
        tcx: TyCtxt<'tcx>,
        rv: &Rvalue<'tcx>,
        roots: &HashMap<Local, LocalRoot>,
        arg_count: usize,
    ) -> LocalRoot {
        match rv {
            Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p) | Rvalue::Reborrow(_, _, p) => {
                Self::place_root(p, roots, arg_count, true)
            }
            Rvalue::CopyForDeref(p) => Self::place_root(p, roots, arg_count, false),
            Rvalue::Use(op, _) | Rvalue::Cast(_, op, _) => {
                Self::operand_root(tcx, op, roots, arg_count)
            }
            Rvalue::ThreadLocalRef(_) => LocalRoot::Mem(MemRoot::Static),
            _ => LocalRoot::Mem(MemRoot::Indirect),
        }
    }

    /// The escaping root of a store to `place`, or `None` when the place is this body's own
    /// memory (no deref, or a deref of a pointer to a local or of a fresh `Box`). A `Box` is
    /// rooted like any other pointer ([`is_fresh_box_constructor`]).
    fn store_root(&self, place: &Place<'_>, arg_count: usize) -> Option<MemRoot> {
        let d = place.projection.iter().rposition(|p| matches!(p, ProjectionElem::Deref))?;
        match Self::deref_base_root(place, d, &self.roots, arg_count) {
            LocalRoot::Local => None,
            LocalRoot::Mem(m) => Some(m),
        }
    }
}

/// The initialization facts the drop census needs at a program point: which whole locals are
/// MAYBE initialized (a "may" set — union at a join), and which direct fields `(local, field)`
/// are DEFINITELY moved out (a "must" set — intersection at a join). A local leaves the first set
/// on `StorageLive`/`StorageDead`, a `move` of the whole local, or a `Drop` of it, and enters it on
/// any assignment to it or a part of it, a call destination, or a yield's resume argument. A field
/// enters the second set on a `move` of exactly that field and leaves it on any assignment to it or
/// to its local. So "not maybe-initialized" means moved-out on every path, and a field in the must
/// set is moved-out on every path.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct InitState {
    maybe_init: BTreeSet<Local>,
    moved_fields: BTreeSet<(Local, u32)>,
}

impl InitState {
    fn kill(&mut self, l: Local) {
        self.maybe_init.remove(&l);
        self.moved_fields.retain(|(x, _)| *x != l);
    }

    fn move_operand(&mut self, op: &Operand<'_>) {
        let Operand::Move(p) = op else { return };
        match p.projection.as_slice() {
            [] => self.kill(p.local),
            [ProjectionElem::Field(f, _)] => {
                self.moved_fields.insert((p.local, f.as_u32()));
            }
            _ => {}
        }
    }

    fn assign(&mut self, place: &Place<'_>) {
        if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            return;
        }
        self.maybe_init.insert(place.local);
        match place.projection.as_slice() {
            [ProjectionElem::Field(f, _)] => {
                self.moved_fields.remove(&(place.local, f.as_u32()));
            }
            _ => self.moved_fields.retain(|(x, _)| *x != place.local),
        }
    }

    /// Join `other` into `self`; true iff `self` changed.
    fn join(&mut self, other: &InitState) -> bool {
        // Trust: union only grows the may set, and intersection only shrinks the must
        // set. Their separate lengths detect every change without cloning both trees;
        // a total length could miss simultaneous growth and shrinkage.
        let before = (self.maybe_init.len(), self.moved_fields.len());
        self.maybe_init.extend(other.maybe_init.iter().copied());
        self.moved_fields.retain(|f| other.moved_fields.contains(f));
        (self.maybe_init.len(), self.moved_fields.len()) != before
    }
}

/// [`InitState`] at each reachable block's entry, by a monotone fixpoint over real edges.
fn init_at_entry(
    body: &Body<'_>,
    reachable: &[bool],
    no_return: &BTreeSet<BasicBlock>,
) -> Vec<Option<InitState>> {
    let n = body.basic_blocks.len();
    let mut entry: Vec<Option<InitState>> = vec![None; n];
    entry[mir::START_BLOCK.as_usize()] =
        Some(InitState { maybe_init: body.args_iter().collect(), moved_fields: BTreeSet::new() });
    let mut work = vec![mir::START_BLOCK];
    let mut queued = vec![false; n];
    queued[mir::START_BLOCK.as_usize()] = true;
    while let Some(bb) = work.pop() {
        // Clear before transfer: a loop backedge may need to schedule this block again.
        // Pending blocks read the latest joined entry, so only one pending visit is needed.
        queued[bb.as_usize()] = false;
        if !reachable[bb.as_usize()] {
            continue;
        }
        let Some(mut state) = entry[bb.as_usize()].clone() else { continue };
        let data = &body.basic_blocks[bb];
        for stmt in &data.statements {
            transfer_statement(&stmt.kind, &mut state);
        }
        let Some(term) = &data.terminator else { continue };
        let succs = real_successors(body, bb, no_return);
        transfer_terminator(&term.kind, &mut state);
        for s in succs {
            if !reachable[s.as_usize()] {
                continue;
            }
            let slot = &mut entry[s.as_usize()];
            let grew = match slot {
                None => {
                    *slot = Some(state.clone());
                    true
                }
                Some(have) => have.join(&state),
            };
            if grew && !std::mem::replace(&mut queued[s.as_usize()], true) {
                work.push(s);
            }
        }
    }
    entry
}

fn rvalue_moves<'tcx>(rv: &Rvalue<'tcx>, state: &mut InitState) {
    match rv {
        Rvalue::Use(op, _)
        | Rvalue::Repeat(op, _)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op) => state.move_operand(op),
        Rvalue::BinaryOp(_, ops) => {
            state.move_operand(&ops.0);
            state.move_operand(&ops.1);
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops.iter() {
                state.move_operand(op);
            }
        }
        Rvalue::WrapUnsafeBinder(op, _) => state.move_operand(op),
        _ => {}
    }
}

fn transfer_statement(kind: &StatementKind<'_>, state: &mut InitState) {
    match kind {
        StatementKind::Assign(assign) => {
            let (place, rv) = &**assign;
            rvalue_moves(rv, state);
            state.assign(place);
        }
        StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => state.kill(*l),
        _ => {}
    }
}

fn transfer_terminator(kind: &TerminatorKind<'_>, state: &mut InitState) {
    match kind {
        TerminatorKind::Call { args, destination, .. } => {
            for a in args.iter() {
                state.move_operand(&a.node);
            }
            state.assign(destination);
        }
        TerminatorKind::TailCall { args, .. } => {
            for a in args.iter() {
                state.move_operand(&a.node);
            }
        }
        TerminatorKind::Drop { place, .. } if place.projection.is_empty() => {
            state.kill(place.local)
        }
        TerminatorKind::Yield { value, resume_arg, .. } => {
            state.move_operand(value);
            state.assign(resume_arg);
        }
        _ => {}
    }
}

/// Does a `Drop` of `place` run a destructor, given `state` just before it? NO only when it is
/// dead by construction: the whole local is moved-out on every path; or the place is a direct
/// field moved-out on every path; or the local is a struct/tuple with no `Drop` impl of its own
/// whose every field that needs dropping is moved-out on every path (a consuming method's
/// `drop(self.held)` leaves only drop-free fields behind) — a closure, and a coroutine body's own
/// env, counting as the tuple of their upvars. Anything through a pointer, an enum, a union, a
/// coroutine value, or a type with its own destructor is LIVE.
fn drop_is_live<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
    state: &InitState,
) -> bool {
    if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
        return true;
    }
    if !state.maybe_init.contains(&place.local) {
        return false;
    }
    match place.projection.as_slice() {
        [ProjectionElem::Field(f, _)] => !state.moved_fields.contains(&(place.local, f.as_u32())),
        [] => {
            let typing_env = body.typing_env(tcx);
            let field_tys: Vec<ty::Ty<'tcx>> = match body.local_decls[place.local].ty.kind() {
                ty::Adt(adt, args) if adt.is_struct() && adt.destructor(tcx).is_none() => adt
                    .non_enum_variant()
                    .fields
                    .iter()
                    .map(|f| f.ty(tcx, *args).skip_normalization())
                    .collect(),
                ty::Tuple(tys) => tys.iter().collect(),
                // A closure's drop glue is its upvars' (it has no `Drop` impl).
                ty::Closure(_, args) => args.as_closure().upvar_tys().iter().collect(),
                // A coroutine body's `drop(_1)` of ITS OWN env drops the upvars only:
                // `rustc_mir_transform::coroutine::drop::elaborate_coroutine_drops` ("`open_drop`
                // can only be reached within that own coroutine's resume function"). A coroutine
                // VALUE dropped anywhere else runs state-dependent drop glue over its saved locals,
                // which no query answers here without a cycle (rustc's own `needs_drop` treats
                // every coroutine as needing drop for that reason): that drop stays live.
                ty::Coroutine(_, args)
                    if body.coroutine.is_some() && place.local == Local::from_u32(1) =>
                {
                    args.as_coroutine().upvar_tys().iter().collect()
                }
                _ => return true,
            };
            // Through the reveal funnel (OPAQUE-IMPL-WHERE-LEAK-1): the built body's analysis
            // mode still leaks a local opaque's auto traits through an impl where-clause.
            field_tys.iter().enumerate().any(|(i, t)| {
                !state.moved_fields.contains(&(place.local, i as u32))
                    && crate::needs_drop_unrevealed(tcx, *t, typing_env)
            })
        }
        _ => true,
    }
}

/// [`drop_runs_destructor`], for the producer's drop planner (`drops.rs`): a shared-borrowed
/// value is dropped through a fresh slot only when its glue cannot observe its address.
pub(crate) fn drop_runs_destructor_pub<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
) -> bool {
    drop_runs_destructor(tcx, typing_env, ty)
}

/// May dropping a value of `ty` run a DESTRUCTOR — code beyond releasing memory? `false` only
/// for drop glue that provably frees memory and nothing else: a `Box`, `Vec` or `String` whose
/// contents are (recursively) the same, and an aggregate (struct, enum, tuple, array, closure)
/// without a `Drop` impl of its own whose every part is. Any other `Drop` impl (a lock guard's
/// unlock, an `OwnedFd`'s close, every user impl) and any type the census cannot see through (a
/// type parameter, a trait object, a coroutine, an alias) is `true`. A type met again while it is
/// being walked (`Node { next: Option<Box<Node>> }`) adds nothing new and reads `false` there.
fn drop_runs_destructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
) -> bool {
    fn walk<'tcx>(
        tcx: TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        ty: ty::Ty<'tcx>,
        active: &mut HashSet<ty::Ty<'tcx>>,
        depth: usize,
    ) -> bool {
        if depth > 32 {
            return true;
        }
        // Through the reveal funnel (OPAQUE-IMPL-WHERE-LEAK-1): this walk reaches field types
        // (a `Box`'s pointee, a field of a field) no question stock `mir_build` asks, and
        // normalizing one in the analysis mode can confirm an impl where-clause that leaks a
        // local opaque's auto trait — inside `mir_built` of that opaque's defining body, E0391.
        let ty = crate::producer_try_normalize(tcx, typing_env, ty).unwrap_or(ty);
        if !crate::needs_drop_unrevealed(tcx, ty, typing_env) {
            return false;
        }
        if !active.insert(ty) {
            return false;
        }
        // `Ok(parts)`: the glue runs exactly the parts' glue; `Err(runs)`: decided here.
        let parts: Result<Vec<ty::Ty<'tcx>>, bool> = match ty.kind() {
            ty::Adt(adt, args)
                if adt.is_box()
                    || tcx.is_diagnostic_item(rustc_span::sym::Vec, adt.did())
                    || tcx.is_diagnostic_item(rustc_span::sym::String, adt.did()) =>
            {
                // The element type and the allocator (`Global` drops nothing).
                Ok(args.types().collect())
            }
            ty::Adt(adt, _) if adt.destructor(tcx).is_some() => Err(true),
            ty::Adt(adt, args) if !adt.is_union() => {
                Ok(adt.all_fields().map(|f| f.ty(tcx, *args).skip_normalization()).collect())
            }
            ty::Adt(..) => Err(false),
            ty::Tuple(tys) => Ok(tys.iter().collect()),
            ty::Array(e, _) | ty::Slice(e) => Ok(vec![*e]),
            ty::Closure(_, args) => Ok(args.as_closure().upvar_tys().iter().collect()),
            ty::Str => Err(false),
            _ => Err(true),
        };
        let runs = match parts {
            Ok(parts) => parts.into_iter().any(|t| walk(tcx, typing_env, t, active, depth + 1)),
            Err(runs) => runs,
        };
        active.remove(&ty);
        runs
    }
    walk(tcx, typing_env, ty, &mut HashSet::new(), 0)
}

/// Every enum type with a value ([`is_valued_enum`]) `ty` holds BY VALUE (itself, and through
/// struct / union / enum-variant / tuple / array / slice / closure-upvar fields; never through a
/// pointer), as `type_id_hash`es.
fn collect_by_value_enums<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
    seen: &mut HashSet<ty::Ty<'tcx>>,
    out: &mut BTreeSet<u128>,
    depth: usize,
) {
    if depth > 32 || !seen.insert(ty) {
        return;
    }
    // Through the reveal funnel (OPAQUE-IMPL-WHERE-LEAK-1), as `drop_runs_destructor` above.
    let ty = crate::producer_try_normalize(tcx, typing_env, ty).unwrap_or(ty);
    let parts: Vec<ty::Ty<'tcx>> = match ty.kind() {
        ty::Adt(adt, args) => {
            // An enum with no value to lose (uninhabited, or one field-less variant: zero-sized)
            // is spelled faithfully by `()`.
            if is_valued_enum(tcx, ty) {
                out.insert(tcx.type_id_hash(ty).as_u128());
            }
            // A `Box` owns its pointee through a pointer: its fields hold no value of it.
            if adt.is_box() {
                Vec::new()
            } else {
                adt.all_fields().map(|f| f.ty(tcx, *args).skip_normalization()).collect()
            }
        }
        ty::Tuple(tys) => tys.iter().collect(),
        ty::Array(e, _) | ty::Slice(e) => vec![*e],
        ty::Closure(_, args) => args.as_closure().upvar_tys().iter().collect(),
        _ => Vec::new(),
    };
    for t in parts {
        collect_by_value_enums(tcx, typing_env, t, seen, out, depth + 1);
    }
}

/// The types whose layout or value a place use depends on, for every place the reachable
/// blocks name: the value's own type, unless the use only takes the place's ADDRESS (a borrow,
/// a raw borrow, a mention: `&*o` passes the caller's pointer on, whatever `*o` holds); and,
/// for every `Field` / `Index` / `ConstantIndex` / `Subslice` step, the aggregate stepped into
/// (its field offsets and element stride are computed from its spelling).
struct PlaceTypes<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    tys: Vec<ty::Ty<'tcx>>,
}

impl<'a, 'tcx> Visitor<'tcx> for PlaceTypes<'a, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
        use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext};
        if matches!(context, PlaceContext::NonUse(_)) {
            return;
        }
        for (i, elem) in place.projection.iter().enumerate() {
            if matches!(
                elem,
                ProjectionElem::Field(..)
                    | ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            ) {
                let base = PlaceRef { local: place.local, projection: &place.projection[..i] };
                self.tys.push(base.ty(self.body, self.tcx).ty);
            }
        }
        let address_only = matches!(
            context,
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::SharedBorrow
                    | NonMutatingUseContext::FakeBorrow
                    | NonMutatingUseContext::RawBorrow
                    | NonMutatingUseContext::PlaceMention
            ) | PlaceContext::MutatingUse(
                MutatingUseContext::Borrow | MutatingUseContext::RawBorrow
            )
        );
        if !address_only {
            self.tys.push(place.ty(self.body, self.tcx).ty);
        }
    }
}

/// Is `ty` an enum that HAS a value to abstract: at least one variant (an uninhabited enum has no
/// value, so a `()` standing for it loses nothing), and not a single field-less variant (that is
/// a zero-sized type, for which `()` is the faithful spelling). A `bool`/`()` on the trust-ir side
/// in a position rustc types like this is a placeholder for the enum.
fn is_valued_enum<'tcx>(_tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Adt(adt, _) if adt.is_enum() => {
            let variants = adt.variants();
            !variants.is_empty()
                && !(variants.len() == 1 && variants.iter().all(|v| v.fields.is_empty()))
        }
        _ => false,
    }
}

/// Is `ty` an integer `Range`/`RangeInclusive`?
fn is_int_range<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    let ty::Adt(adt, args) = ty.kind() else { return false };
    let li = tcx.lang_items();
    if li.range_struct() != Some(adt.did()) && li.range_inclusive_struct() != Some(adt.did()) {
        return false;
    }
    args.types().next().is_some_and(|t| t.is_integral())
}

/// Is `<lhs as PartialEq<rhs>>::eq` the std comparison [`Equivalence::BuiltinEq`] audits: a
/// primitive scalar, `()`, `str`, or a slice / array of primitive scalars (not of `str`), compared
/// with ITS OWN type? A user `impl PartialEq<Foo> for u32` (or `for str`) has a builtin `Self`
/// and is user code, with whatever effects it has: its right-hand side differs.
fn is_builtin_eq(lhs: &crate::SiteTy, rhs: &crate::SiteTy) -> bool {
    use crate::SiteTy;
    let scalar = |t: &SiteTy| {
        matches!(
            t,
            SiteTy::Bool
                | SiteTy::Char
                | SiteTy::Int(_)
                | SiteTy::Uint(_)
                | SiteTy::Float(_)
                | SiteTy::Str
        ) || matches!(t, SiteTy::Tuple(ts) if ts.is_empty())
    };
    let builtin = match lhs {
        SiteTy::Slice(e) | SiteTy::Array(e, _) => scalar(e) && !matches!(**e, SiteTy::Str),
        t => scalar(t),
    };
    builtin && lhs == rhs
}

/// The audited equivalence a direct call's callee belongs to, if any (see [`Equivalence`]).
fn audited_equivalence<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &MirRoots,
    def_id: DefId,
    generic_args: ty::GenericArgs<'tcx>,
    call_args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> Option<Equivalence> {
    if let Some(intrinsic) = tcx.intrinsic(def_id) {
        return PURE_INTRINSICS
            .contains(&intrinsic.name.as_str())
            .then_some(Equivalence::PureIntrinsic);
    }
    if let Some(comparison) = crate::core_ptr_eq::recognize(tcx, def_id, generic_args) {
        let input = comparison.input();
        if call_args.len() == 2
            && call_args.iter().all(|arg| arg.node.ty(&body.local_decls, tcx) == input)
        {
            return Some(Equivalence::BuiltinEq);
        }
    }
    if crate::core_bool_from_output_ty(tcx, def_id, generic_args).is_some() {
        return Some(Equivalence::BoolFromInteger);
    }
    let li = tcx.lang_items();
    if li.slice_len_fn() == Some(def_id) {
        return Some(Equivalence::SliceLen);
    }
    let self_ty = generic_args.types().next();
    if li.into_iter_fn() == Some(def_id) && self_ty.is_some_and(|t| is_int_range(tcx, t)) {
        return Some(Equivalence::RangeIntoIter);
    }
    if li.next_fn() == Some(def_id) && self_ty.is_some_and(|t| is_int_range(tcx, t)) {
        // Only an iterator the body OWNS: the receiver `&mut it` must point into a local.
        let local_receiver = call_args.first().is_some_and(|a| {
            matches!(
                MirRoots::operand_root(tcx, &a.node, &roots.roots, body.arg_count),
                LocalRoot::Local
            )
        });
        return local_receiver.then_some(Equivalence::RangeNext);
    }
    let is_option_or_result = |t: ty::Ty<'tcx>| match t.kind() {
        ty::Adt(adt, _) => {
            tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did())
                || tcx.is_diagnostic_item(rustc_span::sym::Result, adt.did())
        }
        _ => false,
    };
    if li.branch_fn() == Some(def_id) && self_ty.is_some_and(is_option_or_result) {
        return Some(Equivalence::TryBranch);
    }
    if li.from_residual_fn() == Some(def_id) {
        // `<Self as FromResidual<R>>::from_residual`: args are [Self, R].
        let mut tys = generic_args.types();
        let (Some(ret), Some(residual)) = (tys.next(), tys.next()) else { return None };
        let (ty::Adt(ret_adt, ret_args), ty::Adt(res_adt, res_args)) =
            (ret.kind(), residual.kind())
        else {
            return None;
        };
        if ret_adt.did() != res_adt.did() {
            return None;
        }
        if tcx.is_diagnostic_item(rustc_span::sym::Option, ret_adt.did()) {
            return Some(Equivalence::TryResidual);
        }
        if tcx.is_diagnostic_item(rustc_span::sym::Result, ret_adt.did()) {
            let error = |args: ty::GenericArgs<'tcx>| {
                args.types().nth(1).map(|t| tcx.erase_and_anonymize_regions(t))
            };
            return (error(*ret_args).is_some() && error(*ret_args) == error(*res_args))
                .then_some(Equivalence::TryResidual);
        }
        return None;
    }
    if tcx
        .opt_item_name(def_id)
        .is_some_and(|n| n.as_str().starts_with("new") || n.as_str() == "from_str")
        && tcx.inherent_impl_of_assoc(def_id).is_some_and(|imp| {
            match tcx.type_of(imp).instantiate_identity().skip_normalization().kind() {
                ty::Adt(adt, _) => {
                    li.format_arguments() == Some(adt.did())
                        || li.format_argument() == Some(adt.did())
                }
                _ => false,
            }
        })
    {
        return Some(Equivalence::FormatArguments);
    }
    if tcx.trait_of_assoc(def_id).is_some_and(|t| li.eq_trait() == Some(t))
        && tcx.opt_item_name(def_id).is_some_and(|n| matches!(n.as_str(), "eq" | "ne"))
    {
        // `PartialEq<Rhs>::eq`'s args are `[Self, Rhs]`.
        let mut tys = generic_args.types().map(|t| crate::encode_ty(tcx, t));
        let builtin = match (tys.next(), tys.next()) {
            (Some(Some(lhs)), Some(Some(rhs))) => is_builtin_eq(&lhs, &rhs),
            _ => false,
        };
        return builtin.then_some(Equivalence::BuiltinEq);
    }
    if tcx.opt_item_name(def_id).is_some_and(|n| matches!(n.as_str(), "is_some" | "is_none")) {
        let inherent_option_impl =
            tcx.inherent_impl_of_assoc(def_id).is_some_and(|imp| {
                match tcx.type_of(imp).instantiate_identity().skip_normalization().kind() {
                    ty::Adt(adt, _) => tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did()),
                    _ => false,
                }
            });
        if inherent_option_impl {
            return Some(Equivalence::OptionDiscriminant);
        }
    }
    None
}

/// The MIR oracle's census of `body` (see the module doc).
pub fn mir_census<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> MirCensus {
    let no_return = uninhabited_returns(tcx, body);
    let reachable = mir_reachable(body, &no_return);
    let roots = MirRoots::compute(tcx, body);
    // Most bodies need no precision beyond the existing coarse roots.
    // Materialize the independent location analysis only for an Indirect store.
    let exact = std::cell::LazyCell::new(|| {
        store_root_facts::StoreRootFacts::compute(
            body,
            &reachable,
            body.basic_blocks
                .iter_enumerated()
                .map(|(bb, _)| {
                    real_successors(body, bb, &no_return)
                        .into_iter()
                        .map(BasicBlock::as_usize)
                        .collect()
                })
                .collect(),
        )
    });
    let init = init_at_entry(body, &reachable, &no_return);
    let mut effects = Vec::new();
    let mut push = |kind: MirEffectKind, span: Span| {
        let index = effects.len();
        effects.push(MirEffect { kind, span });
        index
    };
    let mut exact_store_args = BTreeMap::new();
    let mut store_values = Vec::new();
    let mut drop_dead_blocks = BTreeSet::new();
    let store_value = |ty: ty::Ty<'tcx>| {
        if is_valued_enum(tcx, ty) {
            StoreValue::ValuedEnum
        } else if ty.is_bool() || ty.is_unit() {
            StoreValue::BoolOrUnit
        } else {
            StoreValue::Other
        }
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if !reachable[bb.as_usize()] {
            continue;
        }
        let mut state = init[bb.as_usize()].clone().unwrap_or_default();
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let location = Location { block: bb, statement_index };
            let span = stmt.source_info.span;
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    if let Some(root) = roots.store_root(&assign.0, body.arg_count) {
                        let index = push(MirEffectKind::Store(root), span);
                        if root == MemRoot::Indirect {
                            if let Some(argument) = exact.store_argument(location, &assign.0) {
                                exact_store_args.insert(index, argument);
                            }
                        }
                        store_values.push((root, store_value(assign.0.ty(body, tcx).ty)));
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if let Some(root) = roots.store_root(place, body.arg_count) {
                        let index = push(MirEffectKind::Store(root), span);
                        if root == MemRoot::Indirect {
                            if let Some(argument) = exact.store_argument(location, place) {
                                exact_store_args.insert(index, argument);
                            }
                        }
                        store_values.push((root, store_value(place.ty(body, tcx).ty)));
                    }
                }
                StatementKind::Intrinsic(intrinsic) => {
                    if let NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic {
                        let root = match MirRoots::operand_root(
                            tcx,
                            &copy.dst,
                            &roots.roots,
                            body.arg_count,
                        ) {
                            LocalRoot::Local => None,
                            LocalRoot::Mem(m) => Some(m),
                        };
                        if let Some(root) = root {
                            let index = push(MirEffectKind::Store(root), span);
                            if root == MemRoot::Indirect {
                                if let Some(argument) =
                                    exact.copy_destination_argument(location, intrinsic)
                                {
                                    exact_store_args.insert(index, argument);
                                }
                            }
                            store_values.push((root, StoreValue::Other));
                        }
                    }
                }
                _ => {}
            }
            transfer_statement(&stmt.kind, &mut state);
        }
        let Some(term) = &data.terminator else { continue };
        let span = term.source_info.span;
        match &term.kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                let destination_ty = destination.ty(&body.local_decls, tcx).ty;
                let enum_result = is_valued_enum(tcx, destination_ty);
                push(call_kind(tcx, body, &roots, func, args, enum_result), span);
                if let Some(root) = roots.store_root(destination, body.arg_count) {
                    let index = push(MirEffectKind::Store(root), span);
                    if root == MemRoot::Indirect {
                        let location =
                            Location { block: bb, statement_index: data.statements.len() };
                        if let Some(argument) = exact.store_argument(location, destination) {
                            exact_store_args.insert(index, argument);
                        }
                    }
                    store_values.push((root, store_value(destination_ty)));
                }
            }
            TerminatorKind::TailCall { func, args, .. } => {
                push(call_kind(tcx, body, &roots, func, args, false), span);
            }
            TerminatorKind::Drop { place, .. } => {
                if drop_is_live(tcx, body, place, &state) {
                    let dropped = place.ty(&body.local_decls, tcx).ty;
                    let destructor = drop_runs_destructor(tcx, body.typing_env(tcx), dropped);
                    push(MirEffectKind::Drop { destructor }, span);
                } else {
                    drop_dead_blocks.insert(bb.as_u32());
                }
            }
            TerminatorKind::Assert { msg, .. } => {
                push(MirEffectKind::Assert(AssertClass::of_mir(msg)), span);
            }
            TerminatorKind::InlineAsm { asm_macro, template, operands, options, .. } => {
                let empty_noreturn = matches!(asm_macro, mir::InlineAsmMacro::Asm)
                    && template.is_empty()
                    && operands.is_empty()
                    && options.contains(rustc_ast::InlineAsmOptions::NORETURN);
                push(MirEffectKind::Asm { empty_noreturn }, span);
            }
            TerminatorKind::Yield { .. } => {
                push(MirEffectKind::Yield, span);
            }
            _ => {}
        }
    }
    let valued = |l: Local| is_valued_enum(tcx, body.local_decls[l].ty);
    // Every type the body holds by value: the signature's, and every place the reachable blocks
    // name at every projection step.
    let mut places = PlaceTypes { tcx, body, tys: Vec::new() };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if reachable[bb.as_usize()] {
            places.visit_basic_block_data(bb, data);
        }
    }
    let typing_env = body.typing_env(tcx);
    let mut enum_types = BTreeSet::new();
    let mut seen = HashSet::new();
    let signature = std::iter::once(mir::RETURN_PLACE).chain(body.args_iter());
    for t in signature.map(|l| body.local_decls[l].ty).chain(places.tys) {
        collect_by_value_enums(tcx, typing_env, t, &mut seen, &mut enum_types, 0);
    }
    // The drop oracle, with each drop's destructor reading (the dropped place's type).
    let drop_oracle = crate::drop_oracle::elaborated_drops(tcx, body).map(|drops| {
        drops
            .into_iter()
            .map(|d| {
                let destructor = match &body.basic_blocks[d.block].terminator().kind {
                    TerminatorKind::Drop { place, .. } => {
                        drop_runs_destructor(tcx, typing_env, place.ty(&body.local_decls, tcx).ty)
                    }
                    _ => true,
                };
                (d, destructor)
            })
            .collect()
    });
    MirCensus {
        effects,
        arg_count: body.arg_count as u32,
        arg_enum: body.args_iter().map(valued).collect(),
        ret_enum: valued(mir::RETURN_PLACE),
        store_values,
        exact_store_args,
        enum_types,
        drop_oracle,
        drop_dead_blocks,
    }
}

fn call_kind<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &MirRoots,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    enum_result: bool,
) -> MirEffectKind {
    // A constant `FnDef`, or a place whose TYPE is a `FnDef` (a fn item held in a local, as in
    // `({ noop })()`): either way the callee is statically known. Anything else is indirect.
    let fn_def = func.const_fn_def().or_else(|| match func.ty(&body.local_decls, tcx).kind() {
        ty::FnDef(def_id, args) => Some((*def_id, args.skip_binder())),
        _ => None,
    });
    let Some((def_id, generic_args)) = fn_def else {
        return MirEffectKind::IndirectCall;
    };
    let mut ids = vec![def_id];
    // A `Fn*` trait call on a closure or fn item: the producer calls the closure / fn directly.
    if tcx.fn_trait_kind_from_def_id(tcx.trait_of_assoc(def_id).unwrap_or(def_id)).is_some() {
        if let Some(self_ty) = generic_args.types().next() {
            match self_ty.kind() {
                ty::Closure(c, _) | ty::FnDef(c, _) | ty::CoroutineClosure(c, _) => ids.push(*c),
                _ => {}
            }
        }
    }
    let equivalence = audited_equivalence(tcx, body, roots, def_id, generic_args, args);
    let enum_args =
        args.iter().map(|a| is_valued_enum(tcx, a.node.ty(&body.local_decls, tcx))).collect();
    // The producer's own encoding of the site's args (`CalleeRef::site_args` is "exactly what
    // built MIR spells", encoded the same way), so the two sides compare like for like.
    let site_args = crate::encode_site_args(tcx, generic_args);
    MirEffectKind::Call { ids, site_args, equivalence, enum_result, enum_args }
}

// ---------------------------------------------------------------------------------------------
// The session registries and the finalize-time judgement.
// ---------------------------------------------------------------------------------------------

/// What the producer's MAINLINE lowering (the `mir_built` hook's, the one `crate_module::record`
/// splices) records about one body.
#[derive(Clone, Debug)]
pub struct ProducerBody {
    pub def_path: String,
    /// `Lowered::unsupported.is_empty()`.
    pub clean: bool,
    /// A const / static initializer (CTFE): no effect census, abstractions only.
    pub const_context: bool,
    /// The producer's body kind; published identity comes from pass 1's DefIndex assignment.
    pub body_kind: crate::BodyKind,
    pub census: IrCensus,
    pub shape: EffectShape,
    /// The `type_id_hash` of every enum type this lowering collapsed to a lone `bool`/`()`
    /// placeholder (`LowerCx::opaque_lane_tys`, written at the one `map_ty` arm that collapses).
    /// The collapse is a function of the TYPE, so finalize unions these over every body: an enum
    /// one body collapsed is a placeholder in every body that holds it.
    pub collapsed_enums: BTreeSet<u128>,
    /// Trust (step 2 increment 6, step 6.1): the degraded struct rows `census` was computed with
    /// (`LowerCx::rmw_degraded_structs`, `ir_census`'s `degraded`), kept so an rmeta entry's
    /// evidence carries them (a consumer re-derives the census over the entry).
    pub degraded_structs: Vec<StructId>,
    /// Trust (step 2 increment 4b): the producer's drop claim (`drops::DropClaim`) — every live
    /// drop its plan places and how many `Inst::Drop` it emitted. `None` when it planned none.
    pub drop_claim: Option<crate::drops::DropClaim>,
    /// Why the producer placed no drop, when its planner refused the body or its placement was
    /// reverted (disclosure only).
    pub drop_refusal: Option<String>,
}

/// The census registry, filled at `mir_built` time from two seams and drained at finalize.
#[derive(Default)]
struct CensusRegistry {
    mir: BTreeMap<u32, MirCensus>,
    producer: BTreeMap<u32, ProducerBody>,
    /// def indices recorded twice by one seam: their census is not trusted.
    duplicated: BTreeSet<u32>,
    /// Trust (step 2 increment 6, step 6.5.1; INC6.5-JUDGE): the producer side of each LEVEL-S
    /// template lowering (`template_lowering`), judged at finalize against the same MIR census
    /// as the mainline record of its definition, into a map of its own
    /// ([`ConservationVerdicts::template_verdict`]) that no codegen, strict, scorecard or sidecar
    /// path reads.
    template: BTreeMap<u32, ProducerBody>,
    /// def indices whose template was recorded twice: neither record is trusted.
    template_duplicated: BTreeSet<u32>,
}

impl CensusRegistry {
    /// Record `body` as `index`'s template record (a second record marks the index duplicated).
    fn insert_template(&mut self, index: u32, body: ProducerBody) {
        if self.template.insert(index, body).is_some() {
            self.template_duplicated.insert(index);
        }
    }

    /// `index`'s template record, if one was recorded.
    #[cfg(test)]
    fn template(&self, index: u32) -> Option<&ProducerBody> {
        self.template.get(&index)
    }
}

/// Does this session run the census at all? Exactly when the producer registry does.
fn census_enabled(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.trust_ir_lower_enabled() || crate::crate_module::emit_requested(tcx)
}

/// Record the MIR oracle's census for `def`. Called by the `mir_built` provider
/// (`rustc_mir_transform`) on the body `build_mir_inner_impl` returned — the same built body the
/// hook handed to the differentials, before any pass runs on it.
pub fn record_mir_census<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &Body<'tcx>) {
    if !census_enabled(tcx) {
        return;
    }
    // Trust (OPAQUE-IMPL-WHERE-LEAK-1): the census runs INSIDE the `mir_built` query — its
    // provider calls this on the body `build_mir_inner_impl` just returned — but after the hook's
    // freeze has ended, so every question it asked through the reveal funnel took the unfrozen
    // path: the built body's own analysis mode, which LEAKS a local opaque's auto traits through
    // an impl where-clause. `collect_by_value_enums` normalizing `<u8 as Prim>::Storage` confirmed
    // `Wrap<u8>: Send` -> `type_of(Tait)` -> borrowck of the very body being built: E0391 on
    // valid Rust (`tests/ui/trust/async-layout-no-cycle/impl_where_leak_sized.rs`,
    // `impl_where_leak_array.rs`, `impl_where_leak_foreign_adt_by_ref.rs`). The census is asked
    // under the same freeze as the hook it is compared with, a frame naming the same body
    // (`enter_building`, as `crate::enter_mir_built_ctfe_freeze` enters it).
    let _frozen = crate::enter_mir_built_ctfe_freeze(def);
    let census = mir_census(tcx, body);
    let index = def.local_def_index.as_u32();
    tcx.sess.with_trust_compiler_state::<CensusRegistry, _>(|r| {
        if r.mir.insert(index, census).is_some() {
            r.duplicated.insert(index);
        }
    });
}

/// Record the producer side for `def` from the mainline lowering's per-body module. Called by
/// `lower_module_inner` only when it registers (the `mir_built` hook's lowering, never the
/// `trust_ir_of` query, the instance lane or the collect-all census).
pub(crate) fn record_producer_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    module: &Module,
    callees: &[crate::CalleeRef],
    body_kind: crate::BodyKind,
    clean: bool,
    degraded_structs: &[StructId],
    lanes: LedgeredLanes,
    collapsed_enums: &[(ty::Ty<'tcx>, Ty)],
    drop_claim: Option<crate::drops::DropClaim>,
    drop_refusal: Option<String>,
) {
    if !census_enabled(tcx) {
        return;
    }
    let collapsed_enums: BTreeSet<u128> =
        collapsed_enums.iter().map(|(t, _)| tcx.type_id_hash(*t).as_u128()).collect();
    let def_path =
        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
    let body = producer_body(
        def_path,
        module,
        callees,
        body_kind,
        clean,
        degraded_structs,
        lanes,
        collapsed_enums,
        drop_claim,
        drop_refusal,
    );
    let index = def.local_def_index.as_u32();
    tcx.sess.with_trust_compiler_state::<CensusRegistry, _>(|r| {
        if r.producer.insert(index, body).is_some() {
            r.duplicated.insert(index);
        }
    });
}

/// Trust (step 2 increment 6, step 6.5.1; INC6.5-JUDGE): record the producer side of `def`'s
/// LEVEL-S template lowering (`template_lowering::capture` -> `lower_template`). It takes exactly
/// the arguments [`record_producer_body`] takes, so the template is judged on the same census
/// inputs the mainline body is (the drop claim and refusal, the degraded rows, the two
/// placeholder lanes and the collapsed enum types), and keeps them in a map of its own: a
/// template record never reaches [`FinalizeOutcome::bodies`], the sidecar or the mainline
/// verdicts. Inert unless this session builds rmeta entries.
pub(crate) fn record_template_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    module: &Module,
    callees: &[crate::CalleeRef],
    body_kind: crate::BodyKind,
    clean: bool,
    degraded_structs: &[StructId],
    lanes: LedgeredLanes,
    collapsed_enums: &[(ty::Ty<'tcx>, Ty)],
    drop_claim: Option<crate::drops::DropClaim>,
    drop_refusal: Option<String>,
) {
    if !census_enabled(tcx) || !crate::rmeta_entry::entries_enabled(tcx) {
        return;
    }
    let collapsed_enums: BTreeSet<u128> =
        collapsed_enums.iter().map(|(t, _)| tcx.type_id_hash(*t).as_u128()).collect();
    let def_path =
        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
    let body = producer_body(
        def_path,
        module,
        callees,
        body_kind,
        clean,
        degraded_structs,
        lanes,
        collapsed_enums,
        drop_claim,
        drop_refusal,
    );
    let index = def.local_def_index.as_u32();
    tcx.sess.with_trust_compiler_state::<CensusRegistry, _>(|r| r.insert_template(index, body));
}

/// The census's view of a callee ledger: per `FuncId`, the identities a MIR call may pair
/// through and the first encodable site, and the result type each call site observed. PURE.
pub(crate) fn census_ledger(
    callees: &[crate::CalleeRef],
) -> (BTreeMap<FuncId, LedgerRow>, BTreeMap<FuncId, Ty>) {
    let mut ledger: BTreeMap<FuncId, LedgerRow> = BTreeMap::new();
    let mut callee_returns: BTreeMap<FuncId, Ty> = BTreeMap::new();
    for c in callees {
        if let Some(t) = &c.ret_ty {
            callee_returns.insert(c.func_id, t.clone());
        }
        let row = ledger.entry(c.func_id).or_default();
        for d in [c.site_def_id, c.def_id] {
            if !row.ids.contains(&d) {
                row.ids.push(d);
            }
        }
        // One `FuncId` is one row (`admit_callee_inner` interns by identity); a second spelling
        // would already have been refused by the producer. Keep the first site.
        if row.site.is_none() {
            row.site = c.site_args.clone().map(|a| (c.site_def_id, a));
        }
    }
    (ledger, callee_returns)
}

/// The producer side of one body, from a lowering's per-body module and the census inputs that
/// lowering ledgered (step 6.5.1 factored it out of [`record_producer_body`], which passes the
/// same arguments, so the mainline record and a template record are built by one rule). PURE.
pub(crate) fn producer_body(
    def_path: String,
    module: &Module,
    callees: &[crate::CalleeRef],
    body_kind: crate::BodyKind,
    clean: bool,
    degraded_structs: &[StructId],
    lanes: LedgeredLanes,
    collapsed_enums: BTreeSet<u128>,
    drop_claim: Option<crate::drops::DropClaim>,
    drop_refusal: Option<String>,
) -> ProducerBody {
    let degraded: BTreeSet<StructId> = degraded_structs.iter().copied().collect();
    let (ledger, callee_returns) = census_ledger(callees);
    let (census, shape) = match module.functions.first() {
        Some(f) => {
            let census = ir_census(module, f, &ledger, &callee_returns, &degraded, lanes);
            let shape = census.shape;
            (census, shape)
        }
        None => (IrCensus::default(), EffectShape::default()),
    };
    ProducerBody {
        def_path,
        clean,
        const_context: body_kind != crate::BodyKind::Fn,
        body_kind,
        census,
        shape,
        collapsed_enums,
        degraded_structs: degraded.iter().copied().collect(),
        drop_claim,
        drop_refusal,
    }
}

/// One body's verdict. `tags` empty means CONSERVED.
#[derive(Clone, Debug)]
pub struct BodyVerdict {
    pub def_path: String,
    pub clean: bool,
    pub tags: Vec<Tag>,
    /// The assembled `FuncId` the splice-consistency check read, when the body was found in the
    /// published module or the codegen handoff.
    pub assembled: Option<FuncId>,
    /// Paired by an audited equivalence, by name, with the count (disclosed, not a finding).
    pub equivalences: BTreeMap<&'static str, usize>,
    /// Trust (step 2 increment 4b): the number of live drops the producer's claim places, when
    /// it planned the body's drops (`drops::DropClaim`); `None` when it placed none.
    pub drop_claim_live: Option<usize>,
    /// Trust (step 2 increment 4c): the producer's [`crate::drops::DropSite`] of every
    /// `Inst::Drop` it emitted in this body (empty when it placed none). The drop-glue lane reads
    /// it back through [`drop_sites_for_codegen`].
    pub drop_sites: Vec<crate::drops::DropSite>,
}

impl BodyVerdict {
    pub fn conserved(&self) -> bool {
        self.tags.is_empty()
    }

    /// The `+`-joined, deduplicated class labels of the tags, `not-conserved(..)` first.
    pub fn classes(&self) -> Vec<String> {
        let kinds: BTreeSet<TagKind> = self.tags.iter().map(|t| t.kind).collect();
        kinds.into_iter().map(TagKind::label).collect()
    }
}

/// The session's verdicts, keyed by `DefIndex`. `ran` is false until [`finalize`] ran; every
/// consumer reads "not run" as a refusal.
#[derive(Default)]
pub struct ConservationVerdicts {
    ran: bool,
    by_def: BTreeMap<u32, BodyVerdict>,
    /// Trust (step 2 increment 6, step 6.5.1; INC6.5-JUDGE, INC6.5-NO-AUTHORITY): the verdicts of
    /// the LEVEL-S template lowerings, keyed like `by_def`. Read only by the template builder
    /// (`rmeta_entry::build_template`) through [`Self::template_verdict`]; never by codegen,
    /// admission, strict, the scorecard or the sidecar, and never merged into `by_def`.
    template_by_def: BTreeMap<u32, BodyVerdict>,
}

impl ConservationVerdicts {
    pub fn ran(&self) -> bool {
        self.ran
    }

    pub fn verdict(&self, def_index: u32) -> Option<&BodyVerdict> {
        self.by_def.get(&def_index)
    }

    /// The verdict of `def_index`'s template lowering, if one was judged (step 6.5.1).
    pub fn template_verdict(&self, def_index: u32) -> Option<&BodyVerdict> {
        self.template_by_def.get(&def_index)
    }

    /// A finalized verdict set, for the template builder's unit tests.
    #[cfg(test)]
    pub(crate) fn finalized_for_test(
        by_def: BTreeMap<u32, BodyVerdict>,
        template_by_def: BTreeMap<u32, BodyVerdict>,
    ) -> Self {
        ConservationVerdicts { ran: true, by_def, template_by_def }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&u32, &BodyVerdict)> {
        self.by_def.iter()
    }
}

/// CODEGEN admission for `def`: `Ok` only for a body the check ran on and found conserved.
/// There is no acceptance list: an abstracted body is never code.
pub fn admit_for_codegen(sess: &rustc_session::Session, def: LocalDefId) -> Result<(), String> {
    sess.with_trust_compiler_state::<ConservationVerdicts, _>(|v| {
        if !v.ran {
            return Err("the effect-conservation check did not run in this session".to_string());
        }
        match v.by_def.get(&def.local_def_index.as_u32()) {
            None => Err("the effect-conservation check has no verdict for this body".to_string()),
            Some(b) if b.conserved() => Ok(()),
            Some(b) => Err(render_tags(&b.tags)),
        }
    })
}

/// Trust (step 2 increment 4c): the producer's drop sites of `def`, for the CODEGEN drop-glue
/// lane — only for a body the check ran on and found CONSERVED (every drop it carries was
/// compared with rustc's elaboration). `Err` otherwise, naming why.
pub fn drop_sites_for_codegen(
    sess: &rustc_session::Session,
    def_index: u32,
) -> Result<Vec<crate::drops::DropSite>, String> {
    sess.with_trust_compiler_state::<ConservationVerdicts, _>(|v| {
        if !v.ran {
            return Err("the effect-conservation check did not run in this session".to_string());
        }
        match v.by_def.get(&def_index) {
            None => Err("the effect-conservation check has no verdict for this body".to_string()),
            Some(b) if b.conserved() => Ok(b.drop_sites.clone()),
            Some(b) => Err(render_tags(&b.tags)),
        }
    })
}

/// The assembled source `FuncId`s judged CONSERVED plus exact typed adapters
/// derived from conserved source constructors and source targets. No adapter is
/// inserted into the DefIndex/MIR verdict registry. A codegen consumer that lowers against
/// the whole module strips every other direct-lane body to a declaration
/// ([`strip_unconserved_bodies`]) so that no refused body is reachable as inlining context.
/// `Err` when the check did not run.
pub fn conserved_function_ids(sess: &rustc_session::Session) -> Result<BTreeSet<FuncId>, String> {
    let mut conserved: BTreeSet<FuncId> = sess
        .with_trust_compiler_state::<ConservationVerdicts, _>(|v| {
            if !v.ran {
                return Err("the effect-conservation check did not run in this session".to_string());
            }
            Ok(v.by_def.values().filter(|b| b.conserved()).filter_map(|b| b.assembled).collect())
        })?;
    crate::crate_module::with_published_crate_module(sess, |published| {
        if let Ok(p) = published {
            let adapters = closure_adapters::derive(
                p.module(),
                p.direct_source_count(),
                &conserved,
                crate::crate_module::TRUST_DIRECT_LANE_AUTHORITY,
            );
            conserved.extend(adapters.keys().copied());
        }
    });
    Ok(conserved)
}

/// Turn every direct-lane (`Producer::TRust`) body of `module` that is not in `conserved` into a
/// bodyless declaration, with no licensing claim. A call to it stays a call to an external
/// symbol, so a caller that would have inlined it is refused by the converter instead of
/// emitting the refused body's bytes.
///
/// Clean-origin rows are NOT stripped, deliberately (plan step 3.4; docs/DECISION_QUEUE.md
/// STEP3.4-NO-CLEAN-STRIP). Until 3.4 they were left to the codegen license's leg 4, which
/// withheld the whole module; leg 4 is per function now, and what keeps a Clean body that is
/// not admitted out of the bytes is that every F1 lane refuses a `Producer::Clean` body by name,
/// lowered or inlined, with or without a body (`module_to_lir`'s `CleanOriginBelowCodegenGate`,
/// the instance lane's `reaches_clean_body`), and the crate-module lane removes every Clean body
/// from its own lowering context. Stripping one here would break the module's own disclosure
/// validation (a clean-origin `fn:N` row must name a bodied function), which the instance
/// assembler re-runs on every module it extends. A Clean ledger row's conservation verdict
/// ([`judge_clean_row`]) withdraws it from the handoff index instead.
///
/// Trust (step 2 increment 4c): a stripped body keeps nothing that names its values. Before, its
/// `value_names` (and `scopes`) survived with no block to define them, so any consumer that
/// re-validated a module built on the handoff failed `InvalidValueName` on the stripped function
/// (measured: the drop-glue lane's postcondition on `trust_ir_effect_conservation_drop_elided.rs`).
pub fn strip_unconserved_bodies(module: &mut Module, conserved: &BTreeSet<FuncId>) -> usize {
    let mut stripped = 0;
    for f in &mut module.functions {
        if !f.is_declaration()
            && f.producer == Some(trust_ir::Producer::TRust)
            && !conserved.contains(&f.id)
        {
            f.blocks.clear();
            f.value_names = None;
            f.scopes = None;
            f.body_gate = None;
            stripped += 1;
        }
    }
    stripped
}

// ---------------------------------------------------------------------------------------------
// The Clean leg (plan step 3.4, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.3, §12
// item 7). A Clean-origin row has no built MIR, so it cannot be compared with MIR's census; it is
// compared with the census its KERNEL DECLARATION fixes instead. Pure.
// ---------------------------------------------------------------------------------------------

/// The Rust callees — in call order, with multiplicity — that the declaration behind a
/// carrier-gated row of `shape` fixes. Every shape the carrier gate reflects today is call-free,
/// so the answer is empty for all of them. The match is exhaustive on purpose: a shape that
/// calls (plan step 3.1(b)'s `RustCallChain`, whose census is the sealed plan's Rust-callee node
/// list; 3.1(c)'s `Nat` handle entry points with their release discipline) must state its census
/// here before a row of it can be conserved.
pub fn declared_clean_callees(shape: trust_clean_ir_gate::GatedShape) -> Vec<FuncId> {
    use trust_clean_ir_gate::GatedShape;
    match shape {
        GatedShape::Projection { .. }
        | GatedShape::ConstantUint { .. }
        | GatedShape::WrappingBinOp
        | GatedShape::Composed { .. }
        | GatedShape::Select { .. }
        | GatedShape::ComparisonValue
        | GatedShape::BoolNot { .. }
        | GatedShape::BoolConnective { .. } => Vec::new(),
    }
}

/// The census of a Clean-origin Function against `declared` (design §5.3): CONSERVED iff its
/// direct `Call`s are exactly `declared` (callees, order, multiplicity, in block and instruction
/// order) and it has no other effect. DENY BY DEFAULT: an instruction outside the pure scalar
/// vocabulary below is a finding — any store or memory operation, `undef`, an indirect or
/// unwinding call form, a panic check, a drop, a dialect op, a yield, or a constant that is not
/// a scalar literal (a function or global address is an unlisted reference). Empty means
/// conserved.
pub fn judge_clean_census(function: &Function, declared: &[FuncId]) -> Vec<Tag> {
    let mut tags = Vec::new();
    let mut calls: Vec<FuncId> = Vec::new();
    let mut finding = |kind: TagKind, block: BlockId, what: &str| {
        tags.push(Tag {
            kind,
            site: format!("`{}` block {}: {what}", function.name, block.index()),
        });
    };
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::BinOp { .. }
                | Inst::UnOp { .. }
                | Inst::Overflow { .. }
                | Inst::ICmp { .. }
                | Inst::FCmp { .. }
                | Inst::Cast { .. }
                | Inst::Select { .. }
                | Inst::Copy { .. }
                | Inst::ExtractField { .. }
                | Inst::InsertField { .. }
                | Inst::ExtractElement { .. }
                | Inst::InsertElement { .. }
                | Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. } => {}
                Inst::Const { value, .. } => {
                    if !matches!(value, Constant::Int(_) | Constant::U128(_) | Constant::Bool(_)) {
                        finding(
                            TagKind::NotConserved(Effect::Census),
                            block.id,
                            &format!("a constant outside the scalar vocabulary ({value:?})"),
                        );
                    }
                }
                Inst::Call { callee, .. } => calls.push(*callee),
                Inst::Undef { .. } => {
                    finding(TagKind::Abstracted(Lane::Undef), block.id, "an `undef` value")
                }
                Inst::Store { .. }
                | Inst::AtomicStore { .. }
                | Inst::AtomicRMW { .. }
                | Inst::CmpXchg { .. }
                | Inst::MemCopy { .. }
                | Inst::MemSet { .. } => {
                    finding(TagKind::NotConserved(Effect::Store), block.id, "a store")
                }
                Inst::CallIndirect { .. }
                | Inst::CallIndirectCannotUnwind { .. }
                | Inst::InvokeIndirect { .. } => finding(
                    TagKind::NotConserved(Effect::IndirectCall),
                    block.id,
                    "an indirect call",
                ),
                Inst::Invoke { .. }
                | Inst::CallCannotUnwind { .. }
                | Inst::AssertInvoke { .. }
                | Inst::DropInvoke { .. } => finding(
                    TagKind::NotConserved(Effect::Call),
                    block.id,
                    "a call form the declaration's census does not spell",
                ),
                Inst::Assert { .. } => {
                    finding(TagKind::NotConserved(Effect::Assert), block.id, "a panic check")
                }
                Inst::Drop { .. } => {
                    finding(TagKind::NotConserved(Effect::Drop), block.id, "a drop")
                }
                Inst::CoroSuspend { .. } => {
                    finding(TagKind::NotConserved(Effect::Yield), block.id, "a yield")
                }
                other => finding(
                    TagKind::NotConserved(Effect::Census),
                    block.id,
                    &format!("`{:?}`, outside the Clean leg's census vocabulary", other.shape()),
                ),
            }
        }
    }
    if calls != declared {
        let render = |ids: &[FuncId]| {
            ids.iter().map(|id| format!("FuncId({})", id.index())).collect::<Vec<_>>().join(", ")
        };
        tags.push(Tag {
            kind: TagKind::NotConserved(Effect::Call),
            site: format!(
                "`{}` calls [{}] where its declaration fixes [{}] (callees, order and \
                 multiplicity must be equal)",
                function.name,
                render(&calls),
                render(declared)
            ),
        });
    }
    tags
}

/// THE CLEAN LEG for one session-ledger entry in `module` (the handoff's module): the entry must
/// authenticate its Function (`AuthenticatedCleanRow::authenticate_in`), and the Function's
/// census must be the one its declaration fixes ([`declared_clean_callees`] of the shape the gate
/// reflected). Empty means conserved.
pub fn judge_clean_row(module: &Module, row: &crate::AuthenticatedCleanRow) -> Vec<Tag> {
    if let Err(reason) = row.authenticate_in(module) {
        return vec![Tag { kind: TagKind::NotConserved(Effect::Census), site: reason }];
    }
    let Some(function) = module.function_by_id(row.func_id()) else {
        return vec![Tag {
            kind: TagKind::NotConserved(Effect::Census),
            site: format!("the ledger entry names missing FuncId({})", row.func_id().index()),
        }];
    };
    judge_clean_census(function, &declared_clean_callees(row.published().shape()))
}

/// VERIFICATION admission for `def`: a body whose every tag is in `accepted` may be READ as a
/// model. Never use this for codegen or strict.
pub fn admit_for_verification(
    sess: &rustc_session::Session,
    def: LocalDefId,
    accepted: &[TagKind],
) -> Result<(), String> {
    sess.with_trust_compiler_state::<ConservationVerdicts, _>(|v| {
        if !v.ran {
            return Err("the effect-conservation check did not run in this session".to_string());
        }
        match v.by_def.get(&def.local_def_index.as_u32()) {
            None => Err("the effect-conservation check has no verdict for this body".to_string()),
            Some(b) => {
                let refused = refused_for_verification(&b.tags, accepted);
                if refused.is_empty() { Ok(()) } else { Err(render_tags(&refused)) }
            }
        }
    })
}

/// The tags of a verdict that a verification reader accepting `accepted` refuses: the one
/// acceptance rule of [`admit_for_verification`] and [`ReaderJudge`]'s readers.
pub fn refused_for_verification(tags: &[Tag], accepted: &[TagKind]) -> Vec<Tag> {
    tags.iter().filter(|t| !accepted.contains(&t.kind)).cloned().collect()
}

/// Trust (spawn census P4): the effect-conservation judgement of a body's per-body lowering
/// for an in-process READER of the module `trust_ir_of` returns for it, made BEFORE
/// [`finalize`] drains the registries. The census's trust-ir shadow lane reads at the analysis
/// seam, ahead of crate finalization and of the front-end error gate, so the verdicts
/// [`admit_for_verification`] serves do not exist yet when it reads.
///
/// Rules 1 and 2 are [`judge`]'s, on the census the mainline lowering recorded, over the same
/// session-wide set of collapsed enum types: every body owner's `mir_built` (and with it every
/// mainline lowering) ran in `run_required_analyses`, before the seam. Rule 3 binds the
/// ASSEMBLED function to the per-body one; a reader of the per-body module reads no assembled
/// function, so in its place the function the reader walks must have the effect shape of the
/// lowering that was judged (the query lowers the body a second time), else
/// `not-conserved(splice)`. A body with no producer record, a duplicated record or no MIR
/// census is `not-conserved(census)`: absent is never conserved.
pub struct ReaderJudge {
    collapsed: BTreeSet<u128>,
}

impl ReaderJudge {
    /// What every judgement of this session shares: the enum types any lowering collapsed.
    pub fn new(tcx: TyCtxt<'_>) -> Self {
        let collapsed = tcx.sess.with_trust_compiler_state::<CensusRegistry, _>(|r| {
            r.producer.values().flat_map(|p| p.collapsed_enums.iter().copied()).collect()
        });
        ReaderJudge { collapsed }
    }

    /// The tags of `def`'s lowering, read as `read` (a function of `module`, the body the reader
    /// walks). Empty means CONSERVED.
    pub fn tags(
        &self,
        tcx: TyCtxt<'_>,
        def: LocalDefId,
        module: &Module,
        read: &Function,
    ) -> Vec<Tag> {
        let index = def.local_def_index.as_u32();
        let (mir, producer, duplicated) =
            tcx.sess.with_trust_compiler_state::<CensusRegistry, _>(|r| {
                (
                    r.mir.get(&index).cloned(),
                    r.producer.get(&index).cloned(),
                    r.duplicated.contains(&index),
                )
            });
        let census = |site: &str| {
            vec![Tag { kind: TagKind::NotConserved(Effect::Census), site: site.to_string() }]
        };
        if duplicated {
            return census("the body was recorded twice; its census is not trusted");
        }
        let Some(producer) = producer else {
            return census("no producer census was recorded for this body");
        };
        let Some(mir) = mir else {
            return census("no MIR census was recorded for this body");
        };
        let (mut tags, _) = judge(tcx, &mir, &producer, &self.collapsed);
        let shape = ir_shape(module, read);
        if shape != producer.shape {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Splice),
                site: format!(
                    "the function read has effect shape {shape:?}, the lowering judged {:?}",
                    producer.shape
                ),
            });
        }
        tags
    }
}

/// `n tag(s): T1; T2; …`, at most eight tags spelled out.
pub fn render_tags(tags: &[Tag]) -> String {
    let mut shown: Vec<String> = tags.iter().take(8).map(Tag::to_string).collect();
    if tags.len() > 8 {
        shown.push(format!("… and {} more", tags.len() - 8));
    }
    format!("{} tag(s): {}", tags.len(), shown.join("; "))
}

/// Render a span as `file.rs:line:col` (file name only; stable across checkouts).
fn render_span(tcx: TyCtxt<'_>, span: Span) -> String {
    if span.is_dummy() {
        return String::new();
    }
    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
    let name = loc.file.name.prefer_remapped_unconditionally().to_string();
    let base = name.rsplit(['/', '\\']).next().unwrap_or(&name).to_string();
    format!("{base}:{}:{}", loc.line, loc.col.0 + 1)
}

fn render_site(tcx: TyCtxt<'_>, effect: &MirEffect) -> String {
    let at = render_span(tcx, effect.span);
    let what = match &effect.kind {
        MirEffectKind::Call { ids, .. } => {
            let d = ids[0];
            format!("`{}`", rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(d)))
        }
        MirEffectKind::IndirectCall => "an indirect call".to_string(),
        MirEffectKind::Store(MemRoot::Arg(i)) => format!("a store through argument {i}"),
        MirEffectKind::Store(MemRoot::Static) => "a store to a static".to_string(),
        MirEffectKind::Store(MemRoot::Indirect) => "a store through a loaded pointer".to_string(),
        MirEffectKind::Drop { .. } => "a drop".to_string(),
        MirEffectKind::Assert(class) => class.name().to_string(),
        MirEffectKind::Asm { .. } => "inline asm".to_string(),
        MirEffectKind::Yield => "a yield".to_string(),
    };
    if at.is_empty() { what } else { format!("{what} at {at}") }
}

// The drop oracle supplies the drop judgement. Preserve original exact-store
// bindings when the count-only drop effects are removed for other pairing.
fn without_drop_effects<Identity: Clone, Site: Clone, Location: Clone, Oracle: Clone>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
) -> MirCensus<Identity, Site, Location, Oracle> {
    let mut filtered = mir.clone();
    filtered.effects.clear();
    filtered.exact_store_args.clear();
    for (original, effect) in mir.effects.iter().enumerate() {
        if !matches!(effect.kind, MirEffectKind::Drop { .. }) {
            if let Some(&argument) = mir.exact_store_args.get(&original) {
                filtered.exact_store_args.insert(filtered.effects.len(), argument);
            }
            filtered.effects.push(effect.clone());
        }
    }
    filtered
}

// The pure abstraction part of the production judgement, shared by the
// refusal tests; source-site rendering contributes no admission authority.
fn judgement_abstractions<Identity: Eq, Site: Eq, Location, Oracle>(
    mir: &MirCensus<Identity, Site, Location, Oracle>,
    ir: &IrCensus<Identity, Site>,
    collapsed: &BTreeSet<u128>,
) -> Abstractions {
    let mut a = ir.abstractions;
    a.placeholder_values = placeholder_values(mir, ir);
    a.collapsed_enum_values = mir.enum_types.intersection(collapsed).count();
    a
}

/// Judge one body (see the module doc). Pure apart from rendering sites.
fn judge(
    tcx: TyCtxt<'_>,
    mir: &MirCensus,
    producer: &ProducerBody,
    collapsed: &BTreeSet<u128>,
) -> (Vec<Tag>, BTreeMap<&'static str, usize>) {
    let mut tags = Vec::new();
    let mut equivalences: BTreeMap<&'static str, usize> = BTreeMap::new();
    // Trust (step 2 increment 4b): with the drop oracle, drops are judged by `drop_leg` against
    // rustc's elaboration, and the by-count pairing of the census's drop effects is not used.
    let filtered;
    let mir = if !producer.const_context && mir.drop_oracle.is_some() {
        filtered = without_drop_effects(mir);
        tags.extend(drop_leg(tcx, mir, producer));
        &filtered
    } else {
        if !producer.const_context
            && (producer.drop_claim.is_some() || producer.census.shape.drops > 0)
        {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Census),
                site: "the body carries drops but the drop oracle could not run on its MIR"
                    .to_string(),
            });
        }
        mir
    };
    if !producer.const_context {
        for u in unpaired_effects(mir, &producer.census) {
            let site = match u.kind {
                TagKind::Abstracted(Lane::Destructor) => {
                    let MirEffect { span, .. } = &mir.effects[u.mir_index];
                    let at = render_span(tcx, *span);
                    if at.is_empty() {
                        "a drop whose glue may run a destructor".to_string()
                    } else {
                        format!("a drop whose glue may run a destructor, e.g. at {at}")
                    }
                }
                _ => render_site(tcx, &mir.effects[u.mir_index]),
            };
            tags.push(Tag { kind: u.kind, site });
        }
        // Disclose the equivalences that carried an UNPAIRED call (a call the trust-ir also
        // carries is paired by identity and is not counted here).
        equivalences = unpaired_equivalences(mir, &producer.census);
    }
    let a = judgement_abstractions(mir, &producer.census, collapsed);
    for kind in abstraction_kinds(&a) {
        let site = match kind {
            TagKind::Abstracted(Lane::Undef) => format!("{} undef value(s)", a.undefs),
            TagKind::Abstracted(Lane::OpaqueLane) => {
                let mut why = Vec::new();
                if a.collapsed_enum_values > 0 {
                    why.push(format!(
                        "{} enum type(s) held by value that the producer spells as a lone \
                         `bool`/`()` placeholder (the Option-discriminant / opaque `()` lane)",
                        a.collapsed_enum_values
                    ));
                }
                if a.degraded_struct_touches > 0 {
                    why.push(format!(
                        "{} use(s) of a degraded struct profile (`()` / discriminant-`bool` \
                         placeholder fields)",
                        a.degraded_struct_touches
                    ));
                }
                if a.placeholder_values > 0 {
                    why.push(format!(
                        "{} enum value(s) spelled as a lone `bool`/`()`",
                        a.placeholder_values
                    ));
                }
                why.join(", ")
            }
            TagKind::Abstracted(Lane::UnionLane) => {
                "a union field or value spelled as a `()` placeholder".to_string()
            }
            TagKind::Abstracted(Lane::EnumParamLane) => {
                "an enum field of a bare type parameter spelled as a `()` placeholder".to_string()
            }
            _ => String::new(),
        };
        tags.push(Tag { kind, site });
    }
    (tags, equivalences)
}

/// The drop leg of [`judge`] (step 2 increment 4b): the producer's drop claim against the
/// drop oracle, plus the oracle / census cross-check.
fn drop_leg(tcx: TyCtxt<'_>, mir: &MirCensus, producer: &ProducerBody) -> Vec<Tag> {
    let mut tags = Vec::new();
    let Some(oracle) = &mir.drop_oracle else { return tags };
    // The census's own init analysis is coarser than rustc's dataflow (it keeps a drop live
    // whenever it cannot see through the place), never finer: a drop it proved dead that the
    // oracle calls live means one of the two readings of the same MIR is wrong.
    for (d, _) in oracle {
        if d.style.is_some() && mir.drop_dead_blocks.contains(&d.block.as_u32()) {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Census),
                site: format!(
                    "the drop oracle and the census's init analysis disagree on the drop at {}",
                    render_span(tcx, d.span)
                ),
            });
        }
    }
    let live: Vec<(DropKey, bool)> = oracle
        .iter()
        .filter_map(|(d, destructor)| {
            d.style.map(|style| {
                (DropKey { identity: d.identity, ty: d.ty, span: d.span, style }, *destructor)
            })
        })
        .collect();
    let keys: Vec<DropKey> = live.iter().map(|(k, _)| *k).collect();
    let claim = producer.drop_claim.as_ref().map(|c| (c.live.as_slice(), c.emitted));
    let cmp = compare_drops(&keys, claim, producer.census.shape.drops);
    let describe = |k: &DropKey| {
        let who = match k.identity {
            crate::drops::DropIdentity::Param(i) => format!("parameter {i}"),
            crate::drops::DropIdentity::Var(_) => "a binding".to_string(),
            crate::drops::DropIdentity::Other => "a temporary or a projected place".to_string(),
        };
        let at = render_span(tcx, k.span);
        let style = match k.style {
            crate::drops::LiveStyle::Static => "",
            crate::drops::LiveStyle::Conditional => " (behind a drop flag)",
            crate::drops::LiveStyle::Open => " (open: per-field)",
        };
        if at.is_empty() {
            format!("a drop of {who}{style}")
        } else {
            format!("a drop of {who}{style} at {at}")
        }
    };
    for &i in &cmp.missing {
        let mut site = describe(&live[i].0);
        if let Some(why) = &producer.drop_refusal {
            site.push_str(&format!(" (the producer placed no drop: {why})"));
        }
        tags.push(Tag { kind: TagKind::Abstracted(Lane::Drop), site });
    }
    if let Some(&i) = cmp.missing.iter().find(|&&i| live[i].1) {
        let at = render_span(tcx, live[i].0.span);
        tags.push(Tag {
            kind: TagKind::Abstracted(Lane::Destructor),
            site: if at.is_empty() {
                "a drop whose glue may run a destructor".to_string()
            } else {
                format!("a drop whose glue may run a destructor, e.g. at {at}")
            },
        });
    }
    if let Some(c) = &producer.drop_claim {
        for &j in &cmp.extra {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Drop),
                site: format!("{}, which the program does not perform", describe(&c.live[j])),
            });
        }
    } else if producer.census.shape.drops > 0 {
        tags.push(Tag {
            kind: TagKind::NotConserved(Effect::Drop),
            site: "the body carries drops the producer never claimed".to_string(),
        });
    }
    if let Some((recorded, carried)) = cmp.ledger {
        if producer.drop_claim.is_some() {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Drop),
                site: format!(
                    "the producer recorded {recorded} drop(s) and the body carries {carried}"
                ),
            });
        }
    }
    tags
}

/// Read the assembler's exact definition assignment. Function names are link-time symbols
/// and display paths may collide; neither is a substitute for the local definition identity.
fn published_function(
    published: &crate::crate_module::PublishedCrateModule,
    def: LocalDefId,
) -> Option<FuncId> {
    let id = published.direct_function_for_definition(def.local_def_index.as_u32())?;
    let f = published.module().function_by_id(id)?;
    (!f.is_declaration() && f.producer == Some(trust_ir::Producer::TRust)).then_some(id)
}

/// One body's verdict as [`finalize`] reports it to its caller.
pub struct BodyReport {
    pub def: LocalDefId,
    pub def_path: String,
    /// The producer pushed no `unsupported` tag (strict's per-body arm already passed it).
    pub clean: bool,
    /// Found in the published module / codegen handoff.
    pub spliced: bool,
    pub tags: Vec<Tag>,
    pub classes: Vec<String>,
    pub equivalences: BTreeMap<&'static str, usize>,
}

/// What [`finalize`] hands back to the caller (`rustc_mir_build::trust_ir_crate_finalize`), which
/// owns the strict policy, the diagnostics and the scorecard event.
#[derive(Default)]
pub struct FinalizeOutcome {
    pub bodies: Vec<BodyReport>,
}

/// THE FINALIZE-TIME CHECK. Drains both census registries, judges every body the mainline
/// lowering recorded, checks the splice consistency of every assembled body it can find, then:
/// installs the verdicts for in-process consumers ([`ConservationVerdicts`]), withdraws every
/// refused body from the F1 codegen handoff and marks the handoff checked, writes the sidecar
/// beside a requested dump / `--emit=trust-ir` artifact, and returns the refusals for strict.
///
/// Wired from `rustc_mir_build::trust_ir_crate_finalize` right after
/// `crate_module::finalize_and_dump` (frozen; this file is not), so the published module and the
/// handoff it reads are the final ones.
pub fn finalize(tcx: TyCtxt<'_>) -> FinalizeOutcome {
    let registry = tcx.sess.with_trust_compiler_state::<CensusRegistry, _>(std::mem::take);
    // Every enum type any lowering collapsed to a placeholder (the collapse is a function of the
    // type, so one body's collapse speaks for every body).
    let collapsed: BTreeSet<u128> =
        registry.producer.values().flat_map(|p| p.collapsed_enums.iter().copied()).collect();
    // The F1 handoff's exact (DefIndex -> FuncId) map, when the codegen frontend installed one.
    let handoff_ids: Option<BTreeMap<u32, FuncId>> =
        tcx.sess.with_trust_compiler_state::<crate::AssembledCrateModuleForCodegen, _>(|h| {
            h.module.as_ref().map(|_| h.bodies.iter().map(|b| (b.def_index, b.func_id)).collect())
        });

    let mut verdicts: BTreeMap<u32, BodyVerdict> = BTreeMap::new();
    let mut outcome = FinalizeOutcome::default();
    for (index, producer) in &registry.producer {
        let def = LocalDefId { local_def_index: DefIndex::from_u32(*index) };
        let (mut tags, equivalences) = match registry.mir.get(index) {
            _ if registry.duplicated.contains(index) => (
                vec![Tag {
                    kind: TagKind::NotConserved(Effect::Census),
                    site: "the body was recorded twice; its census is not trusted".to_string(),
                }],
                BTreeMap::new(),
            ),
            None => (
                vec![Tag {
                    kind: TagKind::NotConserved(Effect::Census),
                    site: "no MIR census was recorded for this body".to_string(),
                }],
                BTreeMap::new(),
            ),
            Some(mir) => judge(tcx, mir, producer, &collapsed),
        };
        // Splice consistency, against the module codegen and every reader actually get.
        let assembled = crate::crate_module::with_published_crate_module(tcx.sess, |p| {
            let p = p.ok()?;
            let id = match &handoff_ids {
                Some(ids) => ids.get(index).copied(),
                None => None,
            }
            .or_else(|| published_function(p, def))?;
            let f = p.module().function_by_id(id)?;
            Some((id, ir_shape(p.module(), f)))
        });
        if let Some((_, shape)) = assembled.as_ref().filter(|(_, shape)| *shape != producer.shape) {
            tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Splice),
                site: format!(
                    "the assembled function's effect shape {shape:?} differs from the lowered \
                     body's {:?}",
                    producer.shape
                ),
            });
        }
        let verdict = BodyVerdict {
            def_path: producer.def_path.clone(),
            clean: producer.clean,
            tags,
            assembled: assembled.map(|(id, _)| id),
            equivalences,
            drop_claim_live: producer.drop_claim.as_ref().map(|c| c.live.len()),
            drop_sites: producer.drop_claim.as_ref().map(|c| c.sites.clone()).unwrap_or_default(),
        };
        outcome.bodies.push(BodyReport {
            def,
            def_path: verdict.def_path.clone(),
            clean: verdict.clean,
            spliced: verdict.assembled.is_some(),
            tags: verdict.tags.clone(),
            classes: verdict.classes(),
            equivalences: verdict.equivalences.clone(),
        });
        verdicts.insert(*index, verdict);
    }

    // Trust (plan step 3.4, design §5.3): THE CLEAN LEG. Every entry of this Session's carrier
    // ledger is judged against the census its declaration fixes ([`judge_clean_row`]), and the
    // verdict is keyed by the Clean def's DefIndex beside the Rust bodies', so the handoff
    // withdraws an unconserved row and keeps a conserved one in the lowering context. A ledger
    // this Session did not install is refused: every entry is a finding. Clean rows are not
    // reported to strict (`outcome.bodies`): strict's arm is about the direct producer's bodies.
    let ledger_session = crate::CleanLedgerSession::of(tcx.sess);
    let clean_verdicts: Vec<(u32, BodyVerdict)> =
        tcx.sess.with_trust_compiler_state::<crate::AssembledCrateModuleForCodegen, _>(|h| {
            let Some(module) = h.module.as_ref() else { return Vec::new() };
            let judged: Vec<(&crate::AuthenticatedCleanRow, Vec<Tag>)> = match h
                .clean_ledger(ledger_session)
            {
                Ok(rows) => rows.iter().map(|row| (row, judge_clean_row(module, row))).collect(),
                Err(reason) => h
                    .clean
                    .iter()
                    .map(|row| {
                        let tag = Tag {
                            kind: TagKind::NotConserved(Effect::Census),
                            site: reason.clone(),
                        };
                        (row, vec![tag])
                    })
                    .collect(),
            };
            judged
                .into_iter()
                .map(|(row, tags)| {
                    let verdict = BodyVerdict {
                        def_path: row.published().rust_def_path().to_string(),
                        clean: true,
                        tags,
                        assembled: Some(row.func_id()),
                        equivalences: BTreeMap::new(),
                        drop_claim_live: None,
                        drop_sites: Vec::new(),
                    };
                    (row.def_index(), verdict)
                })
                .collect()
        });
    for (index, verdict) in clean_verdicts {
        match verdicts.get_mut(&index) {
            // A Clean def and a recorded Rust body share no DefIndex; if they ever did, neither
            // verdict stands (fail-closed), rather than one silently replacing the other.
            Some(existing) => existing.tags.push(Tag {
                kind: TagKind::NotConserved(Effect::Census),
                site: format!(
                    "DefIndex({index}) is both a recorded Rust body and a Clean carrier ledger \
                     entry"
                ),
            }),
            None => {
                verdicts.insert(index, verdict);
            }
        }
    }

    // Withdraw every refused body from the codegen handoff, strip it from the handoff's lowering
    // context (a conserved caller must not inline it), and mark the handoff checked.
    let conserved_ids: BTreeSet<FuncId> =
        verdicts.values().filter(|v| v.conserved()).filter_map(|v| v.assembled).collect();
    let source_count = crate::crate_module::with_published_crate_module(tcx.sess, |p| {
        p.ok().map(|p| p.direct_source_count()).unwrap_or(0)
    });
    tcx.sess.with_trust_compiler_state::<crate::AssembledCrateModuleForCodegen, _>(|h| {
        if let Some(module) = &h.module {
            // Adapters have no Rust DefIndex/MIR body. Authenticate their own
            // exact protocol against two independently conserved source rows.
            let adapters = closure_adapters::derive(
                module,
                source_count,
                &conserved_ids,
                crate::crate_module::TRUST_DIRECT_LANE_AUTHORITY,
            );
            let context: BTreeSet<_> =
                conserved_ids.iter().copied().chain(adapters.keys().copied()).collect();
            let mut stripped = (**module).clone();
            strip_unconserved_bodies(&mut stripped, &context);
            h.module = Some(std::sync::Arc::new(stripped));
        }
        let withdrawn: BTreeMap<FuncId, String> = h
            .bodies
            .iter()
            .filter_map(|b| match verdicts.get(&b.def_index) {
                Some(v) if v.conserved() => None,
                Some(v) => Some((b.func_id, render_tags(&v.tags))),
                None => Some((
                    b.func_id,
                    "the effect-conservation check has no verdict for this body".to_string(),
                )),
            })
            .collect();
        h.conservation = crate::HandoffConservation::Checked { withdrawn };
    });

    if let Err(error) = write_sidecar(tcx, &verdicts) {
        tcx.dcx().warn(format!("trust-ir effect-conservation sidecar not written: {error}"));
    }
    // Trust (step 2 increment 6, step 6.5.1; INC6.5-JUDGE): judge every LEVEL-S template
    // lowering, after the mainline verdicts and the sidecar are final and before the MIR census
    // map is handed to `retain_evidence`. The same `judge`, against the same MIR census of the
    // definition, over `collapsed_t`: the mainline set (computed above exactly as before) united
    // with the templates' own collapses. No splice-consistency leg (a template is never spliced).
    // The verdicts go to `template_by_def` only: never `outcome.bodies`, the sidecar or `by_def`.
    let collapsed_t: BTreeSet<u128> = collapsed
        .iter()
        .copied()
        .chain(registry.template.values().flat_map(|p| p.collapsed_enums.iter().copied()))
        .collect();
    let template_verdicts: BTreeMap<u32, BodyVerdict> = registry
        .template
        .iter()
        .map(|(index, template)| {
            let (tags, equivalences) = if registry.template_duplicated.contains(index)
                || registry.duplicated.contains(index)
            {
                (
                    vec![Tag {
                        kind: TagKind::NotConserved(Effect::Census),
                        site: "the body or its template was recorded twice; its census is not \
                               trusted"
                            .to_string(),
                    }],
                    BTreeMap::new(),
                )
            } else {
                match registry.mir.get(index) {
                    None => (
                        vec![Tag {
                            kind: TagKind::NotConserved(Effect::Census),
                            site: "no MIR census was recorded for this body".to_string(),
                        }],
                        BTreeMap::new(),
                    ),
                    Some(mir) => judge(tcx, mir, template, &collapsed_t),
                }
            };
            let verdict = BodyVerdict {
                def_path: template.def_path.clone(),
                clean: template.clean,
                tags,
                assembled: None,
                equivalences,
                drop_claim_live: template.drop_claim.as_ref().map(|c| c.live.len()),
                drop_sites: template
                    .drop_claim
                    .as_ref()
                    .map(|c| c.sites.clone())
                    .unwrap_or_default(),
            };
            (*index, verdict)
        })
        .collect();
    // Trust (step 2 increment 6, step 6.1): an rmeta entry carries the inputs of this verdict
    // (the MIR census, the drop claim, the collapsed enum types, the degraded rows and lanes),
    // never the verdict, so a consumer re-derives it (D4, D39 (ii)). Keep them for the entry
    // builder, which runs when metadata is encoded. Step 6.5.1: a definition with a template
    // record keeps the template's producer half and the set its template was judged with.
    let mut registry = registry;
    crate::rmeta_entry::retain_evidence(
        tcx,
        &mut registry.mir,
        &mut registry.producer,
        &mut registry.template,
        &collapsed,
        &collapsed_t,
    );
    tcx.sess.with_trust_compiler_state::<ConservationVerdicts, _>(|v| {
        v.ran = true;
        v.by_def = verdicts;
        v.template_by_def = template_verdicts;
    });
    outcome
}

// ---------------------------------------------------------------------------------------------
// The sidecar: `<crate>.effect-conservation.json` beside a dump / `--emit=trust-ir` artifact.
// ---------------------------------------------------------------------------------------------

/// The sidecar schema name. A reader refuses any other.
pub const SIDECAR_SCHEMA: &str = "trust.effect-conservation.v1";

/// FNV-1a 64 of `bytes`: binds the sidecar to the exact `.trust-ir.txt` it describes (a stale
/// sidecar beside a fresh dump is refused by a reader that recomputes it). Staleness detection,
/// not an authentication: nothing here is a trust boundary.
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Render the sidecar for `module_text` (the dumped canonical text) and the verdicts of the
/// functions it carries. One body per line, so a line-oriented reader can parse it.
pub fn render_sidecar(
    crate_name: &str,
    text_name: &str,
    module_text: &[u8],
    rows: &[(String, &BodyVerdict)],
) -> String {
    render_sidecar_with_adapters(crate_name, text_name, module_text, rows, &BTreeMap::new())
}

fn render_sidecar_with_adapters(
    crate_name: &str,
    text_name: &str,
    module_text: &[u8],
    rows: &[(String, &BodyVerdict)],
    adapters: &BTreeMap<FuncId, closure_adapters::Witness>,
) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"schema\": {},\n", json_str(SIDECAR_SCHEMA)));
    out.push_str(&format!("  \"crate\": {},\n", json_str(crate_name)));
    out.push_str(&format!(
        "  \"module_text\": {{ \"name\": {}, \"bytes\": {}, \"fnv1a64\": \"{:016x}\" }},\n",
        json_str(text_name),
        module_text.len(),
        fnv1a64(module_text)
    ));
    out.push_str(
        "  \"rule\": \"a function listed `refused` is not the program: it is never codegen-licensed \
         and never passes -Ztrust-ir-lower=strict; a verification reader may read it only by \
         accepting every one of its tags by name (docs/DECISION_QUEUE.md D28)\",\n",
    );
    out.push_str("  \"functions\": [\n");
    for (i, (name, v)) in rows.iter().enumerate() {
        let tags: Vec<String> = v.classes().iter().map(|c| json_str(c)).collect();
        let details: Vec<String> = v.tags.iter().map(|t| json_str(&t.to_string())).collect();
        let equivalences: Vec<String> = v
            .equivalences
            .iter()
            .map(|(name, count)| format!("{}: {count}", json_str(name)))
            .collect();
        let basis = v
            .assembled
            .and_then(|id| adapters.get(&id))
            .map(|w| format!(", \"basis\": {}", w.disclosure()))
            .unwrap_or_default();
        out.push_str(&format!(
            "    {{ \"function\": {}, \"def_path\": {}, \"verdict\": \"{}\", \"tags\": [{}], \
             \"detail\": [{}], \"equivalences\": {{{}}}{basis} }}{}\n",
            json_str(name),
            json_str(&v.def_path),
            if v.conserved() { "conserved" } else { "refused" },
            tags.join(", "),
            details.join(", "),
            equivalences.join(", "),
            if i + 1 == rows.len() { "" } else { "," }
        ));
    }
    out.push_str("  ]\n}\n");
    out
}

/// Write the sidecar beside every requested artifact. Every function of the published module
/// that is a direct-lane BODY gets a row. An authenticated typed adapter names
/// its separate derived owner/body basis; every other body with no verdict is `refused`
/// with `not-conserved(census)`, so a reader can never mistake an absent row for a clean one.
fn write_sidecar(tcx: TyCtxt<'_>, verdicts: &BTreeMap<u32, BodyVerdict>) -> Result<(), String> {
    let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE).to_string();
    let mut targets: Vec<(std::path::PathBuf, std::path::PathBuf)> = Vec::new();
    if let Some(dir) = tcx.sess.opts.unstable_opts.trust_dump.ir.clone() {
        targets.push((
            dir.join(format!("{crate_name}.trust-ir.txt")),
            dir.join(format!("{crate_name}.effect-conservation.json")),
        ));
    }
    if crate::crate_module::emit_requested(tcx) {
        if let rustc_session::config::OutFileName::Real(p) =
            tcx.output_filenames(()).path(rustc_session::config::OutputType::TrustIr)
        {
            targets.push((p.with_extension("txt"), p.with_extension("effect-conservation.json")));
        }
    }
    if targets.is_empty() {
        return Ok(());
    }
    let by_func: BTreeMap<FuncId, &BodyVerdict> =
        verdicts.values().filter_map(|v| v.assembled.map(|id| (id, v))).collect();
    let missing = BodyVerdict {
        def_path: String::new(),
        clean: false,
        tags: vec![Tag {
            kind: TagKind::NotConserved(Effect::Census),
            site: "no effect-conservation verdict for this function".to_string(),
        }],
        assembled: None,
        equivalences: BTreeMap::new(),
        drop_claim_live: None,
        drop_sites: Vec::new(),
    };
    // The rows, and the module text they describe — RENDERED from the published module (the
    // dump's text is `trust_ir::format::canonical` of this same module), never re-read from disk:
    // a concurrent compile into the same directory may have replaced the file since, and binding
    // this compile's verdicts to another compile's text is exactly the mix-up the binding exists
    // to refuse.
    let source_ids: BTreeSet<_> =
        verdicts.values().filter(|v| v.conserved()).filter_map(|v| v.assembled).collect();
    let rendered: Option<(
        Vec<(String, FuncId)>,
        Vec<u8>,
        BTreeMap<FuncId, closure_adapters::Witness>,
    )> = crate::crate_module::with_published_crate_module(tcx.sess, |p| {
        let p = p.ok()?;
        let rows = p
            .module()
            .functions
            .iter()
            .filter(|f| !f.is_declaration() && f.producer == Some(trust_ir::Producer::TRust))
            .map(|f| (f.name.clone(), f.id))
            .collect();
        let adapters = closure_adapters::derive(
            p.module(),
            p.direct_source_count(),
            &source_ids,
            crate::crate_module::TRUST_DIRECT_LANE_AUTHORITY,
        );
        Some((rows, trust_ir::format::canonical(p.module()).into_bytes(), adapters))
    });
    // No published module: the dump was not written either (publication and the dump share the
    // finalizer's error gate), so there is nothing to describe; remove a stale sidecar. A sidecar
    // left by an earlier generation is harmless anyway — it is bound to the text it described.
    for (text_path, sidecar_path) in targets {
        match (&rendered, text_path.is_file()) {
            (Some((names, text, adapters)), true) => {
                // These rows disclose a separate derived basis; they never enter
                // by_def, the MIR registry, strict's source count or proof grades.
                let derived: BTreeMap<_, _> = adapters
                    .keys()
                    .map(|id| {
                        (
                            *id,
                            BodyVerdict {
                                def_path: String::new(),
                                clean: false,
                                tags: Vec::new(),
                                assembled: Some(*id),
                                equivalences: BTreeMap::new(),
                                drop_claim_live: None,
                                drop_sites: Vec::new(),
                            },
                        )
                    })
                    .collect();
                let rows: Vec<_> = names
                    .iter()
                    .map(|(name, id)| {
                        (
                            name.clone(),
                            by_func
                                .get(id)
                                .copied()
                                .or_else(|| derived.get(id))
                                .unwrap_or(&missing),
                        )
                    })
                    .collect();
                let name = text_path
                    .file_name()
                    .map(|n| n.to_string_lossy().into_owned())
                    .unwrap_or_default();
                let body = render_sidecar_with_adapters(&crate_name, &name, text, &rows, adapters);
                // Write-then-rename, so a reader never sees a partial ledger.
                let tmp = sidecar_path.with_extension(format!("json.tmp-{}", std::process::id()));
                std::fs::write(&tmp, body)
                    .and_then(|()| std::fs::rename(&tmp, &sidecar_path))
                    .map_err(|e| format!("{}: {e}", sidecar_path.display()))?;
            }
            _ => {
                let _ = std::fs::remove_file(&sidecar_path);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "effect_conservation/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "effect_conservation/init_worklist_tests.rs"]
mod init_worklist_tests;
