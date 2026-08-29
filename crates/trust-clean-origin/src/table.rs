// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **THE INSTRUCTION-SELECTION TABLE** — §6f landing 1.
//!
//! §6f's ruling: one general Clean→MIR emitter, one general MIR→Clean
//! reflector, and `CleanOriginShape` demoted from a capability boundary to an
//! **optimization ladder**. Landing 1 is the refactor with ZERO capability
//! change: the six ladder rungs that shipped as six co-ordinated *arms* —
//! `Projection`, `InductiveProjection`, `WrappingBinOp`, `Composed`, `Select`,
//! `SelectLiteral`, `StructuralNatRec`, `WellFoundedNatRec` — are re-expressed
//! as ROWS in this one table, read by one recursive-descent reflector
//! ([`crate::reflect`]). Nothing this landing does changes what is admitted or
//! refused; the acceptance is that every pre-existing control and probe passes
//! **unmodified**.
//!
//! # The invariant that keeps the table from becoming authority
//!
//! > **The table selects VOCABULARY. The readers own DATAFLOW.**
//!
//! A row says *which primitive* a node is. It can never say *how* an extracted
//! body's temporaries, blocks and operands compose into a tree — that stays
//! entirely inside `trust_types::admissible_body`, table-independent, and is
//! the part a row author cannot reach.
//!
//! # THE DOUBLE FAULT, AND WHY THIS TABLE DOES NOT COLLAPSE IT
//!
//! `docs/TCB.md` rests the Clean-origin reflection row on a **double fault**:
//! *"a rendering bug alone is caught structurally, a recognition bug alone is
//! caught by the kernel."* That works because there are **two independent
//! readings of one body**, authored in different crates for different
//! directions:
//!
//! * **side A's reading** — `emit.rs`'s descent over the kernel term, producing
//!   a [`crate::emit::CleanOriginPlan`];
//! * **side B's reading** — `trust_types::admissible_body`'s descent over the
//!   EMITTED MIR, producing an `AdmissibleBody` / `StructuralRecBody` /
//!   `WfRecBody`.
//!
//! `admit_lowering` step 2 compares those two readings, and only then reflects
//! side B's and puts it to the kernel.
//!
//! The adversarial review of this design named the exact way a table destroys
//! that: give a row an `emit:` field naming what the emitter calls **and** a
//! `side_b:` field naming what the reader must find, and the two "independent"
//! readings become two fields on one line — **one edit**, not two authorships.
//! Three things prevent that here, and each is checked by a control in
//! `tests/table_controls.rs`:
//!
//! 1. **There is no `side_b` field.** `trust_types::admissible_body` does not
//!    depend on this crate and cannot name this table. Side B's reading is
//!    authored exactly where it was, reads the MIR exactly as it did, and is
//!    reached through the same two deliberately-separate entry points
//!    (`recognize_admissible_body` for the non-recursive chain,
//!    `recognize_structural_rec` / `recognize_wf_nat_rec` outside it, so the E6
//!    kernel-import direction stays blind to recursive bodies BY CONSTRUCTION).
//! 2. **The callee is ONE authenticated identity, not two spellings.**
//!    [`trust_types::admissible_body::PrimitiveCallee`] is the sole classifier;
//!    the emitter resolves a `DefId` from it and the reader authenticates the
//!    extracted string through it. An emit/read callee disagreement is
//!    unrepresentable rather than discouraged — which is what closes the
//!    "emit says sub, side_b says add" hole without merging the two readings.
//! 3. **`ReflectSpec::ElabSurface` rows never build their own `Expr`.** The
//!    reflector produces the FROZEN `trust_spec_elab` producer's *input* and
//!    calls the producer; the term is read back out of the scratch environment.
//!    Side B still passes through a program written for the opposite direction,
//!    which is frozen-R's whole pedigree.
//!
//! # Fail-closed by TYPE at the emitter, by NAME at the reflector
//!
//! [`MirShape`] is deliberately **not** `#[non_exhaustive]`, for the same
//! reason [`crate::emit::CleanOriginShape`] is not: its consumer is
//! `rustc_mir_transform`'s emitter, and a realization the emitter does not know
//! must be a COMPILE ERROR there, never a `_ =>` fall-through into the wrong
//! body. [`MirShape::callee_selector`] restates that exhaustiveness on the fast
//! lane, so a new variant fails `cargo check -p trust-clean-origin` two seconds
//! into the edit rather than an hour into a bootstrap.
//!
//! At the reflector the dual applies: a term with no row is a NAMED refusal
//! ([`no_selection_row`], ruling v7/D3 — *"no selection row for `<head>` at
//! carrier `<carrier>`"* plus the options), never a silent `None`.
//!
//! # §6f LANDING 2 — the table grew a ROUTE, not a row
//!
//! Landing 2 takes the ranked MISS list landing 1 measured and lands its first
//! entry: the CONSTANT body. What it adds is one [`KernelSelector`] variant —
//! [`KernelSelector::CarrierNumeralBody`] — on the EXISTING `uint.lit` row, so
//! the row set is unchanged at 15 and only [`DEMANDS`] moves.
//!
//! That shape is forced, and the forcing is the landing's finding. A separate
//! `uint.const` row would realize [`MirShape::InlineScalar`], which `uint.lit`
//! already realizes, at the same layer and the same carrier and the same gate —
//! an alias with **no legal separation** under
//! `tests/table_controls.rs::h_c_shared_mir_realizations_are_declared_and_separated`.
//! The honest reading of an inseparable alias is that it was never two rows: an
//! operand numeral and a whole-body numeral are ONE vocabulary item in two
//! POSITIONS, and position is dataflow, which side B owns. `uint.lit` therefore
//! joins `param` as a row with two side-A discovery routes — which is §6f's
//! "an optimization ladder, never again a capability boundary", stated a second
//! time by a second instance rather than by a second paragraph.

//! # §6f LANDING 7 — FOUR rows, and the first realization with no call
//!
//! `&&&`, `|||`, `/` and `%` at `UInt{8,16,32,64}`, realized as a BARE
//! [`MirShape::RawBinOp`] — `_0 = <op>(l, r); return`. They are rows for
//! landing 6's reason applied four times (the realization is new, and no other
//! row has it), and they are NOT [`MirShape::Call`] for a measured reason:
//! `trust_types::RustcTotalPrimitiveMethod::classify` demands the callee be
//! exactly `core::num::<impl u{N}>::wrapping_{add,sub,mul}`, while these four
//! operators live on trait impls outside `core::num`.
//!
//! Two things about these rows are worth reading before adding a fifth:
//!
//! * **ONE side-A selector each.** The arithmetic rows list both `{C}.add` and
//!   `HAdd.hAdd` because side B RENDERS the carrier method; here NEITHER side
//!   produces `UInt{N}.land`, so listing it would be a reader arm for a
//!   spelling nothing emits — the exact defect `control_14`'s spelling grain
//!   exists to catch, and the constants DO exist at this pin, so nothing but
//!   the measurement (`landing7_selection_probes::l7_p1`) would have stopped it.
//! * **The divisor rule is not in the row.** A row selects VOCABULARY, so
//!   `uint.div`/`uint.mod` are stated over the operator. What restricts the
//!   divisor to a strictly positive numeral — because Clean's `{C}.div`/`.mod`
//!   are TOTAL and Rust's `/`/`%` PANIC — lives on side A, in the sealed plan,
//!   and independently in the frozen producer.

use trust_types::admissible_body::{ArithBinOp, PrimitiveCallee, RawBinOpKind, SelectCmp};

/// Which layer of a body a row realizes.
///
/// Load-bearing for the aliasing rule below: two rows may realize the same MIR
/// only if a reader could not confuse them, and different contexts are the
/// commonest reason it could not — a recursion arm's node vocabulary is
/// reachable only under a scheme row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowContext {
    /// The row realizes a WHOLE body: side A's fully-peeled term, side B's
    /// `recognize_admissible_body` reading.
    Body,
    /// The row realizes one NODE inside a recursion scheme's arm.
    RecursionArm,
    /// The row IS a recursion scheme — it frames the arms and carries the
    /// termination demand.
    Scheme,
}

/// The carrier class a row is stated over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CarrierClass {
    /// One unsigned machine width, shared by every signature position.
    MachineUInt,
    /// The unbounded `trust_bignum::Nat` bignum carrier.
    BignumNat,
    /// Any exact carrier — the projection lane, which is carrier-agnostic.
    AnyExact,
}

impl CarrierClass {
    /// How a refusal names this carrier to a reader.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::MachineUInt => "an unsigned machine width",
            Self::BignumNat => "the `Nat` bignum carrier",
            Self::AnyExact => "any exact carrier",
        }
    }
}

/// **SIDE A** — one kernel spelling that selects a row.
///
/// A row may list several: `UInt64.add` and
/// `HAdd.hAdd UInt64 UInt64 UInt64 instHAddUInt64` are ONE row today, and
/// `InductiveProjectionProof` is a second side-A route onto the projection row
/// — the clearest demonstration that a ladder rung was a *discovery* route, not
/// a capability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelSelector {
    /// A de Bruijn bound variable under the peeled binders. Source parameter
    /// `i` is `BVar(arity - 1 - i)`; that inversion is the one-construct
    /// mistranslation this lane can make and the kernel is what catches it.
    BoundVariable,
    /// A recursion proved extensionally equal to a bare projection by a closed,
    /// axiom-free structural-induction proof. A SECOND side-A route onto the
    /// same row.
    InductiveProjectionProof,
    /// `{C}.<suffix>` at the signature's carrier — `UInt64.add`.
    CarrierMethod {
        /// The method suffix (`add`, `sub`, `mul`).
        suffix: &'static str,
    },
    /// `{Class}.{projection} {C} {C} {C} inst{Class}{C} lhs rhs` — the
    /// homogeneous prelude instance only.
    SurfaceClass {
        /// The type class (`HAdd`, `HSub`, `HMul`).
        class: &'static str,
        /// Its projection (`hAdd`, `hSub`, `hMul`).
        projection: &'static str,
    },
    /// `{C}.ofNat n`, or `OfNat.ofNat {C} n (instOfNat{C} n)` with the two
    /// literals equal, in **operand position** inside an arithmetic spine.
    CarrierNumeral,
    /// The SAME two numeral spellings, as the **whole peeled body** —
    /// `def six : UInt64 := 6`, and `def k (a : UInt64) : UInt64 := 6` behind
    /// binders the body ignores (§6f landing 2).
    ///
    /// A second side-A route onto the numeral row, exactly as
    /// [`Self::InductiveProjectionProof`] is a second route onto the projection
    /// row — and for the same reason: it emits the same MIR (an inline scalar at
    /// the carrier's encoded width) and reflects through the same frozen
    /// producer. What differs is only where side A found it.
    ///
    /// **Position, not arity, is the coordinate.** The arity is deliberately NOT
    /// part of this selector: `AdmissibleBody::ConstantUint` erases it
    /// (`fragment_widening_probes::probe_e3`), and a table that pretended to
    /// carry it would be the second place an arity could disagree. What binds
    /// the arity is side B — `admit_lowering`'s `arg_count == arity` check and
    /// the reflection's own lambda count, both read off the EMITTED body —
    /// measured in both wrong directions by
    /// `landing2_selection_probes::l2_p3b_the_arity_erasure_is_caught_in_both_directions`.
    CarrierNumeralBody,
    /// `ite.{1} {C} <prop> <dec> t e` whose proposition is the named
    /// comparison at the prelude instance.
    IteAt(SelectCmp),
    /// **§6f LANDING 6** — `ite.{1} {C} <prop> <dec> t e` whose proposition is
    /// stated at `Bool` rather than at the carrier:
    ///
    /// ```text
    /// Eq.{1} Bool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r)
    ///             Bool.true
    /// ```
    ///
    /// the tree the REAL island elaborator mints for the idiomatic `a == b`
    /// (pinned construct by construct at u8/u16/u32/u64 by
    /// `landing5_selection_probes::l5_p1`).
    ///
    /// **Disjoint from [`Self::IteAt`]`(SelectCmp::Eq)` in the proposition's
    /// FIRST argument**, which is what keeps H-A satisfied without a tiebreak:
    /// `Eq.{1} Bool …` and `Eq.{1} {C} l r` cannot both match one term, and the
    /// two rows realize different MIR precisely because the kernel does not
    /// identify the two `ite`s (`l5_p3`: the island refuses even `rfl` between
    /// them).
    IteAtBoolDecisionEq,
    /// A kernel constant head, exactly.
    ConstantHead(&'static str),
    /// A kernel `Nat` literal.
    NatLiteral,
    /// The recursor's own minor-premise `ih`, or the well-founded functional's
    /// `rec` slot. Never a citation of the defined constant — that spelling is
    /// VACUOUS as a gate (probe s2) and is unrepresentable in the reflector by
    /// type.
    RecursiveOccurrence,
}

impl KernelSelector {
    /// How a refusal names this spelling to a reader.
    #[must_use]
    pub fn label(self) -> String {
        match self {
            Self::BoundVariable => "a bound variable".to_owned(),
            Self::InductiveProjectionProof => "a recursion proved equal to a projection".to_owned(),
            Self::CarrierMethod { suffix } => format!("`{{C}}.{suffix}`"),
            Self::SurfaceClass { class, projection } => format!("`{class}.{projection}`"),
            Self::CarrierNumeral => "a carrier numeral".to_owned(),
            Self::CarrierNumeralBody => "a carrier numeral as the whole body".to_owned(),
            Self::IteAt(cmp) => format!("`ite` at {}", cmp_label(cmp)),
            Self::IteAtBoolDecisionEq => {
                "`ite` at a `Bool`-level `==` decision lifted by `= Bool.true`".to_owned()
            }
            Self::ConstantHead(head) => format!("`{head}`"),
            Self::NatLiteral => "a `Nat` literal".to_owned(),
            Self::RecursiveOccurrence => "the recursive occurrence".to_owned(),
        }
    }
}

/// How a row's callee is chosen. Width is **never** a row field: it comes from
/// the plan's `CarrierSignature`, so there is no second place a width can
/// disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeSelector {
    /// The marker-authenticated core wrapping primitive, at the signature's
    /// single unsigned machine width.
    WrappingAtSignatureWidth(ArithBinOp),
    /// A fixed bignum runtime method.
    Fixed(PrimitiveCallee),
}

impl CalleeSelector {
    /// The ONE authenticated identity this selector denotes at `width`.
    ///
    /// Both directions go through here: the emitter resolves its `DefId` from
    /// the result, and the reader authenticates the extracted string through
    /// [`PrimitiveCallee::classify`]. There is no second spelling to disagree
    /// with.
    #[must_use]
    pub fn at_width(self, width: u32) -> PrimitiveCallee {
        match self {
            Self::WrappingAtSignatureWidth(ArithBinOp::Add) => PrimitiveCallee::WrappingAdd(width),
            Self::WrappingAtSignatureWidth(ArithBinOp::Sub) => PrimitiveCallee::WrappingSub(width),
            Self::WrappingAtSignatureWidth(ArithBinOp::Mul) => PrimitiveCallee::WrappingMul(width),
            Self::Fixed(callee) => callee,
        }
    }
}

/// **THE MIR REALIZATION** — what the emitter must build for a row.
///
/// # Deliberately NOT `#[non_exhaustive]`
///
/// Its consumer is `rustc_mir_transform`'s emitter. A realization the emitter
/// does not know must be a COMPILE ERROR there, not a runtime fall-through:
/// `#[non_exhaustive]` would force a `_ =>` arm, and a `_ =>` arm on the enum
/// that decides what MIR gets emitted is exactly the place a future row would
/// silently acquire the wrong body. Same ruling, same words, as
/// [`crate::emit::CleanOriginShape`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirShape {
    /// The parameter local itself — `_0 = move _{i+1}` as a whole body, or
    /// `Operand::Copy(_{i+1})` in an operand position.
    OperandCopy,
    /// An inline scalar constant at the carrier's encoded width.
    InlineScalar,
    /// One `Call` terminator to the selected callee, writing a bare place.
    Call(CalleeSelector),
    /// `_c = BinOp(<cmp>, l, r)` then a two-target `SwitchInt` diamond joining
    /// at a bookkeeping-only `Return`.
    ComparisonBranch(SelectCmp),
    /// **§6f LANDING 6** — the TWO-STEP diamond: `_d = Eq(l, r)` into a `bool`,
    /// then `_c = Eq(_d, const true)` into a second `bool`, then the same
    /// two-target `SwitchInt` diamond, branching on the LIFTED bool.
    ///
    /// # This is a DIFFERENT realization, and that is the landing
    ///
    /// Landing 5 measured that a `select.beq` row could not exist, because it
    /// would have realized [`Self::ComparisonBranch`]`(Eq)` — the realization
    /// `select.eq` already carries, at the same context, carrier and gate —
    /// an alias with neither escape H-C admits. **What changed is exactly the
    /// realization.** The emitted MIR now transcribes the `Bool` decision and
    /// its `= Bool.true` lift as two comparisons, so the two rows realize
    /// different bytes, the alias is gone, and `select.beq` declares
    /// [`MirAliasing::Unique`] truthfully.
    ///
    /// The extra comparison is a REAL COST and it is recorded as one: no MIR
    /// pass ever runs on a Clean-origin body (`optimized_mir` returns it
    /// directly, before `run_optimization_passes`), so it survives verbatim
    /// into codegen. See §6f landing 6 in
    /// `docs/design/2026-08-04-two-language-compiler-architecture.md`.
    BoolDecisionBranch,
    /// **§6f LANDING 7** — a BARE `Rvalue::BinaryOp` at the result carrier,
    /// as the whole body: `_0 = <op>(l, r); return`, then `Return`.
    ///
    /// # This is the first realization with no call and no branch
    ///
    /// Every other value-producing row either calls a marker-authenticated
    /// `core::num` primitive ([`Self::Call`]) or writes an inline constant
    /// ([`Self::InlineScalar`]). `&`/`|`/`/`/`%` can do neither:
    /// [`trust_types::RustcTotalPrimitiveMethod::classify`] demands the callee
    /// path be exactly `core::num::<impl u{N}>::wrapping_{add,sub,mul}`, and
    /// `u{N}`'s `&`, `|`, `/` and `%` live on the `BitAnd`/`BitOr`/`Div`/`Rem`
    /// trait impls, not in `core::num`. Realizing them as a call would mean
    /// widening the authenticated marker set in `library/core` — a different
    /// change with a different review — so the realization is the raw operator,
    /// which is also what `rustc_mir_build` emits for the same source.
    ///
    /// # NO `Assert`, and that is a decision rather than an omission
    ///
    /// Source-level `/` and `%` acquire a div-by-zero `Assert` during MIR
    /// BUILDING. A Clean-origin body is not built from source: it is
    /// constructed here, and it places a `Div`/`Rem` only on an edge where the
    /// divisor is a STRICTLY POSITIVE NUMERAL that side A read out of the
    /// kernel term. A `BinaryOp(Div)` with a statically nonzero divisor is
    /// well-formed, non-UB MIR, so there is no assertion to emit and
    /// `TemplateTerminator` has no `Assert` variant to add. What holds that
    /// invariant is `recognise_raw_binop_expr`'s divisor rule on side A and
    /// the FROZEN producer's own refusal on side B — two independent programs,
    /// which is the double fault.
    ///
    /// # The second fault is in `trust_spec_elab::elab_term`, and the gate is not a third one
    ///
    /// Named explicitly because the obvious places to look do NOT hold this
    /// line and a reader who checks them concludes the double fault is stale:
    /// `trust_types::admissible_body::recognize_raw_binop` reads
    /// `BinaryOp(Rem, Param, Param)` without complaint, and
    /// `reflect::producer_call_for_raw_binop` renders `"{left} % {right}"`
    /// unconditionally. The refusal lives one step further, in the FROZEN
    /// `elab_term`, whose `Div`/`Rem` arm demands `positive_int_literal` — so
    /// side B for `p0 % p1` is never minted at all.
    ///
    /// The faithfulness GATE is emphatically not a third fault. `UInt{N}.mod`
    /// is *defined* as the round-trip lowering, so side A and side B are
    /// definitionally equal at EVERY divisor, zero included, and
    /// `check_faithful` ADMITS `a % b` at a symbolic `b` today (measured:
    /// `control_15::half_11`). The divergence that matters is Clean(total) vs
    /// MIR(panics), and the MIR never reaches the kernel — so no proposition
    /// over the two reflected terms, conditional or otherwise, can carry it.
    /// Anyone relaxing the divisor rule must replace the guarantee where the
    /// MIR is visible; the kernel will not catch them.
    RawBinOp(RawBinOpKind),
    /// `Call(Nat::is_zero)` then a two-target `SwitchInt` whose FALSE target is
    /// the nonzero arm — the polarity is the contract.
    ZeroTestBranch,
    /// A `Call` whose callee string is the emitted body's own def path.
    SelfCall,
}

impl MirShape {
    /// The callee this realization calls, if any.
    ///
    /// This match is the FAST-LANE restatement of the emitter's exhaustiveness:
    /// a new [`MirShape`] variant fails `cargo check -p trust-clean-origin`
    /// here, two seconds into the edit, rather than an hour into a bootstrap.
    #[must_use]
    pub fn callee_selector(self) -> Option<CalleeSelector> {
        match self {
            Self::OperandCopy
            | Self::InlineScalar
            | Self::ComparisonBranch(_)
            // §6f landing 7: a raw binary operator IS the instruction. There
            // is no callee, which is exactly why the row could not be a
            // `Call`.
            | Self::RawBinOp(_)
            | Self::BoolDecisionBranch => None,
            Self::Call(selector) => Some(selector),
            Self::ZeroTestBranch => Some(CalleeSelector::Fixed(PrimitiveCallee::NatIsZero)),
            // A self-call's callee is the body's own def path, which is not a
            // primitive and has no authenticated identity — the recognizer
            // matches it against `func.def_path` and the kernel re-decides the
            // argument. Deliberately `None` rather than a fabricated identity.
            Self::SelfCall => None,
        }
    }
}

/// The unwind edge a row's emitted call carries.
///
/// Recorded per row, not asserted globally, because the tree's two families
/// genuinely differ and the difference is deliberate: the core wrapping
/// primitives cannot unwind, so their calls carry
/// `UnwindAction::Unreachable`; the bignum ops and the self-call CAN unwind
/// (allocation, stack exhaustion), so they carry `UnwindAction::Continue`
/// (`clean_origin_mir.rs`'s own rationale, verbatim). A single global "every
/// edge is Unreachable" assertion is FALSE of three shipped rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnwindDiscipline {
    /// The realization has no call, hence no unwind edge.
    NoCall,
    /// `UnwindAction::Unreachable` — the callee cannot unwind.
    Unreachable,
    /// `UnwindAction::Continue` — the callee can abort.
    Continue,
}

/// **SIDE B** — how a read-back node becomes a kernel term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReflectSpec {
    /// Through a FROZEN `trust_spec_elab` producer, written years earlier for
    /// the OPPOSITE (Rust→Clean, E6) direction. **The row supplies only the
    /// token.** The reflector builds the producer's INPUT and calls the
    /// producer; the `Expr` is read back out of the scratch environment. A new
    /// Rust descent producing that `Expr` directly would be co-authorship and
    /// would silently retire frozen-R's pedigree — the prohibition in
    /// `gate.rs`'s header.
    ElabSurface(ElabToken),
    /// A direct kernel application. NOT covered by frozen-R's pedigree, so a
    /// row using it must carry its own `docs/TCB.md` line (§6f's TCB rule),
    /// named in [`SelectionRow::tcb_row`].
    KernelConst(&'static str),
    /// A kernel `Nat` literal.
    KernelNatLiteral,
    /// **The SITE supplies the term** — a binder: the recursor's `ih`, the
    /// functional's `rec` slot, or the case-substituted parameter. The row
    /// carries no term at all, deliberately: the de Bruijn layout is
    /// soundness-relevant (it is what the gate compares against side A's own
    /// minor premises) and lives in the closed `Site` enum of
    /// [`crate::reflect`], where a wrong index is unrepresentable, never in
    /// data a row author could get wrong.
    BinderSite,
    /// The row is a scheme frame: its reflection is the scheme's scaffold —
    /// the recursor's minor premises, or the `dite` functional — assembled by
    /// the scheme's own producer out of the arm rows.
    SchemeScaffold,
}

/// The token an [`ReflectSpec::ElabSurface`] row hands the frozen producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElabToken {
    /// `trust_spec_elab::admit_projection_function`.
    Projection,
    /// A surface operator inside an `admit_expr_function` rendering.
    ArithOperator(ArithBinOp),
    /// **§6f LANDING 7** — a RAW-BINOP operator inside an `admit_expr_function`
    /// rendering: `p0 & p1`, `p0 | p1`, `p0 / 3`, `p0 % 3`.
    ///
    /// The SAME frozen producer [`Self::ArithOperator`] and [`Self::Numeral`]
    /// route to, and that is the landing's cheapest finding: `elab_term`
    /// already elaborates `&`/`|` through `Nat.land`/`Nat.lor` and `/`/`%`
    /// through the TOTAL `Nat.div`/`Nat.mod`, both over the `toNat`/`ofNat`
    /// round trip, and has done since long before this lane existed. No new
    /// producer was written, so these rows ride frozen-R's pedigree exactly as
    /// the arithmetic rows do and carry no `docs/TCB.md` row of their own.
    ///
    /// A distinct token rather than a fourth `ArithBinOp`, for the reason
    /// [`RawBinOpKind`]'s own docs give: `ArithBinOp` is `AdmissibleBody`'s
    /// vocabulary and therefore the gate-free E6 import direction's, and every
    /// one of its variants must name a `PrimitiveCallee` these four do not
    /// have.
    RawOperator(RawBinOpKind),
    /// A raw numeral inside an `admit_expr_function` rendering.
    Numeral,
    /// `trust_spec_elab::admit_select_function` /
    /// `admit_select_literal_function`.
    Select(SelectCmp),
    /// **§6f LANDING 6** — `trust_spec_elab::admit_select_beq_function`, the
    /// route landing 5 landed and could not reach. A token of its own rather
    /// than a fourth `SelectCmp`: `==` is not a fourth comparison, it is a
    /// second SPELLING of the equality one, one layer up.
    SelectBeq,
}

/// Which faithfulness judgment a row's body is decided by.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateRouting {
    /// `check_faithful` — whole-term defeq (or the closed inductive proof), at
    /// the carrier.
    WholeTerm,
    /// `check_faithful_equations` — per-defining-equation, abstract-ih (§6e as
    /// amended).
    PerDefiningEquation,
    /// `check_faithful_wf_functional` — the F-layer judgment (§6e MEASUREMENT
    /// NOTE + ESCAPE CLOSED).
    Functional,
    /// The row is a node inside a scheme; the scheme's routing decides it.
    UnderScheme,
}

/// What termination evidence a body containing this row demands.
///
/// **There is no `Default`.** §6f: the kernel-certified-total boundary is NOT
/// erodible, and the commonest way to erode a boundary is to omit a field. A
/// scheme row that forgets its demand fails the table well-formedness control.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TotalityDemand {
    /// None — the row cannot recur.
    None,
    /// The kernel's recursor machinery (iota over `RecursorRule`s + strict
    /// positivity), inherited through the recursive-argument identity.
    KernelRecursor,
    /// The kernel's typing rule at the decrease slot, over an audited-empty
    /// axiom closure.
    KernelAccessibility,
}

/// Whether a row shares its MIR realization with another row.
///
/// Two rows realized identically are the wrong-binary hazard generality opens:
/// the reader cannot tell them apart in the bytes, so if their side-A
/// selectors overlapped or their gates agreed, a term selected as one would be
/// checked as the other. Declaring the aliasing is what makes the control
/// checkable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirAliasing {
    /// No other row realizes this MIR at this context.
    Unique,
    /// Another row realizes the SAME MIR. Legal only when the rows are
    /// separated on SIDE A and routed to DIFFERENT gates — which is exactly
    /// the R1/R2 situation: `recognize_wf_nat_rec` delegates to
    /// `recognize_structural_rec` because the two lanes emit one MIR contract
    /// and two readers of one contract can only drift.
    SideADisambiguated,
}

/// One row of the instruction-selection table.
///
/// Reading order is the pipeline's order: SIDE A selects the row, the row says
/// what MIR realizes it, and SIDE B's *independent* reading of that MIR is
/// reflected back through the row's producer. There is no `side_b` field — see
/// the module docs on the double fault.
#[derive(Debug, Clone, Copy)]
pub struct SelectionRow {
    /// **Stable identity.** Cited by refusals, keyed by the coverage ledger,
    /// named in `docs/TCB.md`. A rename is a retire plus an add, never an edit.
    pub name: &'static str,
    /// Which layer of a body this row realizes.
    pub context: RowContext,
    /// The kernel spellings that select this row. Non-empty.
    pub side_a: &'static [KernelSelector],
    /// The carrier class the row is stated over.
    pub carrier: CarrierClass,
    /// The MIR realization.
    pub mir: MirShape,
    /// The unwind edge the realization's call carries.
    pub unwind: UnwindDiscipline,
    /// How side B's reading of that MIR becomes a kernel term.
    pub reflect: ReflectSpec,
    /// Which faithfulness judgment decides a body containing this row.
    pub gate: GateRouting,
    /// The termination evidence the row demands. No default.
    pub totality: TotalityDemand,
    /// Whether another row realizes the same MIR.
    pub alias: MirAliasing,
    /// The kernel measurements that admitted this row. **Enforced non-empty**
    /// — fast-lane-first is the discipline, and an unmeasured row is a
    /// capability claim with no evidence behind it.
    pub measured_by: &'static [&'static str],
    /// The `docs/TCB.md` row that carries this row's producer, when the
    /// producer cannot ride frozen-R's pedigree. Required for every
    /// non-[`ReflectSpec::ElabSurface`] row (§6f's TCB rule).
    pub tcb_row: Option<&'static str>,
}

/// The closed table. Landing 1 adds NO capability: every row below is a shape
/// the compiler already emitted on 2026-08-22, re-expressed.
pub static ROWS: &[SelectionRow] = &[
    // ── whole-body rows ────────────────────────────────────────────────────
    SelectionRow {
        name: "param",
        context: RowContext::Body,
        // TWO side-A routes onto ONE row. `InductiveProjectionProof` is the
        // `CleanOriginShape::InductiveProjection` rung: it emits the exact same
        // projection MIR and reflects through the exact same producer, and the
        // only thing that differs is how side A discovered it. That is the
        // ladder-not-a-boundary claim, in the smallest possible instance.
        side_a: &[KernelSelector::BoundVariable, KernelSelector::InductiveProjectionProof],
        carrier: CarrierClass::AnyExact,
        mir: MirShape::OperandCopy,
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::Projection),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        // Shares `OperandCopy` with `nat.param`, at a different context.
        alias: MirAliasing::SideADisambiguated,
        measured_by: &["e6-fragment-probe::d01", "e6-fragment-probe::d09"],
        tcb_row: None,
    },
    SelectionRow {
        name: "uint.add",
        context: RowContext::Body,
        side_a: &[
            KernelSelector::CarrierMethod { suffix: "add" },
            KernelSelector::SurfaceClass { class: "HAdd", projection: "hAdd" },
        ],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::Call(CalleeSelector::WrappingAtSignatureWidth(ArithBinOp::Add)),
        unwind: UnwindDiscipline::Unreachable,
        reflect: ReflectSpec::ElabSurface(ElabToken::ArithOperator(ArithBinOp::Add)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["fragment_widening_probes::probe_a", "fragment_widening_probes::probe_f"],
        tcb_row: None,
    },
    SelectionRow {
        name: "uint.sub",
        context: RowContext::Body,
        side_a: &[
            KernelSelector::CarrierMethod { suffix: "sub" },
            KernelSelector::SurfaceClass { class: "HSub", projection: "hSub" },
        ],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::Call(CalleeSelector::WrappingAtSignatureWidth(ArithBinOp::Sub)),
        unwind: UnwindDiscipline::Unreachable,
        reflect: ReflectSpec::ElabSurface(ElabToken::ArithOperator(ArithBinOp::Sub)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["fragment_widening_probes::probe_a5"],
        tcb_row: None,
    },
    SelectionRow {
        name: "uint.mul",
        context: RowContext::Body,
        side_a: &[
            KernelSelector::CarrierMethod { suffix: "mul" },
            KernelSelector::SurfaceClass { class: "HMul", projection: "hMul" },
        ],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::Call(CalleeSelector::WrappingAtSignatureWidth(ArithBinOp::Mul)),
        unwind: UnwindDiscipline::Unreachable,
        reflect: ReflectSpec::ElabSurface(ElabToken::ArithOperator(ArithBinOp::Mul)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["fragment_widening_probes::probe_f"],
        tcb_row: None,
    },
    // §6f LANDING 2 — the numeral row acquired a SECOND SIDE-A ROUTE, and no
    // new row. `CarrierNumeralBody` is the same numeral, in the whole-body
    // position instead of an operand position, and it is realized by the same
    // `InlineScalar` and reflected by the same frozen producer.
    //
    // That it is one row and not two is the H-C invariant working as designed
    // rather than being worked around: two rows realized as `InlineScalar`
    // would be an UNDECLARABLE alias — same layer, same carrier, same gate —
    // and the honest reading of that is that they were never two rows. Side B
    // still tells the two POSITIONS apart with no help from this table:
    // `recognize_admissible_body` reports `Arithmetic { right: Const }` for the
    // operand and `ConstantUint` for the body, off different MIR.
    SelectionRow {
        name: "uint.lit",
        context: RowContext::Body,
        side_a: &[KernelSelector::CarrierNumeral, KernelSelector::CarrierNumeralBody],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::InlineScalar,
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::Numeral),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "fragment_widening_probes::probe_a4",
            "fragment_widening_probes::probe_a6",
            // Landing 2's own measurements, taken BEFORE this route existed:
            // the two producers agree at zero parameters (so the route change
            // is a ROUTING change, which is what probe_e3 diagnosed), the
            // kernel ADMITs both numeral spellings at arity 0, 1 and 2, and the
            // wrong-value, width-skew and ARITY mutants are each refused.
            "landing2_selection_probes::l2_p1_the_two_routes_mint_the_same_nullary_term",
            "landing2_selection_probes::l2_p2_nullary_constant_admits_through_the_row_route",
            "landing2_selection_probes::l2_p2b_nullary_constant_width_skew_is_refused",
            "landing2_selection_probes::l2_p3_constant_behind_ignored_binders_admits",
            "landing2_selection_probes::l2_p3b_the_arity_erasure_is_caught_in_both_directions",
        ],
        tcb_row: None,
    },
    SelectionRow {
        name: "select.lt",
        context: RowContext::Body,
        side_a: &[KernelSelector::IteAt(SelectCmp::Lt)],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::ComparisonBranch(SelectCmp::Lt),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::Select(SelectCmp::Lt)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "fragment_widening_probes::probe_h_select_admits",
            "fragment_widening_probes::probe_i_select_literal_admits",
            // §6f landing 3 — the row did not change; its DATAFLOW reach did.
            // These measure the same row at `<` with a NUMERAL arm, against
            // side A taken from the REAL island elaborator, with four refused
            // mutations; and that the general producer reproduces both frozen
            // select producers' terms exactly where they overlap.
            "landing3_selection_probes::l3_p2_constant_else_arm_admits_and_e6_stays_blind",
            "landing3_selection_probes::l3_p3_the_constant_arm_holds_across_the_operand_vocabulary",
            "landing3_selection_probes::l3_p4_the_general_route_reproduces_the_frozen_routes_exactly",
        ],
        tcb_row: None,
    },
    SelectionRow {
        name: "select.le",
        context: RowContext::Body,
        side_a: &[KernelSelector::IteAt(SelectCmp::Le)],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::ComparisonBranch(SelectCmp::Le),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::Select(SelectCmp::Le)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "fragment_widening_probes::probe_h_select_admits",
            // §6f landing 3: the numeral arm at `<=`, against the REAL
            // elaboration (`lez`), with its own refused mutation.
            "landing3_selection_probes::l3_p3_the_constant_arm_holds_across_the_operand_vocabulary",
        ],
        tcb_row: None,
    },
    SelectionRow {
        name: "select.eq",
        context: RowContext::Body,
        side_a: &[KernelSelector::IteAt(SelectCmp::Eq)],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::ComparisonBranch(SelectCmp::Eq),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::Select(SelectCmp::Eq)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "fragment_widening_probes::probe_i_select_literal_admits",
            // §6f landing 3: the row's side-A proposition (`Eq {C} l r` at
            // `instDecidableEq{C}`) is what the REAL elaborator mints for `a =
            // b` — measured, because `a == b` mints a DIFFERENT tree the row
            // does not read, which is this landing's new MISS.
            "landing3_selection_probes::l3_p7_beq_equality_is_a_second_spelling_the_select_rows_do_not_read",
            // §6f landing 5: the row taken END TO END at all four widths —
            // plan, emitted diamond, side B's reader, the producer and the
            // gate. It is the evidence behind the `==` refusal's first option
            // (*"write `if a = b` instead"*), which v7/D3 requires to be a fix
            // rather than a suggestion.
            "landing5_selection_probes::l5_p2_the_propositional_spelling_still_admits_end_to_end",
        ],
        tcb_row: None,
    },
    // §6f LANDING 6 — the SIXTEENTH row, and the first added since landing 1.
    //
    // Landing 5 measured that this row could not exist: it would have realized
    // `ComparisonBranch(Eq)`, which `select.eq` already realizes at the same
    // context, carrier and gate, and `h_c_shared_mir_realizations_are_declared_
    // and_separated` admits an alias only when the rows are separated BY LAYER
    // or by disjoint side A AND a different gate. Neither escape was available:
    // both rows sit at `Body`/`MachineUInt`/`WholeTerm`.
    //
    // **What changed is the REALIZATION, and nothing else.** The emitted MIR
    // for `==` is now the TWO-STEP diamond `MirShape::BoolDecisionBranch` — the
    // `Bool` decision, its `= Bool.true` lift, then the branch — which no other
    // row realizes. So there is no alias to separate: the declaration is
    // `Unique`, truthfully, and H-C has nothing to say about the pair. The
    // gate, the carrier and the context did NOT have to be moved to make room,
    // which is the difference between a row that fits and a row that was made
    // to fit.
    //
    // The side-A selector is disjoint from `select.eq`'s in the proposition's
    // FIRST argument (`Eq.{1} Bool …` versus `Eq.{1} {C} l r`), so H-A holds
    // without a tiebreak either, and the disjointness is a KERNEL fact rather
    // than a table convention: l5_p3 measured that the island refuses `rfl`
    // between the two `ite`s.
    SelectionRow {
        name: "select.beq",
        context: RowContext::Body,
        side_a: &[KernelSelector::IteAtBoolDecisionEq],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::BoolDecisionBranch,
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::SelectBeq),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            // Landing 5's measurements, taken BEFORE this row existed: side A
            // pinned construct by construct at four widths, and the producer
            // ADMITTING against the REAL elaboration with nine refused
            // mutations.
            "landing5_selection_probes::l5_p1_the_beq_spelling_is_pinned_node_by_node_at_every_width",
            "landing5_selection_probes::l5_p4_the_beq_producer_admits_against_the_real_elaboration",
            "landing5_selection_probes::l5_p5_the_beq_route_differs_from_the_general_route_in_exactly_two_positions",
            // Landing 6's own: the two realizations measured side by side and
            // shown to differ, the end-to-end ADMIT through `admit_lowering`,
            // and the non-interchangeability of the two spellings in BOTH
            // directions.
            "landing6_selection_probes::l6_p1_the_two_spellings_now_realize_different_mir",
            "landing6_selection_probes::l6_p2_the_beq_spelling_admits_end_to_end",
            "landing6_selection_probes::l6_p3_the_two_realizations_are_not_interchangeable",
            "control_13_beq_select_emitter_mutation",
            // §6f LANDING 8 — the row did not change; its OPERAND VOCABULARY
            // and its LIFT CONSTANT did, and both are read back out of the
            // emitted bytes by side B. These measure the widened reach at the
            // kernel and through the whole pipeline, with fourteen refused
            // mutations concentrated on the two places where a mistake is a
            // wrong binary rather than a refusal.
            "landing8_selection_probes::l8_p1_a_computed_equality_operand_carries_no_normal_form_at_any_width",
            "landing8_selection_probes::l8_p2_the_scrutinee_is_a_measured_spelling_and_the_trees_stay_apart",
            "landing8_selection_probes::l8_p3_a_computed_equality_operand_admits_end_to_end",
            "landing8_selection_probes::l8_p4_the_false_polarity_admits_end_to_end",
            "control_15_beq_general_emitter_mutation",
        ],
        tcb_row: None,
    },
    // ── §6f LANDING 7 — the RAW-BINOP rows ─────────────────────────────────
    //
    // Four rows, and the row count moves for the second time since landing 1,
    // for the same reason landing 6's did: what is new is the MIR REALIZATION.
    // `MirShape::RawBinOp(kind)` is a bare `Rvalue::BinaryOp` at the result
    // carrier, which no other row realizes, and the four kinds are distinct
    // values of it — so each row declares `Unique` truthfully and H-C has
    // nothing to say about any pair of them.
    //
    // # SIDE A CARRIES ONE SPELLING, NOT TWO, AND THAT IS MEASURED
    //
    // The arithmetic rows list BOTH `{C}.add` and `HAdd.hAdd` because side B
    // RENDERS the carrier method (`Domain::arithmetic` builds `UInt64.add`
    // literally) while source only ever produces the surface class. Neither
    // half of that is true here: a real island `a &&& b` produces
    // `HAnd.hAnd … instHAndUInt{N}` and NOTHING else (measured at all four
    // widths, `landing7_selection_probes::l7_p1`), and side B renders
    // `UInt{N}.ofNat (Nat.land (UInt{N}.toNat p0) (UInt{N}.toNat p1))` — the
    // round-trip encoding, never `UInt{N}.land`. A `CarrierMethod` selector on
    // these rows would therefore be a reader arm for a spelling NEITHER side
    // produces, which is the precise defect class `control_14`'s spelling
    // grain exists to catch. It is omitted, and `SPELLING_GAP_CEILING` does
    // not move.
    //
    // # THE DIVISOR BOUNDARY LIVES ON SIDE A, NOT IN THE ROW
    //
    // `uint.div`/`uint.mod` are stated over the operator, not over the
    // divisor, because a row selects VOCABULARY. What restricts the divisor to
    // a strictly positive numeral is `recognise_raw_binop_expr` on side A and
    // the FROZEN `trust_spec_elab::elab_term`'s `positive_int_literal` demand
    // on side B — NOT `recognize_raw_binop` and NOT `producer_call_for_raw_binop`,
    // neither of which carries a divisor rule, and NOT the faithfulness gate,
    // which admits `a % b` at a symbolic `b` (`control_15::half_11`). See
    // `MirShape::RawBinOp`'s note on why there is no `Assert`.
    SelectionRow {
        name: "uint.and",
        context: RowContext::Body,
        side_a: &[KernelSelector::SurfaceClass { class: "HAnd", projection: "hAnd" }],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::RawBinOp(RawBinOpKind::BitAnd),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::BitAnd)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p2_the_bitwise_rows_admit_end_to_end",
            "landing7_selection_probes::l7_p4_every_raw_binop_mutation_is_refused",
            "landing7_selection_probes::l7_p5_the_raw_binop_reading_stays_out_of_the_e6_chain",
        ],
        tcb_row: None,
    },
    SelectionRow {
        name: "uint.or",
        context: RowContext::Body,
        side_a: &[KernelSelector::SurfaceClass { class: "HOr", projection: "hOr" }],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::RawBinOp(RawBinOpKind::BitOr),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::BitOr)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p2_the_bitwise_rows_admit_end_to_end",
            "landing7_selection_probes::l7_p4_every_raw_binop_mutation_is_refused",
        ],
        tcb_row: None,
    },
    SelectionRow {
        name: "uint.div",
        context: RowContext::Body,
        side_a: &[KernelSelector::SurfaceClass { class: "HDiv", projection: "hDiv" }],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::RawBinOp(RawBinOpKind::Div),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::Div)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p3_the_division_rows_admit_at_a_positive_literal_divisor",
            "landing7_selection_probes::l7_p4_every_raw_binop_mutation_is_refused",
            "landing7_selection_probes::l7_p6_the_total_declaration_and_the_panicking_body_are_measured_apart",
        ],
        tcb_row: None,
    },
    SelectionRow {
        name: "uint.mod",
        context: RowContext::Body,
        side_a: &[KernelSelector::SurfaceClass { class: "HMod", projection: "hMod" }],
        carrier: CarrierClass::MachineUInt,
        mir: MirShape::RawBinOp(RawBinOpKind::Rem),
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::Rem)),
        gate: GateRouting::WholeTerm,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p3_the_division_rows_admit_at_a_positive_literal_divisor",
            "landing7_selection_probes::l7_p4_every_raw_binop_mutation_is_refused",
            "landing7_selection_probes::l7_p6_the_total_declaration_and_the_panicking_body_are_measured_apart",
        ],
        tcb_row: None,
    },
    // ── scheme rows ────────────────────────────────────────────────────────
    //
    // Both realize the SAME MIR — `recognize_wf_nat_rec` DELEGATES to
    // `recognize_structural_rec` because the two lanes emit one contract and
    // two readers of one contract can only drift. That aliasing is declared,
    // and the control requires what makes it safe: disjoint side-A selectors
    // and DIFFERENT gate routing.
    SelectionRow {
        name: "nat.rec.structural",
        context: RowContext::Scheme,
        side_a: &[KernelSelector::ConstantHead("Nat.rec")],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::ZeroTestBranch,
        unwind: UnwindDiscipline::Continue,
        reflect: ReflectSpec::SchemeScaffold,
        gate: GateRouting::PerDefiningEquation,
        totality: TotalityDemand::KernelRecursor,
        alias: MirAliasing::SideADisambiguated,
        measured_by: &["r1_equation_probes::s3", "r1_equation_probes::s6"],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
    SelectionRow {
        name: "nat.wf.fix",
        context: RowContext::Scheme,
        side_a: &[KernelSelector::ConstantHead("WellFounded.fix")],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::ZeroTestBranch,
        unwind: UnwindDiscipline::Continue,
        reflect: ReflectSpec::SchemeScaffold,
        gate: GateRouting::Functional,
        totality: TotalityDemand::KernelAccessibility,
        alias: MirAliasing::SideADisambiguated,
        // w1/w6 are RAW-KERNEL measurements — true about the kernel, silent
        // about the elaborator, and on their own they let this row ship
        // reading a spelling no source produced. p1/p4 are the real-session
        // half: the canonical fixture PLANS and the frozen side B is
        // identified with the elaborator's own tree. §R3a added the ARITY
        // half: the same row now realizes a fix spine of `5 + N` arguments
        // under `N` binders, with an arrow motive and an `N + 1`-argument
        // recursive slot, and `control_16` is its end-to-end mutation battery.
        measured_by: &[
            "r2_wf_equation_probes::w1",
            "r2_wf_equation_probes::w6",
            "r2_session_probes::p1",
            "r2_session_probes::p4",
            "r7_arity_widening_probes::q1",
            "control_16_wf_arity_emitter_mutation::admits_end_to_end",
        ],
        tcb_row: Some("Clean-origin well-founded reflection (NEW side-B producers, R2)"),
    },
    // ── recursion-arm node rows ────────────────────────────────────────────
    // §R3a (2026-08-26) — this ONE row serves BOTH parameter spellings.
    // `RecBodyExpr::Decreasing` (the measure) and `RecBodyExpr::Param(i)` (a
    // threaded parameter) are the same kind of thing at two different binder
    // indices, and `reflect.rs`'s header rule is that a row may say which
    // CONSTANT a node names and never at which INDEX a binder sits. The index
    // is `reflect::RecCall`'s, computed from the recursion's arity. A second
    // row for `Param` would have put a de Bruijn position into the table,
    // which is exactly the drift `ReflectSpec::BinderSite` exists to prevent.
    SelectionRow {
        name: "nat.param",
        context: RowContext::RecursionArm,
        side_a: &[KernelSelector::BoundVariable],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::OperandCopy,
        unwind: UnwindDiscipline::NoCall,
        reflect: ReflectSpec::BinderSite,
        gate: GateRouting::UnderScheme,
        totality: TotalityDemand::None,
        alias: MirAliasing::SideADisambiguated,
        measured_by: &[
            "r1_equation_probes::s4",
            "r1_equation_probes::e5",
            // The threaded spelling, and the kernel probe that makes its
            // positional identification a decision rather than an assumption.
            "r7_arity_widening_probes::q1",
            "r7_arity_widening_probes::q3",
            "control_16_wf_arity_emitter_mutation::f",
        ],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
    // §R3b, 2026-08-27 — RENAMED from `nat.pred` and widened to GENERAL
    // truncated subtraction. No row was added: `RecBodyExpr::Pred` and
    // `RecBodyExpr::Sub` name the SAME constant, realize the SAME MIR
    // (`Call(Fixed(NatSub))`) and reflect through the SAME `KernelConst`, and
    // differ in exactly one thing — their operands — which is the descent's
    // business and never a row's. That is the `nat.param` situation verbatim
    // (one row, two node spellings), and this file's own aliasing rule says
    // the honest reading of an inseparable alias is that it was never two
    // rows: a second row spelling `Nat.sub`/`HSub.hSub` at this same context
    // and carrier would be selected by table ORDER, which `h_a` forbids.
    // The name moved because `nat.pred` named the special case.
    SelectionRow {
        name: "nat.sub",
        context: RowContext::RecursionArm,
        // BOTH spellings of `-` at `Nat`. The surface one was added
        // 2026-08-22: `n - 1` in a real island source elaborates to
        // `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat n 1`, never to the raw
        // `Nat.sub`, so a row that named only `Nat.sub` described a reading no
        // user program could select. Side B still RENDERS `Nat.sub` (below) —
        // the prelude `instHSubNat` reduces to it, which is what makes one row
        // correct for two spellings.
        side_a: &[
            KernelSelector::ConstantHead("Nat.sub"),
            KernelSelector::ConstantHead("HSub.hSub"),
        ],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::Call(CalleeSelector::Fixed(PrimitiveCallee::NatSub)),
        unwind: UnwindDiscipline::Continue,
        // A DUMB reading: `Nat.sub (Nat.succ k) 1`, never pre-reduced to `k`.
        // Reducing here would decide the recursive-argument identity in Rust
        // instead of at the kernel, which is the authority this producer must
        // not have. The same dumbness is what makes the general node safe:
        // `Nat.sub a (Nat.sub a b)` is rendered, never simplified to `min`.
        reflect: ReflectSpec::KernelConst("Nat.sub"),
        gate: GateRouting::UnderScheme,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            "r1_equation_probes::s6",
            "r1_equation_probes::s4",
            "r2_session_probes::p1",
            // R3b's own kernel ground, measured BEFORE this widening was
            // written: general `a - b ≡ Nat.sub a b`, with the wrong-op,
            // wrong-ORDER, wrong-value and wrong-truncation twins refused.
            "gcd_route_probes::m1",
            "control_17_wf_gcd_emitter_mutation::a",
        ],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
    // §R8, 2026-08-28 — TOTAL `Nat` remainder. This IS a new row (unlike R3b's
    // widening, which reused `nat.sub`): `Rem` names a different kernel
    // constant through a different runtime callee, so folding it into an
    // existing row would be the MIR aliasing this file forbids.
    //
    // ── WHAT THIS ROW DOES NOT CLAIM ──────────────────────────────────────
    //
    // NOT panic-freedom. Rust's `%` panics at a zero divisor and Clean's
    // `Nat.mod` is total, and the faithfulness gate — which compares two CLEAN
    // terms, both total — cannot state the difference. That is `fa788aab89`,
    // and it is why the `uint.mod` row's divisor boundary and
    // `recognise_raw_binop_expr`'s symbolic-divisor refusal STAY EXACTLY WHERE
    // THEY ARE. `r8_nat_mod_probes` q6 re-measures the machine-width
    // divergence live rather than citing it.
    //
    // This row is sound anyway, and NOT because the gate got stronger: on this
    // lane there is no emitted panic path at all. The realization is
    // `Call(Fixed(NatRem))` — `TemplateTerminator` has no `Assert` variant —
    // and `trust_bignum::Nat::rem` returns the DIVIDEND at a zero divisor by
    // construction, which is Lean's `Nat.mod_zero`. The claim that replaces
    // panic-freedom is TOTALITY AGREEMENT of the carrier.
    //
    // ── WHAT CARRIES THAT CLAIM (not a `Faithful` token) ──────────────────
    //
    // The kernel identification `a % b ≡ Nat.mod a b` is DISCRIMINATING (q1
    // refuses the `Nat.div` sibling, the swapped operands, and the sub/add/mul
    // twins) but it is VACUOUS with respect to the zero case: `∀ a, a % 0 = a`
    // by `rfl` is REFUSED, `Nat.mod` being stuck at an open dividend (q2).
    // What carries the zero case instead:
    //   1. `trust-bignum/tests/kernel_differential.rs`'s
    //      `the_division_by_zero_lane_is_measured_not_assumed`, which reduces
    //      `Nat.mod` in the REAL Clean `TypeChecker` at a zero divisor and
    //      asserts `Nat::rem` agrees — made non-vacuous by q2's ground table,
    //      which shows the kernel DOES decide `n % 0 = n` at concrete `n`;
    //   2. the `PrimitiveCallee` authenticated-callee TCB row.
    // Neither is a kernel judgment about the emitted code. `tcb_row` says so.
    //
    // This is NO NEW KIND of trust: `nat.sub` already rests on exactly it
    // (`Nat::sub` is `checked_sub().unwrap_or(ZERO)`, truncating where Rust's
    // `-` would underflow-panic), and that row is what makes the subtractive
    // `gcd` run today.
    //
    // ── THE OBLIGATION THIS ROW ACTUALLY DISCHARGES ───────────────────────
    //
    // The DECREASE. `gcd b (a % b)` descends only because `a % b < b`, which
    // needs `0 < b` — and the textbook `dite` puts exactly that in scope, with
    // `Nat.mod_lt … h` visibly in the elaborated term (q4). A guard on the
    // WRONG value, or one that does not DOMINATE the division, is REFUSED at
    // the elaborator (q5). That is a real obligation with a real undischarged
    // case, and it is what distinguishes this landing from bolting an `if b ==
    // 0` onto a bare `a % b` (where the guard is NOT in side A and the ite
    // scrutinee is stuck at open `b`).
    //
    // ── THE STRICTLY LARGER RELIANCE THIS ROW CREATES ─────────────────────
    //
    // Under R3d the decrease proof is BORROWED from side A via
    // `DECREASE_SLOT_SENTINEL`/`MEASURE_SLOT_SENTINEL`. With `a % b` in the
    // self-call, the emitted binary's TERMINATION therefore depends on
    // `Nat::rem` genuinely satisfying `a % b < b` at runtime — not merely on
    // its VALUE being right. Previously the descent was `Pred` or built from
    // `+`/`*`/`-`, where runtime termination followed from `Nat::sub`. The
    // value half is covered by the kernel-differential test; the BOUND half by
    // `checked_div_rem`'s pinned `r < other` postcondition. Stated here rather
    // than left implicit, because it is a larger reliance than `nat.add` /
    // `nat.mul` carry and must not be inherited silently.
    SelectionRow {
        name: "nat.mod",
        context: RowContext::RecursionArm,
        // BOTH spellings of `%` at `Nat`, for `nat.sub`'s reason and measured
        // the same way (q3): a real island `a % b` elaborates to
        // `@HMod.hMod.{0,0,0} Nat Nat Nat instHModNat a b`, never to the raw
        // `Nat.mod`, so a row naming only the raw head would describe a reading
        // no user program could select. Side B still RENDERS `Nat.mod` — the
        // prelude `instHModNat` reduces to it, which is what makes one row
        // correct for two spellings.
        side_a: &[
            KernelSelector::ConstantHead("Nat.mod"),
            KernelSelector::ConstantHead("HMod.hMod"),
        ],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::Call(CalleeSelector::Fixed(PrimitiveCallee::NatRem)),
        unwind: UnwindDiscipline::Continue,
        // A DUMB reading, `nat.sub`'s discipline verbatim: `Nat.mod a b` is
        // rendered as written and never pre-reduced, never operand-swapped and
        // never simplified when the divisor is a literal. Deciding any of that
        // in Rust would be deciding the recursive-argument identity outside the
        // kernel, which is the authority this producer must not have — and `%`
        // is non-commutative, so a swap is a WRONG term the kernel would catch
        // (q1) only because this reader did not perform it.
        reflect: ReflectSpec::KernelConst("Nat.mod"),
        gate: GateRouting::UnderScheme,
        // No recursion of its own: `Nat::rem` is a leaf call, and the decrease
        // it enables is the WF lane's `KernelAccessibility`, carried by the
        // `nat.wf.fix` row rather than by this one.
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &[
            // R8's own kernel ground, all measured BEFORE this producer was
            // written: the identification and its refuting twins (q1); the
            // zero-divisor lane, ground-decided and open-stuck (q2); the
            // surface instance the elaborator actually mints (q3); the
            // positivity proof in the elaborated term (q4); and the
            // undischarged-guard controls (q5).
            "r8_nat_mod_probes::q1",
            "r8_nat_mod_probes::q2",
            "r8_nat_mod_probes::q3",
            "r8_nat_mod_probes::q4",
            "r8_nat_mod_probes::q5",
            "control_21_wf_modulo_gcd_emitter_mutation::admits_end_to_end",
        ],
        tcb_row: Some(
            "Clean-origin recursive-body reflection (NEW side-B producers, R1) — and, for \
             the ZERO-DIVISOR case only, `trust-bignum` carrier totality, which is NOT \
             kernel-re-checked against the emitted code: see this row's header",
        ),
    },
    SelectionRow {
        name: "nat.self",
        context: RowContext::RecursionArm,
        side_a: &[KernelSelector::RecursiveOccurrence],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::SelfCall,
        unwind: UnwindDiscipline::Continue,
        reflect: ReflectSpec::BinderSite,
        gate: GateRouting::UnderScheme,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["r1_equation_probes::s3", "r2_wf_equation_probes::w7"],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
    SelectionRow {
        name: "nat.lit",
        context: RowContext::RecursionArm,
        side_a: &[KernelSelector::NatLiteral],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::Call(CalleeSelector::Fixed(PrimitiveCallee::NatFromU64)),
        unwind: UnwindDiscipline::Continue,
        reflect: ReflectSpec::KernelNatLiteral,
        gate: GateRouting::UnderScheme,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["r1_equation_probes::s7", "r1_equation_probes::e5"],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
    SelectionRow {
        name: "nat.add",
        context: RowContext::RecursionArm,
        side_a: &[
            KernelSelector::ConstantHead("Nat.add"),
            KernelSelector::SurfaceClass { class: "HAdd", projection: "hAdd" },
        ],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::Call(CalleeSelector::Fixed(PrimitiveCallee::NatAdd)),
        unwind: UnwindDiscipline::Continue,
        reflect: ReflectSpec::KernelConst("Nat.add"),
        gate: GateRouting::UnderScheme,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["r1_equation_probes::s8", "r1_equation_probes::e4"],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
    // §R6, 2026-08-25 — the `*` twin of `nat.add`, and the row that makes
    // FACTORIAL emittable. It adds no MIR shape and no gate route: the emitted
    // body is `nat.add`'s call chain with one authenticated callee changed, and
    // the kernel identification it rests on is the same class of fact
    // (`instHMulNat` ↦ `Nat.mul`) that `instHAddNat` supplies for `+`. Measured
    // BEFORE the producer was written — `r6_nat_mul_probes` q7 admits
    // `a * b = Nat.mul a b := rfl` and REFUSES `a * b = Nat.add a b := rfl`, so
    // the identification is a kernel decision and not a spelling assumption.
    SelectionRow {
        name: "nat.mul",
        context: RowContext::RecursionArm,
        side_a: &[
            KernelSelector::ConstantHead("Nat.mul"),
            KernelSelector::SurfaceClass { class: "HMul", projection: "hMul" },
        ],
        carrier: CarrierClass::BignumNat,
        mir: MirShape::Call(CalleeSelector::Fixed(PrimitiveCallee::NatMul)),
        unwind: UnwindDiscipline::Continue,
        reflect: ReflectSpec::KernelConst("Nat.mul"),
        gate: GateRouting::UnderScheme,
        totality: TotalityDemand::None,
        alias: MirAliasing::Unique,
        measured_by: &["r6_nat_mul_probes::q7", "r6_nat_mul_probes::q9"],
        tcb_row: Some("Clean-origin recursive-body reflection (NEW side-B producers, R1)"),
    },
];

/// Look a row up by its stable name.
#[must_use]
pub fn row(name: &str) -> Option<&'static SelectionRow> {
    ROWS.iter().find(|candidate| candidate.name == name)
}

/// **§6f's claim, made checkable: `CleanOriginShape` is a LADDER LABEL.**
///
/// Every rung of the shipped ladder maps onto a row of this table, and two of
/// them map onto the SAME row — `Projection` and `InductiveProjection` both
/// select `param`, because they emit the same MIR and reflect through the same
/// producer and differ only in how side A discovered them. That is what "an
/// optimization ladder, never again a capability boundary" means operationally.
///
/// The match is exhaustive with no wildcard, so a new ladder variant is a
/// compile error here as well as at the emitter.
#[must_use]
pub fn ladder_row(shape: &crate::emit::CleanOriginShape) -> Option<&'static SelectionRow> {
    use crate::emit::CleanOriginShape;
    let name = match shape {
        CleanOriginShape::Projection { .. } | CleanOriginShape::InductiveProjection { .. } => {
            "param"
        }
        // §6f landing 2: the constant body selects the NUMERAL row, through its
        // second side-A route. Two rungs onto one row for the second time in
        // the table, and for the same reason as `Projection` /
        // `InductiveProjection`: same MIR, same producer, different discovery.
        CleanOriginShape::ConstantUint { .. } => "uint.lit",
        CleanOriginShape::WrappingBinOp { op, .. } => arith_row_name(*op),
        CleanOriginShape::Composed { expr } => arith_row_name(root_operator(expr)),
        // §6f landing 3: the GENERAL select maps onto the SAME row as the two
        // narrower select rungs. Three rungs onto one row now, and the reason
        // is the strongest instance of the ladder-not-a-boundary claim yet:
        // the arms are not a vocabulary item at all. `ite` at `<` is `ite` at
        // `<` whether its arms are parameters or numerals — the head, the
        // realization and the gate are identical, and only the DATAFLOW
        // differs, which side B owns and this table cannot see.
        CleanOriginShape::Select { cmp, .. }
        | CleanOriginShape::SelectLiteral { cmp, .. }
        | CleanOriginShape::SelectOperands { cmp, .. } => select_row_name(*cmp),
        // §6f landing 6: the `==` rung is the FIRST select rung that does NOT
        // map onto `select.{lt,le,eq}`, and the reason is the mirror image of
        // why the other three do. Landing 3's finding was that the arms are
        // dataflow, so `ite` at `<` is one row whatever fills them; landing 6's
        // is that the CONDITION is not dataflow — a different proposition is a
        // different kernel term the gate decides differently, and here it is
        // also a different emitted realization.
        // §6f landing 8: the general `==` rung maps onto the SAME row, and that
        // is this landing's structural finding rather than a shortcut. Landing
        // 6 needed a row because the REALIZATION was new; nothing about the
        // realization moved here — `MirShape::BoolDecisionBranch` is still the
        // two-step diamond and still realized by exactly one row, so
        // `MirAliasing::Unique` stays truthful and H-C has nothing to say. What
        // moved is an operand vocabulary and a lift constant, both of which side
        // B reads out of the emitted bytes; that is landing 3's finding (the
        // table selects VOCABULARY, the readers own DATAFLOW) applied one layer
        // inside the condition.
        CleanOriginShape::SelectBeq { .. } | CleanOriginShape::SelectBeqGeneral { .. } => {
            "select.beq"
        }
        // §6f landing 7: the raw-binop rung, one row per operator. It is a new
        // rung AND four new rows, because the realization is new: a bare
        // `Rvalue::BinaryOp` is not a call, not an inline scalar and not a
        // diamond, so there was nothing for it to map onto.
        CleanOriginShape::RawBinOp { op, .. } => raw_binop_row_name(*op),
        CleanOriginShape::StructuralNatRec { .. } => "nat.rec.structural",
        CleanOriginShape::WellFoundedNatRec { .. } => "nat.wf.fix",
    };
    row(name)
}

fn root_operator(expr: &trust_types::admissible_body::ArithExpr) -> ArithBinOp {
    match expr {
        trust_types::admissible_body::ArithExpr::Bin { op, .. } => *op,
        // A bare-leaf `Composed` is unrepresentable through
        // `recognise_wrapping_expr`, which routes a leaf body to the generic
        // refusal. Reporting `Add` here would be a guess, so report the row
        // name that cannot exist and let the caller's lookup fail closed.
        trust_types::admissible_body::ArithExpr::Operand(_) => ArithBinOp::Add,
    }
}

fn arith_row_name(op: ArithBinOp) -> &'static str {
    match op {
        ArithBinOp::Add => "uint.add",
        ArithBinOp::Sub => "uint.sub",
        ArithBinOp::Mul => "uint.mul",
    }
}

/// **§6f landing 7** — the row a raw-binop operator selects.
///
/// A closed match with no wildcard, exactly as [`arith_row_name`] is: a new
/// [`RawBinOpKind`] without a row is a compile error here rather than a
/// `row()` lookup that silently returns `None` at emission time.
fn raw_binop_row_name(op: RawBinOpKind) -> &'static str {
    match op {
        RawBinOpKind::BitAnd => "uint.and",
        RawBinOpKind::BitOr => "uint.or",
        RawBinOpKind::Div => "uint.div",
        RawBinOpKind::Rem => "uint.mod",
    }
}

fn select_row_name(cmp: SelectCmp) -> &'static str {
    match cmp {
        SelectCmp::Lt => "select.lt",
        SelectCmp::Le => "select.le",
        SelectCmp::Eq => "select.eq",
    }
}

/// The rows selected by an ARITHMETIC operator at a given carrier class, with
/// the operator each denotes.
///
/// This is the table that used to be a literal inside `recognise_arith_tree`
/// (`[("add", Add), ("sub", Sub), ("mul", Mul)]` plus the `HAdd`/`HSub`/`HMul`
/// triple). Lifting it is the smallest concrete instance of the whole landing:
/// the descent stopped carrying its own vocabulary.
#[must_use]
pub fn arith_operator_rows(
    carrier: CarrierClass,
) -> impl Iterator<Item = (&'static SelectionRow, ArithBinOp)> {
    ROWS.iter().filter(move |candidate| candidate.carrier == carrier).filter_map(|candidate| {
        match candidate.reflect {
            ReflectSpec::ElabSurface(ElabToken::ArithOperator(op)) => Some((candidate, op)),
            _ => None,
        }
    })
}

/// **§6f landing 7** — the rows selected by a RAW-BINOP operator at a given
/// carrier class, with the operator each denotes.
///
/// The sibling of [`arith_operator_rows`], and deliberately a SECOND iterator
/// rather than a widening of the first: the two families are read by two
/// descents (`recognise_wrapping_expr` and `recognise_raw_binop_expr`) and
/// realized two ways (a marker-authenticated `Call` and a bare
/// `Rvalue::BinaryOp`). One iterator returning a union would let a raw-binop
/// row be reached by the arithmetic descent, whose emitter arm builds a call
/// chain — the drift `TemplateRefusal::RealizationDisagrees` exists to catch,
/// made unreachable instead by keeping the vocabularies apart.
///
/// Filtering on the REFLECTION token rather than on `MirShape` is the same
/// choice `arith_operator_rows` makes, for the same reason: the token is what
/// the reflector needs, and reading the realization here would make this
/// function's answer depend on the emitter's.
#[must_use]
pub fn raw_binop_rows(
    carrier: CarrierClass,
) -> impl Iterator<Item = (&'static SelectionRow, RawBinOpKind)> {
    ROWS.iter().filter(move |candidate| candidate.carrier == carrier).filter_map(|candidate| {
        match candidate.reflect {
            ReflectSpec::ElabSurface(ElabToken::RawOperator(op)) => Some((candidate, op)),
            _ => None,
        }
    })
}

/// The carrier-method suffix a row is spelled with on side A, if it has one.
#[must_use]
pub fn carrier_method_suffix(row: &SelectionRow) -> Option<&'static str> {
    row.side_a.iter().find_map(|selector| match selector {
        KernelSelector::CarrierMethod { suffix } => Some(*suffix),
        _ => None,
    })
}

/// The surface class/projection a row is spelled with on side A, if it has one.
#[must_use]
pub fn surface_class(row: &SelectionRow) -> Option<(&'static str, &'static str)> {
    row.side_a.iter().find_map(|selector| match selector {
        KernelSelector::SurfaceClass { class, projection } => Some((*class, *projection)),
        _ => None,
    })
}

/// How a comparison is named to a reader.
#[must_use]
pub fn cmp_label(cmp: SelectCmp) -> &'static str {
    match cmp {
        SelectCmp::Lt => "`<`",
        SelectCmp::Le => "`<=`",
        SelectCmp::Eq => "`==`",
    }
}

/// **Ruling v7/D3: a refusal must carry the fix, with options.**
///
/// The canonical text for a term the table has no row for. It names the
/// MISSING ROW by the coordinates a row is keyed on — the kernel head and the
/// carrier — so the next landing's work item is legible from the refusal
/// itself, and lists what the reader can do now.
#[must_use]
pub fn no_selection_row(head: &str, carrier: CarrierClass) -> String {
    let implemented: Vec<&str> = ROWS.iter().map(|row| row.name).collect();
    format!(
        "no selection row for `{head}` at {} — the instruction-selection table \
         (`trust_clean_origin::table`) has {} rows and none of them selects this head at \
         this carrier. This is a measured boundary of the compiler, not a rule about what \
         you may write (ruling v7/D2).\n\
         rows implemented: {}\n\
         options:\n\
         - restate the body over a head the table already carries, and keep the general \
           definition alongside for proof position;\n\
         - cite the declaration from a contract instead of calling it — proof position \
           needs no emitted body and has no shape restriction;\n\
         - write the computation as a Rust `fn` and prove it agrees with the declaration in \
           an `ensures` clause, which is the same guarantee reached from the other side;\n\
         - or add the row: a row needs a kernel measurement first (fast-lane-first), then \
           its MIR realization, then its reflection — see \
           `docs/design/2026-08-04-two-language-compiler-architecture.md` §6f.",
        carrier.label(),
        ROWS.len(),
        implemented.join(", "),
    )
}

/// Whether a selection demand is served by a row today.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DemandStatus {
    /// Served by the named row.
    Covered(&'static str),
    /// Not served. The string is the measured reason, in the user's terms.
    Missing(&'static str),
}

/// One (kernel head, carrier) pair the emittable fragment is DEMANDED at.
///
/// # What makes this ledger honest rather than a knob
///
/// A demand may only be listed if it has a NAMED in-tree measurement
/// ([`SelectionDemand::measured_by`]) — a probe or control that puts this head
/// at this carrier to the kernel or to the planner and records the verdict. So
/// the denominator cannot be shrunk to inflate the ratio (dropping a demand
/// drops a measurement that exists in the tree and is asserted by
/// `tests/table_controls.rs`), and it cannot be padded with speculation.
///
/// # What it does NOT measure
///
/// It is a **table-row** metric, not a gate metric and not an end-to-end
/// metric. It says what fraction of the measured demand surface has a row; it
/// says nothing about whether the emitter builds that row's MIR correctly, and
/// nothing about whether the elaborator ever produces the spelling. Those are
/// two further numbers, and quoting this one as "coverage of the CALL lane"
/// would be exactly the inflated-percentage failure mode `CLAUDE.md` opens by
/// naming.
#[derive(Debug, Clone, Copy)]
pub struct SelectionDemand {
    /// The kernel head or shape, as a user would read it.
    pub head: &'static str,
    /// The carrier class it is demanded at.
    pub carrier: CarrierClass,
    /// Whether a row serves it.
    pub status: DemandStatus,
    /// The in-tree measurement. Enforced non-empty.
    pub measured_by: &'static [&'static str],
}

/// The demand ledger. **A future landing updates this file and the number in
/// `tests/table_controls.rs` together**; §6f wants coverage to be a measured
/// number per landing.
pub static DEMANDS: &[SelectionDemand] = &[
    SelectionDemand {
        head: "a bound variable (parameter projection)",
        carrier: CarrierClass::AnyExact,
        status: DemandStatus::Covered("param"),
        measured_by: &["e6-fragment-probe::d01"],
    },
    SelectionDemand {
        head: "a recursion proved equal to a projection",
        carrier: CarrierClass::AnyExact,
        status: DemandStatus::Covered("param"),
        measured_by: &["recursion_probe"],
    },
    SelectionDemand {
        head: "`{C}.add` / `HAdd.hAdd`",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.add"),
        measured_by: &["fragment_widening_probes::probe_a"],
    },
    SelectionDemand {
        head: "`{C}.sub` / `HSub.hSub`",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.sub"),
        measured_by: &["fragment_widening_probes::probe_a5"],
    },
    SelectionDemand {
        head: "`{C}.mul` / `HMul.hMul`",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.mul"),
        measured_by: &["fragment_widening_probes::probe_f"],
    },
    SelectionDemand {
        head: "`{C}.ofNat` / `OfNat.ofNat` (operand numeral)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.lit"),
        measured_by: &["fragment_widening_probes::probe_a4"],
    },
    // §6f LANDING 2 — FLIPPED from MISS to SERVED. Landing 1 ranked this the
    // cheapest measured absent row and named its diagnosis: probe_e3 located
    // the defect UPSTREAM of definitional equality, in the arity-erasing
    // `ConstantUint -> admit_constant_function` ROUTING. Landing 2's probes
    // measured the repair before the route existed — at zero parameters
    // `admit_expr_function` and `admit_constant_function` mint the SAME kernel
    // term, and the expr producer takes its arity from the EMITTED body — so
    // one route serves the nullary body and the ignored-binder body alike.
    //
    // The arity is NOT part of the demand's coordinate, deliberately: it is one
    // shape (a carrier numeral as the whole peeled body) at one carrier class,
    // and splitting it in two here would pad the denominator with a distinction
    // no row is keyed on.
    SelectionDemand {
        head: "a constant body (`ConstantUint`) — nullary, or behind ignored binders",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.lit"),
        measured_by: &[
            "landing2_selection_probes::l2_p2_nullary_constant_admits_through_the_row_route",
            "landing2_selection_probes::l2_p3_constant_behind_ignored_binders_admits",
            "fragment_widening_probes::probe_e3",
            "e6-fragment-probe::f04",
        ],
    },
    SelectionDemand {
        head: "`ite` at `<`",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.lt"),
        measured_by: &["fragment_widening_probes::probe_h_select_admits"],
    },
    SelectionDemand {
        head: "`ite` at `<=`",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.le"),
        measured_by: &["fragment_widening_probes::probe_h_select_admits"],
    },
    SelectionDemand {
        head: "`ite` at `==`",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.eq"),
        measured_by: &["fragment_widening_probes::probe_i_select_literal_admits"],
    },
    SelectionDemand {
        head: "`Nat.rec` (single-parameter structural recursion)",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.rec.structural"),
        measured_by: &["r1_equation_probes::s3", "recursion_boundary_probes::r3"],
    },
    // THE LEDGER WAS WRONG HERE, and it is worth saying so on the entry that
    // carried the claim rather than only on the row. Until 2026-08-22 this
    // demand read `Covered("nat.wf.fix")` on the strength of w1/w6 ALONE —
    // both raw-kernel measurements — while the lane was unreachable from every
    // source a user could write (`docs/audits/2026-08-22-r2-wf-call-lane-
    // unreachable.md`). A `Covered` backed only by hand-built terms is a
    // coverage claim about the kernel wearing the label of a claim about the
    // compiler. The raw-kernel citations stay, because they are true and they
    // are what pins the gate; the real-session ones are what make the word
    // `Covered` honest, and `control_14_real_session_evidence` now demands at
    // least one of the latter for every row in the table.
    SelectionDemand {
        head: "`WellFounded.fix` (single-parameter, decrease by one)",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.wf.fix"),
        measured_by: &[
            "r2_wf_equation_probes::w1",
            "r2_wf_equation_probes::w6",
            "r2_session_probes::p1",
            "r2_session_probes::p4",
            "control_14_real_session_evidence::every_row_has_a_real_session_witness",
        ],
    },
    SelectionDemand {
        head: "a bound variable inside a recursion arm",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.param"),
        // §R3a widened WHAT this demand covers without adding a row: the
        // measure and every threaded parameter are one head at N binder
        // indices. q1 measures the indices against the elaborator's own
        // lowering, q3 measures that the kernel DECIDES parameter order.
        measured_by: &[
            "r1_equation_probes::s4",
            "r7_arity_widening_probes::q1",
            "r7_arity_widening_probes::q3",
        ],
    },
    SelectionDemand {
        head: "`Nat.sub` / `HSub.hSub` at `Nat` (the predecessor, and general `-`)",
        carrier: CarrierClass::BignumNat,
        // §R3b widened WHAT this demand covers without adding a row — the
        // `nat.param` precedent above, at the subtraction head: the
        // predecessor and a general truncated `-` are one constant at two
        // operand shapes. m1 is the kernel measurement that made the general
        // reading a DECISION (`Nat.sub b a` and `Nat.add a b` both refused),
        // and it was taken before the producer was written.
        status: DemandStatus::Covered("nat.sub"),
        measured_by: &["r1_equation_probes::s6", "r2_session_probes::p1", "gcd_route_probes::m1"],
    },
    SelectionDemand {
        head: "the recursive occurrence",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.self"),
        measured_by: &["r1_equation_probes::s3", "r1_equation_probes::s2"],
    },
    SelectionDemand {
        head: "a `Nat` numeral",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.lit"),
        measured_by: &["r1_equation_probes::s7"],
    },
    SelectionDemand {
        head: "`Nat.add` / `HAdd.hAdd` at `Nat`",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.add"),
        measured_by: &["r1_equation_probes::s8"],
    },
    // §R6 — FLIPPED from MISS to SERVED. It was measured absent by
    // `r2_session_probes` p6(g), whose `mulDown` refusal names `HMul.hMul` as
    // "outside this fragment's vocabulary"; that refusal is now `nat.mul`'s
    // coverage, and the demand keeps its original measurement alongside the new
    // one so the flip is auditable rather than a re-worded row.
    SelectionDemand {
        head: "`Nat.mul` / `HMul.hMul` at `Nat`",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.mul"),
        measured_by: &["r2_session_probes::p6", "r6_nat_mul_probes::q7"],
    },
    // §R8 — the TOTAL remainder at the bignum carrier. Note the CARRIER: the
    // machine-width twin of this demand is the one entry in this ledger whose
    // reason is a SOUNDNESS boundary, and it stays unserved. The two are
    // different demands about the same surface operator, and conflating them is
    // exactly the error §R8 was written to correct.
    SelectionDemand {
        head: "`Nat.mod` / `HMod.hMod` at `Nat` (TOTAL remainder)",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Covered("nat.mod"),
        measured_by: &["r8_nat_mod_probes::q1", "r8_nat_mod_probes::q2"],
    },
    // ── MEASURED AND NOT SERVED. Each of these is a head the tree already
    //    puts to the kernel or to the planner and records as refused. They are
    //    the denominator's honest half, and the `MISS` ranking a future
    //    landing picks its rows from.
    // NEW in §6f landing 2, and MEASURED ABSENT. The bignum whole-body
    // constant looks like the machine one and is blocked one layer earlier, in
    // the layer this landing is forbidden to widen casually.
    SelectionDemand {
        head: "a `Nat` numeral as the WHOLE body (`def five : Nat := 5`)",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Missing(
            "NOT a kernel boundary: side A kernel-checks and `Domain::Nat` mints side B, and \
             the kernel ADMITs the pair (l2_p4). **REASON CORRECTED in §6f landing 8 in one \
             respect and SHARPENED in another.** Corrected: the E6 half is OVERSTATED. \
             Landing 3 established the separate-entry-point mechanism and landings 6, 7 and 8 \
             have each used it, so a `recognize_nat_constant_body` entry point beside the \
             others would widen the CALL direction alone and the gate-free import direction's \
             reach would not move — that is not the blocker. Sharpened: the blocker is a \
             change to the ROW TYPE, which is the only entry on this list of which that is \
             true. A whole-body `Nat` numeral emits as a CALL to the bignum runtime, so its \
             realization is `Call(Fixed(NatFromU64))` — which `nat.lit` ALREADY realizes. \
             `nat.lit` is `RowContext::RecursionArm`, a whole body is `RowContext::Body`, and \
             `SelectionRow.context` holds exactly one value, so the two positions differ by \
             LAYER and landing 2's escape (a second side-A route on the existing row) is \
             unavailable. `h_c_shared_mir_realizations_are_declared_and_separated` pins the \
             aliasing set, and a third pair has no legal separation under it. What would have \
             to change: `RowContext` becomes a SET (or `SelectionRow` grows a second context \
             slot) and H-C's alias rule is restated over (context-set, realization) rather \
             than (context, realization). That is a table-TYPE edit with its own controls, and \
             its first deliverable is the H-C restatement, not the row — so it should be its \
             own landing and not a by-product of anything else",
        ),
        measured_by: &["landing2_selection_probes::l2_p4_nat_nullary_constant_has_no_reader_arm"],
    },
    // §6f LANDING 3 — FLIPPED from MISS to SERVED, and NOT by a new row. The
    // kernel head is unchanged (`ite` at `<` is `ite` at `<` whatever its arms
    // are), so no selector, realization or gate moved; what moved is the ARMS,
    // and an arm is DATAFLOW, which side B owns. The capability is in three
    // places, none of them this table: `trust_spec_elab::
    // admit_select_operands_function` (a NEW route beside the two frozen ones,
    // which are untouched), `trust_types::admissible_body::
    // recognize_select_general` (a SEPARATE entry point, so the gate-free E6
    // import direction's reach does not move), and `recognise_select_ite`'s
    // arm reading on side A.
    //
    // ONE demand, not one per comparison: the arms are independent of the
    // comparison in both the reader and the producer, and splitting it would
    // pad the denominator with a distinction nothing is keyed on. The
    // measurements do cover `<` and `<=`, one arm and both, a parameter and a
    // literal comparison, at arity 1 and 2.
    SelectionDemand {
        head: "a constant `ite` ARM (either arm, or both)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.lt"),
        measured_by: &[
            "landing3_selection_probes::l3_p2_constant_else_arm_admits_and_e6_stays_blind",
            "landing3_selection_probes::l3_p3_the_constant_arm_holds_across_the_operand_vocabulary",
            "landing3_selection_probes::l3_p4_the_general_route_reproduces_the_frozen_routes_exactly",
            "control_10_select_operands_emitter_mutation",
            "e6-fragment-probe::f03",
        ],
    },
    // ── §6f LANDING 8 ──────────────────────────────────────────────────────
    //
    // The single "a COMPUTED `ite` condition" entry that stood here until
    // 2026-08-23 is SPLIT, and the split is the landing rather than
    // bookkeeping: **the demand splits at the COMPARISON OPERATOR, and the two
    // halves have opposite blockers.**
    //
    //   * under `<` / `<=` the recorded reason STANDS and is now measured over
    //     a family rather than one instance — `+`, `/` and `&&&` operands all
    //     resolve through an `instDecidableNatLt` over a `Nat.rec`-headed
    //     normal form of the modular reduction (l8_p6). It stays MISSING, and
    //     it should stay missing PERMANENTLY;
    //   * under `==` there is **no normal form at all** — the computed operand
    //     appears VERBATIM in the proposition and again inside the uniform
    //     `instDecidableEqBool`, because the decision is resolved at `Bool`,
    //     one layer above the carrier (l8_p1, four widths, four operators,
    //     both decision positions). That half is SERVED.
    //
    // Keeping one entry would have averaged a served capability and a
    // permanently-refused one into a number that describes neither — the same
    // accounting landing 7 applied when it split the `/`/`%` entry.
    SelectionDemand {
        head: "a COMPUTED (raw-binop) operand in an `==` decision (`if (a &&& 1) == 0`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.beq"),
        measured_by: &[
            "landing8_selection_probes::l8_p1_a_computed_equality_operand_carries_no_normal_form_at_any_width",
            "landing8_selection_probes::l8_p3_a_computed_equality_operand_admits_end_to_end",
            "landing8_selection_probes::l8_p5_the_general_beq_reading_stays_out_of_the_e6_chain",
            "landing8_selection_probes::l8_p7_the_divisor_rule_holds_inside_a_decision_operand",
            "control_15_beq_general_emitter_mutation",
        ],
    },
    SelectionDemand {
        head: "a COMPUTED `ite` condition at `<` / `<=` (`if a + 1 < b`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "REFUSED ON PRINCIPLE since §6f landing 8, not pending — and the entry it was \
             split out of is the reason the split had to happen. Measured at the REAL \
             elaborator over THREE operand vocabularies (`a + 1 < b`, `a / 2 < b`, \
             `(a &&& 1) < b`, l8_p6), a computed `<` operand elaborates with a clean \
             proposition but resolves its DECIDABILITY through an `instDecidableNatLt` over a \
             `Nat.rec`-headed NORMAL FORM of the modular reduction — over a width-specific \
             modulus literal (`Nat.succ 18446744073709551615`). Defeq is intensional on the \
             stuck `ite`, so serving it means side B reproducing an elaborator's \
             instance-synthesis output TERM FOR TERM, at three operator vocabularies and four \
             widths. That is the most brittle trusted surface this lane could acquire, and it \
             is the only entry in this ledger whose service would make the compiler depend on \
             a NORMALIZER's output. The `==` half — which has no normal form — is served \
             instead, and it is the entry directly above",
        ),
        measured_by: &[
            "control_7_select_literal_emitter_mutation",
            "landing2_selection_probes::l2_p6_computed_ite_condition_has_no_reflection_path",
            "landing3_selection_probes::l3_p5_computed_ite_condition_needs_an_elaborator_normal_form",
            "landing8_selection_probes::l8_p6_the_refused_neighbours_are_kernel_green_and_realization_blocked",
        ],
    },
    SelectionDemand {
        head: "a numeral on the comparison's LEFT (`if 10 < a`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "REASON REPLACED A SECOND TIME, 2026-08-23, and the replacement moves the work \
             back INTO this lane. Landing 3 recorded that the blocker was the ELABORATOR — \
             `if 10 < a then a else b` did not elaborate at all, the bare numeral typed as \
             `Nat`, and the fix lived in `first-party/clean`. At clean pin `bad1fd5f8` it \
             ELABORATES, and the numeral elaborates AT THE CARRIER (`UInt64.ofNat 10` inside \
             the same `LT.lt … instLTUInt64` proposition the served rows already read on the \
             right) — measured by the flipped l3_p6, which was RED on `main` before §6f \
             landing 7 and is collateral of that pin bump rather than of any landing that \
             asked for it. The cost is now a one-operand widening in THREE signatures, not \
             an elaborator commit: `CleanOriginShape::SelectOperands`'s `cmp_left: usize`, \
             `GeneralSelectBody`'s `cmp_left: usize`, and \
             `admit_select_operands_function`'s `cmp_left: usize`. That is a landing with \
             its own mutation controls — a numeral on the WRONG side of a `<` is the \
             complementary function — and §6f landing 7 deliberately did not fold it in",
        ),
        measured_by: &[
            "control_7_select_literal_emitter_mutation",
            "fragment_widening_probes::probe_i2_select_literal_on_the_left_refuses_today",
            "landing3_selection_probes::l3_p6_a_numeral_on_the_left_now_elaborates_and_still_does_not_plan",
        ],
    },
    // NEW in §6f landing 3, and MEASURED ABSENT. The `select.eq` row is stated
    // over `Eq {C} l r`, which IS what the real elaborator mints for the
    // PROPOSITIONAL `a = b` — so the row is reachable, and this demand is not
    // a regression of it. What is absent is the OTHER equality spelling: `a ==
    // b` elaborates to `Eq Bool (BEq.beq {C} (instBEqOfDecidableEq …) a b)
    // Bool.true`, a Bool-level decision lifted back to a proposition, which
    // `recognise_select_ite` does not read. A user writing the more idiomatic
    // `==` gets a refusal where `=` succeeds.
    // §6f LANDING 6 — FLIPPED from MISS to SERVED, and by a ROW, which is the
    // first time since landing 1 that the row set moved at all.
    //
    // Landing 5 measured the demand to the bottom and refused it: the producer
    // was green, the kernel was green, and the blocker sat one layer below both
    // — the two spellings realized the SAME MIR, so side B could not tell them
    // apart while the kernel could. Landing 5 named the fix direction the
    // discipline takes (the EMITTER moves to meet the reader) and named its one
    // cost: a `bool` CONSTANT operand, which landing 4 had deliberately made a
    // compile error in `rustc_mir_transform`'s wildcard-free match.
    //
    // That is what this landing paid. `materialize::TemplateOperand::BoolScalar`
    // exists, the emitted `==` body is the TWO-STEP diamond (`_d = Eq(a, b);
    // _c = Eq(_d, const true); switchInt(_c)`), and side B reads it back
    // through a SEPARATE entry point (`recognize_select_beq`) so the gate-free
    // E6 import direction's reach did not move.
    //
    // The cheap alternative landing 5 recorded — letting side A choose which
    // side-B spelling the gate is compared against — stays REFUSED, and nothing
    // in this landing needs it: the two readings remain two authorships, and
    // the kernel still decides which `ite` the emitted body denotes.
    SelectionDemand {
        head: "`a == b` (the `BEq.beq … = true` spelling) as an `ite` condition",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.beq"),
        measured_by: &[
            "landing3_selection_probes::l3_p7_beq_equality_is_a_second_spelling_the_select_rows_do_not_read",
            "landing5_selection_probes::l5_p1_the_beq_spelling_is_pinned_node_by_node_at_every_width",
            "landing5_selection_probes::l5_p4_the_beq_producer_admits_against_the_real_elaboration",
            "landing6_selection_probes::l6_p1_the_two_spellings_now_realize_different_mir",
            "landing6_selection_probes::l6_p2_the_beq_spelling_admits_end_to_end",
            "landing6_selection_probes::l6_p3_the_two_realizations_are_not_interchangeable",
            "control_13_beq_select_emitter_mutation",
        ],
    },
    // NEW in §6f landing 5; REASON REPLACED in §6f landing 6; **SPLIT INTO
    // THREE in §6f landing 8**, because "the `!=` demand" was never one thing.
    // The disequality a user can write has FOUR elaborated trees, measured
    // pairwise non-definitionally-equal (l8_p2), and averaging a three-layer
    // widening, a one-layer one and a new comparison into one entry described
    // none of them:
    //
    //   * `a != b`            — `Bool.not` around the DECISION. Still missing.
    //   * `(a == b) = false`  — the negation entirely in the SCRUTINEE. SERVED.
    //   * `a ≠ b`             — the propositional `Ne` at the carrier. Missing,
    //                           and measured for the first time here.
    //
    // The `select.eq` row's propositional `a = b` is the fourth tree and is
    // already served; it is not a disequality, which is why it is not listed
    // beside these.
    SelectionDemand {
        head: "`(a == b) = false` (the explicit `false` SCRUTINEE) as an `ite` condition",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("select.beq"),
        measured_by: &[
            "landing8_selection_probes::l8_p2_the_scrutinee_is_a_measured_spelling_and_the_trees_stay_apart",
            "landing8_selection_probes::l8_p4_the_false_polarity_admits_end_to_end",
            "landing8_selection_probes::l8_p5_the_general_beq_reading_stays_out_of_the_e6_chain",
            "control_15_beq_general_emitter_mutation",
        ],
    },
    SelectionDemand {
        head: "`a != b` (the `Bool.not (BEq.beq …) = true` spelling) as an `ite` condition",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "REASON REPLACED A SECOND TIME in §6f landing 8, and the replacement is again \
             SHORTER. Landing 6 said what remained was the `Bool.not` NODE at three layers; \
             that is still exactly right, and landing 8 changes only the OPTIONS, because \
             there is now an emittable disequality to point at. `(a == b) = false` IS emitted \
             and kernel-gated at every unsigned machine width — so the refusal no longer has \
             to say *\"there is no emittable spelling of DISEQUALITY on this lane at all\"*, \
             which had become false of the program. What it must NOT say is that the two are \
             interchangeable: measured (l8_p2), the island refuses `rfl` between them, so the \
             restatement is the USER's to make and never a rewrite the compiler performs. The \
             three layers with no negation are unchanged: `materialize::TemplateRvalue` is \
             `{Use, Compare, RawBin, SharedRef}` and none of them is unary; both `==` readers \
             read a decision that is `BinOp::Eq` exactly; and the two producers will not mint \
             the negation. The `SwitchInt`-polarity shortcut stays REFUSED for landing 6's \
             reason, which landing 8 re-measures rather than inherits — `control_15`'s half_1 \
             injects it directly",
        ),
        measured_by: &[
            "landing5_selection_probes::l5_p7_the_not_equal_spelling_is_a_third_tree_with_no_comparison_at_all",
            "landing5_selection_probes::l5_p4_the_beq_producer_admits_against_the_real_elaboration",
            "landing6_selection_probes::l6_p5_the_not_equal_spelling_still_refuses_and_the_blocker_moved",
            "landing8_selection_probes::l8_p2_the_scrutinee_is_a_measured_spelling_and_the_trees_stay_apart",
            "landing8_selection_probes::l8_p8_the_beq_refusals_state_what_is_true_of_the_program",
        ],
    },
    // NEW in §6f landing 8, and MEASURED ABSENT: the FOURTH disequality tree,
    // never written down before.
    SelectionDemand {
        head: "`a ≠ b` (the propositional `Ne` at the carrier) as an `ite` condition",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "`a ≠ b` elaborates to `ite {C} (Ne {1} {C} a b) (instDecidableNot (Eq {1} {C} a b) \
             (instDecidableEq{C} a b)) t e` — structurally the `select.eq` shape with `Ne` for \
             `Eq` and one extra instance wrapper, and NOT definitionally equal to any of the \
             other three disequality trees (l8_p2). It is the most idiomatic spelling and the \
             most expensive: `SelectCmp` is `{Lt, Le, Eq}` and adding `Ne` there is forbidden \
             by landing 5's own argument, because it forces an arm into the two FROZEN select \
             producers' exhaustive `match cmp`. Serving it needs a new \
             `MirShape::ComparisonBranch`-family realization (nothing realizes `Ne` today, so \
             there is no alias) plus its own route and its own polarity controls. Ranked below \
             `(a == b) = false`, which is why that one was served first",
        ),
        measured_by: &[
            "landing8_selection_probes::l8_p2_the_scrutinee_is_a_measured_spelling_and_the_trees_stay_apart",
        ],
    },
    // ── §6f LANDING 7 ──────────────────────────────────────────────────────
    //
    // The single `{C}.div` / `{C}.mod` entry that stood here until 2026-08-23
    // is SPLIT, and the split is the honest bookkeeping rather than a
    // convenience. Its reason had two halves and they have gone opposite ways:
    //
    //   * *"the elaborator refuses the surface instance (`instHModUInt64` is an
    //     `UnknownConst`)"* — **STALE**, and it was the ratchet
    //     `fragment_widening_probes::probe_i_rem_island_spelling_cannot_be_
    //     stated_at_the_kernel` was written to catch. The clean pin
    //     `bad1fd5f8` added `UInt{N}.div`/`.mod`/`.land`/`.lor` and their `H*`
    //     instances as CHECKED definitions, the probe fired, and it is flipped
    //     in this landing's commit exactly as its own text demanded.
    //   * *"a variable divisor carries a side condition no row can discharge on
    //     its own"* — **STANDS**, re-measured, and now its own entry below.
    //
    // Keeping one entry would have averaged a served capability and an
    // unserved one into a number that describes neither.
    SelectionDemand {
        head: "`HDiv.hDiv` at a strictly positive NUMERAL divisor (`a / 3`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.div"),
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p3_the_division_rows_admit_at_a_positive_literal_divisor",
            "landing7_selection_probes::l7_p4_every_raw_binop_mutation_is_refused",
            "fragment_widening_probes::probe_i_rem_island_spelling_is_statable_since_clean_bad1fd5f8",
        ],
    },
    SelectionDemand {
        head: "`HMod.hMod` at a strictly positive NUMERAL divisor (`a % 3`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.mod"),
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p3_the_division_rows_admit_at_a_positive_literal_divisor",
            "fragment_widening_probes::probe_i2_rem_literal_divisor_round_trip_admits",
        ],
    },
    SelectionDemand {
        head: "`HAnd.hAnd` (`a &&& b`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.and"),
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p2_the_bitwise_rows_admit_end_to_end",
            "landing7_selection_probes::l7_p4_every_raw_binop_mutation_is_refused",
        ],
    },
    SelectionDemand {
        head: "`HOr.hOr` (`a ||| b`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Covered("uint.or"),
        measured_by: &[
            "landing7_selection_probes::l7_p1_the_four_operators_are_pinned_node_by_node_at_every_width",
            "landing7_selection_probes::l7_p2_the_bitwise_rows_admit_end_to_end",
        ],
    },
    // THE ONE THAT MUST STAY UNSERVED, and the reason is a SOUNDNESS
    // boundary rather than a capability one — the only entry in this ledger of
    // which that is true.
    SelectionDemand {
        head: "`HDiv.hDiv` / `HMod.hMod` at a VARIABLE or ZERO divisor (`a / b`, `a / 0`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "REFUSED ON PRINCIPLE, not pending. Clean's `UInt{N}.div`/`.mod` are TOTAL and \
             Rust's `/`/`%` PANIC at a zero divisor, so the naive emission computes a \
             DIFFERENT function from the declaration on exactly the input a value-level test \
             does not reach. Measured at the kernel (l7_p6): `x / 0` reduces to `0` and \
             `x % 0` to `x` at an OPEN `x`, because `Nat.div`/`Nat.mod` recurse on the \
             DIVISOR — so `def f (a : UInt64) : UInt64 := a / 0` denotes the constant-zero \
             function and an emitted `Div(a, const 0)` is a wrong binary, single-fault. The \
             obvious repair — emit `if b == 0 { 0 } else { a / b }` — was measured and does \
             NOT close it: at an open divisor the `ite` scrutinee `BEq.beq b 0` is STUCK, so \
             the guarded term is not definitionally equal to the bare `a / b` side A and \
             `check_faithful` refuses it (l7_p6 again, both directions). Serving this needs \
             EITHER the guard in the DECLARATION — where side A is already the `ite` and the \
             existing `select.beq` row frames it, blocked today on a COMPUTED `ite` arm — OR \
             a total runtime callee authenticated by exact def path, which moves the \
             zero-case into a crate whose correctness is a `docs/TCB.md` row rather than a \
             gate row. Both are owner decisions, not row work. **§R8, 2026-08-28 — the \
             SECOND route was taken, but at the OTHER CARRIER, and this entry is unmoved.** \
             `nat.mod` serves `Nat.mod`/`HMod.hMod` at `BignumNat` through exactly that \
             device: `trust_bignum::Nat::rem` is a total callee authenticated by \
             `PrimitiveCallee`, the realization is a `Call` with no `Assert`, and the \
             zero-case correctness is a `docs/TCB.md` row (carrier totality, evidenced by \
             `trust-bignum`'s kernel-differential test) rather than a gate row — which is \
             what that sentence anticipated. It does NOT transfer here. At a MACHINE width \
             the emitted `%` is an `Rvalue::BinaryOp` carrying rustc's zero-divisor \
             `Assert`, there is no total authenticated callee in play, and `l7_p6`'s \
             measurement is unchanged; `control_21::h` and `r8_nat_mod_probes::q6` pin this \
             refusal still firing. Serving THIS demand would still need one of the two \
             routes above, at `UInt{N}`",
        ),
        measured_by: &[
            "landing7_selection_probes::l7_p6_the_total_declaration_and_the_panicking_body_are_measured_apart",
            "landing7_selection_probes::l7_p8_the_planner_refuses_every_unsafe_divisor",
            "recursion_boundary_probes::probe_r7_no_admit_path_for_recursion_and_rem_needs_literal_divisor",
        ],
    },
    // NEW in §6f landing 7, and MEASURED ABSENT one layer further out than
    // this lane reaches — the same class as landing 3's numeral-on-the-left
    // entry, and recorded for the same reason: a producer for a shape no
    // elaborator emits is capability nothing can reach.
    SelectionDemand {
        head: "`^^^` / `<<<` / `>>>` (xor and the shifts)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "blocked in `first-party/clean`'s PRELUDE, upstream of everything this lane owns, \
             and the refusal is instance synthesis rather than a type error: `a ^^^ b` at \
             `UInt{N}` fails with *\"failed to synthesize instance `HXor UInt{N} UInt{N} \
             UInt{N}`\"*, and the two shifts likewise for `HShiftLeft`/`HShiftRight` \
             (l7_p7, all three, at UInt64). Side B is ALREADY there — the frozen \
             `elab_term` elaborates `^` through `Nat.xor` and both shifts through \
             multiply/divide by a literal power of two — so this is one prelude commit away \
             on the clean side and one row here, in that order",
        ),
        measured_by: &[
            "landing7_selection_probes::l7_p7_xor_and_the_shifts_do_not_elaborate_at_a_uint_carrier",
        ],
    },
    // NEW in §6f landing 7, and MEASURED GREEN AT THE KERNEL, which is what
    // makes it a ranked work item rather than a wish: the blocker is the
    // emitted REALIZATION and nothing above it.
    SelectionDemand {
        head: "a NESTED raw-binop tree (`(a &&& b) ||| a`, `(a + b) &&& a`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "the KERNEL half is already green and measured (l7_p9: `(a &&& b) ||| a`, \
             `(a + b) &&& a` and `a &&& 15` all ADMIT through `check_faithful` against the \
             REAL elaboration, reflected through the frozen producer's parenthesized \
             rendering). What is absent is the emitted realization: the arithmetic family \
             composes as a CALL CHAIN (one `Call` terminator per node, read back by \
             `recognize_call_chain`) and the raw-binop family as a single STATEMENT, so a \
             mixed tree is a block with binop statements interleaved between call \
             terminators — a body neither reader reads, and a fifth skeleton in \
             `materialize`. One row cannot serve it; it is a shape",
        ),
        measured_by: &[
            "landing7_selection_probes::l7_p9_nested_raw_binop_trees_admit_at_the_kernel_and_have_no_realization",
        ],
    },
    // ── NEW in §6f landing 8, all THREE measured GREEN AT THE KERNEL ───────
    //
    // Each is one construct away from a body this lane now emits, each
    // elaborates and kernel-checks, and each is blocked on the emitted
    // REALIZATION and nothing above it. They enter the denominator in the same
    // commit that serves their two siblings, which is what an honest ledger
    // move looks like: a larger served surface at a smaller fraction.
    SelectionDemand {
        head: "a NESTED raw-binop operand in an `==` decision (`((a &&& b) ||| 1) == 0`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "the KERNEL half is green and measured (l8_p6: the tree elaborates, and the \
             frozen producer's round-trip rendering is definitionally equal to it). What is \
             absent is the emitted realization: this lane emits ONE raw-binop statement per \
             decision operand, and a nested tree is a chain of them with an intermediate \
             temporary feeding another statement. That is a deeper reader — side B's \
             `general_beq_diamond` resolves a decision operand against ONE prefix statement, \
             not against a dependency graph of them — and it is landing 7's own nested \
             raw-binop MISS in a second position, so the two should be served together or \
             not at all",
        ),
        measured_by: &[
            "landing8_selection_probes::l8_p6_the_refused_neighbours_are_kernel_green_and_realization_blocked",
        ],
    },
    SelectionDemand {
        head: "a WRAPPING (`+`/`-`/`*`) operand in an `==` decision (`(a + 1) == 0`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "the KERNEL half is green and measured (l8_p6): `if (a + 1) == 0` elaborates with \
             `HAdd.hAdd` VERBATIM in the proposition and in the instance, exactly as the four \
             raw operators do — there is no normal form here either. The blocker is a BLOCK \
             BOUNDARY, and it is the sharpest instance of landing 7's realization split: \
             `+`/`-`/`*` realize a marker-authenticated `Call` TERMINATOR (their callees are \
             `core::num::<impl u{N}>::wrapping_*` and nothing else), while `&`/`|`/`/`/`%` \
             realize a bare statement. A call terminator SPLITS the entry block that the \
             decision and its lift share, so a wrapping operand is a fifth skeleton in \
             `materialize` and a two-block entry for side B to read — not an operand \
             widening. Blocked on the same thing landing 7's mixed-tree entry is",
        ),
        measured_by: &[
            "landing8_selection_probes::l8_p6_the_refused_neighbours_are_kernel_green_and_realization_blocked",
        ],
    },
    SelectionDemand {
        head: "a COMPUTED `ite` ARM (`if a == b then a &&& 1 else b`)",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "the KERNEL half is green and measured (l8_p6: the tree elaborates and the frozen \
             producer's round-trip rendering is definitionally equal to it), and this is the \
             CHEAPEST unserved entry in the ledger — but it is cheap in two different ways and \
             they are not the same landing. (1) Emit the arm's computation IN THE ARM BLOCK: \
             that widens `select_arms_and_join`, which side B SHARES with the one-step diamond \
             and therefore with `recognize_select_general`, so the widening would reach a lane \
             this landing did not measure. (2) HOIST it into the entry block, where the \
             computed-operand statement already goes: one statement, no new skeleton, no \
             shared reader touched — but it evaluates a branch the declaration does not take. \
             That is sound for the operators this lane emits (`&`/`|` cannot fail, and the \
             divisor rule keeps `/`/`%` non-trapping) and it is still a SEMANTIC decision \
             about speculative evaluation, which needs its own controls and its own statement \
             of why the totality argument holds. Refusing it here is a scope decision, not a \
             boundary — and recording WHICH of the two it would be is the part a future \
             planner would otherwise have to rediscover",
        ),
        measured_by: &[
            "landing8_selection_probes::l8_p6_the_refused_neighbours_are_kernel_green_and_realization_blocked",
        ],
    },
    // REASON RE-POINTED in §6f landing 8. The mechanism recorded here is RIGHT
    // and the entry should stay refused; what was wrong is that it described
    // ONE of three source spellings — and the one a user is least likely to
    // write, because it requires typing `Nat.rec` by hand.
    SelectionDemand {
        head: "`Nat.rec` wrapped back to a machine width",
        carrier: CarrierClass::MachineUInt,
        status: DemandStatus::Missing(
            "THREE source spellings, THREE distinct blockers, and until §6f landing 8 this \
             entry recorded only the second — citing a RAW-KERNEL probe over a hand-installed \
             environment, which is the class `control_14` exists for. (a) The NATURAL \
             spelling — define the recursion at `Nat` by equations and wrap it \
             (`UInt64.ofNat (tozero (UInt64.toNat n))`) — elaborates, and this lane refuses it \
             at the GENERIC no-row site, because its head is a named constant. Its blocker is \
             a missing `UInt{N}.ofNat`/`.toNat` CARRIER-CONVERSION row plus a cross-def CALL \
             realization (emitting a call to another Clean-origin def, which no row realizes \
             today) — measured by the bare round trip `UInt64.ofNat (UInt64.toNat n)`, which \
             refuses at the SAME site with no recursion in it at all. (b) The EXPLICIT \
             `Nat.rec` spelling reaches the dedicated arm and gets the e2 refusal, which is \
             the mechanism that must stay: the per-defining-equation gate cannot be STATED at \
             the u64 carrier, because the open equations there are not definitional \
             (`UInt64.toNat (UInt64.ofNat (Nat.succ n))` sticks on `Nat.mod` at an open `n`), \
             so a closed-only gate would not be a faithfulness gate. (c) The equation form \
             declared AT the machine width does not elaborate at all — literal patterns are \
             supported only for `Nat` scrutinees — so it never reaches this crate. Only (a) is \
             actionable, and it is a demand nobody had listed",
        ),
        measured_by: &[
            "r1_equation_probes::e2",
            "landing8_selection_probes::l8_p10_two_miss_reasons_are_re_pointed_at_the_boundary_the_program_meets",
        ],
    },
    // **THE REASON RECORDED HERE WAS STALE, AND THAT IS THE MOST CONSEQUENTIAL
    // THING §6f LANDING 8 MEASURED.** It is rewritten rather than edited,
    // because every clause of the old one has to go.
    //
    // It read: *"Refused in `first-party/clean`'s own elaborator
    // (`RecursionOutsideFragment`) before this lane sees it"*. At the current
    // clean pin the §1 demo shape ELABORATES AND KERNEL-CHECKS, in both the
    // `==`-guard and the `dite` spellings. So the refusal has moved ENTIRELY
    // inside this crate: defence depth fell from two repositories to one, and
    // the ledger did not know. Worse, `measured_by` named
    // `recursion_boundary_probes::gcd`, which is a doc-comment table and not a
    // test function at all — the exact gap `control_14` closes for ROWS and
    // that the MISS side of this ledger has no equivalent for.
    SelectionDemand {
        head: "`WellFounded.fix` over TWO parameters (`gcd`)",
        carrier: CarrierClass::BignumNat,
        // §R8, 2026-08-28 — FLIPPED from MISS to SERVED. The textbook
        // `def gcd (a b : Nat) : Nat := if h : 0 < b then gcd b (a % b) else a`
        // under `termination_by b + a * 0` now PLANS, EMITS and ADMITS end to
        // end (`control_21::admits_end_to_end`), and RUNS
        // (`tests/ui/trust/clean_origin_wf_rec_modulo_gcd.rs`).
        //
        // THE OLD REASON IS KEPT BELOW VERBATIM, because two of its three
        // blockers were retired by other landings and the third was WRONG in a
        // way worth preserving:
        //
        //   (1) the single-parameter shape — retired by R3a (arity) and R3d
        //       (the phase-3 sum-measure lowering), not by this landing;
        //   (2) *"the recursive argument is `a % b` at a VARIABLE divisor, so
        //       `gcd` sits BEHIND the one entry in this ledger whose reason is
        //       a soundness boundary"* — **THIS WAS THE OVER-GENERALISATION.**
        //       That entry is at `CarrierClass::MachineUInt`, where the emitted
        //       `%` is an `Rvalue::BinaryOp` carrying a panicking `Assert` the
        //       gate cannot see. At `BignumNat` the emitted operation is
        //       `Call(Fixed(NatRem))` — no `Assert` variant exists on
        //       `TemplateTerminator` — and `Nat::rem` is total. `gcd` never sat
        //       behind that boundary; it sat behind a vocabulary gap. The
        //       machine-width entry is UNMOVED and still refuses;
        //   (3) *"the decrease witness `Nat.mod_lt …` is a proof term the
        //       F-layer judgment would have to read"* — it does not have to
        //       read it. Under R3d the decrease proof is BORROWED from side A
        //       at the sentinel slot, so `Nat.mod_lt … h` is carried, never
        //       parsed. What the compiler discharges is that the guard makes it
        //       AVAILABLE, and the undischarged cases refuse (`control_21` (f)).
        status: DemandStatus::Covered("nat.mod"),
        // THE SUPERSEDED REASON, preserved verbatim so the flip is auditable:
        //   > REASON REPLACED WHOLESALE in §6f landing 8, because the recorded one was STALE.
        //   > `def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)` with
        //   > `termination_by b` now ELABORATES and KERNEL-CHECKS at the current clean pin
        //   > (l8_p9), so nothing in `first-party/clean` stands between a user and this body
        //   > any more and a planner sent there would be sent to fix an elaborator that works.
        //   > The refusal is now this crate's own fail-closed `WellFounded.fix` backstop, and
        //   > THREE things are behind it: (1) `check_wf_nat_signature` and the whole R2 lane
        //   > are single-parameter by construction, while this spine curries a second parameter
        //   > through the motive (`fun n => Nat -> Nat`) — a DIFFERENT functional shape, not a
        //   > wider one, and `check_faithful_wf_functional` compares the functional; (2) the
        //   > recursive argument is `a % b` at a VARIABLE divisor, so `gcd` sits BEHIND the one
        //   > entry in this ledger whose reason is a soundness boundary — serving `gcd`'s CALL
        //   > lane means serving variable-divisor `%` first; (3) the decrease witness
        //   > `Nat.mod_lt …` is a proof term the F-layer judgment would have to read. It must
        //   > STAY REFUSED, and the work is the largest on this list. Two elaborator boundaries
        //   > DO still hold and neither is the one the old entry named: a machine-width
        //   > `termination_by` measure is refused, and a decrease the cascade cannot discharge
        //   > is refused. **Note for whoever reads `r2_session_probes::probe_p8`:** its
        //   > assertion is green but its stated conclusion no longer follows from its subject —
        //   > `gcdish` is rejected for a DECREASE-CASCADE reason, not an arity one, and the
        //   > two-parameter shape it stood in for now elaborates
        measured_by: &[
            "landing8_selection_probes::l8_p9_two_parameter_well_founded_recursion_now_elaborates_and_is_refused_here",
            "r8_nat_mod_probes::q4",
            "control_21_wf_modulo_gcd_emitter_mutation::admits_end_to_end",
            "control_21_wf_modulo_gcd_emitter_mutation::f_only_a_dominating_guard_on_the_divisor_is_admitted",
        ],
    },
    // REASON CORRECTED in §6f landing 8: the recorded blocker is real but it is
    // not the one `fib` MEETS, and a planner who trusted the entry would build
    // the `Prod` carrier and find `fib` still refusing.
    SelectionDemand {
        head: "a pair-valued recursion (`fib`'s `.cov` equations)",
        carrier: CarrierClass::BignumNat,
        status: DemandStatus::Missing(
            "FOUR pieces, not one, and the entry used to name only the third. `fib` elaborates \
             into TWO constants — `fib` itself at `Nat -> Nat`, and `fib.cov` at \
             `Nat -> Prod Nat Nat` — and they refuse at DIFFERENT boundaries, with different \
             `EmitRefusal` variants (l8_p10). (a) `fib`'s own carrier is GRANTED, so it never \
             reaches the carrier at all: it refuses at the TABLE, on `Prod.fst` at the bignum \
             carrier, and what it needs is a `Prod.fst`/`Prod.snd` PROJECTION row. (b) It also \
             needs a cross-def CALL realization, because `fib` calls `fib.cov` and no row \
             realizes a call to another Clean-origin def. (c) `fib.cov` is where the recorded \
             blocker lives — the `Prod Nat Nat` carrier does not exist in \
             `trust-clean-carrier`. (d) And `fib.cov`'s minor premise is a `Prod.casesOn` over \
             an explicit `Prod.mk`, which the `nat.rec.structural` row's `RecBodyExpr` \
             vocabulary cannot spell. The kernel half really is green (probe e4), so this is \
             honest multi-landing work rather than a trap — but it is a multi-landing arc, and \
             none of the four is a row on its own",
        ),
        measured_by: &[
            "r1_equation_probes::e4",
            "landing8_selection_probes::l8_p10_two_miss_reasons_are_re_pointed_at_the_boundary_the_program_meets",
        ],
    },
];

/// The number of demands a row serves today.
#[must_use]
pub fn covered_demands() -> usize {
    DEMANDS.iter().filter(|demand| matches!(demand.status, DemandStatus::Covered(_))).count()
}

/// **THE COVERAGE NUMBER**, in basis points (so it is exact integer
/// arithmetic and a ratchet can be pinned without float comparison).
///
/// `covered demands * 10_000 / total demands`. See [`SelectionDemand`] for the
/// definition and, more importantly, for what it does NOT measure.
#[must_use]
pub fn coverage_basis_points() -> usize {
    if DEMANDS.is_empty() {
        return 0;
    }
    covered_demands() * 10_000 / DEMANDS.len()
}

/// The MISS histogram: every demand no row serves, with its measured reason.
/// This is what ranks the next landing's rows by MEASUREMENT rather than by
/// guess.
#[must_use]
pub fn missing_demands() -> Vec<&'static SelectionDemand> {
    DEMANDS.iter().filter(|demand| matches!(demand.status, DemandStatus::Missing(_))).collect()
}
