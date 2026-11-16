// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f landing 1 — the controls generality has to pay for, and the coverage
//! number.**
//!
//! The ladder's narrowness prevented most of the wrong-binary hazards below BY
//! CONSTRUCTION: each shape had one rigid MIR pattern, side B's `.or_else`
//! chain was five long, and every arm failed closed on anything unexpected.
//! Expressing the ladder as a TABLE removes that accident, so every hazard it
//! removed gets a named control here, in the landing that opens it — not
//! deferred to the landing that would exploit it.
//!
//! | hazard | what it manufactures | control |
//! |---|---|---|
//! | **H-A** row overlap makes selection order-dependent | reordering the table silently changes the emitted body | [`h_a_side_a_selectors_are_disjoint`] |
//! | **H-B** the emitted callee and the read callee drift apart | the gate certifies a call that was never emitted | [`h_b_the_one_callee_identity_round_trips`] |
//! | **H-C** two rows realized as the SAME MIR | side B reads row X's emission as row Y and the kernel checks the wrong claim | [`h_c_shared_mir_realizations_are_declared_and_separated`] |
//! | **H-D** reflector-pedigree drift | a row silently leaves frozen-R without saying so | [`h_d_every_non_frozen_reflection_names_its_tcb_row`] |
//! | **H-E** an unmeasured row | a capability claim with no kernel evidence behind it | [`h_e_every_row_is_measured`] |
//! | **H-F** the kernel-certified-total boundary eroded by OMISSION | a recursion row with no termination demand | [`h_f_only_scheme_rows_demand_termination`] |
//! | **H-G** an emitted unwind edge nobody declared | a caller-side model change the value-level gate is blind to | [`h_g_the_unwind_discipline_matches_the_realization`] |
//! | **H-H** the ladder label drifting off the table | `CleanOriginShape` becoming a second, disagreeing vocabulary | [`h_h_every_ladder_rung_maps_onto_a_row`] |
//! | **H-I** THE DOUBLE FAULT collapsing into one edit | side A's and side B's readings stop being two authorships | [`h_i_the_side_b_reader_cannot_name_the_table`], [`h_i_the_reflector_never_sees_the_plan`] |
//!
//! Plus [`coverage_is_recomputed_and_pinned`], which is §6f's *"coverage is a
//! measured number per landing"* — with its definition, its denominator's
//! evidence requirement, and an explicit statement of what it does NOT measure.

use std::collections::BTreeSet;

use trust_clean_origin::CleanOriginShape;
use trust_clean_origin::table::{
    AnchoredCarriers, CalleeSelector, CarrierAnchor, CarrierClass, DEMANDS, DemandStatus,
    MirAliasing, MirShape, ROWS, ReflectSpec, RowContext, SelectionRow, TotalityDemand,
    UnwindDiscipline, coverage_basis_points, covered_demands, ladder_row, missing_demands,
    no_selection_row, row, rows_selecting_head, whole_body_refusal,
};
use trust_types::admissible_body::{
    ArithBinOp, ArithExpr, ArithOperand, PrimitiveCallee, RawBinOpKind, RecBodyExpr, SelectCmp,
};

/// **THE COVERAGE NUMBER, PINNED.** A landing that moves the ledger updates
/// `src/table.rs` and this constant in the same commit — §6f's "a measured
/// number per landing", with no silent ratchet in either direction.
///
/// | landing | covered | demanded | coverage |
/// |---|---|---|---|
/// | 1 (2026-08-22) | 16 | 24 | 66.66% = 6666 bp |
/// | 2 (2026-08-22) | 17 | 25 | 68.00% = 6800 bp |
/// | 3 (2026-08-22) | 18 | 26 | 69.23% = 6923 bp |
/// | 4 (2026-08-22) | 18 | 26 | 69.23% = 6923 bp (capability-neutral) |
/// | 5 (2026-08-22) | 18 | 27 | 66.66% = 6666 bp |
/// | **6 (2026-08-22)** | **19** | **27** | **70.37% = 7037 bp** |
///
/// Landing 2 moved BOTH halves, which is what an honest landing looks like: the
/// constant body flipped from MISS to SERVED (`landing2_selection_probes`
/// l2_p1..l2_p3b measured it before the route existed), and a NEWLY MEASURED
/// absence — the `Nat` whole-body numeral, whose blocker is side B's READER and
/// not the kernel (l2_p4) — entered the denominator. Two further candidates
/// were measured and REFUSED rather than landed (the constant `ite` arm and the
/// computed `ite` condition, l2_p5/l2_p6): both are blocked in
/// `trust-spec-elab`'s producer signatures, so their entries gained evidence
/// and kept their MISS.
///
/// Landing 3 moved both halves again. The constant `ite` ARM — landing 2's
/// ranked MISS 2 — flipped to SERVED, through a NEW `trust-spec-elab` route
/// beside the two frozen ones and a SEPARATE `trust-types` reader entry point,
/// with side A taken from the REAL island elaborator throughout
/// (`landing3_selection_probes` l3_p2/l3_p3/l3_p4). A newly measured absence
/// entered the denominator: `a == b` elaborates to a Bool-level `BEq.beq`
/// lifted to a proposition, which the `select.eq` row does not read (l3_p7).
///
/// Landing 4 was capability-neutral by construction — it collapsed nine
/// emitter builders into one materializer with byte identity as its acceptance
/// — so neither half moved and this constant did not have to.
///
/// **Landing 5 moved ONE half, DOWNWARD, and that is what an honest ledger
/// looks like when a landing refuses.** It took the `==` / `BEq.beq` spelling
/// and measured every part of it: side A pinned construct by construct at four
/// widths, a producer that ADMITS against the real elaboration with nine
/// refused mutations, and the kernel's own statement (the island refuses `rfl`
/// between the two `ite`s) that the spellings are not definitionally equal. It
/// still did not flip to SERVED, because the two spellings realize the SAME
/// MIR and side B — which sees only the emitted body — cannot tell them apart;
/// distinguishing them needs a `bool` constant operand, which is a new
/// `materialize::TemplateOperand` primitive and therefore a compile error in
/// `rustc_mir_transform` by landing 4's own design. So `covered` stayed at 18
/// while a NEWLY MEASURED absence — `a != b`, the same tree with `Bool.not`
/// around the decision, which has no `Ne` in the emit lane's comparison
/// vocabulary at all — entered the denominator. 18/27 lands back on landing
/// 1's 6666 bp by arithmetic coincidence; the two numbers describe completely
/// different tables and neither is quotable without this history.
///
/// | 7 (2026-08-23) | 23 | 33 | 69.69% = 6969 bp |
///
/// **Landing 7 served FOUR demands and the number went DOWN, which is the
/// second time this ledger has recorded that and the reason is the same one.**
/// `&&&`, `|||`, `/` and `%` at `UInt{8,16,32,64}` are now emitted — four rows,
/// four demands flipped (`/` and `%` split from one stale entry into two served
/// ones, plus the two bitwise operators). Three NEWLY MEASURED absences entered
/// the denominator in the same commit:
///
/// * `/` and `%` at a VARIABLE or ZERO divisor — refused ON PRINCIPLE, not
///   pending. Clean's `UInt{N}.div`/`.mod` are TOTAL (`x / 0 = 0`, `x % 0 = x`,
///   measured at the kernel) and Rust's `/`/`%` panic, so the naive emission is
///   a wrong binary and the obvious guard `if b == 0 { 0 } else { a / b }` is
///   NOT definitionally equal to the bare `a / b` side A — measured, both
///   directions. This is the only MISS in the ledger whose reason is a
///   soundness boundary rather than a capability one.
/// * `^^^` / `<<<` / `>>>` — blocked in `first-party/clean`'s PRELUDE (no
///   `HXor`/`HShiftLeft`/`HShiftRight` instance at a `UInt{N}` carrier), with
///   side B already able to elaborate all three. (True at landing 7; the clean
///   pin `bf31976f48` lifted it — see the 2026-09-23 paragraph below.)
/// * a NESTED raw-binop tree — measured GREEN at the kernel, blocked on the
///   emitted realization, because the wrapping family composes as a call chain
///   and this family as a single statement.
///
/// 23/33 is a smaller fraction than 19/27 and describes a strictly larger
/// served surface. That is what the denominator's evidence requirement buys:
/// serving a demand and measuring three more absences in the same commit moves
/// the number the "wrong" way, and the alternative — not writing the absences
/// down — would move it the "right" way while measuring less.
///
/// **The row count moved to 20, and by FOUR at once for the first time.** The
/// justification is landing 6's, applied four times: what is new is the MIR
/// REALIZATION. `MirShape::RawBinOp(kind)` is a bare `Rvalue::BinaryOp` at the
/// result carrier, which no other row realizes, and its four kinds are distinct
/// values — so every one of the four declares `Unique` truthfully and H-C has
/// nothing to say about any pair of them. What they did NOT add is a skeleton:
/// `control_11`'s `half_10` still measures SIX, because
/// `_0 = <op>(l, r); return` is the single-assignment skeleton with a different
/// rvalue. A new realization PRIMITIVE, not a new body SHAPE — which is exactly
/// the distinction landing 6 qualified landing 4's claim with.
///
/// **Landing 6 flipped landing 5's refusal, and the DENOMINATOR did not move.**
/// Nothing newly measured entered it: the `!=` entry that landing 5 added is
/// still there and still unserved, with its reason REPLACED rather than
/// restated — half of it (the emitted-MIR blocker `==` shared) has been paid
/// off, and what remains is the `Bool.not` node, absent at three layers. So
/// 18/27 became 19/27 by serving one demand and nothing else, which is the
/// narrowest kind of ledger move there is.
///
/// **The row count moved for the FIRST time since landing 1**, and that is the
/// finding rather than an exception to it. Landings 2 and 3 served their
/// demands as a side-A route and as dataflow, landing 4 was a refactor, landing
/// 5 refused — and each recorded that a row was not the unit. Landing 6 IS a
/// row, because what changed is the one thing a row is keyed on that none of
/// those changed: the MIR REALIZATION. Landing 5 measured that a `select.beq`
/// row would alias `select.eq` under H-C with neither escape available; the
/// two-step `==` diamond is a realization no other row has, so the alias never
/// arises and the row declares `Unique` truthfully. The gate, carrier and
/// context were NOT moved to make room — the difference between a row that
/// fits and a row made to fit.
///
/// **§R6 (2026-08-25) — 20/29 → 21/29, by ONE row and ONE demand.** The
/// denominator moved too, and both moves are the same event: `Nat.mul` /
/// `HMul.hMul` at `Nat` was a MEASURED-ABSENT head (`r2_session_probes` p6(g)
/// refused `n * f (n - 1)` naming `HMul.hMul`), so writing it into the ledger
/// as a demand and serving it with the `nat.mul` row are one landing, not a
/// padded denominator followed by a flip. The row is keyed on a MIR
/// realization no other row has — `Call(Fixed(NatMul))` — so it declares
/// `Unique` truthfully and the H-C alias question never arises. What it buys
/// is FACTORIAL, end to end (`r6_nat_mul_probes` q6/q9,
/// `tests/ui/trust/clean_origin_wf_rec_mul.rs`).
///
/// (§R6's fractions above are MISSTATED and are corrected here rather than
/// deleted, because the number below has to be traceable: `20/29 → 21/29` are
/// ROW counts written into a covered/demanded slot with a denominator from no
/// era of this ledger. The measured move §R6 actually made is **23/33 → 24/34
/// = 6969 → 7058 bp**, which is what `a7cfa20ad2` and `09d6383573` recompute
/// from their own `DEMANDS`. One row and one demand is still the right prose;
/// only the fractions were wrong.)
///
/// # §R7 (2026-08-27) — 24/34 → 26/40 = 7058 → **6500 bp**. NO landing did this
///
/// **The number moved because two ledgers were MERGED, and a one-line constant
/// cannot merge.** Nothing in the crate regressed and nothing new was served
/// here; this entry is arithmetic, and it is recorded because the control fired
/// exactly where it was supposed to and the cause is not visible from either
/// branch alone.
///
/// §6f landing 8 (`b98324a64b`, 2026-08-23) was authored on a branch off
/// `a7cfa20ad2` and was INTERNALLY HONEST: it moved 23/33 = 6969 bp to
/// 25/39 = 6410 bp and pinned 6_410 in this file, in its own commit. On the
/// other line, §R6 (`09d6383573`) moved 23/33 to 24/34 = 7058 bp and pinned
/// 7_058. When the two met at merge `04016464e1`, git took **both** sides of
/// `DEMANDS` — the two insertions are textually disjoint, so they both applied
/// — and **one** side of the constant, main's `7_058`. The ledger composed;
/// the pin did not. `DEMANDS` has read 40 entries / 26 covered ever since, and
/// this control has been red ever since, on `main`, for four days.
///
/// **Demand by demand, that is the whole of the movement** — landing 8's six
/// entries, verified against `git show b98324a64b` as the only additions
/// between `c9d9895d54`'s 34 and today's 40:
///
/// | # | demand landing 8 added | status |
/// |---|---|---|
/// | 1 | a COMPUTED (raw-binop) operand in an `==` decision (`if (a &&& 1) == 0`) | **Covered** (`select.beq`) |
/// | 2 | `(a == b) = false` (the explicit `false` SCRUTINEE) as an `ite` condition | **Covered** (`select.beq`) |
/// | 3 | `a ≠ b` (the propositional `Ne` at the carrier) | Missing |
/// | 4 | a NESTED raw-binop operand in an `==` decision | Missing |
/// | 5 | a WRAPPING (`+`/`-`/`*`) operand in an `==` decision | Missing |
/// | 6 | a COMPUTED `ite` ARM (`if a == b then a &&& 1 else b`) | Missing |
///
/// 24 + 2 = 26, 34 + 6 = 40, and `26 * 10_000 / 40` = **6500** exactly. Two
/// further `DEMANDS` edits in this window are head-TEXT only and move no count:
/// §R3b renamed `Nat.sub _ 1 (the predecessor)` to `Nat.sub / HSub.hSub at Nat
/// (the predecessor, and general -)` with its row `nat.pred` → `nat.sub`, and
/// landing 8 restated `a COMPUTED ite condition` as `… at < / <=`. `ROWS` did
/// not move ACROSS THIS MERGE at all — both branches served their demands from
/// rows that already existed — which is why this entry moves the coverage pin
/// and leaves `PINNED_ROW_COUNT` alone.
///
/// **6500 is a smaller fraction than 7058 over a strictly larger served
/// surface**, for the third time in this ledger and for the third time with the
/// same cause: landing 8 served two demands and measured four absences in the
/// same commit. Re-pinning to 6_410 (landing 8's own number) or back to 7_058
/// would both be wrong — each is one branch's arithmetic over the other
/// branch's table.
///
/// **The lesson this row now carries.** A merged ledger recomputes and a merged
/// pin does not, so the pair must be re-derived after any merge that touches
/// `DEMANDS` — the `assert_eq!` at the bottom of this file is the only thing
/// that reports it, no pre-push lane runs it (`CLAUDE.md`: *"no pre-push lane
/// RUNS a `crates/` test"*), and a constant that is one branch's truth is
/// indistinguishable from a regression until someone does this arithmetic.
/// **§R8, 2026-08-28 — re-derived, not nudged.** The landing moves BOTH sides
/// of the fraction, which is why the arithmetic is written out here rather than
/// left as a diff: it ADDS one demand (`Nat.mod`/`HMod.hMod` at `Nat`, served
/// by the new `nat.mod` row) and FLIPS one from MISS to SERVED (`WellFounded.
/// fix` over two parameters — the textbook `gcd`). So 26/40 becomes 28/41, and
/// `28 * 10_000 / 41 = 6_829` under the ledger's integer division.
///
/// The flipped entry's superseded reason is preserved verbatim beside it in
/// `table.rs`, because one of its three stated blockers was not retired but
/// WRONG: it claimed `gcd` sat behind the variable-divisor soundness boundary,
/// which is a `MachineUInt` entry. That entry is unmoved and still refuses.
///
/// **W6, 2026-09-13 — Rust calls a Clean comparison returned as `Bool`.** Three
/// rows (`comparison.{lt,le,eq}`) flip three demands from absent to SERVED, and
/// ONE newly measured absence enters the denominator in the same commit: a
/// comparison against a NUMERAL operand (`a < 10 : Bool`), whose Nat-reduced
/// Decidable instance is not definitionally equal to the frozen
/// `admit_comparison_function`'s carrier-instance mint (refused fail-closed by
/// the gate, measured). So 29/42 becomes 32/46, and `32 * 10_000 / 46 = 6_956`
/// under the ledger's integer division.
///
/// **W6, 2026-09-13 (second increment) — Rust calls a Clean boolean connective.**
/// Three rows (`bool.{not,and,or}`) flip three demands from absent to SERVED —
/// `not b`, `a && b`, `a || b` over `Bool` parameters, minted by the AUTHORED
/// `admit_bool_value_function` as `Bool.not`/`Bool.and`/`Bool.or` (def-eq to the
/// island's `not`/`and`/`or`). No new absence enters the denominator. So 32/46
/// becomes 35/49, and `35 * 10_000 / 49 = 7_142`.
///
/// **2026-09-23 — `^^^` and `>>>`, two rows at once, and the number went DOWN
/// for the fourth time with the same cause.** The clean pin `bf31976f48` gave
/// the prelude `HXor`/`HShiftLeft`/`HShiftRight` and `landing7_selection_
/// probes::l7_p7`'s tripwire fired. The ONE entry it guarded (`^^^` / `<<<` /
/// `>>>`, Missing) is SPLIT into four, because the three operators went three
/// ways: `^^^` SERVED (`uint.xor`); `>>>` at a numeral amount below the width
/// SERVED (`uint.shr`); `>>>` at a variable or out-of-range amount MISSING — a
/// side-B capability boundary, not a soundness one, since Lean and MIR both
/// reduce the amount modulo the width (l7_p14); and `<<<` MISSING — it
/// elaborates, and swept over every amount the gate admits the frozen
/// producer's `UInt{N}.mul` reading at exactly `k = 1` (the function `uint.mul`
/// already serves as `a * 2`) and refuses every other amount below the width
/// (l7_p7), so no row. So one Missing entry leaves and two
/// Covered plus two Missing arrive: 35/49 becomes 37/52, and
/// `37 * 10_000 / 52 = 7_115` under the ledger's integer division — a smaller
/// fraction over a strictly larger served surface.
const PINNED_COVERAGE_BASIS_POINTS: usize = 7_115;

/// The row set the table ships. Named here so that ADDING a row is a visible
/// edit to a control, never an invisible widening.
///
/// **Landing 2 did not move it, and that is the finding.** Its capability
/// arrived as a second SIDE-A ROUTE on the existing `uint.lit` row rather than
/// as a row, because a separate constant row would realize
/// `MirShape::InlineScalar` — which `uint.lit` already realizes, at the same
/// layer, carrier and gate — and `h_c_shared_mir_realizations_are_declared_and_
/// separated` admits no such alias. The honest reading of an inseparable alias
/// is that it was never two rows.
///
/// **Landing 6 moved it to 16**, and the reason is the exact converse of the
/// paragraph above: `select.beq` realizes `MirShape::BoolDecisionBranch`, which
/// no other row realizes, so there is no alias to be inseparable. Landing 5
/// could not add this row precisely because its realization was
/// `ComparisonBranch(Eq)`; landing 6 changed the realization, and the row
/// followed.
/// §R6 (2026-08-25): 21. The `nat.mul` row — measured first
/// (`r6_nat_mul_probes` q7 put both `*` spellings to the kernel BEFORE the
/// producer existed), then witnessed from real sources (`control_14`'s
/// `wf-rec-mul` and `wf-rec-mul-raw`), then landed.
/// §R8 (2026-08-28): 22. The `nat.mod` row — measured first
/// (`r8_nat_mod_probes` q1–q5 put the identification, the zero-divisor lane,
/// the surface instance, the positivity proof and the UNDISCHARGED-guard
/// controls to the kernel BEFORE the producer existed), then witnessed from a
/// real source (`control_14`'s `wf-rec-modulo-gcd`), then landed. It is a NEW
/// row rather than a widening of an existing one — unlike R3b, which reused
/// `nat.sub` — because `Rem` names a different kernel constant (`Nat.mod`)
/// through a different runtime callee (`Nat::rem`), so sharing would be the
/// MIR aliasing H-C forbids.
/// 2026-09-23: 31. `uint.xor` and `uint.shr` — each a `MirShape::RawBinOp`
/// value no other row realizes, measured first (`landing7_selection_probes`
/// l7_p11..l7_p15 put side A, the frozen side B and the gate to the kernel at
/// every width), then witnessed from real sources (`control_14`'s `bitxor`,
/// `bitxor-u32` and `shr-literal`). There is no `uint.shl`, by measurement
/// (l7_p7).
const PINNED_ROW_COUNT: usize = 31;

// ── well-formedness ────────────────────────────────────────────────────────

#[test]
fn row_names_are_unique_and_the_row_count_is_pinned() {
    let names: BTreeSet<&str> = ROWS.iter().map(|r| r.name).collect();
    assert_eq!(names.len(), ROWS.len(), "two rows share a stable name; a name is an identity");
    assert_eq!(
        ROWS.len(),
        PINNED_ROW_COUNT,
        "the row set moved. Landing 1 is capability-neutral: if this is a real widening it \
         belongs in a landing that measures it first (fast-lane-first), and the coverage \
         ledger moves with it."
    );
    for candidate in ROWS {
        assert!(!candidate.name.is_empty(), "a row without a name cannot be cited by a refusal");
        assert!(
            !candidate.side_a.is_empty(),
            "row `{}` has no side-A spelling, so nothing can ever select it",
            candidate.name
        );
    }
}

/// **H-E.** Fast-lane-first is the discipline: a row exists because a kernel
/// measurement admitted its shape, not because an emitter arm was written.
#[test]
fn h_e_every_row_is_measured() {
    for candidate in ROWS {
        assert!(
            !candidate.measured_by.is_empty(),
            "row `{}` declares no kernel measurement. A row without evidence is a capability \
             claim with nothing behind it.",
            candidate.name
        );
    }
}

// ── H-A: row overlap ───────────────────────────────────────────────────────

/// Two rows may share a side-A spelling only when a descent could not confuse
/// them — a different LAYER of the body, or a different carrier. `HAdd.hAdd`
/// legitimately selects `uint.add` at a machine width and `nat.add` inside a
/// recursion arm at the bignum carrier; nothing may select two rows at one
/// place.
#[test]
fn h_a_side_a_selectors_are_disjoint() {
    for (index, left) in ROWS.iter().enumerate() {
        for right in &ROWS[index + 1..] {
            let shared: Vec<_> =
                left.side_a.iter().filter(|selector| right.side_a.contains(selector)).collect();
            if shared.is_empty() {
                continue;
            }
            assert!(
                left.context != right.context || left.carrier != right.carrier,
                "rows `{}` and `{}` share the side-A spelling(s) {:?} at the SAME layer and \
                 carrier, so which one a term selects depends on the order of the table. \
                 First-match-wins is forbidden: separate them or merge them.",
                left.name,
                right.name,
                shared
            );
        }
    }
}

// ── H-B: the one authenticated callee identity ─────────────────────────────

/// **The amendment that closes the "emit says sub, side_b says add" hole.**
///
/// A row carries ONE callee identity, and both directions derive from it: the
/// emitter resolves a `DefId` from it, the reader authenticates the extracted
/// string through `PrimitiveCallee::classify`. This control executes the round
/// trip, so "one identity" is a checked statement rather than a comment.
#[test]
fn h_b_the_one_callee_identity_round_trips() {
    let mut checked = 0usize;
    for candidate in ROWS {
        let Some(selector) = candidate.mir.callee_selector() else {
            continue;
        };
        let widths: &[u32] = match selector {
            CalleeSelector::WrappingAtSignatureWidth(_) => &[8, 16, 32, 64],
            // The bignum rows are width-free; one probe is the whole domain.
            CalleeSelector::Fixed(_) => &[0],
        };
        for &width in widths {
            let identity = selector.at_width(width);
            assert_eq!(
                PrimitiveCallee::classify(&identity.canonical_path()),
                Some(identity),
                "row `{}`: the callee identity {identity:?} does not authenticate back to \
                 itself, so the emitter and the reader are naming two different things.",
                candidate.name
            );
            checked += 1;
        }
    }
    assert!(checked >= 16, "the round trip must actually have run over the callee rows");
}

/// A near-miss must still be refused by the ONE classifier — the widening that
/// merged `arith_method` and `bignum_callee` into it must not have widened
/// either.
#[test]
fn h_b_the_one_classifier_still_fails_closed() {
    for impostor in [
        "core::num::<impl u64>::wrapping_add",
        "@trust-rustc-total-primitive-method::core::num::<impl i64>::wrapping_add",
        "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_div",
        // §R6, 2026-08-25: `mul` MOVED — it is now the authenticated
        // `PrimitiveCallee::NatMul` (the `nat.mul` row). The near-miss this
        // pair was here to make — a SIBLING in the very same `mod arith`
        // impl block, sharing the whole `<impl …>` prefix — is preserved by
        // moving it one method over to `div`, which is still outside the
        // vocabulary and whose Rust realization PANICS where Clean's is total.
        "trust_bignum::Nat::div",
        "trust_bignum::arith::<impl trust_bignum::Nat>::div",
        "evil_bignum::Nat::mul",
        "trust_bignum::arith::<impl trust_bignum::Nat>::checked_mul",
        "evil_bignum::Nat::add",
        "trust_bignum::Nat::checked_sub",
    ] {
        assert_eq!(
            PrimitiveCallee::classify(impostor),
            None,
            "`{impostor}` must not authenticate: the classifier is the only thing standing \
             between a same-named user function and an emitted call"
        );
    }
}

// ── H-C: THE shape-drift control ───────────────────────────────────────────

/// **The hazard generality opens, and the price paid in this landing.**
///
/// A general emitter can produce MIR that side B reads back as a DIFFERENT row
/// than the one selected. The ladder prevented that by accident — five rigid
/// patterns, one reader arm each. A table does not.
///
/// The invariant is: two rows may realize the same MIR only when the reader
/// could not act on the confusion. That means the aliasing is DECLARED, and
/// the rows are separated either by the layer they sit at or by BOTH a
/// disjoint side A and a different gate. R1 and R2 are the real instance:
/// `recognize_wf_nat_rec` DELEGATES to `recognize_structural_rec` because the
/// two lanes emit one MIR contract, and two readers of one contract can only
/// drift — so the separation is `Nat.rec` vs `WellFounded.fix` on side A, and
/// `check_faithful_equations` vs `check_faithful_wf_functional` at the gate.
#[test]
fn h_c_shared_mir_realizations_are_declared_and_separated() {
    let mut shares_with_someone: BTreeSet<&str> = BTreeSet::new();
    for (index, left) in ROWS.iter().enumerate() {
        for right in &ROWS[index + 1..] {
            if left.mir != right.mir {
                continue;
            }
            shares_with_someone.insert(left.name);
            shares_with_someone.insert(right.name);

            assert_eq!(
                left.alias,
                MirAliasing::SideADisambiguated,
                "row `{}` realizes the same MIR as `{}` but declares its realization unique. \
                 An undeclared alias is the wrong-binary hazard: side B reads bytes, and \
                 these bytes are the same.",
                left.name,
                right.name
            );
            assert_eq!(
                right.alias,
                MirAliasing::SideADisambiguated,
                "row `{}` realizes the same MIR as `{}` but declares its realization unique",
                right.name,
                left.name
            );

            // The separation must be somewhere a reader can act on. Exactly
            // two forms qualify, and both are instantiated in the tree today:
            //
            //  * BY LAYER — a reader that reaches one cannot reach the other.
            //    `param` is a whole body read by `recognize_admissible_body`;
            //    `nat.param` is a node inside an arm, reachable only through
            //    `recognize_structural_rec`, which is deliberately NOT in that
            //    chain. Sharing the `BoundVariable` spelling is fine because no
            //    single descent ever has both rows in scope.
            //
            //  * BY SIDE A **AND** THE GATE — the same layer, but disjoint
            //    kernel spellings and different faithfulness judgments. That is
            //    R1 vs R2: `Nat.rec` vs `WellFounded.fix`, then
            //    `check_faithful_equations` vs `check_faithful_wf_functional`.
            //    Either half alone is insufficient — disjoint spellings with
            //    one gate would check the wrong claim about identical bytes,
            //    and two gates with an overlapping spelling would pick by table
            //    order.
            let side_a_disjoint =
                left.side_a.iter().all(|selector| !right.side_a.contains(selector));
            let separated_by_layer = left.context != right.context;
            let separated_by_side_a_and_gate = side_a_disjoint && left.gate != right.gate;
            assert!(
                separated_by_layer || separated_by_side_a_and_gate,
                "rows `{}` and `{}` realize the SAME MIR and nothing separates them: they sit \
                 at the same layer ({:?}), and they do not have both a disjoint side A and a \
                 different gate ({} / {:?} vs {:?}). Side B reads bytes, and these bytes are \
                 identical — a term selected as one would be checked as the other.",
                left.name,
                right.name,
                left.context,
                if side_a_disjoint { "side A disjoint" } else { "side A OVERLAPS" },
                left.gate,
                right.gate,
            );
        }
    }

    // The converse: a row that declares an alias must actually have one, or
    // the declaration is decoration and the control above is vacuous for it.
    for candidate in ROWS {
        if candidate.alias == MirAliasing::SideADisambiguated {
            assert!(
                shares_with_someone.contains(candidate.name),
                "row `{}` declares `SideADisambiguated` but no other row realizes its MIR. A \
                 stale declaration makes the aliasing control pass for the wrong reason.",
                candidate.name
            );
        }
    }

    // And the aliasing that exists today is exactly the two pairs the tree
    // documents. A THIRD one appearing is a review event, not a refactor.
    assert_eq!(
        shares_with_someone,
        BTreeSet::from(["param", "nat.param", "nat.rec.structural", "nat.wf.fix"]),
        "the set of rows sharing a MIR realization moved. The two documented pairs are the \
         projection-vs-recursion-parameter operand copy and the R1/R2 zero-test contract; a \
         new one needs its own measurement and its own review."
    );
}

// ── H-D: reflector pedigree ────────────────────────────────────────────────

/// The arithmetic, select and projection rows reflect through
/// `trust_spec_elab` producers written years earlier for the OPPOSITE
/// direction — frozen-R's pedigree, and the whole reason side B means
/// something for them. Every OTHER reflection is a Trust-authored producer,
/// and §6f's TCB rule says a new trusted surface gets a `docs/TCB.md` row. This
/// control makes migrating a row off frozen-R impossible to do silently.
#[test]
fn h_d_every_non_frozen_reflection_names_its_tcb_row() {
    for candidate in ROWS {
        match candidate.reflect {
            ReflectSpec::ElabSurface(_) => assert!(
                candidate.tcb_row.is_none(),
                "row `{}` reflects through a FROZEN producer and must ride frozen-R's \
                 pedigree, not claim a row of its own",
                candidate.name
            ),
            ReflectSpec::KernelConst(_)
            | ReflectSpec::KernelNatLiteral
            | ReflectSpec::BinderSite
            | ReflectSpec::SchemeScaffold
            // W5: the Rust-callee application is a Trust-authored producer
            // (`reflect_rust_call`), so it too must name its TCB row.
            | ReflectSpec::RustCalleeConst => assert!(
                candidate.tcb_row.is_some(),
                "row `{}` reflects through a Trust-authored producer, which CANNOT ride the \
                 frozen-R/E6 pedigree, and names no `docs/TCB.md` row. §6f: a new trusted \
                 surface gets a row.",
                candidate.name
            ),
        }
    }
}

// ── H-F: the kernel-certified-total boundary ───────────────────────────────

/// §6f: *"the kernel-certified-total boundary is NOT erodible"*, and the
/// commonest way to erode a boundary is to omit a field. `TotalityDemand` has
/// no `Default`, and this control adds the other half: exactly the scheme rows
/// demand termination evidence, and each one names WHICH kernel machinery
/// supplies it.
#[test]
fn h_f_only_scheme_rows_demand_termination() {
    for candidate in ROWS {
        match candidate.context {
            RowContext::Scheme => assert_ne!(
                candidate.totality,
                TotalityDemand::None,
                "scheme row `{}` demands no termination evidence. A recursion the kernel does \
                 not certify total is not callable, and omitting the field is exactly how \
                 that boundary erodes.",
                candidate.name
            ),
            // W5 (Lean-calls-Rust): the ONE body row whose totality is not
            // the kernel's. It cannot recur, but the binary computes its
            // total Clean term only if every Rust callee RETURNS, and that
            // evidence is the callee's E6 facets, charged outside the kernel.
            // The demand is named rather than defaulted to `None` precisely
            // so this control has to see it.
            RowContext::Body if candidate.mir == MirShape::RustCallChain => assert_eq!(
                candidate.totality,
                TotalityDemand::RustCalleeFacets,
                "row `{}` calls user Rust code; its totality rests on the callee's facets, \
                 and the row must say so",
                candidate.name
            ),
            RowContext::Body | RowContext::RecursionArm => assert_eq!(
                candidate.totality,
                TotalityDemand::None,
                "row `{}` demands termination evidence but cannot recur; the demand belongs \
                 on the scheme that frames it",
                candidate.name
            ),
        }
    }
    // Both schemes are present and route to DIFFERENT kernel machinery — R1's
    // recursor iota, R2's typing rule at the decrease slot over an
    // audited-empty closure. One demand serving both would mean one of the two
    // measurements was never taken.
    let demands: BTreeSet<TotalityDemand> = ROWS
        .iter()
        .filter(|candidate| candidate.context == RowContext::Scheme)
        .map(|candidate| candidate.totality)
        .collect();
    assert_eq!(
        demands,
        BTreeSet::from([TotalityDemand::KernelRecursor, TotalityDemand::KernelAccessibility])
    );
}

// ── H-G: unwind edges ──────────────────────────────────────────────────────

/// A wrong `UnwindAction` adds a cleanup edge that changes the caller-side
/// model without changing a value, so the faithfulness gate is blind to it.
/// The tree's two families genuinely differ — the core wrapping primitives
/// cannot unwind (`Unreachable`), the bignum ops and the self-call CAN abort
/// on allocation or stack exhaustion (`Continue`) — so the expectation is
/// PER ROW, and a single global "every edge is Unreachable" assertion would be
/// false of five shipped rows.
#[test]
fn h_g_the_unwind_discipline_matches_the_realization() {
    for candidate in ROWS {
        let expected = match candidate.mir {
            MirShape::OperandCopy
            | MirShape::InlineScalar
            | MirShape::ComparisonBranch(_)
            // W6 (Rust-calls-Clean): a comparison returned as a `Bool` value is
            // one `Rvalue::BinaryOp` instruction and no call — no unwind edge.
            | MirShape::ComparisonValue(_)
            // W6: a boolean connective/negation is one bare `BinaryOp`/`UnaryOp`
            // and no call — no unwind edge.
            | MirShape::BoolConnValue(_)
            | MirShape::BoolNotValue
            // §6f landing 6: the two-step `==` diamond is two comparisons and a
            // switch — one more instruction than the one-step diamond and still
            // not a call, so still no unwind edge.
            | MirShape::BoolDecisionBranch
            // §6f landing 7: a bare `Rvalue::BinaryOp` is one instruction and
            // no call. `Div`/`Rem` are the first realizations in this table
            // that CAN fault — but a fault is not an unwind edge, and the fault
            // is excluded upstream rather than caught downstream: the planner
            // admits `/`/`%` only at a strictly positive numeral divisor, so
            // the emitted instruction cannot trap and there is no edge to
            // declare. See `MirShape::RawBinOp`'s note on why there is no
            // `Assert` either.
            | MirShape::RawBinOp(_) => UnwindDiscipline::NoCall,
            MirShape::Call(CalleeSelector::WrappingAtSignatureWidth(_)) => {
                UnwindDiscipline::Unreachable
            }
            MirShape::Call(CalleeSelector::Fixed(_))
            | MirShape::ZeroTestBranch
            | MirShape::SelfCall
            // W5 (Lean-calls-Rust): a call into USER code, which may panic
            // and may unwind. `Continue` is the honest edge; the callee's
            // panic-freedom is an ordinary obligation of that `fn`.
            | MirShape::RustCallChain => UnwindDiscipline::Continue,
        };
        assert_eq!(
            candidate.unwind, expected,
            "row `{}` declares the unwind discipline {:?}, which its realization {:?} does not \
             produce",
            candidate.name, candidate.unwind, candidate.mir
        );
        if candidate.unwind == UnwindDiscipline::Continue {
            // `Continue` is a statement about the CALLEE: the bignum runtime
            // can abort on allocation, and (W5) a user `fn` can do anything.
            // No other realization may claim it.
            let callee_can_unwind = candidate.carrier == CarrierClass::BignumNat
                || candidate.mir == MirShape::RustCallChain;
            assert!(
                callee_can_unwind,
                "row `{}` carries an unwind edge but calls neither the bignum runtime nor user \
                 code. `Continue` is a statement about the callee, not a default.",
                candidate.name
            );
        }
    }
}

// ── H-H: the ladder is a LABEL ─────────────────────────────────────────────

/// §6f: `CleanOriginShape` becomes an optimization ladder, never again a
/// capability boundary. Made checkable: every rung maps onto a row, and the two
/// projection rungs map onto the SAME row — which is the claim, in its smallest
/// instance.
#[test]
fn h_h_every_ladder_rung_maps_onto_a_row() {
    let rungs = [
        CleanOriginShape::Projection { projected: 0 },
        CleanOriginShape::InductiveProjection { projected: 0 },
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(1),
        },
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Mul,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
        CleanOriginShape::Composed {
            expr: ArithExpr::Bin {
                op: ArithBinOp::Mul,
                left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                right: Box::new(ArithExpr::Operand(ArithOperand::Param(1))),
            },
        },
        CleanOriginShape::Select {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        },
        CleanOriginShape::Select {
            cmp: SelectCmp::Le,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        },
        CleanOriginShape::SelectLiteral {
            cmp: SelectCmp::Eq,
            cmp_param: 0,
            literal: 10,
            then_param: 0,
            else_param: 1,
        },
        // §6f landing 6 — the `==` rung, which is the FIRST select rung that
        // does not map onto `select.{lt,le,eq}`.
        CleanOriginShape::SelectBeq {
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        },
        // §6f landing 7 — the raw-binop rungs, one per operator, and the
        // DIVISION ones carry a strictly positive numeral divisor because that
        // is the only divisor this shape admits. A rung written with
        // `ArithOperand::Param(1)` on the right of a `Div` would map onto a row
        // fine (a row selects vocabulary) and could never be PLANNED, which is
        // the boundary `landing7_selection_probes::l7_p8` measures.
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::BitAnd,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::BitOr,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(15),
        },
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::Div,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(3),
        },
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::Rem,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(3),
        },
        // 2026-09-23: the two rungs clean `bf31976f48` unlocked. The shift
        // carries a numeral amount below the width because that is the only
        // amount this shape plans (`landing7_selection_probes::l7_p14`).
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::BitXor,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::Shr,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(3),
        },
        CleanOriginShape::StructuralNatRec {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
        CleanOriginShape::WellFoundedNatRec {
            zero_value: RecBodyExpr::NatConst(0),
            nonzero_value: RecBodyExpr::Rec,
            rec_args: vec![RecBodyExpr::Pred],
            measure_index: 0,
            lowering: trust_clean_origin::WfLowering::OnParameter,
        },
        // W5 (Lean-calls-Rust): the Rust-call chain rung, `inc (inc x)`.
        CleanOriginShape::RustCallChain {
            nodes: vec![
                trust_clean_origin::RustCallNode {
                    callee: 0,
                    args: vec![trust_clean_origin::RustCallArg::Param(0)],
                    let_binding: None,
                },
                trust_clean_origin::RustCallNode {
                    callee: 0,
                    args: vec![trust_clean_origin::RustCallArg::Node(0)],
                    let_binding: None,
                },
            ],
        },
    ];
    for rung in &rungs {
        assert!(
            ladder_row(rung).is_some(),
            "the ladder rung {rung:?} maps onto no row, so the label and the table disagree \
             about what the compiler can emit"
        );
    }
    let projection = ladder_row(&CleanOriginShape::Projection { projected: 0 }).expect("row");
    let inductive =
        ladder_row(&CleanOriginShape::InductiveProjection { projected: 0 }).expect("row");
    assert_eq!(
        projection.name, inductive.name,
        "the two projection rungs must select ONE row: they emit the same MIR and reflect \
         through the same producer, and the only thing that differs is how side A found them. \
         That identity is the ladder-not-a-boundary claim."
    );
}

// ── H-I: THE DOUBLE FAULT ──────────────────────────────────────────────────

/// `docs/TCB.md` rests the Clean-origin reflection row on a double fault: *"a
/// rendering bug alone is caught structurally, a recognition bug alone is
/// caught by the kernel."* It works because side B's reader was authored in a
/// different crate, for a different direction, and knows nothing about side A.
///
/// The mechanical guarantee is that `trust-types` does not — and cannot —
/// depend on `trust-clean-origin`. A dependency edge in that direction would
/// make the reader able to consult the table, and the two "independent"
/// readings would become one.
#[test]
fn h_i_the_side_b_reader_cannot_name_the_table() {
    let manifest =
        std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-types/Cargo.toml"))
            .expect("trust-types' manifest is a sibling of this crate");
    assert!(
        !manifest.contains("trust-clean-origin"),
        "trust-types has acquired a dependency on trust-clean-origin. Side B's reader could \
         then consult the instruction-selection table, and the two independent readings the \
         gate compares would collapse into one authorship. This is the double fault \
         docs/TCB.md rests on; the edge must not exist."
    );

    let reader = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../trust-types/src/admissible_body.rs"
    ))
    .expect("side B's reader is where it has always been");
    assert!(
        !reader.contains("SelectionRow") && !reader.contains("trust_clean_origin"),
        "side B's reader names the selection table. The table selects VOCABULARY; the reader \
         owns DATAFLOW, and it must own it without consulting what side A was told to emit."
    );
    // The two deliberately-separate entry points are still separate: the E6
    // kernel-import direction must stay blind to recursive bodies BY
    // CONSTRUCTION, which is a missing VARIANT, not a runtime profile flag.
    assert!(
        reader.contains("pub fn recognize_structural_rec")
            && reader.contains("pub fn recognize_wf_nat_rec"),
        "the recursive readers must remain separate entry points outside \
         `recognize_admissible_body`'s chain"
    );
    let chain_start = reader
        .find("pub fn recognize_admissible_body")
        .expect("the non-recursive chain is where it has always been");
    let chain = &reader[chain_start..chain_start + 1_200];
    assert!(
        !chain.contains("recognize_structural_rec") && !chain.contains("recognize_wf_nat_rec"),
        "a recursive reader has joined `recognize_admissible_body`'s chain. That chain also \
         feeds `trust_certify::clean_island::admit_function_into`, where a recognized body \
         becomes a defining equation with NO side A and NO kernel gate — a false definitional \
         import, which is strictly worse than a wrong binary."
    );
}

/// The reflector reads side B ONLY. If it could see the plan, its rendering
/// could be derived from side A and the kernel comparison would degenerate
/// into a round trip — the failure `emit.rs`'s module header opens by naming.
#[test]
fn h_i_the_reflector_never_sees_the_plan() {
    let reflector = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/reflect.rs"))
        .expect("the reflector is where this landing put it");
    for forbidden in ["CleanOriginPlan", "CleanOriginShape", "plan_clean_origin_body"] {
        assert!(
            !reflector.contains(forbidden),
            "the reflector names `{forbidden}`. Side B must be a reading of what was EMITTED; \
             taking anything from the plan makes the gate check that the compiler read the \
             Clean term correctly and say nothing about what it emitted."
        );
    }
}

// ── v7/D3: a refusal cites the missing row BY NAME, with options ───────────

#[test]
fn a_row_miss_is_a_named_refusal_with_options() {
    let note = no_selection_row("Nat.div", CarrierClass::BignumNat);
    assert!(note.contains("no selection row for `Nat.div`"), "must cite the head: {note}");
    assert!(note.contains("the `Nat` bignum carrier"), "must cite the carrier: {note}");
    assert!(note.contains("options:"), "v7/D3: a refusal without options is a defect: {note}");
    assert!(
        note.contains("proof position"),
        "the options must include the one that always works: {note}"
    );
    assert!(
        note.contains("nat.add") && note.contains("uint.add"),
        "the refusal must enumerate the rows that DO exist, so the reader can see the \
         boundary rather than guess at it: {note}"
    );
    // The enumeration is derived from the table, never hand-maintained prose:
    // every row must appear, so the text cannot lag the thing it describes.
    for candidate in ROWS {
        assert!(
            note.contains(candidate.name),
            "row `{}` is missing from the row-derived enumeration",
            candidate.name
        );
    }
}

/// **A head a row selects is never cited as a row miss — and a row is asked at
/// ITS OWN position.**
///
/// `rows_selecting_head` is the table's answer to the question
/// `no_selection_row`'s text used to answer "none" to unconditionally. This
/// control asks it with head spellings written HERE, independently of
/// `KernelSelector::selects_head` — one per constant-keyed side-A selector of
/// every row — each in a body whose positions are the ones that row family is
/// stated over, and requires the selecting rows AND the carrier they are cited
/// at to be exactly the expected ones. It also requires every row of the table
/// to be accounted for, either in the spelling list or in the list of rows
/// keyed on no constant name, so a new row fails this control until someone
/// says which head selects it.
///
/// The second half is the refutation of 2026-09-23 made permanent: a row is
/// matched at the carrier of the position IT is stated over, never at one
/// carrier assumed for the whole body. `ite` in a `Bool`-VALUED body selects no
/// `select.*` row; `decide` selects the `comparison.*` rows only at a compared
/// width (not at the result, not at the parameters); `and`/`or`/`Bool.not` are
/// cited at their `Bool` operands' class and never at a machine width; and
/// every such miss keeps `no_selection_row` at the RESULT's class,
/// byte-for-byte.
#[test]
fn a_selected_head_is_not_cited_as_a_row_miss() {
    use CarrierClass::{AnyExact, BignumNat, MachineUInt};
    // The positions of a body, written out per family.
    let result = AnchoredCarriers::result_only;
    // A `Bool`-valued comparison: result `Bool`, compared at `class`.
    let compared = |class| AnchoredCarriers {
        result: AnyExact,
        compared_operands: Some(class),
        head_operands: None,
    };
    // A `Bool` connective: result `Bool`, operands `Bool`.
    let connective = AnchoredCarriers {
        result: AnyExact,
        compared_operands: None,
        head_operands: Some(AnyExact),
    };
    // (head label, the body's positions, the carrier the citation must name,
    // the rows that must — and alone may — select it). Carrier-spelled
    // selectors are sampled at a width other than u64 on purpose: `{C}` ranges
    // over the class, not over one width.
    let spellings: &[(&str, AnchoredCarriers, CarrierClass, &[&str])] = &[
        ("HAdd.hAdd", result(MachineUInt), MachineUInt, &["uint.add"]),
        ("UInt64.add", result(MachineUInt), MachineUInt, &["uint.add"]),
        ("HSub.hSub", result(MachineUInt), MachineUInt, &["uint.sub"]),
        ("UInt8.sub", result(MachineUInt), MachineUInt, &["uint.sub"]),
        ("HMul.hMul", result(MachineUInt), MachineUInt, &["uint.mul"]),
        ("UInt16.mul", result(MachineUInt), MachineUInt, &["uint.mul"]),
        ("OfNat.ofNat", result(MachineUInt), MachineUInt, &["uint.lit"]),
        ("UInt32.ofNat", result(MachineUInt), MachineUInt, &["uint.lit"]),
        (
            "ite",
            result(MachineUInt),
            MachineUInt,
            &["select.lt", "select.le", "select.eq", "select.beq"],
        ),
        (
            "decide",
            compared(MachineUInt),
            MachineUInt,
            &["comparison.lt", "comparison.le", "comparison.eq"],
        ),
        (
            "Decidable.decide",
            compared(MachineUInt),
            MachineUInt,
            &["comparison.lt", "comparison.le", "comparison.eq"],
        ),
        ("BEq.beq", compared(MachineUInt), MachineUInt, &["comparison.eq"]),
        ("Bool.not", connective, AnyExact, &["bool.not"]),
        ("and", connective, AnyExact, &["bool.and"]),
        ("or", connective, AnyExact, &["bool.or"]),
        ("HAnd.hAnd", result(MachineUInt), MachineUInt, &["uint.and"]),
        ("HOr.hOr", result(MachineUInt), MachineUInt, &["uint.or"]),
        ("HDiv.hDiv", result(MachineUInt), MachineUInt, &["uint.div"]),
        ("HMod.hMod", result(MachineUInt), MachineUInt, &["uint.mod"]),
        ("HXor.hXor", result(MachineUInt), MachineUInt, &["uint.xor"]),
        ("HShiftRight.hShiftRight", result(MachineUInt), MachineUInt, &["uint.shr"]),
        ("Nat.rec", result(BignumNat), BignumNat, &["nat.rec.structural"]),
        ("WellFounded.fix", result(BignumNat), BignumNat, &["nat.wf.fix"]),
        ("Nat.sub", result(BignumNat), BignumNat, &["nat.sub"]),
        ("HSub.hSub", result(BignumNat), BignumNat, &["nat.sub"]),
        ("Nat.mod", result(BignumNat), BignumNat, &["nat.mod"]),
        ("HMod.hMod", result(BignumNat), BignumNat, &["nat.mod"]),
        ("Nat.add", result(BignumNat), BignumNat, &["nat.add"]),
        ("HAdd.hAdd", result(BignumNat), BignumNat, &["nat.add"]),
        ("Nat.mul", result(BignumNat), BignumNat, &["nat.mul"]),
        ("HMul.hMul", result(BignumNat), BignumNat, &["nat.mul"]),
        // `nat.lit`'s arm readers take the kernel literal (no constant), these
        // two constant spellings, and — on the well-founded lane — a
        // `Nat.succ` tower over one of them.
        ("OfNat.ofNat", result(BignumNat), BignumNat, &["nat.lit"]),
        ("Nat.zero", result(BignumNat), BignumNat, &["nat.lit"]),
        // `Nat.succ` is read by TWO arm readers: the structural lane's case
        // value reads `Nat.succ k` as the parameter (`nat.param`), the
        // well-founded lane's numeral reader unwinds a tower (`nat.lit`).
        ("Nat.succ", result(BignumNat), BignumNat, &["nat.param", "nat.lit"]),
    ];
    // Keyed on no constant NAME: a whole-body variable, the recursive
    // occurrence, and the compiler-declared callee (which never reaches the
    // generic site).
    let unnamed = ["param", "nat.self", "rust.call"];

    let mut accounted: BTreeSet<&str> = unnamed.into_iter().collect();
    for (head, at, label, expected) in spellings {
        let selections = rows_selecting_head(head, *at);
        let selecting: Vec<&str> = selections.iter().map(|(selected, _)| selected.name).collect();
        assert_eq!(
            selecting, *expected,
            "`{head}` at {at:?} must be selected by exactly {expected:?}"
        );
        accounted.extend(expected.iter().copied());
        for (selected, position) in &selections {
            assert_eq!(
                *position,
                *label,
                "`{head}`: row `{}` must be matched at {}, the class of the position it is \
                 stated over",
                selected.name,
                label.label()
            );
        }
        // One head, one position: the rows a head selects share one anchor,
        // which is what lets the refusal name ONE carrier for all of them.
        let anchors: BTreeSet<String> =
            selections.iter().map(|(selected, _)| format!("{:?}", selected.anchor)).collect();
        assert_eq!(anchors.len(), 1, "`{head}`: the rows selecting it sit at {anchors:?}");
        // …and the whole-body refusal for it is NOT the row-miss text, and
        // names the carrier the rows were matched at.
        let refusal = whole_body_refusal(head, *at);
        assert_ne!(
            refusal,
            no_selection_row(head, at.result),
            "`{head}` is selected by {expected:?}, so the row-miss text would be false"
        );
        let whole =
            selections.iter().any(|(selected, _)| selected.context != RowContext::RecursionArm);
        let cited = if whole {
            format!("`{head}` at {} IS selected — by ", label.label())
        } else {
            format!("no selection row for `{head}` as a WHOLE body at {} — ", label.label())
        };
        assert!(refusal.starts_with(&cited), "`{head}`: must open with {cited:?}: {refusal}");
        for name in *expected {
            assert!(
                refusal.contains(&format!("`{name}`")),
                "the refusal for `{head}` must cite `{name}`: {refusal}"
            );
        }
    }
    for candidate in ROWS {
        assert!(
            accounted.contains(candidate.name),
            "row `{}` is in neither the spelling list nor the unnamed list: say which head \
             selects it, or why none does",
            candidate.name
        );
    }
    for name in unnamed {
        for (head, at, _, _) in spellings {
            assert!(
                rows_selecting_head(head, *at).iter().all(|(selected, _)| selected.name != name),
                "row `{name}` is keyed on no constant, yet `{head}` selected it"
            );
        }
    }

    // TRUE misses. The coordinate is (head, the position each row is stated
    // over): the SAME head at another class, a carrier spelling a row
    // deliberately does not carry, a category — and the four measured
    // refutations of reading every row at one body carrier. Each selects
    // nothing, and the refusal is `no_selection_row` at the RESULT's class,
    // BYTE-IDENTICAL.
    let misses: &[(&str, AnchoredCarriers, &str)] = &[
        ("HDiv.hDiv", result(BignumNat), "no `Nat` division row"),
        ("HOr.hOr", result(BignumNat), "`uint.or` is a machine-width row"),
        ("UInt64.mod", result(MachineUInt), "the raw-binop rows carry no carrier method"),
        ("UInt64.add", result(BignumNat), "a machine carrier method at a `Nat` result"),
        ("Nat.add", result(MachineUInt), "`nat.add` is a bignum row"),
        ("Nat.succ", result(MachineUInt), "the `Nat.succ` readers are bignum rows"),
        ("Bool.casesOn", result(BignumNat), "no `match` row"),
        ("a projection out of a structure", result(MachineUInt), "a category, not a constant"),
        ("a bound variable", result(AnyExact), "a category, not a constant"),
        // `if a < b then true else false : Bool` — the `select.*` rows are
        // stated over a machine-width RESULT, and this result is `Bool`.
        ("ite", result(AnyExact), "a `Bool`-valued `ite`"),
        // `if h : a < b then true else false : Bool`.
        ("Decidable.casesOn", result(AnyExact), "a dependent `if`"),
        // The comparison rows are stated over the COMPARED width: not over
        // the result, not over the parameters, not over a `Nat` comparison,
        // and not when the proposition compares nothing at a carrier.
        ("decide", result(MachineUInt), "no compared position"),
        ("decide", result(AnyExact), "`decide (a ≠ b)`: an arrow, no compared carrier"),
        ("decide", compared(BignumNat), "a `Nat` comparison"),
        ("BEq.beq", compared(AnyExact), "`Bool == Bool`"),
        // The `bool.*` rows are stated over `Bool` OPERANDS: a body that has
        // no such position selects none of them, whatever its result.
        ("and", result(MachineUInt), "no `Bool`-operand position"),
        ("Bool.not", result(AnyExact), "no `Bool`-operand position"),
    ];
    for (head, at, why) in misses {
        assert!(
            rows_selecting_head(head, *at).is_empty(),
            "`{head}` at {at:?} must select no row ({why})"
        );
        assert_eq!(
            whole_body_refusal(head, *at),
            no_selection_row(head, at.result),
            "`{head}` ({why}): a TRUE row miss keeps the v7/D3 text byte-identical, named at \
             the RESULT's class"
        );
    }
}

/// **Every row declares the position its carrier class is stated over, and
/// the declaration agrees with the realization.**
///
/// `SelectionRow::anchor` has no default, so a row cannot omit it; this
/// control makes the VALUE a checked statement twice over. First, an
/// exhaustive list written HERE, by row name — a new row fails until someone
/// says which position its class is a claim about. Second, the position
/// follows from what the row's MIR computes, stated as an exhaustive match
/// over `MirShape` with no wildcard: a row returning a `bool` computed FROM a
/// comparison of carrier values (`ComparisonValue`) is stated over the compared
/// width, a `bool` connective (`BoolNotValue`, `BoolConnValue`) over its
/// `Bool` operands, the Rust-call chain over its callees' own carriers, and
/// every other realization writes a value AT the carrier its row is stated
/// over — the result.
#[test]
fn every_row_declares_the_position_it_is_stated_over() {
    use CarrierAnchor::{CalleeSignature, ComparedOperands, HeadOperands, Result};
    let declared: &[(&str, CarrierAnchor)] = &[
        ("param", Result),
        ("uint.add", Result),
        ("uint.sub", Result),
        ("uint.mul", Result),
        ("uint.lit", Result),
        ("select.lt", Result),
        ("select.le", Result),
        ("select.eq", Result),
        ("select.beq", Result),
        ("comparison.lt", ComparedOperands),
        ("comparison.le", ComparedOperands),
        ("comparison.eq", ComparedOperands),
        ("bool.not", HeadOperands),
        ("bool.and", HeadOperands),
        ("bool.or", HeadOperands),
        ("uint.and", Result),
        ("uint.or", Result),
        ("uint.div", Result),
        ("uint.mod", Result),
        ("uint.xor", Result),
        ("uint.shr", Result),
        ("nat.rec.structural", Result),
        ("nat.wf.fix", Result),
        ("nat.param", Result),
        ("nat.sub", Result),
        ("nat.mod", Result),
        ("nat.self", Result),
        ("nat.lit", Result),
        ("nat.add", Result),
        ("nat.mul", Result),
        ("rust.call", CalleeSignature),
    ];
    let listed: BTreeSet<&str> = declared.iter().map(|(name, _)| *name).collect();
    let rows: BTreeSet<&str> = ROWS.iter().map(|candidate| candidate.name).collect();
    assert_eq!(listed, rows, "every row, and only rows, must be listed with its anchor");
    for (name, anchor) in declared {
        let candidate = row(name).expect("listed rows exist");
        assert_eq!(candidate.anchor, *anchor, "row `{name}` is stated over the wrong position");
        let from_realization = match candidate.mir {
            MirShape::ComparisonValue(_) => ComparedOperands,
            MirShape::BoolNotValue | MirShape::BoolConnValue(_) => HeadOperands,
            MirShape::RustCallChain => CalleeSignature,
            MirShape::OperandCopy
            | MirShape::InlineScalar
            | MirShape::Call(_)
            | MirShape::ComparisonBranch(_)
            | MirShape::BoolDecisionBranch
            | MirShape::RawBinOp(_)
            | MirShape::ZeroTestBranch
            | MirShape::SelfCall => Result,
        };
        assert_eq!(
            candidate.anchor, from_realization,
            "row `{name}`: its realization {:?} writes a value whose carrier is the {:?} \
             position, but the row declares {:?}",
            candidate.mir, from_realization, candidate.anchor
        );
    }
}

// ── the coverage number ────────────────────────────────────────────────────

/// **§6f: coverage is a MEASURED NUMBER per landing.**
///
/// # The definition
///
/// ```text
/// coverage = |{ d in DEMANDS : a row serves d }| / |DEMANDS|
/// ```
///
/// where a DEMAND is one `(kernel head, carrier class)` pair that
///
/// * the Clean elaborator can place in a `def` body at a total carrier, and
/// * has a NAMED in-tree kernel or planner measurement recording its verdict.
///
/// The evidence requirement is what makes the denominator honest: it cannot be
/// shrunk to inflate the ratio, because dropping a demand drops a measurement
/// this control asserts exists; and it cannot be padded with speculation,
/// because a demand with no measurement fails the same control.
///
/// # What it does NOT measure — read this before quoting it
///
/// It is a **table-row** metric. It says what fraction of the measured demand
/// surface has a row. It says **nothing** about
///
/// * whether the emitter builds a row's MIR correctly (that is the gate's job
///   and would be a second number, measured end-to-end through
///   `build_gated_body`, which needs a build);
/// * whether the elaborator ever produces a spelling (that is
///   `tests/e6-fragment-probe/`'s `matrix.json`, a third number);
/// * anything at all about the whole of Clean — the denominator is a measured
///   LOWER BOUND on the reachable fragment, not the fragment.
///
/// Quoting this as "coverage of the CALL lane" would be exactly the inflated
/// single percentage `CLAUDE.md` opens by warning about.
#[test]
fn coverage_is_recomputed_and_pinned() {
    for demand in DEMANDS {
        assert!(
            !demand.measured_by.is_empty(),
            "demand `{}` carries no measurement. An unmeasured demand is speculation, and \
             speculation in the denominator is a knob.",
            demand.head
        );
        if let DemandStatus::Covered(name) = demand.status {
            assert!(
                row(name).is_some(),
                "demand `{}` claims to be served by row `{name}`, which does not exist",
                demand.head
            );
        }
        if let DemandStatus::Missing(reason) = demand.status {
            assert!(
                reason.len() > 40,
                "demand `{}` is unserved with no stated reason. The MISS histogram is what \
                 ranks the next landing's rows BY MEASUREMENT rather than by guess; a blank \
                 reason ranks nothing.",
                demand.head
            );
        }
    }

    // Every row must be demanded by something. A row nobody demands is either
    // dead or an undocumented widening.
    let served: BTreeSet<&str> = DEMANDS
        .iter()
        .filter_map(|demand| match demand.status {
            DemandStatus::Covered(name) => Some(name),
            DemandStatus::Missing(_) => None,
        })
        .collect();
    for candidate in ROWS {
        assert!(
            served.contains(candidate.name),
            "row `{}` serves no demand in the ledger. Either it is dead, or a demand was \
             never written down — and an unwritten demand is a capability nobody measured.",
            candidate.name
        );
    }

    let covered = covered_demands();
    let total = DEMANDS.len();
    let basis_points = coverage_basis_points();
    println!(
        "\n§6f — SELECTION-TABLE COVERAGE (per-landing history: \
         `PINNED_COVERAGE_BASIS_POINTS`)\n\
         rows implemented : {}\n\
         demands measured : {total}\n\
         demands served   : {covered}\n\
         COVERAGE         : {}.{:02}%  ({basis_points} basis points)\n\
         MISS (ranked work for the next landing):",
        ROWS.len(),
        basis_points / 100,
        basis_points % 100,
    );
    for miss in missing_demands() {
        println!("  - {} @ {}", miss.head, miss.carrier.label());
    }

    assert_eq!(
        basis_points, PINNED_COVERAGE_BASIS_POINTS,
        "the coverage number moved. Landing 1 is capability-neutral, so it must not move by \
         even one demand; a landing that adds rows updates `src/table.rs`'s ledger and this \
         control's pinned constant in the SAME commit. Deviation in EITHER direction fails: a \
         regression, and equally a demand that newly gates without its expectation updated."
    );
}

/// The two-tier honesty statement, executed rather than asserted in prose: the
/// coverage number counts ROWS, and the rows it counts are the ones the tree
/// has measurements for. This pins the shape of the ledger so a future edit
/// that turns it into a free-form list is a failing test.
#[test]
fn the_ledger_separates_measured_absence_from_silence() {
    let missing = missing_demands();
    assert!(
        missing.len() >= 8,
        "the MISS half of the ledger has shrunk. Unserved demands are the honest half of the \
         denominator; deleting them raises the percentage and measures nothing."
    );
    for miss in &missing {
        assert!(
            !miss.measured_by.is_empty(),
            "unserved demand `{}` cites no measurement, so nobody can tell whether it is \
             refused for a reason or merely unimplemented",
            miss.head
        );
    }
}

/// A last structural guard on the row type itself: nothing in a row may name a
/// runtime string. Every constant a reflection can put in a kernel term goes
/// through a `&'static str`, which is what makes the DEFINED CONSTANT —
/// arriving as an ordinary borrowed `&str` — unrenderable, and hence the s2
/// vacuity unconstructible.
#[test]
fn a_row_cannot_smuggle_a_runtime_constant_name() {
    fn is_static(_: &'static str) {}
    for candidate in ROWS {
        if let ReflectSpec::KernelConst(constant) = candidate.reflect {
            is_static(constant);
            assert!(
                !constant.is_empty()
                    && (constant.starts_with("Nat.") || constant.starts_with("Bool.")),
                "row `{}` names the kernel constant `{constant}`, which is outside the `Nat` \
                 recursion prelude and the `Bool` connective prelude (W6) this fragment is \
                 stated over",
                candidate.name
            );
        }
        is_static(candidate.name);
    }
}

/// A `SelectionRow` must remain a plain data row: this pins that the type is
/// `Copy`, i.e. it holds no owned, runtime-constructed state. A row someone
/// could build at runtime is a row an emitter bug could invent.
#[test]
fn rows_are_static_data() {
    fn assert_copy<T: Copy>() {}
    assert_copy::<SelectionRow>();
    assert_copy::<MirShape>();
    assert_copy::<ReflectSpec>();
}
