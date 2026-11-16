// Trust: THE SEAM RATCHET.
//
// Deleting `guards::whole_local_def_count` and `crate::unique_whole_local_def` makes a
// call to either a COMPILE ERROR, which is what stops a rebase re-introducing one. It
// does not stop someone writing a FRESH tally — `for block in &func.body.blocks { … if
// place.local == l { n += 1 } } … n == 1` — which is exactly how the class survived
// three rounds of site-by-site fixing.
//
// This row scans the sources of the two crates that hold a `VerifiableFunction` and
// fails on any def-tally idiom outside `local_defs`. Every entry in the allowlist below
// is a site the pattern audit classified, with the reason it is not a local's
// definition count (or the reason its own count is correct and deliberately stricter).
// A NEW tally fails this test by file and line, which forces the classification.
//
// It is a lint, not a proof: an idiom spelled differently enough escapes it. What it
// buys is that the shapes the audit actually found cannot be added without a reviewer
// seeing this list. FOUR detectors, each the generalization of a site that escaped an
// earlier round. The first three are about COUNTERS ("how many values?") and share
// [`CLASSIFIED`]; the fourth is about RESOLVERS ("what value?") and has its own list.
//
//   * `def-tally-*` — a counter or a `saw_*` flag inside a definition-scanning
//     function. The first cut filtered on the counter's NAME (`_count`, `defs`,
//     `assigns`), which is how `bmc_reduction::local_write_count` (`writes += 1`)
//     escaped; the name filter is gone.
//   * `def-set-collector` — a function whose NAME denotes a per-local whole-definition
//     SET (`*_whole_local*`, `*_local_defs`). Such a function has no parameter opinion
//     of its own, so every CONSUMER carries the entry-definition question;
//     `float_range::float_whole_local_defs` is the site that escaped.
//   * `parameter-arm-def-question` — a function that both branches on `arg_count` and
//     asks one of the def questions listed in [`DEF_QUESTIONS`]. This is the shape of a
//     site that gets the parameter arm RIGHT or WRONG by hand;
//     `discharge::local_versions_collapse_to_bare` is the site that escaped.
//   * the VALUE RESOLVER — see [`every_value_resolver_outside_the_seam_is_classified`].
//     A resolver contains no counter at all, so the three detectors above are blind to
//     it by construction, and it is the more dangerous family: its answer is INLINED,
//     so version renaming cannot rescue a wrong one. `lib.rs::index_local_const` and
//     `guards.rs::latest_same_block_bool_definition` are the two sites that escaped —
//     both live kernel-certified false proofs, both fixed with the round that added
//     this detector.
//   * the CHANNEL SUBSET — see [`every_channel_subset_scan_outside_the_seam_is_classified`].
//     The four detectors above all fire on the SHAPE of a scan. This one fires on what
//     the scan ENUMERATES: a per-local definition scan that sees `Statement::Assign`
//     and is blind to the `Call` DESTINATION. That is the exact shape of `pmod` and
//     `p8`, two live kernel-certified false proofs found after four rounds of
//     shape-only detectors, and it is not a shape a resolver/counter detector can see
//     — `guards.rs::latest_same_block_bool_definition`'s cross-block uniqueness scan
//     was ALREADY in the RESOLVERS list, with a reason that was true of `Assign` and
//     false of `Call` dests.

use std::path::{Path, PathBuf};

/// The crates whose sources may hold a def tally over a `VerifiableFunction`.
/// `trust-mir-extract` is deliberately absent: its counters run over rustc's OWN
/// `mir::Body`, a different type with a different definition model
/// (`mir::Body::args_iter` makes the parameters explicit), and it is audited in the
/// report rather than linted here.
fn scanned_crates() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("crates/").to_path_buf();
    vec![root.join("trust-vcgen/src"), root.join("trust-ir-bridge/src")]
}

/// `<crate-relative path>` of every file that owns a def-counting seam and is therefore
/// allowed to tally definitions.
const SEAM_FILES: &[&str] = &["trust-vcgen/src/local_defs.rs", "trust-ir-bridge/src/local_defs.rs"];

/// Sites the pattern audit classified as NOT a whole-local definition tally of a local
/// that could be a parameter — or as a deliberately stricter one. Keyed by
/// `<crate-relative path>::<symbol on the line>`; the note is the classification.
///
/// Adding an entry means asserting the reason. Removing a site from the sources
/// without removing its entry fails this test too, so the list cannot rot silently.
const CLASSIFIED: &[(&str, &str)] = &[
    (
        "trust-vcgen/src/enum_entry.rs::origin",
        "The parameter arm is dominated by `place_source_is_stable`, whose seam \
         `value_count` charges ENTRY and refuses an in-body parameter write. The \
         whole-CFG pure-body gate also refuses parameter stores, calls and aliases; \
         non-parameters resolve only through `local_defs::unique_value_def`. This \
         branch selects a typed entry-enum origin, not a hand-counted definition.",
    ),
    (
        "trust-vcgen/src/enum_entry.rs::call_argument_origin",
        "The parameter arm follows the seam-backed ENTRY-aware \
         `place_source_is_stable` AND `local_defs::storage_never_aliased` gates. \
         Non-parameters use `local_defs::unique_value_def`; rewritten or aliased \
         arguments cannot become immutable entry values. The arm itself tallies \
         no definitions.",
    ),
    (
        "trust-vcgen/src/generate/constructor_return.rs::infer_constructor_return_candidate",
        "Counts only exact whole-return-slot (`_0`) one-field struct constructions, \
         including unreachable blocks, and requires exactly one. The return slot \
         cannot be a parameter; other return writes refuse. This deliberately \
         stricter shape screen proposes a scalar expression, while the ORIGINAL \
         aggregate body's cleared-entry postcondition rows must all be kernel \
         checked before a constructor fact is admitted.",
    ),
    (
        "trust-vcgen/src/generate/inferred_return/enum_return.rs::eval_uncached",
        "Not a definition tally: `self.case_visits += 1` counts switch-arm visits against \
         `MAX_BLOCK_VISITS`, like the scalar inferencer. Parameters are seeded \
         at ENTRY, the whole-CFG pure-body gate and evaluator both refuse their \
         reassignment, and the candidate still requires original-body kernel checks.",
    ),
    (
        "trust-vcgen/src/generate/contract_vcs.rs::operand_place",
        "Reported at `return_pin_reads_are_current` (the scan attributes it to its inner \
         helper `operand_place`). It asks the seam's own question, \
         `local_defs::is_single_static_assignment`, ONLY for parameters (`1..=arg_count`), \
         where that predicate already counts the ENTRY definition: a parameter read by a \
         bare return pin must have no in-body write. Non-parameters are judged by a \
         separate path-ordered no-later-write scan, never by a tally.",
    ),
    (
        "trust-vcgen/src/type_invariant/unwind.rs::replace_assign",
        "Not a definition tally: the increment counts each BLOCK's CFG predecessors (every \
         normal and cleanup successor edge), so the drop-and-replace walk can require that \
         each block it enters has exactly one. No local is counted, so the parameter \
         question does not arise; `bb0`, which has the implicit entry edge, is refused \
         outright.",
    ),
    (
        "trust-vcgen/src/generate/value_facts.rs::of",
        "Not a definition tally (`BodyFactPresence::of`, PERF-467; VCGEN-SEAM-PERF-REDS-1, \
         refuter-reviewed): `discr_count`, `bare_discr_count` and `bare_binary_calls` are \
         body-wide sums of statement and terminator SHAPES (`Rvalue::Discriminant` \
         assignments, those with a whole-local destination, and whole-local-destination \
         two-argument `Call`s). No count is keyed by a local or compared to 1, and no \
         parameter question arises. Each threshold only pre-gates a global-fact builder \
         whose own scan re-checks the shape, and the gate's outcome never enters a fact. An \
         over-count restores the unconditional pre-PERF-467 run; an under-count withholds \
         facts that every consumer conjoins only as hypotheses (`RowGlobalFacts::for_row`), \
         which can cost a proof or surface a spurious FAILED or replay-lane refutation, \
         never a false proof.",
    ),
    (
        "trust-vcgen/src/generate/inferred_return.rs::eval",
        "Not a definition tally: the increment is `self.visits += 1`, the D5-B \
         synthesizer's BLOCK-visit path budget (`MAX_BLOCK_VISITS`). On the parameter \
         question the synthesizer is exact by construction: parameters are seeded into \
         its environment at ENTRY and any `Assign` to one is refused (`parameter \
         reassigned`), and its output is a candidate the kernel re-checks, never a fact.",
    ),
    (
        "trust-vcgen/src/guards.rs::value_local_is_unstable_scan",
        "ALREADY parameter-aware (`if is_param { assigns >= 1 } else { assigns >= 2 }`) and \
         deliberately STRICTER than the seam: it also counts PROJECTED and `*local = v` \
         stores, so routing it through `value_count` would LOOSEN it. On the PARAMETER \
         question the two are identical — the seam charges the entry definition \
         unconditionally — and \
         `the_scan_keeping_predicates_agree_on_a_live_entry_parameter` pins that. (Renamed \
         2026-10-01 from `value_local_is_unstable`, which now answers from the one-pass \
         per-function table `unstable_locals` — the same predicate, asserted equal to \
         this scan on every question under `cfg(test)`.)",
    ),
    (
        "trust-vcgen/src/lib.rs::index_local_stable",
        "Seeds its counter at `usize::from(is_param)` — the ENTRY definition, spelled out \
         in its own doc — and ANDs the result with `array_local_escapes`. Correct as \
         written; deliberately keeps its scan for the call-dest arm.",
    ),
    (
        "trust-vcgen/src/generate/int_conversion.rs::local_value_is_stable",
        "Seeds its counter at `1` for a parameter, for the same reason and with the same \
         `reassigned_source_gets_no_payload_facts` witness named in its doc.",
    ),
    (
        "trust-vcgen/src/generate/value_facts.rs::vec_length_is_invariant",
        "Not a definition tally: the increment counts every MENTION of the base (and of \
         each reborrow temp) with the exhaustive place walk, to prove all of them are the \
         receiver of a length-benign std call. The base IS required to be a parameter, \
         and its definition question goes through the seam (`local_defs::is_parameter` \
         and `is_single_static_assignment`, which charges the entry definition). The \
         other-parameter arm (`1..=arg_count`) reads parameter TYPES, not definitions.",
    ),
    (
        "trust-vcgen/src/generate/value_facts.rs::vec_sole_mutator_block",
        "Not a definition tally: the increments count every MENTION of the mutator's \
         reborrow temp with the exhaustive place walk, to prove its only use is the \
         receiver (review round 95). The temp is never a parameter: it reaches here only \
         when it differs from the base, has an in-body `&mut (*base)` definition, and \
         passed the seam's `is_single_static_assignment`, which charges a parameter's \
         entry definition.",
    ),
    (
        "trust-vcgen/src/generate/value_facts.rs::root_is_never_reseated",
        "Parameter-aware by construction (`if is_param { defs == 0 } else { defs == 1 }`) \
         — the same answer the seam gives on the parameter arm — and STRICTER than the \
         seam elsewhere: a projected store or a `Call` dest returns `false` outright, \
         where `holds_one_value` counts the call dest as one of the values it allows.",
    ),
    (
        "trust-vcgen/src/generate/assert_refutation.rs::v2_input_free_locals",
        "The REFUTATION lane's input-free set. Its two per-local tallies (`LocalCounter` \
         `read_count` and the `mut_borrowed` flags, PERF-471) count READS and borrows, not \
         definitions. `read_count` is consulted only for a payload-extractor ARGUMENT that \
         is already a parameter in `safe` (entry-stable by \
         `local_versions_collapse_to_bare`, which refuses every visible in-body write and \
         mutable escape), and an unanalyzable terminator returns before any such \
         admission. It never decides whether a parameter is written. A read it misses (an \
         `Index` projection's local, an intrinsic operand) only makes an extractor result \
         FREER, and a freer variable can only produce a counterexample — a false REFUTE, \
         never an UNSAT (refuter-reviewed, VCGEN-SEAM-PERF-REDS-1).",
    ),
    (
        "trust-vcgen/src/generate/loop_bounds.rs::accumulator_init_const",
        "The tally identifies WHICH two definitions were seen (const init + self-add); \
         the VALUE count beside it is `local_defs::value_count(func, acc).is_exactly(2)`. Both \
         are required — `param_accumulator_bound_still_refutes` is the row.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::acc_accumulator_init_const",
        "The bridge port of that producer, with the same split: the tally identifies the \
         two definitions, `local_defs::value_count` counts the values.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::resolve_bool_comparison_def",
        "The tally is the function's own `> 1` fail-closed bail; the parameter question \
         is `local_defs::holds_one_value(func, local)` on the same line.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::step_by_local_reseatable",
        "`saw_next` records whether an ALIAS temp is used only as `Iterator::next`'s \
         receiver. It counts USES of a borrow, not definitions of a local.",
    ),
    (
        "trust-vcgen/src/paired_condvar_cert.rs::single_def_unaliased",
        "The tally pins the definition to ONE GIVEN statement `(db, ds)`; the value count \
         is `local_defs::has_one_explicit_def` on the same expression.",
    ),
    (
        "trust-vcgen/src/typestate.rs::operand_is_input_field",
        "The tally pins the operand to a single `Use` definition it then inspects; the \
         value count is `local_defs::body_has_one_explicit_def` on the same condition.",
    ),
    (
        "trust-vcgen/src/recursive_datatype_functional.rs::walk",
        "`ih_counter` names FRESH induction-hypothesis variables (`__ih0`, `__ih1`, …) at \
         recursive call sites. It counts calls, not definitions of any local.",
    ),
    // ── NOT definition tallies: counters that happen to sit in a def-scanning fn ──
    (
        "trust-vcgen/src/generate/float_range.rs::is_dest",
        "`uses`/`int_cast_uses` count READS of a float result (is it consumed only by a \
         saturating `as INT` cast?), never definitions of it.",
    ),
    (
        "trust-vcgen/src/generate/bmc_reduction.rs::body_is_straight_line_reduction",
        "`next_calls` counts `Iterator::next` CALL terminators against the trip count. \
         Not a per-local definition tally.",
    ),
    (
        "trust-vcgen/src/generate/induction.rs::countdown_trip_analysis",
        "`steps` is the acyclic-path-enumeration fuel (`steps > 4096` bails). It counts \
         search steps, not definitions.",
    ),
    (
        "trust-vcgen/src/generate/witness_grounding.rs::resolve_forwarded_call_return_variant",
        "`n_reaching` counts SwitchInt EDGES that reach the forwarding block, to insist \
         on exactly one. It counts edges, not definitions.",
    ),
    (
        "trust-vcgen/src/generate/assert_refutation.rs::def_base_name",
        "`qi` is the cursor of the needed-variable worklist while resolving definitions \
         into the conjunction. It indexes a queue, not definition sites.",
    ),
    (
        "trust-vcgen/src/guards.rs::local_mut_borrows_may_resize_one",
        "`mentions`/`benign` count USES of a BORROW TEMP (`_t = &mut v`) — every mention \
         anywhere, against the ones accounted for as `Index`/`IndexMut` receivers (and, since \
         VEC-AS-SLICE, as the receiver of `Vec`'s own `deref_mut`/`as_mut_slice`). Uses of a \
         temp, not definitions of the borrowed local. W4 fix round 1 (2026-09-25): the body \
         moved here from `local_mut_borrows_may_resize`, which now asks it once per member of \
         the base's alias closure; the key follows the body.",
    ),
    (
        "trust-vcgen/src/guards.rs::mut_pointer_uses_may_resize",
        "`mentions`/`benign` count USES of a mutable POINTER local (a `&mut Vec` parameter \
         or an alias of one) against the forms that cannot resize its pointee. `own_defs` \
         admits at most ONE whole-local aliasing `Assign` of a NON-parameter local \
         (`local <= arg_count` admits none, so a parameter's entry definition is never \
         mistaken for a body one); every other write of it, through any channel, is a \
         mention the exhaustive place walk counts and nothing accounts, so it answers \
         \"may resize\". It resolves no value (VEC-LEN-PARAM-COPY-1, 2026-10-07).",
    ),
    (
        "trust-vcgen/src/value_analysis.rs::analyze_function",
        "`iteration` is the forward-dataflow fixpoint counter, capped at \
         `blocks.len() * 15 + 50`. Not a definition tally.",
    ),
    (
        "trust-vcgen/src/fuel_outcome_functional.rs::emit_loop_sim",
        "`n_dones`/`n_continues` count the loop-simulation ARMS emitted per constructor. \
         Not a definition tally.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::lower_rvalue",
        "`operand_idx` walks an `Aggregate`'s operand list against the ADT's field list. \
         An operand cursor, not a definition tally.",
    ),
    // ── REAL definition/write tallies, each parameter-aware ─────────────────
    (
        "trust-vcgen/src/generate/assert_refutation.rs::generate_full_assert_refutation_candidates_impl",
        "Two per-local `LocalCounter` tallies (PERF-471): `wrap_call_def_count` over Call \
         dests and the whole-local `Assign` count behind `single_assign_names`, which also \
         requires `wrap_call_def_count == 0`, so a local with ANY Call-dest definition is \
         never named. These DEFINITIONS matter in the proof direction: the lane's UNSAT is \
         consumed as a proof (`panic_calls_proven_unreachable`). Each count is checked by \
         its caller (the wrap lane and `clean_origin_definitional_call_models` require \
         exactly one Call dest; `wrapping_result_local_is_stable` is passed a literal 1) \
         and ANDed with `guards::value_local_is_unstable`, which IS parameter-aware (`if \
         is_param { assigns >= 1 }`, counting every Assign, SetDiscriminant, Deinit and \
         Call dest, and true on any `&mut` / `AddressOf`), so a parameter with any visible \
         body write is excluded from both. Inline-assembly outputs (`Terminator::Opaque`) \
         are invisible to that check; such a body carries an unsupported-MIR row that \
         blocks the function-level discharge (refuter-reviewed, VCGEN-SEAM-PERF-REDS-1).",
    ),
    (
        "trust-vcgen/src/generate/bmc_reduction.rs::local_write_count",
        "A raw write tally with no parameter opinion. Its ONE caller \
         (`is_iterator_option_tag_fact`) excludes parameters BEFORE consulting it — \
         `if d == 0 || d <= func.body.arg_count || local_write_count(func, d) != 1`.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::local_is_stable_for_value_witness",
        "The consumer that gives `local_write_count` its parameter arm: it forces \
         `expected_writes = 0` for `1..=arg_count`, so a parameter with ANY body write \
         fails every value witness whatever the caller asked for.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::local_write_count",
        "A raw write tally over `&[TrustBlock]`, which carries no `arg_count` and so can \
         have no parameter opinion. Its consumer `local_is_stable_for_value_witness` \
         takes `arg_count` and forces `expected_writes = 0` for a parameter, so a \
         parameter with any body write fails every value witness.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::bundled_member_assert_admission",
        "NOT A LOCAL'S DEFINITION COUNT. `discharged` tallies member ASSERTS retired by a \
         nonzero constant divisor — one `continue` per member — so it never decides how many \
         values any local holds; it trips the shape detector only because the enclosing \
         function also walks blocks. The local question is delegated to the `resolve` closure, \
         which answers the parameter arm FIRST (`place.local >= 1 && place.local <= arg_count` \
         returns `DivisorRoot::Formal`) and therefore never hands back a parameter's BODY \
         store as that parameter's value — the failure mode this file exists to stop. \
         RESIDUAL, NOT CLOSED BY THIS ENTRY: that same early return also does not check \
         whether the parameter is REASSIGNED before the operation, so a divisor spelled \
         `d` after `d = a` resolves to the caller-facing formal `d` while the division \
         reads `a`. Charging the caller a precondition on the ENTRY value would then \
         discharge an Assert about a different one. No witness was built for it here and \
         it is upstream's code (`8e6bda6986`), so it is recorded rather than changed; the \
         RESOLVER detector cannot see it because `resolve` is a closure, not a named fn.",
    ),
    // ── def-SET collectors: no parameter opinion of their own ───────────────
    (
        "trust-vcgen/src/generate/float_range.rs::float_whole_local_defs",
        "Returns the whole-local def SET (poisoned to `None` by a projected store, \
         `SetDiscriminant`/`Deinit`, a `&mut`/`&raw mut` borrow or an `Opaque` \
         terminator) and takes no position on parameters. EVERY consumer is classified \
         below and each writes the entry-definition arm itself.",
    ),
    (
        "trust-vcgen/src/generate/witness_grounding.rs::f4_whole_local_defs",
        "Rejects a PARAMETER outright — defs or no defs — so the edge facts joined over \
         the visible defs cover every value a read can see.",
    ),
    (
        "trust-vcgen/src/generate/slice_conversion.rs::unique_whole_local_conversion_call",
        "Rejects a PARAMETER receiver outright. Its conclusion SUPPRESSES a panic \
         obligation, so an entry value the conversion Call does not dominate would be a \
         false proof.",
    ),
    (
        "trust-vcgen/src/generate/value_facts.rs::whole_local",
        "A nested `fn whole_local(op) -> Option<usize>` that destructures an operand into \
         its projection-free local; the lint attributes the enclosing \
         `clamp_upper_bound` scan to it. That scan's own budget is \
         `defs.len() == 2 && local_defs::value_count(func, local).is_exactly(2)`, so a merged \
         PARAMETER (three values) is refused.",
    ),
    // ── parameter-arm def questions ─────────────────────────────────────────
    (
        "trust-vcgen/src/generate/discharge.rs::local_versions_collapse_to_bare",
        "Writes the parameter arm explicitly and STRICTER than the seam: a parameter must \
         have NO statement write, NO call-dest write and pass `place_source_is_stable`; \
         only a non-parameter is allowed the seam's one definition.",
    ),
    (
        "trust-vcgen/src/generate/discharge.rs::caller_precondition_var_is_entry_stable",
        "Requires `1 <= local <= arg_count` AND `local_is_never_written` AND \
         `place_source_is_stable` AND no Call dest — zero body definitions, which is the \
         strictest reading of the entry-value question.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::entry_stable_operand_formula",
        "On reaching a parameter it demands `local_defs::never_explicitly_reseated` \
         before returning the entry-value term; a non-parameter hop goes through \
         `local_defs::unique_value_def`.",
    ),
    (
        "trust-vcgen/src/generate/float_overflow.rs::v2_float_contract_magnitude_hypotheses",
        "Hops through `place_source_is_stable` + `local_defs::unique_value_def` and stops \
         at the first PARAMETER-rooted place, handing that place to `contract_range`, \
         which re-checks the formal's entry stability.",
    ),
    // `callsite.rs::callee_postcondition_is_injectable` was HERE, and its key was
    // removed by the stale-claim half of this row rather than kept: upstream moved the
    // callee-arity match out of that function, so its body no longer mentions
    // `arg_count` and the detector no longer sees it. Its dest gate is still
    // `local_defs::is_single_static_assignment` — the seam routing that made the entry
    // sound in the first place is unchanged; only the claim about a shape that is no
    // longer there is gone.
    (
        "trust-vcgen/src/generate/induction.rs::countdown_zero_trip_eq",
        "Resolves the compared operand to a PARAMETER root explicitly (`(1..=arg_count)\
         .contains(&p.local)`, or one single-def whole copy of one) and then requires \
         `local_value_is_stable` of that root.",
    ),
    (
        "trust-vcgen/src/generate/unwrap_panic.rs::unwrap_receiver_tag_term",
        "The `Discriminant` destination must NOT be a parameter \
         (`(1..=arg_count).contains(&dest.local)` is a `continue`), and must pass \
         `place_source_is_stable` plus a `local_defs::unique_value_def` re-check.",
    ),
    (
        "trust-vcgen/src/generate/unwrap_panic.rs::subject_read_pinned_dest",
        "The read-pinned twin of `unwrap_receiver_tag_term` for a SUBJECT place (2026-10-03): \
         the `Discriminant` destination must NOT be a parameter \
         (`(1..=arg_count).contains(&dest.local)` is a `continue`), and must pass \
         `place_source_is_stable` plus a `local_defs::unique_value_def` re-check that the \
         read of exactly this subject is its one definition.",
    ),
    (
        "trust-vcgen/src/generate/bmc_reduction.rs::is_iterator_option_tag_fact",
        "Excludes parameters before the write tally (`d <= func.body.arg_count` returns \
         false), so the `local_write_count(func, d) != 1` budget only ever decides a \
         body temp.",
    ),
    (
        "trust-vcgen/src/generate/float_range.rs::float_range",
        "The tracer's whole-local arm: `is_param` with a NON-EMPTY def set returns `None` \
         outright (the entry value is a def the hull does not enclose); an EMPTY def set \
         is the entry-stable formal, read from the caller override / contract facts.",
    ),
    (
        "trust-vcgen/src/generate/float_range.rs::float_aggregate_range",
        "Bails on a parameter base before the def set is consulted \
         (`if local >= 1 && local <= ctx.func.body.arg_count`).",
    ),
    (
        "trust-vcgen/src/generate/float_range.rs::collect_adt_construction_defs",
        "Same parameter bail, before `float_whole_local_defs`.",
    ),
    (
        "trust-vcgen/src/generate/float_range.rs::float_abs_guard_magnitude_bounds",
        "`stable_base` writes the parameter arm (`base_is_param => defs.is_empty()`), and \
         `resolve_to_source` — which is also reached on the abs ARGUMENT, a place \
         `stable_base` has not vetted — rejects a parameter outright for the same \
         reason.",
    ),
    (
        "trust-vcgen/src/generate/mod.rs::guard_alias_names",
        "Skips parameters explicitly before the single-def alias test: a parameter's \
         entry value is an invisible extra def, so its one `Use(copy place)` does not \
         pin its value at every read.",
    ),
    (
        "trust-vcgen/src/sep_engine.rs::box_value_is_validity_rooted",
        "Not a definition tally: the increment is `hops += 1`, the number of \
         `single_copy_source` hops the root walk has taken (D14 admits a reference-argument \
         root only after exactly one hop). Every hop's value count goes through \
         `local_defs::holds_one_value` first.",
    ),
    (
        "trust-vcgen/src/generate/panic_calls.rs::range_bound_unchanged_until_call",
        "Not a definition tally: `seen_terminator_read` counts the TERMINATORS that READ \
         the range local, to one, so the call being verified is the only call that reads it \
         (review round 34's false proof). No definition is counted. The range local's one \
         value and the bound's are judged as its RESOLVERS entry says, through the seam and \
         the per-block `local_write` checks.",
    ),
];

/// Sites the RESOLVER audit classified — the parallel family the counter detectors
/// above cannot see, because a resolver has no counter in it at all. Keyed and read
/// exactly like [`CLASSIFIED`]: adding an entry asserts the reason, and an entry whose
/// site is gone fails the test.
///
/// The question every entry answers is the SAME one, in the resolver direction: CAN THE
/// LOCAL BE A PARAMETER, and if it can, what stops the block-scanned definition — the
/// parameter's SECOND value — from being handed back as its value? There are four sound
/// answers, and each entry names which one it is:
///   (a) it asks the seam (`local_defs::unique_value_def` / `holds_one_value` /
///       `has_one_explicit_def` / `value_count` / `is_single_static_assignment`);
///   (b) it excludes parameters outright (`arg_count`, `is_parameter`);
///   (c) EVERY consumer does one of those before consulting it;
///   (d) the local it is keyed on cannot be a parameter — it is a `Call` destination,
///       a `CheckedBinaryOp` tuple temp, or another local the resolver itself created.
///
/// WHAT AN ENTRY MEANS. This list is an ALLOWLIST — the FOURTH of this lint's four, the
/// other three being [`CLASSIFIED`], [`CHANNEL_SUBSETS`] and [`CHANNEL_SUBSET_BASELINE`].
/// Entering a key here is the act that stops
/// [`every_value_resolver_outside_the_seam_is_classified`] failing on that site: the
/// detector still sees the scan, and the entry is a REVIEWER'S CLAIM that the scan is
/// sound for the reason written beside it. Adding one is therefore an allowlisting act,
/// and it MUST carry a reason naming one of (a)-(d) above — a bare key, an empty reason
/// or a reason that classifies nothing is refused by
/// [`every_resolver_entry_carries_a_reason_and_a_live_site`], as is an entry whose site
/// has been renamed or deleted. Adding an entry WITH a reason is the sanctioned move —
/// the detector's own failure message prescribes it in those words ("add it to RESOLVERS
/// with which of those it is") — but sanctioned is not invisible: a change that adds one
/// has widened an allowlist and says so.
const RESOLVERS: &[(&str, &str)] = &[
    (
        "trust-vcgen/src/generate/value_facts.rs::vec_sole_mutator_block",
        "(b) The block scan resolves only the receiver temp's `&mut (*base)` definition, \
         and only when the temp differs from the base; the temp must then pass the seam's \
         `is_single_static_assignment`, which charges a parameter's entry definition, so a \
         parameter temp is refused. The base's own definition question is \
         `vec_length_is_invariant`'s, which goes through the seam.",
    ),
    (
        "trust-vcgen/src/generate/loop_bounds.rs::shrinking_trip",
        "(c)/(b) A PARAMETER counter is expected and safe: the trip bound uses only `n <= \
         MAX(width)`, never `n`'s entry (or any outside-the-loop) value, so the entry \
         definition the block scan cannot see is never consulted. Inside the loop the scan \
         requires exactly ONE write (any second write, partial write, escape or \
         unlocatable write refuses), and the temp it reads through is resolved by the seam \
         (`is_single_static_assignment` + `unique_value_def`).",
    ),
    (
        "trust-vcgen/src/generate/panic_calls.rs::range_bound_unchanged_until_call",
        "(a) The bound's temp is resolved through the seam (`local_defs::unique_value_def` and \
         `is_single_static_assignment`). The range local and the bound's source are NOT given \
         a block-scanned value: the VC reads them at the indexing call, where the version \
         rename binds the version current there, and the resolver only checks that the \
         range's in-block aggregate write and the source's read are the LAST writes before \
         that call (`local_write` Untouched after each) with no escape anywhere, so a \
         parameter's entry definition is never the value read.",
    ),
    (
        "trust-vcgen/src/guards.rs::clean_variant_switch_target",
        "(d) `local` is the destination of the `Call` terminating `from` (`<[T]>::get`, \
         core's `Try::branch` or `Option::copied`, or a TINV-21 inventory call), never a \
         parameter. The scan reads ONE block — entered only from that call block — whose \
         sole value statement is `d = Discriminant(local)` before its own switch, beside \
         only storage markers/`Nop`s naming neither `local` nor `d` (TINV-21), so the tag \
         read is the one that call just wrote on every path in (2026-10-04: the \
         single-predecessor gates closed a false proof on a shared switch block, \
         `tests/slice_get_try_realmir.rs`).",
    ),
    (
        "trust-vcgen/src/guards.rs::try_branch_continue_target",
        "(d) `opt` is the `<[T]>::get` call destination and the `branch` result is the \
         destination of the block's own authenticated `Try::branch` call, never a \
         parameter; it only checks that the block is that call on `move opt` and hands the \
         result to `clean_variant_switch_target` under the same single-predecessor gate.",
    ),
    (
        "trust-vcgen/src/guards.rs::option_copied_hop",
        "(d) `opt` is the destination of the `<[T]>::get` call terminating `from`, never a \
         parameter, and `out` is the destination of the block's own call, authenticated as \
         core's `SysrootItem::OptionCopied` from the real sysroot. It only checks that the \
         block — entered only from that call block, storage markers/`Nop`s beside the call \
         naming neither local — is that call on `move opt`, and hands `out` to \
         `option_some_arm` under the same single-predecessor gate (TINV-21, 2026-10-06).",
    ),
    (
        "trust-vcgen/src/generate/range_bound_use.rs::defining_assign",
        "(b) A parameter's ENTRY value never reaches this arm: the statement is the one the \
         version oracle names as the write the read sees (`ValueId::Def`; a read of the entry \
         value is `ValueId::Entry` and declines), and where the oracle names nothing the \
         fallback is `local_defs::unique_defining_block`, which refuses a parameter and any \
         local with a second value, a partial write or an alias. The block-scanned statement \
         is then only LOCATED in the block the seam named, and kept only if it dominates the \
         read (Trust 2026-10-02, class 10).",
    ),
    (
        "trust-vcgen/src/generate/dominating_facts.rs::copy_source",
        "(b) A parameter's ENTRY value never reaches this arm: the statement is the one the \
         version oracle names as the write the read sees (`ValueId::Def`), and a read of the \
         entry value is `ValueId::Entry`, so a parameter's block-scanned SECOND value is \
         read only where it IS the value read. The copy is then used only when its source \
         holds the same `ValueId` at the copy and at the read, the copy dominating the read.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::acc_accumulator_init_const",
        "(a) The def SET is this scan's own `def_count`, but the VALUE budget beside it is \
         `local_defs::value_count(func, acc).is_exactly(2)`, which charges a PARAMETER for its entry \
         definition. Its trust-vcgen twin carried a live kernel-certified false proof on exactly \
         this hole; the note in the body says so.",
    ),
    // Trust: 2026-09-16 (second round) — SEVEN MORE ENTRIES RETIRED, NOT WAIVED, and the
    // reason each of them gave was TRUE AND INSUFFICIENT. `acc_next_call_range_operands`,
    // `acc_next_call_to_array_operand` (bridge), `slice_iter_next_kind`,
    // `next_call_enumerated_slice`, `next_call_range_operands`, `next_call_to_array_operand`
    // and `charindices_iter_string_root` (vcgen) were each classified "(d) keyed on an
    // `Iterator::next` `Call` dest, hands off to a tracer that asks the seam". A `next`
    // result cannot be a PARAMETER — that much held — but it CAN have two writes: rustc's
    // `expr_into_dest` lowering of `let o = if c { small.next() } else { big.next() }`
    // writes ONE Option local from two `next` calls, and each of these took the FIRST call
    // in block order and handed its receiver to a tracer whose every hop below was
    // legitimately single-constructor. `a[i]` on a `[u8; 5]` PROVED, kernel-certified, on
    // the pristine driver while the `big` branch yields 50 (`tests/escaped_local_seam_
    // realmir.rs`, the `two_next_*` rows; enumerate, windows and loop/match forms too).
    // The scan is gone from all seven: the ENTRANCE is now a seam question —
    // `local_defs::unique_value_call`, through `iterator_yield::next_call_receiver` /
    // the bridge's `acc_next_call_receiver`; the CharIndices iterator local goes through
    // `call_dest_hop` like every other call-dest hop. The lesson for the next entry
    // written under (d): "the local cannot be a parameter" answers the ENTRY-definition
    // question this list was built for, and says nothing about a SECOND BODY write —
    // a `(d)` entry must also say why the local has one write, or route the scan.
    // This detector no longer sees a block scan in any of them, and an entry whose site is
    // gone is exactly the stale claim the assertion below refuses; a first-call scan
    // re-added to any of them fires this test by file and line.
    // Trust: 2026-09-16 — SIX ENTRIES RETIRED, NOT WAIVED. `acc_trace_iter_to_into_iter_arg`,
    // `acc_trace_local_to_range_aggregate` (bridge) and `trace_local_to_slice_iter_call` (now
    // `trace_slice_iter_item`),
    // `trace_local_to_enumerated_slice`, `trace_local_to_range_aggregate_from`,
    // `trace_iter_to_into_iter_arg` (vcgen) each carried a `for block in blocks { if Call {
    // dest.local == local } .. }` fallback that took the FIRST call writing the local and
    // asked nothing about its other writes — so a call-dest iterator reseated by `r = ..`
    // or through `&mut r` traced to its first constructor (five kernel-certified false
    // bounds proofs on real MIR; `tests/escaped_local_seam_realmir.rs`, the `reseated call
    // destination` rows). The scan is gone from all six: the hop is now a seam question —
    // `local_defs::unique_value_call`, and in vcgen (`iterator_yield::call_dest_hop`) its
    // origin twin `unique_initializing_call` under the `iter_mut_borrows_only_feed_next`
    // conduit gate; the bridge (`acc_call_dest_hop`) asks the value question only. Both
    // refuse every second write channel; the origin twin readmits exactly the alias, and
    // only under the gate.
    // This detector no longer sees a block scan in any of them, and an entry whose site is
    // gone is exactly the stale claim the assertion below refuses.
    (
        "trust-ir-bridge/src/lower.rs::find_checked_op_def",
        "(c)+(d) Split out of `resolve_checked_result_through_dominating_overflow_assert` by \
         e51f0f01d0 so `FunctionScanMemo` answers it once per tuple local; it returns the FIRST \
         `_t = CheckedBinaryOp(op, a, b)` in block order. (d) the key is a `CheckedBinaryOp` \
         tuple temp, which rustc mints fresh and never makes a parameter. (c) its one consumer \
         is reached only through `reconstruct_native_own_block_defs`'s \
         `memo.operand_value_is_stable(_t.0)` arm, i.e. `local_value_is_stable(_t)`: a \
         PARAMETER must have ZERO body stores, so one with this definition never gets here, \
         and any other local at most ONE store, counting `Call` destinations and projected \
         stores. So the definition found is the tuple's only value, and a second \
         `CheckedBinaryOp` into the same temp fails the gate first.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::resolve_bool_comparison_def",
        "(a) The single-assignment budget is ANDed with `local_defs::holds_one_value(func, \
         local)` on the same line, and the second conjunct is the entry definition. The vcgen \
         twin of this resolver — `guards::latest_same_block_bool_definition` — is W7.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::step_by_unique_block_def",
        "(c) BLOCK SCAN ONLY, by design: it takes `&[TrustBlock]` and has no `arg_count`, so it \
         cannot ask. All three consumers carry the question. The two StepBy tracers require \
         `step_by_producer_precedes` — same-block program order, or `step_by_block_dominates` \
         across blocks — so the resolved definition runs before every consumer execution and the \
         entry value cannot reach it; `step_by_cfg_successors` omits unwind edges, which makes a \
         cleanup-region consumer UNREACHABLE and the dominance query `false`, so that channel \
         fails closed rather than open. The third (the eq-model unit-variant classifier at \
         lower.rs) has no dominance check and calls `local_defs::is_parameter_of` explicitly. A \
         FOURTH consumer would have to add one of the two.",
    ),
    (
        "trust-vcgen/src/contracts.rs::exact_slice_raw_metadata_pair",
        "(b) Both fresh locals it resolves are required NON-argument (`pointer.local <= \
         func.body.arg_count` and `length.local <= func.body.arg_count` both return `None`), and \
         `collection_local` is matched as a READ (`source.local != collection_local`), never \
         scanned for its definitions.",
    ),
    (
        "trust-vcgen/src/contracts.rs::exact_terminal_mutable_alias_reborrow_return",
        "(b) `temporary.local <= func.body.arg_count` returns `None`; `alias_local` is matched as \
         the borrowed place of an exact four-statement return shape, not resolved from a \
         definition scan.",
    ),
    // Trust: 2026-10-11 (CL-FOLD-LOCALDEF-1) — TWO ENTRIES RETIRED, NOT WAIVED.
    // `alloc_vcs.rs::local_def` and `local_def_call_key` were classified "(a)" because
    // they asked `local_defs::has_one_explicit_def` before taking the first block-scanned
    // definition. That reason was TRUE AND INSUFFICIENT: it is the COUNTING question,
    // which counts neither a projected store nor a `&mut` alias, and both resolvers'
    // answers are INLINED. `let mut r = 0u8..4; r.end = 200; r.sum::<u8>()` (and the
    // `&mut` callee, `mem::swap`, store-through and closure-capture twins, a `v[r]` slice
    // row, a literal `Duration`) was PROVED and kernel-certified while the program
    // panics. The scan is gone from both: they now ask the seam's VALUE question
    // `local_defs::unique_value_modulo_whole_drops` (`unique_value_def` /
    // `unique_value_call` with a whole-local `Drop` read as the end of the value). This
    // detector no longer sees a block scan in either, and an entry whose site is gone is
    // exactly the stale claim the assertion below refuses.
    (
        "trust-vcgen/src/generate/callee_summaries.rs::callsite_unique_mut_borrow_target",
        "(a) The definition comes from `local_defs::unique_value_def`; the block scan in the body \
         only KILLS (a `Call` dest writing `temp`, any borrow of `temp`).",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::cast_source_const_lower",
        "(c) Keyed on a `Call` dest. Its one consumer requires `is_single_static_assignment` of \
         BOTH the cast source and the cast dest before consulting it, and that question counts \
         the entry definition — a parameter with a `Call`-dest definition holds two values and is \
         refused.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::cast_source_const_upper_nonneg",
        "(c) Same consumer gate (`is_single_static_assignment` on source and dest) at the \
         cast-bound site, and the same one on every hop of the return-summary chain.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::min_call_const_upper_bound",
        "(c) Reached only from `function_return_const_upper_bound`, whose `_0` trace asserts \
         `is_single_static_assignment` at every hop and once more at the leaf.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::ret_call_const_lower_bound",
        "(c) Reached only from `function_return_const_lower_bound`, with the same per-hop \
         `is_single_static_assignment` chain.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::find_field_probe",
        "(a) `pred_local` appears only as a READ (`referent.local == pred_local`, the borrowed \
         place of the probe receiver). Every hop it does resolve goes through \
         `local_defs::unique_value_def` plus `unwrap_receiver_local_is_pinned`.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::tier2a_switch_body_summary",
        "(d) `pred_local` is matched as the SUBJECT of the entry block's `Discriminant` read \
         (`src.local == pred_local`). No definition of `pred_local` is scanned or resolved.",
    ),
    // `container_len.rs::slice_iter_next_kind` was HERE — retired 2026-09-16 (second
    // round), see the note above `resolve_bool_comparison_def`.
    (
        "trust-vcgen/src/generate/float_range.rs::float_whole_local_defs",
        "(c) The def-SET collector with no parameter opinion — the `def-set-collector` detector \
         lists it in CLASSIFIED too, with each of its consumers and the parameter arm that \
         consumer writes itself.",
    ),
    (
        "trust-vcgen/src/generate/induction.rs::checked_sub_block",
        "(d) `t` is a `CheckedBinaryOp(Sub, ..)` destination — a compiler temp of the checked \
         arithmetic lowering, never a formal. The answer is a BLOCK ID fed to a dominance query, \
         not a value.",
    ),
    (
        "trust-vcgen/src/generate/induction.rs::countdown_companion_qual",
        "(b) Writes the parameter arm explicitly: `is_param_x` makes ANY non-division definition \
         of the companion a `return None`, and `!is_param_x && init.is_none()` requires a \
         non-parameter to have one.",
    ),
    (
        "trust-vcgen/src/generate/induction.rs::countdown_guard_true_edge_lower_bound",
        "(b)+(a) The companion `x` must have NO definition in the switch block, and each copy hop \
         is `is_single_static_assignment` + `local_defs::unique_value_def`; a cross-block copy \
         additionally requires its region to be x-definition-free.",
    ),
    (
        "trust-vcgen/src/generate/int_conversion.rs::int_try_from_def",
        "(a) `is_single_static_assignment(func, local)` is the FIRST thing it checks, at every \
         recursion depth, and that question counts the entry definition.",
    ),
    // `iterator_yield.rs::charindices_iter_string_root`, `::next_call_enumerated_slice`
    // and `::next_call_range_operands` were HERE — retired 2026-09-16 (second round), see
    // the note above `resolve_bool_comparison_def`.
    (
        "trust-vcgen/src/generate/loop_bounds.rs::accumulator_init_const",
        "(a) The scan identifies WHICH two definitions were seen; the VALUE budget is \
         `local_defs::value_count(func, acc).is_exactly(2)`. Classified above as a counter too, with \
         `param_accumulator_bound_still_refutes` as the row.",
    ),
    (
        "trust-vcgen/src/generate/loop_bounds.rs::checked_result_field0_consumer",
        "(d) `tuple_local` is matched as the SOURCE of a `Use(Copy(tuple.0))` read; what is \
         resolved is the CONSUMER local, and its uniqueness is this function's own `!= 1` bail. \
         No definition of `tuple_local` is read.",
    ),
    // Trust: 2026-09-19 — THREE SITES IN THIS FILE RETIRED, NOT WAIVED, and the fourth
    // is the entry below. `counter_local_compared_at` found the block defining the
    // compared copy with a `Statement::Assign`-only `find`; it now asks
    // `local_defs::unique_defining_block`, which grants an answer only when the local
    // holds ONE value on every channel and is not a parameter. `local_min_upper_bound`
    // and `bound_operand_upper_bound` each scanned for "exactly one defining `Call` and
    // no `Assign`"; both are now `local_defs::unique_value_call`, and
    // `bound_operand_upper_bound` — the one `min`-bound reader that had NO parameter
    // arm — is `local_min_upper_bound` on the operand's local. A `mut m` written once by
    // `m = x.min(5)` reaches a loop test with its unbounded ENTRY value on any path that
    // skips the call, and the trip count read off `m <= 5` UNDER-counts.
    // `loop_bounds_tests::{a_min_bounded_parameter_limit_is_refused,
    // a_cast_from_a_parameter_min_gets_no_bound}` are the rows, each paired with the
    // non-parameter twin that still answers. This detector no longer sees a block scan
    // in any of the three.
    (
        "trust-vcgen/src/generate/loop_bounds.rs::loop_instance_initializer",
        "(a) Refuses a PARAMETER outright (`local_defs::is_parameter`) before scanning. The scan \
         reads every channel through `Statement::local_write` / `Terminator::local_write` and \
         accepts exactly one `WholeNamed` write; any second whole write, `Partial` write or \
         `Unlocatable` write refuses, except a whole-place `Drop` of the instance in a block \
         OUTSIDE the loop, which ends its life and is not observed by an iteration. Its caller \
         (`next_loop_driver`) has already required `iterator_instance_is_fixed`: no write inside \
         the loop, and no alias but the `next` receiver.",
    ),
    (
        "trust-vcgen/src/generate/loop_bounds.rs::counter_init_stride_block",
        "(a) The counter's DEFINITIONS are `local_defs::value_defs` — the N-definition \
         generalization of `unique_value_def`, which refuses a PARAMETER outright (its entry \
         definition is in no block, so no list built from `body.blocks` could contain it) and \
         every channel beside `WholeNamed`. WHICH rvalue the self-add temp holds and WHICH \
         block it sits in are `unique_value_def` / `unique_defining_block`. The only \
         `.local != ctr` left is a READ check on the checked add's LHS operand — that the add \
         is the counter's OWN — and no definition of `ctr` is scanned. \
         `a_counter_written_through_the_partial_channel_is_refused` is the row for the \
         channel the replaced scan could not see.",
    ),
    // `loop_bounds.rs::next_call_to_array_operand` was HERE — retired 2026-09-16 (second
    // round), see the note above `resolve_bool_comparison_def`.
    (
        "trust-vcgen/src/generate/slice_conversion.rs::unique_whole_local_conversion_call",
        "(b) Rejects a PARAMETER outright in its first three lines, with the reason: its \
         conclusion SUPPRESSES a panic obligation, so an entry value the conversion `Call` does \
         not dominate would be a false proof.",
    ),
    (
        "trust-vcgen/src/generate/unwrap_panic.rs::unwrap_origin_call_def",
        "(c) The origin is PINNED by `unwrap_receiver_origin`'s `place_source_is_stable` chain \
         before this is called, which is what makes at most one whole-local store (statement or \
         `Call` dest) exist; and `unwrap_receiver_tag_term`, classified above, excludes a \
         parameter destination explicitly.",
    ),
    (
        "trust-vcgen/src/generate/witness_grounding.rs::f4_whole_local_defs",
        "(b) Rejects a PARAMETER outright, definitions or none, so the edge facts joined over the \
         visible definitions cover every value a read can see. Classified above as a def-set \
         collector too.",
    ),
    (
        "trust-vcgen/src/generate/witness_grounding.rs::leaf_push_blocks",
        "(d) `leaf` is matched as the TARGET of a `&mut` borrow used as a `Vec::push` receiver — \
         a read of `leaf`, not a definition of it. The answer is a list of block ids.",
    ),
    (
        "trust-vcgen/src/generate/witness_grounding.rs::resolve_forwarded_call_return_variant",
        "(d)+(a) `call_dest` must BE a `Call` destination (the function checks that first) and \
         must pass `place_source_is_stable`; a parameter is neither.",
    ),
    (
        "trust-vcgen/src/generate/vec_region.rs::build",
        "(b)+(a) `VecRegion::build` scans for the block holding the base's whole-local \
         definition ONLY on its `!is_param` arm (a parameter's region starts at entry and no \
         body definition is looked up), and only after \
         `local_defs::has_one_explicit_def(func, base)` has said there is exactly one. The \
         scan LOCATES that one definition's block; it resolves no value, and the region it \
         seeds is closed under every other write by `region_mutation_blocks`. W4 fix round 1 \
         (2026-09-25): classified when the integration targets were first run on VEC-INSERT.",
    ),
    (
        "trust-vcgen/src/generate/vec_len_invariant.rs::vec_len_never_changes",
        "(b) An OWNED base is admitted only when `base_kind` has said it is not a parameter \
         (`!local_defs::is_parameter`); a `&mut Vec` PARAMETER base must have ZERO body \
         writes (any statement or terminator writing it refuses), so its entry value is its \
         only one. The scan resolves no value: it counts the owned base's one whole write to \
         LOCATE the block where it takes effect, and refuses every other mention \
         (VEC-LEN-LOOP-1, 2026-10-07).",
    ),
    (
        "trust-vcgen/src/generate/vec_len_invariant.rs::establishers",
        "(a)+(d) The `len` destination is a `Call` destination asked through \
         `local_defs::is_single_static_assignment` (which charges a parameter its entry \
         definition); the `vec![x; n]` count local is asked through the same seam question \
         and, unless it is a parameter, through `local_defs::unique_defining_block`; the base \
         itself was classified by `vec_len_never_changes` (VEC-LEN-LOOP-1, 2026-10-07).",
    ),
    (
        "trust-vcgen/src/guards.rs::base_collection_step",
        "(c) One hop of a trace whose driver `base_collection_local_unique` asks \
         `local_defs::value_count(func, l).may_exceed(1)` for the START local AND for every hop before \
         following it, so a parameter with any body definition stops the trace.",
    ),
    (
        "trust-vcgen/src/guards.rs::call_block_defining_local",
        "(a) The scan finds the `Call` whose destination is the local, and runs only after \
         `local_defs::holds_one_value(func, local)` has answered yes. That seam question charges \
         a PARAMETER for its entry value and counts every other write channel, so the call it \
         finds is the local's one value. `call_defining_local` is its callee-and-argument view \
         (2026-09-29: split out so the ascii guard can version its set at the call's block).",
    ),
    (
        "trust-vcgen/src/guards.rs::bool_definition_reaching_step",
        "(a) FIXED ACROSS TWO ROUNDS — W7 then X2 (the scan moved here out of \
         `latest_same_block_bool_definition` on 2026-09-25, when it became a lookup of the \
         definition REACHING a read, `stmts[..end]`, rather than the block's latest one — the \
         shape that recursed forever on `c = c | t`). The SAME-BLOCK arm needs no check (that \
         definition precedes the read by program order). The CROSS-BLOCK \
         fallback's justification — \"a local with a single static definition dominates all its \
         uses (MIR never reads an uninitialized local)\" — is false of a parameter (initialized \
         at ENTRY) and false of a local written on a channel the scan does not enumerate. The \
         first round added a parameter bail and left the fallback's own \
         `Statement::Assign`-only uniqueness scan, which `p8` walked through; the whole \
         question is now `local_defs::unique_defining_block`. \
         `param_bool_reassigned_once_cross_block_guard_still_refutes` and \
         `call_dest_defined_bool_cross_block_guard_still_refutes` are the rows.",
    ),
    (
        "trust-vcgen/src/lib.rs::array_theory_local_uncached",
        "(a)+(d) Every element-store INDEX local — where a wrong value would name the wrong \
         element — must pass `index_local_stable`, which seeds its counter at \
         `usize::from(is_param)`. The ARRAY local's own definitions are asked of the seam: \
         `local_defs::value_count(..).is_at_most(1)` (2026-09-29, phase 2b) gives the \
         version chain's `v0` at most one definition — the construction a `[v; N]` seed \
         states as a constant array, or a parameter's entry value — so two constructions, \
         or a reassignment after element stores, decline the channel instead of equating \
         two arrays. The \
         Store/Select model engages only under `func_has_no_join`, the condition its module \
         banner states as the reason no stale array fact can leak across a control-flow \
         merge.",
    ),
    (
        "trust-vcgen/src/lib.rs::index_local_const",
        "(b) FIXED IN THIS CHANGE — W5. It agreed a set of identical constants and handed one \
         back; for a PARAMETER those are its SECOND..Nth values. The answer is INLINED into a \
         place NAME by `constant_array_index_segment`, which — unlike `array_theory_local` — does \
         not gate on the parameter-aware sibling COUNTER `index_local_stable`. \
         `param_reassigned_once_const_index_still_refutes` is the row.",
    ),
    (
        "trust-vcgen/src/loop_analysis.rs::find_init_value",
        "(b) FIXED IN THIS CHANGE. The pre-header `p = c` it returned is not what a parameter \
         holds on a path that skips it, and the answer is inlined as the CHC invariant's INITIAL \
         state (`chc::build_init_args`). Declining leaves that function's `init_<name>` fallback \
         — an unconstrained initial value, strictly harder to prove.",
    ),
    (
        "trust-vcgen/src/termination.rs::assignments_to_local_in_body",
        "(d) A complete SET of the assignment sites inside the given LOOP BLOCKS, handed to a \
         caller that requires exactly one and that it dominate the latch. No definition is \
         RESOLVED to a value here, and the ENTRY definition is not a statement in any block, so \
         it is not a member this set could be missing: the loop's INITIAL value is the \
         termination lane's separate question, carried as the unprimed state of the transition \
         relation (see `checked_chain_through_assert_pred`'s own note).",
    ),
    (
        "trust-vcgen/src/termination.rs::checked_chain_through_assert_pred",
        "(d) `tuple_local` is a `CheckedBinaryOp` destination — a compiler temp. Its operands are \
         separately required to be constants or locals that `local_ever_mutated` says are never \
         written (or that the caller vouches for by name).",
    ),
    (
        "trust-vcgen/src/sep_engine.rs::place_reads_param_pointee",
        "(b) Reported at `reference_param_is_confined` (the scan attributes it to its nested \
         helper). The local is a reference PARAMETER by construction (its caller requires \
         `local_defs::is_parameter` and `holds_one_value`), and nothing here resolves its \
         value: it refuses ANY assignment into a place rooted at it and any terminator \
         mention, and admits only pointee reads and disjoint shared borrows.",
    ),
];

/// The def QUESTIONS whose parameter arm a caller can get wrong by hand. A function
/// that calls one of these AND branches on `arg_count` is writing that arm itself.
const DEF_QUESTIONS: &[&str] = &[
    "local_is_never_written",
    "place_source_is_stable",
    "local_has_call_dest_write",
    "float_whole_local_defs",
    "local_write_count",
    "is_single_static_assignment",
];

/// The idioms the audit found. Each is a (name, predicate) over one source line.
///
/// A hit counts only inside a function that also SCANS DEFINITIONS (see
/// [`scans_definitions`]) — an unrelated counter (`pred_count` over CFG edges, a
/// recursion depth, a worklist index) is not this class and must not be listed. The
/// counter's NAME is deliberately NOT filtered: `writes += 1` is the spelling that
/// escaped the first cut.
fn tally_idioms() -> Vec<(&'static str, fn(&str) -> bool)> {
    vec![
        ("def-tally-increment", |l: &str| {
            let l = l.trim();
            l.ends_with("+= 1;") || l.ends_with("+= 2;") || l.ends_with("+= 1")
        }),
        // Trust: 2026-11-09 (VCGEN-SEAM-PERF-REDS-1) — PERF-471 moved both of
        // `assert_refutation`'s classified tallies behind a dense per-local counter
        // (`LocalCounter`), so the `+= 1` now sits in the counter's own `inc`, a function
        // that scans no definitions, and the two CLASSIFIED entries lost their site while
        // both tallies were still there. The method spelling is the same idiom.
        ("def-tally-counter-method", |l: &str| l.contains(".inc(")),
        // Trust: 2026-11-10 (VCGEN-NINE-REDS-20261110) — `seen_` is the same flag.
        // Wave 529 turned `panic_calls::range_bound_unchanged_until_call`'s
        // `.take(2).count()` into `terminator_reads += 1`, which the increment detector
        // flagged; de077b9c36 (PERF-COMPILER-VCGEN-542..546) respelled the same count as
        // `let mut seen_terminator_read = false;`, which only this prefix missed. The
        // site is now CLASSIFIED with what it counts.
        ("saw-flag-over-defs", |l: &str| {
            let l = l.trim();
            (l.starts_with("let mut saw_") || l.starts_with("let mut seen_"))
                && l.ends_with("= false;")
        }),
        ("def-set-collector", |l: &str| {
            let name = match owning_fn_name_of_header(l) {
                Some(n) => n,
                None => return false,
            };
            name.contains("whole_local") || name.ends_with("_local_defs")
        }),
    ]
}

/// The function name a `fn` HEADER line declares, if the line is one.
fn owning_fn_name_of_header(line: &str) -> Option<String> {
    ["pub(crate) fn ", "pub(super) fn ", "pub fn ", "fn ", "async fn "]
        .iter()
        .find_map(|kw| line.trim_start().strip_prefix(kw))
        .map(|rest| rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect())
        .filter(|n: &String| !n.is_empty())
}

/// The `[start, end)` line range of the function containing `hit`, and its name.
/// Boundaries are the outermost `fn` headers, found by the item's indentation.
fn owning_fn(lines: &[&str], hit: usize) -> (String, usize, usize) {
    let is_fn = |t: &str| {
        ["pub(crate) fn ", "pub(super) fn ", "pub fn ", "fn ", "async fn "]
            .iter()
            .find_map(|kw| t.trim_start().strip_prefix(kw))
            .map(|rest| {
                rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect::<String>()
            })
            .filter(|n| !n.is_empty())
    };
    let mut start = 0usize;
    let mut name = "<file scope>".to_string();
    for i in (0..=hit).rev() {
        if let Some(n) = is_fn(lines[i]) {
            name = n;
            start = i;
            break;
        }
    }
    let end =
        ((start + 1)..lines.len()).find(|i| is_fn(lines[*i]).is_some()).unwrap_or(lines.len());
    (name, start, end)
}

/// True iff the given source range reads a local's DEFINITION SITES — the only place
/// this lint is about.
fn scans_definitions(lines: &[&str], start: usize, end: usize) -> bool {
    lines[start..end].iter().any(|l| {
        l.contains("Statement::Assign")
            || l.contains("place.local ==")
            || l.contains("dest.local ==")
            || l.contains("d.local ==")
    })
}

/// The `fn` HEADER starting at `start`, joined onto one line: everything up to and
/// including the first `{`. A signature that spans several lines (most of them do) is
/// one string here, so the formals and the return type can be read off it.
fn fn_header(lines: &[&str], start: usize, end: usize) -> String {
    let mut header = String::new();
    for line in &lines[start..end.min(start + 16)] {
        header.push_str(line.trim());
        header.push(' ');
        if line.contains('{') {
            break;
        }
    }
    header
}

/// The names of the `usize`-typed FORMALS a header declares — the candidates for "the
/// local this function is asked about". Reads only the parameter list (everything
/// before the first `{`), so a `usize` inside the return type is not one.
fn usize_formals(header: &str) -> Vec<String> {
    let params = header.split('{').next().unwrap_or(header);
    let bytes: Vec<char> = params.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == ':' {
            // the identifier immediately before the colon
            let mut j = i;
            while j > 0 && bytes[j - 1].is_whitespace() {
                j -= 1;
            }
            let e = j;
            while j > 0 && (bytes[j - 1].is_alphanumeric() || bytes[j - 1] == '_') {
                j -= 1;
            }
            let name: String = bytes[j..e].iter().collect();
            // the type that follows, up to the next `,` at depth 0
            let mut k = i + 1;
            while k < bytes.len() && bytes[k].is_whitespace() {
                k += 1;
            }
            let mut ty = String::new();
            let mut depth = 0i32;
            while k < bytes.len() {
                match bytes[k] {
                    '<' | '(' | '[' => depth += 1,
                    '>' | ')' | ']' => {
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                    }
                    ',' if depth == 0 => break,
                    _ => {}
                }
                ty.push(bytes[k]);
                k += 1;
            }
            if ty.trim() == "usize" && !name.is_empty() {
                out.push(name);
            }
            i = k;
            continue;
        }
        i += 1;
    }
    out
}

/// The declared RETURN type of a header, `"()"` when there is none.
fn return_type(header: &str) -> String {
    let Some(arrow) = header.find("->") else { return "()".to_string() };
    let rest = &header[arrow + 2..];
    let brace = rest.find('{').unwrap_or(rest.len());
    rest[..brace].trim().to_string()
}

/// Every identifier `X` appearing as `<something>.local == X` / `!= X` in the source
/// range — the locals a definition scan is KEYED ON. A literal or an expression on the
/// right yields nothing.
fn keyed_locals(lines: &[&str], start: usize, end: usize) -> Vec<String> {
    let mut out = Vec::new();
    for line in &lines[start..end] {
        if line.trim_start().starts_with("//") {
            continue;
        }
        for op in [".local ==", ".local !="] {
            let mut from = 0usize;
            while let Some(at) = line[from..].find(op) {
                let after = from + at + op.len();
                let ident: String = line[after..]
                    .chars()
                    .skip_while(|c| c.is_whitespace())
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !ident.is_empty() && !ident.chars().next().is_some_and(|c| c.is_ascii_digit()) {
                    out.push(ident);
                }
                from = after;
            }
        }
    }
    out
}

/// `true` for every line inside a `#[cfg(test)] mod … { … }` region, by brace depth.
/// The file-name filter above catches `tests.rs` and `tests/`; this catches the
/// in-file test modules the big producers keep at the bottom.
fn test_module_mask(lines: &[&str]) -> Vec<bool> {
    let mut mask = vec![false; lines.len()];
    let mut i = 0usize;
    while i < lines.len() {
        if lines[i].trim() == "#[cfg(test)]" {
            let mut j = i + 1;
            while j < lines.len() && lines[j].trim_start().starts_with("#[") {
                j += 1;
            }
            if j < lines.len() && lines[j].trim_start().starts_with("mod ") {
                let (mut depth, mut started, mut k) = (0i32, false, j);
                while k < lines.len() {
                    depth += lines[k].matches('{').count() as i32;
                    depth -= lines[k].matches('}').count() as i32;
                    started |= lines[k].contains('{');
                    mask[k] = true;
                    if started && depth <= 0 {
                        break;
                    }
                    k += 1;
                }
                i = k + 1;
                continue;
            }
        }
        i += 1;
    }
    mask
}

fn rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            rs_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}

/// `crates/`-relative path, the spelling the allowlist uses.
fn rel(p: &Path) -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("crates/");
    p.strip_prefix(root).unwrap_or(p).to_string_lossy().replace('\\', "/")
}

#[test]
fn every_definition_tally_outside_the_seam_is_classified() {
    let idioms = tally_idioms();
    let mut files = Vec::new();
    for dir in scanned_crates() {
        rs_files(&dir, &mut files);
    }
    assert!(files.len() > 50, "the source walk found almost nothing: {} files", files.len());

    let mut found: Vec<(String, String, usize, &str)> = Vec::new();
    for f in &files {
        let path = rel(f);
        if SEAM_FILES.contains(&path.as_str()) {
            continue;
        }
        // Test modules state expectations about the predicates; they do not decide a
        // verdict, and their tallies are the fixtures' own.
        if path.contains("tests.rs") || path.contains("/tests/") || path.contains("_tests/") {
            continue;
        }
        let text = std::fs::read_to_string(f).expect("source must be readable");
        let lines: Vec<&str> = text.lines().collect();
        let in_test_mod = test_module_mask(&lines);
        for (i, line) in lines.iter().enumerate() {
            // A `#[cfg(test)] mod` states expectations about the predicates and builds
            // fixtures; it decides no verdict, and its counters are the fixtures' own.
            if in_test_mod[i] || line.trim_start().starts_with("//") {
                continue;
            }
            for (name, pred) in &idioms {
                if !pred(line) {
                    continue;
                }
                let (sym, start, end) = owning_fn(&lines, i);
                if scans_definitions(&lines, start, end) {
                    found.push((path.clone(), sym, i + 1, name));
                }
            }
            if !line.trim_start().starts_with("//")
                && DEF_QUESTIONS.iter().any(|q| line.contains(&format!("{q}(")))
            {
                let (sym, start, end) = owning_fn(&lines, i);
                if lines[start..end].iter().any(|l| l.contains("arg_count")) {
                    found.push((path.clone(), sym, i + 1, &"parameter-arm-def-question"));
                }
            }
        }
    }

    let classified: Vec<String> = CLASSIFIED.iter().map(|(k, _)| (*k).to_string()).collect();
    let mut unclassified: Vec<String> = found
        .iter()
        .map(|(p, sym, line, idiom)| (format!("{p}::{sym}"), *line, *idiom))
        .filter(|(key, _, _)| !classified.contains(key))
        .map(|(key, line, idiom)| format!("{key} (line {line}, {idiom})"))
        .collect();
    unclassified.sort();
    unclassified.dedup();
    assert!(
        unclassified.is_empty(),
        "a definition tally outside `local_defs` is not in this file's CLASSIFIED list.\n\
         For EACH: can the local be a PARAMETER (whose definition is at ENTRY and is not \
         in `body.blocks`)? If it can, route the count through `local_defs`; if it \
         cannot, or the site is deliberately stricter, add it to CLASSIFIED with the \
         reason.\n{unclassified:#?}"
    );

    // The other direction: an allowlist entry whose site is gone is a stale claim.
    let keys: Vec<String> = found.iter().map(|(p, sym, _, _)| format!("{p}::{sym}")).collect();
    let stale: Vec<&str> =
        CLASSIFIED.iter().map(|(k, _)| *k).filter(|k| !keys.contains(&(*k).to_string())).collect();
    assert!(stale.is_empty(), "CLASSIFIED entries whose site no longer exists: {stale:#?}");
}

/// THE RESOLVER HALF OF THE RATCHET.
///
/// A resolver takes a LOCAL, scans `blocks` for that local's definition, and hands back
/// something derived from it — a constant, an `Rvalue`, a `Formula`, a source `Place`.
/// It contains no counter, so none of the three detectors above sees it, and it is the
/// more dangerous half: the answer is INLINED (into a place name, into a SwitchInt edge
/// fact), so version renaming cannot rebind a wrong one afterwards. Four site-by-site
/// audits of the counter family missed `lib.rs::index_local_const` and
/// `guards.rs::latest_same_block_bool_definition`, both of which were live
/// kernel-certified false proofs (`entry_def_structural.rs` § W5/W7).
///
/// The shape, deliberately structural rather than name-based (`index_local_const` is
/// not spelled like a resolver, and `local_def` is not spelled like anything):
///   * a `usize` FORMAL — the local being asked about;
///   * `<place>.local == <that formal>` somewhere in the body — the definition scan is
///     KEYED on it;
///   * the body mentions `blocks` — it is a whole-body scan, not a single-statement
///     destructuring;
///   * the return type is `Option<…>` / `Vec<…>` / a reference — it HANDS BACK a value.
///     A `bool` or a `usize` is the counting family, which the detectors above own.
#[test]
fn every_value_resolver_outside_the_seam_is_classified() {
    let mut files = Vec::new();
    for dir in scanned_crates() {
        rs_files(&dir, &mut files);
    }
    assert!(files.len() > 50, "the source walk found almost nothing: {} files", files.len());

    let mut found: Vec<(String, String, usize)> = Vec::new();
    for f in &files {
        let path = rel(f);
        // The seam owns both halves of the question — the counting one and this one.
        if SEAM_FILES.contains(&path.as_str()) {
            continue;
        }
        if path.contains("tests.rs") || path.contains("/tests/") || path.contains("_tests/") {
            continue;
        }
        let text = std::fs::read_to_string(f).expect("source must be readable");
        let lines: Vec<&str> = text.lines().collect();
        let in_test_mod = test_module_mask(&lines);
        for (i, line) in lines.iter().enumerate() {
            if in_test_mod[i] || line.trim_start().starts_with("//") {
                continue;
            }
            let Some(declared) = owning_fn_name_of_header(line) else { continue };
            let (sym, start, end) = owning_fn(&lines, i);
            if sym != declared {
                continue;
            }
            let header = fn_header(&lines, start, end);
            let formals = usize_formals(&header);
            if formals.is_empty() {
                continue;
            }
            let ret = return_type(&header);
            if !(ret.starts_with("Option<") || ret.starts_with("Vec<") || ret.starts_with('&')) {
                continue;
            }
            // A whole-body scan, not a single-statement destructuring. COMMENTS are
            // excluded: the next item's doc comment sits inside this function's line
            // range, and `loop_analysis::detect_step` — a pure `match` on one `Rvalue`
            // — was attributed a `blocks` mention that belonged to the doc of the
            // function after it.
            let scans_blocks = lines[start..end]
                .iter()
                .any(|l| !l.trim_start().starts_with("//") && l.contains("blocks"));
            if !scans_blocks {
                continue;
            }
            let keyed = keyed_locals(&lines, start, end);
            if !keyed.iter().any(|k| formals.contains(k)) {
                continue;
            }
            found.push((path.clone(), sym, i + 1));
        }
    }

    let classified: Vec<String> = RESOLVERS.iter().map(|(k, _)| (*k).to_string()).collect();
    let mut unclassified: Vec<String> = found
        .iter()
        .map(|(p, sym, line)| (format!("{p}::{sym}"), *line))
        .filter(|(key, _)| !classified.contains(key))
        .map(|(key, line)| format!("{key} (line {line})"))
        .collect();
    unclassified.sort();
    unclassified.dedup();
    assert!(
        unclassified.is_empty(),
        "a per-local VALUE RESOLVER outside `local_defs` is not in this file's RESOLVERS \
         list.\nFor EACH: can the local be a PARAMETER (defined at ENTRY, never in \
         `body.blocks`)? If it can, the block-scanned definition is that parameter's \
         SECOND value — route the question through `local_defs`, exclude parameters, or \
         show that every CONSUMER already does. Then add it to RESOLVERS with which of \
         those it is.\n{unclassified:#?}"
    );

    // The other direction: an allowlist entry whose site is gone is a stale claim.
    let keys: Vec<String> = found.iter().map(|(p, sym, _)| format!("{p}::{sym}")).collect();
    let stale: Vec<&str> =
        RESOLVERS.iter().map(|(k, _)| *k).filter(|k| !keys.contains(&(*k).to_string())).collect();
    assert!(stale.is_empty(), "RESOLVERS entries whose site no longer exists: {stale:#?}");
}

/// THE ALLOWLIST CONTRACT, shared by the three reason-bearing lists in this file
/// ([`CLASSIFIED`], [`RESOLVERS`], [`CHANNEL_SUBSETS`]): every entry carries a real
/// reason, no two entries claim one site, and every key names a site that still exists
/// in the source. Same rule the pin-waiver and frozen-file gates already run — an
/// allowlist entry may not outlive its subject, and may not be added as a bare key.
///
/// It is the independent half of each list's detector row. A detector row refuses an
/// entry the DETECTOR no longer fires on, which couples staleness to that detector's
/// shape test; this reads the source FILE directly, so a renamed or deleted function
/// fails here whatever the shape test does, and it is what makes "an entry must carry a
/// reason" enforceable rather than a convention — measured on the tree this landed on: a
/// blanked reason and a duplicated key each passed every row the file had. It weakens
/// nothing: it only adds obligations to entries already in the lists.
///
/// `answer_classes`, when non-empty, is the set of prefixes one of which the reason must
/// OPEN with — the list's own enumerated answers — and what follows the prefix must
/// itself be a justification.
///
/// WHAT "A REAL REASON" IS, structurally (2026-10-01; the first cut used a 40-character
/// floor, a magic number a padded `(a) ` plus filler passed): the justification is a
/// SENTENCE — at least two words, ending in sentence punctuation ([`is_sentence`]). A
/// bare class tag (`(a)`), a key repeated as its own reason or a run of filler is not
/// one. No structural rule can tell a true reason from a false one; that is the
/// reviewer's job, and this row's is to make sure there is a reason to review.
///
/// Each source file is read and scanned ONCE however many entries name it, so the cost
/// is linear in the lists plus the files they name.
fn allowlist_contract_defects(
    list_name: &str,
    list: &[(&str, &str)],
    answer_classes: &[&str],
) -> Vec<String> {
    use std::collections::{BTreeMap, BTreeSet};

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("crates/").to_path_buf();
    let mut defects: Vec<String> = Vec::new();
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    // `<crate-relative path>` -> the names of the non-test `fn`s it declares, or `None`
    // when the file cannot be read.
    let mut declared_fns: BTreeMap<&str, Option<BTreeSet<String>>> = BTreeMap::new();

    for &(key, reason) in list {
        if !seen.insert(key) {
            defects.push(format!(
                "{list_name} {key}: DUPLICATE key — two entries claim the same site"
            ));
        }

        // (1) The entry IS its reason. An allowlisting act with nothing written beside it
        // is the shape this contract exists to refuse.
        let reason = reason.trim();
        let justification = if answer_classes.is_empty() {
            Some(reason)
        } else {
            let class = answer_classes.iter().find(|class| reason.starts_with(*class));
            if class.is_none() {
                defects.push(format!(
                    "{list_name} {key}: the reason must OPEN with the answer class it claims, \
                     one of {answer_classes:?}. Got: {:?}",
                    reason.chars().take(48).collect::<String>()
                ));
            }
            class.map(|class| reason[class.len()..].trim())
        };
        if reason.is_empty() {
            defects.push(format!("{list_name} {key}: EMPTY reason — an entry here is its reason"));
        } else if let Some(justification) = justification
            && !is_sentence(justification)
        {
            defects.push(format!(
                "{list_name} {key}: the reason must JUSTIFY the entry in at least one sentence \
                 (two or more words, ending in sentence punctuation); a tag, a key or filler \
                 is not a reason. Got: {justification:?}"
            ));
        }

        // (2) The site must still exist, read straight from the file rather than from
        // whatever a detector happens to match this round.
        let Some((path, sym)) = key.split_once("::") else {
            defects
                .push(format!("{list_name} {key}: key is not `<crate-relative path>::<symbol>`"));
            continue;
        };
        if !path.ends_with(".rs") || !path.contains('/') {
            defects.push(format!("{list_name} {key}: `{path}` is not a crate-relative `.rs` path"));
            continue;
        }
        let fns = declared_fns.entry(path).or_insert_with(|| {
            let text = std::fs::read_to_string(root.join(path)).ok()?;
            let lines: Vec<&str> = text.lines().collect();
            let in_test_mod = test_module_mask(&lines);
            Some(
                lines
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !in_test_mod[*i])
                    .filter_map(|(_, l)| owning_fn_name_of_header(l))
                    .collect(),
            )
        });
        let Some(fns) = fns else {
            defects
                .push(format!("{list_name} {key}: `{path}` no longer exists — the entry is stale"));
            continue;
        };
        if !fns.contains(sym) {
            defects.push(format!(
                "{list_name} {key}: `{path}` declares no non-test `fn {sym}` — the entry has \
                 outlived its subject. An allowlist entry is deleted WITH the site it \
                 allowlisted."
            ));
        }
    }
    defects
}

/// Is `text` a SENTENCE — at least two words (runs containing a letter), ending in
/// sentence punctuation (a closing quote, backtick or parenthesis may follow it)?
fn is_sentence(text: &str) -> bool {
    let text = text.trim();
    let words = text.split_whitespace().filter(|w| w.chars().any(char::is_alphabetic)).count();
    words >= 2 && text.trim_end_matches([')', '`', '"', '\'']).ends_with(['.', '!', '?'])
}

/// [`is_sentence`] refuses exactly the shapes the contract names: a bare class tag, a
/// key, filler and a single word; and admits a short real justification.
#[test]
fn a_reason_is_a_sentence_not_a_length() {
    for not_a_reason in [
        "",
        "(a)",
        "x".repeat(36).as_str(),
        "trust-vcgen/src/guards.rs::value_local_is_unstable",
        "Sound.",
        "see the doc comment",
    ] {
        assert!(!is_sentence(not_a_reason), "{not_a_reason:?} is not a reason");
    }
    for reason in ["Keyed on a `Call` dest.", "It cannot be a parameter (see `value_count`)."] {
        assert!(is_sentence(reason), "{reason:?} is a reason");
    }
}

/// The [`RESOLVERS`] allowlist meets [`allowlist_contract_defects`], and every reason
/// OPENS with the answer class (a)-(d) it claims.
#[test]
fn every_resolver_entry_carries_a_reason_and_a_live_site() {
    // Emptying the list is the other way to defeat this row: with no entries, every
    // per-entry obligation below is vacuous. (An emptied list with live resolver sites
    // also fails `every_value_resolver_outside_the_seam_is_classified`, which is the
    // row that knows how many entries there should be; no floor is kept here.)
    assert!(!RESOLVERS.is_empty(), "RESOLVERS is empty, so this row would be vacuous");
    let defects = allowlist_contract_defects("RESOLVERS", RESOLVERS, &["(a)", "(b)", "(c)", "(d)"]);
    assert!(
        defects.is_empty(),
        "RESOLVERS entries that do not meet the allowlist contract.\nAn entry in that list \
         is an ALLOWLISTING ACT: it is what stops the resolver detector failing on its \
         site, so it must carry the reason the scan is sound — naming which of (a)-(d) it \
         is — and it must name a site that still exists.\n{defects:#?}"
    );
}

/// The two other reason-bearing allowlists meet the same contract. Their reasons are
/// free-form classifications (neither list enumerates answer classes), so only the
/// reason, uniqueness and live-site obligations apply.
#[test]
fn every_classified_and_channel_subset_entry_carries_a_reason_and_a_live_site() {
    let mut defects = Vec::new();
    for (list_name, list) in [("CLASSIFIED", CLASSIFIED), ("CHANNEL_SUBSETS", CHANNEL_SUBSETS)] {
        assert!(!list.is_empty(), "{list_name} is empty, so this row would be vacuous");
        defects.extend(allowlist_contract_defects(list_name, list, &[]));
    }
    assert!(
        defects.is_empty(),
        "allowlist entries that do not meet the allowlist contract (each entry is an \
         ALLOWLISTING ACT: it must carry its reason and name a site that still \
         exists).\n{defects:#?}"
    );
}

/// Per-local definition scans that enumerate the `Statement::Assign` channel and NOT
/// the `Call`-DESTINATION channel, each with the reason the omission is not a value
/// question. Keyed and read exactly like [`CLASSIFIED`].
///
/// THE SCOPE OF THIS DETECTOR, stated plainly. `trust_types::LocalWrite` has six
/// channels; this lint polices ONE of the omissions — `Assign` without the `Call`
/// destination. That is the omission with a measured cost: `pmod` (`local_defs`'s
/// resolver) and `p8` (`guards`'s cross-block uniqueness scan) were both live
/// kernel-certified false proofs of exactly this shape, and `guards.rs`'s scan was
/// already allowlisted with a reason that only covered `Assign`. The rarer channels
/// (`SetDiscriminant`, `Deinit`, `Drop`, the pointer-write sentinels, and the mutable
/// ALIAS) are NOT policed here; what covers them is the compile-time anchor rather
/// than a lint — `Statement::local_write`/`Terminator::local_write` are wildcard-free
/// matches in the crate that owns those `#[non_exhaustive]` enums, and every question
/// in `local_defs` is a wildcard-free match over `LocalWrite`, so a channel cannot be
/// added without every seam question failing to compile. A hand-rolled scan OUTSIDE
/// the seam that omits one of the rare channels is caught by this test only if it also
/// omits the `Call` destination.
const CHANNEL_SUBSETS: &[(&str, &str)] = &[
    (
        "trust-vcgen/src/guards.rs::clean_variant_switch_target",
        "Not a definition scan of `local`: it requires the block's ONLY value statement to \
         be the discriminant read of `local`, a `Call` destination written by the block's \
         sole predecessor, and refuses any other statement but a storage marker or `Nop` \
         naming neither `local` nor the temp (TINV-21). The `Assign` it names is the \
         discriminant TEMP, defined and switched on within the same block.",
    ),
    (
        "trust-vcgen/src/generate/dominating_facts.rs::copy_source",
        "Not a definition scan: the one statement it reads is the write the statement \
         version oracle NAMES as the one the read sees (`StmtVersionCtx::value_id_at` \
         answering `ValueId::Def { block, stmt }`). A `Call`-destination write is a \
         TERMINATOR write, which the oracle names `ValueId::Def { stmt: u32::MAX }`, and \
         `stmts.get(u32::MAX)` is `None`, so a `Call` dest is never taken for a copy; every \
         other channel moves the `ValueId` the copy is checked against.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::bool_local_has_definition",
        "Answers \"would `guard_to_formula` inline this bool?\". Blindness to a `Call` dest \
         makes it answer `false` where the truth is `true`, and `false` is the arm that \
         DECLINES to inline and reproduces the guard as the bare local — the safe direction.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::moved_value_local",
        "Gated on its own `local_write_count(local, all_blocks) != 1` bail on the FIRST line, \
         and that tally counts `Call` destinations. A local with an `Assign` and a `Call` dest \
         scores 2 and the hop is refused before this scan runs.",
    ),
    (
        "trust-ir-bridge/src/lower.rs::native_blocks_local_reseatable",
        "Asks only the ALIAS question (`Rvalue::Ref { mutable: true }` / `AddressOf` of \
         `local`). A `Call` destination is not a borrow, so the channel is irrelevant to what \
         it decides; it exists to ADD a fail-closed condition to a resolver, never to license \
         one.",
    ),
    (
        "trust-vcgen/src/contracts.rs::exact_fixed_array_slice_metadata_pair",
        "Matches an EXACT two-statement shape at a given `(block_index, statement_index)` and \
         then requires the view temp to occur nowhere else in the function. It reads one \
         named statement, not the definition set of a local.",
    ),
    (
        "trust-vcgen/src/contracts.rs::exact_slice_raw_metadata_pair",
        "Both fresh locals it resolves are required NON-argument and are matched as an exact \
         statement shape; `collection_local` appears only as a READ. No local's definition \
         SET is consulted, so no channel is enumerated.",
    ),
    (
        "trust-vcgen/src/contracts.rs::exact_terminal_mutable_alias_reborrow_return",
        "An exact four-statement return shape; `alias_local` is the borrowed place of that \
         shape, never scanned for definitions.",
    ),
    (
        "trust-vcgen/src/generate/bmc_reduction.rs::const_init_is_outside_loop",
        "Asks whether a CONSTANT initializer sits on the loop cycle. A `Call` destination is \
         not a constant initializer, so it cannot be one of the definitions this question is \
         about; the accumulator's value budget is `local_defs::value_count(func, acc).is_exactly(2)` at \
         the caller, which does count `Call` dests.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::local_mut_escapes",
        "The ALIAS question (`&mut local` / `&raw local`), the `LocalWrite::Escape` channel. A \
         `Call` destination is not a borrow. Its answer is used as an EXTRA fail-closed \
         conjunct beside `local_defs::value_count`, never on its own.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::probe_result_reaches_return",
        "A straight-line CFG shape check (`dest_local` flows into `_0` and reaches the single \
         `Return` within 8 hops). It reads the statements on that path for storage \
         annotations; it does not count or resolve definitions of any local.",
    ),
    (
        "trust-vcgen/src/generate/callee_summaries.rs::tier2a_switch_body_summary",
        "`pred_local` is matched as the SUBJECT of the entry block's `Discriminant` read. No \
         definition of it is scanned.",
    ),
    (
        "trust-vcgen/src/generate/container_len.rs::local_mutation_blocks",
        "The `Call`-dest channel IS enumerated — by `local_write_blocks`, whose result this \
         function starts from; the scan visible here adds only the ALIAS channel on top. Its \
         own doc says so (\"whole/projected/call-dest store OR take a `&mut`/raw borrow\").",
    ),
    (
        "trust-vcgen/src/generate/block_defs.rs::v2_slice_metadata_root_rebinds_between",
        "4006bc923f split `v2_slice_metadata_root_can_rebind` in two. The ALIAS half \
         (`&mut`/raw borrow of the pointer local) stays whole-function. The DIRECT-WRITE half \
         reads only the statements that can run between the length read and the access: the \
         assert block's tail after `len_stmt` and the use block's prefix before the access. \
         The caller has already established a sole-entry `BoundsCheck` success edge between \
         the two. Those are STATEMENTS, and the one terminator between them is that \
         `BoundsCheck` assert. A `Call` destination is a terminator write, so it cannot occur \
         in the interval. The loop re-seat the old whole-function scan refused runs in a \
         different execution.",
    ),
    (
        "trust-vcgen/src/generate/induction.rs::checked_sub_block",
        "`t` is a `CheckedBinaryOp(Sub, ..)` destination — a compiler temp of the checked \
         arithmetic lowering, which is an `Assign` by construction and never a `Call` dest. \
         The answer is a BLOCK ID fed to a dominance query, not a value.",
    ),
    (
        "trust-vcgen/src/generate/induction.rs::cursor_written_since_guard",
        "Asks whether the cursor was written between the guard and the decrement. The \
         cross-block half is `local_write_blocks`, which counts `Call` dests; the in-block \
         half scans the statements BEFORE the `CheckedSub` of the same block, and a `Call` \
         is a terminator, so none can sit there. A missed write only withholds a fact.",
    ),
    (
        "trust-vcgen/src/generate/iterator_yield.rs::local_has_projected_write",
        "Asks for the channels `value_count` does NOT see — projected stores, \
         `SetDiscriminant`, `Deinit` — and is ANDed with it. `Call` dests are the counter's \
         job, not this predicate's; its own doc states the division.",
    ),
    (
        "trust-vcgen/src/generate/loop_bounds.rs::guard_operand_reads_current",
        "Scans ONE block, the guard, which ends in the `SwitchInt` under test: no `Call` \
         terminator can write the cursor between the comparison and the switch. The copy \
         chain it follows is positional (copies made in that block before the compare), so \
         a `Call`-dest copy source declines (`false` withholds the guard fact).",
    ),
    (
        "trust-vcgen/src/generate/loop_bounds.rs::checked_result_field0_consumer",
        "`tuple_local` is matched as the SOURCE of a `Use(Copy(tuple.0))` read; what is \
         resolved is the CONSUMER local, whose uniqueness is this function's own \
         second-distinct-consumer bail. No definition of `tuple_local` is read.",
    ),
    (
        "trust-vcgen/src/guards.rs::local_is_mutably_borrowed",
        "The ALIAS question again — `Rvalue::Ref { mutable: true }` / `AddressOf` of `local`. \
         A `Call` destination is not a borrow. Used to FAIL-CLOSE enum-payload routing, so \
         answering `true` less often is the only direction that could matter and the channel \
         cannot produce one.",
    ),
    (
        "trust-vcgen/src/guards.rs::operand_local_is_mut_borrow_of",
        "Asks what `borrow_temp`'s defining rvalue IS (`&mut target`). A `Call` destination \
         has no `Rvalue` at all, so it can never be the mutable borrow this recognizes.",
    ),
    (
        "trust-vcgen/src/guards.rs::pointer_local_reseatable",
        "The ALIAS question for a reference or raw-pointer local: is its whole place \
         `&mut`/`&raw` borrowed, so a write through that alias can reseat it unseen by \
         `value_count`. A `Call` destination is a definition, which `value_count` (checked \
         beside it at every hop) already counts; it is never a borrow. `true` ends the base \
         trace, so the channel could only make the answer fail-closed.",
    ),
    (
        "trust-vcgen/src/guards.rs::value_local_is_mut_borrowed",
        "The ALIAS question (`Rvalue::Ref { mutable: true }` / `AddressOf` of `local`), the \
         borrow-escape slice of `value_local_is_unstable`. A `Call` destination is not a \
         borrow, so the channel cannot produce a mutable alias; `true` withholds a derived \
         value bound.",
    ),
    (
        "trust-vcgen/src/lib.rs::local_storage_borrowed_anywhere",
        "Trust: 2026-09-17 (round A12, fixer) — not a definition scan at all: it asks whether \
         any statement TAKES THE ADDRESS of the local's own storage (`Rvalue::Ref` / \
         `Rvalue::AddressOf` whose place is not `Deref`-rooted). A `Call` DESTINATION WRITES \
         the local, it does not borrow it, and a callee cannot mint an alias of a local this \
         body never borrowed — a borrow exists in MIR only as an `Assign` rvalue, every other \
         channel carrying operands (values), never addresses. The reading is one-directional \
         and fail-closed: `true` makes the referent-fold walk treat a write of that local as \
         possibly rebinding a pointer-reached guard, and the walk's answer to a write it \
         cannot attribute is already `rebinds`.",
    ),
    (
        "trust-vcgen/src/lib.rs::local_is_never_written",
        "A statement-only never-written test whose every consumer ANDs it with a \
         `Call`-dest-aware question — `discharge::local_versions_collapse_to_bare` and \
         `caller_precondition_var_is_entry_stable` both add \"no `Call` dest\" explicitly, \
         and both are in CLASSIFIED with that reason.",
    ),
    (
        "trust-vcgen/src/termination.rs::assignments_to_local_in_body",
        "A complete SET of the ASSIGNMENT sites inside the given LOOP BLOCKS, handed to a \
         caller that requires exactly one and that it dominate the latch. The caller's \
         separate write-risk gates (`block_has_nonassign_write_risk`, `local_ever_mutated`) \
         carry the non-`Assign` channels.",
    ),
    (
        "trust-vcgen/src/termination.rs::checked_chain_through_assert_pred",
        "`tuple_local` is a `CheckedBinaryOp` destination — a compiler temp, an `Assign` by \
         construction. Its operands are separately required to be constants or locals that \
         `local_ever_mutated` says are never written.",
    ),
    (
        "trust-vcgen/src/typestate.rs::self_edge_preserves_value",
        "Asks whether a self-edge returns its INPUT UNCHANGED — `_0 = move _param`, or the \
         same variant rebuilt from verbatim field copies. Any operand it cannot see as a \
         verbatim copy makes it answer `false` (not preserved), which is the arm that \
         DECLINES the whole machine.",
    ),
    (
        "trust-vcgen/src/sep_engine.rs::box_copy_is_deref_only",
        "A USE census, not a definition set (D14 / review rounds 85-87, the box-root fences). It asks whether every MENTION of one local is a pointee read or another admitted use; every terminator mention — a `Call` destination included — refuses outright through `terminator_mentions_local_anywhere`, so the channel it does not enumerate as a definition is a refusal, not a blind spot. The single-value question is asked of `local_defs::holds_one_value` by its callers.",
    ),
    (
        "trust-vcgen/src/sep_engine.rs::place_is_through_box_temp",
        "A USE census, not a definition set (D14 / review rounds 85-87, the box-root fences). It asks whether every MENTION of one local is a pointee read or another admitted use; every terminator mention — a `Call` destination included — refuses outright through `terminator_mentions_local_anywhere`, so the channel it does not enumerate as a definition is a refusal, not a blind spot. The single-value question is asked of `local_defs::holds_one_value` by its callers.",
    ),
    (
        "trust-vcgen/src/sep_engine.rs::place_reads_param_pointee",
        "A USE census, not a definition set (D14 / review rounds 85-87, the box-root fences). It asks whether every MENTION of one local is a pointee read or another admitted use; every terminator mention — a `Call` destination included — refuses outright through `terminator_mentions_local_anywhere`, so the channel it does not enumerate as a definition is a refusal, not a blind spot. The single-value question is asked of `local_defs::holds_one_value` by its callers.",
    ),
];

/// THE CHANNEL-SUBSET HALF OF THE RATCHET.
///
/// A per-local definition scan that enumerates `Statement::Assign` and is blind to the
/// `Call` DESTINATION reads a local written by both as singly-defined. `pmod` and `p8`
/// (`tests/entry_def_structural.rs` § X1/X2) are the two live kernel-certified false
/// proofs that shape produced.
///
/// The shape, the same structural signal the resolver detector uses plus the channel
/// question:
///   * a `usize` FORMAL, and `<place>.local == <that formal>` in the body — the scan is
///     KEYED on a local;
///   * the body mentions `blocks` — a whole-body scan;
///   * the body mentions `Statement::Assign` — it enumerates the named-write channel;
///   * the body does NOT mention `Terminator::Call` and does NOT delegate to
///     `local_defs` — it is blind to the `Call`-destination channel and does not ask
///     the seam to cover it.
#[test]
fn every_channel_subset_scan_outside_the_seam_is_classified() {
    let mut files = Vec::new();
    for dir in scanned_crates() {
        rs_files(&dir, &mut files);
    }
    assert!(files.len() > 50, "the source walk found almost nothing: {} files", files.len());

    let mut found: Vec<(String, String, usize)> = Vec::new();
    for f in &files {
        let path = rel(f);
        if SEAM_FILES.contains(&path.as_str()) {
            continue;
        }
        if path.contains("tests.rs") || path.contains("/tests/") || path.contains("_tests/") {
            continue;
        }
        let text = std::fs::read_to_string(f).expect("source must be readable");
        let lines: Vec<&str> = text.lines().collect();
        let in_test_mod = test_module_mask(&lines);
        for (i, line) in lines.iter().enumerate() {
            if in_test_mod[i] || line.trim_start().starts_with("//") {
                continue;
            }
            let Some(declared) = owning_fn_name_of_header(line) else { continue };
            let (sym, start, end) = owning_fn(&lines, i);
            if sym != declared {
                continue;
            }
            let header = fn_header(&lines, start, end);
            let formals = usize_formals(&header);
            if formals.is_empty() {
                continue;
            }
            let code: Vec<&&str> =
                lines[start..end].iter().filter(|l| !l.trim_start().starts_with("//")).collect();
            let mentions = |needle: &str| code.iter().any(|l| l.contains(needle));
            if !mentions("blocks") || !mentions("Statement::Assign") {
                continue;
            }
            // Delegating to the seam is the whole point of the seam.
            if mentions("local_defs::") {
                continue;
            }
            // Enumerating the `Call` destination is what this detector asks for.
            if mentions("Terminator::Call") {
                continue;
            }
            let keyed = keyed_locals(&lines, start, end);
            if !keyed.iter().any(|k| formals.contains(k)) {
                continue;
            }
            found.push((path.clone(), sym, i + 1));
        }
    }

    let classified: Vec<String> = CHANNEL_SUBSETS.iter().map(|(k, _)| (*k).to_string()).collect();
    let mut unclassified: Vec<String> = found
        .iter()
        .map(|(p, sym, line)| (format!("{p}::{sym}"), *line))
        .filter(|(key, _)| !classified.contains(key))
        .map(|(key, line)| format!("{key} (line {line})"))
        .collect();
    unclassified.sort();
    unclassified.dedup();
    assert!(
        unclassified.is_empty(),
        "a per-local definition scan enumerates `Statement::Assign` and NOT the `Call` \
         DESTINATION, and is not in this file's CHANNEL_SUBSETS list.\nFor EACH: a local \
         written by BOTH an `Assign` and a `Call` dest reads as singly-defined here. Route \
         the question through `local_defs`, add the channel, or add it to CHANNEL_SUBSETS \
         with the reason the omission is not a value question.\n{unclassified:#?}"
    );

    // The other direction: an allowlist entry whose site is gone is a stale claim.
    let keys: Vec<String> = found.iter().map(|(p, sym, _)| format!("{p}::{sym}")).collect();
    let stale: Vec<&str> = CHANNEL_SUBSETS
        .iter()
        .map(|(k, _)| *k)
        .filter(|k| !keys.contains(&(*k).to_string()))
        .collect();
    assert!(stale.is_empty(), "CHANNEL_SUBSETS entries whose site no longer exists: {stale:#?}");
}

/// The MIR CONSTRUCTS a value reaches a local through, each labelled with the
/// `trust_types::LocalWrite` channel it produces and with the source tokens a
/// hand-rolled scan spells when it enumerates it.
///
/// The unit is the CONSTRUCT, not the channel: `Partial` is reached through four
/// different constructs, and a scan that matches `Statement::Assign` places but never
/// looks at a `Terminator::Drop` is blind to a `Drop` however the channel is named.
/// [`the_channel_token_groups_cover_every_localwrite_variant`] pins the label set
/// against the enum itself, so adding a channel fails this file before it can widen the
/// blind spot.
const CHANNEL_TOKENS: &[(&str, &str, &[&str])] = &[
    ("WholeNamed", "Assign", &["Statement::Assign"]),
    ("WholeOpaque", "Call dest", &["Terminator::Call"]),
    ("WholeOpaque", "TailCall", &["TailCall"]),
    ("Partial", "SetDiscriminant", &["SetDiscriminant"]),
    ("Partial", "Deinit", &["Deinit"]),
    ("Partial", "Drop glue", &["Terminator::Drop", "Drop {"]),
    (
        "Unlocatable",
        "pointer write / asm / unmodelled",
        &["Opaque", "CopyNonOverlapping", "Statement::Intrinsic", "Statement::Unsupported"],
    ),
    ("Escape", "mutable alias", &["Rvalue::Ref", "AddressOf"]),
];

/// The `LocalWrite` variants [`CHANNEL_TOKENS`] was written against. `Untouched` is not
/// a write and has no construct; every other variant must be the label of at least one.
const LOCALWRITE_VARIANTS: &[&str] =
    &["Escape", "Partial", "Unlocatable", "Untouched", "WholeNamed", "WholeOpaque"];

/// EVERY per-local definition scan outside the seam that enumerates SOME channels and
/// not all of them, frozen as of this change. Mechanically generated by the row below —
/// the keys carry NO adjudication, and none is claimed for them here.
///
/// WHAT THIS LIST IS FOR, stated plainly so it is not mistaken for an audit. The
/// `Assign`-without-`Call`-dest omission is the one with two measured kernel-certified
/// false proofs behind it (`pmod`, `p8`), and every site with THAT shape is adjudicated
/// with a reason in [`CHANNEL_SUBSETS`]. The other partial enumerations below are NOT
/// adjudicated: the list exists so that a NEW one cannot be added silently, and so the
/// next round has the exact worklist rather than a search. The keys that carry a reason
/// are the ones [`CHANNEL_SUBSETS`] also lists, plus any commented inline below; read
/// those rather than a count, because a count here is checked by nothing and goes stale
/// silently.
const CHANNEL_SUBSET_BASELINE: &[&str] = &[
    // A whole-CFG USE/omission screen, not a definition count: every read,
    // assignment destination, index-local mention and call argument/destination
    // naming the empty parameter refuses. Only enumerated scalar operand shapes
    // are inspected; every other statement, rvalue, operand or terminator refuses,
    // including unreachable uses and drops. It grants no value fact; the ordinary
    // evaluator separately refuses calls and effects. It names BOTH Assign and
    // Call, so it is outside CHANNEL_SUBSETS's Assign-without-Call adjudications.
    "trust-vcgen/src/generate/inferred_return.rs::empty_parameter_is_unused",
    // Trust: 2026-10-03 (unwrap-from-facts) — a USE scan, not a definition scan: the
    // local's one definition is found under pinning by `unwrap_origin_call_def`. It only
    // REFUSES: every mention other than storage markers, the defining `as_ref` call and
    // the bare receiver of an unwrap-family call declines, and the
    // `contracts::{statement,terminator}_mentions_local_anywhere` walkers answer `true`
    // for a construct they have not audited, so a channel it does not name keeps the
    // unwrap row fail-closed.
    "trust-vcgen/src/generate/unwrap_panic.rs::as_ref_view_only_unwrapped",
    // Trust: 2026-09-16 (second round) — `acc_next_call_range_operands`,
    // `acc_next_call_to_array_operand` (bridge), `slice_iter_next_kind`,
    // `next_call_enumerated_slice`, `next_call_range_operands` and
    // `next_call_to_array_operand` (vcgen) are GONE from this baseline: their
    // `Terminator::Call`-only entrance scans are now `local_defs::unique_value_call`
    // (see the RESOLVERS note). A re-added scan is a FRESH key and fails the row below.
    "trust-ir-bridge/src/lower.rs::bool_local_has_definition",
    // Trust: 2026-09-30 — the return-interval admission gate's borrow-use scan. Not a
    // definition scan: it asks whether a `&mut` temporary is USED for anything but being
    // passed, as itself, to calls, and checks EVERY statement and terminator mention through
    // `contracts::*_mentions_local_anywhere` (a `Call` destination included). The only answer
    // that admits anything is "no other use at all", which lets `return_interval_admissible`
    // keep a body whose call havoc (`terminator_def_names`) already forgets the borrowed
    // place; any mention it cannot place refuses the body.
    "trust-vcgen/src/abstract_interp/transfer.rs::mutable_borrow_only_passed_to_calls",
    "trust-ir-bridge/src/lower.rs::local_write_count",
    "trust-ir-bridge/src/lower.rs::moved_value_local",
    "trust-ir-bridge/src/lower.rs::native_blocks_local_reseatable",
    "trust-ir-bridge/src/lower.rs::step_by_local_reseatable",
    "trust-ir-bridge/src/lower.rs::step_by_unique_block_def",
    "trust-vcgen/src/contracts.rs::exact_fixed_array_slice_metadata_pair",
    "trust-vcgen/src/contracts.rs::exact_slice_raw_metadata_pair",
    "trust-vcgen/src/contracts.rs::exact_terminal_mutable_alias_reborrow_return",
    "trust-vcgen/src/contracts.rs::exclusive_mutable_collection_alias_pair_is_stable",
    "trust-vcgen/src/contracts.rs::exclusive_mutable_collection_arg_is_stable",
    "trust-vcgen/src/contracts.rs::read_only_collection_alias_is_stable",
    "trust-vcgen/src/contracts.rs::read_only_collection_arg_is_stable",
    "trust-vcgen/src/generate/block_defs.rs::v2_slice_metadata_root_can_rebind",
    // 4006bc923f: the interval half of `_can_rebind`; adjudicated in CHANNEL_SUBSETS.
    "trust-vcgen/src/generate/block_defs.rs::v2_slice_metadata_root_rebinds_between",
    "trust-vcgen/src/generate/bmc_reduction.rs::body_is_straight_line_reduction",
    "trust-vcgen/src/generate/bmc_reduction.rs::const_init_is_outside_loop",
    "trust-vcgen/src/generate/bmc_reduction.rs::local_write_count",
    "trust-vcgen/src/generate/callee_summaries.rs::cast_source_const_lower",
    "trust-vcgen/src/generate/callee_summaries.rs::cast_source_const_upper_nonneg",
    "trust-vcgen/src/generate/callee_summaries.rs::local_is_min_max_result",
    "trust-vcgen/src/generate/callee_summaries.rs::local_mut_escapes",
    "trust-vcgen/src/generate/callee_summaries.rs::min_call_const_upper_bound",
    "trust-vcgen/src/generate/callee_summaries.rs::probe_result_reaches_return",
    "trust-vcgen/src/generate/callee_summaries.rs::ret_call_const_lower_bound",
    "trust-vcgen/src/generate/callee_summaries.rs::tier2a_switch_body_summary",
    "trust-vcgen/src/generate/container_len.rs::local_mutation_blocks",
    "trust-vcgen/src/generate/container_len.rs::vec_created_empty",
    "trust-vcgen/src/generate/discharge.rs::local_has_call_dest_write",
    // 2026-10-01: reads the ONE statement the version oracle names as the write a read
    // sees (`ValueId::Def`); adjudicated in CHANNEL_SUBSETS and RESOLVERS.
    "trust-vcgen/src/generate/dominating_facts.rs::copy_source",
    "trust-vcgen/src/generate/float_range.rs::float_whole_local_defs",
    "trust-vcgen/src/generate/float_range.rs::is_dest",
    "trust-vcgen/src/generate/float_range.rs::param_place_is_entry_stable",
    "trust-vcgen/src/generate/induction.rs::checked_sub_block",
    "trust-vcgen/src/generate/induction.rs::countdown_companion_qual",
    "trust-vcgen/src/generate/induction.rs::cursor_written_since_guard",
    "trust-vcgen/src/generate/int_conversion.rs::int_try_from_def",
    "trust-vcgen/src/generate/int_conversion.rs::local_value_is_stable",
    "trust-vcgen/src/generate/intrinsic_semantics.rs::is_abi_written_parameter",
    // STR_BYTE_POSITION (2026-10-04): a READ scan of the iterator local, not a
    // definition scan. Writes are refused upstream by its one caller's
    // `local_defs::unique_initializing_call` (every channel but the call destination
    // and the `&mut` alias) and the alias by `iter_mut_borrows_only_feed`; it only
    // names the `&mut` borrow it admits.
    "trust-vcgen/src/generate/iterator_yield.rs::iter_consumed_once_by",
    "trust-vcgen/src/generate/iterator_yield.rs::local_has_projected_write",
    // The RAW recognizer, deliberately untightened: it answers "is `C` a value `acc`
    // can hold at loop ENTRY", which is all the BMC refutation lane needs — that lane
    // refutes by exhibiting an input, so an extra value `acc` may hold cannot make its
    // counterexample spurious. Every lane that ASSERTS the derived bound
    // `acc <= C + K*M` calls `accumulator_bound_init_const`, which refuses a PARAMETER
    // outright — the entry definition being the channel this scan cannot see.
    // `path_definition_map_tests::accumulator_bound_withheld_when_accumulator_is_a_parameter`
    // is the matched triple over one body: parameter declines, non-parameter still
    // yields, raw recognizer stays raw.
    "trust-vcgen/src/generate/loop_bounds.rs::accumulator_init_const",
    "trust-vcgen/src/generate/loop_bounds.rs::checked_result_field0_consumer",
    "trust-vcgen/src/generate/loop_bounds.rs::guard_operand_reads_current",
    "trust-vcgen/src/generate/loop_bounds.rs::local_write_blocks",
    "trust-vcgen/src/generate/slice_conversion.rs::unique_whole_local_conversion_call",
    "trust-vcgen/src/generate/unwrap_panic.rs::unwrap_origin_call_def",
    "trust-vcgen/src/generate/value_facts.rs::local_is_immutable_input_param",
    "trust-vcgen/src/generate/value_facts.rs::root_is_never_reseated",
    "trust-vcgen/src/generate/value_facts.rs::selector_write_channel_is_unaccountable",
    // W4 fix round 1 (2026-09-25): VEC-INSERT's region mutation set. Every write
    // channel is enumerated by `container_len::local_mutation_blocks`, which it starts
    // from; its own scan only ADDS blocks (operand mentions, `SetDiscriminant`/`Deinit`,
    // `Drop`, an unknown rvalue), and a larger set only shrinks the region — the
    // fail-closed direction. VEC-INSERT-FIELD-2 (2026-10-07): that additive per-block
    // scan moved into `vec_region::block_mutates_root` (asked per block, so the
    // reservation check can ask it of one block with one statement skipped); it is no
    // longer a keyed whole-body scan, so the key `vec_region.rs::region_mutation_blocks`
    // left this list. The argument above is unchanged: `region_mutation_blocks` still
    // starts from `local_mutation_blocks`, and the per-block predicate only adds.
    // VEC-LEN-LOOP-1 (2026-10-07): a USE scan of a std `Vec` base that only REFUSES.
    // Every statement and terminator whose serialized text names the base is refused
    // unless it is one of the forms it admits (a shared borrow, a `&mut` temp consumed
    // only as a std length-benign receiver, an owned base's one whole write, `Drop`),
    // so a channel it does not name — `SetDiscriminant`, `Deinit`, a pointer write, an
    // unknown statement — refuses the fact rather than passing unseen.
    "trust-vcgen/src/generate/vec_len_invariant.rs::vec_len_never_changes",
    "trust-vcgen/src/generate/witness_grounding.rs::f4_whole_local_defs",
    "trust-vcgen/src/generate/witness_grounding.rs::leaf_push_blocks",
    "trust-vcgen/src/guards.rs::base_collection_step",
    "trust-vcgen/src/guards.rs::clean_variant_switch_target",
    "trust-vcgen/src/guards.rs::local_has_projected_write",
    "trust-vcgen/src/guards.rs::try_branch_continue_target",
    "trust-vcgen/src/guards.rs::option_copied_hop",
    "trust-vcgen/src/guards.rs::local_is_mutably_borrowed",
    // W4 fix round 1 (2026-09-25): VEC-AS-SLICE moved this scan's body into `_one`
    // (asked per alias-closure member); the key follows the body.
    "trust-vcgen/src/guards.rs::local_mut_borrows_may_resize_one",
    // VEC-LEN-PARAM-COPY-1 (2026-10-07): a USE scan of a mutable pointer that only
    // DECLINES. Its whole-local `Assign` arm is the one definition it admits; a write
    // through any channel it does not name is still a mention of the pointer in the
    // exhaustive place walk, unaccounted, so the answer is "may resize".
    "trust-vcgen/src/guards.rs::mut_pointer_uses_may_resize",
    "trust-vcgen/src/guards.rs::operand_local_is_mut_borrow_of",
    "trust-vcgen/src/guards.rs::pointer_local_reseatable",
    "trust-vcgen/src/guards.rs::value_local_is_mut_borrowed",
    // 2026-10-01: the scan keeps its key under its new name; `value_local_is_unstable`
    // answers from the `unstable_locals` table, asserted equal to it under `cfg(test)`.
    "trust-vcgen/src/guards.rs::value_local_is_unstable_scan",
    "trust-vcgen/src/lib.rs::array_local_escapes",
    "trust-vcgen/src/lib.rs::index_local_stable",
    "trust-vcgen/src/lib.rs::local_is_never_written",
    "trust-vcgen/src/lib.rs::local_storage_borrowed_anywhere",
    "trust-vcgen/src/paired_condvar_cert.rs::chases_to_param",
    "trust-vcgen/src/paired_condvar_cert.rs::local_has_any_def",
    // Trust: 2026-09-25 — `Call`-only ROOT tests (047d35ba90 `Box::new`, 171c7536da D8
    // returned box). Neither is a definition question: their one caller,
    // `box_value_is_validity_rooted`, first requires `local_defs::holds_one_value`, which
    // sees every channel, and only then asks whether the one value came from such a call.
    "trust-vcgen/src/sep_engine.rs::is_certified_returned_box_destination",
    "trust-vcgen/src/sep_engine.rs::is_fresh_box_alloc_destination",
    "trust-vcgen/src/termination.rs::assignments_to_local_in_body",
    "trust-vcgen/src/termination.rs::checked_chain_through_assert_pred",
    "trust-vcgen/src/termination.rs::local_ever_mutated",
    "trust-vcgen/src/termination.rs::loop_measure_has_write_risk",
    "trust-vcgen/src/typestate.rs::self_edge_preserves_value",
    // Trust: 2026-10-09 — D14 and the box-root fences of review rounds 85-87: use
    // censuses whose terminator mentions all refuse (see CHANNEL_SUBSETS).
    "trust-vcgen/src/sep_engine.rs::box_copy_is_deref_only",
    "trust-vcgen/src/sep_engine.rs::place_is_through_box_temp",
    "trust-vcgen/src/sep_engine.rs::place_reads_param_pointee",
    // Trust: 2026-10-09 — the synthesized-box-pointer SHAPE belt factored out of
    // `statement_derefs_synthesized_box_ptr`. It mirrors the compiler's nomination (the
    // primary key; a miss here only keeps a row), names the whole-local `Assign` and
    // `Call`-destination channels, and every consumer that roots a box temp also asks
    // `local_defs::holds_one_value` of it.
    "trust-vcgen/src/unsafe_verify/detection.rs::local_is_synthesized_box_ptr",
];

/// THE PROPER-SUBSET RATCHET.
///
/// [`every_channel_subset_scan_outside_the_seam_is_classified`] fires on ONE omission
/// (`Assign` without the `Call` destination). This row fires on ANY proper subset: a
/// keyed whole-body definition scan that names some [`CHANNEL_TOKENS`] group and not
/// every one, and does not delegate to `local_defs`. The set is frozen against
/// [`CHANNEL_SUBSET_BASELINE`] in BOTH directions, so a newly-written partial scan fails
/// by file and line and a site that goes away cannot leave a stale key behind.
#[test]
fn no_new_partial_channel_scan_appears_outside_the_seam() {
    let mut files = Vec::new();
    for dir in scanned_crates() {
        rs_files(&dir, &mut files);
    }
    assert!(files.len() > 50, "the source walk found almost nothing: {} files", files.len());

    let mut found: Vec<String> = Vec::new();
    for f in &files {
        let path = rel(f);
        if SEAM_FILES.contains(&path.as_str()) {
            continue;
        }
        if path.contains("tests.rs") || path.contains("/tests/") || path.contains("_tests/") {
            continue;
        }
        let text = std::fs::read_to_string(f).expect("source must be readable");
        let lines: Vec<&str> = text.lines().collect();
        let in_test_mod = test_module_mask(&lines);
        for (i, line) in lines.iter().enumerate() {
            if in_test_mod[i] || line.trim_start().starts_with("//") {
                continue;
            }
            let Some(declared) = owning_fn_name_of_header(line) else { continue };
            let (sym, start, end) = owning_fn(&lines, i);
            if sym != declared {
                continue;
            }
            let header = fn_header(&lines, start, end);
            let formals = usize_formals(&header);
            if formals.is_empty() {
                continue;
            }
            let code: Vec<&&str> =
                lines[start..end].iter().filter(|l| !l.trim_start().starts_with("//")).collect();
            let mentions = |needle: &str| code.iter().any(|l| l.contains(needle));
            if !mentions("blocks") || mentions("local_defs::") {
                continue;
            }
            let present = CHANNEL_TOKENS
                .iter()
                .filter(|(_, _, toks)| toks.iter().any(|t| mentions(t)))
                .count();
            // Nothing enumerated is not a definition scan; everything enumerated is not
            // a SUBSET.
            if present == 0 || present == CHANNEL_TOKENS.len() {
                continue;
            }
            let keyed = keyed_locals(&lines, start, end);
            if !keyed.iter().any(|k| formals.contains(k)) {
                continue;
            }
            found.push(format!("{path}::{sym}"));
        }
    }
    found.sort();
    found.dedup();

    let mut fresh: Vec<&String> =
        found.iter().filter(|k| !CHANNEL_SUBSET_BASELINE.contains(&k.as_str())).collect();
    fresh.sort();
    assert!(
        fresh.is_empty(),
        "a per-local definition scan enumerates SOME `trust_types::LocalWrite` channels \
         and not all of them, and is not in CHANNEL_SUBSET_BASELINE.\nA local written \
         through a channel the scan does not name reads as singly-defined. Route the \
         question through `local_defs`, name every channel, or — if the omission is \
         deliberate — adjudicate it in CHANNEL_SUBSETS and add the key to the \
         baseline.\n{fresh:#?}"
    );

    let stale: Vec<&&str> =
        CHANNEL_SUBSET_BASELINE.iter().filter(|k| !found.contains(&(**k).to_string())).collect();
    assert!(
        stale.is_empty(),
        "CHANNEL_SUBSET_BASELINE keys whose site no longer exists: {stale:#?}"
    );
}

/// [`CHANNEL_TOKENS`] is written against the `LocalWrite` enum as it stands. Adding a
/// channel there has to reach this file, or the ratchet above silently stops policing
/// it — the exact failure mode the seam exists to prevent, one level up.
#[test]
fn the_channel_token_groups_cover_every_localwrite_variant() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("crates/");
    let model = std::fs::read_to_string(root.join("trust-types/src/model.rs"))
        .expect("the model source must be readable");
    let at = model.find("pub enum LocalWrite<'a> {").expect("LocalWrite must be declared");
    let body = &model[at..][..model[at..].find("\n}").expect("LocalWrite must be closed")];
    let mut variants: Vec<&str> = body
        .lines()
        .map(str::trim)
        .filter(|l| !l.starts_with("//") && !l.starts_with("pub enum"))
        .filter_map(|l| l.split(&['(', ',', ' '][..]).next())
        .filter(|l| l.chars().next().is_some_and(char::is_uppercase))
        .collect();
    variants.sort_unstable();
    variants.dedup();
    assert_eq!(
        variants, LOCALWRITE_VARIANTS,
        "`LocalWrite`'s variants changed; CHANNEL_TOKENS must be revisited"
    );
    let mut labelled: Vec<&str> = CHANNEL_TOKENS.iter().map(|(channel, _, _)| *channel).collect();
    labelled.sort_unstable();
    labelled.dedup();
    let uncovered: Vec<&&str> = LOCALWRITE_VARIANTS
        .iter()
        .filter(|v| **v != "Untouched" && !labelled.contains(*v))
        .collect();
    assert!(
        uncovered.is_empty(),
        "`LocalWrite` channels with no construct in CHANNEL_TOKENS: {uncovered:#?}"
    );
    assert!(
        labelled.iter().all(|l| LOCALWRITE_VARIANTS.contains(l)),
        "CHANNEL_TOKENS labels a channel that is not a `LocalWrite` variant: {labelled:#?}"
    );
}

/// The compile-error half, asserted as a source fact: the two names the previous rounds
/// called are gone, so a rebase cannot reintroduce a call to either.
#[test]
fn the_pre_seam_names_are_gone_from_the_sources() {
    let mut files = Vec::new();
    for dir in scanned_crates() {
        rs_files(&dir, &mut files);
    }
    for f in &files {
        let text = std::fs::read_to_string(f).expect("source must be readable");
        for banned in ["whole_local_def_count", "unique_whole_local_def", "max_explicit_defs"] {
            assert!(
                !text.contains(banned),
                "{}: `{banned}` is the pre-seam spelling; the entry-definition-aware \
                 question lives in `local_defs`",
                rel(f)
            );
        }
    }
}
