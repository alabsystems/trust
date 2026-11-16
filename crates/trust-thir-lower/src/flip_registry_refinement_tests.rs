//! The flip gate's REFINEMENT HARNESS: `current_accepts(x) => pinned_accepts(x)`.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! WHY. `src/flip_registry.rs` is blob-frozen (`scripts/frozen-files.txt`). Every waiver that
//! has ever moved it argues one sentence — "REFUSES MORE, ADMITS NOTHING NEW" — and until this
//! file nothing checked whether the sentence was TRUE: the freeze gate checks that a waiver
//! EXISTS and names the right blob. This harness makes the sentence a test. The build script
//! compiles the gate's production section twice — once from the blob the manifest PINS, read
//! out of git so the baseline is the ratified one and moves only with the pin, and once from
//! the working tree — and the tests below drive both over one corpus of `Lowered` bodies:
//!
//! ```text
//! for every x in CORPUS:    current_accepts(x)  =>  pinned_accepts(x)
//! ```
//!
//! A body the current gate admits and the pinned gate refused is a WIDENING of the frozen
//! oracle, and it fails here whatever the waiver row says.
//!
//! WHAT IS COMPARED. `accepts` is the `TyCtxt`-free half of `record_green`: the per-body lane
//! aggregate (`body_lane_gates_allow_flip`) followed by the constructor that is the only way a
//! `GreenBody` comes into existence (`green_body`) — the same conjunction the file's own tests
//! exercise, on the same fixtures. `session_gates_allow_flip` is covered separately and
//! EXHAUSTIVELY over its whole input cube. Outside the harness, stated rather than blurred:
//! `record_green`'s `TyCtxt`-side gates (session flags, body kind, pending consts,
//! `unsupported`, source-place provenance) and the registry's double-record poison rule.
//!
//! WHAT THIS IS NOT. Evidence, not proof. The corpus is synthetic — the fixtures the file's own
//! tests use, crossed with every lane and both witness kinds — not the differential's real
//! bodies, so a widening only a real body could reach is not seen here. The rung above this is
//! a `Lowered` corpus captured from the producer; it is named in the waiver row, not claimed.
//!
//! MUTATION PROOF, IN TREE. `the_harness_catches_a_widened_gate` runs the same checker against
//! the current gate with one lane conjunct deleted and asserts the widening list is NON-EMPTY
//! and names exactly that lane's points. The corpus is armed, not decorative. The same
//! mutation was also measured once on the frozen file itself; the commit that added this file
//! records the count.
//!
//! WHEN THE PIN MOVES. Two places here know more than "the pin, whatever it is". The two
//! `accepts` wrappers spell each side's signature — since the 2026-09-28 ratification (pin
//! 2a7207af) both sides have the `LaneGatesPassed` token and a five-argument `green_body`; a
//! re-pin to a blob of another shape fails the pinned wrapper's compile, loudly, and the
//! ratifying commit updates the wrapper, as that one did. And `waived_delta` names the
//! CURRENT waiver's movement — the lane every strict refusal must be attributable to and the
//! one body that witnesses it — which the next waiver must update to its own.
//!
//! WHEN THE PIN IS RATIFIED AT THE WORKING TREE, pinned == current and there is NO delta to
//! witness: `pin_meta::PIN_IS_CURRENT` (computed by the build script from the two production
//! sections it compiles) turns the "REFUSES MORE" witness into its dual — the two gates must
//! AGREE everywhere, or the harness itself is defective — and skips the waived delta's witness.
//! The ratifying commit that moves `scripts/frozen-files.txt`'s pin to the working tree's blob
//! needs no edit here ONLY when the pinned wrapper already spells the new pin's gate signature;
//! a ratification across a signature change rewrites that wrapper, as the 2026-09-28 one
//! (771cd9ec -> 2a7207af, 155d985ac9) did (see WHEN THE PIN MOVES). A new movement after it
//! must again witness that it refuses more and name its lane in `waived_delta`. The refinement
//! assertion itself (`current_accepts(x) => pinned_accepts(x)`) and the mutation proof hold in
//! both states.
//!
//! CORRECTED 2026-09-28. This paragraph used to say that ratifying commit "is green with NO edit
//! here (measured 2026-09-24 by re-pinning to 38a964a7 in the working tree and running this
//! module)". That cannot have held with the wrapper of the day: blob 38a964a7 already has the
//! `LaneGatesPassed` token and the five-argument `green_body`, and the pinned wrapper still
//! spelled the `bool` aggregate and four arguments (measured 2026-09-28 on
//! integ/2026-09-27/b2-final5: moving the pin to 6e706457, the same shape, with that wrapper
//! fails with E0308 and E0061 in `pinned::accepts`).

mod pin_meta {
    include!(concat!(env!("OUT_DIR"), "/flip_registry_pin_meta.rs"));
}

/// The frozen `rustc_mir_transform` flip driver, read once for every census in this file
/// that pins its text (the marker gate's CTFE seam, the waived pass lists).
const SEAM: &str = include_str!("../../../compiler/rustc_mir_transform/src/trust_ir_flip.rs");

/// The current waiver adds the declared-opaque return lane to the flip conjunction.
/// The product corpus includes a point that the pin admits and this lane refuses.
#[cfg(trust_frozen_pin_flip_registry)]
mod waived_delta {
    // The new lane alone refuses more; the existing marker gate is unchanged.
    pub(super) const LANE_MARKER: Option<&str> = Some("opaque:");
    pub(super) const MARKER_WITNESS: Option<(bool, bool, usize, Option<bool>, bool, bool)> = None;
    pub(super) const TEXT_DELTA: &[&str] = &[
        "-    let every_lane_clear = union_lane_allows_flip(lowered.union_lane)",
        "+    let every_lane_clear = !lowered.unsubstituted_opaque_return",
        "+        && union_lane_allows_flip(lowered.union_lane)",
    ];
}

/// Trust (F4, 2026-09-29): the premise the marker gate's exemption rests on, pinned where it
/// lives. `marker_gate_allows_flip` exempts an unproven marker sequence only when
/// RemoveStorageMarkers strips it before anything reads `optimized_mir`; `record_green` hands it
/// `mir_opt_level()`, `emit_lifetime_markers()` and the last `-Zmir-enable-passes` entry NAMED
/// `RemoveStorageMarkers`. Those are exactly what the pass's enabling reads ONLY while the
/// sources below say what they say today. No `TyCtxt` runs here, so the premise is pinned as
/// source text, in both directions: a change to the pass's `is_enabled`, to its name (the
/// type name, since it defines no `fn name`), to its overridability or `is_required`, to
/// `should_run_pass`'s override rule, to the pass's place in the optimization pipeline, or to
/// the flip's install point before that pipeline fails this test; a change to
/// `record_green`'s inputs fails it and the census. Behaviourally the same chain is measured
/// by tests/ui/trust/trust_ir_flip_marker_gate_unstripped.rs (four revisions).
#[test]
fn the_marker_gate_inputs_are_remove_storage_markers_own() {
    const PASS: &str =
        include_str!("../../../compiler/rustc_mir_transform/src/remove_storage_markers.rs");
    const MANAGER: &str = include_str!("../../../compiler/rustc_mir_transform/src/pass_manager.rs");
    const PIPELINE: &str = include_str!("../../../compiler/rustc_mir_transform/src/lib.rs");
    const GATE: &str = include_str!("flip_registry.rs");
    let has = |text: &str, needle: &str, why: &str| {
        assert!(text.contains(needle), "{why}: `{needle}` is gone");
    };
    // The pass: its name is its type name, and it is enabled exactly when the gate says.
    // Upstream 1.101 spelling: `is_enabled`/`is_required`/`can_be_overridden` collapsed
    // into `policy() -> PassPolicy`; `Optional` with this default is the same rule.
    has(PASS, "pub(super) struct RemoveStorageMarkers;", "the pass's type (= its name)");
    has(
        PASS,
        "    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {\n        \
         PassPolicy::optional(ctx.mir_opt_level() >= 1 && !ctx.emit_lifetime_markers())\n    }",
        "the pass's enabling rule the gate replicates",
    );
    for absent in ["fn name(", "PassPolicy::Required"] {
        assert!(
            !PASS.contains(absent),
            "RemoveStorageMarkers now defines `{absent}`: its name or overridability is no \
             longer the default the gate assumes"
        );
    }
    // The manager: the default name, and the override rule (last entry wins for an
    // optional pass; required passes always run, which this pass is not).
    has(
        MANAGER,
        "const { simplify_pass_type_name(std::any::type_name::<Self>()) }",
        "a pass's default name is its type name",
    );
    has(
        MANAGER,
        ".find_map(|(name_, polarity)| if name == name_ { Some(*polarity) } else { None })",
        "the last `-Zmir-enable-passes` entry naming the pass wins",
    );
    has(MANAGER, "PassPolicy::Required => true,", "only a required pass always runs");
    has(
        MANAGER,
        "PassPolicy::Optional { enabled_by_default } => {",
        "an optional pass runs by its default unless overridden",
    );
    has(
        MANAGER,
        "            if let Some(o) = pass_override() {",
        "the override replaces the default",
    );
    // The pipeline: the pass is in the optimization pipeline, and the flip installs BEFORE it.
    has(PIPELINE, "&remove_storage_markers::RemoveStorageMarkers,", "the pass is scheduled");
    let flip = PIPELINE
        .find("if let Some(flipped) = trust_ir_flip::try_flip(tcx, did, &body) {")
        .expect("the flip's install point in inner_optimized_mir");
    let optimize = PIPELINE[flip..]
        .find("run_optimization_passes(tcx, &mut body);")
        .expect("the optimization pipeline runs after the flip installs");
    assert!(optimize > 0);
    // The gate: record_green hands the predicate exactly these inputs.
    for needle in [
        ".find(|(name, _)| name == \"RemoveStorageMarkers\")",
        "tcx.sess.emit_lifetime_markers(),",
        "tcx.sess.mir_opt_level(),",
        "remove_storage_markers_override,",
        "tcx.sess.opts.unstable_opts.mir_opt_bisect_limit.is_some(),",
    ] {
        has(GATE, needle, "record_green's input to marker_gate_allows_flip");
    }
    // Trust (F4, round 4): `ctfe_body` is "the CTFE seam installs this body", and the seam's
    // admission set is `try_flip_ctfe`'s. record_green must ask the SAME question of
    // `hir_body_const_context`, and that question must still cover a `#[rustc_comptime]` fn
    // (whose `BodyKind` is `Fn`): the review's measured hole when it keyed on the kind alone.
    const HIR_MAP: &str = include_str!("../../../compiler/rustc_middle/src/hir/map.rs");
    let admission =
        "Some(rustc_hir::ConstContext::Const { .. } | rustc_hir::ConstContext::Static(_))";
    let ctfe_seam = SEAM
        .split_once("pub(crate) fn try_flip_ctfe")
        .expect("the CTFE seam's installer")
        .1
        .split_once("derive_flip_body(")
        .expect("the CTFE seam derives after its admission gate")
        .0;
    has(
        ctfe_seam,
        &format!("{admission} => {{}}\n        _ => return None,"),
        "the seam's admission",
    );
    has(
        GATE,
        &format!(
            "matches!(lowered.body_kind, crate::BodyKind::ConstInit)\n            || matches!(\n                \
             tcx.hir_body_const_context(def),\n                {admission}\n            ),"
        ),
        "record_green's ctfe_body is the seam's own admission predicate",
    );
    has(
        HIR_MAP,
        "if matches!(self.constness(def_id), rustc_hir::Constness::Const { always: true }) {\n                    \
         ConstContext::Const { allow_const_fn_promotion: false }",
        "a comptime fn's const context is `Const`, so the seam installs it",
    );
}

/// FAIL-CLOSED: no baseline, no green. The build script could not produce the pinned blob's
/// production section (no git, a checkout without the object, a manifest row missing or
/// malformed, a blob of a shape the cutter refuses), so nothing compared the two gates.
#[cfg(not(trust_frozen_pin_flip_registry))]
#[test]
fn the_pinned_flip_gate_could_not_be_compiled() {
    panic!(
        "flip_registry refinement harness has NO BASELINE: {}. Until the blob \
         scripts/frozen-files.txt pins for crates/trust-thir-lower/src/flip_registry.rs can be \
         read out of git here, nothing checks that the current gate refines the pinned one.",
        pin_meta::PIN_UNAVAILABLE
    );
}

#[cfg(trust_frozen_pin_flip_registry)]
mod armed {
    use rustc_session::config::DebugInfo;
    use rustc_span::def_id::{CrateNum, DefId, DefIndex};
    use trust_ir::proof::ProofDigest;
    use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ValueId};

    use super::{pin_meta, waived_delta};
    use crate::lineage::{DefinitionIdentity, body_lineage_digest};
    use crate::mir_differential::SourceHeaderCorrespondence;
    use crate::{CalleeRef, Lowered, ThinReborrow, ThinReborrowProvenance};

    /// The gate as the manifest PINS it. A module's private items are reachable only from
    /// inside the module that `include!`s them, so each side exports exactly one wrapper.
    mod pinned {
        #![allow(dead_code, unused_imports)]
        include!(concat!(env!("OUT_DIR"), "/flip_registry_pinned.rs"));

        // Ratified 2026-09-28 at blob 2a7207af (scripts/frozen-files.txt): the pinned gate has the
        // token shape now, so this wrapper spells it exactly as the current side's does.
        pub(super) fn accepts(
            lowered: &Lowered,
            definition: crate::lineage::DefinitionIdentity,
            witness: crate::mir_differential::SourceHeaderCorrespondence,
        ) -> bool {
            let Some(lane_gates) = body_lane_gates_allow_flip(lowered) else {
                return false;
            };
            green_body(definition, &lowered.module, &lowered.callees, witness, lane_gates).is_some()
        }
    }

    /// The gate as the working tree has it, compiled a second time so its private items are
    /// reachable — the same instrument `mir_differential_tailcall_ratification_tests` uses on
    /// the MIR differential. Every token is the frozen file's own.
    mod current {
        #![allow(dead_code, unused_imports)]
        include!(concat!(env!("OUT_DIR"), "/flip_registry_current.rs"));

        pub(super) fn accepts(
            lowered: &Lowered,
            definition: crate::lineage::DefinitionIdentity,
            witness: crate::mir_differential::SourceHeaderCorrespondence,
        ) -> bool {
            let Some(lane_gates) = body_lane_gates_allow_flip(lowered) else {
                return false;
            };
            green_body(definition, &lowered.module, &lowered.callees, witness, lane_gates).is_some()
        }
    }

    // ----------------------------------------------------------------------------------------
    // The corpus.
    // ----------------------------------------------------------------------------------------

    const PROBE_CALLEE: FuncId = FuncId::new(1);
    const FORWARDED: ValueId = ValueId::new(7);

    /// Which correspondence witness a point hands the gate.
    #[derive(Clone, Copy, Debug)]
    enum Witness {
        /// Minted over THIS body's lineage — the shape `record_green` passes.
        Exact,
        /// Minted over some other body's lineage.
        Foreign,
    }

    /// One body the harness asks both gates about.
    struct Point {
        name: String,
        lowered: Lowered,
        definition: DefinitionIdentity,
        witness: Witness,
    }

    fn witness_for(point: &Point) -> SourceHeaderCorrespondence {
        let lineage = match point.witness {
            Witness::Exact => {
                body_lineage_digest(point.definition, &point.lowered.module, &point.lowered.callees)
                    // An undigestable body has no exact witness; hand it a well-formed foreign
                    // one so the gate's own `?` is what refuses it, not a panic here.
                    .unwrap_or_else(|_| ProofDigest::sha256_domain("refinement.undigestable", b""))
            }
            Witness::Foreign => ProofDigest::sha256_domain("refinement.foreign", b"another body"),
        };
        SourceHeaderCorrespondence::test_only(lineage)
    }

    fn function(module: &mut Module, name: &str, body: Option<Vec<InstrNode>>) {
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let index = module.functions.len() as u32;
        let mut function = Function::new(FuncId::new(index), name, ty, BlockId::new(0));
        if let Some(body) = body {
            let mut entry = Block::new(BlockId::new(0));
            entry.body = body;
            function.blocks.push(entry);
        }
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
    }

    /// The file's `probe_module`: one function, no blocks.
    fn plain_module(name: &str) -> Module {
        let mut module = Module::new("refinement_probe");
        function(&mut module, name, None);
        module
    }

    /// The file's `reborrow_probe_module(vec![call_defining_forwarded()])`: one function whose
    /// entry block is a direct `Call` to `PROBE_CALLEE` with `results: [FORWARDED]` — the one
    /// provenance the thin-reborrow lane can certify.
    fn call_module() -> Module {
        let mut node = InstrNode::new(Inst::Call { callee: PROBE_CALLEE, args: Vec::new() });
        node.results = vec![FORWARDED];
        let mut module = Module::new("refinement_probe");
        function(&mut module, "call_probe", Some(vec![node]));
        module
    }

    fn two_function_module() -> Module {
        let mut module = plain_module("first");
        function(&mut module, "second", None);
        module
    }

    /// The file's `probe_callee_ref`, with the identity parameterised so two rows can share one
    /// `FuncId` and disagree on who they are.
    fn ledgered_callee(func_id: FuncId, def_index: u32) -> CalleeRef {
        let def_id = DefId { krate: CrateNum::from_u32(0), index: DefIndex::from_u32(def_index) };
        let definition = DefinitionIdentity::test_only(0xC0DE, u64::from(def_index));
        CalleeRef {
            func_id,
            is_local: true,
            def_index,
            def_id,
            definition,
            concrete_key: Some(crate::lineage::ConcreteCalleeKey::test_only(
                definition,
                crate::lineage::ConcreteInstanceKind::Item,
                Vec::new(),
            )),
            instance_args: Some(Vec::new()),
            def_path: format!("refinement_probe::callee_{def_index}"),
            force_havoc: false,
            site_def_id: def_id,
            site_args: Some(Vec::new()),
            ret_ty: None,
            ret_ty_conflict: false,
            abi: crate::calling_convention::FunctionAbi::C,
            params: crate::ParamSignature::Unsigned,
        }
    }

    fn row(provenance: ThinReborrowProvenance) -> ThinReborrow {
        ThinReborrow { value: FORWARDED, provenance }
    }

    /// The file's `lane_probe_lowered` posture — every lane clear — around a given body.
    fn clean(module: Module, callees: Vec<CalleeRef>) -> Lowered {
        Lowered {
            global_origins: Vec::new(),
            module,
            body_kind: crate::BodyKind::Fn,
            opaque_collapse: false,
            enum_declines: Vec::new(),
            union_lane: false,
            layout_withheld_structs: Vec::new(),
            enum_param_lane: false,
            symbolic: false,
            unsubstituted_opaque_return: false,
            unsupported: Vec::new(),
            contains_call: false,
            place_path_carrier: false,
            zst_closure_arg: false,
            coroutine_frame_ptr: false,
            fnptr_adapter: false,
            thin_reborrows: Vec::new(),
            mut_reborrows: Vec::new(),
            callees,
            pending_consts: Vec::new(),
            enum_fold_switch_blocks: std::collections::HashSet::new(),
        }
    }

    type Base = (&'static str, fn() -> (Module, Vec<CalleeRef>));
    type Variation = (&'static str, fn(&mut Lowered));

    /// Every BASE is a `(module, callee ledger)` shape the file's own tests use; every VARIATION
    /// moves one lane off the clean posture (or several, in the compound points). The corpus is
    /// their product, under both witness kinds.
    fn corpus() -> Vec<Point> {
        let bases: [Base; 6] = [
            ("plain", || (plain_module("lane_gate_probe"), Vec::new())),
            ("call+ledger", || (call_module(), vec![ledgered_callee(PROBE_CALLEE, 11)])),
            ("call+no-ledger", || (call_module(), Vec::new())),
            ("call+ambiguous-ledger", || {
                (
                    call_module(),
                    vec![ledgered_callee(PROBE_CALLEE, 11), ledgered_callee(PROBE_CALLEE, 12)],
                )
            }),
            ("two-functions", || (two_function_module(), Vec::new())),
            ("no-function", || (Module::new("refinement_probe"), Vec::new())),
        ];
        let variations: [Variation; 13] = [
            ("clean", |_| {}),
            ("opaque:return", |l| l.unsubstituted_opaque_return = true),
            ("union_lane", |l| l.union_lane = true),
            ("enum_param_lane", |l| l.enum_param_lane = true),
            ("fnptr_adapter", |l| l.fnptr_adapter = true),
            ("thin:CallResult", |l| l.thin_reborrows.push(row(ThinReborrowProvenance::CallResult))),
            ("thin:Binding", |l| l.thin_reborrows.push(row(ThinReborrowProvenance::Binding))),
            ("thin:Projection", |l| l.thin_reborrows.push(row(ThinReborrowProvenance::Projection))),
            ("thin:Other", |l| l.thin_reborrows.push(row(ThinReborrowProvenance::Other))),
            ("thin:CallResult+Binding", |l| {
                l.thin_reborrows.push(row(ThinReborrowProvenance::CallResult));
                l.thin_reborrows.push(row(ThinReborrowProvenance::Binding));
            }),
            ("mut:CallResult", |l| l.mut_reborrows.push(row(ThinReborrowProvenance::CallResult))),
            ("thin:CallResult+mut:CallResult", |l| {
                l.thin_reborrows.push(row(ThinReborrowProvenance::CallResult));
                l.mut_reborrows.push(row(ThinReborrowProvenance::CallResult));
            }),
            ("every-lane", |l| {
                l.union_lane = true;
                l.enum_param_lane = true;
                l.fnptr_adapter = true;
                l.thin_reborrows.push(row(ThinReborrowProvenance::Other));
                l.mut_reborrows.push(row(ThinReborrowProvenance::CallResult));
            }),
        ];
        let mut points = Vec::new();
        for (base_name, base) in bases {
            for (variation_name, vary) in variations {
                for witness in [Witness::Exact, Witness::Foreign] {
                    let (module, callees) = base();
                    let mut lowered = clean(module, callees);
                    vary(&mut lowered);
                    points.push(Point {
                        name: format!("{base_name}/{variation_name}/{witness:?}"),
                        lowered,
                        definition: DefinitionIdentity::test_only(0xC0DE, 3),
                        witness,
                    });
                }
            }
        }
        points
    }

    // ----------------------------------------------------------------------------------------
    // The checker.
    // ----------------------------------------------------------------------------------------

    /// The names of every point `new` accepts that `old` refused — the refinement check as a
    /// function of the two predicates, so a MUTANT runs through the very same code path.
    fn widenings<'p>(
        corpus: &'p [Point],
        new: impl Fn(&Point) -> bool,
        old: impl Fn(&Point) -> bool,
    ) -> Vec<&'p str> {
        corpus.iter().filter(|p| new(p) && !old(p)).map(|p| p.name.as_str()).collect()
    }

    fn current_accepts(point: &Point) -> bool {
        current::accepts(&point.lowered, point.definition, witness_for(point))
    }

    fn pinned_accepts(point: &Point) -> bool {
        pinned::accepts(&point.lowered, point.definition, witness_for(point))
    }

    /// THE CLAIM. Every waiver row for `flip_registry.rs` says the moved gate refuses more and
    /// admits nothing new, relative to the pin. Over this corpus that is checked, not read.
    #[test]
    fn the_current_flip_gate_refines_the_pinned_one() {
        let corpus = corpus();
        let widened = widenings(&corpus, current_accepts, pinned_accepts);
        assert!(
            widened.is_empty(),
            "the current flip gate ADMITS bodies the pinned gate refused — a WIDENING of the \
             frozen oracle, which no waiver row may excuse: {widened:?}"
        );

        // NON-VACUITY, three ways. A corpus nothing accepts, or one on which the two gates
        // never disagree, would pass the assertion above while establishing nothing.
        let both: Vec<&str> = corpus
            .iter()
            .filter(|p| current_accepts(p) && pinned_accepts(p))
            .map(|p| p.name.as_str())
            .collect();
        assert!(
            both.len() >= 2,
            "fewer than two points are accepted by BOTH gates ({both:?}); the refinement check \
             is vacuous over a corpus nothing admits"
        );
        assert!(
            corpus.iter().any(|p| !pinned_accepts(p)),
            "the pinned gate refuses nothing in this corpus, so no widening could ever show"
        );
        let strictly_more: Vec<&str> = corpus
            .iter()
            .filter(|p| pinned_accepts(p) && !current_accepts(p))
            .map(|p| p.name.as_str())
            .collect();
        if pin_meta::PIN_IS_CURRENT {
            // The ratified state: the pin IS the working tree, so the two compiled gates are
            // the same text and must agree on every point. A disagreement here is a defect
            // of the harness (the cutter, the wrappers), not of the gate.
            assert!(
                strictly_more.is_empty(),
                "pinned and current production sections are byte-identical, yet the two \
                 compiled gates disagree: {strictly_more:?}"
            );
        } else {
            // A waived movement: it must be VISIBLE here as a strict refusal, or "REFUSES
            // MORE" is a sentence the corpus cannot tell from "unchanged" -- unless it moves
            // no lane at all, and is witnessed by its own channel's test instead.
            assert!(
                !strictly_more.is_empty() || waived_delta::LANE_MARKER.is_none(),
                "REFUSES MORE was not witnessed: no point is refused by the current gate and \
                 admitted by the pinned one, so the two gates are indistinguishable here"
            );
            // Every strict refusal must be attributable to the lane the waiver names; a
            // strict refusal from anywhere else is a movement no waiver row has accounted
            // for, and the fix is to name it in `waived_delta` with its row. A waiver that
            // names no lane moved none: its witness lives in another channel's test.
            match waived_delta::LANE_MARKER {
                Some(lane) => assert!(
                    strictly_more.iter().all(|name| name.contains(lane)),
                    "a strict refusal outside the waived `{lane}` lane: {strictly_more:?}"
                ),
                None => assert!(
                    strictly_more.is_empty() || waived_delta::MARKER_WITNESS.is_none(),
                    "the waiver moves the marker gate only, yet the LANE corpus refuses more: \
                     {strictly_more:?}"
                ),
            }
        }
    }

    /// THE MUTATION PROOF. The same checker, run against the current gate with ONE lane
    /// conjunct deleted, must report the widening — or the test above is a test of nothing.
    /// Two lanes, so the arming is not a property of one flag.
    #[test]
    fn the_harness_catches_a_widened_gate() {
        let corpus = corpus();
        // `union_lane` is read at exactly one place in the production section, the aggregate's
        // first conjunct: evaluating the current gate on the body with that flag cleared IS
        // that conjunct deleted.
        let union_conjunct_deleted = |point: &Point| {
            let mut lowered = point.lowered.clone();
            lowered.union_lane = false;
            current::accepts(&lowered, point.definition, witness_for(point))
        };
        let widened = widenings(&corpus, union_conjunct_deleted, pinned_accepts);
        assert!(
            !widened.is_empty(),
            "deleting the union-lane conjunct admitted nothing the pin refused: the corpus has \
             no point that lane decides, so the refinement test is DISARMED"
        );
        assert!(
            widened.iter().all(|name| name.contains("/union_lane/")),
            "the union-lane mutant widened points that lane does not decide: {widened:?}"
        );

        let thin_conjunct_deleted = |point: &Point| {
            let mut lowered = point.lowered.clone();
            lowered.thin_reborrows.clear();
            current::accepts(&lowered, point.definition, witness_for(point))
        };
        let widened = widenings(&corpus, thin_conjunct_deleted, pinned_accepts);
        assert!(
            !widened.is_empty(),
            "deleting the thin-reborrow conjunct admitted nothing the pin refused: DISARMED"
        );
        assert!(
            widened.iter().all(|name| name.contains("/thin:")),
            "the thin-reborrow mutant widened points that lane does not decide: {widened:?}"
        );
    }

    /// The wave-MR `mut_reborrows` lane is the one movement between the pin and the working
    /// tree that refuses a body the pin admitted — and it is NOT in the file's own wiring pin
    /// (`test_every_body_lane_gate_is_wired_into_the_flip_decision` lists four lanes; measured
    /// 2026-09-24, `mut_reborrows` occurs in that tests module only as a fixture initialiser).
    /// Pinned here, against the working tree.
    #[test]
    fn the_mut_reborrow_lane_is_wired_into_the_current_gate() {
        let corpus = corpus();
        let point = corpus
            .iter()
            .find(|p| p.name == "call+ledger/mut:CallResult/Exact")
            .expect("the corpus carries the certified-call body with one &mut row");
        // The &mut lane's own witness while it was the waived delta: the pin had no &mut lane.
        // Since the 2026-09-28 ratification the pin carries it, both sides refuse this body,
        // and the wiring assertions below — about the CURRENT gate alone — still hold.
        if !pin_meta::PIN_IS_CURRENT && waived_delta::LANE_MARKER == Some("mut:") {
            assert!(pinned_accepts(point), "the pinned gate had no &mut lane and admits this body");
        }
        assert!(
            !current_accepts(point),
            "the current gate declares the &mut lane refuses the whole class, but it is NOT \
             WIRED into the decision"
        );
        let mut cleared = point.lowered.clone();
        cleared.mut_reborrows.clear();
        assert!(
            current::accepts(&cleared, point.definition, witness_for(point)),
            "the same body without the &mut row must be admitted, or the refusal above proves \
             nothing"
        );
    }

    /// `session_gates_allow_flip` takes four scalars, so refinement is checked over its WHOLE
    /// input cube (2 × 2 × 5 × 2 = 40 points), not a sample.
    #[test]
    fn the_session_gates_refine_exhaustively() {
        let levels = [
            DebugInfo::None,
            DebugInfo::LineDirectivesOnly,
            DebugInfo::LineTablesOnly,
            DebugInfo::Limited,
            DebugInfo::Full,
        ];
        let mut widened = Vec::new();
        let mut admitted = 0;
        let mut points = 0;
        for lower in [false, true] {
            for flip in [false, true] {
                for level in levels {
                    for coverage in [false, true] {
                        points += 1;
                        let new = current::session_gates_allow_flip(lower, flip, level, coverage);
                        let old = pinned::session_gates_allow_flip(lower, flip, level, coverage);
                        if new && !old {
                            widened.push(format!("({lower}, {flip}, {level:?}, {coverage})"));
                        }
                        admitted += usize::from(new && old);
                    }
                }
            }
        }
        assert_eq!(points, 40);
        assert!(widened.is_empty(), "session gates widened at {widened:?}");
        assert_eq!(
            admitted, 1,
            "exactly one session posture flips: both flags, no debuginfo, no coverage"
        );
    }

    /// Trust (F4): the per-body MARKER gate over its whole input cube (2 x 2 x 5 x 3 x 2 x 2 =
    /// 240 points). Pin 53da2f13 carries the named marker helper. Call that
    /// independently compiled function directly: another lane's waiver can
    /// change the production section without changing the marker rule.
    /// A pin without this signature must fail to compile until reviewed.
    #[test]
    fn the_marker_gate_refines_exhaustively() {
        type Point = (bool, bool, usize, Option<bool>, bool, bool);
        let pinned_allows = |p: Point| {
            let (exact, emit, level, ovr, bisect, ctfe) = p;
            pinned::marker_gate_allows_flip(exact, emit, level, ovr, bisect, ctfe)
        };
        let current_allows = |p: Point| {
            let (exact, emit, level, ovr, bisect, ctfe) = p;
            current::marker_gate_allows_flip(exact, emit, level, ovr, bisect, ctfe)
        };
        let mut cube: Vec<Point> = Vec::new();
        for exact in [false, true] {
            for emit in [false, true] {
                for level in 0..=4usize {
                    for ovr in [None, Some(false), Some(true)] {
                        for bisect in [false, true] {
                            for ctfe in [false, true] {
                                cube.push((exact, emit, level, ovr, bisect, ctfe));
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(cube.len(), 240);
        let widened: Vec<Point> =
            cube.iter().copied().filter(|p| current_allows(*p) && !pinned_allows(*p)).collect();
        assert!(widened.is_empty(), "the marker gate WIDENED at {widened:?}");
        let bisect_guard_deleted: Vec<Point> = cube
            .iter()
            .copied()
            .filter(|&(exact, emit, level, ovr, bisect, ctfe)| {
                current::marker_gate_allows_flip(exact, emit, level, ovr, false, ctfe)
                    && !pinned_allows((exact, emit, level, ovr, bisect, ctfe))
            })
            .collect();
        assert_eq!(
            bisect_guard_deleted.len(),
            9,
            "the marker comparison lost its mutation witness"
        );
        assert!(bisect_guard_deleted.contains(&(false, false, 1, None, true, false)));
        // Every exact body is admitted, whatever the session.
        assert!(
            cube.iter().filter(|p| p.0).all(|p| current_allows(*p)),
            "an EXACT marker sequence was refused"
        );
        // The exemption still exists (a stripped, unbisected fn body at -O0) ...
        assert!(current::marker_gate_allows_flip(false, false, 1, None, false, false));
        // ... and is exactly: no lifetime intrinsics, the pass provably runs, no bisect, and
        // not a const initializer.
        for p in &cube {
            let (exact, emit, level, ovr, bisect, ctfe) = *p;
            let stripped = match ovr {
                Some(on) => on,
                None => level > 0,
            };
            let expect = exact || (!emit && stripped && !bisect && !ctfe);
            assert_eq!(current_allows(*p), expect, "marker gate at {p:?}");
        }
        let mut strictly_more: Vec<Point> =
            cube.iter().copied().filter(|p| pinned_allows(*p) && !current_allows(*p)).collect();
        if pin_meta::PIN_IS_CURRENT {
            assert!(strictly_more.is_empty(), "pinned == current, yet they disagree");
        } else if let Some(w) = waived_delta::MARKER_WITNESS {
            assert!(strictly_more.contains(&w), "REFUSES MORE was not witnessed at {w:?}");
            let mut expected: Vec<Point> = cube
                .iter()
                .copied()
                .filter(|&(exact, emit, level, ovr, bisect, ctfe)| {
                    let stripped = match ovr {
                        Some(on) => on,
                        None => level > 0,
                    };
                    !exact && !emit && (!stripped || bisect || ctfe)
                })
                .collect();
            strictly_more.sort();
            expected.sort();
            assert_eq!(strictly_more, expected, "the marker gate refuses more than F4 argues");
        } else {
            assert!(strictly_more.is_empty(), "the waiver authorizes no marker-gate movement");
        }
    }

    /// Trust (F4): the CENSUS. Every production token of `flip_registry.rs` that moved pin ->
    /// tree is one the waiver names -- in particular the `TyCtxt`-side inputs `record_green`
    /// hands `marker_gate_allows_flip`, which no behavioural test here can reach.
    #[cfg(trust_frozen_pin_mir_differential)]
    #[test]
    fn the_flip_registry_production_delta_is_exactly_the_waived_one() {
        use crate::mir_differential_refinement_tests::armed::{line_delta, production_lines};
        const PINNED_SECTION: &str =
            include_str!(concat!(env!("OUT_DIR"), "/flip_registry_pinned.rs"));
        const CURRENT_SECTION: &str =
            include_str!(concat!(env!("OUT_DIR"), "/flip_registry_current.rs"));
        let delta =
            line_delta(&production_lines(PINNED_SECTION), &production_lines(CURRENT_SECTION));
        if pin_meta::PIN_IS_CURRENT {
            assert!(
                delta.is_empty(),
                "pinned == current, yet the census found a delta: {delta:#?}"
            );
            return;
        }
        let expected: Vec<String> =
            waived_delta::TEXT_DELTA.iter().map(|l| l.to_string()).collect();
        assert!(
            delta == expected,
            "flip_registry.rs's production section moved by a delta no waiver names. MEASURED \
             delta (pin -> tree), in `waived_delta::TEXT_DELTA` spelling:\n{}",
            delta.iter().map(|l| format!("        {l:?},")).collect::<Vec<_>>().join("\n")
        );
    }

    /// The baseline the build script compiled is the blob the MANIFEST pins right now, so a
    /// stale build output cannot quietly compare against yesterday's pin. `include_str!` also
    /// makes the manifest a compile-time dependency of this test target.
    #[test]
    fn the_compiled_baseline_is_the_manifest_pin() {
        let manifest = include_str!("../../../scripts/frozen-files.txt");
        let pin = manifest
            .lines()
            .map(str::trim)
            .filter(|row| !row.is_empty() && !row.starts_with('#'))
            .find_map(|row| {
                let mut cols = row.split('|');
                (cols.next() == Some("crates/trust-thir-lower/src/flip_registry.rs"))
                    .then(|| cols.next().unwrap_or_default())
            })
            .expect("scripts/frozen-files.txt pins flip_registry.rs");
        assert_eq!(
            super::pin_meta::PINNED_BLOB,
            pin,
            "the harness compiled a baseline that is not the manifest's pin"
        );
    }
}

/// The frozen rustc_mir_transform flip driver's advance_built_to_runtime runs
/// exactly the pass lists the 1.101 waiver row for trust_ir_flip.rs claims
/// survived the run_passes signature change (the deleted Optimizations
/// argument gated optimization passes this driver never listed). A source
/// census in the trust-clean-ir-gate style: any edit to those lists fails
/// here before it can pretend the waiver still describes the file.
#[test]
fn advance_built_to_runtime_runs_exactly_the_waived_pass_lists() {
    let source = SEAM;
    assert_eq!(source.matches("pm::run_passes(").count(), 2);
    assert_eq!(source.matches("&[&simplify::SimplifyCfg::Initial]").count(), 1);
    assert_eq!(
        source
            .matches("&[&promote_pass, &simplify::SimplifyCfg::PromoteConsts, &coverage::InstrumentCoverage]")
            .count(),
        1
    );
    assert!(!source.contains("Optimizations"));
}
