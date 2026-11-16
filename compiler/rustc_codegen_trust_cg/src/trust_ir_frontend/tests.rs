// ---------------------------------------------------------------------------
// Refusal-classification tests
//
// Everything these exercise is pure data: `FrontendRefusal`'s variants carry
// `String`/`usize`/`u32` and nothing else, so the classification, the census and
// the rendered report are all testable without a `TyCtxt`, unlike the crate's
// `src/tests.rs`. That is deliberate — the one thing this
// module must never get wrong is which class an item was refused under, and a
// property that needs a whole compiler session to check is a property nobody
// checks.
// ---------------------------------------------------------------------------
mod refusal_class_tests {
    use super::super::*;

    fn upstream(sym: &str, krate: &str) -> FrontendRefusal {
        FrontendRefusal::UpstreamBody {
            symbol: sym.to_string(),
            def_path: format!("{krate}::thing"),
            krate: krate.to_string(),
        }
    }

    fn generic(sym: &str) -> FrontendRefusal {
        FrontendRefusal::GenericInstance { symbol: sym.to_string(), args: "[u64]".to_string() }
    }

    fn synthesized(sym: &str) -> FrontendRefusal {
        FrontendRefusal::SynthesizedInstance {
            symbol: sym.to_string(),
            detail: "Shim(DropGlue(..))".to_string(),
        }
    }

    /// `CLASS_COUNT`, `ALL` and `slot` are three spellings of one list. If they
    /// ever disagree the census silently mis-attributes counts, which is worse
    /// than not having a census at all.
    #[test]
    fn class_list_is_complete_and_indexable() {
        assert_eq!(RefusalClass::ALL.len(), CLASS_COUNT);
        // Trust (step 2 increment 3): the instance lane's class, the elided-drop class and the
        // R-8 unfaithful-panic class.
        assert_eq!(CLASS_COUNT, 21);
        assert_eq!(RefusalClass::InstanceAssembly.slot(), 12);
        // One `unfaithful-panic` class: main's 9eb52da524 numbered it 12 independently; unified
        // on merge, it sits LAST so every class keeps a unique slot.
        assert_eq!(RefusalClass::ElidedDrop.slot(), 13);
        assert_eq!(RefusalClass::UnfaithfulPanic.slot(), 14);
        assert_eq!(RefusalClass::InstanceAssembly.tag(), "instance-assembly");
        assert_eq!(RefusalClass::ElidedDrop.tag(), "elided-drop");
        assert_eq!(RefusalClass::UnfaithfulPanic.tag(), "unfaithful-panic");
        // Main's effect-conservation class (D28), merged after the three above.
        assert_eq!(RefusalClass::EffectNotConserved.slot(), 15);
        assert_eq!(RefusalClass::EffectNotConserved.tag(), "effect-not-conserved");
        // Trust (plan step 3.0): every refusal F1 makes because of a Clean-origin body.
        assert_eq!(RefusalClass::CleanBelowGate.slot(), 16);
        assert_eq!(RefusalClass::CleanBelowGate.tag(), "clean-below-gate");
        // Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's three classes, after step 3.0's.
        assert_eq!(RefusalClass::CodegenModule.slot(), 17);
        assert_eq!(RefusalClass::CodegenModule.tag(), "codegen-module");
        assert_eq!(RefusalClass::TrustCgRefused.slot(), 18);
        assert_eq!(RefusalClass::TrustCgRefused.tag(), "trust-cg-refused");
        assert_eq!(RefusalClass::CalleeAbiMismatch.slot(), 19);
        assert_eq!(RefusalClass::UpstreamEntry.slot(), 20);
        assert_eq!(RefusalClass::UpstreamEntry.tag(), "upstream-entry");
        assert_eq!(RefusalClass::CalleeAbiMismatch.tag(), "callee-abi-mismatch");
        for (i, class) in RefusalClass::ALL.iter().enumerate() {
            assert_eq!(class.slot(), i, "{class:?} indexes {} but sits at {i}", class.slot());
        }
        let mut tags: Vec<&str> = RefusalClass::ALL.iter().map(|c| c.tag()).collect();
        tags.sort_unstable();
        let distinct = tags.len();
        tags.dedup();
        assert_eq!(tags.len(), distinct, "two classes share a tag; the census cannot be grepped");
        for class in RefusalClass::ALL {
            assert!(!class.retired_by().is_empty(), "{class:?} does not say what retires it");
        }
    }

    /// The class tag leads every message. This is the half of the improvement
    /// that is live with no call-site change: a caller that only prints the flat
    /// refusal list can still classify it.
    #[test]
    fn every_message_leads_with_its_class_tag() {
        let all = [
            upstream("_RNvC1a", "core"),
            synthesized("_RNvC1b"),
            generic("_RNvC1c"),
            FrontendRefusal::UnsupportedAbi { symbol: "_RNvC1d".into(), detail: "variadic".into() },
            FrontendRefusal::NotALocalItem {
                symbol: "_RNvC1e".into(),
                detail: "constructor shim".into(),
            },
            FrontendRefusal::SelectedFunctionMissing {
                symbol: "_RNvC1f".into(),
                func_id: 2,
                functions: 2,
            },
            FrontendRefusal::AssembledHandoffUnavailable { symbol: "_RNvC1i".into() },
            FrontendRefusal::ExactAssembledBodyAbsent {
                symbol: "_RNvC1j".into(),
                def_index: 7,
                definition: "Item".into(),
            },
            FrontendRefusal::MissingFuncType { symbol: "_RNvC1g".into(), ty: 9 },
            FrontendRefusal::ConverterRefused {
                symbol: "_RNvC1h".into(),
                detail: "unsupported inst".into(),
            },
            FrontendRefusal::InstanceAssembly {
                symbol: "_RNvC1k".into(),
                detail: "instance cycle".into(),
            },
            FrontendRefusal::InstanceProducerRefused {
                symbol: "_RNvC1l".into(),
                reason: "PendingConsts".into(),
                refusal: trust_thir_lower::InstanceRefusal::PendingConsts,
            },
            FrontendRefusal::UnfaithfulPanic {
                symbol: "_RNvC1m".into(),
                detail: "reaches a runtime check".into(),
            },
            FrontendRefusal::CodegenModule {
                symbol: "_RNvC1n".into(),
                detail: "an indirect call (INC5.4-FNREF)".into(),
            },
            FrontendRefusal::TrustCgRefused {
                symbol: "_RNvC1o".into(),
                variant: "Adapter::UnlicensedBody".into(),
                detail: "unlicensed".into(),
            },
            FrontendRefusal::CalleeAbiMismatch {
                symbol: "_RNvC1p".into(),
                detail: "signed (u32) -> (u64)".into(),
            },
            FrontendRefusal::UpstreamEntry {
                symbol: "_RNvC1q".into(),
                check: "digest",
                detail: "corrupt metadata envelope".into(),
            },
        ];
        for refusal in &all {
            let rendered = refusal.to_string();
            let expected = format!("[{}] ", refusal.class().tag());
            assert!(
                rendered.starts_with(&expected),
                "{rendered:?} does not lead with {expected:?}"
            );
        }
    }

    /// Trust (step 2 increment 5, sub-step 5.4.2): a trust-cg census row prints its
    /// `CompileError` variant in its sample, so three distinct rows read as three variants.
    #[test]
    fn a_trust_cg_census_row_names_its_variant() {
        let refusal = FrontendRefusal::TrustCgRefused {
            symbol: "_RNvC1q".into(),
            variant: "Adapter::ImplicitDestructor".into(),
            detail: "drop of String".into(),
        };
        assert_eq!(refusal.class(), RefusalClass::TrustCgRefused);
        let line = refusal.sample_line();
        assert!(line.contains("[trust-cg-refused:Adapter::ImplicitDestructor]"), "{line}");
        let mut census = RefusalCensus::default();
        census.record(refusal);
        let report = census.report(1);
        assert!(report.contains("[trust-cg-refused]"), "{report}");
        assert!(report.contains("[trust-cg-refused:Adapter::ImplicitDestructor]"), "{report}");
    }

    /// The two `NotALocalItem` halves are now distinct classes. Merging them was
    /// the specific thing that made the old diagnostic unreadable: they are
    /// 86% and 13% of a real crate and have completely different fixes.
    #[test]
    fn upstream_and_synthesized_are_different_classes() {
        assert_ne!(upstream("a", "core").class(), synthesized("b").class());
        assert_eq!(upstream("a", "core").class(), RefusalClass::UpstreamBody);
        assert_eq!(synthesized("b").class(), RefusalClass::SynthesizedInstance);
    }

    /// Both malformed-Module variants are one class: a user cannot act on them
    /// separately, and both mean the producer/consumer contract broke.
    #[test]
    fn malformed_module_variants_share_one_class() {
        let a = FrontendRefusal::SelectedFunctionMissing {
            symbol: "a".into(),
            func_id: 0,
            functions: 0,
        };
        let b = FrontendRefusal::MissingFuncType { symbol: "b".into(), ty: 1 };
        assert_eq!(a.class(), RefusalClass::MalformedProducerModule);
        assert_eq!(b.class(), a.class());
    }

    #[test]
    fn empty_census_is_empty() {
        let census = RefusalCensus::default();
        assert!(census.is_empty());
        assert_eq!(census.len(), 0);
        for class in RefusalClass::ALL {
            assert_eq!(census.count(class), 0);
        }
    }

    /// The shape of the real measurement: the nine-line `Vec` + `HashMap`
    /// program, 160 reachable items, 1 admitted, 137 upstream, 22 synthesized,
    /// ZERO generic.
    #[test]
    fn census_counts_and_orders_by_descending_count() {
        let mut census = RefusalCensus::default();
        for i in 0..137 {
            census.record(upstream(&format!("_RNvCsUp{i}"), "core"));
        }
        for i in 0..22 {
            census.record(synthesized(&format!("_RNvCsShim{i}")));
        }
        assert_eq!(census.len(), 159);
        assert!(!census.is_empty());
        assert_eq!(census.count(RefusalClass::UpstreamBody), 137);
        assert_eq!(census.count(RefusalClass::SynthesizedInstance), 22);
        assert_eq!(census.count(RefusalClass::GenericInstance), 0);

        let report = census.report(160);
        let up = report.find("[upstream-body]").expect("upstream class missing from report");
        let shim =
            report.find("[synthesized-instance]").expect("synthesized class missing from report");
        assert!(up < shim, "the largest class must lead the report");
        // An EMPTY class is omitted rather than printed as zero: a census that
        // lists classes nobody hit is a wall of noise again.
        assert!(!report.contains("[generic-instance]"), "empty class was printed");
        assert!(report.contains("refused 159 of 160"));
    }

    /// Samples are bounded and the remainder is stated. The unbounded list this
    /// replaces printed 159 mangled symbols.
    #[test]
    fn census_samples_are_bounded_and_the_remainder_is_stated() {
        let mut census = RefusalCensus::default();
        for i in 0..500 {
            census.record(upstream(&format!("_RNvCsUp{i}"), "core"));
        }
        let report = census.report(500);
        assert_eq!(report.matches("e.g. ").count(), CENSUS_SAMPLES_PER_CLASS);
        assert!(
            report.contains(&format!("and {} more in this class", 500 - CENSUS_SAMPLES_PER_CLASS)),
            "report did not state the un-sampled remainder:\n{report}"
        );
        assert!(report.lines().count() < 40, "a census must not become a wall of symbols");
    }

    /// A class that is well under 1% must not render as `0.0%` and read as
    /// empty; permille is the reason the report divides by ten by hand.
    #[test]
    fn a_sub_one_percent_class_still_renders_nonzero() {
        let mut census = RefusalCensus::default();
        census.record(generic("_RNvCsG0"));
        let report = census.report(160);
        assert!(report.contains("(0.6%)"), "1/160 did not render as 0.6%:\n{report}");
    }

    /// Zero reachable items must not divide by zero. Unreachable through the
    /// call site (no refusals without items) but a report must never panic.
    #[test]
    fn report_survives_zero_reachable() {
        let mut census = RefusalCensus::default();
        census.record(generic("_RNvCsG0"));
        let report = census.report(0);
        assert!(report.contains("(0.0%)"));
    }

    /// The report must keep saying that the absence of a MIR fallback is
    /// deliberate. This is the property most likely to be "fixed" by someone
    /// reading a 159-item refusal list.
    #[test]
    fn report_states_that_no_fallback_is_deliberate() {
        let mut census = RefusalCensus::default();
        census.record(upstream("_RNvCsUp0", "core"));
        let report = census.report(1);
        assert!(report.contains("never falls back to the MIR path"));
        assert!(report.contains("do not add one"));
    }

    /// A census SAMPLE must not repeat the class boilerplate: three copies of
    /// one sentence per class is the same wall of text the census replaces.
    #[test]
    fn samples_carry_only_the_discriminating_detail() {
        let r = upstream("_RNvCsUp0", "core");
        let sample = r.sample_line();
        assert!(sample.contains("_RNvCsUp0"), "sample dropped the symbol: {sample}");
        assert!(!sample.contains(r.class().tag()), "sample repeats the class tag: {sample}");
        assert!(!sample.contains("local-only query"), "sample repeats the class explanation");
        assert!(sample.len() < r.to_string().len(), "sample is no shorter than the full message");

        let mut census = RefusalCensus::default();
        census.record(upstream("_RNvCsUp0", "core"));
        let report = census.report(1);
        // Exactly one occurrence: the class header. Not one per sample.
        assert_eq!(report.matches("[upstream-body]").count(), 1);
    }

    /// Trust (step 2 increment 3): the instance lane's two refusals. An
    /// assembly refusal is its own class; the producer refusing the instance's
    /// own body is producer coverage, the class `ExactAssembledBodyAbsent`
    /// already counts under.
    #[test]
    fn the_instance_lane_refusals_are_classified() {
        let assembly = FrontendRefusal::InstanceAssembly {
            symbol: "_RNvCsA".into(),
            detail: "`g`'s callee is refused".into(),
        };
        assert_eq!(assembly.class(), RefusalClass::InstanceAssembly);
        assert!(assembly.to_string().starts_with("[instance-assembly] "));
        let producer =
            |refusal: trust_thir_lower::InstanceRefusal| FrontendRefusal::InstanceProducerRefused {
                symbol: "_RNvCsP".into(),
                reason: format!("{refusal:?}"),
                refusal,
            };
        use trust_thir_lower::InstanceRefusal as R;
        // By variant: drops are increment 4's; the instance lane's own module gaps are its class;
        // everything else is producer coverage.
        assert_eq!(producer(R::LaneRefused("drop-bearing")).class(), RefusalClass::ElidedDrop);
        assert_eq!(producer(R::PendingConsts).class(), RefusalClass::InstanceAssembly);
        assert_eq!(
            producer(R::UnsignableCallee("c".into())).class(),
            RefusalClass::InstanceAssembly
        );
        assert_eq!(
            producer(R::NotSelfContained("m".into())).class(),
            RefusalClass::InstanceAssembly
        );
        assert_eq!(producer(R::ProducerDeclined("Ty")).class(), RefusalClass::ProducerDeclined);
        assert_eq!(producer(R::LaneRefused("symbolic")).class(), RefusalClass::ProducerDeclined);
        let producer = producer(R::PendingConsts);
        assert!(producer.to_string().contains("PendingConsts"));

        let mut census = RefusalCensus::default();
        census.record(assembly);
        census.record(producer);
        let report = census.report(2);
        assert!(RefusalClass::ElidedDrop.retired_by().contains("increment 4"));
        assert!(RefusalClass::UnfaithfulPanic.retired_by().contains("item P"));
        assert!(report.contains("[instance-assembly]"), "{report}");
        assert!(report.contains(RefusalClass::InstanceAssembly.retired_by()), "{report}");
        assert!(RefusalClass::InstanceAssembly.retired_by().contains("increment 5"));
        assert!(
            RefusalClass::GenericInstance.retired_by().contains("crate-module"),
            "the generic class now survives only in crate-module mode"
        );
    }

    /// Every class carries an actionable `retired_by`, and the report prints it
    /// for each class that actually occurred.
    #[test]
    fn report_prints_what_retires_each_occurring_class() {
        let mut census = RefusalCensus::default();
        census.record(upstream("_RNvCsUp0", "core"));
        census.record(generic("_RNvCsG0"));
        let report = census.report(2);
        assert!(report.contains(RefusalClass::UpstreamBody.retired_by()));
        assert!(report.contains(RefusalClass::GenericInstance.retired_by()));
        assert_eq!(report.matches("retired by:").count(), 2);
    }
}

// ---------------------------------------------------------------------------
// Crate-module-mode tests (gap G2)
//
// Everything exercised here is PURE: `trust_ir::Module` in, `Result` out. No
// `TyCtxt`, no `Session`, no rustc type. That is what makes the negative
// license gate — the one thing in this file whose failure mode COMPILES
// CLEANLY and ships wrong code — actually checkable, in this crate and in a
// standalone scratch crate outside the compiler build.
// ---------------------------------------------------------------------------
mod crate_module_tests {
    use std::collections::BTreeMap;

    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::BlockId;
    use trust_ir::{Block, BodyGate, Function, Module, Producer};

    use super::super::*;

    /// The fixture's stand-in for `tcx.symbol_name`: `k::f` -> `_RNvCk1f`, the
    /// spelling every link pair below uses.
    fn sym(def_path: &str) -> String {
        let leaf = def_path.rsplit("::").next().unwrap_or(def_path);
        format!("_RNvCk{}{leaf}", leaf.len())
    }

    /// `(def_path, gate, has a body)`. WS5.2: each function is NAMED by its
    /// link-time symbol ([`sym`]) and carries the def path as `display_path`,
    /// exactly as the crate producer publishes it.
    fn module_with(specs: &[(&str, Option<BodyGate>, bool)]) -> Module {
        let mut module = Module::new("k");
        // A bodyless external declaration pins the ABI, so `validate_module`
        // requires target info. The real producer sets this
        // (`crate_module.rs`: `module.target_info = Some(..)`).
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".to_string()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        let ty = module
            .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
            .expect("Module::add_func_type: test fixture");
        for (i, (name, gate, defined)) in specs.iter().enumerate() {
            let mut function = Function::new(FuncId::new(i as u32), sym(name), ty, BlockId::new(0));
            function.display_path = Some((*name).to_string());
            if *defined {
                let mut block = Block::new(BlockId::new(0));
                block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
                function.blocks.push(block);
            }
            function.producer = Some(Producer::TRust);
            function.body_gate = gate.clone();
            module.try_add_function(function).expect("Module::try_add_function: test fixture");
        }
        module
    }

    /// The producer's `display_path` index (`PublishedCrateModule::display_paths`).
    fn by_def_path(module: &Module) -> BTreeMap<String, FuncId> {
        module
            .functions
            .iter()
            .filter_map(|f| f.display_path.clone().map(|path| (path, f.id)))
            .collect()
    }

    /// The gate the producer stamps and the ONE authority this consumer
    /// recognizes. This used to spell `clean-kernel-tv`, which the producer
    /// never stamps on this lane: trust-ir's validator now binds that
    /// authority to a kernel-replayed `clean_backend_tv` certificate, and the
    /// recognition leg refuses it anyway, so every fixture built on it was
    /// refused before reaching the leg its test is about.
    fn gated() -> Option<BodyGate> {
        Some(BodyGate::Gated { authority: RECOGNIZED_GATE_AUTHORITY.to_string(), evidence: None })
    }

    fn prep(
        module: &Module,
        licensed: &[FuncId],
        refusal: Option<&str>,
        links: &[(&str, &str)],
    ) -> Result<PreparedCrateModule, String> {
        let links: Vec<(String, String)> =
            links.iter().map(|(a, b)| ((*a).to_string(), (*b).to_string())).collect();
        prepare_crate_module("k", module, &by_def_path(module), &[], licensed, refusal, &links)
    }

    // ---- (b) the negative gate itself ----------------------------------

    /// The three states are three values, and only one of them fails to
    /// withhold.
    #[test]
    fn the_gate_is_three_valued_and_only_gated_withholds_nothing() {
        assert_eq!(body_gate_verdict(None), GateVerdict::NoClaim);
        assert_eq!(body_gate_verdict(Some(&BodyGate::Ungated)), GateVerdict::Ungated);
        assert_eq!(
            body_gate_verdict(Some(&BodyGate::Gated {
                authority: "a".to_string(),
                evidence: None
            })),
            GateVerdict::NotWithheld { authority: "a".to_string() }
        );
        assert!(body_gate_verdict(None).withholds(), "an absent claim must withhold");
        assert!(
            body_gate_verdict(Some(&BodyGate::Ungated)).withholds(),
            "an affirmative `ungated` must withhold"
        );
        assert!(
            !body_gate_verdict(Some(&BodyGate::Gated {
                authority: "a".to_string(),
                evidence: None
            }))
            .withholds()
        );
    }

    /// The four verdict tags are a vocabulary: they appear in diagnostics, so
    /// two of them sharing a spelling would make a refusal unclassifiable in
    /// exactly the way the class tags exist to prevent.
    #[test]
    fn the_verdict_tags_are_distinct() {
        let tags = [
            GateVerdict::NotWithheld { authority: "a".to_string() }.tag(),
            GateVerdict::Ungated.tag(),
            GateVerdict::NoClaim.tag(),
            GateVerdict::BlankAuthority.tag(),
        ];
        let mut sorted = tags.to_vec();
        sorted.sort_unstable();
        let distinct = sorted.len();
        sorted.dedup();
        assert_eq!(sorted.len(), distinct, "two verdicts share a tag: {tags:?}");
        assert!(tags.iter().all(|t| !t.is_empty()));
    }

    /// STRICTER than `trust_ir::BodyGate::is_gated`, deliberately: that reads
    /// the discriminant, and a positive license naming no gate is not a gate.
    #[test]
    fn a_blank_authority_is_not_a_gate() {
        let blank = BodyGate::Gated { authority: "   ".to_string(), evidence: None };
        assert!(blank.is_gated(), "the format crate reads the discriminant alone");
        assert_eq!(body_gate_verdict(Some(&blank)), GateVerdict::BlankAuthority);
        assert!(body_gate_verdict(Some(&blank)).withholds());
    }

    /// THE PROPERTY THE WHOLE GAP TURNS ON: `Ungated` and absent are never
    /// collapsed. Different variants, different classes, different counts,
    /// different `retired_by`.
    #[test]
    fn ungated_and_no_claim_are_never_collapsed() {
        let ungated = FrontendRefusal::UngatedBody { symbol: "_RNvC1a".to_string(), func: 0 };
        let absent = FrontendRefusal::UnlicensedBody { symbol: "_RNvC1b".to_string(), func: 1 };
        assert_ne!(ungated.class(), absent.class());
        assert_ne!(ungated.class().tag(), absent.class().tag());
        assert_ne!(ungated.class().retired_by(), absent.class().retired_by());
        assert!(ungated.to_string().contains("AFFIRMATIVE"));
        assert!(absent.to_string().contains("NO licensing claim"));

        let module = module_with(&[
            ("a", Some(BodyGate::Ungated), true),
            ("b", None, true),
            ("c", gated(), true),
        ]);
        let report = ModuleGateReport::of(&module);
        assert_eq!(report.ungated.len(), 1);
        assert_eq!(report.no_claim.len(), 1);
        assert_eq!(report.gated, 1);
        assert!(!report.is_positive());
        let text = report.refusal();
        assert!(text.contains("AFFIRMATIVELY UNGATED"), "{text}");
        assert!(text.contains("MAKE NO LICENSING CLAIM AT ALL"), "{text}");
        assert!(text.contains("FuncId 0 `_RNvCk1a`"), "{text}");
        assert!(text.contains("FuncId 1 `_RNvCk1b`"), "{text}");
        assert_ne!(
            text.find("AFFIRMATIVELY UNGATED"),
            text.find("MAKE NO LICENSING CLAIM AT ALL"),
            "the two must be separate lines"
        );
    }

    /// A bodyless declaration is not a codegen subject, so it must not
    /// withhold. (Otherwise every module with one external symbol refuses.)
    #[test]
    fn a_declaration_needs_no_license() {
        let module = module_with(&[("decl", None, false), ("body", gated(), true)]);
        let report = ModuleGateReport::of(&module);
        assert_eq!(report.declarations, 1);
        assert_eq!(report.gated, 1);
        assert!(report.is_positive(), "{}", report.refusal());
    }

    /// Our walk and `trust_ir_build::validate::validate_module_for_codegen`
    /// must agree on every shape. Two independent readings of one field.
    #[test]
    fn our_walk_agrees_with_the_format_crate() {
        use trust_ir_build::validate::{ValidationError, validate_module_for_codegen};
        for specs in [
            vec![("a", gated(), true)],
            vec![("a", None, true)],
            vec![("a", Some(BodyGate::Ungated), true)],
            vec![("a", None, true), ("b", Some(BodyGate::Ungated), true), ("c", gated(), true)],
            vec![("a", None, false), ("b", gated(), true)],
        ] {
            let module = module_with(&specs);
            let license: Vec<_> = validate_module_for_codegen(&module)
                .into_iter()
                .filter(|e| {
                    matches!(
                        e,
                        ValidationError::UngatedBodyForCodegen { .. }
                            | ValidationError::UnlicensedBodyForCodegen { .. }
                    )
                })
                .collect();
            let report = ModuleGateReport::of(&module);
            cross_check_license(&report, &license).unwrap_or_else(|e| panic!("{specs:?}: {e}"));
        }
    }

    #[test]
    fn a_cross_check_disagreement_refuses() {
        let module = module_with(&[("a", None, true)]);
        let report = ModuleGateReport::of(&module);
        // Pretend the format crate reported nothing.
        let err = cross_check_license(&report, &[]).unwrap_err();
        assert!(err.contains("DISAGREEMENT"), "{err}");
        assert!(err.contains("NOTHING is lowered"), "{err}");
    }

    /// A positive gate from any other authority is a refusal of the whole
    /// lowering context, never a pass (the recognition leg). The foreign name
    /// carries no evidence rule in trust-ir, so this reaches the leg itself
    /// rather than the validator.
    #[test]
    fn a_foreign_gate_authority_refuses_the_whole_module() {
        let foreign = Some(BodyGate::Gated {
            authority: "foreign-producer-gate".to_string(),
            evidence: None,
        });
        let module = module_with(&[("k::f", gated(), true), ("k::g", foreign, true)]);
        let err =
            prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1f"), ("k::g", "_RNvCk1g")])
                .unwrap_err();
        assert!(err.contains("does not recognize"), "{err}");
        // WS5.2: the row is named by its link-time symbol, then the def path it displays.
        assert!(err.contains("`_RNvCk1g` (`k::g`) gated by \"foreign-producer-gate\""), "{err}");
    }

    /// Plan step 3.4 (owner ruling D37): a Clean-origin body in the published module — stamped
    /// `clean-carrier-gate` (a tier-`gate` row) or `Ungated` (below `gate`) — no longer withdraws
    /// the crate module through legs 3 and 3b. This lane emits no Clean body, so it is a bodyless
    /// declaration in the private lowering context (producer kept, so the converter still refuses
    /// a call to it by name), and the Rust body prepares. Before 3.4 both modules were refused
    /// whole (measured: t1's `rust_only` `[crate-module-unavailable]`). A body of any OTHER
    /// producer with the same claims still refuses the whole module (control).
    #[test]
    fn a_clean_origin_body_is_a_declaration_in_the_crate_module_lowering_context() {
        let carrier =
            Some(BodyGate::Gated { authority: "clean-carrier-gate".to_string(), evidence: None });
        for clean_gate in [carrier.clone(), Some(BodyGate::Ungated)] {
            let mut module = module_with(&[("k::rust", gated(), true), ("cleanWsum", None, true)]);
            module.functions[1].producer = Some(Producer::Clean);
            module.functions[1].body_gate = clean_gate.clone();
            // The join's disclosure row for it: `fn:N` must name a BODIED function, so leg 2
            // validates the module as published, before the Clean body leaves the context
            // (measured on a stage 1 of this branch: validating the stripped clone refused t1's
            // whole crate module, "disclosure row fn:3 names no bodied function").
            let mut disclosure = trust_ir::SpecModule::new(
                trust_thir_lower::clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME,
            );
            disclosure.invariants.push(trust_ir::SpecInvariant::new("fn:1", "{}"));
            module.spec_modules.push(disclosure);
            let prepared = prep(&module, &[FuncId::new(0)], None, &[("k::rust", "_RNvCk4rust")])
                .unwrap_or_else(|err| panic!("{clean_gate:?}: the Rust body must prepare: {err}"));
            let clean = prepared.module.function_by_id(FuncId::new(1)).unwrap();
            assert!(clean.is_declaration(), "{clean_gate:?}: no Clean bytes in the context");
            assert_eq!(clean.producer, Some(Producer::Clean), "the converter refuses it by name");
            assert_eq!(clean.body_gate, None);
            assert!(!prepared.licensed.contains(&FuncId::new(1)));
            assert_eq!(
                admit_from_crate_module(&prepared, "k::rust", "_RNvCk4rust").unwrap(),
                FuncId::new(0)
            );
            // The producer's module is never mutated.
            assert!(!module.functions[1].is_declaration());
            assert_eq!(module.functions[1].body_gate, clean_gate);
        }
        // Control: the same claims on a non-Clean body still refuse the whole module (leg 3b for
        // the foreign authority, leg 3 for `Ungated`).
        for (foreign, needle) in
            [(carrier, "does not recognize"), (Some(BodyGate::Ungated), "UNGATED")]
        {
            let module = module_with(&[("k::rust", gated(), true), ("k::later", foreign, true)]);
            let err =
                prep(&module, &[FuncId::new(0)], None, &[("k::rust", "_RNvCk4rust")]).unwrap_err();
            assert!(err.contains(needle), "{err}");
        }
    }

    // ---- (a) the lowering context ---------------------------------------

    #[test]
    fn a_fully_gated_module_prepares_when_every_name_is_the_mangled_symbol() {
        let module = module_with(&[("k::f", gated(), true), ("k::g", gated(), true)]);
        let prepared = prep(
            &module,
            &[FuncId::new(0), FuncId::new(1)],
            None,
            &[("k::f", "_RNvCk1f"), ("k::g", "_RNvCk1g")],
        )
        .expect("a fully gated, fully licensed module must prepare");
        assert_eq!(prepared.link_name(FuncId::new(0)), Some("_RNvCk1f"));
        assert_eq!(prepared.module.function_by_id(FuncId::new(0)).unwrap().name, "_RNvCk1f");
        assert_eq!(prepared.module.function_by_id(FuncId::new(1)).unwrap().name, "_RNvCk1g");
        // WS5.2: leg 4 is a CHECK, not a rename — the prepared context IS the
        // producer's module, byte for byte.
        assert_eq!(*prepared.module, module);
        assert_eq!(admit_from_crate_module(&prepared, "k::f", "_RNvCk1f").unwrap(), FuncId::new(0));
        // BOTH functions are in the context, which is the whole point: an
        // intra-module callee resolves.
        assert_eq!(prepared.module.functions.len(), 2);
        assert_eq!(prepared.licensed_count(), 2);
    }

    /// ONE unlicensed body anywhere refuses the WHOLE module — including a
    /// function this compilation never intended to emit. That is the
    /// inlined-callee hole being closed by making the reachability question
    /// vacuous.
    #[test]
    fn one_unlicensed_body_refuses_the_whole_module() {
        let module = module_with(&[("k::f", gated(), true), ("k::g", None, true)]);
        let err = prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1f")]).unwrap_err();
        assert!(err.contains("NO LICENSING CLAIM"), "{err}");
        assert!(err.contains("`k::g`"), "the refusal must name the offender: {err}");
    }

    #[test]
    fn one_ungated_body_refuses_the_whole_module() {
        let module =
            module_with(&[("k::f", gated(), true), ("k::g", Some(BodyGate::Ungated), true)]);
        let err = prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1f")]).unwrap_err();
        assert!(err.contains("AFFIRMATIVELY UNGATED"), "{err}");
    }

    #[test]
    fn a_producer_license_refusal_refuses_the_whole_module() {
        let module = module_with(&[("k::f", gated(), true)]);
        let err = prep(&module, &[], Some("clean-origin rows present"), &[("k::f", "_RNvCk1f")])
            .unwrap_err();
        assert!(err.contains("REFUSED the codegen license"), "{err}");
        assert!(err.contains("clean-origin rows present"), "{err}");
    }

    /// Two functions claiming one symbol is refused. Since WS5.2 the name IS
    /// the symbol, so the format crate's `DuplicateFunctionSymbol` (leg 2,
    /// "share the link symbol") refuses the module before leg 4's own claim
    /// check is reached.
    #[test]
    fn two_functions_may_not_claim_one_link_symbol() {
        let mut module = module_with(&[("k::f", gated(), true), ("k::g", gated(), true)]);
        module.functions[1].name = "_RNvCk1f".to_string();
        let err = prep(
            &module,
            &[FuncId::new(0), FuncId::new(1)],
            None,
            &[("k::f", "_RNvCk1f"), ("k::g", "_RNvCk1f")],
        )
        .unwrap_err();
        assert!(err.contains("share the link symbol \"_RNvCk1f\""), "{err}");
    }

    /// WS5.2 NEGATIVE TWIN: a producer row whose name is not the symbol this
    /// compilation mangles for its def path refuses the WHOLE module, naming
    /// both spellings — it is never renamed into agreement.
    #[test]
    fn a_producer_name_that_is_not_this_compilations_symbol_refuses_the_module() {
        let module = module_with(&[("k::f", gated(), true)]);
        let err = prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1WRONG")]).unwrap_err();
        assert!(err.contains("`_RNvCk1f`"), "the producer's spelling is named: {err}");
        assert!(err.contains("`_RNvCk1WRONG`"), "this compilation's spelling is named: {err}");
        assert!(err.contains("nothing is lowered"), "{err}");
    }

    /// WS5.2 MUTATION CONTROL (roadmap: "swap two entries of the symbol map and
    /// the frontend leg-4 check refuses"). The swap is the exact corruption the
    /// old rename would have silently written into the private clone.
    #[test]
    fn swapping_two_symbol_map_entries_is_refused_by_the_leg_4_check() {
        let module = module_with(&[("k::f", gated(), true), ("k::g", gated(), true)]);
        let straight = prep(
            &module,
            &[FuncId::new(0), FuncId::new(1)],
            None,
            &[("k::f", "_RNvCk1f"), ("k::g", "_RNvCk1g")],
        );
        assert!(straight.is_ok(), "the unswapped map must prepare: {:?}", straight.err());
        let err = prep(
            &module,
            &[FuncId::new(0), FuncId::new(1)],
            None,
            &[("k::f", "_RNvCk1g"), ("k::g", "_RNvCk1f")],
        )
        .unwrap_err();
        assert!(err.contains("disagree about the item's identity"), "{err}");
    }

    // ---- per-item admission ---------------------------------------------

    #[test]
    fn a_def_path_absent_from_the_crate_module_is_refused() {
        let module = module_with(&[("k::f", gated(), true)]);
        let prepared = prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1f")]).unwrap();
        let err = admit_from_crate_module(&prepared, "k::missing", "_RNvCk7missing").unwrap_err();
        assert_eq!(err.class(), RefusalClass::ProducerDeclined);
        assert!(matches!(err, FrontendRefusal::NotInCrateModule { .. }));
    }

    /// THE DIRECTION OF THE GATE. `Gated` withheld nothing, and the item is
    /// STILL refused, because permission comes from the producer's inventory.
    /// Producer-supplied metadata never grants authority.
    #[test]
    fn a_gated_body_outside_the_producers_inventory_is_still_refused() {
        let module = module_with(&[("k::f", gated(), true)]);
        let prepared = prep(&module, &[], None, &[("k::f", "_RNvCk1f")]).unwrap();
        let err = admit_from_crate_module(&prepared, "k::f", "_RNvCk1f").unwrap_err();
        assert_eq!(err.class(), RefusalClass::UnlicensedByProducer);
        assert!(err.to_string().contains("does not grant what the inventory withholds"), "{err}");
    }

    #[test]
    fn a_declaration_is_never_a_codegen_subject() {
        let module = module_with(&[("k::ext", None, false), ("k::f", gated(), true)]);
        let prepared = prep(
            &module,
            &[FuncId::new(1)],
            None,
            &[("k::f", "_RNvCk1f"), ("k::ext", "_RNvCk3ext")],
        )
        .unwrap();
        let err = admit_from_crate_module(&prepared, "k::ext", "_RNvCk3ext").unwrap_err();
        assert!(matches!(err, FrontendRefusal::DeclarationOnlyInCrateModule { .. }));
        assert_eq!(err.class(), RefusalClass::ProducerDeclined);
    }

    /// Emitting one function under another's symbol is the silent corruption
    /// `compiled_module` guards at the far end; refuse it at admission too.
    #[test]
    fn admission_refuses_a_symbol_that_is_not_this_functions_link_name() {
        let module = module_with(&[("k::f", gated(), true)]);
        let prepared = prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1f")]).unwrap();
        let err = admit_from_crate_module(&prepared, "k::f", "_RNvCk1WRONG").unwrap_err();
        assert_eq!(err.class(), RefusalClass::MalformedProducerModule);
        assert!(err.to_string().contains("_RNvCk1f"), "{err}");
    }

    /// The per-item gate arms are unreachable through a module that PREPARED
    /// (the whole-module gate caught them first) — which is exactly why the
    /// whole-module gate is the load-bearing one. Exercise them directly so
    /// they are not dead code with an untested classification.
    #[test]
    fn the_per_item_gate_arms_are_exercised_directly() {
        let module = module_with(&[("k::f", gated(), true)]);
        let mut prepared = prep(&module, &[FuncId::new(0)], None, &[("k::f", "_RNvCk1f")]).unwrap();

        std::sync::Arc::make_mut(&mut prepared.module)
            .function_by_id_mut(FuncId::new(0))
            .unwrap()
            .body_gate = None;
        let err = admit_from_crate_module(&prepared, "k::f", "_RNvCk1f").unwrap_err();
        assert_eq!(err.class(), RefusalClass::UnlicensedBody);

        std::sync::Arc::make_mut(&mut prepared.module)
            .function_by_id_mut(FuncId::new(0))
            .unwrap()
            .body_gate = Some(BodyGate::Ungated);
        let err = admit_from_crate_module(&prepared, "k::f", "_RNvCk1f").unwrap_err();
        assert_eq!(err.class(), RefusalClass::UngatedBody);

        std::sync::Arc::make_mut(&mut prepared.module)
            .function_by_id_mut(FuncId::new(0))
            .unwrap()
            .body_gate = Some(BodyGate::Gated { authority: " ".to_string(), evidence: None });
        let err = admit_from_crate_module(&prepared, "k::f", "_RNvCk1f").unwrap_err();
        assert_eq!(err.class(), RefusalClass::MalformedProducerModule);
        assert!(matches!(err, FrontendRefusal::MalformedBodyGate { .. }));
    }

    /// THE MEASURED STATE OF THE WORLD ON 2026-09-01, when nothing in `~/trust`
    /// stamped `trust_ir::Function::body_gate` and every published crate module
    /// was all-`None`, so this mode refused every crate. The producer has stamped
    /// since (`trust_thir_lower::crate_module::stamp_codegen_license`; plan step
    /// 3.0 corrected this comment); the fixture keeps the all-`None` shape, which
    /// must still refuse and say what retires it.
    #[test]
    fn todays_producer_output_shape_refuses_and_says_what_retires_it() {
        let module = module_with(&[("k::main", None, true), ("k::helper", None, true)]);
        let err = prep(
            &module,
            &[FuncId::new(0), FuncId::new(1)],
            None,
            &[("k::main", "_RNvCk4main"), ("k::helper", "_RNvCk6helper")],
        )
        .unwrap_err();
        assert!(err.contains("2 MAKE NO LICENSING CLAIM"), "{err}");
        assert!(!err.contains("AFFIRMATIVELY UNGATED"), "no ungated body here: {err}");
        assert!(
            err.contains(RefusalClass::UnlicensedBody.retired_by()),
            "the refusal must name what retires it: {err}"
        );
    }

    /// A whole-module refusal must still be COUNTED per item, never
    /// short-circuited, or `refused == reachable` stops being true.
    #[test]
    fn a_whole_module_refusal_feeds_the_same_census() {
        let mut census = RefusalCensus::default();
        for i in 0..5 {
            census.record(FrontendRefusal::CrateModuleUnavailable {
                symbol: format!("_RNvCsX{i}"),
                detail: "the producer REFUSED the codegen license".to_string(),
            });
        }
        assert_eq!(census.len(), 5);
        assert_eq!(census.count(RefusalClass::CrateModuleUnavailable), 5);
        let report = census.report(5);
        assert!(report.contains("[crate-module-unavailable]"), "{report}");
        assert!(report.contains("refused 5 of 5"), "{report}");
        assert!(report.contains("never falls back to the MIR path"), "{report}");
    }

    /// The three crate-module license classes are separately countable in one
    /// census, which is the whole reason they are classes and not one message.
    #[test]
    fn the_license_classes_are_separately_counted() {
        let mut census = RefusalCensus::default();
        for i in 0..7 {
            census
                .record(FrontendRefusal::UnlicensedBody { symbol: format!("_RNvCsA{i}"), func: i });
        }
        for i in 0..3 {
            census.record(FrontendRefusal::UngatedBody { symbol: format!("_RNvCsB{i}"), func: i });
        }
        census.record(FrontendRefusal::UnlicensedByProducer {
            symbol: "_RNvCsC0".to_string(),
            func: 9,
        });
        assert_eq!(census.count(RefusalClass::UnlicensedBody), 7);
        assert_eq!(census.count(RefusalClass::UngatedBody), 3);
        assert_eq!(census.count(RefusalClass::UnlicensedByProducer), 1);
        let report = census.report(11);
        let a = report.find("[unlicensed-body]").expect("missing");
        let b = report.find("[ungated-body]").expect("missing");
        let c = report.find("[unlicensed-by-producer]").expect("missing");
        assert!(a < b && b < c, "classes must order by descending count");
    }
}

// ---------------------------------------------------------------------------
// R-8 ledger item 1: a function whose trust-ir can reach a runtime check is
// refused (F1 lowers the check to a bare trap).
// ---------------------------------------------------------------------------
mod runtime_check_tests {
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, ValueId};
    use trust_ir::{Block, Constant, Function, Module, Ty};

    use super::super::*;

    fn body(id: u32, name: &str, callee: Option<u32>, assert: bool) -> Function {
        let mut f = Function::new(
            FuncId::new(id),
            name,
            trust_ir::value::FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
        let mut result = ValueId::new(0);
        if let Some(c) = callee {
            b.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(c), args: vec![ValueId::new(0)] })
                    .with_result(ValueId::new(1)),
            );
            result = ValueId::new(1);
        }
        if assert {
            b.body.push(
                InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                    .with_result(ValueId::new(2)),
            );
            b.body.push(
                InstrNode::new(Inst::Assert {
                    cond: ValueId::new(2),
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                })
                .with_proof(trust_ir::proof::ProofAnnotation::NoOverflow),
            );
        }
        b.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
        f.blocks.push(b);
        f
    }

    fn module(functions: Vec<Function>) -> Module {
        let mut m = Module::new("k");
        m.add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
        for f in functions {
            m.try_add_function(f).expect("Module::try_add_function: test fixture");
        }
        m
    }

    #[test]
    fn a_runtime_check_in_the_item_or_any_callee_it_inlines_is_found() {
        let clean = module(vec![body(0, "f", Some(1), false), body(1, "g", None, false)]);
        assert_eq!(reachable_runtime_check(&clean, FuncId::new(0)), None);
        let own = module(vec![body(0, "f", None, true)]);
        let found = reachable_runtime_check(&own, FuncId::new(0)).expect("the item's own check");
        assert!(found.contains("`f`") && found.contains("NoOverflow"), "{found}");
        // The check lives in a CALLEE the leaf inliner would splice into the item.
        let callee = module(vec![body(0, "f", Some(1), false), body(1, "g", None, true)]);
        let found = reachable_runtime_check(&callee, FuncId::new(0)).expect("the callee's check");
        assert!(found.contains("`g`"), "{found}");
        // An unrelated function's check is not the item's.
        let unrelated = module(vec![body(0, "f", None, false), body(1, "g", None, true)]);
        assert_eq!(reachable_runtime_check(&unrelated, FuncId::new(0)), None);
        // `Unreachable` is not a panic: it stands only where MIR has `Unreachable`, and reaching
        // it is UB on both paths.
        let mut unreachable = module(vec![body(0, "f", None, false)]);
        unreachable.functions[0].blocks[0].body.insert(0, InstrNode::new(Inst::Unreachable));
        assert_eq!(reachable_runtime_check(&unreachable, FuncId::new(0)), None);
        // The check's SOURCE location is named when the producer stamped one.
        let mut located = module(vec![body(0, "f", None, true)]);
        located.files = vec!["src/lib.rs".to_string()];
        for node in &mut located.functions[0].blocks[0].body {
            if matches!(node.inst, Inst::Assert { .. }) {
                node.span = Some(trust_ir::value::SourceSpan { file: 0, line: 3, col: 5 });
            }
        }
        let found = reachable_runtime_check(&located, FuncId::new(0)).expect("the check");
        assert!(found.ends_with(" at src/lib.rs:3:5"), "{found}");
    }

    /// ONE refusal for every lane: `refuse_unfaithful_panic` is the only constructor of the
    /// variant, and both lowering tails (`lower_from_module`: handoff and instance lanes;
    /// `lower_from_crate_module`) call it. A check reached only through a CALLEE refuses too.
    #[test]
    fn one_refusal_function_serves_every_lane() {
        let callee = module(vec![body(0, "f", Some(1), false), body(1, "g", None, true)]);
        let refused = refuse_unfaithful_panic(&callee, FuncId::new(0), "_RNvCs0_1k1f")
            .expect_err("a check in a callee is the item's");
        assert_eq!(refused.class(), RefusalClass::UnfaithfulPanic);
        let line = refused.sample_line();
        assert!(line.contains("in `g`") && line.contains("would lower to a bare trap"), "{line}");
        let clean = module(vec![body(0, "f", Some(1), false), body(1, "g", None, false)]);
        assert!(refuse_unfaithful_panic(&clean, FuncId::new(0), "_RNvCs0_1k1f").is_ok());

        let source = include_str!("../trust_ir_frontend.rs");
        let code: String = source
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(
            code.matches("FrontendRefusal::UnfaithfulPanic").count(),
            1,
            "only `refuse_unfaithful_panic` builds the variant"
        );
        let span = |from: &str, to: &str| {
            let start = code.find(from).unwrap_or_else(|| panic!("no `{from}`"));
            let end = start + code[start..].find(to).unwrap_or_else(|| panic!("no `{to}`"));
            code[start..end].to_string()
        };
        for (tail, next) in [
            ("fn lower_from_module<", "lower_module_to_lir_with_abi_cross_check("),
            ("fn lower_from_crate_module<", "lower_module_to_lir_with_abi_cross_check("),
        ] {
            assert!(
                span(tail, next).contains("refuse_unfaithful_panic("),
                "`{tail}` must refuse an unfaithful panic before it lowers"
            );
        }
    }

    #[test]
    fn the_refusal_names_its_class_and_the_retiring_work_item() {
        let refusal = FrontendRefusal::UnfaithfulPanic {
            symbol: "_RNvCs0_1k1f".into(),
            detail: "reaches a runtime check (`Assert` NoOverflow) in `f`".into(),
        };
        assert_eq!(refusal.class(), RefusalClass::UnfaithfulPanic);
        let rendered = refusal.to_string();
        assert!(rendered.starts_with("[unfaithful-panic] "), "{rendered}");
        assert!(rendered.contains("every output-gate policy"), "{rendered}");
        assert!(rendered.contains("would lower to a bare trap"), "{rendered}");
    }
}

// ---------------------------------------------------------------------------
// Trust (plan step 3.0, docs/design/2026-10-02-step3-lean-through-trust-ir.md §9): the
// `[clean-below-gate]` class. Everything here is pure: the disclosure reader, the instance-lane
// detail classifier, the converter wording and the rendered refusal.
// ---------------------------------------------------------------------------
mod clean_below_gate_tests {
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::{FuncTy, Ty};
    use trust_ir::value::BlockId;
    use trust_ir::{Block, Function, Module, Producer, SpecInvariant, SpecModule};

    use super::super::clean_below_gate::*;
    use super::super::*;

    const GATE_ROW: &str = "{\"schema\":\"trust.clean-origin-disclosure.v1\",\
        \"def_path\":\"m::cleanWsum\",\"clean_name\":\"cleanWsum\",\"shape\":\"wrapping-binop\",\
        \"tier\":\"gate\",\"body_gate\":\"carrier-faithful\"}";
    const SELECT_ROW: &str = "{\"schema\":\"trust.clean-origin-disclosure.v1\",\
        \"def_path\":\"m::cleanMin\",\"clean_name\":\"cleanMin\",\"shape\":\"select\",\
        \"tier\":\"structural\",\"body_gate\":\"ungated\",\"tv_note\":\"a \\\"quoted\\\" note\"}";
    const SKIPPED_ROW: &str = "{\"schema\":\"trust.clean-origin-disclosure.v1\",\
        \"def_path\":\"m::half\",\"shape\":\"rust-call-chain\",\"reason\":\"why\"}";

    /// A module shaped like the assembled handoff of `tests/run-make/trust-cg-clean-origin-below-gate`:
    /// a Rust caller (FuncId 0), a retired declaration (1), and the appended Clean rows
    /// `cleanWsum` (2) and `cleanMin` (3), with the clean-origin disclosure.
    fn handoff() -> Module {
        let mut module = Module::new("clean_below_gate");
        let ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::U64, Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        for (i, (name, producer)) in [
            ("calls_clean", Producer::TRust),
            ("m::cleanWsum::<shadowed>", Producer::TRust),
            ("cleanWsum", Producer::Clean),
            ("cleanMin", Producer::Clean),
        ]
        .into_iter()
        .enumerate()
        {
            let mut function = Function::new(FuncId::new(i as u32), name, ty, BlockId::new(0));
            if i != 1 {
                let mut block = Block::new(BlockId::new(0));
                block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
                function.blocks.push(block);
            }
            function.producer = Some(producer);
            module.try_add_function(function).expect("Module::try_add_function: test fixture");
        }
        let mut disclosure =
            SpecModule::new(trust_thir_lower::clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME);
        disclosure.invariants.push(SpecInvariant::new("fn:2", GATE_ROW));
        disclosure.invariants.push(SpecInvariant::new("fn:3", SELECT_ROW));
        disclosure.invariants.push(SpecInvariant::new("skipped:9", SKIPPED_ROW));
        disclosure
            .invariants
            .push(SpecInvariant::new("linked:1", "{\"def_path\":\"m::cleanWsum\"}"));
        module.spec_modules.push(disclosure);
        // A user spec module that happens to carry a `fn:` invariant is not the disclosure.
        let mut other = SpecModule::new("user::spec");
        other.invariants.push(SpecInvariant::new("fn:0", GATE_ROW));
        module.spec_modules.push(other);
        module
    }

    #[test]
    fn the_json_reader_undoes_the_disclosure_escaping() {
        assert_eq!(json_string_field(GATE_ROW, "tier").as_deref(), Some("gate"));
        assert_eq!(json_string_field(SELECT_ROW, "tv_note").as_deref(), Some("a \"quoted\" note"));
        assert_eq!(
            json_string_field(r#"{"a":"x\\y\n\u0001z"}"#, "a").as_deref(),
            Some("x\\y\n\u{1}z")
        );
        assert_eq!(json_string_field(GATE_ROW, "absent"), None);
        assert_eq!(json_string_field(r#"{"a":"unterminated"#, "a"), None);
    }

    #[test]
    fn disclosed_rows_reads_emitted_and_skipped_rows_of_the_disclosure_only() {
        let rows = disclosed_rows(&handoff());
        assert_eq!(rows.len(), 3, "{rows:?}");
        assert_eq!(
            rows[0],
            DisclosedRow {
                func_id: Some(2),
                def_path: "m::cleanWsum".into(),
                clean_name: Some("cleanWsum".into()),
                shape: Some("wrapping-binop".into()),
                tier: "gate".into(),
            }
        );
        assert_eq!(rows[1].tier, "structural");
        assert_eq!(rows[1].shape.as_deref(), Some("select"));
        assert_eq!(rows[2].func_id, None);
        assert_eq!(rows[2].tier, "skipped");
        assert_eq!(rows[2].def_path, "m::half");
        assert!(disclosed_rows(&Module::new("no_islands")).is_empty());
    }

    /// The converter's `CleanOriginBelowCodegenGate` becomes `[clean-below-gate]`, worded from the
    /// lowering context's own disclosure, with the converter's message kept verbatim.
    #[test]
    fn the_converter_refusal_names_the_row_tier_and_shape() {
        let converter = "Clean-origin trust-ir function `cleanWsum` is not admitted to codegen \
                         (it is a callee of `_RNvCs1k11calls_clean` and would have been inlined)";
        let refusal =
            converter_refusal("_RNvCs1k11calls_clean", &handoff(), "cleanWsum", converter.into());
        assert_eq!(refusal.class(), RefusalClass::CleanBelowGate);
        let FrontendRefusal::CleanBelowGate { row, .. } = &refusal else { panic!("{refusal:?}") };
        assert_eq!(row.role, CleanRole::Reaches);
        assert_eq!(row.def, "m::cleanWsum");
        assert_eq!(row.row.as_ref().map(|r| r.tier.as_str()), Some("gate"));
        let rendered = refusal.to_string();
        assert!(rendered.starts_with("[clean-below-gate] `_RNvCs1k11calls_clean`: "), "{rendered}");
        for expected in [
            "reaches the Clean-origin def `m::cleanWsum`",
            "tier `gate`, shape `wrapping-binop`",
            converter,
            "Options: (1) build this crate on the MIR lane",
            "this trust-ir-frontend unit",
            "never falls back to the MIR path",
        ] {
            assert!(rendered.contains(expected), "missing `{expected}` in {rendered}");
        }
        // The census sample names the row too, and the class's retiring work is plan step 3.
        let sample = refusal.sample_line();
        assert!(sample.contains("tier `gate`, shape `wrapping-binop`"), "{sample}");
        let mut census = RefusalCensus::default();
        census.record(refusal);
        let report = census.report(4);
        assert!(report.contains("[clean-below-gate]"), "{report}");
        assert!(report.contains(RefusalClass::CleanBelowGate.retired_by()), "{report}");
        assert!(RefusalClass::CleanBelowGate.retired_by().contains("step 3.4"));
        // A Clean function the disclosure does not list is still named, honestly unrecorded.
        let bare = converter_refusal("s", &Module::new("x"), "cleanZ", "c".into());
        assert!(bare.to_string().contains("not recorded on this lane"), "{bare}");
        assert!(bare.to_string().contains("`cleanZ`"), "{bare}");
    }

    #[test]
    fn the_instance_lane_detail_is_classified_by_clean_symbol_or_by_its_frozen_phrase() {
        let rows = disclosed_rows(&handoff());
        let symbols = vec![("_RNvNtCs1k1m9cleanWsum".to_string(), "m::cleanWsum".to_string())];
        // Verification off: the callee is the Clean def itself, named by its mangled symbol.
        let off = "`_RNvCs1k11calls_clean`'s callee `_RNvNtCs1k1m9cleanWsum` is refused: monomorphic \
                   callee `_RNvNtCs1k1m9cleanWsum` has no assembled handoff body (ExactBodyAbsent { \
                   def_index: 4, definition: \"511b\" })";
        assert_eq!(
            instance_lane_names_clean(off, &symbols, &rows),
            Some(Some("m::cleanWsum".into()))
        );
        // Verification on: the frozen phrase, with the Clean function's name.
        let edge =
            "edge FuncId(1) `m::cleanMin::<shadowed>` maps to the Clean-origin body `cleanMin`";
        assert_eq!(
            instance_lane_names_clean(edge, &symbols, &rows),
            Some(Some("m::cleanMin".into()))
        );
        // The frozen phrase without a nameable Clean row is still a Clean refusal.
        let reach = "monomorphic callee `_RNvCs1k1g` reaches a Clean-origin body, which is not \
                     admitted to codegen";
        assert_eq!(instance_lane_names_clean(reach, &symbols, &rows), Some(None));
        // An unrelated refusal is left alone.
        let upstream = "`_RNvCs1k3inc`'s callee `_RNvMs7_core3numy12wrapping_add` is refused: it is \
                        an upstream body";
        assert_eq!(instance_lane_names_clean(upstream, &symbols, &rows), None);
    }

    /// The frozen instance lane (owner ruling D17, byte-identical) spells the two phrases the
    /// classifier reads. A waiver that rewords them must move this pin and the classifier together.
    #[test]
    fn the_frozen_instance_lane_still_spells_the_phrases_the_classifier_reads() {
        let frozen = include_str!("instance_assembly.rs");
        assert!(frozen.contains("reaches a Clean-origin body, which is not admitted"));
        assert!(frozen.contains("maps to the Clean-origin body `{}`"));
        assert!(frozen.contains("has no assembled handoff body"));
    }

    /// Trust (plan step 3.3): the F1 inventory reads a Clean-origin row's Rust callees from the
    /// published row's `Call`s — in call order, each once — located through the disclosure, and
    /// only from a `Producer::Clean` body.
    #[test]
    fn the_inventory_reads_the_published_rows_callees_not_mir() {
        use super::super::clean_inventory::published_row_callees;
        let mut module = handoff();
        // `cleanMin` (FuncId 3) calls the Rust caller (0) twice and the declaration (1) once.
        let body = &mut module.functions[3].blocks[0].body;
        body.clear();
        for callee in [0u32, 1, 0] {
            body.push(InstrNode::new(Inst::Call { callee: FuncId::new(callee), args: vec![] }));
        }
        body.push(InstrNode::new(Inst::Return { values: vec![] }));
        assert_eq!(
            published_row_callees(&module, "m::cleanMin"),
            Some(vec![FuncId::new(0), FuncId::new(1)])
        );
        // `cleanWsum` calls nothing: a recorded, call-free row (the MIR lane's
        // `u64::wrapping_add` is not in the trust-ir row).
        assert_eq!(published_row_callees(&module, "m::cleanWsum"), Some(Vec::<FuncId>::new()));
        // No row recorded for the def on this lane, or a skipped row: no row to read (`None`),
        // which is not "no callee".
        assert_eq!(published_row_callees(&module, "m::absent"), None);
        assert_eq!(published_row_callees(&module, "m::half"), None);
        // A disclosure row that points at a non-Clean function is not a Clean row.
        module.functions[3].producer = Some(Producer::TRust);
        assert_eq!(published_row_callees(&module, "m::cleanMin"), None);
    }

    /// Trust (plan step 3.3, step-3 review 2026-10-07; plan R-8): the inventory reads a row in
    /// place of the MIR walk only when the row is COMPLETE. With no recorded row, or a `Call` the
    /// handoff's identity index cannot map, the answer is `None` (walk the MIR as before), never
    /// an empty or partial neighbour set. Before the review an unrecorded def answered no
    /// neighbour, which dropped a Rust callee reached only through it from every F1 inventory
    /// (`tests/run-make/trust-cg-f1-mixed-crate`, t4p with verification off: 0/2 for 0/4).
    #[test]
    fn the_inventory_walks_the_mir_unless_the_row_is_complete() {
        use super::super::clean_inventory::row_neighbours;
        let mut module = handoff();
        let body = &mut module.functions[3].blocks[0].body;
        body.clear();
        for callee in [0u32, 1, 0] {
            body.push(InstrNode::new(Inst::Call { callee: FuncId::new(callee), args: vec![] }));
        }
        body.push(InstrNode::new(Inst::Return { values: vec![] }));
        // Every callee indexed: the definitions, in call order, each once.
        let both = |id: FuncId| match id.index() {
            0 => Some(10),
            1 => Some(11),
            _ => None,
        };
        assert_eq!(row_neighbours(&module, "m::cleanMin", both), Some(vec![10, 11]));
        // One callee the handoff does not index (another Clean row, an unassembled Rust body):
        // the row cannot stand in for the MIR walk.
        let only_caller = |id: FuncId| (id.index() == 0).then_some(10);
        assert_eq!(row_neighbours(&module, "m::cleanMin", only_caller), None);
        // A recorded call-free row: no neighbour, read from the row.
        assert_eq!(row_neighbours(&module, "m::cleanWsum", both), Some(vec![]));
        // Nothing recorded for the def (a planner-skipped def, or a finalization that published
        // no row; before plan step 3.5 every verification-off compile): walk the MIR.
        assert_eq!(row_neighbours(&module, "m::absent", both), None);
        assert_eq!(row_neighbours(&module, "m::half", both), None);
        // The references are trust-ir's dependency census, not a match on `Inst::Call`: a
        // `CallCannotUnwind` is a call like any other, and a self-call is no neighbour.
        let body = &mut module.functions[3].blocks[0].body;
        body.clear();
        body.push(InstrNode::new(Inst::CallCannotUnwind { callee: FuncId::new(1), args: vec![] }));
        body.push(InstrNode::new(Inst::Call { callee: FuncId::new(3), args: vec![] }));
        body.push(InstrNode::new(Inst::Return { values: vec![] }));
        assert_eq!(row_neighbours(&module, "m::cleanMin", both), Some(vec![11]));
        // An indirect call the census cannot resolve to one target: not a complete callee list.
        let sig = module.functions[3].ty;
        module.functions[3].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::CallIndirect {
                callee: trust_ir::value::ValueId::new(0),
                sig,
                args: vec![],
                calling_conv: trust_ir::CallingConv::C,
            }),
        );
        assert_eq!(row_neighbours(&module, "m::cleanMin", both), None);
    }

    /// Trust (plan step 3.0, step-3 review 2026-10-05): the census prints the class's options
    /// ONCE, under its `retired by:` line and before its samples, however many Clean refusals
    /// it records; no other class prints an options line. Before, `report` printed only the
    /// samples and `retired_by`, so the options (in `message()`, i.e. `Display`, which no
    /// production path formats) reached no output.
    #[test]
    fn the_census_prints_the_clean_options_once_for_the_class() {
        let mut census = RefusalCensus::default();
        for i in 0..5 {
            census.record(converter_refusal(
                &format!("_RNvCs1k{i}calls_clean"),
                &handoff(),
                "cleanWsum",
                "the converter's own refusal".into(),
            ));
        }
        let report = census.report(5);
        for needle in [
            "No F1 lane admits a Clean-origin Function yet, whatever its tier",
            "Options: (1) build this crate on the MIR lane",
            "owner ruling D38",
            "(3) keep the Clean call outside this trust-ir-frontend unit",
        ] {
            assert_eq!(report.matches(needle).count(), 1, "`{needle}` once in {report}");
        }
        let retired = report.find("retired by:").expect("retired by");
        let options = report.find("until then: No F1 lane admits").expect("options");
        let sample = report.find("e.g. ").expect("a sample");
        assert!(retired < options && options < sample, "{report}");
        assert_eq!(
            RefusalClass::ALL.iter().filter(|class| class.options().is_some()).count(),
            1,
            "only `[clean-below-gate]` prints options"
        );
        assert_eq!(RefusalClass::CleanBelowGate.options(), Some(CLASS_OPTIONS));
        // One refusal's `Display` carries the same text.
        let one = converter_refusal("s", &handoff(), "cleanWsum", "c".into()).to_string();
        assert!(one.contains(CLASS_OPTIONS), "{one}");
    }

    #[test]
    fn an_unrecorded_own_refusal_says_so_and_keeps_the_lane_reason() {
        let refusal = FrontendRefusal::CleanBelowGate {
            symbol: "_RNvNtCs1k1m9cleanWsum".into(),
            row: CleanRowRefusal {
                role: CleanRole::Own,
                def: "m::cleanWsum".into(),
                row: None,
                imported_from: None,
                why: "the assembled handoff indexes no body for it".into(),
            },
        };
        let rendered = refusal.to_string();
        assert!(rendered.starts_with("[clean-below-gate] "), "{rendered}");
        assert!(rendered.contains("the Clean-origin def `m::cleanWsum`"), "{rendered}");
        assert!(rendered.contains("not recorded on this lane"), "{rendered}");
        assert!(rendered.contains("step 3.5"), "{rendered}");
        // Plan step 3.5: the recorder runs on every F1 compile, so an unrecorded def is one this
        // compile's finalization published no row for, not a verification-off compile.
        assert!(rendered.contains("runs on every F1 compile"), "{rendered}");
        assert!(!rendered.contains("only with verification on"), "{rendered}");
        assert!(!CLASS_OPTIONS.contains("needs the recorder on every F1"), "{CLASS_OPTIONS}");
        assert!(rendered.contains("indexes no body for it"), "{rendered}");
        assert!(!rendered.contains("[producer-declined]"), "{rendered}");
    }

    /// Plan step 3.4 (the step-3 lander's hand-over; the landing review): step (1) of `name`, the
    /// reading of the lane's refusal of a Clean-origin def's OWN item. A contract break
    /// (`[malformed-producer-module]`) keeps its class (before 3.4 it was renamed
    /// `[clean-below-gate]`), and the handoff lane's `ExactAssembledBodyAbsent` says the handoff
    /// indexes a Clean row only as an entry of the Session's carrier ledger (before: that it
    /// never indexes one, naming the now `#[cfg(test)]`-only `checked`).
    #[test]
    fn own_def_refusals_keep_a_contract_break_and_name_the_ledger() {
        for malformed in [
            FrontendRefusal::SelectedFunctionMissing {
                symbol: "_RNvC1f".into(),
                func_id: 2,
                functions: 2,
            },
            FrontendRefusal::MissingFuncType { symbol: "_RNvC1g".into(), ty: 9 },
        ] {
            assert_eq!(malformed.class(), RefusalClass::MalformedProducerModule);
            assert_eq!(own_def_why(&malformed), None, "{malformed:?} keeps its own class");
        }
        let absent = FrontendRefusal::ExactAssembledBodyAbsent {
            symbol: "_RNvC1j".into(),
            def_index: 4,
            definition: "Item(0xc1ea)".into(),
        };
        let why = own_def_why(&absent).expect("renamed `[clean-below-gate]`");
        for needle in [
            "indexes no body for it (DefIndex(4), Item(0xc1ea))",
            "only as an entry of this Session's carrier ledger",
            "`clean-carrier-gate`",
            "`trust_thir_lower::AssembledCrateModuleForCodegen::checked_with_ledger`",
        ] {
            assert!(why.contains(needle), "`{needle}` in: {why}");
        }
        for stale in ["never indexes", "::checked`"] {
            assert!(!why.contains(stale), "`{stale}` in: {why}");
        }
        // Every other class keeps the lane's reason, through its census sample line.
        let converter =
            FrontendRefusal::ConverterRefused { symbol: "_RNvC1h".into(), detail: "d".into() };
        let why = own_def_why(&converter).expect("renamed `[clean-below-gate]`");
        assert!(why.starts_with("the lane refused it as [converter-refused]: "), "{why}");
    }

    /// Plan step 3.0, cross-crate: an imported Clean-origin def's copy, and an upstream body whose
    /// MIR inlines one, name the exporting crate and increment 6 instead of the same-crate
    /// recorder, and keep the lane's reason.
    #[test]
    fn an_imported_refusal_names_its_crate_and_increment_6() {
        let own = FrontendRefusal::CleanBelowGate {
            symbol: "_RNvNtCs1u2up1m8cleanXorCs1d4down".into(),
            row: CleanRowRefusal {
                role: CleanRole::Own,
                def: "up::m::cleanXor".into(),
                row: None,
                imported_from: Some("up".into()),
                why: "the lane refused it as [upstream-body]: `s` = cleanXor".into(),
            },
        };
        let rendered = own.to_string();
        assert_eq!(own.class(), RefusalClass::CleanBelowGate);
        for expected in [
            "the Clean-origin def `up::m::cleanXor` (imported from crate `up`",
            "cross-crate Clean bodies are increment 6",
            "[upstream-body]",
            "Options: (1) build this crate on the MIR lane",
        ] {
            assert!(rendered.contains(expected), "missing `{expected}` in {rendered}");
        }
        assert!(!rendered.contains("not recorded on this lane"), "{rendered}");
        let inlines = CleanRowRefusal {
            role: CleanRole::Inlines,
            why: "the exporting crate's MIR inliner copied the Clean-origin body".into(),
            ..match own {
                FrontendRefusal::CleanBelowGate { row, .. } => row,
                _ => unreachable!(),
            }
        };
        let sample = inlines.sample();
        assert!(
            sample.starts_with("its MIR inlines the Clean-origin def `up::m::cleanXor` (imported"),
            "{sample}"
        );
        assert!(sample.contains("MIR inliner copied"), "{sample}");
        assert!(RefusalClass::CleanBelowGate.retired_by().contains("increment 6"));
    }
}

// ---------------------------------------------------------------------------
// Trust (step 2 increment 5, sub-step 5.4.2; review must-fix): where the compiler lane's
// coverage rows say a body's code ships, read off the certificates.
// ---------------------------------------------------------------------------
mod compiler_lane_code_placement_tests {
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, ValueId};
    use trust_ir::{Block, Function, Module, Ty};

    use super::super::*;

    /// `m_cg` with `name(x: u64) -> u64` bodies, each calling its listed callees in turn.
    fn module(bodies: &[(&str, &[&str])]) -> Module {
        let mut m = Module::new("k");
        let sig = m
            .add_func_type(FuncTy {
                params: vec![Ty::U64],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let id_of = |name: &str| {
            FuncId::new(bodies.iter().position(|(n, _)| *n == name).expect("a body") as u32)
        };
        for (index, (name, callees)) in bodies.iter().enumerate() {
            let mut f = Function::new(FuncId::new(index as u32), *name, sig, BlockId::new(0));
            let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
            let mut last = ValueId::new(0);
            for (i, callee) in callees.iter().enumerate() {
                let result = ValueId::new(i as u32 + 1);
                b.body.push(
                    InstrNode::new(Inst::Call { callee: id_of(callee), args: vec![last] })
                        .with_result(result),
                );
                last = result;
            }
            b.body.push(InstrNode::new(Inst::Return { values: vec![last] }));
            f.blocks.push(b);
            m.try_add_function(f).expect("Module::try_add_function: test fixture");
        }
        m
    }

    fn certified(rows: &[(&str, &[&str])]) -> Vec<(String, Vec<String>)> {
        rows.iter()
            .map(|(f, inlined)| (f.to_string(), inlined.iter().map(|s| s.to_string()).collect()))
            .collect()
    }

    /// The residue fixture's shape: `r0` inlined `helper`, which is ALSO defined under its own
    /// symbol. The row must say both (it said `inlined_into: []` before the fix).
    #[test]
    fn an_inlined_body_names_its_inliner_and_keeps_its_own_symbol() {
        let m = module(&[("helper", &[]), ("r0", &["helper"])]);
        let placed =
            compiler_lane_code_placement(&m, &certified(&[("helper", &[]), ("r0", &["helper"])]));
        assert_eq!(
            placed["helper"],
            CodePlacement { emitted_as_own_symbol: true, inlined_into: vec!["r0".into()] }
        );
        assert_eq!(
            placed["r0"],
            CodePlacement { emitted_as_own_symbol: true, inlined_into: vec![] }
        );
    }

    /// The gate interprets an inlined callee's WHOLE body, so what `g` calls ships inside `f`
    /// too; a body only CALLED (a `Direct` site, absent from `certified`'s inline list) is not
    /// inlined anywhere, and a body the object does not define is not its own symbol.
    #[test]
    fn inlining_is_transitive_through_the_inlined_callee_and_only_through_it() {
        let m = module(&[("h", &[]), ("g", &["h"]), ("f", &["g"]), ("k", &["h"]), ("w", &["k"])]);
        let placed = compiler_lane_code_placement(
            &m,
            &certified(&[("f", &["g"]), ("g", &["h"]), ("k", &[]), ("w", &[])]),
        );
        assert_eq!(placed["h"].inlined_into, ["f", "g"], "via g into f, and directly into g");
        assert!(!placed["h"].emitted_as_own_symbol, "h has no certificate: not its own symbol");
        assert_eq!(placed["g"].inlined_into, ["f"]);
        assert!(placed["k"].inlined_into.is_empty(), "w CALLS k (no inline site)");
        assert!(placed["w"].emitted_as_own_symbol && placed["w"].inlined_into.is_empty());
    }
}
