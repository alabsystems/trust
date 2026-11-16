// Frozen-oracle TailCall ratification regressions.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//
// `mir_differential.rs` is blob-frozen, including its in-file tests.  Re-pinning it to the
// exact already-landed production blob while editing that blob to add tests would defeat the
// point of the ratification.  Compile a second, test-only instance instead: the assertions below
// exercise the exact frozen implementation, including its private canonicalizer, evaluator,
// marker walk, and local-write helper, without changing the production blob.
//
// `allow(dead_code)`: this instance exists only for the tests below, so the production entry
// points (`compare_derived` and everything only it reaches) are never called HERE, by
// construction. Dead code in the real module is still reported, by the `lib` build of
// `mir_differential.rs`, which carries no such allow.
#[allow(dead_code)]
mod frozen_oracle {
    // `include!` cannot accept another module's leading `//!` comments.  The build script changes
    // only that contiguous comment prefix to ordinary `//` comments in OUT_DIR; every production
    // token compiled below is taken from the exact frozen source file.
    include!(concat!(env!("OUT_DIR"), "/mir_differential_without_inner_docs.rs"));

    fn terminal_body(terminator: Terminator) -> VerifiableBody {
        let uint = Ty::Int { width: 32, signed: false };
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: uint.clone(), name: None },
                trust_types::LocalDecl { index: 1, ty: uint.clone(), name: Some("x".into()) },
                trust_types::LocalDecl { index: 2, ty: uint.clone(), name: None },
            ],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: Vec::new(),
                terminator,
            }],
            arg_count: 1,
            return_ty: uint,
            datatype_defs: Default::default(),
        }
    }

    fn tail_call_body() -> VerifiableBody {
        terminal_body(Terminator::TailCall {
            func: "crate::callee".into(),
            args: vec![Operand::Copy(Place::local(1))],
            span: trust_types::SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: None,
        })
    }

    /// Exercise the evaluator's defence-in-depth arm directly.  `canonicalize` cannot reach it
    /// with a TailCall because the earlier successor walk already refuses, so this one-node graph
    /// keeps the later refusal independently mutation-sensitive.
    fn eval_single_terminal(body: &VerifiableBody) -> CanonResult<Vec<String>> {
        let graph = Graph {
            blocks: vec![(Vec::new(), &body.blocks[0].terminator)],
            arg_kinds: CallArgKinds::new(),
            order: vec![0],
            succ_of: HashMap::from([(0, Vec::new())]),
            edges_in: HashMap::from([(0, vec![Edge { pred: None, slot: 0, path: Vec::new() }])]),
            topo: vec![0],
            back_edges: HashSet::new(),
            header: None,
            headers: Vec::new(),
            final_of: HashMap::from([(0, 0)]),
            ret_of: HashMap::new(),
            nodes_total: 1,
        };
        let (lines, _) = eval_with_header_envs(
            body,
            &graph,
            &HashMap::new(),
            None,
            &NormCounter::default(),
            &EscapeNames::default(),
        )?;
        Ok(lines)
    }

    /// Mutation proof: the in-fragment `Unreachable` control traverses every relevant walk;
    /// changing only its terminator to TailCall makes all four independent surfaces refuse with
    /// the dedicated reason.  The direct evaluator assertion is not masked by the earlier CFG
    /// refusal.
    #[test]
    fn tail_call_is_refused_by_every_differential_walk() {
        let control = terminal_body(Terminator::Unreachable);
        assert!(canonical_cfg_roles(&control).is_ok(), "the CFG-role control must be admitted");
        assert!(
            canonicalize(&control, CallArgKinds::new()).0.is_ok(),
            "the semantic canonicalizer control must be admitted",
        );
        assert!(eval_single_terminal(&control).is_ok(), "the evaluator control must be admitted");
        assert!(canon_markers(&control).is_ok(), "the marker-walk control must be admitted");

        let tail = tail_call_body();
        let expected = "TailCall outside MIR differential fragment";
        assert_eq!(canonical_cfg_roles(&tail).unwrap_err(), expected);
        assert_eq!(canonicalize(&tail, CallArgKinds::new()).0.unwrap_err(), expected);
        assert_eq!(eval_single_terminal(&tail).unwrap_err(), expected);
        assert_eq!(canon_markers(&tail).unwrap_err(), expected);
    }

    /// A TailCall has no explicit destination, but successful completion writes the
    /// caller-visible result represented by `_0`.  Mutation back to an otherwise-identical
    /// non-writing terminal proves this arm is the sole reason `_0` changes classification;
    /// every other in-range and out-of-range local remains non-written.
    #[test]
    fn tail_call_marks_only_the_return_local_as_written() {
        let tail = tail_call_body();
        assert!(local_ever_written(&tail, 0));
        for local in 1..=tail.locals.len() + 1 {
            assert!(
                !local_ever_written(&tail, local),
                "TailCall must not manufacture a write to local _{local}",
            );
        }

        let control = terminal_body(Terminator::Unreachable);
        for local in 0..=control.locals.len() + 1 {
            assert!(
                !local_ever_written(&control, local),
                "without TailCall the statement-free control writes no local (_{local})",
            );
        }
    }
}
