//! The PREMISE behind the COLLISION guard in `versioned_param_type_ranges`.
//!
//! `conjoin_arg_type_ranges` bounds a parameter's versioned spellings (`n#e`,
//! `n#s1_0`, `n#e_s1_t`) by looking up the base name left of the '#'. That is sound
//! because a type range is a property of the local's DECLARED TYPE and so holds at
//! every program point — but the lookup is keyed on a NAME, and `validate_function`
//! does not reserve '#' in local names (`place_to_var_name` passes it straight
//! through, as this file measures). If a REAL, differently-typed local could reach a
//! shipped formula spelled `n#…`, bounding it by the parameter `n`'s type would be a
//! FALSE bound, not a conservative one. The pass refuses that case.
//!
//! # This is NOT a planted-violation guard, and must not be read as one
//!
//! I could not make the collision guard DECIDE. Every declared local name containing
//! '#' COLLAPSES to its base in the shipped VC — measured below across five name
//! shapes, both written and never-written — so the pass never sees `n#…` for a local
//! that is not a genuine version token. Deleting the collision guard therefore leaves
//! the whole suite green, and no fixture in this crate isolates it.
//!
//! It is KEPT anyway, and the asymmetry that justifies keeping an untested clause
//! here is specific: this guard only ever DECLINES to add a hypothesis. Its failure
//! mode is a LOST BOUND (precision), never a minted fact (soundness), so an
//! unreachable decline cannot cause a false proof. That is categorically unlike the
//! entry-sentinel TIE's refusals, which stand between a minted equality and a false
//! proof — which is why those are planted and watched in
//! `entry_sentinel_tie_guards.rs` and this one is honestly labelled instead.
//!
//! What this file DOES pin is the premise that makes it dead. If the collapse below
//! ever changes, a `#`-spelled real local reaches the formula, the collision guard
//! goes live, and these assertions are what say so.
//!
//! # A separate, PRE-EXISTING hazard this measurement exposes
//!
//! The collapse means a local literally named `n#e` and a parameter named `n` become
//! the SAME SMT symbol `n`. `conjoin_arg_type_ranges`' original BARE loop then
//! attaches the parameter's `0 ..= u32::MAX` to a symbol an `i8` local also spells —
//! asserting that signed local is non-negative. That is on the clean tree, in the
//! bare loop, and is NOT introduced by the versioned pass; it is recorded here rather
//! than fixed, because the fix belongs in the name-collision demotion in
//! `place_to_var_name`, not in a range helper. rustc does not produce such names (the
//! demotion's own comment measures 0 names outside `[A-Za-z0-9_]` across 2326
//! functions), so the hazard is reachable only from hand-built IR.

use trust_types::*;

/// `f(n: u32)` alongside a local literally named `colliding` of type `i8`, WRITTEN in
/// bb0 and read in bb1 (so it is not merely its entry value — the case where bare
/// legitimately means "the entry value").
///
/// `out = c / colliding` keeps both division operands `i8`, which the IR audit
/// requires.
fn colliding_local(colliding: &str) -> VerifiableFunction {
    let i8_ty = || Ty::Int { width: 8, signed: true };
    VerifiableFunction {
        name: "colliding_local".into(),
        def_path: "range_guard::colliding_local".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::u32(),
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("__ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: i8_ty(), name: Some(colliding.into()) },
                LocalDecl { index: 3, ty: i8_ty(), name: Some("c".into()) },
                LocalDecl { index: 4, ty: i8_ty(), name: Some("out".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `place_to_var_name` DOES pass '#' through — the hazard the collision guard is
/// written against is real at the naming layer.
#[test]
fn a_local_name_containing_a_hash_survives_place_to_var_name() {
    for name in ["n#e", "n#zz", "n#s0_0", "n#e_s0_t"] {
        let func = colliding_local(name);
        assert_eq!(
            trust_vcgen::place_to_var_name(&func, &Place::local(2)),
            name,
            "`validate_function` does not reserve '#', so the naming layer hands \
             the version machinery a name it cannot distinguish from its own tokens"
        );
    }
}

/// …but it never REACHES a shipped formula under that spelling: it collapses to its
/// base. This is the premise that makes the collision guard dead, and the thing that
/// must go RED before that guard can be trusted to be doing anything.
#[test]
fn but_it_collapses_to_its_base_before_any_vc_ships() {
    for name in ["n#e", "n#zz", "n#s0_0", "n#e_s0_t"] {
        let func = colliding_local(name);
        trust_vcgen::validate_function(&func).expect("the fixture must be VALID TrustIR");
        let vcs = trust_vcgen::generate_vcs(&func);
        assert!(!vcs.is_empty(), "the `c / {name}` division must raise obligations");
        for vc in &vcs {
            let free = vc.formula.free_variables();
            assert!(
                !free.iter().any(|v| v == name),
                "if `{name}` now reaches a shipped VC under its own spelling, the \
                 COLLISION guard in `versioned_param_type_ranges` has become LIVE \
                 and needs a planted-violation test of its own — see this file's \
                 header.\n  free: {free:?}"
            );
        }
    }
    // Control: a name WITHOUT '#' is not collapsed, so the assertion above is about
    // the '#' handling and not about the local being unreachable.
    let func = colliding_local("nq");
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| vc.formula.free_variables().iter().any(|v| v == "nq")),
        "the control local must reach a formula, or the collapse assertion above is \
         passing for the wrong reason"
    );
}

/// Laundering control: whatever the naming does, the obligation must still exist.
#[test]
fn the_collision_fixture_still_raises_its_division_obligation() {
    for name in ["n#e", "nq"] {
        let vcs = trust_vcgen::generate_vcs(&colliding_local(name));
        assert!(
            vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
            "{name}: the row must survive; got {:?}",
            vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }
}
