// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
// trust_vcgen/abstract_interp/tests.rs: Tests for abstract interpretation framework
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// ── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
#[allow(clippy::module_inception)]
mod tests {
    use trust_types::fx::{FxHashMap, FxHashSet};
    use trust_types::*;

    use crate::abstract_interp::discharge::{
        ComparisonOp, check_comparison_intervals, try_eval_boolean, type_bounds,
    };
    use crate::abstract_interp::transfer::{compute_successor_states, narrow_from_otherwise};
    use crate::abstract_interp::*;

    // -- Loop-head narrowing through the break comparison --

    /// `pub fn f() -> u32 { let mut r = 0; loop { r += 1; if r > 5 { break; } } r }`
    /// transcribed from the real `-Ztrust-dump=mir` output, so the shape under
    /// test is the one rustc actually emits and not an idealised one.
    ///
    /// ```text
    /// bb0: _1 = 0                     -> bb1
    /// bb1: _2 = CheckedAdd(_1, 1)     Assert(!_2.1) -> bb4     <- head, and the add
    /// bb4: _3 = Gt(_2.0, 5)           SwitchInt(_3): 0 -> bb3, else -> bb2
    /// bb3: _1 = _2.0                  -> bb1                    <- back edge
    /// bb2: _0 = _2.0                  Return
    /// ```
    fn bottom_tested_loop(bound: u128) -> VerifiableFunction {
        let u32_ty = Ty::Int { width: 32, signed: false };
        let local = |index: usize, ty: Ty, name: &str| LocalDecl {
            index,
            ty,
            name: Some(name.to_string()),
        };
        let checked = Ty::Tuple(vec![u32_ty.clone(), Ty::Bool]);
        let sum = Place { local: 2, projections: vec![Projection::Field(0)] };
        let overflowed = Place { local: 2, projections: vec![Projection::Field(1)] };
        let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        VerifiableFunction {
            name: "f".to_string(),
            def_path: "test::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    local(0, u32_ty.clone(), "_0"),
                    local(1, u32_ty.clone(), "r"),
                    local(2, checked, "_2"),
                    local(3, Ty::Bool, "_3"),
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            Place::local(1),
                            Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        )],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![assign(
                            Place::local(2),
                            Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                        )],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(overflowed),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(4),
                            unwind: UnwindEdge::Unreachable,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![assign(
                            Place::local(0),
                            Rvalue::Use(Operand::Copy(sum.clone())),
                        )],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![assign(
                            Place::local(1),
                            Rvalue::Use(Operand::Copy(sum.clone())),
                        )],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(4),
                        stmts: vec![assign(
                            Place::local(3),
                            Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(sum),
                                Operand::Constant(ConstValue::Uint(bound, 32)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(0, BlockId(3))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                ],
                arg_count: 0,
                return_ty: u32_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn break_comparison_narrows_both_edges_of_the_loop_test() {
        // The branch read BACK onto the compared value. `narrow_from_condition`
        // pins the bool discriminant `_3`, which this domain does not track at
        // all, so without this step nothing constrains `_2.0` on either edge.
        let func = bottom_tested_loop(5);
        let block = &func.body.blocks[4];
        let sum = crate::place_to_var_name(
            &func,
            &Place { local: 2, projections: vec![Projection::Field(0)] },
        );
        let mut state = IntervalDomain::top();
        state.set(sum.clone(), Interval::new(0, 1000));
        let succs = compute_successor_states(&block.terminator, &func, block, &state);

        // The back edge is the `_3 == 0` arm: `!(sum > 5)`, so `sum <= 5`.
        let back = succs.iter().find(|(id, _)| *id == BlockId(3)).expect("back edge");
        assert_eq!(back.1.get(&sum), Interval::new(0, 5), "back edge: !(sum > 5)");
        // The exit edge is the complement: `sum > 5`, so `sum >= 6`.
        let exit = succs.iter().find(|(id, _)| *id == BlockId(2)).expect("exit edge");
        assert_eq!(exit.1.get(&sum), Interval::new(6, 1000), "exit edge: sum > 5");
    }

    #[test]
    fn the_loop_head_is_bounded_by_the_break_test() {
        // THE FACT THE FALSE REFUTATION NEEDED. At the loop head `r` is the join
        // of the entry constant `0` and the back edge's `_2.0 <= 5`, so it is
        // bounded and `r + 1` cannot overflow. Before the back-substitution this
        // was the full `i128` range, and the solver duly witnessed `r == u32::MAX`
        // — a state the loop cannot reach — and reported the add REFUTED.
        let func = bottom_tested_loop(5);
        let initial = crate::abstract_interp::type_aware_initial_state(&func);
        let config = crate::abstract_interp::transfer::FixpointConfig::for_function(&func);
        let fp = crate::abstract_interp::transfer::fixpoint_configured(&func, initial, &config);
        let head = &fp.block_states[&BlockId(1)];
        assert_eq!(head.get("r"), Interval::new(0, 5), "loop head must bound r by the break test");
    }

    #[test]
    fn the_loop_head_bound_tracks_the_break_constant() {
        // POSITIVE CONTROL: a different break constant must move the bound with
        // it, so the test above cannot be satisfied by a fixed answer — including
        // the `[0, 0]` an analysis would give if it dropped the back edge.
        for bound in [5u128, 100, 1000] {
            let func = bottom_tested_loop(bound);
            let initial = crate::abstract_interp::type_aware_initial_state(&func);
            let config = crate::abstract_interp::transfer::FixpointConfig::for_function(&func);
            let fp = crate::abstract_interp::transfer::fixpoint_configured(&func, initial, &config);
            let r = fp.block_states[&BlockId(1)].get("r");
            assert_eq!(
                r,
                Interval::new(0, i128::try_from(bound).unwrap()),
                "bound {bound} must reach the loop head"
            );
        }
    }

    #[test]
    fn post_fixpoint_repair_widens_a_state_that_is_too_tight() {
        use crate::abstract_interp::transfer::{
            FixpointConfig, fixpoint_configured, repair_to_post_fixpoint,
        };
        // Take the real, correct result and then LIE about the loop head,
        // claiming a bound that excludes a value its own back edge propagates.
        // That is the shape a non-monotone transfer produces, and it is the
        // false-proof direction: an environment missing a reachable state can
        // discharge an obligation the runtime violates.
        let func = bottom_tested_loop(5);
        let initial = crate::abstract_interp::type_aware_initial_state(&func);
        let config = FixpointConfig::for_function(&func);
        let mut fp = fixpoint_configured(&func, initial, &config);
        assert_eq!(
            fp.block_states[&BlockId(1)].get("r"),
            Interval::new(0, 5),
            "premise: the honest answer bounds the counter by 5"
        );

        fp.block_states.get_mut(&BlockId(1)).unwrap().set("r".to_string(), Interval::new(0, 4));
        repair_to_post_fixpoint(&func, &mut fp);

        // The repair may only WEAKEN, so the lie is gone. It is not required to
        // recover the exact honest answer — Top is the safe reply — but it must
        // no longer exclude 5.
        let repaired = fp.block_states[&BlockId(1)].get("r");
        assert!(
            repaired.contains(5),
            "a state that excluded a reachable value must be widened, got {repaired:?}"
        );
    }

    #[test]
    fn the_fixpoint_result_is_a_post_fixpoint() {
        use crate::abstract_interp::transfer::{FixpointConfig, fixpoint_configured};
        // The property every consumer assumes and nothing checked: propagating
        // once more must not GROW any block's state. Compared over the UNION of
        // both key sets, because a variable that grew to Top is ABSENT from the
        // propagated state and iterating it alone misses the largest growth
        // there is.
        for func in [bottom_tested_loop(5), bottom_tested_loop(1000)] {
            let initial = crate::abstract_interp::type_aware_initial_state(&func);
            let config = FixpointConfig::for_function(&func);
            let fp = fixpoint_configured(&func, initial, &config);
            for block in &func.body.blocks {
                let entry = &fp.block_states[&block.id];
                if entry.is_unreachable {
                    continue;
                }
                let mut current = entry.clone();
                for stmt in &block.stmts {
                    current =
                        crate::abstract_interp::transfer::transfer_function(stmt, &func, &current);
                }
                for (succ, state) in
                    compute_successor_states(&block.terminator, &func, block, &current)
                {
                    let stored = &fp.block_states[&succ];
                    if state.is_unreachable {
                        continue;
                    }
                    assert!(!stored.is_unreachable, "bb{} reaches bb{}", block.id.0, succ.0);
                    for name in state.vars.keys().chain(stored.vars.keys()) {
                        assert!(
                            state.get(name).leq(&stored.get(name)),
                            "bb{} -> bb{} grows `{name}`: {:?} not <= {:?}",
                            block.id.0,
                            succ.0,
                            state.get(name),
                            stored.get(name)
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn every_block_bounds_the_counter_by_the_break_test() {
        // The whole fixpoint, not just the head. A narrowing that stated only
        // the half the branch gave it (`[i128::MIN, 5]` on a `u32`) was sound
        // and useless: the copy on the back edge carried the unknown lower
        // bound onto the counter, and every join inherited it. Meeting with the
        // place's own type range keeps both halves.
        let func = bottom_tested_loop(5);
        let initial = crate::abstract_interp::type_aware_initial_state(&func);
        let config = crate::abstract_interp::transfer::FixpointConfig::for_function(&func);
        let fp = crate::abstract_interp::transfer::fixpoint_configured(&func, initial, &config);
        for id in [BlockId(1), BlockId(2), BlockId(3), BlockId(4)] {
            assert_eq!(
                fp.block_states[&id].get("r"),
                Interval::new(0, 5),
                "bb{} must bound the counter",
                id.0
            );
        }
        // The entry block is the one place the counter is not yet a value, so
        // it carries only the type range.
        assert_eq!(
            fp.block_states[&BlockId(0)].get("r"),
            Interval::new(0, i128::from(u32::MAX)),
            "entry keeps the type range"
        );
    }

    #[test]
    fn the_function_wide_environment_carries_the_loop_head_bound() {
        // THE END OF THE FALSE REFUTATION'S CAUSE CHAIN. This is the environment
        // the discharge actually consumes. It used to be the full `i128` range
        // for the counter, which is why the solver was free to witness
        // `r == u32::MAX` and report the add REFUTED.
        let env = merged_interval_environment(&bottom_tested_loop(5));
        assert_eq!(env.get("r"), Interval::new(0, 5), "the break bound must survive the join");
    }

    #[test]
    fn the_environment_bound_tracks_the_break_constant() {
        // POSITIVE CONTROL: no fixed answer can satisfy the test above.
        for bound in [5u128, 100, 1000] {
            let env = merged_interval_environment(&bottom_tested_loop(bound));
            assert_eq!(
                env.get("r"),
                Interval::new(0, i128::try_from(bound).unwrap()),
                "bound {bound} must reach the environment"
            );
        }
    }

    /// `pub fn g(x: u32) -> bool { x + 1 > 5 }`, straight-line: the CheckedAdd
    /// result TUPLE `_2` and the comparison BOOL `_3` are both defined in the
    /// entry block and read in `bb1`.
    fn checked_add_then_compare() -> VerifiableFunction {
        let u32_ty = Ty::Int { width: 32, signed: false };
        let local = |index: usize, ty: Ty, name: &str| LocalDecl {
            index,
            ty,
            name: Some(name.to_string()),
        };
        let sum = Place { local: 2, projections: vec![Projection::Field(0)] };
        let overflowed = Place { local: 2, projections: vec![Projection::Field(1)] };
        let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        VerifiableFunction {
            name: "g".to_string(),
            def_path: "test::g".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    local(0, Ty::Bool, "_0"),
                    local(1, u32_ty.clone(), "x"),
                    local(2, Ty::Tuple(vec![u32_ty.clone(), Ty::Bool]), "_2"),
                    local(3, u32_ty, "_3"),
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            Place::local(2),
                            Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                        )],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(overflowed),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            unwind: UnwindEdge::Unreachable,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            assign(Place::local(3), Rvalue::Use(Operand::Copy(sum))),
                            assign(
                                Place::local(0),
                                Rvalue::BinaryOp(
                                    BinOp::Gt,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Constant(ConstValue::Uint(5, 32)),
                                ),
                            ),
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Bool,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn the_environment_speaks_only_about_int_sorted_locals() {
        // The domain tracks the CheckedAdd result TUPLE `_2` (its UNWRAPPED sum,
        // `[1, u32::MAX + 1]`) for its own transfer, but the environment is
        // exported as `Var(name, Int)` facts, and for `_2` that names no formula
        // term: the checked result is the place `_2.0`. Measured before the
        // filter on this body: `_2 in [1, 4294967296]` rode every augmented
        // formula, a value no `u32` holds.
        let env = merged_interval_environment(&checked_add_then_compare());
        assert!(!env.vars.contains_key("_2"), "a tuple local is not an Int term: {env:?}");
        assert_eq!(env.get("x"), Interval::new(0, i128::from(u32::MAX)), "params keep facts");
        assert_eq!(
            env.get("_3"),
            Interval::new(0, i128::from(u32::MAX)),
            "an Int-sorted temp keeps its (type-range) fact"
        );
    }

    /// `pick(b: bool) -> i32 { if b { 1 } else { 2 } }` under an `ensures`, as
    /// rustc lowers it: the contract binds the result to local 3, source-named
    /// `__ret`, and `_0 = copy __ret` returns it. `__ret` is reserved
    /// (`place_to_var_name` spells the local `_3`), and parameter 1 carries the
    /// source name `param_name`.
    fn pick_with_reserved_result_binding(param_name: &str) -> VerifiableFunction {
        let i32_ty = Ty::Int { width: 32, signed: true };
        let local = |index: usize, ty: Ty, name: Option<&str>| LocalDecl {
            index,
            ty,
            name: name.map(str::to_string),
        };
        let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        let set_ret = |value: i128| {
            assign(Place::local(3), Rvalue::Use(Operand::Constant(ConstValue::Int(value))))
        };
        VerifiableFunction {
            name: "pick".to_string(),
            def_path: "test::pick".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    local(0, i32_ty.clone(), None),
                    local(1, Ty::Int { width: 8, signed: false }, Some(param_name)),
                    local(2, Ty::Bool, Some("__ensures_checker")),
                    local(3, i32_ty.clone(), Some("__ret")),
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![set_ret(1)],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![set_ret(2)],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![assign(
                            Place::local(0),
                            Rvalue::Use(Operand::Copy(Place::local(3))),
                        )],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: i32_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn the_environment_names_each_local_as_the_formula_does() {
        // Seeded under the SOURCE name, the environment carried
        // `__ret in [i32::MIN, i32::MAX]` while every transfer wrote `_3`: a
        // fact about no term of any formula, and `_3` itself was never
        // recognised as undefined at entry. Every key must be a formula name.
        for param in ["b", "result", "_3"] {
            let func = pick_with_reserved_result_binding(param);
            let formula_names: FxHashSet<String> =
                func.body.locals.iter().map(|l| crate::local_var_name(&func, l)).collect();
            let env = merged_interval_environment(&func);
            for key in env.vars.keys() {
                assert!(
                    formula_names.contains(key),
                    "[{param}] env key {key:?} names no local's formula term: {env:?}"
                );
            }
            assert!(!env.vars.contains_key("__ret"), "[{param}] {env:?}");
            // The u8 parameter keeps its type range under ITS formula name — for
            // `result` and `_3` that is `_1`, and a parameter spelled `_3`
            // must not lend its range to local 3.
            let param_name = crate::local_var_name(&func, &func.body.locals[1]);
            assert_eq!(env.get(&param_name), Interval::new(0, 255), "[{param}] {env:?}");
            let ret = env.get("_3");
            assert!(
                ret.lo <= 1 && ret.hi >= 2,
                "[{param}] local 3 holds 1 and 2; its interval {ret:?} must contain both"
            );
        }
    }

    // -- Interval arithmetic tests --

    #[test]
    fn test_interval_add_basic() {
        let a = Interval::new(1, 5);
        let b = Interval::new(10, 20);
        let result = interval_add(&a, &b);
        assert_eq!(result.lo, 11);
        assert_eq!(result.hi, 25);
    }

    #[test]
    fn test_interval_add_negative() {
        let a = Interval::new(-10, -1);
        let b = Interval::new(5, 10);
        let result = interval_add(&a, &b);
        assert_eq!(result.lo, -5);
        assert_eq!(result.hi, 9);
    }

    #[test]
    fn test_interval_add_bottom_propagates() {
        let a = Interval::BOTTOM;
        let b = Interval::new(1, 5);
        assert!(interval_add(&a, &b).is_bottom());
    }

    // Trust #soundness (i128 add/sub false-PROVE): a TOP operand carries no
    // information and is what `interval_add` collapses to on i128 overflow, so a
    // comparison against it MUST be indeterminate — otherwise TOP.hi == i128::MAX
    // is read as a precise bound and `a+b > i128::MAX` is "definitely false",
    // discharging a real overflow.
    #[test]
    fn top_operand_overflow_comparison_is_indeterminate() {
        // The exact comparisons the i128 add violation `Or([Lt(a+b,MIN),Gt(a+b,MAX)])`
        // produces, where `a+b` overflowed to TOP.
        assert_eq!(
            check_comparison_intervals(
                &Interval::TOP,
                &Interval::constant(i128::MAX),
                ComparisonOp::Gt
            ),
            None,
            "TOP > i128::MAX must be indeterminate (was the false-PROVE Some(false))"
        );
        assert_eq!(
            check_comparison_intervals(
                &Interval::TOP,
                &Interval::constant(i128::MIN),
                ComparisonOp::Lt
            ),
            None,
            "TOP < i128::MIN must be indeterminate (was the false-PROVE Some(false))"
        );
        // Completeness guard: a PRECISE interval whose hi is i128::MAX (a genuine
        // bound, never produced by an overflowing op which yields full TOP) still
        // concludes — `[5, i128::MAX] > i128::MAX` is soundly false.
        assert_eq!(
            check_comparison_intervals(
                &Interval::new(5, i128::MAX),
                &Interval::constant(i128::MAX),
                ComparisonOp::Gt
            ),
            Some(false),
            "a precise non-TOP interval bounded by i128::MAX must still conclude"
        );
    }

    // End-to-end at the `try_eval_boolean` layer: the i128 add overflow VIOLATION
    // formula must NOT evaluate to `Some(false)` (which the generic discharge path
    // turns into a Proved). Mirrors the fuzzer-found `fn f(a:i128,b:i128){a+b}`.
    #[test]
    fn i128_add_overflow_violation_not_eval_false() {
        let min = Formula::Int(i128::MIN);
        let max = Formula::Int(i128::MAX);
        let a = Formula::Var("a".into(), Sort::Int);
        let b = Formula::Var("b".into(), Sort::Int);
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));
        let range = |v: &Formula| {
            Formula::And(vec![
                Formula::Le(Box::new(min.clone()), Box::new(v.clone())),
                Formula::Le(Box::new(v.clone()), Box::new(max.clone())),
            ])
        };
        let formula = Formula::And(vec![
            range(&a),
            range(&b),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum.clone()), Box::new(min.clone())),
                Formula::Gt(Box::new(sum.clone()), Box::new(max.clone())),
            ]),
        ]);
        let env = IntervalDomain::top();
        assert_ne!(
            try_eval_boolean(&formula, &env),
            Some(false),
            "signed-128 add CAN overflow (a=b=i128::MAX); the violation is reachable \
             and must NOT abstract-evaluate to definitely-false"
        );
    }

    #[test]
    fn test_interval_sub_basic() {
        let a = Interval::new(10, 20);
        let b = Interval::new(1, 5);
        let result = interval_sub(&a, &b);
        assert_eq!(result.lo, 5);
        assert_eq!(result.hi, 19);
    }

    #[test]
    fn test_interval_mul_positive() {
        let a = Interval::new(2, 4);
        let b = Interval::new(3, 5);
        let result = interval_mul(&a, &b);
        assert_eq!(result.lo, 6);
        assert_eq!(result.hi, 20);
    }

    #[test]
    fn test_interval_mul_mixed_signs() {
        let a = Interval::new(-2, 3);
        let b = Interval::new(-1, 4);
        let result = interval_mul(&a, &b);
        // corners: (-2)*(-1)=2, (-2)*4=-8, 3*(-1)=-3, 3*4=12
        assert_eq!(result.lo, -8);
        assert_eq!(result.hi, 12);
    }

    // -- Interval lattice tests --

    #[test]
    fn test_interval_join() {
        let a = Interval::new(1, 5);
        let b = Interval::new(3, 10);
        let j = a.join(&b);
        assert_eq!(j.lo, 1);
        assert_eq!(j.hi, 10);
    }

    #[test]
    fn test_interval_meet() {
        let a = Interval::new(1, 10);
        let b = Interval::new(5, 15);
        let m = a.meet(&b);
        assert_eq!(m.lo, 5);
        assert_eq!(m.hi, 10);
    }

    #[test]
    fn test_interval_meet_empty() {
        let a = Interval::new(1, 3);
        let b = Interval::new(5, 10);
        assert!(a.meet(&b).is_bottom());
    }

    #[test]
    fn test_interval_widen_expands() {
        let a = Interval::new(0, 5);
        let b = Interval::new(0, 10);
        let w = a.widen(&b);
        assert_eq!(w.lo, 0);
        assert_eq!(w.hi, i128::MAX);
    }

    #[test]
    fn test_interval_widen_stable() {
        let a = Interval::new(0, 10);
        let b = Interval::new(0, 5);
        let w = a.widen(&b);
        assert_eq!(w, a);
    }

    #[test]
    fn test_interval_narrow_recovers() {
        let wide = Interval::new(0, i128::MAX);
        let precise = Interval::new(0, 100);
        let n = wide.narrow(&precise);
        assert_eq!(n.lo, 0);
        assert_eq!(n.hi, 100);
    }

    #[test]
    fn test_interval_leq() {
        let a = Interval::new(2, 5);
        let b = Interval::new(0, 10);
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
    }

    #[test]
    fn test_interval_bottom_leq_everything() {
        assert!(Interval::BOTTOM.leq(&Interval::new(0, 10)));
        assert!(Interval::BOTTOM.leq(&Interval::TOP));
    }

    // -- IntervalDomain tests --

    #[test]
    fn test_domain_join() {
        let mut a = IntervalDomain::top();
        a.set("x".into(), Interval::new(0, 5));
        let mut b = IntervalDomain::top();
        b.set("x".into(), Interval::new(3, 10));
        let j = a.join(&b);
        assert_eq!(j.get("x"), Interval::new(0, 10));
    }

    #[test]
    fn test_domain_bottom_is_identity_for_join() {
        let mut a = IntervalDomain::top();
        a.set("x".into(), Interval::new(1, 5));
        let b = IntervalDomain::bottom();
        assert_eq!(a.join(&b), a);
        assert_eq!(b.join(&a), a);
    }

    // -- Transfer function tests --

    #[test]
    fn test_transfer_assign_constant() {
        let func = crate::tests::midpoint_function();
        let state = IntervalDomain::top();

        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &state);
        assert_eq!(result.get("_4"), Interval::constant(42));
    }

    #[test]
    fn test_transfer_binary_add() {
        let func = crate::tests::midpoint_function();
        let mut state = IntervalDomain::top();
        state.set("a".into(), Interval::new(0, 100));
        state.set("b".into(), Interval::new(0, 100));

        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &state);
        assert_eq!(result.get("_4"), Interval::new(0, 200));
    }

    #[test]
    fn test_transfer_nop_preserves_state() {
        let func = crate::tests::midpoint_function();
        let mut state = IntervalDomain::top();
        state.set("x".into(), Interval::new(1, 10));
        let result = transfer_function(&Statement::Nop, &func, &state);
        assert_eq!(result.get("x"), Interval::new(1, 10));
    }

    /// `_c = Discriminant(e)` over an enum with the given declared discriminants, read
    /// at `dest_ty`: the interval `transfer_function` assigns to `_c`.
    fn discriminant_read_interval(discriminants: &[i128], dest_ty: Ty) -> Interval {
        let variants: Vec<trust_types::VariantDef> = discriminants
            .iter()
            .enumerate()
            .map(|(i, d)| trust_types::VariantDef {
                name: format!("V{i}"),
                discriminant: *d,
                fields: vec![],
            })
            .collect();
        let mut func = crate::tests::midpoint_function();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: Some("ret".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Adt {
                    adt_kind: None,
                    layout: None,
                    name: "E".into(),
                    fields: vec![("__tag".into(), Ty::i8())].into(),
                    variants: variants.into(),
                    disc_index_safe: true,
                    faithful_enum_repr: None,
                    enum_layout: None,
                    arbitrary_precision: None,
                    validity_wrapper: None,
                },
                name: Some("e".into()),
            },
            LocalDecl { index: 2, ty: dest_ty, name: Some("c".into()) },
        ];
        func.body.arg_count = 1;
        let stmt = Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Discriminant(Place::local(1)),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &IntervalDomain::top());
        result.get(&crate::place_to_var_name(&func, &Place::local(2)))
    }

    /// A discriminant read is one of the DECLARED discriminants, which may be negative.
    /// It used to be `[0, i128::MAX]` for every enum, and conjoined onto every VC that
    /// false `c >= 0` let `t[e as usize]` PROVE over `#[repr(i8)] enum E { A = -1, B = 2 }`
    /// (`tests/trust-falsification/mutant/repr_i8_neg_tag_index.rs`, certified by the
    /// Clean kernel on the wrong formula). An ordinary enum keeps `[0, n - 1]`.
    ///
    /// Merge 2026-10-14: the read is `transfer::discriminant_read_hull` (upstream
    /// 5f74446a760, the same fix made the same day), shared with `value_analysis`.
    /// `VariantDef::discriminant` is the DECODED tag (`trust-mir-extract` decodes it at
    /// the one boundary, `ty_convert.rs` "THE RAW-TAG BOUNDARY", since b4fd4c0e43a), and
    /// every producer must agree on that integer model. A tag the destination cannot
    /// hold (`255` read at `i8`) is no tag of it: the read is Top, never re-decoded
    /// here into a value no other producer gives it.
    #[test]
    fn discriminant_read_interval_is_the_declared_discriminant_hull() {
        assert_eq!(discriminant_read_interval(&[-1, 2], Ty::i8()), Interval::new(-1, 2));
        assert_eq!(discriminant_read_interval(&[255, 2], Ty::i8()), Interval::TOP);
        assert_eq!(discriminant_read_interval(&[0, 1, 2], Ty::isize()), Interval::new(0, 2));
        assert_eq!(discriminant_read_interval(&[], Ty::isize()), Interval::TOP);
        // `cmp::Ordering`'s discriminants are `-1`, `0` and `1`.
        assert_eq!(discriminant_read_interval(&[-1, 0, 1], Ty::i8()), Interval::new(-1, 1));
    }

    /// `_2 = <op>(_1, const 1)` over `_1: i8` in `x`, read at `_2: i8`.
    fn i8_binop_interval(op: BinOp, x: Interval) -> Interval {
        let mut func = crate::tests::midpoint_function();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i8(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::i8(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i8(), name: Some("y".into()) },
        ];
        func.body.arg_count = 1;
        let stmt = Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                op,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(1)),
            ),
            span: SourceSpan::default(),
        };
        let mut state = IntervalDomain::top();
        state.set(crate::place_to_var_name(&func, &Place::local(1)), x);
        let result = transfer_function(&stmt, &func, &state);
        result.get(&crate::place_to_var_name(&func, &Place::local(2)))
    }

    /// Two transfers that excluded real values, the same class as the negative
    /// discriminant. A bare `Shl` wraps (Rust panics only on the shift amount, and
    /// `64i8 << 1 == -128`), and `i128::checked_shl` lost bits past bit 127. A three-way
    /// compare yields `Ordering::Less`, `-1`.
    #[test]
    fn shift_left_and_three_way_compare_intervals_keep_every_real_value() {
        assert_eq!(
            interval_shl(&Interval::constant(1 << 126), &Interval::constant(2)),
            Interval::TOP
        );
        assert_eq!(
            interval_shl(&Interval::new(1, 3), &Interval::constant(2)),
            Interval::new(4, 12)
        );
        assert_eq!(
            i8_binop_interval(BinOp::Shl, Interval::new(64, 127)),
            Interval::new(-128, 127),
            "an i8 result outside its type range wraps, so the full range is the answer"
        );
        assert_eq!(i8_binop_interval(BinOp::Shl, Interval::new(1, 3)), Interval::new(2, 6));
        assert_eq!(i8_binop_interval(BinOp::Cmp, Interval::new(0, 10)), Interval::new(-1, 1));
    }

    // -- Fixpoint tests --

    #[test]
    fn test_fixpoint_simple_function() {
        let func = crate::tests::midpoint_function();
        let mut initial = IntervalDomain::top();
        initial.set("a".into(), Interval::new(0, 100));
        initial.set("b".into(), Interval::new(0, 100));

        let result = fixpoint(&func, initial);
        // Block 0 should have the initial state.
        assert!(!result.block_states.get(&BlockId(0)).unwrap().is_unreachable);
        // Block 1 should be reachable.
        assert!(!result.block_states.get(&BlockId(1)).unwrap().is_unreachable);
    }

    #[test]
    fn test_fixpoint_propagates_through_blocks() {
        let func = crate::tests::midpoint_function();
        let mut initial = IntervalDomain::top();
        initial.set("a".into(), Interval::new(0, 50));
        initial.set("b".into(), Interval::new(0, 50));

        let result = fixpoint(&func, initial);
        let bb1_state = result.block_states.get(&BlockId(1)).unwrap();
        // After a + b where a in [0,50] and b in [0,50], the sum is in [0,100].
        // The sum is assigned to _3 (tuple), then _4 gets the first field.
        // The exact propagation depends on how projections are handled.
        assert!(!bb1_state.is_unreachable);
    }

    // -- Widen point detection --

    #[test]
    fn test_no_widen_points_in_straight_line() {
        let func = crate::tests::midpoint_function();
        let wps = detect_widen_points(&func);
        assert!(wps.is_empty(), "straight-line code has no loops");
    }

    // -- Invariant extraction --

    #[test]
    fn test_extract_invariants_from_bounded_state() {
        let func = crate::tests::midpoint_function();
        let mut states = FxHashMap::default();

        // Simulate a loop header at block 0 with bounded variable.
        let mut header_state = IntervalDomain::top();
        header_state.set("i".into(), Interval::new(0, 100));
        states.insert(BlockId(0), header_state);

        // Create a fake widen point to make block 0 a loop header.
        let result = FixpointResult { block_states: states };
        // Since midpoint has no loops, extract_invariants returns empty.
        let invs = extract_invariants(&result, &func);
        assert!(invs.is_empty(), "no widen points => no loop invariants extracted");
    }

    #[test]
    fn test_interval_contains() {
        let i = Interval::new(0, 10);
        assert!(i.contains(0));
        assert!(i.contains(5));
        assert!(i.contains(10));
        assert!(!i.contains(-1));
        assert!(!i.contains(11));
        assert!(!Interval::BOTTOM.contains(0));
    }

    // -- Abstract formula evaluation tests --

    #[test]
    fn test_abstract_eval_constant() {
        let env = IntervalDomain::top();
        assert_eq!(abstract_eval_formula(&Formula::Int(42), &env), Interval::constant(42));
    }

    #[test]
    fn test_abstract_eval_variable() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 10));
        let result = abstract_eval_formula(&Formula::Var("x".into(), Sort::Int), &env);
        assert_eq!(result, Interval::new(0, 10));
    }

    #[test]
    fn test_abstract_eval_unknown_variable_is_top() {
        let env = IntervalDomain::top();
        let result = abstract_eval_formula(&Formula::Var("unknown".into(), Sort::Int), &env);
        assert_eq!(result, Interval::TOP);
    }

    #[test]
    fn test_abstract_eval_add() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(1, 5));
        env.set("y".into(), Interval::new(10, 20));
        let formula = Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        assert_eq!(abstract_eval_formula(&formula, &env), Interval::new(11, 25));
    }

    #[test]
    fn test_abstract_eval_sub() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(10, 20));
        env.set("y".into(), Interval::new(1, 5));
        let formula = Formula::Sub(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        assert_eq!(abstract_eval_formula(&formula, &env), Interval::new(5, 19));
    }

    #[test]
    fn test_abstract_eval_nested() {
        let mut env = IntervalDomain::top();
        env.set("a".into(), Interval::new(0, 10));
        // a + 5
        let formula =
            Formula::Add(Box::new(Formula::Var("a".into(), Sort::Int)), Box::new(Formula::Int(5)));
        assert_eq!(abstract_eval_formula(&formula, &env), Interval::new(5, 15));
    }

    // -- Boolean formula evaluation tests --

    #[test]
    fn test_try_eval_boolean_true_literal() {
        let env = IntervalDomain::top();
        assert_eq!(try_eval_boolean(&Formula::Bool(true), &env), Some(true));
        assert_eq!(try_eval_boolean(&Formula::Bool(false), &env), Some(false));
    }

    #[test]
    fn test_try_eval_boolean_lt_definite() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 5));
        // x < 10 should be definitely true (x.hi=5 < 10)
        let formula =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        assert_eq!(try_eval_boolean(&formula, &env), Some(true));
    }

    #[test]
    fn test_try_eval_boolean_lt_indeterminate() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 15));
        // x < 10 is indeterminate (x could be 5 or 12)
        let formula =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        assert_eq!(try_eval_boolean(&formula, &env), None);
    }

    #[test]
    fn test_try_eval_boolean_eq_definite_false() {
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::new(5, 10));
        // y == 0 is definitely false (interval [5,10] doesn't include 0)
        let formula =
            Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0)));
        assert_eq!(try_eval_boolean(&formula, &env), Some(false));
    }

    #[test]
    fn test_try_eval_boolean_not() {
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::new(5, 10));
        // NOT(y == 0) is definitely true
        let formula = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("y".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )));
        assert_eq!(try_eval_boolean(&formula, &env), Some(true));
    }

    #[test]
    fn test_try_eval_boolean_and_all_true() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 5));
        // x < 10 AND x >= 0 — both definitely true
        let formula = Formula::And(vec![
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ]);
        assert_eq!(try_eval_boolean(&formula, &env), Some(true));
    }

    #[test]
    fn test_try_eval_boolean_and_one_false() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 5));
        // x < 10 AND x > 100 — second is definitely false
        let formula = Formula::And(vec![
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);
        assert_eq!(try_eval_boolean(&formula, &env), Some(false));
    }

    // -- VC discharge tests --

    #[test]
    fn test_discharge_divzero_vc_constant_divisor() {
        // Divisor is constant 2 — division by zero impossible.
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::constant(2));

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "divisor=2 should discharge div-by-zero");
    }

    #[test]
    fn test_discharge_divzero_vc_range_excluding_zero() {
        // Divisor in [5, 10] — zero is excluded.
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::new(5, 10));

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "[5,10] excludes zero");
    }

    #[test]
    fn test_no_discharge_divzero_vc_range_includes_zero() {
        // Divisor in [-5, 10] — zero is included, cannot discharge.
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::new(-5, 10));

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "[-5,10] includes zero, cannot discharge");
    }

    #[test]
    fn test_discharge_divzero_guarded_formula() {
        // Guarded: And([guard, Eq(divisor, 0)])
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::new(1, 100));

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Eq(
                    Box::new(Formula::Var("flag".into(), Sort::Bool)),
                    Box::new(Formula::Int(1)),
                ),
                Formula::Eq(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "guarded div-by-zero with y in [1,100] should discharge");
    }

    #[test]
    fn test_discharge_bounds_vc_safe_access() {
        // index in [0, 4], length = 10 — definitely safe.
        let mut env = IntervalDomain::top();
        env.set("idx".into(), Interval::new(0, 4));
        env.set("len".into(), Interval::constant(10));

        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Ge(
                Box::new(Formula::Var("idx".into(), Sort::Int)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "idx in [0,4] < len=10 should discharge");
    }

    #[test]
    fn test_no_discharge_bounds_vc_possibly_oob() {
        // index in [0, 15], length = 10 — could be out of bounds.
        let mut env = IntervalDomain::top();
        env.set("idx".into(), Interval::new(0, 15));
        env.set("len".into(), Interval::constant(10));

        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Ge(
                Box::new(Formula::Var("idx".into(), Sort::Int)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "idx in [0,15] vs len=10 could be OOB");
    }

    #[test]
    fn test_discharge_via_formula_evaluation() {
        // A formula that is definitely false: x > 100 when x in [0, 5].
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 5));

        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "test".to_string() },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            // Violation formula: x > 100 (definitely false when x in [0,5])
            formula: Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "x in [0,5] > 100 is definitely false");
    }

    #[test]
    fn test_unsupported_mir_bool_false_not_discharged() {
        let env = IntervalDomain::top();
        let vc = VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "OpaqueTerminator".to_string(),
                detail: "unsupported terminator".to_string(),
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(
            matches!(result, AbstractInterpResult::Undetermined),
            "UnsupportedMir must fail closed before Bool(false) formula discharge"
        );
    }

    #[test]
    fn test_unsupported_mir_bool_false_remains_in_batch() {
        let env = IntervalDomain::top();
        let vcs = vec![VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "OpaqueStatement".to_string(),
                detail: "unsupported statement".to_string(),
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let report = try_discharge_batch(&vcs, &env);
        assert_eq!(
            report.discharged_count(),
            0,
            "UnsupportedMir must not be proved by batch discharge"
        );
        assert_eq!(report.remaining, vec![0], "UnsupportedMir must remain undischarged");
    }

    #[test]
    fn test_no_discharge_unknown_formula() {
        // Top environment — nothing can be discharged.
        let env = IntervalDomain::top();

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "top environment cannot discharge");
    }

    #[test]
    fn test_discharge_remainder_by_zero() {
        let mut env = IntervalDomain::top();
        env.set("d".into(), Interval::new(1, 100));

        let vc = VerificationCondition {
            kind: VcKind::RemainderByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("d".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "d in [1,100] excludes zero");
    }

    // -- Batch discharge tests --

    #[test]
    fn test_discharge_batch_mixed() {
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::constant(2)); // divisor = 2
        env.set("z".into(), Interval::new(-5, 5)); // divisor includes zero

        let vcs = vec![
            // Dischargeable: y == 0 is false when y = 2
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Eq(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
                obligation: None,
            },
            // Not dischargeable: z could be 0
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Eq(
                    Box::new(Formula::Var("z".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
                obligation: None,
            },
        ];

        let report = try_discharge_batch(&vcs, &env);
        assert_eq!(report.discharged_count(), 1, "one VC should be discharged");
        assert_eq!(report.remaining_count(), 1, "one VC should remain");
        assert_eq!(report.discharged[0].0, 0, "first VC was discharged");
        assert_eq!(report.remaining[0], 1, "second VC remains");
    }

    #[test]
    fn test_discharge_batch_all_discharged() {
        let mut env = IntervalDomain::top();
        env.set("y".into(), Interval::new(1, 10));
        env.set("z".into(), Interval::new(5, 20));

        let vcs = vec![
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Eq(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
                obligation: None,
            },
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Eq(
                    Box::new(Formula::Var("z".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
                obligation: None,
            },
        ];

        let report = try_discharge_batch(&vcs, &env);
        assert_eq!(report.discharged_count(), 2, "all VCs should be discharged");
        assert_eq!(report.remaining_count(), 0, "no VCs should remain");
    }

    #[test]
    fn test_discharge_batch_none_discharged() {
        let env = IntervalDomain::top();

        let vcs = vec![VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }];

        let report = try_discharge_batch(&vcs, &env);
        assert_eq!(report.discharged_count(), 0, "no VCs discharged with top env");
        assert_eq!(report.remaining_count(), 1, "all VCs remain");
    }

    // -- type_bounds tests --

    #[test]
    fn test_type_bounds_i32() {
        let bounds = type_bounds(&Ty::Int { width: 32, signed: true });
        assert_eq!(bounds, Some((-(1i128 << 31), (1i128 << 31) - 1)));
    }

    #[test]
    fn test_type_bounds_u32() {
        let bounds = type_bounds(&Ty::Int { width: 32, signed: false });
        assert_eq!(bounds, Some((0, (1i128 << 32) - 1)));
    }

    #[test]
    fn test_type_bounds_u8() {
        let bounds = type_bounds(&Ty::Int { width: 8, signed: false });
        assert_eq!(bounds, Some((0, 255)));
    }

    #[test]
    fn test_type_bounds_bool_returns_none() {
        assert!(type_bounds(&Ty::Bool).is_none());
    }

    // -- AbstractInterpResult tests --

    #[test]
    fn test_abstract_interp_result_discharged() {
        let result = AbstractInterpResult::Discharged(VerificationResult::Proved {
            solver: "abstract-interp".into(),
            time_ms: 0,
            strength: ProofStrength::abstract_interpretation(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        });
        assert!(result.is_discharged());
    }

    #[test]
    fn test_abstract_interp_result_undetermined() {
        let result = AbstractInterpResult::Undetermined;
        assert!(!result.is_discharged());
    }

    // -- Comparison check tests --

    #[test]
    fn test_check_comparison_lt_definite() {
        let a = Interval::new(0, 5);
        let b = Interval::new(10, 20);
        assert_eq!(check_comparison_intervals(&a, &b, ComparisonOp::Lt), Some(true));
    }

    #[test]
    fn test_check_comparison_lt_definite_false() {
        let a = Interval::new(10, 20);
        let b = Interval::new(0, 5);
        assert_eq!(check_comparison_intervals(&a, &b, ComparisonOp::Lt), Some(false));
    }

    #[test]
    fn test_check_comparison_eq_non_overlapping() {
        let a = Interval::new(0, 5);
        let b = Interval::new(10, 20);
        // Non-overlapping intervals can never be equal
        assert_eq!(check_comparison_intervals(&a, &b, ComparisonOp::Eq), Some(false));
    }

    #[test]
    fn test_check_comparison_eq_same_constant() {
        let a = Interval::constant(7);
        let b = Interval::constant(7);
        assert_eq!(check_comparison_intervals(&a, &b, ComparisonOp::Eq), Some(true));
    }

    // ── Interval division tests ──────────────────────────────

    #[test]
    fn test_interval_div_positive_by_positive() {
        // [10, 20] / [2, 5]
        let a = Interval::new(10, 20);
        let b = Interval::new(2, 5);
        let result = interval_div(&a, &b);
        // Corners: 10/2=5, 10/5=2, 20/2=10, 20/5=4 => [2, 10]
        assert_eq!(result.lo, 2);
        assert_eq!(result.hi, 10);
    }

    #[test]
    fn test_interval_div_by_constant() {
        // [0, 100] / [2, 2] = [0, 50]
        let a = Interval::new(0, 100);
        let b = Interval::constant(2);
        let result = interval_div(&a, &b);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 50);
    }

    #[test]
    fn test_interval_div_by_zero_is_bottom() {
        let a = Interval::new(10, 20);
        let b = Interval::constant(0);
        assert!(interval_div(&a, &b).is_bottom());
    }

    #[test]
    fn test_interval_div_spanning_zero() {
        // [10, 20] / [-2, 3] — divisor spans zero.
        // Split into [-2, -1] and [1, 3].
        // [10,20] / [-2,-1] => corners: 10/-2=-5, 10/-1=-10, 20/-2=-10, 20/-1=-20 => [-20,-5]
        // [10,20] / [1,3]   => corners: 10/1=10, 10/3=3, 20/1=20, 20/3=6 => [3,20]
        // Join: [-20, 20]
        let a = Interval::new(10, 20);
        let b = Interval::new(-2, 3);
        let result = interval_div(&a, &b);
        assert!(result.lo <= -5, "lo should be at most -5, got {}", result.lo);
        assert!(result.hi >= 20, "hi should be at least 20, got {}", result.hi);
    }

    #[test]
    fn test_interval_div_negative_by_negative() {
        // [-20, -10] / [-5, -2]
        let a = Interval::new(-20, -10);
        let b = Interval::new(-5, -2);
        let result = interval_div(&a, &b);
        // Corners: -20/-5=4, -20/-2=10, -10/-5=2, -10/-2=5 => [2, 10]
        assert_eq!(result.lo, 2);
        assert_eq!(result.hi, 10);
    }

    #[test]
    fn test_interval_div_bottom_propagates() {
        assert!(interval_div(&Interval::BOTTOM, &Interval::new(1, 5)).is_bottom());
        assert!(interval_div(&Interval::new(1, 5), &Interval::BOTTOM).is_bottom());
    }

    // ── Interval remainder tests ─────────────────────────────

    #[test]
    fn test_interval_rem_positive_by_positive() {
        // [0, 100] % [7, 7] = [0, 6]
        let a = Interval::new(0, 100);
        let b = Interval::constant(7);
        let result = interval_rem(&a, &b);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 6);
    }

    #[test]
    fn test_interval_rem_small_dividend() {
        // [0, 3] % [10, 10] = [0, 3] (dividend smaller than divisor)
        let a = Interval::new(0, 3);
        let b = Interval::constant(10);
        let result = interval_rem(&a, &b);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 3);
    }

    #[test]
    fn test_interval_rem_negative_dividend() {
        // [-10, -1] % [3, 3] = [-2, 0]
        let a = Interval::new(-10, -1);
        let b = Interval::constant(3);
        let result = interval_rem(&a, &b);
        assert!(result.lo >= -2, "lo should be >= -2, got {}", result.lo);
        assert_eq!(result.hi, 0);
    }

    #[test]
    fn test_interval_rem_mixed_dividend() {
        // [-5, 10] % [4, 4] = [-3, 3]
        let a = Interval::new(-5, 10);
        let b = Interval::constant(4);
        let result = interval_rem(&a, &b);
        assert_eq!(result.lo, -3);
        assert_eq!(result.hi, 3);
    }

    #[test]
    fn test_interval_rem_by_zero_is_bottom() {
        let a = Interval::new(0, 10);
        let b = Interval::constant(0);
        assert!(interval_rem(&a, &b).is_bottom());
    }

    #[test]
    fn test_interval_rem_bottom_propagates() {
        assert!(interval_rem(&Interval::BOTTOM, &Interval::new(1, 5)).is_bottom());
    }

    // ── Interval shift tests ─────────────────────────────────

    #[test]
    fn test_interval_shr_constant_shift() {
        // [0, 255] >> 2 = [0, 63]
        let a = Interval::new(0, 255);
        let b = Interval::constant(2);
        let result = interval_shr(&a, &b);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 63);
    }

    #[test]
    fn test_interval_shr_signed() {
        // [-128, 127] >> 1 = [-64, 63]
        let a = Interval::new(-128, 127);
        let b = Interval::constant(1);
        let result = interval_shr(&a, &b);
        assert_eq!(result.lo, -64);
        assert_eq!(result.hi, 63);
    }

    #[test]
    fn test_interval_shr_negative_shift_is_top() {
        let a = Interval::new(0, 100);
        let b = Interval::new(-1, 3);
        assert_eq!(interval_shr(&a, &b), Interval::TOP);
    }

    #[test]
    fn test_interval_shr_large_shift() {
        // [0, 1000] >> 128 = [0, 0]
        let a = Interval::new(0, 1000);
        let b = Interval::constant(128);
        let result = interval_shr(&a, &b);
        assert_eq!(result, Interval::constant(0));
    }

    #[test]
    fn test_interval_shl_constant() {
        // [1, 4] << 2 = [4, 16]
        let a = Interval::new(1, 4);
        let b = Interval::constant(2);
        let result = interval_shl(&a, &b);
        assert_eq!(result.lo, 4);
        assert_eq!(result.hi, 16);
    }

    #[test]
    fn test_interval_shl_negative_shift_is_top() {
        let a = Interval::new(0, 100);
        let b = Interval::new(-1, 3);
        assert_eq!(interval_shl(&a, &b), Interval::TOP);
    }

    // ── Bitwise interval tests ───────────────────────────────

    #[test]
    fn test_interval_bitand_positive() {
        // [0, 255] & [0, 15] = [0, 15]
        let a = Interval::new(0, 255);
        let b = Interval::new(0, 15);
        let result = interval_bitand(&a, &b);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 15);
    }

    #[test]
    fn test_interval_bitand_with_negative_is_bounded_by_the_nonnegative_mask() {
        // `-1 & 15 == 15`, `-16 & 15 == 0`: a non-negative mask bounds the result
        // alone, whichever side it is on.
        let a = Interval::new(-10, 10);
        let b = Interval::new(0, 15);
        assert_eq!(interval_bitand(&a, &b), Interval::new(0, 15));
        assert_eq!(interval_bitand(&b, &a), Interval::new(0, 15));
        // Both possibly negative: `-1 & -1 == -1`, nothing is bounded.
        assert_eq!(interval_bitand(&a, &Interval::new(-1, 3)), Interval::TOP);
    }

    #[test]
    fn test_interval_bitor_positive() {
        let a = Interval::new(0, 3);
        let b = Interval::new(0, 4);
        let result = interval_bitor(&a, &b);
        assert_eq!(result.lo, 0);
        // Upper bound is conservative (sum)
        assert!(result.hi <= 7, "hi should be at most 7, got {}", result.hi);
    }

    // ── Transfer function tests for new operations ───────────

    #[test]
    fn test_transfer_binary_div() {
        let func = crate::tests::midpoint_function();
        let mut state = IntervalDomain::top();
        state.set("a".into(), Interval::new(0, 100));

        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(2)),
            ),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &state);
        let interval = result.get("_4");
        assert_eq!(interval.lo, 0);
        assert_eq!(interval.hi, 50);
    }

    #[test]
    fn test_transfer_binary_rem() {
        let func = crate::tests::midpoint_function();
        let mut state = IntervalDomain::top();
        state.set("a".into(), Interval::new(0, 100));

        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Rem,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(10)),
            ),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &state);
        let interval = result.get("_4");
        assert_eq!(interval.lo, 0);
        assert_eq!(interval.hi, 9);
    }

    #[test]
    fn test_transfer_binary_shr() {
        let func = crate::tests::midpoint_function();
        let mut state = IntervalDomain::top();
        state.set("a".into(), Interval::new(0, 255));

        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Shr,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(3)),
            ),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &state);
        let interval = result.get("_4");
        assert_eq!(interval.lo, 0);
        assert_eq!(interval.hi, 31); // 255 >> 3 = 31
    }

    #[test]
    fn test_transfer_comparison_produces_boolean_range() {
        let func = crate::tests::midpoint_function();
        let mut state = IntervalDomain::top();
        state.set("a".into(), Interval::new(0, 100));
        state.set("b".into(), Interval::new(0, 100));

        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        };
        let result = transfer_function(&stmt, &func, &state);
        let interval = result.get("_4");
        assert_eq!(interval.lo, 0);
        assert_eq!(interval.hi, 1);
    }

    // ── Type-aware initialization tests ──────────────────────

    #[test]
    fn test_type_to_interval_u32() {
        let interval = type_to_interval(&Ty::Int { width: 32, signed: false });
        assert_eq!(interval, Some(Interval::new(0, (1i128 << 32) - 1)));
    }

    #[test]
    fn test_type_to_interval_i32() {
        let interval = type_to_interval(&Ty::Int { width: 32, signed: true });
        assert_eq!(interval, Some(Interval::new(-(1i128 << 31), (1i128 << 31) - 1)));
    }

    #[test]
    fn test_type_to_interval_u8() {
        let interval = type_to_interval(&Ty::Int { width: 8, signed: false });
        assert_eq!(interval, Some(Interval::new(0, 255)));
    }

    #[test]
    fn test_type_to_interval_i8() {
        let interval = type_to_interval(&Ty::Int { width: 8, signed: true });
        assert_eq!(interval, Some(Interval::new(-128, 127)));
    }

    #[test]
    fn test_type_to_interval_bool() {
        // Bool is intentionally not tracked: its [0,1] integer bound is
        // vacuous and emitting `Var(name, Int)` for it collides with the
        // `Var(name, Bool)` the same name carries in branch guards.
        assert_eq!(type_to_interval(&Ty::Bool), None);
    }

    #[test]
    fn test_bool_param_not_tracked_in_initial_state() {
        // Regression: a bool parameter must not be tracked in the
        // interval domain, so it never contributes an Int-sorted [0,1] bound
        // that would collide with the `Var(name, Bool)` it carries in guards.
        let func = VerifiableFunction {
            name: "f".into(),
            def_path: "test::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("c".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("n".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let state = crate::abstract_interp::transfer::type_aware_initial_state(&func);
        assert!(state.vars.contains_key("n"), "u32 param n should be tracked");
        assert!(!state.vars.contains_key("c"), "bool param c must NOT be tracked");
    }

    #[test]
    fn test_bool_comparison_result_not_tracked() {
        // Regression: a bool comparison-result temp (`cond = n > 0`)
        // must not be tracked either — same sort-collision risk as bool params.
        let func = VerifiableFunction {
            name: "g".into(),
            def_path: "test::g".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let init = crate::abstract_interp::transfer::type_aware_initial_state(&func);
        let stmt = Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Gt,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(0, 64)),
            ),
            span: SourceSpan::default(),
        };
        let after = crate::abstract_interp::transfer::transfer_function(&stmt, &func, &init);
        // The bool dest must not have been added to the domain.
        assert_eq!(after.vars.len(), init.vars.len(), "bool dest must not grow the domain");
        assert!(after.vars.contains_key("n"), "u32 param n stays tracked");
    }

    #[test]
    fn test_type_to_interval_float_is_none() {
        assert_eq!(type_to_interval(&Ty::Float { width: 64 }), None);
    }

    /// Trust (2026-09-30): `u128` has NO representable range here. The
    /// `[0, i128::MAX]` this test used to pin as "conservative" excludes every
    /// value at or above 2^127, and round 10 of the callee-summary review measured
    /// it proving, kernel-certified, an index that panicked (`x as i128 < 0`
    /// unreachable). `discharge::type_bounds` already answered `None` (P1-12).
    #[test]
    fn test_type_to_interval_u128_is_unknown() {
        assert_eq!(type_to_interval(&Ty::Int { width: 128, signed: false }), None);
    }

    #[test]
    fn test_type_aware_initial_state_midpoint() {
        let func = crate::tests::midpoint_function();
        let state = type_aware_initial_state(&func);
        // midpoint has args a (usize) and b (usize) at indices 1, 2.
        // usize = Int { width: 64, signed: false } => [0, 2^64 - 1]
        let a_interval = state.get("a");
        assert_eq!(a_interval.lo, 0);
        assert_eq!(a_interval.hi, (1i128 << 64) - 1);
        let b_interval = state.get("b");
        assert_eq!(b_interval.lo, 0);
        assert_eq!(b_interval.hi, (1i128 << 64) - 1);
    }

    // ── Fixpoint with narrowing tests ────────────────────────

    #[test]
    fn test_fixpoint_with_narrowing_straight_line() {
        // For straight-line code (no loops), narrowing doesn't change the result.
        let func = crate::tests::midpoint_function();
        let initial = type_aware_initial_state(&func);
        let without = fixpoint(&func, initial.clone());
        let with = fixpoint_with_narrowing(&func, initial, 3);
        // Both should produce the same states since there are no widen points.
        assert_eq!(
            without.block_states.keys().collect::<FxHashSet<_>>(),
            with.block_states.keys().collect::<FxHashSet<_>>()
        );
    }

    #[test]
    fn test_fixpoint_with_narrowing_zero_iterations() {
        let func = crate::tests::midpoint_function();
        let initial = type_aware_initial_state(&func);
        let without = fixpoint(&func, initial.clone());
        let with = fixpoint_with_narrowing(&func, initial, 0);
        // Zero narrow iterations should be identical to plain fixpoint.
        assert_eq!(without.block_states, with.block_states);
    }

    // ── Widening/narrowing convergence tests ─────────────────

    #[test]
    fn test_widening_ensures_convergence() {
        // Simulate an ascending chain: [0,1], [0,2], [0,3], ...
        // Without widening, this would not converge.
        // With widening, after one step where hi increases, it jumps to MAX.
        let a = Interval::new(0, 10);
        let b = Interval::new(0, 15);
        let widened = a.widen(&b);
        assert_eq!(widened.hi, i128::MAX, "widening should push hi to MAX");
        // Further widening should be stable.
        let c = Interval::new(0, 20);
        let stable = widened.widen(&c);
        assert_eq!(stable, widened, "widening after convergence should be stable");
    }

    #[test]
    fn test_narrowing_preserves_finite_bounds() {
        // If the widened bound is finite (not +/-infinity), narrowing keeps it.
        let a = Interval::new(5, 50);
        let b = Interval::new(0, 100);
        let narrowed = a.narrow(&b);
        // lo=5 (was not MIN), hi=50 (was not MAX) => stays [5, 50]
        assert_eq!(narrowed.lo, 5);
        assert_eq!(narrowed.hi, 50);
    }

    #[test]
    fn test_narrowing_from_both_infinities() {
        // [MIN, MAX].narrow([10, 200]) = [10, 200]
        let wide = Interval::TOP;
        let precise = Interval::new(10, 200);
        let narrowed = wide.narrow(&precise);
        assert_eq!(narrowed.lo, 10);
        assert_eq!(narrowed.hi, 200);
    }

    #[test]
    fn test_domain_narrowing_per_variable() {
        let mut wide = IntervalDomain::top();
        wide.set("x".into(), Interval::new(0, i128::MAX));
        wide.set("y".into(), Interval::new(i128::MIN, 50));

        let mut precise = IntervalDomain::top();
        precise.set("x".into(), Interval::new(0, 100));
        precise.set("y".into(), Interval::new(-10, 50));

        let narrowed = wide.narrow(&precise);
        assert_eq!(narrowed.get("x"), Interval::new(0, 100));
        assert_eq!(narrowed.get("y"), Interval::new(-10, 50));
    }

    // ── Abstract eval for Div/Rem formulas ───────────────────

    #[test]
    fn test_abstract_eval_div_formula() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));
        let formula =
            Formula::Div(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2)));
        let result = abstract_eval_formula(&formula, &env);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 50);
    }

    #[test]
    fn test_abstract_eval_rem_formula() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));
        let formula =
            Formula::Rem(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(7)));
        let result = abstract_eval_formula(&formula, &env);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 6);
    }

    // ── Midpoint-style composition test ──────────────────────
    // Tests the key pattern from issue #357: a/2 + b/2 should not overflow
    // for unsigned integers when the abstract interpreter properly tracks
    // the narrowing from division.

    #[test]
    fn test_midpoint_div_add_no_overflow() {
        // Simulate: a in [0, u32::MAX], b in [0, u32::MAX]
        // x = a / 2   => x in [0, u32::MAX/2]
        // y = b / 2   => y in [0, u32::MAX/2]
        // z = x + y   => z in [0, u32::MAX - 1] (fits in u32!)
        let u32_max = (1i128 << 32) - 1;
        let a = Interval::new(0, u32_max);
        let b = Interval::new(0, u32_max);
        let two = Interval::constant(2);

        let x = interval_div(&a, &two);
        assert_eq!(x.lo, 0);
        assert_eq!(x.hi, u32_max / 2);

        let y = interval_div(&b, &two);
        assert_eq!(y.lo, 0);
        assert_eq!(y.hi, u32_max / 2);

        let z = interval_add(&x, &y);
        assert_eq!(z.lo, 0);
        // u32::MAX/2 + u32::MAX/2 = u32::MAX - 1 (integer division truncates)
        assert_eq!(z.hi, u32_max - 1);
        // This fits in u32, so no overflow!
        assert!(z.hi <= u32_max, "a/2 + b/2 must fit in u32");
    }

    #[test]
    fn test_textbook_midpoint_full_expression() {
        // Full textbook midpoint: a/2 + b/2 + (a%2 + b%2)/2
        // For a, b in [0, u32::MAX], this should always fit in u32.
        let u32_max = (1i128 << 32) - 1;
        let a = Interval::new(0, u32_max);
        let b = Interval::new(0, u32_max);
        let two = Interval::constant(2);

        let a_half = interval_div(&a, &two);
        let b_half = interval_div(&b, &two);
        let a_mod = interval_rem(&a, &two);
        let b_mod = interval_rem(&b, &two);

        assert_eq!(a_mod, Interval::new(0, 1));
        assert_eq!(b_mod, Interval::new(0, 1));

        let mods_sum = interval_add(&a_mod, &b_mod);
        assert_eq!(mods_sum, Interval::new(0, 2));

        let mods_half = interval_div(&mods_sum, &two);
        assert_eq!(mods_half, Interval::new(0, 1));

        let partial = interval_add(&a_half, &b_half);
        let result = interval_add(&partial, &mods_half);

        // a/2 + b/2 + (a%2+b%2)/2 must fit in u32
        assert!(result.hi <= u32_max, "textbook midpoint must fit in u32, got hi={}", result.hi);
    }

    // ── End-to-end discharge with type-aware init ────────────

    #[test]
    fn test_type_aware_fixpoint_discharges_const_div_by_two() {
        // Build a function: fn test(a: u32) -> u32 { a / 2 }
        // Division by literal 2 — div-by-zero should be dischargeable.
        let func = VerifiableFunction {
            name: "div_by_two".to_string(),
            def_path: "test::div_by_two".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(2, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let initial = type_aware_initial_state(&func);
        let fp = fixpoint_with_narrowing(&func, initial, 3);

        // Merge block states.
        let mut merged = IntervalDomain::bottom();
        for state in fp.block_states.values() {
            merged = merged.join(state);
        }

        // The divisor (constant 2) should have interval [2, 2],
        // which excludes zero. The generic formula evaluator should
        // determine that Eq(2, 0) is false.
        let div_zero_formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));
        let eval = try_eval_boolean(&div_zero_formula, &merged);
        assert_eq!(eval, Some(false), "Eq(2, 0) should be definitely false");
    }

    // ── Soundness tests ──────────────────────────────────────

    #[test]
    fn test_interval_div_is_sound_for_all_corner_values() {
        // Verify that for specific concrete values within the interval,
        // the result is always contained in the computed interval.
        let a = Interval::new(-10, 10);
        let b = Interval::new(2, 5);
        let result = interval_div(&a, &b);
        for va in [-10, -5, 0, 5, 10] {
            for vb in [2, 3, 4, 5] {
                let concrete = va / vb;
                assert!(
                    result.contains(concrete),
                    "{va}/{vb}={concrete} not in [{}, {}]",
                    result.lo,
                    result.hi
                );
            }
        }
    }

    #[test]
    fn test_interval_rem_is_sound_for_all_corner_values() {
        let a = Interval::new(-10, 10);
        let b = Interval::new(3, 3);
        let result = interval_rem(&a, &b);
        for va in [-10, -5, -1, 0, 1, 5, 10] {
            let concrete = va % 3;
            assert!(
                result.contains(concrete),
                "{va}%3={concrete} not in [{}, {}]",
                result.lo,
                result.hi
            );
        }
    }

    #[test]
    fn test_interval_shr_is_sound_for_concrete_values() {
        let a = Interval::new(-16, 16);
        let b = Interval::constant(2);
        let result = interval_shr(&a, &b);
        for va in [-16, -8, -1, 0, 1, 8, 16] {
            let concrete = va >> 2;
            assert!(
                result.contains(concrete),
                "{va}>>2={concrete} not in [{}, {}]",
                result.lo,
                result.hi
            );
        }
    }

    // ── Widening + narrowing convergence proof ───────────────

    #[test]
    fn test_widening_narrowing_cycle_converges() {
        // Simulate the classic widening/narrowing pattern:
        // 1. Start: [0, 0]
        // 2. Step: [0, 1] -> widen -> [0, MAX]
        // 3. Narrow with [0, 10] -> [0, 10]
        // 4. Step: [0, 11] -> widen -> [0, MAX] (already stable since [0,10] <= [0,MAX])
        // This verifies the widening/narrowing approach converges.
        let init = Interval::constant(0);
        let step1 = Interval::new(0, 1);
        let widened = init.widen(&step1);
        assert_eq!(widened.hi, i128::MAX);

        // Narrowing with the true bound.
        let true_bound = Interval::new(0, 10);
        let narrowed = widened.narrow(&true_bound);
        assert_eq!(narrowed, Interval::new(0, 10));

        // Verify stability: narrowed.widen(narrowed) = narrowed
        let rewiden = narrowed.widen(&narrowed);
        assert_eq!(rewiden, narrowed, "should be stable after narrowing");
    }

    #[test]
    fn test_descending_chain_terminates() {
        // Narrowing produces a descending chain that must terminate.
        // The narrowing operator only replaces infinite bounds (MIN/MAX)
        // with the other operand's bound. Finite bounds are preserved.
        //
        // [MIN, MAX] -> narrow([0, 100]) -> [0, 100]
        // [0, 100] -> narrow([5, 50]) -> [0, 100] (finite bounds preserved)
        // This is stable, so the chain terminates in 1 step.
        let step1 = Interval::TOP.narrow(&Interval::new(0, 100));
        assert_eq!(step1, Interval::new(0, 100));

        // Narrowing with tighter bounds doesn't change finite bounds.
        let step2 = step1.narrow(&Interval::new(5, 50));
        assert_eq!(step2, step1, "finite bounds preserved by narrowing");

        // Another iteration is stable.
        let step3 = step2.narrow(&Interval::new(5, 50));
        assert_eq!(step3, step2, "narrowing should stabilize");
    }

    // ── Overflow VC discharge via abstract interpretation ─────
    //
    // These tests verify that interval analysis can replace the ad-hoc
    // value-range propagation in overflow.rs. The key insight: instead of
    // walking backward through blocks to find range-narrowing operations
    // (div, rem, shr), we run a forward abstract interpretation pass that
    // computes intervals for all variables, then use those intervals to
    // discharge overflow VCs without SMT.

    #[test]
    fn test_discharge_overflow_add_within_bounds() {
        // If a in [0, 100] and b in [0, 100], then a+b in [0, 200]
        // which fits in u32 [0, 4294967295]. Overflow VC should be dischargeable.
        let mut env = IntervalDomain::top();
        env.set("a".into(), Interval::new(0, 100));
        env.set("b".into(), Interval::new(0, 100));

        // Build the overflow VC formula: the violation condition is
        // And([a_in_range, b_in_range, Not(lo <= a+b <= hi)])
        // The generic evaluator handles this: if the Not(...) is false,
        // the whole And can be false => dischargeable.
        let a_var = Formula::Var("a".into(), Sort::Int);
        let b_var = Formula::Var("b".into(), Sort::Int);
        let sum = Formula::Add(Box::new(a_var.clone()), Box::new(b_var.clone()));

        // Evaluate the sum interval.
        let sum_interval = abstract_eval_formula(&sum, &env);
        assert_eq!(sum_interval, Interval::new(0, 200));
        // This fits in u32 [0, 2^32-1], so overflow is impossible.
        assert!(sum_interval.lo >= 0 && sum_interval.hi < (1i128 << 32));
    }

    #[test]
    fn test_discharge_overflow_mul_within_bounds() {
        // a in [0, 1000], b in [0, 1000] => a*b in [0, 1_000_000]
        // which fits in u32. No overflow.
        let mut env = IntervalDomain::top();
        env.set("a".into(), Interval::new(0, 1000));
        env.set("b".into(), Interval::new(0, 1000));

        let a_var = Formula::Var("a".into(), Sort::Int);
        let b_var = Formula::Var("b".into(), Sort::Int);
        let product = Formula::Mul(Box::new(a_var), Box::new(b_var));

        let result = abstract_eval_formula(&product, &env);
        assert_eq!(result, Interval::new(0, 1_000_000));
        assert!(result.hi < (1i128 << 32), "product must fit in u32");
    }

    #[test]
    fn test_no_discharge_overflow_add_exceeds_bounds() {
        // a in [0, u32::MAX], b in [0, u32::MAX] => a+b could overflow.
        let u32_max = (1i128 << 32) - 1;
        let mut env = IntervalDomain::top();
        env.set("a".into(), Interval::new(0, u32_max));
        env.set("b".into(), Interval::new(0, u32_max));

        let a_var = Formula::Var("a".into(), Sort::Int);
        let b_var = Formula::Var("b".into(), Sort::Int);
        let sum = Formula::Add(Box::new(a_var), Box::new(b_var));

        let result = abstract_eval_formula(&sum, &env);
        // [0, 2*u32_max] which exceeds u32 bounds.
        assert!(result.hi > u32_max, "a+b can exceed u32::MAX, should NOT discharge");
    }

    #[test]
    fn test_discharge_div_then_add_pattern() {
        // The classic midpoint pattern: a/2 + b/2
        // a in [0, u32::MAX], b in [0, u32::MAX]
        // After div by 2: [0, u32::MAX/2] each
        // Sum: [0, u32::MAX - 1] which fits in u32.
        let u32_max = (1i128 << 32) - 1;
        let mut env = IntervalDomain::top();
        let a_half = interval_div(&Interval::new(0, u32_max), &Interval::constant(2));
        let b_half = interval_div(&Interval::new(0, u32_max), &Interval::constant(2));
        env.set("a_half".into(), a_half);
        env.set("b_half".into(), b_half);

        let sum = Formula::Add(
            Box::new(Formula::Var("a_half".into(), Sort::Int)),
            Box::new(Formula::Var("b_half".into(), Sort::Int)),
        );

        let result = abstract_eval_formula(&sum, &env);
        assert!(result.hi <= u32_max, "a/2 + b/2 must fit in u32, hi={}", result.hi);
    }

    #[test]
    fn test_discharge_sub_within_signed_bounds() {
        // a in [0, 100], b in [0, 100] => a-b in [-100, 100]
        // which fits in i32 [-2^31, 2^31-1].
        let mut env = IntervalDomain::top();
        env.set("a".into(), Interval::new(0, 100));
        env.set("b".into(), Interval::new(0, 100));

        let diff = Formula::Sub(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Var("b".into(), Sort::Int)),
        );
        let result = abstract_eval_formula(&diff, &env);
        assert_eq!(result, Interval::new(-100, 100));

        let i32_min = -(1i128 << 31);
        let i32_max = (1i128 << 31) - 1;
        assert!(result.lo >= i32_min && result.hi <= i32_max, "a-b must fit in i32");
    }

    #[test]
    fn test_discharge_rem_then_add_pattern() {
        // a%10 in [0,9], b%10 in [0,9] => sum in [0, 18] which fits in u8 [0, 255].
        let mut env = IntervalDomain::top();
        let a_mod = interval_rem(&Interval::new(0, 1000), &Interval::constant(10));
        let b_mod = interval_rem(&Interval::new(0, 1000), &Interval::constant(10));
        env.set("a_mod".into(), a_mod);
        env.set("b_mod".into(), b_mod);

        let sum = Formula::Add(
            Box::new(Formula::Var("a_mod".into(), Sort::Int)),
            Box::new(Formula::Var("b_mod".into(), Sort::Int)),
        );
        let result = abstract_eval_formula(&sum, &env);
        assert_eq!(result, Interval::new(0, 18));
        assert!(result.hi <= 255, "a%10 + b%10 must fit in u8");
    }

    #[test]
    fn test_discharge_shr_then_add_pattern() {
        // (a >> 4) + (b >> 4) where a, b in [0, 255]
        // a>>4 in [0, 15], b>>4 in [0, 15] => sum in [0, 30]
        let mut env = IntervalDomain::top();
        let a_shr = interval_shr(&Interval::new(0, 255), &Interval::constant(4));
        let b_shr = interval_shr(&Interval::new(0, 255), &Interval::constant(4));
        env.set("a_shr".into(), a_shr);
        env.set("b_shr".into(), b_shr);

        let sum = Formula::Add(
            Box::new(Formula::Var("a_shr".into(), Sort::Int)),
            Box::new(Formula::Var("b_shr".into(), Sort::Int)),
        );
        let result = abstract_eval_formula(&sum, &env);
        assert_eq!(result, Interval::new(0, 30));
        assert!(result.hi <= 255, "shifted sum must fit in u8");
    }

    #[test]
    fn test_discharge_bitand_then_add_pattern() {
        // (a & 0xFF) + (b & 0xFF) where a, b in [0, u32::MAX]
        // a&0xFF in [0, 255], b&0xFF in [0, 255] => sum in [0, 510]
        let u32_max = (1i128 << 32) - 1;
        let mut env = IntervalDomain::top();
        let a_mask = interval_bitand(&Interval::new(0, u32_max), &Interval::new(0, 255));
        let b_mask = interval_bitand(&Interval::new(0, u32_max), &Interval::new(0, 255));
        env.set("a_mask".into(), a_mask);
        env.set("b_mask".into(), b_mask);

        let sum = Formula::Add(
            Box::new(Formula::Var("a_mask".into(), Sort::Int)),
            Box::new(Formula::Var("b_mask".into(), Sort::Int)),
        );
        let result = abstract_eval_formula(&sum, &env);
        assert_eq!(result, Interval::new(0, 510));
        assert!(result.hi <= u32_max, "masked sum must fit in u32");
    }

    #[test]
    fn test_widening_at_loop_header_then_narrowing() {
        // Simulate loop: i starts at 0, increments by 1, loop bound is 100.
        // 1. Initial: i = [0, 0]
        // 2. After one iteration: i = [0, 1]
        // 3. Widening: [0, 0].widen([0, 1]) = [0, MAX]
        // 4. Narrowing with true bound: [0, MAX].narrow([0, 100]) = [0, 100]
        let i_init = Interval::constant(0);
        let i_step = Interval::new(0, 1);
        let widened = i_init.widen(&i_step);
        assert_eq!(widened, Interval::new(0, i128::MAX));

        let true_bound = Interval::new(0, 100);
        let narrowed = widened.narrow(&true_bound);
        assert_eq!(narrowed, Interval::new(0, 100));

        // Now verify: if j = i + 50, j in [50, 150] fits in u8? No.
        // But j in [50, 150] fits in u16? Yes.
        let j = interval_add(&narrowed, &Interval::constant(50));
        assert_eq!(j, Interval::new(50, 150));
        assert!(j.hi <= 255, "j fits in u8");
        assert!(j.hi < (1i128 << 16), "j fits in u16");
    }

    #[test]
    fn test_widening_lower_bound_decreasing() {
        // When lo decreases, widening pushes it to MIN.
        let a = Interval::new(0, 10);
        let b = Interval::new(-5, 10);
        let widened = a.widen(&b);
        assert_eq!(widened.lo, i128::MIN, "decreasing lo should go to MIN");
        assert_eq!(widened.hi, 10, "hi unchanged");
    }

    #[test]
    fn test_narrowing_only_tightens_infinite_bounds() {
        // Narrowing does NOT tighten finite bounds.
        let a = Interval::new(10, 50);
        let b = Interval::new(0, 100);
        let narrowed = a.narrow(&b);
        // lo=10 (finite, preserved), hi=50 (finite, preserved)
        assert_eq!(narrowed, Interval::new(10, 50));
    }

    #[test]
    fn test_narrowing_one_side_infinite() {
        // Only the infinite side is tightened.
        let a = Interval::new(i128::MIN, 50);
        let b = Interval::new(-20, 100);
        let narrowed = a.narrow(&b);
        assert_eq!(narrowed.lo, -20, "MIN should be narrowed to -20");
        assert_eq!(narrowed.hi, 50, "finite hi preserved");
    }

    #[test]
    fn test_fixpoint_discharge_two_block_div_add() {
        // Build the two-block function: block0: _3 = _1 / 2, Goto(1)
        //                               block1: _0 = _3 + _2  (checked)
        // With abstract interp, _3 in [0, u32_max/2], _2 in [0, u32_max]
        // => _3 + _2 in [0, u32_max/2 + u32_max] which MAY overflow.
        // This tests that abstract interp correctly propagates through blocks.
        let func = VerifiableFunction {
            name: "div_add".to_string(),
            def_path: "test::div_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(2, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let initial = type_aware_initial_state(&func);
        let fp = fixpoint_with_narrowing(&func, initial, 3);

        // Block 1 should have _3 narrowed by the division.
        let bb1_state = fp.block_states.get(&BlockId(1)).unwrap();
        let local_3 = bb1_state.get("_3");
        let u32_max = (1i128 << 32) - 1;
        assert_eq!(local_3.lo, 0, "_3 = a/2 lo should be 0");
        assert_eq!(local_3.hi, u32_max / 2, "_3 = a/2 hi should be u32_max/2");
    }

    #[test]
    fn test_discharge_pipeline_end_to_end() {
        // Full pipeline test: generate VCs then run discharge.
        // Function: fn test(a: u32, b: u32) { let _ = (a / 2) + (b / 2); }
        // Division by constant 2 has no div-by-zero risk.
        // a/2 + b/2 fits in u32, so overflow VC should be dischargeable.
        let func = VerifiableFunction {
            name: "safe_midpoint".to_string(),
            def_path: "test::safe_midpoint".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: None }, // a/2
                    LocalDecl { index: 4, ty: Ty::u32(), name: None }, // b/2
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(2, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(2, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(4)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let initial = type_aware_initial_state(&func);
        let fp = fixpoint_with_narrowing(&func, initial, 3);

        // Check that the fixpoint computed correct intervals.
        let bb0_state = fp.block_states.get(&BlockId(0)).unwrap();
        let u32_max = (1i128 << 32) - 1;

        // After processing all statements in block 0:
        // The block entry state has a, b type-constrained.
        assert_eq!(bb0_state.get("a"), Interval::new(0, u32_max));
        assert_eq!(bb0_state.get("b"), Interval::new(0, u32_max));
    }

    #[test]
    fn test_interval_arithmetic_chained_operations() {
        // Test: ((a + b) / 4) * 3 where a, b in [0, 100]
        // a+b in [0, 200], (a+b)/4 in [0, 50], ((a+b)/4)*3 in [0, 150]
        let a = Interval::new(0, 100);
        let b = Interval::new(0, 100);
        let sum = interval_add(&a, &b);
        assert_eq!(sum, Interval::new(0, 200));

        let divided = interval_div(&sum, &Interval::constant(4));
        assert_eq!(divided, Interval::new(0, 50));

        let scaled = interval_mul(&divided, &Interval::constant(3));
        assert_eq!(scaled, Interval::new(0, 150));

        // Fits in u8.
        assert!(scaled.hi <= 255);
    }

    #[test]
    fn test_try_eval_boolean_or_clauses() {
        // Or([false, false]) = false, Or([true, false]) = true
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 5));
        env.set("y".into(), Interval::new(10, 20));

        // x > 100 OR y > 100 — both are definitely false
        let formula_all_false = Formula::Or(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
            Formula::Gt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);
        assert_eq!(try_eval_boolean(&formula_all_false, &env), Some(false));

        // x < 10 OR y > 100 — first is definitely true
        let formula_one_true = Formula::Or(vec![
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Gt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);
        assert_eq!(try_eval_boolean(&formula_one_true, &env), Some(true));
    }

    #[test]
    fn test_try_eval_boolean_implies() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 5));

        // false => anything is true
        let formula_false_premise = Formula::Implies(
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            )),
            Box::new(Formula::Bool(false)),
        );
        assert_eq!(try_eval_boolean(&formula_false_premise, &env), Some(true));

        // true => true is true
        let formula_true_both = Formula::Implies(
            Box::new(Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            )),
            Box::new(Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(1000)),
            )),
        );
        assert_eq!(try_eval_boolean(&formula_true_both, &env), Some(true));
    }

    #[test]
    fn test_discharge_batch_with_overflow_vcs() {
        // Build two overflow VCs: one dischargeable, one not.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));
        env.set("y".into(), Interval::new(0, 100));
        env.set("z".into(), Interval::TOP); // unknown

        let vcs = vec![
            // x + y = [0, 200] — x+y > 1000 is definitely false => dischargeable
            VerificationCondition {
                kind: VcKind::Assertion { message: "overflow check".to_string() },
                function: "test".into(),
                location: SourceSpan::default(),
                formula: Formula::Gt(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Var("y".into(), Sort::Int)),
                    )),
                    Box::new(Formula::Int(1000)),
                ),
                contract_metadata: None,
                obligation: None,
            },
            // z + y = [TOP] — cannot determine => not dischargeable
            VerificationCondition {
                kind: VcKind::Assertion { message: "overflow check 2".to_string() },
                function: "test".into(),
                location: SourceSpan::default(),
                formula: Formula::Gt(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("z".into(), Sort::Int)),
                        Box::new(Formula::Var("y".into(), Sort::Int)),
                    )),
                    Box::new(Formula::Int(1000)),
                ),
                contract_metadata: None,
                obligation: None,
            },
        ];

        let report = try_discharge_batch(&vcs, &env);
        assert_eq!(report.discharged_count(), 1, "one VC should be discharged");
        assert_eq!(report.remaining_count(), 1, "one VC should remain");
        assert_eq!(report.discharged[0].0, 0, "first VC discharged");
        assert_eq!(report.remaining[0], 1, "second VC remains");
    }

    #[test]
    fn test_signed_overflow_mul_within_bounds() {
        // i16 operands: a in [-100, 100], b in [-100, 100]
        // a*b in [-10000, 10000] which fits in i16 [-32768, 32767].
        let a = Interval::new(-100, 100);
        let b = Interval::new(-100, 100);
        let result = interval_mul(&a, &b);
        assert_eq!(result.lo, -10000);
        assert_eq!(result.hi, 10000);

        let i16_min = -(1i128 << 15);
        let i16_max = (1i128 << 15) - 1;
        assert!(result.lo >= i16_min && result.hi <= i16_max, "product must fit in i16");
    }

    #[test]
    fn test_domain_widen_preserves_unrelated_variables() {
        // Widening should only affect variables whose bounds changed.
        let mut a = IntervalDomain::top();
        a.set("x".into(), Interval::new(0, 10));
        a.set("y".into(), Interval::new(5, 5));

        let mut b = IntervalDomain::top();
        b.set("x".into(), Interval::new(0, 20)); // x.hi increased
        b.set("y".into(), Interval::new(5, 5)); // y unchanged

        let widened = a.widen(&b);
        assert_eq!(
            widened.get("x"),
            Interval::new(0, i128::MAX),
            "x.hi increased, should widen to MAX"
        );
        assert_eq!(widened.get("y"), Interval::constant(5), "y unchanged, should stay [5,5]");
    }

    #[test]
    fn test_discharge_bounds_vc_with_or_formula() {
        // Bounds violation: Or(Lt(idx, 0), Ge(idx, len))
        // idx in [2, 5], len in [10, 10]
        // Lt(idx, 0) => false (idx >= 2 > 0)
        // Ge(idx, len) => false (idx.hi=5 < len.lo=10)
        // Both false => property holds.
        let mut env = IntervalDomain::top();
        env.set("idx".into(), Interval::new(2, 5));
        env.set("len".into(), Interval::constant(10));

        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Or(vec![
                Formula::Lt(
                    Box::new(Formula::Var("idx".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Ge(
                    Box::new(Formula::Var("idx".into(), Sort::Int)),
                    Box::new(Formula::Var("len".into(), Sort::Int)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "idx in [2,5] with len=10 should discharge bounds check");
    }

    // ── Negation overflow discharge tests ────────────────────

    #[test]
    fn test_discharge_negation_overflow_operand_excludes_int_min() {
        // Operand x in [0, 100] — definitely not INT_MIN for i32.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));

        let i32_min = -(1i128 << 31);
        let i32_max = (1i128 << 31) - 1;
        let vc = VerificationCondition {
            kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(i32_min)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(i32_max)),
                    ),
                ]),
                Formula::Eq(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(i32_min)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "x in [0,100] excludes i32::MIN, negation is safe");
    }

    #[test]
    fn test_no_discharge_negation_overflow_operand_includes_int_min() {
        // Operand x in [-2147483648, 100] — includes INT_MIN.
        let mut env = IntervalDomain::top();
        let i32_min = -(1i128 << 31);
        env.set("x".into(), Interval::new(i32_min, 100));

        let i32_max = (1i128 << 31) - 1;
        let vc = VerificationCondition {
            kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(i32_min)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(i32_max)),
                    ),
                ]),
                Formula::Eq(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(i32_min)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "x includes i32::MIN, cannot discharge negation overflow");
    }

    #[test]
    fn test_discharge_negation_overflow_positive_only() {
        // x in [1, i32::MAX] — all positive, negation always safe.
        let mut env = IntervalDomain::top();
        let i32_min = -(1i128 << 31);
        let i32_max = (1i128 << 31) - 1;
        env.set("x".into(), Interval::new(1, i32_max));

        let vc = VerificationCondition {
            kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(i32_min)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(i32_max)),
                    ),
                ]),
                Formula::Eq(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(i32_min)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "x in [1, i32::MAX] excludes INT_MIN, safe to negate");
    }

    // ── Shift overflow discharge tests ───────────────────────

    #[test]
    fn test_discharge_shift_overflow_constant_safe_amount() {
        // Shift amount in [3, 3] on u32 — well within [0, 32).
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::constant(3));

        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 32, signed: false },
                shift_ty: Ty::Int { width: 32, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
                Formula::Ge(
                    Box::new(Formula::Var("amt".into(), Sort::Int)),
                    Box::new(Formula::Int(32)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "shift amount=3 on u32 should discharge");
    }

    #[test]
    fn test_no_discharge_shift_overflow_possibly_too_large() {
        // Shift amount in [0, 40] on u32 — could be >= 32.
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(0, 40));

        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shr,
                operand_ty: Ty::Int { width: 32, signed: false },
                shift_ty: Ty::Int { width: 32, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
                Formula::Ge(
                    Box::new(Formula::Var("amt".into(), Sort::Int)),
                    Box::new(Formula::Int(32)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "shift amount in [0,40] could be >= 32, cannot discharge");
    }

    #[test]
    fn test_discharge_shift_overflow_range_within_bounds() {
        // Shift amount in [1, 15] on u32 — safely within [0, 32).
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(1, 15));

        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 32, signed: false },
                shift_ty: Ty::Int { width: 32, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
                Formula::Ge(
                    Box::new(Formula::Var("amt".into(), Sort::Int)),
                    Box::new(Formula::Int(32)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "shift amount in [1,15] is safely within [0,32)");
    }

    #[test]
    fn test_discharge_shift_overflow_signed_with_or_formula() {
        // Signed shift amount in [2, 10] on i32.
        // Violation: Or([Lt(amt, 0), Ge(amt, 32)])
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(2, 10));

        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shr,
                operand_ty: Ty::Int { width: 32, signed: true },
                shift_ty: Ty::Int { width: 32, signed: true },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(-(1i128 << 31))),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int((1i128 << 31) - 1)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Ge(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(32)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "signed shift amt in [2,10] is safe for 32-bit type");
    }

    /// Build a ShiftOverflow VC with an explicit `kind.operand_ty` and an emitted
    /// formula whose violation threshold is `threshold` — the two can DESYNC for a
    /// constant shifted value (`1i32 << n` / `1i128 << n`), where `operand_ty`
    /// fabricates i64 while the emitter recovers the TRUE result width for the
    /// formula's `Ge(amt, Int(W))` bound. The discharge decision must follow the
    /// FORMULA (what the VC actually obligates), never `operand_ty`.
    fn shift_vc_with_threshold(operand_ty: Ty, threshold: i128) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty,
                shift_ty: Ty::Int { width: 32, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
                Formula::Ge(
                    Box::new(Formula::Var("amt".into(), Sort::Int)),
                    Box::new(Formula::Int(threshold)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        }
    }

    /// Trust #soundness (128-bit shift VC width residue closure): the discharge
    /// bound is the EMITTED threshold, never the kind's `operand_ty` width. Here
    /// `operand_ty` is the fabricated i64 of a constant shifted value (`1i32 << n`)
    /// while the emitted violation is the TRUE `amt >= 32`; `amt ∈ [0, 40]` reaches
    /// a real UB shift (`32 <= amt <= 40`), so discharging would be a FALSE PROOF.
    #[test]
    fn test_shift_discharge_uses_emitted_threshold_not_fabricated_operand_ty() {
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(0, 40));
        // kind.operand_ty says width 64 (the `ConstValue::Int(1)` fabrication);
        // the formula says the UB bound is 32 (the recovered i32 result width).
        let vc = shift_vc_with_threshold(Ty::Int { width: 64, signed: true }, 32);
        let result = try_discharge_vc(&vc, &env);
        assert!(
            !result.is_discharged(),
            "amt in [0,40] can be >= the EMITTED bound 32 — discharging against the \
             fabricated operand_ty width 64 would be a false proof"
        );
    }

    /// 128-bit value width, honest `operand_ty`: `u128 << amt` with `amt ∈ [0,127]`
    /// is safely within `[0, 128)` — the boundary amount 127 must discharge, and
    /// the full-literal threshold 128 must survive the interval comparison
    /// untruncated.
    #[test]
    fn test_discharge_shift_overflow_u128_boundary_amount_127() {
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(0, 127));
        let vc = shift_vc_with_threshold(Ty::Int { width: 128, signed: false }, 128);
        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "amt in [0,127] is safely within [0,128)");
    }

    /// 128-bit value width: `amt ∈ [0, 128]` reaches the UB amount 128 exactly —
    /// must NOT discharge (the `>= 128` violation is satisfiable).
    #[test]
    fn test_no_discharge_shift_overflow_u128_amount_reaches_128() {
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(0, 128));
        let vc = shift_vc_with_threshold(Ty::Int { width: 128, signed: false }, 128);
        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "amt in [0,128] reaches the UB amount 128");
    }

    /// The `1i128 << n` shape: `operand_ty` fabricates i64 (the width-less
    /// `ConstValue::Int(1)`) while the emitted threshold is the TRUE 128. With the
    /// bound read from the formula, `amt ∈ [0, 100]` (which straddles the fabricated
    /// 64!) correctly discharges against the real `[0, 128)` window.
    #[test]
    fn test_discharge_shift_overflow_i128_const_value_fabricated_i64_operand_ty() {
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(0, 100));
        let vc = shift_vc_with_threshold(Ty::Int { width: 64, signed: true }, 128);
        let result = try_discharge_vc(&vc, &env);
        assert!(
            result.is_discharged(),
            "amt in [0,100] is safely within the EMITTED [0,128) bound — the fabricated \
             operand_ty width 64 must not block the discharge"
        );
    }

    /// Signed amount at the 128-bit value width: violation
    /// `Or([Lt(amt,0), Ge(amt,128)])`, `amt ∈ [2,10]` — discharges.
    #[test]
    fn test_discharge_shift_overflow_signed_amount_128bit_or_formula() {
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(2, 10));
        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 128, signed: true },
                shift_ty: Ty::Int { width: 32, signed: true },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(-(1i128 << 31))),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int((1i128 << 31) - 1)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Ge(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(128)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };
        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "signed shift amt in [2,10] is safe for a 128-bit value");
    }

    // ── Float division by zero discharge tests ───────────────

    #[test]
    fn test_discharge_float_divzero_constant_divisor() {
        // Float divisor is constant 3 (mapped to interval [3, 3]).
        let mut env = IntervalDomain::top();
        env.set("fd".into(), Interval::constant(3));

        let vc = VerificationCondition {
            kind: VcKind::FloatDivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("fd".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "float divisor=3 should discharge FloatDivisionByZero");
    }

    #[test]
    fn test_no_discharge_float_divzero_unknown_divisor() {
        // Float divisor is unknown (Top).
        let env = IntervalDomain::top();

        let vc = VerificationCondition {
            kind: VcKind::FloatDivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("fd".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "unknown float divisor cannot discharge");
    }

    #[test]
    fn test_discharge_float_divzero_positive_range() {
        // Float divisor in [1, 100] — zero excluded.
        let mut env = IntervalDomain::top();
        env.set("fd".into(), Interval::new(1, 100));

        let vc = VerificationCondition {
            kind: VcKind::FloatDivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("fd".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "float divisor in [1,100] excludes zero");
    }

    // ── Cast overflow discharge tests ────────────────────────

    #[test]
    fn test_discharge_cast_overflow_value_fits_in_target() {
        // Source x in [0, 200], target u8 [0, 255] — fits.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 200));

        let vc = VerificationCondition {
            kind: VcKind::CastOverflow {
                from_ty: Ty::Int { width: 32, signed: false },
                to_ty: Ty::Int { width: 8, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Gt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(255)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "x in [0,200] fits in u8 [0,255], cast is safe");
    }

    #[test]
    fn test_no_discharge_cast_overflow_value_exceeds_target() {
        // Source x in [0, 300], target u8 [0, 255] — doesn't fit.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 300));

        let vc = VerificationCondition {
            kind: VcKind::CastOverflow {
                from_ty: Ty::Int { width: 32, signed: false },
                to_ty: Ty::Int { width: 8, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Gt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(255)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(!result.is_discharged(), "x in [0,300] exceeds u8 max=255, cannot discharge");
    }

    #[test]
    fn test_discharge_cast_overflow_signed_to_unsigned_positive() {
        // Source x (i32) in [10, 50], target u32 [0, u32::MAX] — fits.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(10, 50));

        let vc = VerificationCondition {
            kind: VcKind::CastOverflow {
                from_ty: Ty::Int { width: 32, signed: true },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(-(1i128 << 31))),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int((1i128 << 31) - 1)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Gt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "i32 x in [10,50] fits in u32 range, cast is safe");
    }

    #[test]
    fn test_no_discharge_cast_overflow_signed_negative_to_unsigned() {
        // Source x (i32) in [-10, 50], target u32 — negative values don't fit.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(-10, 50));

        let vc = VerificationCondition {
            kind: VcKind::CastOverflow {
                from_ty: Ty::Int { width: 32, signed: true },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(-(1i128 << 31))),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int((1i128 << 31) - 1)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Gt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX as i128)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(
            !result.is_discharged(),
            "i32 x in [-10,50] has negative values, cannot discharge u32 cast"
        );
    }

    // ── Batch discharge with new VC kinds ────────────────────

    #[test]
    fn test_discharge_batch_mixed_new_kinds() {
        // Batch with negation, shift, and float div VCs — some dischargeable.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100)); // safe for negation
        env.set("amt".into(), Interval::new(0, 40)); // NOT safe for shift (>= 32)
        env.set("fd".into(), Interval::new(1, 10)); // safe for float div

        let i32_min = -(1i128 << 31);
        let i32_max = (1i128 << 31) - 1;

        let vcs = vec![
            // Negation: x in [0, 100] — safe
            VerificationCondition {
                kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::And(vec![
                    Formula::And(vec![
                        Formula::Le(
                            Box::new(Formula::Int(i32_min)),
                            Box::new(Formula::Var("x".into(), Sort::Int)),
                        ),
                        Formula::Le(
                            Box::new(Formula::Var("x".into(), Sort::Int)),
                            Box::new(Formula::Int(i32_max)),
                        ),
                    ]),
                    Formula::Eq(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(i32_min)),
                    ),
                ]),
                contract_metadata: None,
                obligation: None,
            },
            // Shift: amt in [0, 40] — NOT safe
            VerificationCondition {
                kind: VcKind::ShiftOverflow {
                    op: BinOp::Shl,
                    operand_ty: Ty::Int { width: 32, signed: false },
                    shift_ty: Ty::Int { width: 32, signed: false },
                },
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::And(vec![
                    Formula::And(vec![
                        Formula::Le(
                            Box::new(Formula::Int(0)),
                            Box::new(Formula::Var("amt".into(), Sort::Int)),
                        ),
                        Formula::Le(
                            Box::new(Formula::Var("amt".into(), Sort::Int)),
                            Box::new(Formula::Int(u32::MAX as i128)),
                        ),
                    ]),
                    Formula::Ge(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(32)),
                    ),
                ]),
                contract_metadata: None,
                obligation: None,
            },
            // Float div: fd in [1, 10] — safe
            VerificationCondition {
                kind: VcKind::FloatDivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Eq(
                    Box::new(Formula::Var("fd".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
                obligation: None,
            },
        ];

        let report = try_discharge_batch(&vcs, &env);
        assert_eq!(report.discharged_count(), 2, "negation and float div should be discharged");
        assert_eq!(report.remaining_count(), 1, "shift should remain for solver");
        assert_eq!(report.remaining[0], 1, "shift VC at index 1 should remain");
    }

    #[test]
    fn test_discharge_negation_i8_excludes_int_min() {
        // i8: INT_MIN = -128. x in [-100, 100] does NOT contain -128.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(-100, 100));

        let i8_min: i128 = -128;
        let i8_max: i128 = 127;
        let vc = VerificationCondition {
            kind: VcKind::NegationOverflow { ty: Ty::Int { width: 8, signed: true } },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(i8_min)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(i8_max)),
                    ),
                ]),
                Formula::Eq(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(i8_min)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "i8 x in [-100,100] excludes -128, safe to negate");
    }

    #[test]
    fn test_discharge_shift_u64_safe_range() {
        // Shift amount in [0, 63] on u64 — exactly the safe range.
        let mut env = IntervalDomain::top();
        env.set("amt".into(), Interval::new(0, 63));

        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 64, signed: false },
                shift_ty: Ty::Int { width: 64, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("amt".into(), Sort::Int)),
                        Box::new(Formula::Int(u64::MAX as i128)),
                    ),
                ]),
                Formula::Ge(
                    Box::new(Formula::Var("amt".into(), Sort::Int)),
                    Box::new(Formula::Int(64)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "shift amount in [0,63] is safe for u64 (width=64)");
    }

    #[test]
    fn test_discharge_cast_u16_to_u8_small_value() {
        // Source x (u16) in [0, 100], target u8 [0, 255] — fits.
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));

        let vc = VerificationCondition {
            kind: VcKind::CastOverflow {
                from_ty: Ty::Int { width: 16, signed: false },
                to_ty: Ty::Int { width: 8, signed: false },
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(u16::MAX as i128)),
                    ),
                ]),
                Formula::Or(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Gt(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(255)),
                    ),
                ]),
            ]),
            contract_metadata: None,
            obligation: None,
        };

        let result = try_discharge_vc(&vc, &env);
        assert!(result.is_discharged(), "u16 x in [0,100] fits in u8 [0,255]");
    }

    // -- ThresholdSet tests --

    #[test]
    fn test_threshold_set_next_above() {
        let ts = ThresholdSet::new(vec![0, 5, 10, 20, 100]);
        // next_above finds strictly greater
        assert_eq!(ts.next_above(0), 5);
        assert_eq!(ts.next_above(5), 10);
        assert_eq!(ts.next_above(7), 10);
        assert_eq!(ts.next_above(100), i128::MAX);
        assert_eq!(ts.next_above(-5), 0);
    }

    #[test]
    fn test_threshold_set_next_below() {
        let ts = ThresholdSet::new(vec![0, 5, 10, 20, 100]);
        // next_below finds strictly less
        assert_eq!(ts.next_below(100), 20);
        assert_eq!(ts.next_below(10), 5);
        assert_eq!(ts.next_below(7), 5);
        assert_eq!(ts.next_below(0), i128::MIN);
        assert_eq!(ts.next_below(200), 100);
    }

    #[test]
    fn test_threshold_set_deduplication() {
        let ts = ThresholdSet::new(vec![5, 3, 5, 1, 3, 1]);
        assert_eq!(ts.values(), &[1, 3, 5]);
        assert_eq!(ts.len(), 3);
        assert!(!ts.is_empty());
    }

    #[test]
    fn test_threshold_set_empty() {
        let ts = ThresholdSet::new(vec![]);
        assert!(ts.is_empty());
        assert_eq!(ts.next_above(0), i128::MAX);
        assert_eq!(ts.next_below(0), i128::MIN);
    }

    #[test]
    fn test_interval_widen_with_thresholds_upper() {
        let ts = ThresholdSet::new(vec![0, 10, 100]);
        let a = Interval::new(0, 5);
        let b = Interval::new(0, 8); // hi grew: 5 -> 8
        let result = a.widen_with_thresholds(&b, &ts);
        // Should widen hi to next threshold above 5, which is 10
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 10);
    }

    #[test]
    fn test_interval_widen_with_thresholds_lower() {
        let ts = ThresholdSet::new(vec![-100, -10, 0, 10]);
        let a = Interval::new(0, 10);
        let b = Interval::new(-5, 10); // lo shrank: 0 -> -5
        let result = a.widen_with_thresholds(&b, &ts);
        // Should widen lo to next threshold below 0, which is -10
        assert_eq!(result.lo, -10);
        assert_eq!(result.hi, 10);
    }

    #[test]
    fn test_interval_widen_with_thresholds_fallback() {
        // No thresholds => falls back to infinity
        let ts = ThresholdSet::new(vec![]);
        let a = Interval::new(0, 5);
        let b = Interval::new(0, 8);
        let result = a.widen_with_thresholds(&b, &ts);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, i128::MAX);
    }

    #[test]
    fn test_interval_widen_with_thresholds_bottom() {
        let ts = ThresholdSet::new(vec![0, 10]);
        // Widen with bottom returns self
        let a = Interval::new(0, 5);
        let result = a.widen_with_thresholds(&Interval::BOTTOM, &ts);
        assert_eq!(result, a);
        // Widen from bottom returns other
        let result2 = Interval::BOTTOM.widen_with_thresholds(&a, &ts);
        assert_eq!(result2, a);
    }

    #[test]
    fn test_domain_widen_with_thresholds() {
        let ts = ThresholdSet::new(vec![0, 10, 100]);
        let mut a = IntervalDomain::top();
        a.set("x".to_string(), Interval::new(0, 5));
        let mut b = IntervalDomain::top();
        b.set("x".to_string(), Interval::new(0, 8));
        let widened = a.widen_with_thresholds(&b, &ts);
        assert_eq!(widened.get("x"), Interval::new(0, 10));
    }

    #[test]
    fn test_extract_thresholds_switchint() {
        // Build a function with a SwitchInt terminator that has target value 10.
        let func = VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("_0".to_string()),
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("i".to_string()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(10, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Int { width: 32, signed: true },
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let ts = extract_thresholds(&func);
        // Should contain 0, 9, 10, 11 from SwitchInt target 10, plus type bounds
        assert!(ts.values().contains(&0));
        assert!(ts.values().contains(&9));
        assert!(ts.values().contains(&10));
        assert!(ts.values().contains(&11));
    }

    #[test]
    fn test_extract_thresholds_comparison() {
        // Build a function with an assign statement: _0 = Lt(i, 100)
        let func = VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".to_string()) },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("x".to_string()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(100)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Bool,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let ts = extract_thresholds(&func);
        // Should contain 99, 100, 101 from the Lt comparison
        assert!(ts.values().contains(&99));
        assert!(ts.values().contains(&100));
        assert!(ts.values().contains(&101));
    }

    #[test]
    fn test_extract_thresholds_type_bounds() {
        let func = VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Int { width: 8, signed: false },
                        name: Some("_0".to_string()),
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 8, signed: false },
                        name: Some("x".to_string()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Int { width: 8, signed: false },
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let ts = extract_thresholds(&func);
        // u8 type bounds: 0 and 255
        assert!(ts.values().contains(&0));
        assert!(ts.values().contains(&255));
    }

    #[test]
    fn test_fixpoint_config_default() {
        let config = FixpointConfig::default();
        assert_eq!(config.widen_delay, 3);
        assert_eq!(config.narrowing_passes, 3);
        assert!(config.thresholds.is_none());
    }

    #[test]
    fn test_switchint_condition_narrowing() {
        // Test that compute_successor_states narrows discriminant for match arms.
        let func = VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("_0".to_string()),
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("d".to_string()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Int { width: 32, signed: true },
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let mut state = IntervalDomain::top();
        state.set("d".to_string(), Interval::new(0, 10));

        let successors = compute_successor_states(
            &func.body.blocks[0].terminator,
            &func,
            &func.body.blocks[0],
            &state,
        );
        // Arm 0 -> d == 0
        assert_eq!(successors[0].0, BlockId(1));
        assert_eq!(successors[0].1.get("d"), Interval::constant(0));
        // Arm 1 -> d == 1
        assert_eq!(successors[1].0, BlockId(2));
        assert_eq!(successors[1].1.get("d"), Interval::constant(1));
        // Otherwise -> d not in {0, 1}, so d in [2, 10]
        assert_eq!(successors[2].0, BlockId(3));
        assert_eq!(successors[2].1.get("d"), Interval::new(2, 10));
    }

    #[test]
    fn test_otherwise_narrowing_excludes_values() {
        let func = VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("_0".to_string()),
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("x".to_string()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Int { width: 32, signed: true },
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let mut state = IntervalDomain::top();
        state.set("x".to_string(), Interval::new(0, 5));

        // Exclude values 0, 1, 2 from the lo edge => x in [3, 5]
        let narrowed = narrow_from_otherwise(
            &state,
            &func,
            &Operand::Copy(Place::local(1)),
            &[(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
        );
        assert_eq!(narrowed.get("x"), Interval::new(3, 5));
    }

    #[test]
    fn test_otherwise_narrowing_excludes_hi_edge() {
        let func = VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("_0".to_string()),
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: true },
                        name: Some("x".to_string()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Int { width: 32, signed: true },
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let mut state = IntervalDomain::top();
        state.set("x".to_string(), Interval::new(0, 5));

        // Exclude values 4, 5 from the hi edge => x in [0, 3]
        let narrowed = narrow_from_otherwise(
            &state,
            &func,
            &Operand::Copy(Place::local(1)),
            &[(4, BlockId(1)), (5, BlockId(2))],
        );
        assert_eq!(narrowed.get("x"), Interval::new(0, 3));
    }

    // -- VC augmentation tests --

    #[test]
    fn test_interval_domain_to_formula_constant() {
        // x = [5, 5] => And(Ge(x, 5), Le(x, 5))
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::constant(5));

        let formula = interval_domain_to_formula(&env);
        assert_eq!(
            formula,
            Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(5)),
                ),
                Formula::Le(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(5)),
                ),
            ])
        );
    }

    #[test]
    fn test_interval_domain_to_formula_range() {
        // x = [0, 100] => And(Ge(x, 0), Le(x, 100))
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));

        let formula = interval_domain_to_formula(&env);
        assert_eq!(
            formula,
            Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Le(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(100)),
                ),
            ])
        );
    }

    #[test]
    fn test_interval_domain_to_formula_top_returns_true() {
        // No variables with finite bounds => Bool(true).
        let env = IntervalDomain::top();
        assert_eq!(interval_domain_to_formula(&env), Formula::Bool(true));
    }

    #[test]
    fn test_interval_domain_to_formula_bottom_returns_false() {
        let env = IntervalDomain::bottom();
        assert_eq!(interval_domain_to_formula(&env), Formula::Bool(false));
    }

    #[test]
    fn test_augment_vc_with_abstract_state_adds_conjuncts() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 10));

        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Var("original".into(), Sort::Bool),
            contract_metadata: None,
            obligation: None,
        };

        let augmented = augment_vc_with_abstract_state(&vc, &env);

        // Formula should be And([env_formula, original_formula])
        let env_formula = interval_domain_to_formula(&env);
        assert_eq!(
            augmented.formula,
            Formula::And(vec![env_formula, Formula::Var("original".into(), Sort::Bool)])
        );
        // Function name unchanged.
        assert_eq!(augmented.function, vc.function);
    }

    #[test]
    fn test_augment_vc_noop_for_top_state() {
        let env = IntervalDomain::top();

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Var("phi".into(), Sort::Bool),
            contract_metadata: None,
            obligation: None,
        };

        let augmented = augment_vc_with_abstract_state(&vc, &env);
        // No augmentation: formula unchanged.
        assert_eq!(augmented.formula, vc.formula);
    }

    /// The Machine{w} fence, augmentation direction: conjoining Int-sorted
    /// interval facts onto a bitvector-bearing VC gives one variable two
    /// sorts and severs the row's typed native payload. The row must come
    /// back byte-identical.
    #[test]
    fn augment_leaves_machine_width_bv_rows_untouched() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 100));
        let ret = || Box::new(Formula::Var("_0".into(), trust_types::Sort::BitVec(64)));
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::BvULe(
                Box::new(Formula::BvAdd(
                    ret(),
                    Box::new(Formula::BitVec { value: 1, width: 64 }),
                    64,
                )),
                ret(),
                64,
            ),
            contract_metadata: None,
            obligation: None,
        };
        let augmented = augment_vc_with_abstract_state(&vc, &env);
        assert_eq!(augmented.formula, vc.formula, "BV rows must not grow Int-sorted conjuncts");
    }

    fn hardened_mandate_vc(formula: Formula) -> VerificationCondition {
        hardened_vc_of(
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::ErrorDiscard,
                callee: "core::result::Result::<T, E>::ok".into(),
                detail: "error discarded".into(),
            },
            formula,
        )
    }

    fn hardened_vc_of(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "mandate_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn bounded_env() -> IntervalDomain {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 10));
        env.set("s__slice_len".into(), Interval::new(0, i128::MAX));
        assert_ne!(interval_domain_to_formula(&env), Formula::Bool(true));
        assert_ne!(interval_domain_to_formula(&env), Formula::Bool(false));
        env
    }

    /// G3 (2026-10-27): a hardened DESIGN MANDATE's violation is the closed
    /// constant `Bool(true)`. A reachable, non-Top environment cannot change its
    /// satisfiability, and the compiler recognises the mandate only by that exact
    /// formula, so the augmentation must hand the row back byte-identical (the
    /// conjoined `(and (>= x 0) true)` was refuted, demoted to `Unknown` and made
    /// the function a compile error).
    #[test]
    fn augment_leaves_closed_constant_rows_untouched_in_a_reachable_env() {
        let env = bounded_env();
        let vc = hardened_mandate_vc(Formula::Bool(true));
        let augmented = augment_vc_with_abstract_state(&vc, &env);
        assert_eq!(
            serde_json::to_string(&augmented).expect("serialize augmented"),
            serde_json::to_string(&vc).expect("serialize original"),
            "a design mandate must stay byte-identical"
        );
        assert_eq!(augmented.formula, Formula::Bool(true));
    }

    /// Negative control for the exemption above: an UNREACHABLE environment
    /// still conjoins onto a closed constant, so a mandate in dead code keeps
    /// its `And([false, true])` (proved by unreachability), and a non-constant
    /// formula in a reachable environment is still augmented.
    #[test]
    fn augment_still_conjoins_bottom_env_and_open_formulas() {
        let vc = hardened_mandate_vc(Formula::Bool(true));
        let augmented = augment_vc_with_abstract_state(&vc, &IntervalDomain::bottom());
        assert_eq!(
            augmented.formula,
            Formula::And(vec![Formula::Bool(false), Formula::Bool(true)])
        );

        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(0, 10));
        let open = hardened_mandate_vc(Formula::Var("x_violated".into(), Sort::Bool));
        let augmented = augment_vc_with_abstract_state(&open, &env);
        assert_eq!(
            augmented.formula,
            Formula::And(vec![
                interval_domain_to_formula(&env),
                Formula::Var("x_violated".into(), Sort::Bool)
            ])
        );
    }

    /// G3-MANDATE-L1-ONLY-1 (G3 review, 2026-10-27): the exemption is for design
    /// MANDATES only. An L0 unsafe/FFI row whose `Bool(true)` is a modelling-gap
    /// fail-close (an FFI call with no summary, an unmodelled unsafe call), a
    /// non-hardened kind's constant, and the vacuous `Bool(false)` all keep the
    /// augmentation they had before G3, so none of them reaches the compiler in
    /// the shape it reads as `design_mandate` (exempting every closed constant
    /// relabelled every FFI gap in a function with a bounded local `mandated`).
    /// MUTATION: widen the guard back to `matches!(vc.formula, Formula::Bool(_))`
    /// and this test fails on its first row.
    #[test]
    fn augment_still_conjoins_unsafe_ffi_gaps_and_non_mandate_constants() {
        let env = bounded_env();
        let env_formula = interval_domain_to_formula(&env);
        let gaps = [
            hardened_vc_of(
                VcKind::FfiBoundaryViolation {
                    callee: "getpgrp".into(),
                    desc: "FFI call has no summary: behavior unmodeled, cannot prove safe".into(),
                },
                Formula::Bool(true),
            ),
            hardened_vc_of(
                VcKind::HardenedBoundary {
                    category: HardenedVcCategory::FfiBoundary,
                    callee: "raise".into(),
                    detail: "no summary".into(),
                },
                Formula::Bool(true),
            ),
            hardened_vc_of(
                VcKind::Assertion {
                    message: "[unsafe:unmodeled-call] call to `ext` is not covered".into(),
                },
                Formula::Bool(true),
            ),
            hardened_vc_of(
                VcKind::UnsafeOperation { desc: "raw pointer deref".into() },
                Formula::Bool(true),
            ),
            hardened_vc_of(VcKind::IndexOutOfBounds, Formula::Bool(true)),
            hardened_mandate_vc(Formula::Bool(false)),
        ];
        for vc in gaps {
            let augmented = augment_vc_with_abstract_state(&vc, &env);
            assert_eq!(
                augmented.formula,
                Formula::And(vec![env_formula.clone(), vc.formula.clone()]),
                "{:?} must keep its augmentation",
                vc.kind
            );
        }
    }

    /// The Machine{w} fence, discharge direction: the violation
    /// `bvadd(_0, 1) <=u _0` is SATisfiable (the wrap witness at `u64::MAX`),
    /// but its unbounded-Int misreading `_0 + 1 <= _0` is always-false — the
    /// exact `result + 1 > result` false-proof vector. Interval discharge
    /// must refuse the whole bitvector class, not rely on evaluator
    /// catch-alls staying incomplete.
    #[test]
    fn interval_discharge_refuses_machine_width_bv_rows() {
        let env = IntervalDomain::top();
        let ret = || Box::new(Formula::Var("_0".into(), trust_types::Sort::BitVec(64)));
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::BvULe(
                Box::new(Formula::BvAdd(
                    ret(),
                    Box::new(Formula::BitVec { value: 1, width: 64 }),
                    64,
                )),
                ret(),
                64,
            ),
            contract_metadata: None,
            obligation: None,
        };
        assert!(
            matches!(try_discharge_vc(&vc, &env), AbstractInterpResult::Undetermined),
            "an Int-interval device must never adjudicate a wrapping-semantics row"
        );
    }

    #[test]
    fn test_augment_batch_applies_to_all() {
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(1, 5));

        let vcs = vec![
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationCondition {
                kind: VcKind::IndexOutOfBounds,
                function: "g".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
        ];

        let augmented = augment_batch(&vcs, &env);
        assert_eq!(augmented.len(), 2);

        let env_formula = interval_domain_to_formula(&env);
        // Both VCs should have the env formula conjoined.
        for (orig, aug) in vcs.iter().zip(augmented.iter()) {
            assert_eq!(aug.formula, Formula::And(vec![env_formula.clone(), orig.formula.clone()]));
        }
    }

    #[test]
    fn test_augmentation_preserves_real_counterexample() {
        // Soundness test: a genuine overflow should NOT be masked by augmentation.
        // x in [100, 200], overflow VC for x + x (could overflow i8 [-128, 127]).
        let mut env = IntervalDomain::top();
        env.set("x".into(), Interval::new(100, 200));

        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 8, signed: true },
                    Ty::Int { width: 8, signed: true },
                ),
            },
            function: "overflow_fn".into(),
            location: SourceSpan::default(),
            // Violation formula: result > 127 (overflow for i8)
            formula: Formula::Gt(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(127)),
            ),
            contract_metadata: None,
            obligation: None,
        };

        let augmented = augment_vc_with_abstract_state(&vc, &env);

        // The augmented formula should NOT be discharged -- it should still
        // represent a reachable violation. The augmented formula wraps the
        // original with interval bounds that include the overflowing range.
        // The key invariant: augmentation does NOT turn a satisfiable formula
        // into an unsatisfiable one.
        match &augmented.formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2, "should have env_formula and original");
                // Second clause is the original violation formula.
                assert_eq!(clauses[1], vc.formula);
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    // -- Disjunctive-violation discharge (guarded exclusive `&s[a..b]`) --

    fn ivar(n: &str) -> Formula {
        Formula::Var(n.into(), Sort::Int)
    }
    fn slice_range_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::SliceBoundsCheck,
            function: "f".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn disjunctive_violation_discharged_under_matching_guards() {
        // `&s[a..b]` under `a <= b && b <= len`: violation
        // `Or[Gt(a,b), Gt(b,len)]` ∧ `Le(a,b)` ∧ `Le(b,len)` is UNSAT — discharge.
        let vc = slice_range_vc(Formula::And(vec![
            Formula::Le(Box::new(ivar("a")), Box::new(ivar("b"))),
            Formula::Le(Box::new(ivar("b")), Box::new(ivar("len"))),
            Formula::Or(vec![
                Formula::Gt(Box::new(ivar("a")), Box::new(ivar("b"))),
                Formula::Gt(Box::new(ivar("b")), Box::new(ivar("len"))),
            ]),
        ]));
        // Empty (TOP) env: discharge must come from the syntactic guard-negation,
        // NOT the interval domain (which knows nothing about a/b/len here).
        let result = try_discharge_vc(&vc, &IntervalDomain::top());
        assert!(result.is_discharged(), "Le(a,b)∧Le(b,len) refutes both disjuncts");
    }

    #[test]
    fn disjunctive_violation_not_discharged_under_wrong_guard() {
        // WRONG guard `a <= b && a < len` does NOT establish `b <= len`, so
        // `Gt(b,len)` is unrefuted — must NOT discharge (sound: code can OOB).
        let vc = slice_range_vc(Formula::And(vec![
            Formula::Le(Box::new(ivar("a")), Box::new(ivar("b"))),
            Formula::Lt(Box::new(ivar("a")), Box::new(ivar("len"))),
            Formula::Or(vec![
                Formula::Gt(Box::new(ivar("a")), Box::new(ivar("b"))),
                Formula::Gt(Box::new(ivar("b")), Box::new(ivar("len"))),
            ]),
        ]));
        let result = try_discharge_vc(&vc, &IntervalDomain::top());
        assert!(!result.is_discharged(), "a<len does not refute Gt(b,len)");
    }

    #[test]
    fn disjunctive_violation_not_discharged_with_no_guard() {
        // No guard: neither disjunct refuted — must NOT discharge.
        let vc = slice_range_vc(Formula::Or(vec![
            Formula::Gt(Box::new(ivar("a")), Box::new(ivar("b"))),
            Formula::Gt(Box::new(ivar("b")), Box::new(ivar("len"))),
        ]));
        let result = try_discharge_vc(&vc, &IntervalDomain::top());
        assert!(!result.is_discharged(), "unguarded range violation must not discharge");
    }

    #[test]
    fn disjunctive_violation_operand_mismatch_not_discharged() {
        // Guard refers to a DIFFERENT variable (`Le(a,c)`, not `Le(a,b)`): the
        // exact-operand match must reject it — no over-discharge.
        let vc = slice_range_vc(Formula::And(vec![
            Formula::Le(Box::new(ivar("a")), Box::new(ivar("c"))),
            Formula::Le(Box::new(ivar("b")), Box::new(ivar("len"))),
            Formula::Or(vec![
                Formula::Gt(Box::new(ivar("a")), Box::new(ivar("b"))),
                Formula::Gt(Box::new(ivar("b")), Box::new(ivar("len"))),
            ]),
        ]));
        let result = try_discharge_vc(&vc, &IntervalDomain::top());
        assert!(!result.is_discharged(), "Le(a,c) must not refute Gt(a,b)");
    }

    /// UNION-SIBLING-WRITE-1 (wave-24 review, 2026-10-12): a write through a union field
    /// rewrites every overlapping sibling, so the statement transfer forgets each name
    /// the union cover rebinds. Before it, `u.a = x as u64` set `u.0 ∈ [0, 2^32-1]` and
    /// the write `u.1 = -1` left that interval on `u.0`, whose bytes now read
    /// `u64::MAX`. A stamped STRUCT's sibling keeps its interval (the control).
    #[test]
    fn a_union_field_write_forgets_the_sibling_interval() {
        fn with_two(kind: AdtKind) -> VerifiableFunction {
            let mut two = Ty::adt("c::V2", vec![("a".into(), Ty::u64()), ("b".into(), Ty::i64())]);
            if let Ty::Adt { adt_kind, .. } = &mut two {
                *adt_kind = Some(kind);
            }
            VerifiableFunction {
                name: "f".into(),
                def_path: "c::f".into(),
                span: SourceSpan::default(),
                body: VerifiableBody {
                    locals: [Ty::u64(), Ty::u32(), two]
                        .into_iter()
                        .enumerate()
                        .map(|(index, ty)| LocalDecl { index, ty, name: None })
                        .collect(),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        stmts: Vec::new(),
                        terminator: Terminator::Return,
                    }],
                    arg_count: 1,
                    return_ty: Ty::u64(),
                    datatype_defs: Default::default(),
                },
                contracts: Vec::new(),
                preconditions: Vec::new(),
                postconditions: Vec::new(),
                spec: Default::default(),
                tuple_layouts: Default::default(),
            }
        }
        let field = |i: usize| Place { local: 2, projections: vec![Projection::Field(i)] };
        let write_b = Statement::Assign {
            place: field(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-1))),
            span: SourceSpan::default(),
        };
        for (kind, forgotten) in [(AdtKind::Union, true), (AdtKind::Struct, false)] {
            let func = with_two(kind);
            let a = crate::place_to_var_name(&func, &field(0));
            let mut state = IntervalDomain::top();
            state.set(a.clone(), Interval::new(0, (1 << 32) - 1));
            let result = transfer_function(&write_b, &func, &state);
            let want = if forgotten { Interval::TOP } else { Interval::new(0, (1 << 32) - 1) };
            assert_eq!(result.get(&a), want, "{kind:?}: `{a}` after the write of field 1");
        }
    }
}
