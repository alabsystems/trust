//! `flip.rs`'s CENSUS: the frozen flip gate's production section, pin -> tree, token for token.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! WHY. `src/flip.rs` is blob-frozen (`scripts/frozen-files.txt`): `derive_flip_body` is the
//! last gate a derived body passes before `optimized_mir` is replaced by it. Its gates take a
//! `TyCtxt`, so nothing compiles the pinned and current gates side by side the way
//! `flip_registry_refinement_tests.rs` does. What CAN be executed is (a) WHICH production tokens
//! moved — the ordered line diff pin -> tree, full-line comments and blank lines removed, by the
//! same lexer `mir_differential_refinement_tests.rs` uses — which must equal the current
//! waiver's `TEXT_DELTA` exactly, and (b) every `TyCtxt`-free function the movement adds, run
//! over its whole input space. That the moved call site sits where the census says it sits, and
//! refuses through `rejected`, is visible in (a); that `derive_flip_body` is the only installer
//! of a derived body is the frozen file's standing structure, not re-argued here.
//!
//! WHEN THE PIN MOVES. Ratifying at the working tree's blob needs no edit (the delta is then
//! empty and asserted empty). The next movement writes its own `TEXT_DELTA`.

mod pin_meta {
    include!(concat!(env!("OUT_DIR"), "/flip_pin_meta.rs"));
}

mod instance_pin_meta {
    include!(concat!(env!("OUT_DIR"), "/instance_flip_pin_meta.rs"));
}

/// The CURRENT waiver's movement of `instance_flip.rs` (1.101 port): upstream wrapped
/// the interned generic-args list in the `GenericArgs` newtype, so the one parameter
/// spelled through the old `GenericArgsRef` alias is respelled by value — the same
/// interned list reaches the same consumer. (The F2 spread-argument refusal this block
/// used to name is in the pin since ratification, so it is no part of the delta.)
#[cfg(trust_frozen_pin_instance_flip)]
mod instance_waived_delta {
    pub(super) const TEXT_DELTA: &[&str] =
        &["-    args: ty::GenericArgsRef<'tcx>,", "+    args: ty::GenericArgs<'tcx>,"];
}

/// FAIL-CLOSED: no baseline, no green.
#[cfg(not(trust_frozen_pin_instance_flip))]
#[test]
fn the_pinned_instance_flip_could_not_be_read() {
    panic!("instance_flip.rs census has NO BASELINE: {}.", instance_pin_meta::PIN_UNAVAILABLE);
}

/// THE CENSUS of `instance_flip.rs`: the instance lane's production section moved pin -> tree
/// by exactly the waived movement — the 1.101 `GenericArgs` respelling of one parameter,
/// in place, and nothing else.
#[cfg(all(trust_frozen_pin_instance_flip, trust_frozen_pin_mir_differential))]
#[test]
fn the_instance_flip_production_delta_is_exactly_the_waived_one() {
    use crate::mir_differential_refinement_tests::armed::{line_delta, production_lines};
    const PINNED: &str = include_str!(concat!(env!("OUT_DIR"), "/instance_flip_pinned.rs"));
    const CURRENT: &str = include_str!(concat!(env!("OUT_DIR"), "/instance_flip_current.rs"));
    let delta = line_delta(&production_lines(PINNED), &production_lines(CURRENT));
    if instance_pin_meta::PIN_IS_CURRENT {
        assert!(delta.is_empty(), "pinned == current, yet the census found a delta: {delta:#?}");
        return;
    }
    let expected: Vec<String> =
        instance_waived_delta::TEXT_DELTA.iter().map(|l| l.to_string()).collect();
    assert!(
        delta == expected,
        "instance_flip.rs moved by a delta no waiver names. MEASURED:\n{}",
        delta.iter().map(|l| format!("        {l:?},")).collect::<Vec<_>>().join("\n")
    );
    // The one deleted line is the respelling's old spelling, and it comes back
    // immediately after, in place (the same discipline as flip.rs's `Goto` pair).
    let deleted: Vec<&String> = delta.iter().filter(|l| !l.starts_with('+')).collect();
    assert_eq!(
        deleted,
        ["-    args: ty::GenericArgsRef<'tcx>,"],
        "the waived movement deletes a production line other than the respelled parameter"
    );
    let back = "+    args: ty::GenericArgs<'tcx>,";
    let at = delta.iter().position(|l| l == back).expect("the respelled parameter");
    assert_eq!(&delta[at - 1], deleted[0], "the parameter is respelled in place");
}

/// The CURRENT waiver's movement (shift-count mask, 2026-10-03, plus the 1.101 `Goto`
/// respelling below; the F2 spread-argument refusal this block used to name is in the
/// pin since the 2026-09-30 ratification).
#[cfg(trust_frozen_pin_flip)]
mod waived_delta {
    /// Pin -> tree, full-line comments and blank lines removed. One refusal widened in
    /// `const_trap_gate`, nothing else. The direct THIR producer now spells a checks-off shift
    /// count `amount & (BITS - 1)` (`emit_masked_shift_count`), so a LITERAL count reaches the
    /// shift as the `And` of two constants instead of as a constant. The insertion collects
    /// those `And` results (`masked_const_vals`, read by nothing but the guard below), and the
    /// shift arm's refusal guard `is_const(rhs)` becomes `is_const(rhs) ||
    /// masked_const_vals.contains(rhs)`: the pin's guard is the first disjunct of the new one,
    /// in an arm that only returns `Err`. Every module the pin refused is refused; a module is
    /// newly refused only for a shift by an `And` of two constants. The flip population of the
    /// masked producer is therefore the unmasked producer's.
    pub(super) const TEXT_DELTA: &[&str] = &[
        "+    let mut masked_const_vals: HashSet<ValueId> = HashSet::new();",
        "+            if let Inst::BinOp { op: BinOp::And, lhs, rhs, .. } = &node.inst {",
        "+                if is_const(lhs) && is_const(rhs) {",
        "+                    masked_const_vals.extend(node.results.iter().copied());",
        "+                }",
        "+            }",
        "+        }",
        "+    }",
        // The LCS aligns the inserted collection loop's header with the gate loop's, so the
        // diff reports the loop header pair after the inserted body: the same text, spelled
        // the way the diff spells it.
        "+    for blk in &func.blocks {",
        "+        for node in &blk.body {",
        "-                    if is_const(rhs) =>",
        "+                    if is_const(rhs) || masked_const_vals.contains(rhs) =>",
        // (1.101) API respelling only: `TerminatorKind::Goto` gained `loop_hint_attrs`,
        // so the two patterns that read only `target` gain `..`. Same terminators
        // matched, same field read.
        "-            TerminatorKind::Goto { target } => target_ok(*target)?,",
        "+            TerminatorKind::Goto { target, .. } => target_ok(*target)?,",
        "-            TerminatorKind::Goto { target } => vec![*target],",
        "+            TerminatorKind::Goto { target, .. } => vec![*target],",
    ];
}

/// FAIL-CLOSED: no baseline, no green.
#[cfg(not(trust_frozen_pin_flip))]
#[test]
fn the_pinned_flip_could_not_be_read() {
    panic!(
        "flip.rs census has NO BASELINE: {}. Until the blob scripts/frozen-files.txt pins for \
         crates/trust-thir-lower/src/flip.rs can be read out of git here, nothing checks which \
         of its production tokens moved.",
        pin_meta::PIN_UNAVAILABLE
    );
}

#[cfg(all(trust_frozen_pin_flip, not(trust_frozen_pin_mir_differential)))]
#[test]
fn the_census_lexer_is_unavailable() {
    panic!(
        "flip.rs census needs the mir_differential harness's lexer, which is compiled only when \
         that harness has its baseline"
    );
}

#[cfg(all(trust_frozen_pin_flip, trust_frozen_pin_mir_differential))]
mod armed {
    use rustc_middle::mir::Local;

    use super::{pin_meta, waived_delta};
    use crate::flip::spread_arg_refusal;
    use crate::mir_differential_refinement_tests::armed::{line_delta, production_lines};

    const PINNED_SECTION: &str = include_str!(concat!(env!("OUT_DIR"), "/flip_pinned.rs"));
    const CURRENT_SECTION: &str = include_str!(concat!(env!("OUT_DIR"), "/flip_current.rs"));

    fn production_delta() -> Vec<String> {
        line_delta(&production_lines(PINNED_SECTION), &production_lines(CURRENT_SECTION))
    }

    /// THE CENSUS. Every production token that moved pin -> tree is one the waiver names.
    #[test]
    fn the_flip_production_delta_is_exactly_the_waived_one() {
        let delta = production_delta();
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
            "flip.rs's production section moved by a delta no waiver names. MEASURED delta (pin \
             -> tree, full-line comments and blank lines removed), in `waived_delta::TEXT_DELTA` \
             spelling:\n{}",
            delta.iter().map(|l| format!("        {l:?},")).collect::<Vec<_>>().join("\n")
        );
        // REFUSES MORE, ADMITS NOTHING NEW, at the token level (shift-count mask, 2026-10-03):
        // of the deleted production lines, one is the shift arm's refusal guard, and it comes
        // back as the first disjunct of its replacement; the other two are the 1.101 `Goto`
        // patterns, each coming back with only `, ..` added. Everything else is an insertion,
        // and the set the insertion fills is read by that guard and nothing else.
        let deleted: Vec<&String> = delta.iter().filter(|l| !l.starts_with('+')).collect();
        assert_eq!(
            deleted,
            [
                "-                    if is_const(rhs) =>",
                "-            TerminatorKind::Goto { target } => target_ok(*target)?,",
                "-            TerminatorKind::Goto { target } => vec![*target],",
            ],
            "the waived movement deletes a production line other than the shift refusal's \
             guard and the two `Goto` patterns"
        );
        for gone in &deleted[1..] {
            let back = format!("+{}", gone[1..].replace("{ target }", "{ target, .. }"));
            let at = delta.iter().position(|l| l == &back).expect("the respelled Goto pattern");
            assert_eq!(&delta[at - 1], *gone, "the Goto pattern is respelled in place");
        }
        let guard = "+                    if is_const(rhs) || masked_const_vals.contains(rhs) =>";
        let at = delta.iter().position(|l| l == guard).expect("the widened guard");
        assert_eq!(delta[at - 1], *deleted[0], "the guard is replaced in place");
        let readers: Vec<&String> = delta
            .iter()
            .filter(|l| l.contains("masked_const_vals") && !l.contains("masked_const_vals.extend"))
            .filter(|l| !l.contains("let mut masked_const_vals"))
            .collect();
        assert_eq!(readers, [guard], "the inserted set is read only by the refusal guard");
    }

    /// The widened gate over its whole input shape (a shift's count is a constant, the `And` of
    /// two constants, the `And` of a non-constant and a constant, or a non-constant; for each,
    /// `Shl`, `LShr` and `AShr`): it refuses every module the pinned guard (`is_const(rhs)`)
    /// refused, newly refuses exactly the `And`-of-two-constants count, and admits the rest as
    /// the pin did. A non-shift use of such an `And` stays admitted: the set is read only by the
    /// shift arm.
    #[test]
    fn the_masked_const_shift_refusal_refuses_more_and_admits_nothing_new() {
        use trust_ir::{
            BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
            ValueId,
        };

        use crate::flip::const_trap_gate;

        let v = ValueId::new;
        let konst = |value: i128, result: u32| {
            InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(value) })
                .with_result(v(result))
        };
        let binop = |op: BinOp, lhs: u32, rhs: u32, result: u32| {
            InstrNode::new(Inst::BinOp { op, ty: Ty::U32, lhs: v(lhs), rhs: v(rhs) })
                .with_result(v(result))
        };
        let module = |body: Vec<InstrNode>| {
            let mut module = Module::new("const_trap_gate_probe");
            let ty = module
                .add_func_type(FuncTy {
                    params: Vec::new(),
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                })
                .expect("Module::add_func_type: test fixture");
            let mut function = Function::new(FuncId::new(0), "probe", ty, BlockId::new(0));
            let mut entry = Block::new(BlockId::new(0));
            entry.body = body;
            function.blocks.push(entry);
            module.try_add_function(function).expect("Module::try_add_function: test fixture");
            module
        };
        // `v(0)` (the shifted value) and `v(1)` (a count) are never defined by a `Const`: the
        // gate reads them as non-constant, as it reads a parameter.
        #[derive(Debug, Clone, Copy, PartialEq)]
        enum Count {
            Literal,
            MaskedLiteral,
            MaskedSymbolic,
            Symbolic,
        }
        let count = |shape: Count| -> (Vec<InstrNode>, u32) {
            match shape {
                Count::Literal => (vec![konst(33, 2)], 2),
                Count::MaskedLiteral => {
                    (vec![konst(33, 2), konst(31, 3), binop(BinOp::And, 2, 3, 4)], 4)
                }
                Count::MaskedSymbolic => (vec![konst(31, 3), binop(BinOp::And, 1, 3, 4)], 4),
                Count::Symbolic => (Vec::new(), 1),
            }
        };
        let mut newly_refused = 0;
        for shape in [Count::Literal, Count::MaskedLiteral, Count::MaskedSymbolic, Count::Symbolic]
        {
            for op in [BinOp::Shl, BinOp::LShr, BinOp::AShr] {
                let (mut body, amount) = count(shape);
                body.push(binop(op, 0, amount, 9));
                let verdict = const_trap_gate(&module(body));
                let pinned_refuses = shape == Count::Literal;
                let refuses = pinned_refuses || shape == Count::MaskedLiteral;
                assert_eq!(verdict.is_err(), refuses, "{shape:?} {op:?}: {verdict:?}");
                if pinned_refuses {
                    assert!(verdict.is_err(), "admits a module the pin refused: {shape:?} {op:?}");
                }
                newly_refused += usize::from(verdict.is_err() && !pinned_refuses);
            }
        }
        assert_eq!(newly_refused, 3, "only the masked literal count is newly refused");
        // The `And` of two constants used by anything but a shift count is not a refusal.
        let not_a_shift = vec![konst(33, 2), konst(31, 3), binop(BinOp::And, 2, 3, 4)];
        assert_eq!(const_trap_gate(&module(not_a_shift)), Ok(()));
    }

    /// The decision itself, over every pairing of "no spread" and three argument locals: it
    /// refuses exactly when the derived body spreads a different argument than built, and
    /// NOTHING else — in particular it never refuses the ordinary `None`/`None` body.
    #[test]
    fn the_spread_arg_refusal_refuses_every_mismatch_and_nothing_else() {
        let space = [
            None,
            Some(Local::from_usize(1)),
            Some(Local::from_usize(2)),
            Some(Local::from_usize(3)),
        ];
        let mut refused = 0;
        for derived in space {
            for built in space {
                let verdict = spread_arg_refusal(derived, built);
                assert_eq!(
                    verdict.is_some(),
                    derived != built,
                    "derived {derived:?} vs built {built:?}: {verdict:?}"
                );
                refused += usize::from(verdict.is_some());
            }
        }
        assert_eq!(refused, 12, "4 x 4 pairings, 4 of them agreeing");
        // The measured shape (F2): a non-closure `extern "rust-call"` body — built spreads its
        // last argument, `Body::new` spreads nothing.
        assert!(spread_arg_refusal(None, Some(Local::from_usize(2))).is_some());
    }
}
