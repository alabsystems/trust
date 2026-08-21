// Trust (wave-CP, 2026-08-19) — the CHECKED-CHAIN PARAMETER-LEAF storage-marker fidelity probe.
//
// Compile with the trust driver and read both channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=cpprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Cdebug-assertions=off -Cpanic=abort -Coverflow-checks=on \
//     -Zdump-mir=all -Zdump-mir-dir=MIR -Ztrust-dump=ir:IR \
//     probes/cp_leaf.rs --out-dir OUT
//
// `IR/cpprobe.coverage.json`'s `derived_mir.markers_exact` is the oracle's verdict, and
// `RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info` on stderr is where the FLIP appears.
//
// WHY THIS PROBE EXISTS. Wave-CK's class is a chain of `Inst::Overflow` units over CONSTANTS, so
// every body it took is a const/static initializer and every flip it earned is a CTFE flip. The
// population that carries a panic arm at RUNTIME — an `assert` on the codegen path — was refused
// on one clause: unit zero's operands had to be constants. Measured at that tip, `clean-kernel`
// flipped 0 assert-carrying bodies at `-O3` CODEGEN and 4 at `-O0`, and every one of the four
// failed `markers_exact` for an ABSENCE (`built mk b0.0:live s… vs derived <end>`).
//
// WHAT BUILT DOES — measured in full, `-Zdump-mir=all`, this compiler, at BOTH `-Cpanic=abort` and
// the default strategy (the two dumps are byte-identical at `mir_built`: `Builder::assert` emits a
// lone-`resume` cleanup edge either way, and `AbortUnwindingCalls` — which the flip REPLAYS on the
// derived body — is what turns it into `unwind unreachable` later).
//
//   fn q2_pc(a: u64) -> u64 { a + 1 }
//     bb0: { StorageLive(_2); _2 = copy _1;
//            _3 = AddWithOverflow(copy _2, const 1_u64);
//            assert(!move (_3.1), …) -> [success: bb1, unwind: bb2]; }
//     bb1: { _0 = move (_3.0); StorageDead(_2); return; }
//
// A PARAMETER READ IS A `Category::Place` EXPRESSION, so `as_operand` sends it through `as_temp`
// and built mints an operand temp with a marker pair. That pair is the whole of this wave.
//
// FOUR THINGS ARE LOAD-BEARING, ALL MEASURED HERE:
//
//   1. THE LEAF IS OPENED AND THEN ASSIGNED. `as_temp` pushes `StorageLive(t)` and only then
//      builds into `t`, so with TWO leaves the second `StorageLive` lands ONE ASSIGN LATER than
//      the first — `mk b0.0:live` and `mk b0.1:live` are different events. `L2_two_params`.
//   2. THE LINK TEMPS COME FIRST. `as_operand` opens the OUTERMOST sub-expression's temp before
//      recursing left, so in a chain the link temps are opened before the leaf, which is the
//      innermost expression there is. `L3_chain_param`, `L4_chain3_param`.
//   3. THE LEAF RETIRES AFTER UNIT ZERO'S DESTINATION WRITE, in REVERSE operand order — a BLOCK
//      EARLIER than the link it feeds, because the unit's own `assert` splits the block between
//      the write and the consumer. `L3_chain_param` is where the two retirements separate.
//   4. A ONE-UNIT CHAIN NOW OWNS MARKERS. Wave-CK refused `chain.len() < 2` because with constant
//      leaves a one-unit body has no non-outermost sub-expression at all; with a parameter leaf it
//      has one. `N1_all_const` is the control that must STAY marker-free and stay refused.
//
// AND THE REFUSALS, each with a minimally-different admitted sibling so the refusal is
// attributable: a parameter in a LATER unit (`R1_late_param`, whose temp opens in the MIDDLE of
// the chain), a leaf read TWICE (`R2_leaf_twice`, which is two built temps for one value), and a
// right-nested chain (`R3_right_nested`, wave-CK's own clause, re-measured with a parameter).
#![allow(dead_code, clippy::identity_op, clippy::precedence, clippy::eq_op)]

// =================================================================================================
// ADMITTED — one unit, one parameter leaf. The smallest body in the class.
// =================================================================================================

/// `StorageLive(_2); _2 = copy _1;` then one pair retired at the `Return` block.
pub fn l1_param_const_add(a: u64) -> u64 {
    a + 1
}

/// The same with the constant on the LEFT: built still mints the parameter's temp, and the
/// derived `AddWithOverflow(const 1, copy _2)` takes NO operand position for the folded constant —
/// which is why the leaf's use-site key is indexed among the bare-local operands only.
pub fn l1b_const_param_add(a: u64) -> u64 {
    1 + a
}

/// Subtraction, to pin that the class is the `Inst::Overflow` unit and not one operator.
pub fn l1c_param_const_sub(a: u32) -> u32 {
    a - 1
}

/// Multiplication on a narrower type: the leaf temp's DECLARED TYPE is the unit's operand type,
/// and the law carries it.
pub fn l1d_param_const_mul_u8(a: u8) -> u8 {
    a * 3
}

// =================================================================================================
// ADMITTED — one unit, TWO parameter leaves: the interleaving and the reverse retirement.
// =================================================================================================

/// ```text
/// bb0: { StorageLive(_3); _3 = copy _1; StorageLive(_4); _4 = copy _2;
///        _5 = AddWithOverflow(copy _3, copy _4); assert -> bb1; }
/// bb1: { _0 = move (_5.0); StorageDead(_4); StorageDead(_3); return; }
/// ```
pub fn l2_two_params(a: u64, b: u64) -> u64 {
    a + b
}

/// Two leaves of DIFFERENT declared types is not expressible for one checked op (both operands
/// share the op's type), so the type component is pinned by the pair above and by `l1d`.
pub fn l2b_two_params_u32(a: u32, b: u32) -> u32 {
    a * b
}

// =================================================================================================
// ADMITTED — a chain with a parameter leaf: link temps first, leaf retired a block earlier.
// =================================================================================================

/// ```text
/// bb0: { StorageLive(_2); StorageLive(_3); _3 = copy _1;
///        _4 = MulWithOverflow(copy _3, const 1024_u64); assert -> bb1; }
/// bb1: { _2 = move (_4.0); StorageDead(_3);
///        _5 = MulWithOverflow(copy _2, const 1024_u64); assert -> bb2; }
/// bb2: { _0 = move (_5.0); StorageDead(_2); return; }
/// ```
pub fn l3_chain_param(a: u64) -> u64 {
    a * 1024 * 1024
}

/// Three units and a leaf: `StorageLive(_2); StorageLive(_3); StorageLive(_4); _4 = copy _1;` —
/// the lives are outermost-first and the leaf is last.
pub fn l4_chain3_param(a: u64) -> u64 {
    a * 2 * 3 * 4
}

/// Both of unit zero's operands are parameters AND there is a link: three temps, and the leaves
/// retire together in block 1 while the link retires in block 2.
pub fn l5_chain_two_params(a: u64, b: u64) -> u64 {
    a * b * 1024
}

// =================================================================================================
// CONTROLS — must stay exactly where they were.
// =================================================================================================

/// Wave-CK's own class, unchanged: two units, no parameter. Still `markers_exact`, still 2 marker
/// lines, still a CTFE flip.
pub const N0_CONST_CHAIN: usize = 256 * 1024 * 1024;

/// ONE unit over two constants: built mints NO temp and this shim mints none. The body is
/// vacuously `markers_exact` today and the plan must keep REFUSING it — a whole-body plan on a
/// body with nothing to plan is a claim with no content.
pub const N1_ALL_CONST: usize = 256 * 1024;

/// No `Inst::Overflow` at all (the operand plan owns this body). The checked plan must not take
/// it, and this body's existing verdict must not move.
pub fn n2_no_checked_op(a: u64) -> bool {
    a == 0
}

// =================================================================================================
// REFUSED — each with its measured reason.
// =================================================================================================

/// `(a * b) * c`: unit ONE's right operand is a parameter, and built opens its temp in the MIDDLE
/// of the chain —
/// `bb1: { _4 = move (_7.0); StorageDead(_6); StorageDead(_5); StorageLive(_8); _8 = copy _3; … }`
/// — which this model does not place. Refused; `l5_chain_two_params` is the admitted sibling.
pub fn r1_late_param(a: u64, b: u64, c: u64) -> u64 {
    a * b * c
}

/// `a + a`: built mints TWO temps for one parameter
/// (`StorageLive(_2); _2 = copy _1; StorageLive(_3); _3 = copy _1;`) and this model mints one.
/// Refused; `l2_two_params` is the admitted sibling.
pub fn r2_leaf_twice(a: u64) -> u64 {
    a + a
}

/// `1024 * (a * 1024)`: the link is the RIGHT operand, so built's live order is not the reverse of
/// the SSA order. Wave-CK's clause, re-measured with a parameter present. Refused;
/// `l3_chain_param` is the admitted sibling.
pub fn r3_right_nested(a: u64) -> u64 {
    1024 * (a * 1024)
}

/// A trailing cast: the shim writes a cast through a temp where built writes one assign, so the
/// retirement's canonical position differs. Wave-CK named this body class; it stays refused with a
/// parameter leaf too.
pub fn r4_trailing_cast(a: u32) -> u64 {
    (a * 1024) as u64
}

/// A `ref`-mode parameter mints a NAMED BINDING LOCAL with its own pair — a marker the trust-ir
/// instruction stream cannot see. `checked_params_mint_no_local` refuses it at the seal site, and
/// that clause is what keeps this body out with the leaf half landed.
pub fn r5_pat_ref_mode(ref a: u64) -> u64 {
    *a + 1
}

/// A `let` puts the body outside wave-MF's firewall, which every plan consults first.
pub fn r6_let_bound(a: u64) -> u64 {
    let t = a + 1;
    t
}
