// trust_ir_gate_refuses_corrupted_emission.rs — the F1 proven-output gate,
// attacked through its PUBLIC re-verification entry point with the emitted
// bytes deliberately corrupted.
//
// WHY THIS EXISTS. `verify_trust_ir_bytes` is the half of the gate that touches
// no emitter: hand it any object and it re-derives the machine side from THOSE
// bytes. It is the only thing that makes a shipped artifact independently
// auditable — and until this file, nothing outside the gate's own module ever
// called it. A gate that is only ever run on bytes its own emitter just produced
// has never been shown to be able to say no.
//
// THE DISCRIMINATOR IS TWO CONSTANTS, NOT ONE. Overwriting the instruction
// before the final `ret` with `movz x0, #K` makes the returned low register the
// constant `K`. A single such mutation flipping to `Refuted` is weak evidence:
// the gate might be refusing "the bytes changed" rather than "the value
// changed". So every function here is mutated TWICE, with constants that differ
// at every width the gate models (0x5a5a vs 0x2b2b differ mod 2^8, 2^16, 2^32,
// 2^64, 2^128). No function equals two different constants, so a `Proven` that
// survives BOTH is a demonstrably vacuous obligation.
//
// AND THERE IS A CONTROL IN THE OTHER DIRECTION. Rewriting the same word with an
// IDENTICAL instruction must leave the verdict `Proven`. Without it, "corruption
// is Refuted" would be satisfied by a gate that refuses every object it did not
// personally emit, which proves nothing about the obligation.
//
// COVERAGE IS BY OBLIGATION WIDTH, because that is the axis the gate's spec
// varies along: 8 and 16 bits (declared-width narrow returns, where the bits
// ABOVE the obligation are deliberately unconstrained), 32 (bool, held to the
// whole slot by `arg_ext: Zext`), 64, and 128 (the X0/X1 register pair, where an
// X0-only check would look exactly like a working 128-bit gate).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::verify_output::OutputVerdict;
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, verify_trust_ir_bytes, verify_trust_ir_output_preserved,
};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

/// AArch64 `ret` (i.e. `ret x30`).
const RET: u32 = 0xd65f_03c0;

/// `movz x0, #imm16` — writes `imm16` into X0 and zeroes every other bit of it.
/// Cross-checked against the encoding pinned in the gate's own unit tests:
/// `movz x1, #7` is `0xd280_00e1`, and `0xd280_0000 | (7 << 5) | 1` is the same
/// word, so `0xd280_0000 | (imm << 5)` is the `x0` form.
fn movz_x0(imm: u32) -> u32 {
    0xd280_0000 | (imm << 5)
}

/// `movz x1, #imm16` — the HIGH half of a 128-bit AAPCS64 result.
fn movz_x1(imm: u32) -> u32 {
    0xd280_0001 | (imm << 5)
}

/// Mach-O 64 `__text` (file offset, size). Deliberately a local reader rather
/// than a call into the bridge: a test that located the code with the same
/// helper the gate uses could not detect the gate looking in the wrong place.
fn text_span(obj: &[u8]) -> Option<(usize, usize)> {
    let rd32 = |o: usize| -> Option<u32> {
        obj.get(o..o + 4).and_then(|s| s.try_into().ok()).map(u32::from_le_bytes)
    };
    if rd32(0)? != 0xfeed_facf {
        return None;
    }
    let ncmds = rd32(16)? as usize;
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = rd32(off)?;
        let cmdsize = rd32(off + 4)? as usize;
        if cmd == 0x19 {
            let nsects = rd32(off + 64)? as usize;
            let mut s = off + 72;
            for _ in 0..nsects {
                if obj.get(s..s + 16)?.starts_with(b"__text\0") {
                    let size = u64::from_le_bytes(obj.get(s + 40..s + 48)?.try_into().ok()?);
                    return Some((rd32(s + 48)? as usize, size as usize));
                }
                s += 80;
            }
        }
        off += cmdsize;
    }
    None
}

/// File offset of the instruction word immediately before the LAST `ret`.
fn slot_before_last_ret(obj: &[u8]) -> usize {
    let (off, size) = text_span(obj).expect("emitted object carries a __text section");
    let words = size / 4;
    let mut last_ret = None;
    for i in 0..words {
        let at = off + i * 4;
        let w = u32::from_le_bytes(obj[at..at + 4].try_into().expect("instruction word"));
        if w == RET {
            last_ret = Some(i);
        }
    }
    let r = last_ret.expect("emitted function ends in a ret");
    assert!(r > 0, "function body is a bare `ret` — nothing to corrupt");
    off + (r - 1) * 4
}

fn with_word_at(obj: &[u8], at: usize, word: u32) -> Vec<u8> {
    let mut out = obj.to_vec();
    out[at..at + 4].copy_from_slice(&word.to_le_bytes());
    out
}

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

/// A one-block function returning a constant of type `ty`. A constant body is
/// the right bed for a corruption test: its spec is a literal, so a surviving
/// `Proven` cannot be excused as the solver failing to model some operation.
fn const_returning(name: &str, ty: Ty, value: i128) -> TrustIrGateSource {
    let mut module = Module::new("corrupt");
    module.func_types.push(FuncTy {
        params: Vec::new(),
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    let constant =
        if matches!(ty, Ty::Bool) { Constant::Bool(value != 0) } else { Constant::Int(value) };
    block.body = vec![
        InstrNode::new(Inst::Const { ty, value: constant }).with_result(ValueId::new(0)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
    ];
    f.blocks.push(block);
    module.functions.push(f);
    TrustIrGateSource { symbol: name.to_string(), module, func_id: FuncId::new(0) }
}

/// If `w` is `mov w0, wK` — the `orr w0, wzr, wK` alias the backend ends every
/// scalar body with — return `K`.
///
/// A WIDTH-BOUNDARY probe has to preserve the low bits while perturbing the high
/// ones, and that is only possible if the mutation reads the SAME register the
/// original move read. Overwriting `mov w0, wK` with `add w0, w0, #256` instead
/// (the tempting fixed encoding) reads `w0`, which at that point holds nothing
/// related to the answer — so it destroys the low bits too and Refutes at every
/// width, silently turning a width probe into a "the bytes changed" probe.
fn mov_w0_src(w: u32) -> Option<u32> {
    let k = (w >> 16) & 0x1f;
    (w == 0x2a00_03e0 | (k << 16) && k != 31).then_some(k)
}

/// `add w0, wK, #imm12` (no shift). Cross-check: `add w0, w1, #1` is
/// `0x1100_0000 | (1 << 10) | (1 << 5)` = `0x1100_0420`, and `add w0, w1, #256`
/// is `0x1104_0020` — the encodings the gate's own unit tests pin for the
/// `Rn = w0` forms (`0x1100_0400`, `0x1104_0000`).
fn add_w0_from(k: u32, imm: u32) -> u32 {
    0x1100_0000 | (imm << 10) | (k << 5)
}

/// Emit through the production path and require the baseline verdict to be
/// `Proven`, returning the exact bytes the verdict was computed over.
fn proven_bytes(source: &TrustIrGateSource) -> Vec<u8> {
    let (verdict, obj) = verify_trust_ir_output_preserved(source, &backend());
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "`{}` must be Proven before it can be corrupted, got {verdict:?}",
        source.symbol
    );
    obj.expect("a Proven verdict ships bytes")
}

fn verdict_of(source: &TrustIrGateSource, obj: &[u8]) -> OutputVerdict {
    verify_trust_ir_bytes(source, obj, TrustCgTargetArch::AArch64)
}

/// THE MAIN ASSERTION, run over every obligation width the gate models.
///
/// For each: baseline Proven; identical rewrite still Proven (the gate is not
/// merely refusing unfamiliar bytes); and BOTH value-changing mutations Refuted
/// (the obligation constrains the value, not just the bytes).
#[test]
fn corrupted_emission_is_refuted_at_every_modeled_width() {
    // `value` is chosen to differ from both mutation constants at the declared
    // width, so a Refuted is a real disagreement rather than an accident.
    let cases = [
        ("c_u8", Ty::U8, 7i128),
        ("c_i8", Ty::I8, -1),
        ("c_u16", Ty::U16, 4097),
        ("c_i16", Ty::I16, -3),
        ("c_bool", Ty::Bool, 1),
        ("c_u32", Ty::U32, 0x1234_5678),
        ("c_i64", Ty::I64, -9_000_000_000),
        ("c_i128", Ty::I128, 1234),
        ("c_u128", Ty::U128, 0),
    ];

    for (name, ty, value) in cases {
        let source = const_returning(name, ty.clone(), value);
        let obj = proven_bytes(&source);
        let at = slot_before_last_ret(&obj);
        let original = u32::from_le_bytes(obj[at..at + 4].try_into().expect("word"));

        // CONTROL: rewriting the word with itself must not move the verdict.
        let rewritten = with_word_at(&obj, at, original);
        assert_eq!(rewritten, obj, "identical rewrite must be byte-identical");
        let control = verdict_of(&source, &rewritten);
        assert!(
            matches!(control, OutputVerdict::Proven { .. }),
            "{name}: an identical rewrite must stay Proven — a gate that refuses every \
             object it did not just emit proves nothing; got {control:?}"
        );

        // ATTACK: two different constants. Surviving both is vacuity.
        let mut survived = Vec::new();
        for k in [0x5a5au32, 0x2b2bu32] {
            let corrupted = with_word_at(&obj, at, movz_x0(k));
            match verdict_of(&source, &corrupted) {
                OutputVerdict::Refuted { .. } => {}
                other => survived.push(format!("k={k:#x} -> {other:?}")),
            }
        }
        assert!(
            survived.len() < 2,
            "{name} ({ty:?}): the obligation does not constrain the returned value at all — \
             it reported non-Refuted for BOTH mutation constants: {survived:?}"
        );
        assert!(
            survived.is_empty(),
            "{name} ({ty:?}): a value-changing corruption was not Refuted: {survived:?}"
        );
    }
}

/// The 128-bit shape has a failure mode the others do not: `X0` alone is a
/// well-typed 64-bit answer, and every small `i128` constant has `X1 == 0`, so a
/// gate that only ever reads `X0` would report `Proven` for all of them and
/// never notice. Corrupt ONLY the high half.
#[test]
fn corrupting_only_the_128_bit_high_half_is_refuted() {
    for (name, ty) in [("hi_i128", Ty::I128), ("hi_u128", Ty::U128)] {
        let source = const_returning(name, ty.clone(), 1234);
        let obj = proven_bytes(&source);
        let at = slot_before_last_ret(&obj);
        // `movz x1, #7` leaves X0 (the low half) untouched and makes the high
        // half 7; the true high half of 1234 is 0.
        let corrupted = with_word_at(&obj, at, movz_x1(7));
        let verdict = verdict_of(&source, &corrupted);
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "{name} ({ty:?}): a wrong HIGH half must be Refuted — an X0-only check wearing a \
             128-bit label would pass here; got {verdict:?}"
        );
    }
}

/// The narrow weakening is EXACTLY the ABI's unspecified bits, and no more —
/// and the `bool` obligation is exactly NOT weakened.
///
/// ONE mutation, five widths, five required answers. Rewriting the closing
/// `mov w0, wK` as `add w0, wK, #0x100` changes only bits 8 and above of the
/// returned value and leaves bits 0..=7 exactly as they were. At a declared
/// width of 8 those bits are not part of the value (a Rust-ABI narrow slot is
/// `arg_ext: None`), so the verdict must NOT move. At 16, at 32, and for `bool`
/// — which rustc marks `arg_ext: Zext`, so the callee owes a zero-extended 0/1
/// across the whole slot — bit 8 IS part of the value and the verdict must flip.
///
/// No single obligation width passes this test: a fixed 8 fails the u16/bool/u32
/// rows, a fixed 32 fails the u8/i8 rows. That is the point — it pins the width
/// as a FUNCTION of the type, at the public API, over real emitted bytes.
#[test]
fn the_declared_width_is_the_exact_boundary_of_the_obligation() {
    for (name, ty, high_bits_are_part_of_the_value) in [
        ("n_u8", Ty::U8, false),
        ("n_i8", Ty::I8, false),
        ("n_u16", Ty::U16, true),
        ("n_bool", Ty::Bool, true),
        ("n_u32", Ty::U32, true),
    ] {
        let source = const_returning(name, ty.clone(), 1);
        let obj = proven_bytes(&source);
        let at = slot_before_last_ret(&obj);
        let closing = u32::from_le_bytes(obj[at..at + 4].try_into().expect("word"));
        // Asserted rather than assumed: if the backend stops closing bodies with
        // `mov w0, wK`, this probe silently stops perturbing what it claims to
        // perturb, and every row below would pass for the wrong reason.
        let k = mov_w0_src(closing).unwrap_or_else(|| {
            panic!("{name}: expected the body to close with `mov w0, wK`, found {closing:#010x}")
        });

        let high = verdict_of(&source, &with_word_at(&obj, at, add_w0_from(k, 0x100)));
        if high_bits_are_part_of_the_value {
            assert!(
                matches!(high, OutputVerdict::Refuted { .. }),
                "{name} ({ty:?}): bit 8 is inside the obligation, so perturbing it must \
                 Refute; got {high:?}"
            );
        } else {
            assert!(
                matches!(high, OutputVerdict::Proven { .. }),
                "{name} ({ty:?}): bits above the declared width are not part of the value \
                 (`arg_ext: None`), so perturbing them must NOT Refute; got {high:?}"
            );
        }

        let low = verdict_of(&source, &with_word_at(&obj, at, add_w0_from(k, 1)));
        assert!(
            matches!(low, OutputVerdict::Refuted { .. }),
            "{name} ({ty:?}): bit 0 is inside the obligation at every width, so perturbing \
             it must always Refute; got {low:?}"
        );
    }
}
