// Trust (wave-CK, 2026-08-17) — the CHECKED-ARITHMETIC-CHAIN storage-marker fidelity probe.
//
// Compile with the trust driver and read both channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=ckprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Cdebug-assertions=off -Cpanic=abort -Coverflow-checks=on \
//     -Zdump-mir=all -Zdump-mir-dir=MIR -Ztrust-dump=ir:IR \
//     probes/mf_checked.rs --out-dir OUT
//
// `IR/ckprobe.coverage.json`'s `derived_mir.markers_exact` is the oracle's verdict.
//
// WHAT BUILT DOES for `const A: usize = 256 * 1024 * 1024` — measured in full, `-Zdump-mir=all`,
// this compiler:
//
//   const A: usize = {
//       let mut _0: usize; let mut _1: usize;
//       let mut _2: (usize, bool); let mut _3: (usize, bool);
//       bb0: { StorageLive(_1);
//              _2 = MulWithOverflow(const 256_usize, const 1024_usize);
//              assert(!move (_2.1), "attempt to compute `{} * {}`, which would overflow",
//                     const 256_usize, const 1024_usize) -> [success: bb1, unwind unreachable]; }
//       bb1: { _1 = move (_2.0);
//              _3 = MulWithOverflow(move _1, const 1024_usize);
//              assert(!move (_3.1), ...) -> [success: bb2, unwind unreachable]; }
//       bb2: { _0 = move (_3.0); StorageDead(_1); return; }
//   }
//
// TWO MARKERS, ONE TEMP, AND IT IS THE WHOLE OBLIGATION.
//
// THREE THINGS ARE LOAD-BEARING AND ALL THREE ARE MEASURED HERE:
//
//   1. `256 * 1024` is a `Binary` THIR expression, not a `Category::Constant`, so `as_operand`
//      sends it through `as_temp`: `StorageLive(_1)` goes in BEFORE the sub-expression is built.
//      `A1_*` (one multiply) is the control — it has no non-outermost sub-expression, mints no
//      temp, and is `markers_exact` today with an EMPTY sequence on both sides.
//   2. The retirement lands after the assign that writes the PARENT's destination
//      (`_0 = move (_3.0)`), NOT after the assign that consumes the temp
//      (`_3 = MulWithOverflow(move _1, ..)`) — the parent's `assert` splits the block in between.
//      That one-block displacement is the whole reason this class needed a walk of its own.
//   3. With THREE factors (`A3_*`) the lives are OUTERMOST-FIRST: `StorageLive(_1)` (the
//      `(a*b)*c` temp) then `StorageLive(_2)` (the `a*b` temp), which is the REVERSE of the
//      producer's SSA order. Swap them and the oracle's alpha numbering (`s0`/`s1`) swaps too.
//
// The `(usize, bool)` tuple temps come from `Builder::temp`, which schedules no storage, and carry
// no markers — which is why the obligation is one pair per non-outermost checked sub-expression
// and not one per multiply.
#![allow(dead_code)]

// ---- the shipped shape, at both widths the crate actually uses ---------------------------

/// `cert::bundle::MAX_BUNDLE_ENV_BYTES` and seven siblings, verbatim.
pub const A2_USIZE: usize = 256 * 1024 * 1024;

/// `cert::compression::limits::MAX_STREAM_UNCOMPRESSED_BYTES`, verbatim — three factors, so two
/// marked links and the outermost-first live order.
pub const A3_U64: u64 = 16 * 1024 * 1024 * 1024;

// ---- controls: the class boundary, each measured -------------------------------------------

/// ONE multiply: no non-outermost sub-expression, so built mints no temp. Must stay
/// `markers_exact` with an EMPTY sequence — the plan must REFUSE it rather than mark it.
pub const A1_USIZE: usize = 256 * 1024;

/// No arithmetic at all: the marker-free form this shim has always shipped.
pub const A0_USIZE: usize = 4096;

/// A RIGHT-nested chain. Built's live order is not the reverse of the SSA order here, so the plan
/// refuses; the body keeps `markers_exact: false` and no flip, exactly as before the wave.
pub const RIGHT_NESTED: usize = 1024 * (256 * 1024);

/// A trailing cast — the shape of `env::ext_instance::PRIORITY_BYTES`' tail. The shim writes a
/// cast through a temp where built writes `_0 = move _1 as usize` in ONE assign, so the
/// retirement's canonical position differs. REFUSED, and named in the plan's doc comment.
pub const TRAILING_CAST: usize = (256u32 * 1024 * 1024) as usize;

/// A signed chain, and a subtraction: the same grammar, different opcode and signedness.
pub const SUB_I64: i64 = 1024 * 1024 - 7 - 9;

/// A body with a PARAMETER. Its built operand temp is minted at the consumer and interleaves with
/// the chain's, which is a different reconstruction — refused.
pub fn param_chain(a: usize) -> usize {
    a * 1024 * 1024
}

/// A `let`-bearing twin of `A2_USIZE`: wave-MF's firewall refuses it, and this is the body that
/// proves the firewall is still consulted first.
pub const fn letted() -> usize {
    let inner = 256 * 1024;
    inner * 1024
}

/// A CSE-shaped chain: the link is used twice, so built evaluates and marks it twice.
pub const fn squared() -> usize {
    let x = 256 * 1024;
    x * x
}

/// Addition and multiplication mixed, four factors deep — the chain grammar is opcode-agnostic.
pub const A4_MIXED: u32 = 2 * 3 * 5 + 7;

/// An UNSIGNED division, which carries the div-by-zero idiom rather than the overflow one:
/// outside the modelled unit set, refused, and the body is unchanged.
pub const DIV_U32: u32 = 4096 / 8 / 2;
