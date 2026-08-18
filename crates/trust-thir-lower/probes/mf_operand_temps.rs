// Trust (wave-MF) — the operand-temp marker fidelity probe.
//
// Compile with the trust driver and read both channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=mfprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Zdump-mir=all -Zdump-mir-dir=MIR \
//     -Ztrust-dump=ir:IR probes/mf_operand_temps.rs --out-dir OUT
//
// The `built.after.mir` dumps are what wave-MF reproduces; `IR/mfprobe.coverage.json`'s
// `derived_mir.markers_exact` is the oracle's verdict on whether it did.
//
// IN the planned class (expected `markers_exact: true`):
#[derive(Clone, Copy)]
pub struct AllocationId(pub u64);
impl AllocationId {
    // built: StorageLive(_2); _2 = copy (_1.0: u64); _0 = Eq(move _2, const 0_u64); StorageDead(_2)
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }
}
#[derive(Clone, Copy)]
pub struct MemoryRegion {
    pub base: u64,
    pub len: usize,
}
impl MemoryRegion {
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }
}
#[derive(Clone, Copy)]
pub struct FlatFlags(pub u8);
impl FlatFlags {
    // The NESTED case: built lives the BitAnd's result temp before its own operand temps.
    #[inline]
    pub const fn contains(self, other: FlatFlags) -> bool {
        (self.0 & other.0) == other.0
    }
}
#[derive(Clone, Copy)]
pub struct NodeId(pub u32);
impl NodeId {
    // A cast's operand temp: `_0 = move _2 as usize (IntToInt)`.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[inline(never)]
pub fn eq_params(a: u64, b: u64) -> bool {
    a == b
}
#[inline(never)]
pub fn left_nested(a: u8, b: u8, c: u8) -> bool {
    (a & b) == c
}
#[inline(never)]
pub fn fadd(a: f64, b: f64) -> f64 {
    a + b
}

// OUT of the planned class — each for a different, named reason. Every one of these must stay
// `markers_exact: false`; they are the boundary, not a to-do list.
//
//   right_nested   : built's evaluation order (outer LHS temp first) is not the trust-ir linear
//                    order, so the derived sequence is wrong. Until 2026-08-13 it was ADMITTED and
//                    the CHANNEL refused it; it is now refused BY THE PLAN, by ordering rule (2)
//                    (a marked operand may not be preceded by a place operand). See
//                    `probes/mf_residual.rs` group A for the rule and its constant-tolerant trap.
//   is_null_letted : a lexical `let`. `func.scopes` is `Some(..)` -> the plan does not engage.
//   ckadd          : the checked-arith Overflow+Assert idiom splits the MIR chain (multi-block).
//   control_tagonly: a `condbr`; built's switch operand temp dies in the join block.
#[inline(never)]
pub fn right_nested(a: u8, b: u8, c: u8) -> bool {
    a == (b & c)
}
impl AllocationId {
    pub const fn is_null_letted(self) -> bool {
        let x = self.0;
        x == 0
    }
}
#[inline(never)]
pub fn ckadd(a: u32, b: u32) -> u32 {
    a + b
}
#[inline(never)]
pub fn control_tagonly(b: bool) -> u8 {
    if b { 1 } else { 0 }
}

// MUST NOT REGRESS: these already reach `markers_exact: true` with ZERO markers on both sides.
// wave-MF touches no arm they use, and the plan's `needs` set is empty for them.
#[inline(never)]
pub fn unitfn() {}
#[inline(never)]
pub fn ident(a: u64) -> u64 {
    a
}
#[inline(never)]
pub fn fieldret(a: AllocationId) -> u64 {
    a.0
}
#[inline(never)]
pub fn konst() -> u64 {
    7
}
