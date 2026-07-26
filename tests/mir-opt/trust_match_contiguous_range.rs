// Trust: Regression test for #933 (rust-lang#123305)
// Trust: Verify that matching on contiguous byte ranges like b'0'..=b'9' is
// Trust: optimized into a single unsigned range comparison rather than a
// Trust: multi-target SwitchInt.
//@ test-mir-pass: MatchBranchSimplification
#![crate_type = "lib"]

// EMIT_MIR trust_match_contiguous_range.is_ascii_digit.MatchBranchSimplification.diff
pub fn is_ascii_digit(b: u8) -> bool {
    // CHECK-LABEL: fn is_ascii_digit(
    // Trust: After MatchBranchSimplification, the multi-target SwitchInt for
    // Trust: b'0'..=b'9' should be replaced with a range comparison pattern:
    // Trust:   _sub = Sub(_1, const 48_u8);
    // Trust:   _cmp = Le(_sub, const 9_u8);
    // Trust:   switchInt(_cmp) -> [0: otherwise_bb, otherwise: match_bb]
    // CHECK: Sub(
    // CHECK: Le(
    // CHECK: switchInt
    // CHECK: return
    matches!(b, b'0'..=b'9')
}

// EMIT_MIR trust_match_contiguous_range.is_ascii_lower.MatchBranchSimplification.diff
pub fn is_ascii_lower(b: u8) -> bool {
    // CHECK-LABEL: fn is_ascii_lower(
    // CHECK: Sub(
    // CHECK: Le(
    // CHECK: switchInt
    // CHECK: return
    matches!(b, b'a'..=b'z')
}
