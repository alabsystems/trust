//@ probe-shape: ComparisonBool
//@ probe-expect: defeq-rejected
//@ probe-note: THE NET UNDER f27/f28. Same admitted shape, same carrier, one conjunct
//@ probe-note: reversed: the body computes `a <= b` and the clause also claims
//@ probe-note: `result == (b <= a)`. If the mint or the clause elaboration ever dropped
//@ probe-note: the operand order — or normalized `>=` by negation instead of by swap —
//@ probe-note: this would start discharging and the positive probes could not tell
//@ probe-note: anyone. The second conjunct is the one that holds, so the kernel reaches
//@ probe-note: the judgment and REFUSES the first: `defeq-rejected`, the row that means
//@ probe-note: the machinery worked and the terms genuinely did not match.
clean {
    def le_isl (a : BitVec 64) (b : BitVec 64) : Bool :=
        decide (Nat.le (Nat.xor (BitVec.toNat a) 9223372036854775808)
                       (Nat.xor (BitVec.toNat b) 9223372036854775808))
}
pub fn le_i64_rev(a: i64, b: i64) -> bool
    ensures result == (b <= a) && result == le_isl(a, b)
{ a <= b }
