//@ run-pass
//@ compile-flags: -Zchecksum-hash-algorithm=sha256 -Ztrust-verify=off

// Trust: native execution of named Lean helper calls, including structural
// identities with identical display text. The Clean-origin gate still runs
// when property verification is disabled.
//
// The `.stderr` companion added 2026-09-16 pins the island's own
// kernel-checked note, which this file emits and had no blessed baseline for.
// It is worth pinning rather than suppressing with `dont-check-compiler-stderr`:
// the note LISTS the nine registered declarations, and this file's subject is
// that `A.b` and `«A.b»` are two DISTINCT declarations with identical display
// text. The list is the only place that distinction is observable from outside
// the kernel, so a regression that collapsed them would show up here as eight
// names instead of nine.
mod m {
    clean {
        def A.b (a b : UInt64) : UInt64 := a
        def «A.b» (a b : UInt64) : UInt64 := b + 1
        def pathPick (a b : UInt64) : UInt64 := A.b a b
        def quotedPick (a b : UInt64) : UInt64 := «A.b» a b
        def plusOne (a : UInt64) : UInt64 := a + 1
        def square (a : UInt64) : UInt64 := a * a
        def nestedCall (a : UInt64) : UInt64 := square (plusOne a)
        def difference (a b : UInt64) : UInt64 := a - b
        def swappedCall (a b : UInt64) : UInt64 := difference b a
    }
}

fn main() {
    for a in [0u64, 1, 37, 255, 1 << 32, u64::MAX - 1, u64::MAX] {
        for b in [0u64, 1, 19, 255, 1 << 32, u64::MAX] {
            assert_eq!(m::pathPick(a, b), a);
            assert_eq!(m::quotedPick(a, b), b.wrapping_add(1));
            assert_eq!(m::swappedCall(a, b), b.wrapping_sub(a));
        }
        assert_eq!(m::nestedCall(a), a.wrapping_add(1).wrapping_mul(a.wrapping_add(1)));
    }
}
