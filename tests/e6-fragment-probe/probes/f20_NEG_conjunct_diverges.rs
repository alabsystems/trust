//@ probe-shape: Projection
//@ probe-expect: defeq-rejected
//@ probe-note: THE SOUNDNESS DIRECTION OF ITEM 2. One conjunct agrees, the other
//@ probe-note: does not. Splitting a conjunction must never become a way to smuggle a
//@ probe-note: false conjunct through: every leaf is still an Eq.refl the kernel
//@ probe-note: checks itself, so one failing conjunct must fail the whole term.
clean {
    def ident_isl (x : UInt64) : UInt64 := x
    def diff_isl (x : UInt64) : UInt64 := UInt64.add x 1
}
pub fn f(x: u64) -> u64
    ensures result == ident_isl(x) && result == diff_isl(x)
{ x }
