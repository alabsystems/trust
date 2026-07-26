//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: ITEM 2 END-TO-END. Two facts in one clause. Before the And.intro
//@ probe-note: split this failed with "defeq route requires an equality-headed goal"
//@ probe-note: — a purely syntactic refusal, even though each conjunct was
//@ probe-note: individually dischargeable.
clean {
    def ident_isl (x : UInt64) : UInt64 := x
    def same_isl (x : UInt64) : UInt64 := x
}
pub fn f(x: u64) -> u64
    ensures result == ident_isl(x) && result == same_isl(x)
{ x }
