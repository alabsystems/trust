// Trust: Regression test for obligation deduplication (#865).
// References: rust-lang#132991, rust-lang#119503.
//
// Without intra-batch deduplication in `evaluate_predicates_recursively`,
// each nesting level doubles the number of obligations evaluated because
// multiple where-clause bounds resolve to the same global predicate.
// With N levels of nesting, this causes O(2^N) evaluations and hangs the
// compiler. The dedup set ensures each unique (param_env, predicate) pair
// is evaluated at most once per batch, keeping evaluation linear.
//
// This test should compile in under a second with the fix, but would hang
// (or hit recursion/iteration limits) without it.

//@ check-pass

// Trust: Trait hierarchy that generates duplicate global obligations.
// Each `impl Check for PairN<T>` has two where-clauses requiring the same
// nested `PairM<T>: Check` obligation, which the dedup collapses.

trait Check {}

// Base case
impl Check for () {}

// Level 1: two bounds that both require `(): Check`
struct Pair1<T>(T, T);
impl<T: Check> Check for Pair1<T> where T: Check {}

// Level 2: two bounds that both require `Pair1<()>: Check`
struct Pair2<T>(T, T);
impl<T> Check for Pair2<T>
where
    Pair1<T>: Check,
    Pair1<T>: Check,
{}

// Level 3: two bounds that both require `Pair2<()>: Check`
struct Pair3<T>(T, T);
impl<T> Check for Pair3<T>
where
    Pair2<T>: Check,
    Pair2<T>: Check,
{}

// Level 4
struct Pair4<T>(T, T);
impl<T> Check for Pair4<T>
where
    Pair3<T>: Check,
    Pair3<T>: Check,
{}

// Level 5
struct Pair5<T>(T, T);
impl<T> Check for Pair5<T>
where
    Pair4<T>: Check,
    Pair4<T>: Check,
{}

// Level 6
struct Pair6<T>(T, T);
impl<T> Check for Pair6<T>
where
    Pair5<T>: Check,
    Pair5<T>: Check,
{}

// Level 7
struct Pair7<T>(T, T);
impl<T> Check for Pair7<T>
where
    Pair6<T>: Check,
    Pair6<T>: Check,
{}

// Level 8
struct Pair8<T>(T, T);
impl<T> Check for Pair8<T>
where
    Pair7<T>: Check,
    Pair7<T>: Check,
{}

// Level 9
struct Pair9<T>(T, T);
impl<T> Check for Pair9<T>
where
    Pair8<T>: Check,
    Pair8<T>: Check,
{}

// Level 10
struct Pair10<T>(T, T);
impl<T> Check for Pair10<T>
where
    Pair9<T>: Check,
    Pair9<T>: Check,
{}

// Without dedup: evaluating `Pair10<()>: Check` generates 2^10 = 1024
// redundant evaluations. Each level doubles because both where-clauses
// produce the same child obligation.
// With dedup: each level evaluates the child obligation once, total = 10.

fn requires_check<T: Check>() {}

fn main() {
    requires_check::<Pair10<()>>();
}
