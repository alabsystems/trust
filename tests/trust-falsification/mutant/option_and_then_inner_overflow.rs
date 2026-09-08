#![crate_type = "lib"]
// OPTION COMBINATOR CHAIN WHOSE INNER ARITHMETIC REALLY OVERFLOWS. The a3d
// `IntervalI64::add` shape — `checked_add(..).and_then(|l| Some(..).map(|h| ..))`
// — but the value flowing into the inner closure is built with an UNCHECKED
// `hi + 1`. IT FAULTS: `hi == i64::MAX` overflows inside the `map` closure, two
// call frames below the `and_then` the caller wrote.
// Runtime oracle (stock rustc 1.96.0, -O -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 7 panics / 64 runs,
// sweep `lo x hi` over {0, 1, -1, 7, i64::MAX-1, i64::MAX, i64::MIN, i64::MIN+1}
// squared. The 7 are exactly `hi == i64::MAX` with `lo != i64::MAX`; the
// eighth (`lo == i64::MAX`) does NOT panic because `checked_add` returns None
// and `and_then` short-circuits before the closure runs — the sweep therefore
// also pins that the short-circuit is real and not an artifact.
//
// WHY THIS FIXTURE EXISTS. The falsification corpus had exactly ONE fixture
// using an Option combinator at all (`proved/method_named_write.rs`, and only
// incidentally). The closure-consumer lowering — which calls the monomorphised
// `Option::<T>::and_then::<{closure}>` wrapper the bundle already holds instead
// of stamping an `Assert(false)` may-panic marker, and compensates for the
// unread closure environment — was therefore guarded by an out-of-tree
// adversary crate and by nothing in the gate. That is a strong regression check
// and a weak positive one. This row makes the positive direction gated: if the
// wrapper call ever stops carrying the callee's panic paths, the overflow
// inside the doubly-nested closure stops being refuted and this row goes red.
//
// The verifier MUST refuse this (exit 1, `[overflow:add]` with a counterexample).
pub fn and_then_inner_overflow(lo: i64, hi: i64) -> Option<i64> {
    lo.checked_add(1).and_then(|l| Some(hi + 1).map(|h| l ^ h))
}
