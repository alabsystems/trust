//@ check-fail
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//
// Trust: the re-entrant path runs through a GENERIC intermediate.
//
// This fixture exists because of a real regression, not for symmetry. On
// 2026-09-13 a bundling decline for generic callees was added inside
// `native_trust_ir_direct_local_fn_callees` — which is ALSO the extraction behind
// the `trust_mir_direct_local_callees` query, i.e. the compiler's local call-graph
// adjacency. Declining there deleted an EDGE from that graph, and this diagnostic
// silently stopped firing whenever the initializer reached its re-entrant wait
// through a generic function: `helper()` still reported, `helper::<u8>(0u8)`
// reported nothing, so a user got a runtime deadlock instead of a compile error.
//
// Every one of the then-existing once-reentrancy fixtures still passed, because
// not one of them routed through a generic intermediate. The lane went dark with
// no red test anywhere. That is the gap this file closes: the decline now lives at
// the bundling drain, and a bundling decision must not change the call graph.
//
// Keep the intermediate GENERIC. If it is ever made concrete "to simplify the
// test", the regression it guards becomes invisible again.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

fn helper<T>(_t: T) -> u32 {
    *C.get_or_init(|| 7)
    //~^ ERROR the initializer of `C` can wait on `C` itself
}

fn main() {
    let _ = C.get_or_init(|| helper(0u8) + 1);
}
