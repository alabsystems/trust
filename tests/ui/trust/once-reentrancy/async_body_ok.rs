//@ check-pass
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//
// Trust: ICE pin. A coroutine's elaborated MIR is STOLEN before the analysis
// hooks run — `run_required_analyses` computes every coroutine's layout, and
// `coroutine_layout` forces `optimized_mir`, whose first act is that steal. The
// facts query therefore reads an `async` body through `optimized_mir`, never
// through the elaborated `Steal` ("attempted to read from stolen value" —
// measured 2026-08-30 on aterm v0.65.0's `aterm-gpu`, where `async fn
// adapter_from_env` shares a crate with cell statics). Nothing here re-enters a
// cell, so the crate compiles; the `.await` gives the coroutine a resolved
// `poll` edge to another coroutine.

#![allow(dead_code)]

use std::sync::OnceLock;

static C: OnceLock<u32> = OnceLock::new();

async fn adapter_from_env() -> Option<u32> {
    let want = std::env::var("ATERM_GPU_ADAPTER").ok()?;
    Some(*C.get_or_init(|| want.len() as u32) + inner().await)
}

async fn inner() -> u32 {
    *C.get_or_init(|| 1)
}

fn main() {
    let _ = adapter_from_env();
}
