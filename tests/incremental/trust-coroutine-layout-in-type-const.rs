//@ revisions: rpass1 rpass2 rpass3
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Zquery-dep-graph -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: E0733
//@ forbid-output: cycle detected
//@ forbid-output: stolen value
//@ ignore-backends: gcc

// Trust: a coroutine's layout used in a TYPE-LEVEL const, across incremental
// sessions. With verification on, `ordinary_coroutine_layout` reads a local
// coroutine's layout from `trust_local_coroutine_layout` — disk-cached, and
// produced by a value-producing call in `inner_optimized_mir` BEFORE the steal
// of the coroutine's elaborated MIR. An ensure-only call could mark the node
// green on a replay without caching its value, and a later `layout_of` would
// then borrow the stolen body.
//
// rpass2 edits the coroutine body (its layout grows: the saved `[u64; 4]`), so
// the layout query is re-executed and the type-level const re-evaluated;
// rpass3 edits only an unrelated fn, so the layout is replayed green. Every
// session runs `main`, which checks the type-level size against the size of
// the future the program actually builds.

#![allow(dead_code)]

const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize {
    core::mem::size_of::<R>()
}

async fn ready() {}

#[cfg(rpass1)]
async fn work() -> usize {
    let s = String::from("held");
    ready().await;
    s.len()
}

#[cfg(any(rpass2, rpass3))]
async fn work() -> usize {
    let s = String::from("held");
    let t = [3u64; 4];
    ready().await;
    s.len() + t.len()
}

const N: usize = size_of_ret(&work);

struct Sized {
    buf: [u8; N],
}

#[cfg(any(rpass1, rpass2))]
fn unrelated() -> u32 {
    1
}

#[cfg(rpass3)]
fn unrelated() -> u32 {
    2
}

fn main() {
    // `[0; N]` would not type-check even on stock rustc: a repeat count inside a
    // body is not evaluated eagerly.
    let s = Sized { buf: core::array::from_fn(|_| 0) };
    let fut = work();
    assert_eq!(s.buf.len(), core::mem::size_of_val(&fut));
    #[cfg(any(rpass2, rpass3))]
    assert!(N >= core::mem::size_of::<String>() + 4 * core::mem::size_of::<u64>());
    drop(fut);
    assert!(unrelated() > 0);
}
