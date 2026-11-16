//@ edition: 2021
//@ compile-flags: --crate-type=rlib -Copt-level=0 -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_lowering_holds.rs` and its twin,
//! built without optimization (the twin of `seal_dep_lowered.rs`): fns of a crate that FORBIDS `unsafe`, each of which only calls
//! back, reads or prints. What the compiler lowers some of these safe
//! constructs into is not safe MIR: `format_args!` calls the `unsafe fn`
//! `fmt::Arguments::new`, an `async fn`'s body transmutes its resume
//! argument, a move out of a `Box` transmutes its pointer, and std's `pin!`
//! calls `Pin::new_unchecked`. Sound.
#![forbid(unsafe_code)]

/// Calls back until it succeeds, saying when an attempt fails.
pub fn with_retry<F: FnMut() -> bool>(mut f: F, tries: u32) -> bool {
    for i in 0..tries {
        if f() {
            return true;
        }
        eprintln!("attempt {i} failed");
    }
    false
}

/// Checks what it calls back, with a message.
pub fn checked<F: FnMut() -> u32>(mut f: F) -> u32 {
    let v = f();
    assert!(v < 1000, "value {v} out of range");
    v
}

/// An `async fn` that only measures.
pub async fn measure<T>(x: &mut T) -> usize {
    std::mem::size_of_val(x)
}

/// Takes a value out of its box.
pub fn unbox<T>(b: Box<T>) -> T {
    *b
}

/// Polls a future once, pinned on the stack with std's `pin!`.
pub fn poll_once<F: std::future::Future>(f: F) -> bool {
    let f = std::pin::pin!(f);
    let mut cx = std::task::Context::from_waker(std::task::Waker::noop());
    f.poll(&mut cx).is_ready()
}
