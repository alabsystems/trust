//@ run-fail
//@ needs-trust-verify
//@ aux-crate: dep=drop_credit_crate_name_collision.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: dependency Conn dropped with 7
//@ ignore-emscripten no processes
//! The WITNESS for `drop_credit_crate_name_collision.rs` (DROP-NAME-COLLIDE-1):
//! the `run` whose `drop(remote)` that file's BEFORE compiler credited as
//! panic-free, because the dependency's `Conn` renders to the same path as a
//! credited local `Conn`. The `Drop` of `auxiliary/drop_credit_crate_name_collision.rs`
//! panics on 7.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the drop really panics, not the verdict. Measured 2026-10-05 on the
//! stage 1 at `scratchpad/stage1-w13fix`: the aux built with its own flags and
//! this file built `-Ztrust-verify=off` exits 101 with the message above.

extern crate dep;

struct Conn(u8);
impl Drop for Conn {
    fn drop(&mut self) {}
}

#[inline(never)]
fn run(local: Conn, remote: dep::Conn) -> u8 {
    let r = local.0;
    drop(remote);
    r
}

fn main() {
    println!("{}", run(Conn(1), dep::Conn(7)));
}
