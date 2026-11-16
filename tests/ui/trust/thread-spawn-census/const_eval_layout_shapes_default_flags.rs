//@ revisions: default advisory off spawning threads
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@[advisory] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off --crate-type lib
//@[spawning] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[threads] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib -Zthreads=2
//@[default] check-fail
//@[advisory] check-pass
//@[off] check-pass
//@[spawning] check-pass
//@[threads] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:E0391
//@ forbid-output: cycle detected
//@[spawning] forbid-output:unmodeled (via HOOK
//@[threads] forbid-output:unmodeled (via HOOK
//! Drop-in (release gate): valid Rust whose `const` / `static` values and
//! types need the LAYOUT of an `async fn`'s future, computed from inside const
//! evaluation / `type_of`. The round-3 census EVALUATED `N` and read
//! `mir_for_ctfe(BUF)` from there, and both closed an E0391 query cycle on
//! crates upstream accepts (review probes c4.rs / c7.rs, 2026-09-29), under
//! verify-on AND under the shipping default. The census now never evaluates
//! an initializer, never reads one whose value cannot carry a callable
//! (`N`, `SN`, `BUF`), and never reads one at all while an item-pipeline or
//! const-evaluation query is on the stack.
//!
//! Since 2026-09-29 that layout no longer demands the coroutine's
//! `optimized_mir` at all under verification: it is read from the coroutine's
//! pre-steal elaborated MIR (`trust_local_coroutine_layout`), and the census is
//! forced at the analysis seam, where no query is active. It used to be forced
//! under `type_of(BUF)`, which evaluates `size_of_ret(&other)` before any body
//! is borrow-checked, and `HOOK` was then declined unread. `HOOK` — read by the
//! coroutine whose layout `N` needs, and by `reads_hook` — is now READ. Where
//! `launch` is spawn-free (`default`, `advisory`) it names nothing that spawns,
//! so the unknown that `work` and `work::{closure#0}` carried while the census
//! ran inside const evaluation is gone and the coroutine has one unproved
//! obligation fewer. Where `launch` spawns (`spawning`) both reads are an
//! ESCAPES row ("const or static read here holds a callable"): a const read is
//! never a spawn claim (S1-S3). Until P2 (design
//! 2026-09-29-spawn-census-by-construction) they were UNKNOWNS, and under
//! `-Zthreads` > 1 every value was declined; the census has no value-read
//! fallback now, so `threads` (`-Zthreads=2`) pins the same rows as `spawning`.
//! Since T4.3 a verifying session runs ONE front-end thread whatever `-Zthreads`
//! asks (pinned, not refused), so this revision also shows the request is
//! accepted. It is NOT coverage of the pin: it reported the same rows before
//! T4.3; with the pin call deleted it fails only because `build_session`
//! refuses an unpinned proof session (an ICE), and a pin moved below the
//! parallel mode or the thread pool passes here. The placement is checked by
//! tests/ui-fulldeps/trust-frontend-thread-pin.rs. Neither may claim a spawn
//! through a `HOOK` read. Before, the coroutine errors (emitted inside
//! `run_required_analyses`) also cut the whole-crate walk short, so `read_n`
//! was never verified; it is now, and its `N + SN` overflow row fails, as it
//! already did under `advisory` (where nothing cut the walk short).
//!
//! `default` states the shipping default (`-Ztrust-verify=on
//! -Ztrust-policy=strict`, as compiletest's verified lane does). It refuses
//! the async bodies, `read_n`, and `reads_hook` (an unresolved indirect call
//! through `HOOK`, which strict refuses in any crate; it too was never
//! verified while the coroutine errors cut the walk short) — Trust refusals,
//! which drop-in permits — and nothing else; `advisory` and `off` compile. No
//! revision may report a query cycle.

#![allow(dead_code)]

#[cfg(not(any(spawning, threads)))]
pub fn launch() {}
#[cfg(any(spawning, threads))]
pub fn launch() { //[spawning,threads]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}
pub const HOOK: fn() = launch;
pub async fn work() -> u8 { HOOK(); 1 }
//[default]~^ ERROR Trust strict verification failed for `const_eval_layout_shapes_default_flags::work::{closure#0}`: coroutine executor-protocol premise is unproved
//[default]~| ERROR Trust strict verification failed for `const_eval_layout_shapes_default_flags::work::{closure#0}`: 1 obligation(s) were not fully verified
//[spawning,threads]~^^^ NOTE const or static read here holds a callable that reaches a std thread spawn
pub async fn other() -> u8 { 2 } //[default]~ ERROR Trust strict verification failed
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub const N: usize = size_of_ret(&work);
pub static SN: usize = size_of_ret(&other);
pub static mut BUF: [u8; size_of_ret(&other)] = [0; 1];
pub fn read_n() -> usize { N + SN }
//[default]~^ ERROR Trust Level 0 safety verification incomplete for `const_eval_layout_shapes_default_flags::read_n`: 1 obligation(s) were not proved
//[default]~| ERROR Trust strict verification failed for `const_eval_layout_shapes_default_flags::read_n`: 1 obligation(s) were not fully verified
pub fn reads_hook() { //[spawning,threads]~ NOTE const or static read here holds a callable that reaches a std thread spawn
    //[default]~^ ERROR Trust strict verification failed for `const_eval_layout_shapes_default_flags::reads_hook`: 1 obligation(s) were not fully verified
    HOOK()
}
