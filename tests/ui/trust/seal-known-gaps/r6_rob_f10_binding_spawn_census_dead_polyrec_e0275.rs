//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: overflow evaluating the requirement `V<T>: Tr`
//@ error-pattern: consider increasing the recursion limit by adding a
//! KNOWN GAP of the declared-binding path (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F10, a crash; lens: robustness). Recorded, not fixed
//! (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! The binding below holds without the dead code at the end; with it, the
//! spawn census the binding runs stops the build with E0275 (no word of the
//! binding, "consider increasing the recursion limit"). Without the island
//! the file builds. The same program with no island at all fails the same
//! way under `-Ztrust-verify=on`, where the verified lane always runs the
//! census (and builds with it off). The file passes while the E0275 is
//! printed; when a fix makes the binding hold, or an error at the binding say
//! that it cannot be checked, it fails: that is the win. Move the program to
//! the fixture that fits, and delete this file.
//! The shape: the dead polymorphic recursion, two obligation levels a step
//! (`impl<T> Tr for W<T> where V<T>: Tr`), that the confirmed R4-ROB-F5 and
//! R5-ROB-F4 had in the seal check, whose fixes (the depth cap,
//! `solver_overflows`) are the seal check's only; the review found the same
//! through a projection (`type Out = <V<T> as Tr2>::Out`). docs/USING_TRUST.md
//! says the census "stops short of the instance whose trait resolution would
//! overflow the recursion limit (within 16 levels of it ...)", and that a call
//! refused for a limit makes a declared binding an error with the reason; two
//! levels a step overflow at half the limit.
//! Root, as its skeptic put it: concurrency_effects.rs guards `try_resolve`
//! only with `near_limit` (`depth(ty) + RESOLVE_MARGIN(16) > limit`, type
//! nesting alone), and `mono()` calls
//! `try_instantiate_mir_and_normalize_erasing_regions` with no such guard;
//! the solver overflows at about 65 nested `W`s, where the census would stop
//! near depth 112 of 128 (backtrace: `spawn_census`, `walk_body`,
//! `try_resolve`, `codegen_select_candidate`).

use std::sync::mpsc::channel;
#[derive(Clone, Copy)]
struct Policy(u8);
struct Config { harness: Policy, theme: u8 }
struct App { config: Config }
enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(level) => self.config.harness = Policy(level),
            Wake::Tick => self.config.theme += 1,
        }
    }
}
clean {
    import Trust.Protocol
    namespace R6RobF10
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
    end R6RobF10
}
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _watcher = std::thread::spawn(move || {
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Tick);
    });
    let mut app = App { config: Config { harness: Policy(0), theme: 0 } };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = (app.config.harness.0, app.config.theme);
}

// Dead code: nothing calls `unused`.
pub trait Tr { fn m(&self) -> u32; }
impl Tr for u8 { fn m(&self) -> u32 { 1 } }
pub struct V<T>(T);
pub struct W<T>(T);
impl<T: Tr> Tr for V<T> { fn m(&self) -> u32 { self.0.m() } }
impl<T> Tr for W<T> where V<T>: Tr { fn m(&self) -> u32 { 2 } }
fn grow<T: Tr>(x: T, n: u32) -> u32 { if n == 0 { x.m() } else { grow(W(x), n - 1) } }
fn unused() -> u32 { grow(0u8, 3) }
