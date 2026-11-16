// trust-router/src/test_panic_hook.rs: panic-hook scopes that COMPOSE under
// libtest's concurrency.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Test-only panic-hook scopes: silence a panic this test EXPECTS, or count the
//! panics raised on this thread, without touching any other test's reporting.
//!
//! # Why this exists
//!
//! The panic hook is ONE process-global slot, and libtest runs this
//! crate's tests CONCURRENTLY in one process. Five helpers here used to swap
//! that slot directly — `take_hook()`, install their own, run, restore what
//! they took — and the swap does not compose across threads. Measured by the
//! regression test below, the losing interleaving is:
//!
//! ```text
//! thread A (silencer)       thread B (counter)
//! take  -> default
//! set   silent
//!                           take  -> silent          <- captures A's hook
//!                           set   count -> silent
//! restore default
//!                           restore silent           <- A's hook, forever
//! ```
//!
//! after which EVERY later panic in the process is swallowed — including the
//! assertion message of a failing test. That is how
//! `native_lane_logic_tests::no_feature_set_loses_a_verdict_to_the_parser`
//! printed its message in a solo run and nothing at all in a module run. The
//! silencers held `ay_exec_lock` and so were serialized among THEMSELVES; the
//! counter did not hold it, and the lock was never the right tool anyway —
//! it orders solver access, not a global the whole test binary shares.
//!
//! # The shape that composes
//!
//! ONE dispatcher is installed, once, over whatever hook the process started
//! with, and it is never removed. Silencing and counting are THREAD-LOCAL
//! state it reads: a scope changes only its own thread's state, and restores
//! it through a drop guard, so no interleaving of scopes on different threads
//! can leave another thread's — or the process's — reporting changed. A panic
//! is counted by every counting scope open on the thread that raised it, and
//! reported unless that thread is inside a silencing scope.
//!
//! The one cost, stated: a silencing scope covers only the thread it was
//! opened on. A panic on a thread the silenced body SPAWNS is reported, where
//! the old global swap swallowed it. That is output, not a verdict, and it is
//! the direction to err in.

use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Once};

thread_local! {
    /// Depth of the silencing scopes open on this thread.
    static SILENCED: Cell<usize> = const { Cell::new(0) };
    /// The counters of the counting scopes open on this thread.
    static COUNTERS: RefCell<Vec<Arc<AtomicUsize>>> = const { RefCell::new(Vec::new()) };
}

static DISPATCHER: Once = Once::new();

/// Install the dispatcher over the process's reporting hook, exactly once.
fn install_dispatcher() {
    DISPATCHER.call_once(|| {
        let reporting = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            // `try_with`/`try_borrow`: a panic during thread-local teardown, or
            // one raised while this thread's counter list is being edited, must
            // still be REPORTED rather than turned into a double panic.
            let _ = COUNTERS.try_with(|counters| {
                if let Ok(counters) = counters.try_borrow() {
                    for counter in counters.iter() {
                        counter.fetch_add(1, Ordering::SeqCst);
                    }
                }
            });
            let silenced = SILENCED.try_with(|depth| depth.get() > 0).unwrap_or(false);
            if !silenced {
                reporting(info);
            }
        }));
    });
}

/// Closes one silencing scope on drop — on the normal path and while
/// unwinding alike.
struct SilenceScope;

impl Drop for SilenceScope {
    fn drop(&mut self) {
        SILENCED.with(|depth| depth.set(depth.get() - 1));
    }
}

/// Closes one counting scope on drop.
struct CountScope;

impl Drop for CountScope {
    fn drop(&mut self) {
        COUNTERS.with(|counters| {
            counters.borrow_mut().pop();
        });
    }
}

/// Run `body` under `catch_unwind` with panics raised ON THIS THREAD
/// unreported, for a probe whose panic IS the measurement (an encoder that
/// refuses a width by panicking, a parser that refuses a name).
///
/// Nothing outside this thread is affected: a concurrently running test's
/// failing assertion is still reported.
pub(crate) fn catch_unwind_silently<R>(body: impl FnOnce() -> R) -> std::thread::Result<R> {
    install_dispatcher();
    SILENCED.with(|depth| depth.set(depth.get() + 1));
    let _scope = SilenceScope;
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(body))
}

/// Run `body` and return its value with the number of panics raised ON THIS
/// THREAD while it ran. Every panic is still reported normally.
///
/// Counting per thread is what makes the count mean something while other
/// tests run concurrently: their contained panics are raised on their threads.
/// A panic that escapes `body` (the test's own failing assertion) propagates
/// unchanged, after being reported.
pub(crate) fn count_panics<R>(body: impl FnOnce() -> R) -> (R, usize) {
    install_dispatcher();
    let counter = Arc::new(AtomicUsize::new(0));
    COUNTERS.with(|counters| counters.borrow_mut().push(Arc::clone(&counter)));
    let _scope = CountScope;
    let value = body();
    (value, counter.load(Ordering::SeqCst))
}

#[cfg(test)]
mod tests {
    use std::process::Command;
    use std::sync::{Arc, Barrier};

    use super::{catch_unwind_silently, count_panics};

    /// Raised on the child's main thread AFTER the overlapping scopes have
    /// closed. It must be reported.
    const REPORTED: &str = "trust-router test_panic_hook: reported-after-overlap";
    /// Raised inside the silencing scope. It must NOT be reported.
    const SILENCED: &str = "trust-router test_panic_hook: silenced-inside-scope";
    /// Raised inside the counting scope, on the counting thread.
    const COUNTED: &str = "trust-router test_panic_hook: counted-inside-scope";

    const CHILD: &str = "test_panic_hook::tests::overlapping_scopes_then_a_panic";

    /// THE SUBPROCESS HALF of [`a_panic_after_overlapping_scopes_is_still_reported`].
    ///
    /// It forces, with barriers rather than timing, the one interleaving that
    /// left the old global swap installed for good: a silencing scope opens, a
    /// counting scope opens on another thread, the silencing scope closes
    /// FIRST, and the counting scope closes last. Then it panics on its own
    /// thread, and the parent reads the child's stderr for that panic.
    ///
    /// It runs in a child process because the property is about the
    /// PROCESS-GLOBAL hook: in the shared test process a regression would
    /// silence every other test, and the observation would race them.
    #[test]
    #[ignore = "subprocess half of `a_panic_after_overlapping_scopes_is_still_reported`, which runs it"]
    fn overlapping_scopes_then_a_panic() {
        let silence_open = Arc::new(Barrier::new(2));
        let count_open = Arc::new(Barrier::new(2));
        let silence_closed = Arc::new(Barrier::new(2));

        let silencer = {
            let (silence_open, count_open, silence_closed) =
                (Arc::clone(&silence_open), Arc::clone(&count_open), Arc::clone(&silence_closed));
            std::thread::spawn(move || {
                let caught = catch_unwind_silently(|| {
                    silence_open.wait();
                    count_open.wait();
                    panic!("{SILENCED}");
                });
                assert!(caught.is_err(), "the silenced body panics by construction");
                silence_closed.wait();
            })
        };
        let counter = std::thread::spawn(move || {
            silence_open.wait();
            let ((), count) = count_panics(|| {
                count_open.wait();
                silence_closed.wait();
                let caught = std::panic::catch_unwind(|| panic!("{COUNTED}"));
                assert!(caught.is_err());
            });
            count
        });
        silencer.join().expect("the silencing thread completes");
        let counted = counter.join().expect("the counting thread completes");

        // FIRST the panic the parent looks for, so its observation does not
        // depend on the assertion below.
        let caught = std::panic::catch_unwind(|| panic!("{REPORTED}"));
        assert!(caught.is_err());

        assert_eq!(
            counted, 1,
            "the counting scope sees its own thread's one panic and not the silencer's"
        );
    }

    #[test]
    fn nested_counts_restore_the_outer_scope_during_unwind() {
        let ((), outer) = count_panics(|| {
            let caught = std::panic::catch_unwind(|| {
                let _ = count_panics(|| {
                    let caught = catch_unwind_silently(|| panic!("nested expected panic"));
                    assert!(caught.is_err());
                    panic!("unwind the inner count scope");
                });
            });
            assert!(caught.is_err());
            let caught = catch_unwind_silently(|| panic!("outer expected panic"));
            assert!(caught.is_err());
        });
        assert_eq!(outer, 3, "the outer scope counts nested and later panics");
        let ((), count) = count_panics(|| {});
        assert_eq!(count, 0, "completed scopes leave no counters behind");
    }

    /// TRUST-25's regression test: a panic raised after a silencing scope and a
    /// counting scope OVERLAPPED on two threads is still reported.
    ///
    /// Before the dispatcher, the five helpers swapped the global hook and the
    /// forced interleaving left the silencer's no-op hook installed for the
    /// rest of the process, so the `REPORTED` panic printed nothing — the
    /// mechanism that hid `no_feature_set_loses_a_verdict_to_the_parser`'s
    /// message in a module run. The silenced panic must stay silent and the
    /// counted one must still be reported, so this cannot pass by silencing
    /// nothing or by reporting nothing.
    #[test]
    fn a_panic_after_overlapping_scopes_is_still_reported() {
        let exe = std::env::current_exe().expect("the test binary knows its own path");
        let output = Command::new(exe)
            .args([CHILD, "--exact", "--ignored", "--nocapture", "--test-threads=1"])
            .output()
            .expect("the test binary re-runs itself");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stdout.contains("running 1 test"),
            "the child must have RUN the scenario:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains(REPORTED),
            "a panic raised after the scopes closed was NOT reported — the process hook was \
             left silenced:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "the child's own checks failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains(COUNTED),
            "a panic inside a counting scope must still be reported:\nstderr:\n{stderr}"
        );
        assert!(
            !stderr.contains(SILENCED),
            "a panic inside a silencing scope must not be reported:\nstderr:\n{stderr}"
        );
    }
}
