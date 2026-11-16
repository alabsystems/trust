//! The `ay` the real-solver integration tests drive.
//!
//! Resolved by [`trust_router::ay_discovery::resolve_test_ay`], the compiler's
//! rule: an explicit `TRUST_TEST_AY`, else the `ay` in the sysroot of the
//! Trust compiler under test (`TRUST_STAGE2_BIN`, `$RUSTC`, this checkout's
//! stage build, the toolchain running the tests), as that compiler reports it.
//! `PATH` is never searched and nothing is built. A test that needs ay and
//! finds none FAILS with a `NOT RUN:` message naming every place it looked;
//! nothing skips.

use std::path::Path;
use std::sync::OnceLock;

use trust_router::IncrementalAYSession;
use trust_router::ay_discovery::{TestAy, TestAyNotRun, resolve_test_ay};

/// This process's resolution, computed once: it runs `trustc -vV` and
/// `ay --version`.
fn resolved() -> &'static Result<TestAy, TestAyNotRun> {
    static RESOLVED: OnceLock<Result<TestAy, TestAyNotRun>> = OnceLock::new();
    RESOLVED.get_or_init(|| {
        let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        resolve_test_ay(&checkout)
    })
}

/// An incremental session on the resolved `ay`, or a panic carrying the
/// `NOT RUN:` diagnostic.
#[must_use]
pub fn require_ay() -> IncrementalAYSession {
    match resolved() {
        Ok(ay) => {
            eprintln!("ay detected: {ay}");
            IncrementalAYSession::with_solver_path(ay.path.to_string_lossy().into_owned())
        }
        Err(not_run) => panic!("{not_run}"),
    }
}
