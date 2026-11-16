//! Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): a compiler with a parallel frontend
//! returns every jobserver token it took before it exits.
//!
//! `-Zthreads=N` (N > 1) gives the frontend a thread pool whose workers take
//! tokens through a helper thread. That helper reads a token out of the pool
//! and only then hands it over. A helper still alive when the process exits can
//! be between the two: the token is then gone for good, and the compiler has
//! exited 0. `docs/OPEN_ISSUES.md` records the measurement this test replays:
//! twelve compilers at a time, twelve times, on a pool of two tokens, with a
//! token lost in 4 of 144 runs.
//!
//! The compiler now retires that helper, and the code generation coordinator's,
//! with no bound on the wait (`Proxy::shutdown`, `CoordinatorHelper`), and its
//! frontend workers no longer ask for a token they have no work for.
//!
//! What this test is, and is not. It is an end-to-end statistical guard on the
//! whole process: any token missing from, or surplus in, the pool after a round
//! fails it. It has not been shown to fail on the compiler from just before the
//! change: this harness, run by hand against a toolchain without the change,
//! lost no token in 1440 runs. What was left to lose needs a helper kept from
//! running for over a second, which this load does not produce on demand. The
//! guards that fail without the change are
//! the unit tests in `compiler/rustc_data_structures/src/jobserver/tests.rs`,
//! `compiler/rustc_thread_pool/src/thread_pool/tests.rs`,
//! `crates/trust-build-cpu/src/worker/tests.rs` and
//! `vendor/jobserver/tests/helper.rs`.
//!
//! The test also has to show that the frontend, and not only code generation,
//! drew on its pool; otherwise a frontend that quietly ran serial would pass
//! having tested nothing here. Metadata-only compiles do no code generation:
//! with `-Zthreads=3` they must be seen taking tokens, and with `-Zthreads=1`
//! they must be seen taking none, which is what makes the first observation
//! the frontend's.
//!
//! A proof session pins the frontend to one thread, so the compilers run with
//! `-Ztrust-verify=off`; otherwise `-Zthreads=3` would not be what is tested.

//@ ignore-cross-compile
//@ ignore-windows

#![deny(warnings)]

use std::ffi::CString;
use std::fmt::Write as _;
use std::fs::{File, OpenOptions};
use std::io::{ErrorKind, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

use run_make_support::{cwd, libc, rfs, rustc, tempfile};

const TOKENS: usize = 2;
const COMPILERS: usize = 12;
const ROUNDS: usize = 12;
const FRONTEND_ROUNDS: usize = 3;

/// Everything that names a scheduler to a compiler. The test's own environment
/// may carry any of these; the compilers under test must see only the FIFO.
const INHERITED_SCHEDULERS: &[&str] = &[
    "CARGO_MAKEFLAGS",
    "MFLAGS",
    "CARGO_JOBSERVER_HANDOFF",
    "TRUST_CPU_HANDOFF",
    "TRUST_FIXED_CLAIM_HANDOFF_V1",
    "BUILD_SLOT_CPU_PROTOCOL",
    "BUILD_SLOT_HELD",
    "TRUST_CPU_IMPLICIT_FD",
    "ATERM_SDK_LEASE_V3",
    "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1",
    "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
];

struct Pool {
    path: PathBuf,
    /// Keeps the FIFO open for reading and writing, so it never loses its
    /// contents, and puts tokens into it.
    owner: File,
    /// A separate read-only, non-blocking description to count with. The byte
    /// count of a read/write FIFO description is not its readable count on
    /// Darwin.
    counter: File,
    _directory: Option<tempfile::TempDir>,
}

impl Pool {
    fn new() -> Pool {
        // GNU's `--jobserver-auth=fifo:PATH` cannot carry whitespace.
        let (directory, path) = if cwd().to_string_lossy().contains(char::is_whitespace) {
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("jobserver-fifo");
            (Some(directory), path)
        } else {
            (None, cwd().join("jobserver-fifo"))
        };
        assert!(
            !path.to_string_lossy().contains(char::is_whitespace),
            "no whitespace-free directory for the jobserver FIFO: {path:?}"
        );
        let name = CString::new(path.as_os_str().as_bytes()).unwrap();
        // SAFETY: `name` is a valid C string; this only creates a new FIFO.
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0, "mkfifo {path:?}");
        let mut owner = OpenOptions::new().read(true).write(true).open(&path).unwrap();
        let counter =
            OpenOptions::new().read(true).custom_flags(libc::O_NONBLOCK).open(&path).unwrap();
        owner.write_all(&[b'|'; TOKENS]).unwrap();
        Pool { path, owner, counter, _directory: directory }
    }

    fn makeflags(&self) -> String {
        format!("-j{TOKENS} --jobserver-auth=fifo:{}", self.path.display())
    }

    /// Take every token out of the pool, count them, and put them back.
    fn count(&mut self) -> usize {
        let mut tokens = Vec::new();
        let mut buffer = [0u8; 64];
        loop {
            match self.counter.read(&mut buffer) {
                // `owner` holds the FIFO open for writing, so this is not EOF.
                Ok(0) => panic!("the jobserver FIFO lost its writer"),
                Ok(read) => tokens.extend_from_slice(&buffer[..read]),
                Err(error) if error.kind() == ErrorKind::WouldBlock => break,
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(error) => panic!("reading the jobserver FIFO: {error}"),
            }
        }
        self.owner.write_all(&tokens).unwrap();
        tokens.len()
    }

    /// The number of tokens in the pool now, without taking any.
    fn peek(&self) -> usize {
        let mut readable: libc::c_int = 0;
        // SAFETY: `FIONREAD` writes one `c_int` through the pointer.
        let status = unsafe {
            libc::ioctl(self.counter.as_raw_fd(), libc::FIONREAD, &mut readable as *mut libc::c_int)
        };
        assert_eq!(status, 0, "FIONREAD: {}", std::io::Error::last_os_error());
        readable as usize
    }
}

/// A crate with enough independent items and tests that a parallel frontend
/// has work to share.
fn write_fixture(path: &Path) {
    let mut source = String::from("#![allow(dead_code)]\n");
    for index in 0..400u64 {
        writeln!(
            source,
            "pub fn f{index}(x: u64) -> u64 {{ \
             let v: Vec<u64> = (0..x).map(|y| y.wrapping_mul({index} + 1)).collect(); \
             v.iter().sum::<u64>() ^ {index} }}\n\
             #[test] fn t{index}() {{ assert_eq!(f{index}(0), {index}); }}"
        )
        .unwrap();
    }
    rfs::write(path, source);
}

/// How much of the compiler a round runs.
#[derive(Clone, Copy, PartialEq)]
enum Work {
    /// A test harness, through code generation and linking.
    Everything,
    /// Metadata only: the frontend, with no code generation to take tokens.
    FrontendOnly,
}

/// Run `COMPILERS` compilers at once on the pool, `rounds` times, and require
/// the pool to hold exactly its tokens after every round. Returns the fewest
/// tokens seen in the pool while compilers ran.
fn compile_rounds(
    pool: &mut Pool,
    label: &str,
    work: Work,
    threads: usize,
    rounds: usize,
) -> usize {
    let makeflags = pool.makeflags();
    let fewest = AtomicUsize::new(TOKENS);
    for round in 0..rounds {
        let running = AtomicBool::new(true);
        std::thread::scope(|scope| {
            let (pool, fewest, running) = (&*pool, &fewest, &running);
            scope.spawn(move || {
                while running.load(Ordering::Relaxed) {
                    fewest.fetch_min(pool.peek(), Ordering::Relaxed);
                    std::thread::sleep(Duration::from_millis(1));
                }
            });
            let compilers: Vec<_> = (0..COMPILERS)
                .map(|index| {
                    let makeflags = &makeflags;
                    scope.spawn(move || {
                        let mut compiler = rustc();
                        for name in INHERITED_SCHEDULERS {
                            compiler.env_remove(name);
                        }
                        compiler
                            .env("MAKEFLAGS", makeflags)
                            .edition("2021")
                            .crate_type("lib")
                            .arg("-Ztrust-verify=off")
                            .arg(format!("-Zthreads={threads}"))
                            .debuginfo("0")
                            .input("fixture.rs")
                            .output(format!("{label}-{round}-{index}"));
                        match work {
                            Work::Everything => compiler.arg("--test"),
                            Work::FrontendOnly => compiler.emit("metadata"),
                        };
                        compiler.run();
                    })
                })
                .collect();
            // Stop the sampler before reporting a failed compiler: the scope
            // waits for it, so a panic here must not leave it running.
            let failed = compilers.into_iter().filter_map(|compiler| compiler.join().err()).count();
            running.store(false, Ordering::Relaxed);
            assert_eq!(failed, 0, "-Zthreads={threads}, round {round}: {failed} compilers failed");
        });
        // Every compiler has exited. A token still missing now was lost.
        let after_exit = pool.count();
        assert_eq!(
            after_exit, TOKENS,
            "-Zthreads={threads}, round {round}: the pool holds {after_exit} of {TOKENS} tokens \
             after every compiler exited"
        );
        // Nor may one turn up late: that would be a token returned twice.
        std::thread::sleep(Duration::from_millis(500));
        let settled = pool.count();
        assert_eq!(
            settled, TOKENS,
            "-Zthreads={threads}, round {round}: the pool holds {settled} of {TOKENS} tokens \
             half a second after every compiler exited"
        );
    }
    fewest.load(Ordering::Relaxed)
}

fn main() {
    write_fixture(Path::new("fixture.rs"));
    let mut pool = Pool::new();
    assert_eq!(pool.count(), TOKENS);

    let fewest = compile_rounds(&mut pool, "parallel", Work::Everything, 3, ROUNDS);
    // Otherwise the compilers never used this pool and the counts above say
    // nothing about them.
    assert!(
        fewest < TOKENS,
        "no compiler was seen taking a token from the test's pool; the test is vacuous"
    );

    // The same without code generation, so that only the frontend's thread
    // pool can take a token.
    let fewest = compile_rounds(&mut pool, "frontend", Work::FrontendOnly, 3, FRONTEND_ROUNDS);
    assert!(
        fewest < TOKENS,
        "no parallel frontend was seen taking a token from the test's pool: `-Zthreads=3` did \
         not give these compilers a frontend thread pool, and the rounds above tested only code \
         generation"
    );
    // A serial frontend has no thread pool and no frontend helper, so here
    // nothing takes a token. If something did, the observation above would not
    // show that the parallel frontend had.
    let fewest = compile_rounds(&mut pool, "frontend-serial", Work::FrontendOnly, 1, 1);
    assert_eq!(
        fewest, TOKENS,
        "a metadata-only compile with a serial frontend took a token: metadata-only rounds do \
         not isolate the frontend"
    );

    // A serial frontend has to conserve the same pool, which its code
    // generation still uses.
    compile_rounds(&mut pool, "serial", Work::Everything, 1, 1);
}
