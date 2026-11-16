//! Trust (RL-05, D21): a verified unit with an unaudited derive-macro dependency
//! keeps its proof lane when the derive expands in the isolated worker, and is
//! still refused when it would expand in the compiler.
//!
//! On the compiler alone (no Targo), with the flags verified Targo passes a unit
//! whose proc-macro TCB is in scope: a session, `-Ztrust-proc-macro-boundary`
//! (PM-1) and, on a host with the worker sandbox, `-Ztrust-proc-macro-isolation`.
//!
//!  * strict, certify and memory-safe, isolated: the unit compiles. The derive
//!    expanded (the unit's `const` assertion on its output holds), in a process
//!    that could not write the files its initializer and its expansion both try
//!    to write (they are absent), and the boundary said nothing.
//!  * the same three, in process (the negative control): refused by the PM-1
//!    boundary before the dylib is opened, naming the crate.
//!  * advisory, in process: the dylib loads, both marks appear and the unit
//!    forfeits proof authority. This is what makes "absent" above mean
//!    something: the marks are live.
//!  * advisory, isolated: nothing forfeited, nothing marked.
//!
//! What the legs pin: without `isolated` in `trust_proc_macro_boundary::decide`
//! an isolated leg takes the refusal its in-process control shows, and a
//! compiler that opened the dylib under the option (`creader.rs`) would leave
//! the `-init` mark the advisory in-process leg shows is live.
//!
//! macOS only: the worker's sandbox is the seatbelt policy, and the option is
//! refused on any other host.

//@ ignore-cross-compile
//@ only-macos
//@ needs-crate-type: proc-macro

use std::path::PathBuf;

use run_make_support::{cwd, dynamic_lib_name, rfs, rust_lib_name, rustc};

/// Bootstrap may deauthorize its own nested compiler processes through this
/// inherited override. A run-make recipe is a new policy boundary.
const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";
const SESSION: &str = "-Ztrust-verify-session=run-make-certify-isolated-derive";
const BOUNDARY_FLAG: &str = "-Ztrust-proc-macro-boundary";
const ISOLATION_FLAG: &str = "-Ztrust-proc-macro-isolation";
const BOUNDARY: &str = "no-proc-macro TCB boundary";
const FORFEITED: &str = "forfeits proof authority";

struct Marks {
    base: PathBuf,
}

impl Marks {
    /// Fresh mark paths: a file left by an earlier leg would read as "ran".
    fn new(name: &str) -> Self {
        let marks = Marks { base: cwd().join("marks").join(name) };
        for path in [marks.init(), marks.expand()] {
            if path.exists() {
                rfs::remove_file(&path);
            }
        }
        marks
    }
    fn path(&self, suffix: &str) -> PathBuf {
        let mut path = self.base.clone().into_os_string();
        path.push(suffix);
        PathBuf::from(path)
    }
    fn init(&self) -> PathBuf {
        self.path("-init")
    }
    fn expand(&self) -> PathBuf {
        self.path("-expand")
    }
    fn assert_absent(&self, leg: &str) {
        assert!(!self.init().exists(), "{leg}: the dylib's initializer wrote its mark");
        assert!(!self.expand().exists(), "{leg}: the expansion wrote its mark");
    }
}

fn output() -> PathBuf {
    cwd().join(rust_lib_name("user"))
}

/// The verified unit, as verified Targo spawns it, with `extra` appended.
fn verified(marks: &Marks, extra: &[&str]) -> run_make_support::Rustc {
    let derive = cwd().join(dynamic_lib_name("iso_derive"));
    assert!(derive.is_file(), "missing proc-macro dylib {}", derive.display());
    let produced = output();
    if produced.exists() {
        rfs::remove_file(&produced);
    }
    let mut cmd = rustc();
    cmd.input("user.rs")
        .crate_type("lib")
        .edition("2021")
        .extern_("iso_derive", &derive)
        .arg("-Ztrust-verify=on")
        .arg(SESSION)
        .arg(BOUNDARY_FLAG)
        .env("PM_ISO_SENTINEL", &marks.base)
        .env_remove(TRUST_NO_VERIFY_ENV);
    for arg in extra {
        cmd.arg(arg);
    }
    cmd
}

fn with<'a>(policy: Option<&'a str>, more: &[&'a str]) -> Vec<&'a str> {
    policy.into_iter().chain(more.iter().copied()).collect()
}

fn main() {
    rfs::create_dir_all("marks");
    let build = Marks::new("derive-build");
    rustc()
        .input("iso_derive.rs")
        .crate_type("proc-macro")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .env("PM_ISO_SENTINEL", &build.base)
        .run();

    // Advisory, in process: the marks are live and the forfeiture is named.
    let marks = Marks::new("advisory-in-process");
    let out = verified(&marks, &["-Ztrust-policy=advisory"]).run();
    let stderr = out.stderr_utf8();
    assert!(
        stderr.contains(FORFEITED) && stderr.contains("unaudited proc-macro crate `iso_derive`"),
        "the advisory in-process load did not name its forfeiture:\n{stderr}"
    );
    assert!(
        marks.init().exists() && marks.expand().exists(),
        "probe is dead: an in-process load left no mark, so `absent` below proves nothing"
    );

    // strict (the default), certify and memory-safe all claim proof authority.
    for (name, policy) in [
        ("strict", None),
        ("certify", Some("-Ztrust-policy=certify")),
        ("memory-safe", Some("-Ztrust-policy=memory-safe")),
    ] {
        // Negative control: in process, the PM-1 boundary still refuses.
        for (leg, extra) in [
            ("in process", &[][..]),
            ("isolation switched off", &["-Ztrust-proc-macro-isolation=no"]),
        ] {
            let leg = format!("{name}, {leg}");
            let marks = Marks::new(&format!("{name}-refused"));
            let out = verified(&marks, &with(policy, extra)).run_fail();
            let stderr = out.stderr_utf8();
            assert!(stderr.contains(BOUNDARY), "{leg}: no boundary diagnostic:\n{stderr}");
            assert!(
                stderr.contains("verified Targo refuses to load proc-macro crate `iso_derive`"),
                "{leg}: the refusal does not name the crate:\n{stderr}"
            );
            marks.assert_absent(&leg);
            assert!(!output().exists(), "{leg}: a refused unit produced {}", output().display());
        }

        // Isolated: admitted, expanded, and contained.
        let leg = format!("{name}, isolated");
        let marks = Marks::new(&format!("{name}-isolated"));
        let out = verified(&marks, &with(policy, &[ISOLATION_FLAG])).run();
        let stderr = out.stderr_utf8();
        assert!(!stderr.contains(BOUNDARY), "{leg}: the boundary spoke:\n{stderr}");
        assert!(!stderr.contains(FORFEITED), "{leg}: proof authority was forfeited:\n{stderr}");
        marks.assert_absent(&leg);
        assert!(output().is_file(), "{leg}: no {} was produced", output().display());
    }

    // Advisory, isolated: nothing runs in the compiler, so nothing is forfeited.
    let marks = Marks::new("advisory-isolated");
    let out = verified(&marks, &["-Ztrust-policy=advisory", ISOLATION_FLAG]).run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains(FORFEITED), "an isolated advisory unit forfeited:\n{stderr}");
    marks.assert_absent("advisory, isolated");
}
