//! Trust (PM-1): the no-proc-macro TCB boundary is enforced by the crate loader,
//! before a proc-macro dylib is `dlopen`ed, for EVERY proc-macro crate of the
//! dependency metadata closure (`compiler/rustc_metadata/src/trust_proc_macro_boundary.rs`,
//! called from `register_crate` ahead of `dlsym_proc_macros`).
//!
//! The hazard (docs/KNOWN_HAZARDS.md, "A strict `targo trust check` PASS does
//! not exclude in-process third-party code"): rustc loads every proc-macro crate
//! recorded in the metadata of the crates it depends on, and a dylib's load-time
//! initializers run at `dlopen`. A facade re-export and a dependency's private
//! derive both ran inside the verifying rustc, with the session nonce on argv,
//! while the gate printed `PASS [strict lane, exit 0]`.
//!
//! tests/ui/trust/pm1_proc_macro_boundary_refuses_unaudited.rs pins the direct
//! `extern crate` shape. This recipe pins, on the compiler alone (no Targo), with
//! `-Ztrust-proc-macro-boundary` (Targo's per-unit control):
//!  * strict, certify, memory-safe: the direct derive, the facade derive and the
//!    private-use initializer are each REFUSED with the boundary diagnostic, and
//!    nothing from the macro ran (its sentinel file is absent);
//!  * `-Ztrust-audited-proc-macro` admits by exact dylib identity: naming the
//!    derive's dylib admits it (it loads and expands — the negative twin), naming
//!    a DIFFERENT dylib admits nothing;
//!  * advisory: the initializer loads and RUNS, and the forfeiture warning names
//!    the crate — which also proves the sentinel probe is live, so the strict
//!    "absent" assertions are not vacuous;
//!  * unchanged: a raw verified compile without the boundary flag, and a
//!    boundary-marked compile with `-Ztrust-verify=off` (a Targo scoped-out unit);
//!  * the driver's domain rules: the boundary requires a session, an audited path
//!    requires the boundary.
//!
//! Mutation control (expected, not measured on this tree): deleting the
//! `trust_proc_macro_boundary::check` call in `compiler/rustc_metadata/src/creader.rs`
//! turns every strict refusal below into a successful compile and fails this recipe
//! at the first `run_fail`. This recipe was first written against a parallel PM-1
//! implementation (`-Ztrust-audited-proc-macro-dylibs`, integ/stage1-batch3) and
//! ported onto main's flags and diagnostics; the port has not been run.
//!
//! Every fixture and consumer names its direct dependency with `--extern`:
//! run-make-support adds only `-L cwd`, and in edition 2021 a crate found only
//! through `-L` is not in the extern prelude (E0432 without it).

//@ ignore-cross-compile
//@ ignore-windows
//@ needs-crate-type: proc-macro

use std::path::{Path, PathBuf};

use run_make_support::{cwd, dynamic_lib_name, rfs, rust_lib_name, rustc};

/// Bootstrap may deauthorize its own nested compiler processes through this
/// inherited override. A run-make recipe is a new policy boundary.
const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";
const SESSION: &str = "-Ztrust-verify-session=run-make-pm1-proc-macro-tcb";
const BOUNDARY_FLAG: &str = "-Ztrust-proc-macro-boundary";
const BOUNDARY: &str = "no-proc-macro TCB boundary";

fn sentinel(name: &str) -> PathBuf {
    let path = cwd().join("sentinels").join(name);
    // A stale file from an earlier step would make "the macro ran" read true.
    if path.exists() {
        rfs::remove_file(&path);
    }
    path
}

/// The on-disk artifact `--extern` names for a fixture crate. run-make-support
/// adds only `-L cwd`, and in edition 2021 a crate found only through `-L` is not
/// in the extern prelude, so every use of a fixture must name it with `--extern`
/// (as tests/run-make/proc-macro-three-crates does with `extern crate`).
#[derive(Clone, Copy)]
enum Dep {
    ProcMacro(&'static str),
    Rlib(&'static str),
}

fn extern_path(dep: Dep) -> (&'static str, PathBuf) {
    let (name, file) = match dep {
        Dep::ProcMacro(name) => (name, dynamic_lib_name(name)),
        Dep::Rlib(name) => (name, rust_lib_name(name)),
    };
    let path = cwd().join(file);
    assert!(path.is_file(), "missing fixture artifact {}", path.display());
    (name, path)
}

fn dylib(crate_name: &str) -> PathBuf {
    let path = cwd().join(dynamic_lib_name(crate_name));
    assert!(path.is_file(), "missing proc-macro dylib {}", path.display());
    path
}

/// A scoped-out build of a fixture crate: vanilla, no session.
fn build_unverified(input: &str, crate_type: &str, deps: &[Dep], sentinel_path: &Path) {
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type(crate_type)
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .env("PM_TCB_SENTINEL", sentinel_path);
    for &dep in deps {
        let (name, path) = extern_path(dep);
        cmd.extern_(name, path);
    }
    cmd.run();
}

/// A consumer compile with its one direct dependency named by `--extern`; the
/// dependency's own dependencies are found through `-L cwd`, as Targo's are
/// through `-L dependency=`.
fn consumer(input: &str, dep: Dep) -> run_make_support::Rustc {
    let (name, path) = extern_path(dep);
    let mut cmd = rustc();
    cmd.input(input).crate_type("lib").edition("2021").extern_(name, path);
    cmd
}

/// The direct dependency of each consumer fixture.
fn dep_of(input: &str) -> Dep {
    match input {
        "direct_user.rs" => Dep::ProcMacro("pm_tcb_derive"),
        "facade_user.rs" => Dep::Rlib("pm_tcb_facade"),
        "private_root.rs" => Dep::Rlib("pm_tcb_private"),
        other => panic!("unknown consumer fixture {other}"),
    }
}

/// A session-scoped, boundary-marked verified compile of a consumer, as verified
/// Targo spawns one.
fn verified(input: &str, sentinel_path: &Path, extra: &[&str]) -> run_make_support::Rustc {
    let mut cmd = consumer(input, dep_of(input));
    cmd.arg("-Ztrust-verify=on")
        .arg(SESSION)
        .arg(BOUNDARY_FLAG)
        .env("PM_TCB_SENTINEL", sentinel_path)
        .env_remove(TRUST_NO_VERIFY_ENV);
    for arg in extra {
        cmd.arg(arg);
    }
    cmd
}

fn assert_refused(stderr: &str, crate_name: &str, sentinel_path: &Path, shape: &str) {
    assert!(stderr.contains(BOUNDARY), "{shape}: no boundary diagnostic:\n{stderr}");
    assert!(
        stderr.contains(&format!(
            "verified Targo refuses to load proc-macro crate `{crate_name}`"
        )),
        "{shape}: the refusal does not name `{crate_name}`:\n{stderr}"
    );
    assert!(
        !sentinel_path.exists(),
        "{shape}: `{crate_name}` RAN inside the verifying compiler before it was refused"
    );
}

fn main() {
    rfs::create_dir_all("sentinels");

    // Fixtures, all scoped out (vanilla). The private-use library's own build
    // loads `pm_tcb_init` and runs its initializer: that is the dependency's
    // rustc, not the verified one, so it is recorded but not asserted against.
    build_unverified("pm_tcb_derive.rs", "proc-macro", &[], &sentinel("derive-build"));
    build_unverified("pm_tcb_init.rs", "proc-macro", &[], &sentinel("init-build"));
    build_unverified(
        "pm_tcb_facade.rs",
        "rlib",
        &[Dep::ProcMacro("pm_tcb_derive")],
        &sentinel("facade-build"),
    );
    let private_dep_ran = sentinel("private-dep-build");
    build_unverified(
        "pm_tcb_private.rs",
        "rlib",
        &[Dep::ProcMacro("pm_tcb_init")],
        &private_dep_ran,
    );
    assert!(
        private_dep_ran.exists(),
        "probe is dead: loading `pm_tcb_init` did not run its initializer even in the \
         vanilla dependency build, so no `absent` assertion below could mean anything"
    );
    let derive_dylib = dylib("pm_tcb_derive");
    let init_dylib = dylib("pm_tcb_init");

    // --- strict, session-scoped: every shape refused before `dlopen` ---------
    let s = sentinel("strict-direct");
    let out = verified("direct_user.rs", &s, &[]).run_fail();
    assert_refused(&out.stderr_utf8(), "pm_tcb_derive", &s, "direct dependency");

    let s = sentinel("strict-facade");
    let out = verified("facade_user.rs", &s, &[]).run_fail();
    assert_refused(&out.stderr_utf8(), "pm_tcb_derive", &s, "facade re-export");

    let s = sentinel("strict-private");
    let out = verified("private_root.rs", &s, &[]).run_fail();
    assert_refused(&out.stderr_utf8(), "pm_tcb_init", &s, "private-use initializer");

    // certify and memory-safe claim proof authority too.
    for policy in ["-Ztrust-policy=certify", "-Ztrust-policy=memory-safe"] {
        let s = sentinel("strict-private-policy");
        let out = verified("private_root.rs", &s, &[policy]).run_fail();
        assert_refused(&out.stderr_utf8(), "pm_tcb_init", &s, policy);
    }

    // --- the audited set admits by exact identity ----------------------------
    // Naming a DIFFERENT dylib admits nothing.
    let wrong = format!("-Ztrust-audited-proc-macro={}", init_dylib.display());
    let s = sentinel("audited-wrong");
    let out = verified("facade_user.rs", &s, &[&wrong]).run_fail();
    assert_refused(&out.stderr_utf8(), "pm_tcb_derive", &s, "audited set names another dylib");

    // Negative twin: naming the derive's own dylib admits it, through the facade.
    let right = format!("-Ztrust-audited-proc-macro={}", derive_dylib.display());
    let s = sentinel("audited-facade");
    let out = verified("facade_user.rs", &s, &[&right]).run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains(BOUNDARY), "an audited dylib was still refused:\n{stderr}");
    assert!(s.exists(), "the admitted derive did not load and expand");

    // --- advisory: loaded, RAN, and the forfeiture names the crate -----------
    let s = sentinel("advisory-private");
    let out = verified("private_root.rs", &s, &["-Ztrust-policy=advisory"]).run();
    let stderr = out.stderr_utf8();
    assert!(
        stderr.contains("advisory lane: this unit forfeits proof authority")
            && stderr.contains("unaudited proc-macro crate `pm_tcb_init`"),
        "the advisory lane loaded an unaudited macro without naming the forfeiture:\n{stderr}"
    );
    assert!(
        s.exists(),
        "non-vacuity: the advisory load did not run the initializer, so the strict \
         `absent` assertions above prove nothing"
    );

    // --- out of scope: unchanged ---------------------------------------------
    // A raw verified compile carries no boundary flag (no Targo session to bind).
    let s = sentinel("raw-no-boundary");
    let out = consumer("private_root.rs", dep_of("private_root.rs"))
        .arg("-Ztrust-verify=on")
        .env("PM_TCB_SENTINEL", &s)
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    assert!(!out.stderr_utf8().contains(BOUNDARY), "raw lane gained the session boundary");
    assert!(s.exists(), "raw lane no longer loads the dependency's proc macro");

    // A boundary-marked unit Targo scoped out (`-Ztrust-verify=off`) proves
    // nothing, so there is nothing for the macro to forge.
    let s = sentinel("session-scoped-out");
    let out = consumer("private_root.rs", dep_of("private_root.rs"))
        .arg("-Ztrust-verify=off")
        .arg(SESSION)
        .arg(BOUNDARY_FLAG)
        .env("PM_TCB_SENTINEL", &s)
        .run();
    assert!(!out.stderr_utf8().contains(BOUNDARY), "a scoped-out unit was refused");
    assert!(s.exists(), "a scoped-out unit no longer loads the dependency's proc macro");

    // --- the driver's domain rules ---------------------------------------------
    // The boundary is Targo's per-unit control; without a session it is refused.
    let out = consumer("facade_user.rs", dep_of("facade_user.rs"))
        .arg("-Ztrust-verify=on")
        .arg(BOUNDARY_FLAG)
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    assert!(
        out.stderr_utf8().contains("-Ztrust-proc-macro-boundary requires -Ztrust-verify-session"),
        "{}",
        out.stderr_utf8()
    );
    // An audited path without the boundary that reads it is refused.
    let out = consumer("facade_user.rs", dep_of("facade_user.rs"))
        .arg("-Ztrust-verify=on")
        .arg(SESSION)
        .arg(&right)
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    assert!(
        out.stderr_utf8()
            .contains("-Ztrust-audited-proc-macro requires -Ztrust-proc-macro-boundary"),
        "{}",
        out.stderr_utf8()
    );
}
