//! Trust (design critique C-15, `docs/design/2026-10-01-platform-protocols-as-trustc-errors.md`):
//! F1 (`-Ztrust-cg-frontend=trust-ir`) either calls a C callee with its real argument
//! placement or refuses the call by name. It never calls one through the producer's unsigned
//! `(...)` declaration.
//!
//! THE HAZARD. On aarch64-apple-darwin the fixed arguments of a variadic call go in registers and
//! the anonymous ones go on the stack. `recover_callee_param_tys` declines `c_variadic`, so until
//! FOREIGN-SCALAR-SIGNATURE-1 (ce9963522d, landed by 3cc914e770; docs/DECISION_QUEUE.md) the
//! producer declared such a callee `params: [] + is_vararg: true` with no ABI record: `fcntl` was
//! `(...) -> (i32)`, zero fixed parameters. A backend that lowers that as written puts `fd` and
//! `cmd` on the stack, where `fcntl` never reads them (trust-cg's adapter: `CallVariadic {
//! fixed_args: 0 }`). A non-variadic C callee the producer cannot sign gets the same spelling,
//! and every one of its arguments would be misplaced.
//!
//! THE PREMISE (pinned below). The producer now reads the ORIGINAL foreign Item's FnAbi after
//! source lowering (`foreign_signature::read`) and publishes it as the declaration's
//! digest-bearing `SignatureAbi`, printed `abi("...")` after the shape. `fcntl` is
//! `(i32, i32, ...) -> (i32)` with `variadic=true,fixed_count=2` and one placed argument per fixed
//! parameter; `dup2`/`lseek` carry the same record with `variadic=false`. The record is read from
//! the source, not assumed: `va_zero_fixed.rs`'s `fcntl(...)` is `(...) -> (i32)` with
//! `fixed_count=0`. `posix_spawn_file_actions_*` still have NO record: their `*mut *mut c_void`
//! carrier is outside that reader's direct-scalar profile. So `vp_local.rs`'s variadic `asprintf`,
//! whose first fixed parameter is that carrier, is STILL the producer's unsigned `(...) -> (i32)`
//! with no record: the C-15 spelling itself, which every lane must refuse by name.
//!
//! THE CASES. Each case is its own crate, because one refused function fails the whole F1
//! compile and would hide the others.
//!  * `nv_libc` / `nv_local`: the non-variadic `dup2(old, new)` and `lseek(fd, off, whence)`,
//!    called through `libc::` and through a local `extern "C"` block. The results prove the
//!    arguments arrived:
//!    - `dup2` answers `new` only if `old` was open;
//!    - `lseek` answers `off` only if `fd` and `whence` were valid;
//!    - the host's own `lseek(fd, 0, SEEK_CUR)` on the ORIGINAL descriptor proves that `new`
//!      duplicates it.
//!  * `pp_libc` / `pp_local`: the NON-variadic `posix_spawn_file_actions_adddup2` and `_destroy`,
//!    through `libc::` and through a local block. `adddup2` answers 0 only if all three arguments
//!    arrived, and EBADF for a negative descriptor in either position. Their parameter is a
//!    POINTER TO A POINTER (`*mut *mut c_void`); until 2026-10-15 the producer would not sign one
//!    (the dropped-borrow guard in `recover_callee_param_tys`), so both were published `(...)`,
//!    the writer's "non-variadic callee through `(...)`" case. That guard is retired (the dropped
//!    borrow is refused at the call site instead, docs/DECISION_QUEUE.md REF-TO-PTR-SIGN-1), so
//!    both are now SIGNED, `(ptr, i32, i32) -> (i32)` and `(ptr) -> (i32)`, and these two cases
//!    pin what F1 does with a signed pointer-to-pointer C callee: exactly what it does with the
//!    `nv_*` ones.
//!  * `va_libc` / `va_local`: the variadic `fcntl(fd, F_SETFD, FD_CLOEXEC)`, after which
//!    `fcntl(fd, F_GETFD)` must be 1. Called through `libc::` and through a local block.
//!  * `vp_local`: the variadic `asprintf(strp, fmt, v)` through a local block, whose prefix the
//!    producer cannot sign (THE PREMISE). It keeps the hazard's own `(...)` declaration on every
//!    lane, so the refusal that reads the `(...)` stays pinned. The oracle prints `n=4 text=v=42`.
//!  * `control`: no C callee. It completes and runs on every F1 lane, so the link-and-execute
//!    path a subject takes once it compiles is exercised today. It is not dead code.
//!
//! THE LANES.
//!  * ORACLE: every case is built with the DEFAULT backend, linked into its driver and
//!    executed. This proves the expected line is what this host prints, so no refusal below
//!    hides a wrong expectation.
//!  * F1, six lanes: the default (instance-keyed) selection and `-Ztrust-ir-crate-module`, each
//!    under the default STRICT output gate and under `allow-unknown`. The crate-module lane is
//!    the one where a body calling the `(...)` declaration reaches `lower_module_to_lir` itself.
//!    Since step 2 increment 5 sub-step 5.4.2, also the COMPILER LANE
//!    (`-Ztrust-cg-f1-backend=compiler`, both policies), which has real calls. Since
//!    FOREIGN-SCALAR-SIGNATURE-1 the instance plan routes a body whose only bodyless callees are
//!    RECORDED scalar foreign declarations to the native consumer on that lane
//!    (`instance_assembly.rs` `reaches_only_recorded_foreign_declarations`), so `nv_*` and `va_*`
//!    compile there. A record is ABI placement, not proof of the external callee: under the
//!    strict gate the module is refused because no calling function is closed-[PROVED]
//!    (`[f1-output-gate:policy]`, each `Unknown`), and under `allow-unknown` it ships with each
//!    function disclosed `Unknown`, is linked and executed, and must print the oracle's line.
//!    `pp_*` and `vp_local` (no record) refuse there exactly as on the default selection.
//!  * Outcomes: a case that compiles on a lane is linked, executed, and must print the
//!    oracle's line. A refused case must name the refusal pinned for each of its functions and
//!    ship no rlib.
//!  * TEETH: `va_zero_fixed.rs` declares `fcntl(...)` with zero fixed parameters, the placement
//!    `CallVariadic { fixed_args: 0 }` would give an unsigned `(...)` declaration. It is built
//!    with the default backend and run through the same driver, and must NOT print the oracle's
//!    line. So the `va_*` rows that RUN (compiler lane, `allow-unknown`) fail if F1 loses the
//!    fixed count; that is measured, not assumed. F1 itself refuses this declaration's calls by
//!    name on every lane; on the compiler lane that is trust-cg's `[TCG-UNSIGNED-VARIADIC]`.
//!
//! MEASURED (2026-11-12, stage 1 of fddd114119; Apple arm64).
//!  * Nothing miscompiles. The only F1 calls to a bodyless declaration are the compiler lane's
//!    under `allow-unknown`, to RECORDED declarations, and each of those prints the oracle's line
//!    (`f1_setfd_cloexec` puts `fd`/`cmd` in `w0`/`w1` and `FD_CLOEXEC` at `[sp]`). The refusals:
//!    - default selection, both policies: the instance lane.
//!      - The instance-keyed producer refuses every edge to an unsigned `(...)` declaration by
//!        name: `UnsignableCallee("`asprintf`: parameter list unsigned")` (`vp_local`, on both
//!        default-selection and both compiler-lane rows). This is the one refusal that reads the
//!        `(...)`. `fcntl` took it until 3cc914e770 and `pp_*` until 2026-10-15; since then
//!        `va_libc` takes the `libc::` text below and `va_local` the local-foreign one, as their
//!        `nv_*` twins do.
//!      - The lane refuses a signed local foreign callee because it needs real call edges
//!        (increment 5).
//!      - It refuses a signed `libc::` callee too. Since a4e15ca586 (the sealed level-R
//!        upstream importer) the lane routes every non-local callee to that importer first, so
//!        the caller is `[upstream-entry]`: `locality` under the strict gate (the instance is
//!        linked externally, never imported) and `strict:` under `allow-unknown`. The caller's
//!        line carries the importer's reason without the callee's name, and the class's
//!        retirement line names a metadata body, which a foreign item can never have; both
//!        texts are the frozen `instance_assembly.rs`/`upstream_entry.rs`, so the class and the
//!        importer's reason are pinned here (re-measured 2026-11-08 on a stage 1 of
//!        d59a1ff978; before a4e15ca586: `[instance-assembly]`, "upstream body ... increment 6").
//!    - crate-module selection, both policies: the converter's generic `unsupported instruction
//!      `Call`` (`[converter-refused]`). The converter runs with `real_calls = false`, so no call
//!      to a bodyless callee is ever lowered. Its real-call arm (`callee_is_real_call_composable`),
//!      which F1 does not use, refuses `is_vararg` too. `pp_*` and `vp_local` stop earlier on
//!      this lane, at their own `*mut *mut c_void` parameter (`[unsupported-abi]`).
//!    - compiler lane, strict: `nv_*`/`va_*` complete and the output gate refuses the module
//!      (`[f1-output-gate:policy] strict: not closed-[PROVED]`, each function `Unknown`); `pp_*`
//!      and `vp_local` refuse as on the default selection. Before 3cc914e770 every C-callee case
//!      refused here exactly as on the default selection.
//!  * On origin/main before S2, `va_local` never reached either lane: the producer read the
//!    local `fcntl` as Rust-ABI and declined both bodies (`[producer-declined]`,
//!    `UnsignableRustAbiDeclaration(fcntl)`). The local `dup2`/`lseek` were declared `rustcc`.
//!    S2 makes each `*_local` case behave like its `*_libc` twin on every lane where the call is
//!    reached.
//!  * TEETH printed `before=0/5 set=6 after=0/7 other=0`. `w1` happened to hold 0, which is
//!    `F_DUPFD`, so each "flag" call silently DUPLICATED the descriptor (5, 6, 7) and FD_CLOEXEC
//!    was never set. The oracle prints `before=0/0 set=0 after=1/1 other=0`.
//!
//! WHEN THIS FLIPS. Real call edges are step 2 increment 5
//! (`docs/design/2026-10-01-step2-inc5-real-calls-retarget.md`, wired at step 5.4). The
//! compiler lane's `allow-unknown` row of `nv_*`/`va_*` flipped from `Refused` to
//! `RunsUnproved` at 3cc914e770, so this test executes those calls on Apple arm64: a variadic
//! call that loses its fixed arguments prints a line the oracle does not (TEETH), and fails here.
//! A row that ships one of these calls as closed-[PROVED] fails here too until the call-event
//! proof (docs/DECISION_QUEUE.md D30) is real and this pin is re-measured.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{cmd, rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// One F1 lane: a selection mode and an output-gate policy.
struct Lane {
    label: &'static str,
    args: &'static [&'static str],
}

const LANES: [Lane; 6] = [
    Lane { label: "strict", args: &[] },
    Lane { label: "allow-unknown", args: &["-Ztrust-cg-output-gate=allow-unknown"] },
    Lane { label: "crate-module-strict", args: &["-Ztrust-ir-crate-module"] },
    Lane {
        label: "crate-module-allow-unknown",
        args: &["-Ztrust-ir-crate-module", "-Ztrust-cg-output-gate=allow-unknown"],
    },
    // Trust (step 2 increment 5, sub-step 5.4.2): the COMPILER LANE, which has real calls. It
    // calls a bodyless declaration only when the producer RECORDED its original foreign FnAbi
    // (FOREIGN-SCALAR-SIGNATURE-1); such a call is never closed-[PROVED], so the strict gate
    // still ships none of them and `allow-unknown` ships them disclosed `Unknown`.
    Lane { label: "compiler-strict", args: &["-Ztrust-cg-f1-backend=compiler"] },
    Lane {
        label: "compiler-allow-unknown",
        args: &["-Ztrust-cg-f1-backend=compiler", "-Ztrust-cg-output-gate=allow-unknown"],
    },
];

/// What F1 does with a case on one lane.
#[derive(Clone, Copy)]
enum Outcome {
    /// Compiles, links into the driver, and prints the oracle's line.
    Runs,
    /// Compiles on the compiler lane under `allow-unknown` with EVERY function disclosed
    /// `Unknown` (none closed-[PROVED]: a recorded C prototype is placement, not a proof of the
    /// callee), links into the driver, and prints the oracle's line.
    RunsUnproved,
    /// Every function compiles on the compiler lane, and the strict output gate then refuses the
    /// module because none is closed-[PROVED], naming each `Unknown`. Nothing ships.
    UnprovedRefused,
    /// Every function reaches the compiler lane's codegen module, and trust-cg's own preflight
    /// refuses each (`[trust-cg-refused]`) with a sample line naming `reason`, where `{callee}`
    /// stands for its C callee. Nothing ships.
    CgRefused { reason: &'static str },
    /// Refused, every function in `class`, each with a sample line naming `reason`. In `reason`,
    /// `{callee}` stands for that function's C callee.
    Refused { class: &'static str, reason: &'static str },
}

/// The instance lane refuses an unsigned (`(...)`) callee edge by name.
const UNSIGNED_EDGE: Outcome = Outcome::Refused {
    class: "[instance-assembly]",
    reason: "UnsignableCallee(\"`{callee}`: parameter list unsigned\")",
};

/// The instance lane routes a signed `libc::` callee, an upstream item, to the sealed level-R
/// importer before any local-body check (a4e15ca586, "The plan routes upstream items before
/// `local_body_def`"; "Upstream instances that Rust links externally are refused, never
/// copied"), and the caller carries that refusal as the importer's class. Under the strict gate
/// the importer's locality check refuses the externally linked instance...
const UPSTREAM_LINKED: Outcome = Outcome::Refused {
    class: "[upstream-entry]",
    reason: "locality: this upstream instance must be linked, not imported as a local body",
};

/// ...and under `allow-unknown` its D17/D39 strict condition refuses first.
const UPSTREAM_STRICT_ONLY: Outcome = Outcome::Refused {
    class: "[upstream-entry]",
    reason: "strict: D17/D39 admits upstream bodies only under the strict output gate",
};

/// A local foreign callee: no body anywhere, and calling it needs real call edges.
const LOCAL_FOREIGN: Outcome = Outcome::Refused {
    class: "[instance-assembly]",
    reason: "`{callee}` is a foreign declaration with no body anywhere in this crate; calling it \
             needs real call edges (increment 5)",
};

/// trust-cg's adapter places no argument of a call to a variadic declaration with zero fixed
/// parameters (DarwinPCS: fixed in registers, anonymous on the stack), so it refuses the call.
const UNSIGNED_VARIADIC: Outcome = Outcome::CgRefused {
    reason: "[trust-cg-refused:Adapter::UnsignedVariadicCallee] adapter error: \
             [TCG-UNSIGNED-VARIADIC] call to `{callee}` through an unsigned variadic declaration",
};

/// The converter (`real_calls = false`) lowers no call to a bodyless callee.
const CONVERTER_CALL: Outcome = Outcome::Refused {
    class: "[converter-refused]",
    reason: "unsupported instruction `Call` in `",
};

/// The definition's OWN `*mut *mut c_void` parameter is outside the crate-module lane's ABI
/// filter, so that lane stops before the body's call. Carrying the pointer as `usize` does not
/// help: the converter then refuses the `inttoptr` cast first (measured).
const DEFINITION_ABI: Outcome = Outcome::Refused {
    class: "[unsupported-abi]",
    reason: "argument 0 uses unsupported ABI type/pass mode `*mut *mut c_void`",
};

struct Case {
    source: &'static str,
    /// The crate name the source declares; also the driver's `extern crate`.
    krate: &'static str,
    driver: &'static str,
    /// Each F1 function's mangled-name fragment, and the C function it calls.
    fns: &'static [(&'static str, &'static str)],
    /// The oracle's line: what the default backend's build of this case prints on this host.
    expect: &'static str,
    /// The pin for each of `LANES`, in order.
    f1: [Outcome; 6],
}

const NV_FNS: &[(&str, &str)] = &[("2nv7f1_dup2", "dup2"), ("2nv8f1_lseek", "lseek")];
const VA_FNS: &[(&str, &str)] = &[("2va16f1_setfd_cloexec", "fcntl"), ("2va8f1_getfd", "fcntl")];
const PP_FNS: &[(&str, &str)] = &[
    ("2pp10f1_adddup2", "posix_spawn_file_actions_adddup2"),
    ("2pp10f1_destroy", "posix_spawn_file_actions_destroy"),
];
const NV_LINE: &str = "dup2=77 lseek=1234 shared=1234";
// EBADF is 9 on Darwin.
const PP_LINE: &str = "ok=0 bad_fd=9 bad_new=9 destroy=0";
// F_GETFD is 0 on a fresh `pipe` end. F_SETFD answers 0. Then F_GETFD is FD_CLOEXEC (1) on that
// end and still 0 on the other.
const VA_LINE: &str = "before=0/0 set=0 after=1/1 other=0";
const VP_FNS: &[(&str, &str)] = &[("2vp9f1_format", "asprintf")];
// `asprintf` answers the length of the text it allocated.
const VP_LINE: &str = "n=4 text=v=42";

const CASES: &[Case] = &[
    Case {
        source: "control.rs",
        krate: "control",
        driver: "control_driver.rs",
        fns: &[],
        // 0x55 ^ 7
        expect: "mix=82",
        f1: [Outcome::Runs; 6],
    },
    Case {
        source: "nv_libc.rs",
        krate: "nv",
        driver: "nv_driver.rs",
        fns: NV_FNS,
        expect: NV_LINE,
        f1: [
            UPSTREAM_LINKED,
            UPSTREAM_STRICT_ONLY,
            CONVERTER_CALL,
            CONVERTER_CALL,
            Outcome::UnprovedRefused,
            Outcome::RunsUnproved,
        ],
    },
    Case {
        source: "nv_local.rs",
        krate: "nv",
        driver: "nv_driver.rs",
        fns: NV_FNS,
        expect: NV_LINE,
        f1: [
            LOCAL_FOREIGN,
            LOCAL_FOREIGN,
            CONVERTER_CALL,
            CONVERTER_CALL,
            Outcome::UnprovedRefused,
            Outcome::RunsUnproved,
        ],
    },
    Case {
        source: "pp_libc.rs",
        krate: "pp",
        driver: "pp_driver.rs",
        fns: PP_FNS,
        expect: PP_LINE,
        f1: [
            UPSTREAM_LINKED,
            UPSTREAM_STRICT_ONLY,
            DEFINITION_ABI,
            DEFINITION_ABI,
            UPSTREAM_LINKED,
            UPSTREAM_STRICT_ONLY,
        ],
    },
    Case {
        source: "pp_local.rs",
        krate: "pp",
        driver: "pp_driver.rs",
        fns: PP_FNS,
        expect: PP_LINE,
        f1: [
            LOCAL_FOREIGN,
            LOCAL_FOREIGN,
            DEFINITION_ABI,
            DEFINITION_ABI,
            LOCAL_FOREIGN,
            LOCAL_FOREIGN,
        ],
    },
    Case {
        source: "va_libc.rs",
        krate: "va",
        driver: "va_driver.rs",
        fns: VA_FNS,
        expect: VA_LINE,
        f1: [
            UPSTREAM_LINKED,
            UPSTREAM_STRICT_ONLY,
            CONVERTER_CALL,
            CONVERTER_CALL,
            Outcome::UnprovedRefused,
            Outcome::RunsUnproved,
        ],
    },
    Case {
        source: "va_local.rs",
        krate: "va",
        driver: "va_driver.rs",
        fns: VA_FNS,
        expect: VA_LINE,
        f1: [
            LOCAL_FOREIGN,
            LOCAL_FOREIGN,
            CONVERTER_CALL,
            CONVERTER_CALL,
            Outcome::UnprovedRefused,
            Outcome::RunsUnproved,
        ],
    },
    Case {
        source: "vp_local.rs",
        krate: "vp",
        driver: "vp_driver.rs",
        fns: VP_FNS,
        expect: VP_LINE,
        f1: [
            UNSIGNED_EDGE,
            UNSIGNED_EDGE,
            DEFINITION_ABI,
            DEFINITION_ABI,
            UNSIGNED_EDGE,
            UNSIGNED_EDGE,
        ],
    },
];

/// The default backend: the oracle's build of a case.
fn default_backend_lib(source: &str, out: &str) {
    rfs::create_dir_all(out);
    rustc()
        .input(source)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .out_dir(out)
        .run();
}

/// The F1 recipe of the sibling `trust-cg-f1-*` fixtures, plus `lane`'s flags.
fn f1(source: &str, out: &str, lane: &Lane) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(source)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .args(lane.args)
        .out_dir(out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited deauthorization
        // override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// Link `case`'s driver (default backend) against the rlib in `lib_dir`, run it in its own
/// process, and return its one line of output.
fn link_and_run(case: &Case, lib_dir: &str, exe: &str) -> String {
    rustc()
        .input(case.driver)
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Ztrust-verify=off")
        .extern_(case.krate, format!("{lib_dir}/lib{}.rlib", case.krate))
        .library_search_path(lib_dir)
        .output(exe)
        .run();
    cmd(format!("./{exe}")).run().stdout_utf8().trim().to_string()
}

fn check_f1(case: &Case, lane: &Lane, outcome: Outcome) {
    let stem = case.source.trim_end_matches(".rs");
    let label = lane.label;
    let out = format!("out-{stem}-f1-{label}");
    let rlib = format!("{out}/lib{}.rlib", case.krate);
    let n = case.fns.len();
    let all_completed = format!("{n}/{n} reachable function(s) completed");
    let executes_as_oracle = || {
        let got = link_and_run(case, &out, &format!("{stem}-f1-{label}"));
        assert_eq!(
            got, case.expect,
            "{stem} ({label}): the F1-built code EXECUTED differently from the default \
             backend's build of the same source. A C call lost or misplaced its arguments."
        );
    };
    let ships_nothing = || {
        let shipped = std::path::Path::new(&rlib).exists();
        assert!(!shipped, "{stem} ({label}): a refused crate ships nothing");
    };
    let refused = |class: &str, reason: &str, completed: &str| {
        let stderr = f1(case.source, &out, lane).run_fail().stderr_utf8();
        assert!(!stderr.contains("internal compiler error"), "{stem} ({label}):\n{stderr}");
        assert!(stderr.contains(completed), "{stem} ({label}): `{completed}`:\n{stderr}");
        assert!(stderr.contains(class), "{stem} ({label}): refused as `{class}`:\n{stderr}");
        for (symbol, callee) in case.fns {
            let reason = reason.replace("{callee}", callee);
            assert!(
                stderr.lines().any(|l| l.contains("e.g.")
                    && l.contains(symbol)
                    && l.contains(&reason)),
                "{stem} ({label}): no refusal names `{symbol}` with `{reason}`:\n{stderr}"
            );
        }
        ships_nothing();
    };
    match outcome {
        Outcome::Runs => {
            let stderr = f1(case.source, &out, lane).run().stderr_utf8();
            assert!(!stderr.contains("internal compiler error"), "{stem} ({label}):\n{stderr}");
            assert!(
                stderr.contains("reachable function(s) completed"),
                "{stem} ({label}): F1 must have compiled this crate:\n{stderr}"
            );
            executes_as_oracle();
        }
        Outcome::RunsUnproved => {
            let stderr = f1(case.source, &out, lane).run().stderr_utf8();
            assert!(!stderr.contains("internal compiler error"), "{stem} ({label}):\n{stderr}");
            let completed = stderr.contains(&all_completed);
            assert!(completed, "{stem} ({label}): `{all_completed}`:\n{stderr}");
            let report = format!("{n} function(s), 0 closed-[PROVED], {n} not closed, 0 refuted");
            assert!(
                stderr.contains(&report),
                "{stem} ({label}): a call to an external C callee is never closed-[PROVED]: \
                 `{report}`:\n{stderr}"
            );
            for (symbol, _) in case.fns {
                let unknown = format!("{symbol}: Unknown;");
                assert!(
                    stderr
                        .lines()
                        .any(|l| l.contains("not closed-[PROVED]: ") && l.contains(&unknown)),
                    "{stem} ({label}): `{symbol}` must ship disclosed `Unknown`:\n{stderr}"
                );
            }
            executes_as_oracle();
        }
        Outcome::UnprovedRefused => {
            let stderr = f1(case.source, &out, lane).run_fail().stderr_utf8();
            assert!(!stderr.contains("internal compiler error"), "{stem} ({label}):\n{stderr}");
            let completed = stderr.contains(&all_completed);
            assert!(completed, "{stem} ({label}): `{all_completed}`:\n{stderr}");
            let gate = "[f1-output-gate:policy] strict: not closed-[PROVED]: ";
            let line = stderr.lines().find(|l| l.contains("REFUSING to emit") && l.contains(gate));
            let line = line.unwrap_or_else(|| {
                panic!("{stem} ({label}): the strict gate must refuse the module:\n{stderr}")
            });
            for (symbol, _) in case.fns {
                let unknown = format!("{symbol} (Unknown;");
                assert!(
                    line.contains(&unknown),
                    "{stem} ({label}): the gate must name `{symbol}` as `Unknown`:\n{stderr}"
                );
            }
            ships_nothing();
        }
        Outcome::Refused { class, reason } => {
            refused(class, reason, &format!("0/{n} reachable function(s) completed"))
        }
        Outcome::CgRefused { reason } => refused("[trust-cg-refused]", reason, &all_completed),
    }
}

/// One bodyless declaration as the producer publishes it.
#[derive(Debug)]
struct Declaration {
    /// The def path (`; #display-path:`), or the symbol when there is none.
    name: String,
    /// The calling-convention prefix: `rustcc` or empty (C).
    prefix: String,
    /// The functy's shape, e.g. `(i32, i32, ...) -> (i32)`.
    shape: String,
    /// The functy's `SignatureAbi` record (its canonical text, unescaped), if it has one.
    record: Option<String>,
}

/// What a declaration's `SignatureAbi` record must say: a plain C source and lowering, no
/// unwinding, whether it is variadic, and how many FIXED arguments it places (the C-15 fact).
#[derive(Clone, Copy)]
struct Record {
    variadic: bool,
    fixed: usize,
}

/// The functy text printer's `abi("...")` operand, unescaped (`display.rs` `write_escaped_string`).
fn unescape_record(escaped: &str) -> String {
    let mut out = String::with_capacity(escaped.len());
    let mut chars = escaped.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some(e @ ('\\' | '"')) => out.push(e),
            other => panic!("unexpected escape `\\{other:?}` in an ABI record: {escaped}"),
        }
    }
    out
}

fn check_record(source: &str, decl: &Declaration, want: Option<Record>) {
    let name = &decl.name;
    match (want, &decl.record) {
        (None, None) => {}
        (Some(Record { variadic, fixed }), Some(record)) => {
            let census = format!(
                "convention=\"C\",lowered_convention=\"ccc\",source_abi=\"C\",can_unwind=false,\
                 variadic={variadic},fixed_count={fixed},arguments=["
            );
            let has = record.contains(&census);
            assert!(has, "{source}: `{name}`'s ABI record: `{census}`:\n{record}");
            // One placed argument per FIXED parameter; an anonymous argument has none.
            let placed = record.matches("place=\"parameter\"").count();
            assert_eq!(placed, fixed, "{source}: `{name}` places its fixed arguments:\n{record}");
            let results = record.matches("place=\"result\"").count();
            assert_eq!(results, 1, "{source}: `{name}` places one result:\n{record}");
        }
        (Some(_), None) => {
            panic!("{source}: `{name}` must carry its original ABI record: {decl:?}")
        }
        (None, Some(_)) => panic!("{source}: `{name}` has an ABI record this pin does not expect \
                                   (re-measure the compiler-lane rows): {decl:?}"),
    }
}

/// The bodyless declarations in the module the producer publishes for `source`.
fn published_declarations(source: &str, krate: &str) -> Vec<Declaration> {
    let dump = format!("ir-{}", source.trim_end_matches(".rs"));
    rustc()
        .input(source)
        .crate_type("lib")
        .crate_name(krate)
        .edition("2024")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg(format!("-Ztrust-dump=ir:{dump}"))
        .out_dir(format!("{dump}/out"))
        .run();
    let text = rfs::read_to_string(format!("{dump}/{krate}.trust-ir.txt"));
    let functy = |id: &str| -> String {
        let key = format!("{id} = ");
        text.lines()
            .find_map(|l| l.strip_prefix(&key))
            .unwrap_or_else(|| panic!("`{id}` is not defined:\n{text}"))
            .to_string()
    };
    let mut decls = Vec::new();
    let mut lines = text.lines().peekable();
    while let Some(line) = lines.next() {
        let Some(at) = line.find("fn @") else { continue };
        // A declaration has no `bbN` block: its header is followed by comments and `}`.
        let mut has_body = false;
        let mut display_path = None;
        while let Some(next) = lines.peek() {
            if next.starts_with('}') {
                break;
            }
            has_body |= next.trim_start().starts_with("bb");
            if let Some(path) = next.trim_start().strip_prefix("; #display-path: ") {
                display_path = Some(path.trim_matches('"').to_string());
            }
            lines.next();
        }
        if has_body {
            continue;
        }
        let rest = &line[at + 4..];
        let open = rest.rfind('(').expect("a header names its functy");
        let symbol = rest[..open].trim_matches('"').to_string();
        let id = rest[open + 1..].trim_end_matches(|c| c == ')' || c == ' ' || c == '{');
        // WS5.2: `Function.name` is the link-time symbol and the def path is the
        // `; #display-path:` directive. A C callee's symbol is its unmangled item name.
        let name = display_path.unwrap_or_else(|| symbol.clone());
        let leaf = name.rsplit("::").next().unwrap_or(&name);
        assert_eq!(symbol, leaf, "{source}: the C callee `{name}` is named by its C symbol");
        // `functy.N = <shape>[ abi("<escaped canonical SignatureAbi>")]` (trust-ir display.rs).
        let functy = functy(id);
        let (shape, record) = match functy.split_once(" abi(\"") {
            Some((shape, rest)) => {
                let escaped = rest.strip_suffix("\")").unwrap_or_else(|| {
                    panic!("{source}: `{name}`'s ABI record is not closed: {functy}")
                });
                (shape.to_string(), Some(unescape_record(escaped)))
            }
            None => (functy, None),
        };
        decls.push(Declaration { name, prefix: line[..at].trim().to_string(), shape, record });
    }
    decls
}

fn main() {
    // ── PREMISE: what the producer hands F1 ──────────────────────────────────────────────────
    // Every callee is C (no `rustcc`; since S2 a LOCAL block's C ABI is read too).
    // Since FOREIGN-SCALAR-SIGNATURE-1 the variadic `fcntl` keeps its two-argument fixed prefix
    // and a record placing exactly those two, instead of the unsigned `(...)` it was; the
    // non-variadic scalar callees carry the same record. The pointer-to-pointer
    // `posix_spawn_file_actions_*` (signed since 2026-10-15, `(...)` before) carry none, and the
    // variadic `asprintf`, whose fixed prefix starts with that carrier, is still the unsigned
    // `(...)` with no record: the hazard's own declaration.
    const VARIADIC_2: Option<Record> = Some(Record { variadic: true, fixed: 2 });
    const FIXED_2: Option<Record> = Some(Record { variadic: false, fixed: 2 });
    const FIXED_3: Option<Record> = Some(Record { variadic: false, fixed: 3 });
    for (source, krate, want) in [
        ("va_libc.rs", "va", &[("libc::fcntl", "(i32, i32, ...) -> (i32)", VARIADIC_2)][..]),
        ("va_local.rs", "va", &[("fcntl", "(i32, i32, ...) -> (i32)", VARIADIC_2)][..]),
        // The record is the SOURCE's fixed count: the TEETH declaration's is zero.
        (
            "va_zero_fixed.rs",
            "va",
            &[("fcntl", "(...) -> (i32)", Some(Record { variadic: true, fixed: 0 }))][..],
        ),
        (
            "nv_libc.rs",
            "nv",
            &[
                ("libc::dup2", "(i32, i32) -> (i32)", FIXED_2),
                ("libc::lseek", "(i32, i64, i32) -> (i64)", FIXED_3),
            ][..],
        ),
        (
            "nv_local.rs",
            "nv",
            &[
                ("dup2", "(i32, i32) -> (i32)", FIXED_2),
                ("lseek", "(i32, i64, i32) -> (i64)", FIXED_3),
            ][..],
        ),
        (
            "pp_libc.rs",
            "pp",
            &[
                ("libc::posix_spawn_file_actions_adddup2", "(ptr, i32, i32) -> (i32)", None),
                ("libc::posix_spawn_file_actions_destroy", "(ptr) -> (i32)", None),
            ][..],
        ),
        (
            "pp_local.rs",
            "pp",
            &[
                ("posix_spawn_file_actions_adddup2", "(ptr, i32, i32) -> (i32)", None),
                ("posix_spawn_file_actions_destroy", "(ptr) -> (i32)", None),
            ][..],
        ),
        ("vp_local.rs", "vp", &[("asprintf", "(...) -> (i32)", None)][..]),
    ] {
        let decls = published_declarations(source, krate);
        assert_eq!(decls.len(), want.len(), "{source}: one declaration per C callee: {decls:?}");
        for &(name, shape, record) in want {
            let decl = decls.iter().find(|d| d.name == name);
            let decl =
                decl.unwrap_or_else(|| panic!("{source}: no declaration `{name}`: {decls:?}"));
            assert_eq!(decl.prefix, "", "{source}: `{name}` is C (no `rustcc`): {decls:?}");
            assert_eq!(decl.shape, shape, "{source}: `{name}`'s published signature");
            check_record(source, decl, record);
        }
    }

    // ── TEETH: the zero-fixed-argument placement is visible to the `fcntl` driver ─────────────
    let teeth = Case {
        source: "va_zero_fixed.rs",
        krate: "va",
        driver: "va_driver.rs",
        fns: VA_FNS,
        expect: VA_LINE,
        f1: [
            LOCAL_FOREIGN,
            LOCAL_FOREIGN,
            CONVERTER_CALL,
            CONVERTER_CALL,
            UNSIGNED_VARIADIC,
            UNSIGNED_VARIADIC,
        ],
    };
    default_backend_lib(teeth.source, "out-va_zero_fixed-default");
    let got = link_and_run(&teeth, "out-va_zero_fixed-default", "va_zero_fixed-default");
    assert_ne!(
        got, VA_LINE,
        "`fcntl` called with zero fixed arguments must NOT pass for a correct call on this host; \
         if it does, the `va_*` rows below that RUN cannot detect the C-15 miscompile"
    );
    // F1 never makes that call: on the compiler lane, which calls the RECORDED `va_*`
    // declarations, trust-cg refuses this zero-fixed one by name, and nothing ships. (`expect`
    // is unused: no lane runs it.)
    for (lane, outcome) in LANES.iter().zip(teeth.f1) {
        check_f1(&teeth, lane, outcome);
    }

    for case in CASES {
        let stem = case.source.trim_end_matches(".rs");
        // ── ORACLE: the default backend's build, executed ─────────────────────────────────────
        let oracle_dir = format!("out-{stem}-default");
        default_backend_lib(case.source, &oracle_dir);
        let got = link_and_run(case, &oracle_dir, &format!("{stem}-default"));
        assert_eq!(got, case.expect, "{stem}: the oracle's own line on this host");

        // ── F1, on every lane ─────────────────────────────────────────────────────────────────
        for (lane, outcome) in LANES.iter().zip(case.f1) {
            check_f1(case, lane, outcome);
        }
    }
}
