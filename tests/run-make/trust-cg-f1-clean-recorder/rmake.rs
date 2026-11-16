//! Trust (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.1, §9 3.5): THE
//! CLEAN RECORDER ON F1, WITHOUT MIR, VERIFICATION ON OR OFF.
//!
//! On F1 (`-Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir -Ztrust-ir-lower`) the Clean
//! recorder runs on every compile, whatever `-Ztrust-verify` says, and demands no
//! `clean_origin_mir` body: no eager demand, no per-row MIR re-earn. A row's verdict is the carrier
//! gate's on the published Function. The Clean language's two Rust-callee rules, which the MIR lane
//! decides inside the `clean_origin_mir` provider, are decided on trust-ir: purity over the callee's
//! conserved effect census, the cross-language cycle over the module's call graph.
//!
//! What it pins (the design's four tests, each FAILING on the base `901d27ca30`, measured):
//! * `verify_off_and_verify_on_record_the_same_rows` — the `clean_origin` coverage section of an F1
//!   compile is the same with verification on and off, and the same as the MIR lane's
//!   `--emit=trust-ir` verify-on section (before: `"recorded": false` with verification off);
//! * `cycle_across_languages_refused_on_f1` — `fn inc` -> `def twice_inc` -> `inc` is refused on F1
//!   from the published module's call graph (before: refused by the MIR lane's provider, the only
//!   place the rule lived);
//! * `impure_rust_callee_refused_on_f1` — a Rust callee writing a `static mut` global is refused on
//!   F1 from its conserved trust-ir effect census (before: by the MIR walk), and one writing through
//!   a `&mut` to a global, whose body the trust-ir producer does not assemble (so the census cannot
//!   decide it), is refused on F1 by the MIR walk of the RUST callee, consulted to refuse only;
//!
//! With verification ON the verifier still reads a Clean def's `clean_origin_mir` body as its
//! callee model until item V (design §5.7; its backing-certificate initializer builds it, charged to
//! the reach counter's `verification` lane), and the MIR provider's own call gate refuses an impure
//! callee or a cycle there, before F1's trust-ir check is reached. Both lanes refuse the same
//! program; the trust-ir wording is asserted where F1 decides alone, with verification off.
//! * `the_recorder_reaches_no_clean_origin_mir_on_f1` — F1's reach counter
//!   (`clean_origin_mir_reached`, design §5.7) prints `recorder 0` (and `codegen 0`, `inventory 0`:
//!   step 3.3's exit, readable since the counter exists) with verification on and off (before: no
//!   counter, and the recorder and the analysis-seam demands built every named def's body).
//!
//! THE ORACLE LANE (design §6). The MIR re-earn moved here, not away: each fixture is also compiled
//! on the MIR lane, where the recorder re-earns every row's kernel verdict against its emitted MIR
//! and the provider runs the MIR purity walk and cycle check. Its rows must equal F1's, and the
//! MIR lane must refuse exactly the programs F1 refuses; a disagreement fails this test.
//! `the_oracle_lane_fails_on_a_mir_disagreement_f1_never_reads` shows the oracle has teeth: a
//! wrong MIR emission (`-Ztrust-clean-origin-mutate-emitter`) fails the MIR lane's re-earn, while
//! F1's recorder, with verification off, publishes the same `gate` row it publishes without the
//! knob: it read no MIR body. The compile still fails, later, where the metadata encoder (the
//! cross-crate reader, I7, until increment 6) builds the mutated body; trust-cg emits only rlibs,
//! so every F1 compile encodes metadata (before 3.5 the analysis-seam demand built the body and
//! refused before any row was published).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// The design's fixtures (§1.3), as in `tests/run-make/trust-cg-f1-mixed-crate`.
const T1: &str = r#"#![crate_name = "t1"]
mod m {
    clean {
        def cleanWsum (a : UInt64) (b : UInt64) : UInt64 := a + b
    }
}
#[inline(never)]
pub fn calls_clean(x: u64) -> u64 { m::cleanWsum(x, 1) }
#[inline(never)]
pub fn rust_only(x: u64) -> u64 { x ^ 0x55 }
"#;

const T2: &str = r#"#![crate_name = "t2"]
mod m {
    clean {
        def fstIsl (a : UInt64) (b : UInt64) : UInt64 := a
    }
}
#[inline(never)]
pub fn calls_fst(x: u64, y: u64) -> u64 { m::fstIsl(x, y) }
"#;

const T3: &str = r#"#![crate_name = "t3"]
mod m {
    clean {
        def cleanMin (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}
#[inline(never)]
pub fn calls_min(x: u64, y: u64) -> u64 { m::cleanMin(x, y) }
"#;

const T4: &str = r#"#![crate_name = "t4"]
#[inline(never)]
pub fn inc(x: u64) -> u64 { x.wrapping_add(1) }
clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
#[inline(never)]
pub fn calls_twice(x: u64) -> u64 { twice_inc(x) }
"#;

const T4P: &str = r#"#![crate_name = "t4p"]
#[inline(never)]
fn inc(x: u64) -> u64 { x.wrapping_add(1) }
clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
#[inline(never)]
pub fn calls_twice(x: u64) -> u64 { twice_inc(x) }
"#;

/// Lean calls a Rust callee the census can decide: no upstream call, no effect.
const TMIX: &str = r#"#![crate_name = "tmix"]
#[inline(never)]
pub fn mix(x: u64) -> u64 { x ^ 0x55 }
clean {
    def twice_mix (x : UInt64) : UInt64 := mix (mix x)
}
#[inline(never)]
pub fn calls_mix(x: u64) -> u64 { twice_mix(x) }
"#;

/// The design's `impure_rust_callee_refused_on_f1` subject, in the form the trust-ir producer
/// assembles: a callee writing a `static mut` global (in trust-ir a store through the global's
/// address), so the conserved effect census decides it.
const IMPURE: &str = r#"#![crate_name = "impure"]
static mut SINK: u64 = 0;
#[inline(never)]
pub fn bump(x: u64) -> u64 {
    unsafe { SINK = x; }
    x
}
clean {
    def useBump (x : UInt64) : UInt64 := bump x
}
#[inline(never)]
pub fn calls_bump(x: u64) -> u64 { useBump(x) }
"#;

/// The design's subject verbatim: a callee writing through a `&mut` to a global. The trust-ir
/// producer does not assemble `bump` (measured: the Clean row is skipped, "callee 0 has 0
/// assembled owners"), so the census has no Function to read; F1 consults the MIR walk of the
/// Rust callee, which may only refuse (docs/DECISION_QUEUE.md STEP3.5-PURITY-UNDECIDED).
const IMPURE_MUT_REF: &str = r#"#![crate_name = "impure_ref"]
static mut SINK: u64 = 0;
#[inline(never)]
pub fn bump(x: u64) -> u64 {
    let sink: &mut u64 = unsafe { &mut *(&raw mut SINK) };
    *sink = x;
    x
}
clean {
    def useBump (x : UInt64) : UInt64 := bump x
}
#[inline(never)]
pub fn calls_bump(x: u64) -> u64 { useBump(x) }
"#;

/// The design's `cycle_across_languages_refused_on_f1` subject
/// (`tests/ui/trust/clean_origin_cross_language_cycle_refused.rs` as a library).
const CYCLE: &str = r#"#![crate_name = "cycle"]
#[inline(never)]
pub fn inc(x: u64) -> u64 {
    if x == 0 { 0 } else { twice_inc(x - 1) }
}
clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
#[inline(never)]
pub fn calls_twice(x: u64) -> u64 { twice_inc(x) }
"#;

/// The reach counter's line (design §5.7).
const REACH_PREFIX: &str = "`clean_origin_mir` reached: ";

fn write(name: &str, source: &str) -> String {
    let input = format!("{name}.rs");
    rfs::write(&input, source);
    input
}

/// An F1 compile of `name`, its published module dumped to `dump-<name>-<tag>`.
fn f1(name: &str, source: &str, verify: bool, tag: &str) -> run_make_support::Rustc {
    let input = write(name, source);
    let out = format!("out-{name}-{tag}");
    let dump = format!("dump-{name}-{tag}");
    rfs::create_dir_all(&out);
    rfs::create_dir_all(&dump);
    let mut cmd = rustc();
    cmd.input(&input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg(if verify { "-Ztrust-verify=on" } else { "-Ztrust-verify=off" })
        .arg(format!("-Ztrust-dump=ir:{dump}"))
        .arg("--crate-name")
        .arg(name)
        .out_dir(&out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited deauthorization
        // override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV);
    if verify {
        cmd.arg("-Ztrust-cg-output-gate=allow-unknown");
    }
    cmd
}

/// The MIR lane's `--emit=trust-ir` compile of `name` (not F1): with verification on, the recorder
/// demands every gated body and re-earns each row's kernel verdict against its emitted MIR.
fn mir_lane_emit(
    name: &str,
    source: &str,
    verify: bool,
    extra: &[&str],
) -> run_make_support::Rustc {
    let input = write(name, source);
    let out = format!("emit-{name}-{verify}");
    rfs::create_dir_all(&out);
    let mut cmd = rustc();
    cmd.input(&input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg(if verify { "-Ztrust-verify=on" } else { "-Ztrust-verify=off" })
        .args(extra)
        .arg("--emit=trust-ir")
        .out_dir(&out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// The default LLVM lane (the MIR lane), verification off: the language's call gate runs in the
/// `clean_origin_mir` provider.
fn mir_lane_build(name: &str, source: &str) -> run_make_support::Rustc {
    let input = write(name, source);
    let out = format!("llvm-{name}");
    rfs::create_dir_all(&out);
    let mut cmd = rustc();
    cmd.input(&input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .out_dir(&out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// The `"clean_origin": { ... }` section of a coverage JSON, by brace matching outside strings.
fn clean_origin_section(json: &str) -> String {
    let key = "\"clean_origin\": {";
    let start = json.find(key).unwrap_or_else(|| panic!("no clean_origin section in:\n{json}"));
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for (i, c) in json[start + key.len() - 1..].char_indices() {
        if in_string {
            match (escaped, c) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return json[start..start + key.len() + i].to_string();
                }
            }
            _ => {}
        }
    }
    panic!("unterminated clean_origin section in:\n{json}")
}

fn no_ice(what: &str, stderr: &str) {
    for forbidden in ["internal compiler error", "panicked at", "thread 'rustc'"] {
        assert!(!stderr.contains(forbidden), "{what}: an ICE (`{forbidden}`):\n{stderr}");
    }
}

/// F1 compiles every recording fixture to its refusal census (no fixture with a Clean def
/// completes on F1 before plan step 3.6) and records; the section, and the stderr.
fn f1_recorded(name: &str, source: &str, verify: bool) -> (String, String) {
    let tag = if verify { "on" } else { "off" };
    let output = f1(name, source, verify, tag).run_fail();
    let stderr = output.stderr_utf8();
    no_ice(&format!("{name} F1 {tag}"), &stderr);
    assert!(
        stderr.contains("reachable function(s) completed"),
        "{name} F1 {tag}: the compile reaches F1's census:\n{stderr}"
    );
    let coverage = rfs::read_to_string(format!("dump-{name}-{tag}/{name}.coverage.json"));
    (clean_origin_section(&coverage), stderr)
}

const RECORDING: &[(&str, &str)] =
    &[("t1", T1), ("t2", T2), ("t3", T3), ("t4", T4), ("t4p", T4P), ("tmix", TMIX)];

fn verify_off_and_verify_on_record_the_same_rows() {
    for &(name, source) in RECORDING {
        let (on, _) = f1_recorded(name, source, true);
        let (off, _) = f1_recorded(name, source, false);
        assert!(
            on.contains("\"recorded\": true"),
            "{name}: F1 records with verification on:\n{on}"
        );
        assert_eq!(off, on, "{name}: F1's rows with verification off are its rows with it on");
        // THE ORACLE (the MIR re-earn): the MIR lane, verification on, re-earns every row against
        // its emitted MIR, and its rows (tiers, shapes, gate digests, links) are F1's.
        let mir = mir_lane_emit(name, source, true, &[]).run();
        no_ice(&format!("{name} MIR lane"), &mir.stderr_utf8());
        let mir = clean_origin_section(&rfs::read_to_string(format!(
            "emit-{name}-true/{name}.trust-ir.coverage.json"
        )));
        assert_eq!(mir, on, "{name}: the MIR lane's verify-on rows are F1's");
    }
    // t1's wrapping-binop row is tier `gate`, recorded with verification off too.
    let (off, _) = f1_recorded("t1", T1, false);
    assert!(off.contains("\"tier\": \"gate\""), "{off}");
    assert!(off.contains("\"codegen_license\": \"clean-carrier-gate\""), "{off}");
    // Verification-off artifact lanes that are not F1 keep `recorded: false` (no new fatal
    // surface, 08-27 §3).
    mir_lane_emit("t1", T1, false, &[]).run();
    let off_lane = rfs::read_to_string("emit-t1-false/t1.trust-ir.coverage.json".to_string());
    assert!(
        clean_origin_section(&off_lane).contains("\"recorded\": false"),
        "a verification-off non-F1 artifact lane still records nothing:\n{off_lane}"
    );
}

/// The reach counter's line in `stderr`, which must exist.
fn reach_line(what: &str, stderr: &str) -> String {
    stderr
        .lines()
        .find(|line| line.contains(REACH_PREFIX))
        .unwrap_or_else(|| {
            panic!("{what}: F1 prints no `clean_origin_mir` reach counter:\n{stderr}")
        })
        .to_string()
}

fn the_recorder_reaches_no_clean_origin_mir_on_f1() {
    for &(name, source) in RECORDING {
        for verify in [true, false] {
            let (_, stderr) = f1_recorded(name, source, verify);
            let line = reach_line(name, &stderr);
            assert!(
                line.contains("reached: codegen 0, inventory 0, recorder 0 "),
                "{name} (verify {verify}): F1's path reads no `clean_origin_mir` body: {line}"
            );
            // Every build is claimed by a lane: a read on F1's path cannot hide as unattributed
            // (with verification on, the verifier's initializers build the body, `verification`;
            // with it off, the metadata encoder, `cross-crate`).
            assert!(
                line.contains("unattributed 0 "),
                "{name} (verify {verify}): a `clean_origin_mir` build no lane claimed: {line}"
            );
        }
    }
}

fn impure_rust_callee_refused_on_f1() {
    // Verification off: F1 decides alone, on the conserved trust-ir effect census.
    let output = f1("impure", IMPURE, false, "off").run_fail();
    let stderr = output.stderr_utf8();
    no_ice("impure F1 off", &stderr);
    for needle in [
        "Clean declaration `useBump` cannot be called from Rust",
        "a Clean `def` may only call a PURE Rust fn",
        "on the conserved trust-ir effect census, `bump`",
        "writes memory outside its own frame, through a pointer rooted at a global",
    ] {
        assert!(stderr.contains(needle), "impure F1 off: missing `{needle}` in:\n{stderr}");
    }
    assert!(
        !stderr.contains("reachable function(s) completed"),
        "impure F1 off: the language refusal stops the compile before codegen:\n{stderr}"
    );
    // The `&mut` global: no trust-ir body for the census to read, so F1 consults the MIR walk of
    // the Rust callee, to refuse only.
    let output = f1("impure_ref", IMPURE_MUT_REF, false, "off").run_fail();
    let stderr = output.stderr_utf8();
    no_ice("impure_ref F1 off", &stderr);
    for needle in [
        "Clean declaration `useBump` cannot be called from Rust",
        "a Clean `def` may only call a PURE Rust fn, but `bump` is not provably pure",
        "The conserved trust-ir effect census could not decide it",
        "F1 consulted the MIR walk, which it uses only to refuse",
    ] {
        assert!(stderr.contains(needle), "impure_ref F1 off: missing `{needle}` in:\n{stderr}");
    }
    assert!(!stderr.contains("reachable function(s) completed"), "{stderr}");
    // Verification on: the verifier reads the Clean body as its callee model (until item V), and
    // the MIR provider's call gate refuses first. Still refused on F1, by the same rule.
    for (name, source) in [("impure", IMPURE), ("impure_ref", IMPURE_MUT_REF)] {
        let output = f1(name, source, true, "on").run_fail();
        let stderr = output.stderr_utf8();
        no_ice(&format!("{name} F1 on"), &stderr);
        for needle in [
            "Clean declaration `useBump` cannot be called from Rust",
            "a Clean `def` may only call a PURE Rust fn",
        ] {
            assert!(stderr.contains(needle), "{name} F1 on: missing `{needle}` in:\n{stderr}");
        }
        assert!(!stderr.contains("reachable function(s) completed"), "{name} F1 on:\n{stderr}");
    }
    // THE ORACLE: the MIR lane refuses both programs, by its MIR walk.
    for (name, source) in [("impure", IMPURE), ("impure_ref", IMPURE_MUT_REF)] {
        let output = mir_lane_build(name, source).run_fail();
        let stderr = output.stderr_utf8();
        for needle in [
            "Clean declaration `useBump` cannot be called from Rust",
            "accesses global or aliased mutable state",
        ] {
            assert!(stderr.contains(needle), "{name} MIR lane: missing `{needle}` in:\n{stderr}");
        }
        assert!(!stderr.contains("trust-ir effect census"), "{stderr}");
    }
    // And a pure Rust callee is admitted by both: F1 records it (the census decides it pure),
    // and the MIR lane compiles it.
    f1_recorded("tmix", TMIX, false);
    mir_lane_build("tmix", TMIX).run();
}

fn cycle_across_languages_refused_on_f1() {
    // Verification off: F1 decides alone, on the published module's call graph.
    let output = f1("cycle", CYCLE, false, "off").run_fail();
    let stderr = output.stderr_utf8();
    no_ice("cycle F1 off", &stderr);
    for needle in [
        "Clean declaration `twice_inc` cannot be called from Rust",
        "CROSS-LANGUAGE CYCLE",
        "calls Rust `fn inc`, which leads back to `twice_inc`",
        "on this crate's published trust-ir call graph",
    ] {
        assert!(stderr.contains(needle), "cycle F1 off: missing `{needle}` in:\n{stderr}");
    }
    assert!(!stderr.contains("E0391"), "cycle F1 off: a designed refusal, not E0391");
    // Verification on: the verifier's callee model reads the body first (until item V), and the
    // MIR provider's cycle check refuses. Still refused on F1, by the same rule.
    let output = f1("cycle", CYCLE, true, "on").run_fail();
    let stderr = output.stderr_utf8();
    no_ice("cycle F1 on", &stderr);
    for needle in
        ["Clean declaration `twice_inc` cannot be called from Rust", "CROSS-LANGUAGE CYCLE"]
    {
        assert!(stderr.contains(needle), "cycle F1 on: missing `{needle}` in:\n{stderr}");
    }
    assert!(!stderr.contains("E0391"), "cycle F1 on: a designed refusal, not E0391");
    // THE ORACLE: the MIR lane refuses the same program, by its own cycle check.
    let output = mir_lane_build("cycle", CYCLE).run_fail();
    let stderr = output.stderr_utf8();
    assert!(stderr.contains("CROSS-LANGUAGE CYCLE"), "cycle MIR lane:\n{stderr}");
    assert!(!stderr.contains("published trust-ir call graph"), "{stderr}");
}

fn the_oracle_lane_fails_on_a_mir_disagreement_f1_never_reads() {
    // A wrong MIR emission: the MIR lane's verify-on recorder demands the body, whose gate refuses
    // it. The oracle fails.
    let output = mir_lane_emit("t2", T2, true, &["-Ztrust-clean-origin-mutate-emitter"]).run_fail();
    let stderr = output.stderr_utf8();
    assert!(
        stderr.contains("refusing to emit code for Clean declaration `fstIsl`"),
        "the MIR re-earn's gate refuses the mutated emission:\n{stderr}"
    );
    // F1, verification off, the same knob: the recorder reads no MIR body, so it publishes the
    // same row (tier `gate`, the same gate digest) it publishes without the knob. The compile
    // fails only afterwards, where the metadata encoder builds the mutated body (I7, the
    // cross-crate reader, until increment 6; trust-cg emits only rlibs). Before 3.5 the
    // analysis-seam demand built it first and refused before any row was published.
    let (clean, _) = f1_recorded("t2", T2, false);
    let output =
        f1("t2", T2, false, "mutated").arg("-Ztrust-clean-origin-mutate-emitter").run_fail();
    let stderr = output.stderr_utf8();
    no_ice("t2 F1 mutated", &stderr);
    assert!(
        stderr.contains("refusing to emit code for Clean declaration `fstIsl`"),
        "t2 F1 mutated: the cross-crate encoder builds the mutated body and refuses it:\n{stderr}"
    );
    let mutated =
        clean_origin_section(&rfs::read_to_string("dump-t2-mutated/t2.coverage.json".to_string()));
    assert!(mutated.contains("\"tier\": \"gate\""), "{mutated}");
    assert_eq!(mutated, clean, "F1's row does not depend on the MIR emission");
}

fn main() {
    let checks: &[(&str, fn())] = &[
        (
            "verify_off_and_verify_on_record_the_same_rows",
            verify_off_and_verify_on_record_the_same_rows,
        ),
        ("cycle_across_languages_refused_on_f1", cycle_across_languages_refused_on_f1),
        ("impure_rust_callee_refused_on_f1", impure_rust_callee_refused_on_f1),
        (
            "the_recorder_reaches_no_clean_origin_mir_on_f1",
            the_recorder_reaches_no_clean_origin_mir_on_f1,
        ),
        (
            "the_oracle_lane_fails_on_a_mir_disagreement_f1_never_reads",
            the_oracle_lane_fails_on_a_mir_disagreement_f1_never_reads,
        ),
    ];
    // Every check runs and reports, so one run names each one that fails.
    let mut failed = Vec::new();
    for (name, check) in checks {
        match std::panic::catch_unwind(check) {
            Ok(()) => eprintln!("PASS {name}"),
            Err(_) => {
                eprintln!("FAIL {name}");
                failed.push(*name);
            }
        }
    }
    assert!(failed.is_empty(), "failed: {failed:?}");
}

/// The recipe under libtest as well as compiletest (a frozen-file waiver may cite it).
#[test]
fn the_recorder_runs_on_every_f1_compile_without_mir() {
    main();
}
