//! Trust (plan step 3.0 and 3.3, docs/design/2026-10-02-step3-lean-through-trust-ir.md §9): the
//! BASELINE the later step-3 increments flip. One crate, two languages, handed to F1
//! (`-Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir`), with the refusal census of every
//! fixture of the design's §1.3 measurement pinned row by row:
//!
//! * t1 `cleanWsum` (`a + b` at `UInt64`, tier `gate`) with a Rust caller and a Rust-only body;
//! * t2 `fstIsl` (projection, tier `gate`);
//! * t3 `cleanMin` (select, tier `structural`);
//! * t4 Lean calls Rust (`twice_inc := inc (inc x)`, tier `structural`);
//! * t6 a Rust-only control.
//!
//! Verification ON and OFF (since plan step 3.5 the Clean recorder runs on every F1 compile, so
//! every row names its disclosed tier and shape on both); the crate-module lane on t1; and step
//! 3.3's `-Copt-level=2 -Ztrust-verify=off` variant.
//!
//! What it pins (each FAILED before its change, measured on a stage 1 of `a6807aa6f0`):
//! * 3.0 — every refusal F1 makes because of a Clean-origin body is `[clean-below-gate]`; no
//!   Clean-origin item is `[producer-declined]`, `[converter-refused]`, `[instance-assembly]` or
//!   `[crate-module-unavailable]` (before: the def `[producer-declined]` with no Clean reason,
//!   the caller `[converter-refused]` or `[instance-assembly]`, every crate-module item
//!   `[crate-module-unavailable]`);
//! * 3.3 — the F1 inventory reads a Clean-origin def's neighbours from its published trust-ir row,
//!   not from `clean_origin_mir`'s MIR, wherever the row is recorded (verification on): t1 has no
//!   `core::num::<impl u64>::wrapping_add` row (before: `[upstream-body]`, 1/4 completed). With
//!   verification on the neighbour sets agree with the MIR lane's modulo the primitive call the
//!   trust-ir row spells as an instruction (`-Zprint-mono-items`: the LLVM lane's t1 inventory has
//!   `wrapping_add`, F1's has not; t4's and t4p's Rust callee `inc` is in both).
//! * 3.3 — at `-Copt-level=2` with verification off the MIR inliner leaves `cleanWsum` a call
//!   on F1, so the Clean def is its own item, refused by name: two `[clean-below-gate]` rows
//!   (before: 1/2 with one `[instance-assembly]` row, measured by the step-3 review on a stage 1
//!   of `a6807aa6f0` plus unrelated main commits: the inliner had copied `cleanWsum`'s
//!   `clean_origin_mir` body, and the `wrapping_add` it calls, into `calls_clean`'s MIR, so the
//!   Clean def was in no inventory and F1 refused its caller only for a callee with no handoff
//!   body).
//! * Plan R-8 (step-3 review, 2026-10-07): before step 3.5, with verification off nothing was
//!   recorded, so F1 had no row to read for a Clean-origin def and walked its MIR as the base
//!   compiler did (t4p 0/4, and t1's MIR-only `wrapping_add` an `[upstream-body]` row, 1/4).
//!   Before that review the inventory answered "no neighbour" for an unrecorded def and t4p read
//!   0/2 with neither row (measured on the stage 1 of `089bf5bd50`).
//! * 3.5 (the recorder on every F1 compile, docs/design/2026-10-02-step3-lean-through-trust-ir.md
//!   §5.1) — the verification-off rows ARE the verify-on ones: t1 loses its `wrapping_add`
//!   `[upstream-body]` row (1/3, was 1/4) at `-Copt-level=0` and `2`, every Clean refusal names
//!   the row's tier and shape (was "not recorded on this lane"), and t4p's neighbours come from
//!   its recorded row (it keeps `inc`, which its row calls, and the `wrapping_add` `inc`'s own MIR
//!   calls). F1's `clean_origin_mir` reach counter reads `codegen 0, inventory 0, recorder 0` on
//!   every lane here (3.3's exit, readable since 3.5; design §5.7). Measured failing on the base
//!   `901d27ca30`.
//!
//! * 3.4 (per-function leg 4, owner ruling D37) — on the crate-module lane a Clean-origin row
//!   no longer withdraws the crate's Rust license: t1's `rust_only` COMPLETES (1/3; before: 0/3,
//!   every item `[crate-module-unavailable]` renamed `[clean-below-gate]` as "the crate's whole
//!   codegen license was withheld"), and so does a Rust-only body beside t3's below-`gate`
//!   `cleanMin` (t3r, 1/3). The published module stamps `cleanWsum` `gated "clean-carrier-gate"`
//!   and the Rust bodies `gated "trust-direct-lane-structural"` (before: every body `ungated`);
//!   `cleanMin` stays `ungated` and is refused by name only where it is reached (its own item and
//!   its caller). Measured on a stage 1 of this branch, and failing on the base.
//!
//! The rows a later step flips are named where they are pinned: 3.6 (admission on
//! `Compiler::compile`), increment 6 (upstream bodies).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// Plan step 3.4: why the handoff lane holds no body for a Clean-origin def's own item
/// (`clean_below_gate::own_def_why`).
const LEDGER_ONLY: &str = "it indexes a `Producer::Clean` row only as an entry of this Session's \
                           carrier ledger";

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

/// t3 with a Rust-only body beside the below-`gate` row: plan step 3.4's "refused by name only if
/// reached".
const T3R: &str = r#"#![crate_name = "t3r"]
mod m {
    clean {
        def cleanMin (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}
#[inline(never)]
pub fn calls_min(x: u64, y: u64) -> u64 { m::cleanMin(x, y) }
#[inline(never)]
pub fn rust_only(x: u64) -> u64 { x ^ 0x55 }
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

/// t4 with a PRIVATE Rust callee: `inc` is no root, so the F1 inventory reaches it only through
/// `twice_inc`'s published trust-ir row (3.3's neighbour reading), as the MIR lane reaches it
/// through `clean_origin_mir`'s call.
const T4P: &str = r#"#![crate_name = "t4p"]
#[inline(never)]
fn inc(x: u64) -> u64 { x.wrapping_add(1) }
clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
#[inline(never)]
pub fn calls_twice(x: u64) -> u64 { twice_inc(x) }
"#;

const T6: &str = r#"#![crate_name = "t6"]
#[inline(never)]
pub fn rust_only(x: u64) -> u64 { x ^ 0x55 }
"#;

#[derive(Clone, Copy)]
enum Lane {
    VerifyOn,
    VerifyOff,
    VerifyOffO2,
    CrateModule,
}

fn f1(name: &str, source: &str, lane: Lane) -> run_make_support::Rustc {
    let input = format!("{name}.rs");
    rfs::write(&input, source);
    let out = format!("out-{name}-{}", lane as u8);
    rfs::create_dir_all(&out);
    let mut cmd = rustc();
    cmd.input(&input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(&out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited deauthorization
        // override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV);
    match lane {
        Lane::VerifyOn => {
            cmd.arg("-Ztrust-verify=on").arg("-Ztrust-cg-output-gate=allow-unknown");
        }
        Lane::VerifyOff => {
            cmd.arg("-Ztrust-verify=off");
        }
        Lane::VerifyOffO2 => {
            cmd.arg("-Ztrust-verify=off").arg("-Copt-level=2");
        }
        Lane::CrateModule => {
            cmd.arg("-Ztrust-verify=on")
                .arg("-Ztrust-cg-output-gate=allow-unknown")
                .arg("-Ztrust-ir-crate-module=on");
        }
    }
    cmd
}

/// The census line for `class` with `count` rows (the census prints `count (pct%) [class]`).
fn class_count(stderr: &str, class: &str) -> usize {
    stderr
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let (count, rest) = line.split_once(' ')?;
            rest.trim_end().ends_with(&format!("[{class}]")).then(|| count.parse::<usize>().ok())?
        })
        .sum()
}

const CLASSES: &[&str] = &[
    "upstream-body",
    "synthesized-instance",
    "generic-instance",
    "unsupported-abi",
    "producer-declined",
    "malformed-producer-module",
    "converter-refused",
    "crate-module-unavailable",
    "ungated-body",
    "unlicensed-body",
    "unlicensed-by-producer",
    "not-a-local-item",
    "instance-assembly",
    "elided-drop",
    "unfaithful-panic",
    "effect-not-conserved",
    "clean-below-gate",
];

/// Refused with exactly these rows (every other class zero), `completed` of `reachable`
/// completed, and every expected needle in the census.
fn refused(
    name: &str,
    source: &str,
    lane: Lane,
    completed: usize,
    reachable: usize,
    rows: &[(&str, usize)],
    needles: &[&str],
) -> String {
    let output = f1(name, source, lane).run_fail();
    let stderr = output.stderr_utf8();
    for forbidden in ["internal compiler error", "panicked at", "thread 'rustc'"] {
        assert!(!stderr.contains(forbidden), "{name}: an ICE (`{forbidden}`):\n{stderr}");
    }
    let header = format!("{completed}/{reachable} reachable function(s) completed");
    assert!(stderr.contains(&header), "{name}: missing `{header}` in:\n{stderr}");
    for class in CLASSES {
        let want = rows.iter().find(|(c, _)| c == class).map_or(0, |(_, n)| *n);
        assert_eq!(class_count(&stderr, class), want, "{name}: `[{class}]` rows in:\n{stderr}");
    }
    for needle in needles {
        assert!(stderr.contains(needle), "{name}: missing `{needle}` in:\n{stderr}");
    }
    // Plan step 3.5 (design §5.7): F1's codegen, its inventory and the Clean recorder read no
    // `clean_origin_mir` body, on every lane here.
    assert!(
        stderr.contains("`clean_origin_mir` reached: codegen 0, inventory 0, recorder 0 "),
        "{name}: F1's path read a `clean_origin_mir` body:\n{stderr}"
    );
    stderr
}

/// The `#body-gate:` directive of the function whose header starts `rustcc fn @<name>(` in a
/// canonical module text.
/// WS5.2: `Function.name` is the link-time symbol, so a function is found by the def path it
/// DISPLAYS (`; #display-path:`), the spelling `name` is; exactly one block may display it.
fn body_gate_of<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    let directive = format!("; #display-path: {name:?}");
    let mut found = None;
    let mut lines = text.lines().peekable();
    while let Some(line) = lines.next() {
        if !line.trim_start().starts_with("rustcc fn @") {
            continue;
        }
        let mut gate = None;
        let mut displays = false;
        while let Some(meta) = lines.next_if(|line| line.trim_start().starts_with(';')) {
            let meta = meta.trim_start();
            displays |= meta == directive;
            gate = gate.or(meta.strip_prefix("; #body-gate: "));
        }
        if displays {
            assert!(found.is_none(), "two functions display `{name}`:\n{text}");
            found = Some(gate);
        }
    }
    found.flatten()
}

/// Plan step 3.4: the crate-module lane's compile of `name`, with the published module dumped,
/// and the dump's canonical text.
fn crate_module_dump(name: &str, source: &str) -> String {
    let dump = format!("dump-{name}");
    rfs::create_dir_all(&dump);
    // `-Ztrust-dump=ir` with `-Ztrust-ir-lower` requires an explicit `--crate-name`.
    let _ = f1(name, source, Lane::CrateModule)
        .arg(format!("-Ztrust-dump=ir:{dump}"))
        .arg("--crate-name")
        .arg(name)
        .run_fail();
    rfs::read_to_string(format!("{dump}/{name}.trust-ir.txt"))
}

fn main() {
    // ── t1: the wrapping-binop `gate` row ─────────────────────────────────────────────────
    // 3.6 flips: `calls_clean` and `cleanWsum` complete under the Compiler::compile lane.
    let on = refused(
        "t1",
        T1,
        Lane::VerifyOn,
        1,
        3,
        &[("clean-below-gate", 2)],
        &[
            "the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
            "reaches the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
        ],
    );
    assert!(!on.contains("wrapping_add"), "3.3: no MIR-only neighbour of `cleanWsum`:\n{on}");
    // Plan step 3.5: the recorder runs on every F1 compile, so with verification off the rows are
    // the verify-on rows above (before: 1/4, both Clean refusals "not recorded on this lane", and
    // the inventory walked `cleanWsum`'s MIR, so its MIR-only `wrapping_add` was an
    // `[upstream-body]` row), at `-Copt-level=0` and `2`.
    for lane in [Lane::VerifyOff, Lane::VerifyOffO2] {
        let off = refused(
            "t1",
            T1,
            lane,
            1,
            3,
            &[("clean-below-gate", 2)],
            &[
                "the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
                "reaches the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
            ],
        );
        assert!(!off.contains("wrapping_add"), "3.5: the row, not the MIR walk:\n{off}");
        assert!(!off.contains("not recorded on this lane"), "3.5: recorded:\n{off}");
        // Plan step 3.4 (landing review): the def's own item never says "it never indexes a
        // `Producer::Clean` row" (false since 3.4, naming the test-only `checked`).
        assert!(!off.contains("never indexes a `Producer::Clean` row"), "{off}");
    }
    // The crate-module lane. Plan step 3.4 (D37): leg 4 is per function, so the appended Clean
    // row no longer withdraws the crate's Rust license and `rust_only` COMPLETES (before: 0/3,
    // the whole module withheld). `cleanWsum` is licensed `clean-carrier-gate` in the published
    // module, but this lane honors no Clean carrier (step 3.6): the def and its caller are
    // refused by name.
    let cm = refused(
        "t1",
        T1,
        Lane::CrateModule,
        1,
        3,
        &[("clean-below-gate", 2)],
        &[
            "the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
            "reaches the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
        ],
    );
    assert!(!cm.contains("whole codegen license was withheld"), "3.4: no withholding:\n{cm}");
    let text = crate_module_dump("t1", T1);
    assert_eq!(body_gate_of(&text, "cleanWsum"), Some("gated \"clean-carrier-gate\""), "{text}");
    for rust in ["calls_clean", "rust_only"] {
        assert_eq!(
            body_gate_of(&text, rust),
            Some("gated \"trust-direct-lane-structural\""),
            "3.4: `{rust}` keeps its license:\n{text}"
        );
    }

    // ── t2: the projection `gate` row ───────────────────────────────────────────────────
    refused(
        "t2",
        T2,
        Lane::VerifyOn,
        0,
        2,
        &[("clean-below-gate", 2)],
        &["the Clean-origin def `m::fstIsl` (tier `gate`, shape `projection`)"],
    );
    // Plan step 3.5: recorded with verification off too (before: "`m::fstIsl` (not recorded").
    refused(
        "t2",
        T2,
        Lane::VerifyOff,
        0,
        2,
        &[("clean-below-gate", 2)],
        &["the Clean-origin def `m::fstIsl` (tier `gate`, shape `projection`)"],
    );

    // ── t3: the select row, below `gate` (3.1's reflector covers it; the join's kernel-TV
    // companion requirement keeps it `structural`) ─────────────────────────────────────────
    refused(
        "t3",
        T3,
        Lane::VerifyOn,
        0,
        2,
        &[("clean-below-gate", 2)],
        &["the Clean-origin def `m::cleanMin` (tier `structural`, shape `select`)"],
    );
    // Plan step 3.5: recorded with verification off too (before: "`m::cleanMin` (not recorded").
    refused(
        "t3",
        T3,
        Lane::VerifyOff,
        0,
        2,
        &[("clean-below-gate", 2)],
        &["the Clean-origin def `m::cleanMin` (tier `structural`, shape `select`)"],
    );
    // Plan step 3.4: a below-`gate` row stays `ungated` and is refused by name only where it is
    // reached (its own item and its caller); the Rust-only body beside it completes on the
    // crate-module lane (before: 0/3, the whole module withheld).
    refused(
        "t3r",
        T3R,
        Lane::CrateModule,
        1,
        3,
        &[("clean-below-gate", 2)],
        &[
            "the Clean-origin def `m::cleanMin` (tier `structural`, shape `select`)",
            "reaches the Clean-origin def `m::cleanMin` (tier `structural`, shape `select`)",
        ],
    );
    let text = crate_module_dump("t3r", T3R);
    assert_eq!(body_gate_of(&text, "cleanMin"), Some("ungated"), "{text}");
    assert_eq!(
        body_gate_of(&text, "rust_only"),
        Some("gated \"trust-direct-lane-structural\""),
        "{text}"
    );
    assert!(!text.contains("clean-carrier-gate"), "no `gate` row, no carrier stamp:\n{text}");

    // ── t4: Lean calls Rust. `inc`'s callee `wrapping_add` is upstream (increment 6). ───────
    refused(
        "t4",
        T4,
        Lane::VerifyOn,
        0,
        4,
        &[("clean-below-gate", 2), ("upstream-body", 1), ("instance-assembly", 1)],
        &[
            "the Clean-origin def `twice_inc` (tier `structural`, shape `rust-call-chain`)",
            "reaches the Clean-origin def `twice_inc`",
            // Plan step 3.4: a `structural` row has no ledger entry, so no handoff body.
            LEDGER_ONLY,
        ],
    );
    // Plan step 3.5: recorded with verification off too (before: "`twice_inc` (not recorded").
    refused(
        "t4",
        T4,
        Lane::VerifyOff,
        0,
        4,
        &[("clean-below-gate", 2), ("upstream-body", 1), ("instance-assembly", 1)],
        &[
            "the Clean-origin def `twice_inc` (tier `structural`, shape `rust-call-chain`)",
            "reaches the Clean-origin def `twice_inc`",
            LEDGER_ONLY,
        ],
    );

    // ── t4p: the private Rust callee, reached only through the Clean def ─────────────────
    // The published row names `inc`, so the inventory reaches it and its upstream callee, with
    // verification on and (plan step 3.5) off: before 3.5 no row was recorded with verification
    // off and the inventory walked the def's MIR (plan R-8; before the step-3 review: 0/2,
    // neither row).
    for lane in [Lane::VerifyOn, Lane::VerifyOff] {
        let census = refused(
            "t4p",
            T4P,
            lane,
            0,
            4,
            &[("clean-below-gate", 2), ("upstream-body", 1), ("instance-assembly", 1)],
            &["the Clean-origin def `twice_inc` (tier `structural`, shape `rust-call-chain`)"],
        );
        // Read the census samples, not the whole stderr: the dead-code warning for `inc` (its
        // only caller is the Lean def) quotes its source line, `x.wrapping_add(1)`.
        let samples: Vec<&str> =
            census.lines().filter(|line| line.trim_start().starts_with("e.g.")).collect();
        assert!(
            samples.iter().any(|line| line.contains("3inc")),
            "t4p has a census row for `inc`, reached only through the Lean def:\n{census}"
        );
    }

    // ── t6: the Rust-only control completes on every lane ───────────────────────────────
    for lane in [Lane::VerifyOn, Lane::VerifyOff, Lane::VerifyOffO2] {
        let done = f1("t6", T6, lane).run();
        done.assert_stderr_contains("1/1 reachable function(s) completed");
    }

    // ── 3.3: the neighbour sets, F1 against the MIR lane ────────────────────────────────
    // The LLVM lane walks `cleanWsum`'s MIR and instantiates the `wrapping_add` it calls; F1
    // reads the published row (one `add`, no call). t4's Rust callee is in both. Verification
    // on: the lane on which the row the inventory reads is recorded.
    let mono_at = |name: &str, source: &str, f1_lane: bool, verify_on: bool| {
        let output = if f1_lane {
            let lane = if verify_on { Lane::VerifyOn } else { Lane::VerifyOff };
            f1(name, source, lane).arg("-Zprint-mono-items=yes").run_fail()
        } else {
            let input = format!("{name}.rs");
            rfs::write(&input, source);
            let out = format!("mono-{name}-llvm-{verify_on}");
            rfs::create_dir_all(&out);
            rustc()
                .input(&input)
                .crate_type("lib")
                .edition("2024")
                .arg("-Cpanic=abort")
                .arg(if verify_on { "-Ztrust-verify=on" } else { "-Ztrust-verify=off" })
                .arg("-Zprint-mono-items=yes")
                .out_dir(&out)
                .env_remove(TRUST_NO_VERIFY_ENV)
                .run()
        };
        output.stdout_utf8()
    };
    let mono = |name: &str, source: &str, f1_lane: bool| mono_at(name, source, f1_lane, true);
    let llvm = mono("t1", T1, false);
    let trust = mono("t1", T1, true);
    assert!(llvm.contains("wrapping_add"), "the MIR lane walks cleanWsum's MIR:\n{llvm}");
    assert!(!trust.contains("wrapping_add"), "F1 reads the published row:\n{trust}");
    for item in ["m::cleanWsum", "calls_clean", "rust_only"] {
        assert!(llvm.contains(item) && trust.contains(item), "`{item}` in both:\n{llvm}\n{trust}");
    }
    let llvm = mono("t4", T4, false);
    let trust = mono("t4", T4, true);
    for item in ["twice_inc", "fn inc", "calls_twice"] {
        assert!(llvm.contains(item) && trust.contains(item), "`{item}` in both:\n{llvm}\n{trust}");
    }
    // The private callee is reached on F1 only through `twice_inc`'s published row.
    let llvm = mono("t4p", T4P, false);
    let trust = mono("t4p", T4P, true);
    for item in ["twice_inc", "fn inc", "calls_twice"] {
        assert!(llvm.contains(item) && trust.contains(item), "`{item}` in both:\n{llvm}\n{trust}");
    }
    // With verification off F1 reads the recorded row too (plan step 3.5; before, it walked the
    // def's MIR, and before the step-3 review its inventory lost both): it keeps `inc`, which the
    // row calls, and the `wrapping_add` `inc`'s own MIR calls, as the MIR lane does.
    let llvm = mono_at("t4p", T4P, false, false);
    let trust = mono_at("t4p", T4P, true, false);
    for item in ["twice_inc", "calls_twice", "fn inc", "wrapping_add"] {
        assert!(llvm.contains(item) && trust.contains(item), "`{item}` in both:\n{llvm}\n{trust}");
    }
    // And t1 with verification off: the row, one `add`, not `cleanWsum`'s MIR, whose
    // `wrapping_add` only the MIR lane instantiates (plan step 3.5; before: F1 had it too).
    let llvm = mono_at("t1", T1, false, false);
    let trust = mono_at("t1", T1, true, false);
    assert!(llvm.contains("wrapping_add"), "the MIR lane walks cleanWsum's MIR:\n{llvm}");
    assert!(!trust.contains("wrapping_add"), "3.5: F1 reads the published row:\n{trust}");
    for item in ["m::cleanWsum", "calls_clean", "rust_only"] {
        assert!(llvm.contains(item) && trust.contains(item), "`{item}` in both:\n{llvm}\n{trust}");
    }
}

/// The recipe under libtest as well as compiletest (the frozen-file waiver cites it).
#[test]
fn the_mixed_crate_rows_are_pinned_and_a_clean_row_no_longer_withdraws_the_rust_license() {
    main();
}
