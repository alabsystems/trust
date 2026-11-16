//! Actual MIR references demand Clean gates in check and codegen modes; unused defs do not.
//@ ignore-cross-compile

use std::path::{Path, PathBuf};

use run_make_support::{CompletedProcess, bin_name, cmd, rfs, run, rustc_path, serde_json, target};

struct Case<'a> {
    name: &'a str,
    source: &'a str,
    emit: &'a str,
    opt: u8,
    lane: &'a str,
    cfgs: &'a [&'a str],
}

#[derive(Clone, Copy)]
enum ExpectedOutcome {
    Success,
    RefusalBeforeOutput,
    IncrementalAssertionAfterMetadata,
}

impl Case<'_> {
    fn output(&self) -> PathBuf {
        if self.emit == "metadata" {
            format!("{}.rmeta", self.name).into()
        } else {
            bin_name(self.name).into()
        }
    }

    fn dump(&self) -> PathBuf {
        format!("ir-{}", self.name).into()
    }
}

fn contains_message(value: &serde_json::Value, expected: &str) -> bool {
    value["message"].as_str().is_some_and(|message| message.contains(expected))
        || value["children"]
            .as_array()
            .is_some_and(|children| children.iter().any(|child| contains_message(child, expected)))
}

fn errors(output: &CompletedProcess) -> Vec<serde_json::Value> {
    output
        .stderr_utf8()
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .filter(|row: &serde_json::Value| {
            row["$message_type"] == "diagnostic" && row["level"] == "error"
        })
        .collect()
}

fn compile(
    trustc: &Path,
    case: &Case<'_>,
    expected: ExpectedOutcome,
    extra: &[String],
    receipt: &str,
) -> CompletedProcess {
    assert!(!case.output().exists(), "stale output for {receipt}");
    let mut compiler = cmd(trustc);
    compiler.arg(case.source).args([
        "--edition=2021",
        "--crate-type=bin",
        "--error-format=json",
        "-Ztrust-verify=off",
        "-Ztrust-policy=strict",
    ]);
    compiler
        .arg(format!("--crate-name={}", case.name))
        .arg(format!("--emit={}", case.emit))
        .arg(format!("-Copt-level={}", case.opt))
        .arg(format!("-Ztrust-ir-lower={}", case.lane))
        .arg("-o")
        .arg(case.output());
    if case.lane == "on" {
        compiler.arg(format!("-Ztrust-dump=ir:{}", case.dump().display()));
    }
    for cfg in case.cfgs {
        compiler.args(["--cfg", cfg]);
    }
    compiler.args(extra);
    let output = if matches!(expected, ExpectedOutcome::Success) {
        compiler.run()
    } else {
        compiler.run_fail()
    };
    rfs::write(format!("{receipt}.stdout"), output.stdout());
    rfs::write(format!("{receipt}.stderr"), output.stderr());
    assert!(!output.stderr_utf8().contains("internal compiler error"));
    assert!(!output.stderr_utf8().contains("RustAbiVararg"));
    if matches!(expected, ExpectedOutcome::Success) {
        assert!(case.output().exists());
        assert!(errors(&output).is_empty());
        if case.emit == "link" {
            run(case.name);
        }
        if case.lane == "on" {
            let coverage: serde_json::Value = serde_json::from_slice(&rfs::read(
                case.dump().join(format!("{}.coverage.json", case.name)),
            ))
            .unwrap();
            assert_eq!(coverage["clean_origin"]["recorded"], false);
        }
    } else {
        output.assert_exit_code(1);
        match expected {
            ExpectedOutcome::RefusalBeforeOutput => assert!(!case.output().exists()),
            ExpectedOutcome::IncrementalAssertionAfterMetadata => {
                // Trust: rustc_clean assertions run in tcx.finish(), after metadata
                // emission. A bin's metadata placeholder is empty; this late test
                // assertion is distinct from every semantic refusal above.
                assert_eq!(case.emit, "metadata");
                assert_eq!(case.lane, "off");
                assert_eq!(rfs::read(case.output()), Vec::<u8>::new());
            }
            ExpectedOutcome::Success => unreachable!(),
        }
        for suffix in ["coverage.json", "trust-ir.txt"] {
            assert!(!case.dump().join(format!("{}.{suffix}", case.name)).exists());
        }
    }
    output
}

fn pure_refusal(output: &CompletedProcess) {
    let diagnostics = errors(output);
    let pure = "may only call a PURE Rust fn";
    assert!(
        diagnostics.iter().any(|row| contains_message(row, pure)),
        "expected actual PURE refusal, including structured child notes: {}",
        output.stderr_utf8()
    );
    assert!(diagnostics.iter().all(|row| {
        contains_message(row, pure)
            || row["message"].as_str().is_some_and(|message| message.starts_with("aborting due to"))
    }));
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    // Keep the full ordinary matrix: metadata must agree with native codegen,
    // and neither an IR flag nor an eager whole-registry walk may set policy.
    for emit in ["metadata", "link"] {
        for opt in [0, 3] {
            for lane in ["off", "on"] {
                for (shape, cfgs, succeeds) in [
                    ("unused", &[][..], true),
                    ("call", &["call"][..], false),
                    ("address", &["address"][..], false),
                    ("frame", &["call", "pure"][..], true),
                ] {
                    let name = format!("clean_gate_{emit}_{opt}_{lane}_{shape}");
                    let case = Case { name: &name, source: "main.rs", emit, opt, lane, cfgs };
                    let expected = if succeeds {
                        ExpectedOutcome::Success
                    } else {
                        ExpectedOutcome::RefusalBeforeOutput
                    };
                    let output = compile(&trustc, &case, expected, &[], &name);
                    if !succeeds {
                        pure_refusal(&output);
                    }
                }
            }
        }
    }

    let type_only = Case {
        name: "clean_gate_type_only",
        source: "main.rs",
        emit: "metadata",
        opt: 0,
        lane: "off",
        cfgs: &["type_only"],
    };
    compile(&trustc, &type_only, ExpectedOutcome::Success, &[], type_only.name);

    // A real frontend error must win before any referenced Clean body is
    // demanded. Reaching optimized MIR here can replace E0425 with an ICE.
    let frontend = Case {
        name: "clean_gate_frontend_error",
        source: "main.rs",
        emit: "metadata",
        opt: 0,
        lane: "off",
        cfgs: &["call", "frontend_error"],
    };
    let output =
        compile(&trustc, &frontend, ExpectedOutcome::RefusalBeforeOutput, &[], frontend.name);
    let diagnostics = errors(&output);
    let missing_type: Vec<_> =
        diagnostics.iter().filter(|row| row["code"]["code"] == "E0425").collect();
    assert_eq!(missing_type.len(), 1);
    assert_eq!(missing_type[0]["message"], "cannot find type `MissingType` in this scope");
    assert!(missing_type[0]["spans"].as_array().unwrap().iter().any(|span| {
        span["is_primary"] == true
            && span["file_name"].as_str().is_some_and(|name| name.ends_with("main.rs"))
    }));
    assert!(diagnostics.iter().all(|row| {
        row["code"]["code"] == "E0425"
            || row["message"].as_str().is_some_and(|message| message.starts_with("aborting due to"))
    }));
    assert!(!diagnostics.iter().any(|row| contains_message(row, "may only call a PURE Rust fn")));

    // Discriminating check-mode cases, without repeating every optimization/IR
    // combination. The pure twins also expose malformed custom MIR/asm fixtures.
    let mut forms = vec![
        ("custom.rs", "custom_call"),
        ("custom.rs", "custom_address"),
        ("symbols.rs", "static_address"),
    ];
    if target().starts_with("x86_64-") || target().starts_with("aarch64-") {
        forms.extend([("symbols.rs", "inline_symbol"), ("symbols.rs", "global_symbol")]);
    }
    for (source, shape) in forms {
        for pure in [false, true] {
            let name = format!("clean_gate_metadata_{shape}_{pure}");
            let cfgs = if pure { vec![shape, "pure"] } else { vec![shape] };
            let case =
                Case { name: &name, source, emit: "metadata", opt: 0, lane: "off", cfgs: &cfgs };
            let expected =
                if pure { ExpectedOutcome::Success } else { ExpectedOutcome::RefusalBeforeOutput };
            let output = compile(&trustc, &case, expected, &[], &name);
            if !pure {
                pure_refusal(&output);
            }
        }
    }

    // This DefId-keyed assertion names the body carrying a nonempty Clean
    // reference set, rather than accepting an unrelated query-kind disk load.
    let cache = Case {
        name: "clean_gate_cached",
        source: "cache.rs",
        emit: "metadata",
        opt: 0,
        lane: "off",
        cfgs: &[],
    };
    for phase in ["cold", "warm", "fresh_negative"] {
        let directory = if phase == "fresh_negative" { "fresh-cache" } else { "warm-cache" };
        let mut extra = vec![
            format!("-Cincremental={directory}"),
            "-Zquery-dep-graph".into(),
            "-Zincremental-verify-ich".into(),
            format!(
                "-Zassert-incr-state={}",
                if phase == "warm" { "loaded" } else { "not-loaded" }
            ),
        ];
        if phase != "cold" {
            extra.extend(["--cfg".into(), "warm".into()]);
        }
        let succeeds = phase != "fresh_negative";
        let expected = if succeeds {
            ExpectedOutcome::Success
        } else {
            ExpectedOutcome::IncrementalAssertionAfterMetadata
        };
        let output = compile(&trustc, &cache, expected, &extra, &format!("cache_{phase}"));
        if succeeds {
            rfs::rename(cache.output(), format!("cache_{phase}.rmeta"));
        } else {
            let diagnostics = errors(&output);
            let expected = "`trust_clean_origin_references(referenced)` should have been loaded from disk but it was not";
            assert_eq!(
                diagnostics.iter().map(|row| row["message"].as_str().unwrap()).collect::<Vec<_>>(),
                // The 2026-09-17 pin counted one warning; the 1.101 stage 1 emits none here.
                vec![expected, "aborting due to 1 previous error"]
            );
            assert!(diagnostics[0]["spans"].as_array().unwrap().iter().any(|span| {
                span["is_primary"] == true
                    && span["file_name"].as_str().is_some_and(|name| name.ends_with("cache.rs"))
            }));
            rfs::rename(cache.output(), format!("cache_{phase}.rmeta"));
        }
    }

    // One path, crate name, output path, command line and cache across edits.
    // First cache a real pure reference, then remove it while making its callee
    // impure: stale nonempty demand must not reject the now-unused definition.
    // Adding the reference must refuse; removing it again must recover.
    let original = rfs::read_to_string("transition.rs");
    let impure = original.replace("let observed = a;", "let observed = unsafe { STATE };");
    let unused = impure.replace("std::hint::black_box(applyRead as fn(u64) -> u64);", "");
    assert_ne!(original, impure);
    assert_ne!(impure, unused);
    let transition = Case {
        name: "clean_gate_transition",
        source: "transition-live.rs",
        emit: "metadata",
        opt: 0,
        lane: "off",
        cfgs: &[],
    };
    for (phase, source, succeeds) in [
        ("reference_pure", &original, true),
        ("removed_impure", &unused, true),
        ("added_impure", &impure, false),
        ("removed_again", &unused, true),
    ] {
        rfs::write(transition.source, source);
        let output = compile(
            &trustc,
            &transition,
            if succeeds { ExpectedOutcome::Success } else { ExpectedOutcome::RefusalBeforeOutput },
            &["-Cincremental=transition-cache".into()],
            phase,
        );
        if succeeds {
            rfs::rename(transition.output(), format!("{phase}.rmeta"));
        } else {
            pure_refusal(&output);
        }
    }
}
