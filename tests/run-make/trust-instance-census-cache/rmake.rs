//! Cold and disk-loaded collector results retain the same typed dependency census.
//! The opaque query-kind assertion proves at least one items_of_instance disk load,
//! not that every individual owner was deserialized.
//@ ignore-cross-compile

use std::path::{Path, PathBuf};

use run_make_support::{
    CompletedProcess, bin_name, cmd, cwd, python_command, rfs, run, rustc_path, serde_json,
    source_root,
};

fn compile(trustc: &Path, source: &Path, scratch: &Path, opt: u8, phase: &str) -> CompletedProcess {
    let mut compiler = cmd(trustc);
    compiler.current_dir(scratch).arg(source).args([
        "--crate-name=collector_cache_probe",
        "--crate-type=bin",
        "--edition=2024",
        "--error-format=json",
        "-Cdebuginfo=0",
        "-Cdebug-assertions=yes",
        "-Ccodegen-units=1",
        "-Zquery-dep-graph",
        "-Zincremental-verify-ich",
        "-Zincremental-info",
        "-Ztrust-policy=strict",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower=off",
        "-Zthreads=1",
        "-Zchecksum-hash-algorithm=sha256",
    ]);
    compiler
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Cincremental={}", scratch.join("cache").display()))
        .arg(format!(
            "-Zassert-incr-state={}",
            if phase == "warm" { "loaded" } else { "not-loaded" }
        ))
        .arg(format!("-Ztrust-instance-census={}", scratch.join("census.jsonl").display()))
        .arg(format!(
            "--emit=link={},mir={}",
            scratch.join(bin_name("probe")).display(),
            scratch.join("probe.mir").display()
        ));
    if phase != "cold" {
        compiler.args(["--cfg", "warm"]);
    }
    if phase == "fresh-negative" { compiler.run_fail() } else { compiler.run() }
}

fn main() {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    let source = cwd().join("main.rs");

    for opt in [0, 3] {
        let scratch = cwd().join(format!("opt{opt}-scratch"));
        rfs::create_dir(&scratch);
        for phase in ["cold", "warm"] {
            let folder = cwd().join(format!("opt{opt}-{phase}"));
            rfs::create_dir(&folder);
            let output = compile(&trustc, &source, &scratch, opt, phase);
            rfs::write(folder.join("compiler.stdout"), output.stdout());
            rfs::write(folder.join("compiler.stderr"), output.stderr());
            for name in [bin_name("probe"), "probe.mir".into(), "census.jsonl".into()] {
                rfs::copy(scratch.join(&name), folder.join(&name));
                assert_eq!(rfs::read(scratch.join(&name)), rfs::read(folder.join(&name)));
            }
            // The report pathname is tracked compiler input: preserve its cold
            // bytes, then remove only this test's publication target before warm.
            rfs::remove_file(scratch.join("census.jsonl"));
            let executed = run(folder.join(bin_name("probe")).to_str().unwrap());
            assert_eq!(executed.stdout_utf8(), "cache=11,20,13,210,37\n");
            assert_eq!(executed.stderr_utf8(), "");
            rfs::write(folder.join("runtime.stdout"), executed.stdout());
        }

        let fresh = cwd().join(format!("opt{opt}-fresh-negative"));
        rfs::create_dir(&fresh);
        let failure = compile(&trustc, &source, &fresh, opt, "fresh-negative");
        failure.assert_exit_code(1);
        rfs::write(fresh.join("compiler.stdout"), failure.stdout());
        rfs::write(fresh.join("compiler.stderr"), failure.stderr());
        let diagnostics: Vec<serde_json::Value> = failure
            .stderr_utf8()
            .lines()
            .filter_map(|line| serde_json::from_str(line).ok())
            .filter(|row: &serde_json::Value| {
                row["$message_type"] == "diagnostic" && row["level"] == "error"
            })
            .collect();
        let message = "`items_of_instance` should have been loaded from disk but it was not";
        let messages: Vec<_> =
            diagnostics.iter().map(|row| row["message"].as_str().unwrap()).collect();
        assert_eq!(messages, vec![message, "aborting due to 1 previous error"]);
        let matches: Vec<_> = diagnostics.iter().filter(|row| row["message"] == message).collect();
        assert_eq!(
            matches.len(),
            1,
            "expected actual cache-load refusal: {}",
            failure.stderr_utf8()
        );
        assert!(matches[0]["spans"].as_array().unwrap().iter().any(|span| {
            span["is_primary"] == true
                && span["file_name"] == source.to_str().unwrap()
                && span["line_start"] == 6
        }));
        assert!(!failure.stderr_utf8().contains("internal compiler error"));
        assert!(!fresh.join(bin_name("probe")).exists());

        python_command()
            .arg("-B")
            .arg("validate.py")
            .arg(source_root())
            .arg(&source)
            .arg(opt.to_string())
            .arg(cwd().join(format!("opt{opt}-cold/census.jsonl")))
            .arg(cwd().join(format!("opt{opt}-warm/census.jsonl")))
            .run();
    }
}
