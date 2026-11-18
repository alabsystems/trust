//! Trust (DC-18a): `-Ztrust-path-free` refuses crate metadata that would carry an
//! absolute host path no `--remap-path-prefix` rule rewrote off this host, and changes
//! nothing else.
//!
//! A library compile under the option that would write such a path ends with exactly one
//! error, whose note is a `trust-path-free-v1` JSON record naming the path and where it
//! came from, and leaves no rlib or rmeta behind, `-Csave-temps` or not. Each origin is a
//! leg:
//!
//!  * the working directory a relative source-file name was resolved against (no rule; a
//!    rule under `--remap-path-scope=macro`, which keeps the local name in metadata; and a
//!    rule that rewrites it into another spelling of a host directory);
//!  * a source-file name: an absolute crate root and its absolute `#[path]` module, outside
//!    every rule while the working directory is remapped, which `to_real_filename` marks as
//!    remapped anyway, so a check on remap scopes would pass them
//!    (`remap_scopes_are_not_evidence_of_a_rewrite`, the unit test, pins that premise);
//!  * an `env!` and an `option_env!` whose values are host paths, one whose value only
//!    holds one (`--flag=/x`), and a proc macro's tracked read;
//!  * a native library named by an absolute path;
//!  * a value written into the metadata under a host directory, from nowhere the checks
//!    above look: a static copied from a dependency compiled without the option, and a
//!    string a proc macro made from an untracked environment read.
//!
//! Every refused leg has a passing twin that differs only in what the leg names (the rule
//! added, the value made relative), and its rlib and rmeta are byte-for-byte those of the
//! same compile without the option, since the option rewrites nothing. Without the option
//! each refused leg compiles as it does today, with the host path written into the rmeta
//! as it is. Incremental reuse cannot carry an rmeta an option-less session encoded into a
//! session that has the option.

//@ ignore-cross-compile
//@ needs-crate-type: proc-macro
//@ ignore-musl (FIXME: can't find `-lunwind`)

use std::path::Path;

use run_make_support::serde_json::{self, Value};
use run_make_support::{bstr::ByteSlice, cwd, dynamic_lib_name, rfs, rustc};

const RECORD_PREFIX: &str = "trust-path-free-v1 ";

const PLAIN: &str = "pub fn answer() -> u32 { 42 }\n";

const ENV: &str = r#"
pub const DIR: &str = env!("TRUST_PATH_FREE_DIR");
pub const OPT: Option<&str> = option_env!("TRUST_PATH_FREE_OPT");
pub fn dir() -> &'static str { DIR }
"#;

/// A dependency compiled without the option, whose constant holds an environment value.
const PATHDEP: &str = "pub const DIR: &str = env!(\"TRUST_PATH_FREE_DIR\");\n";

/// A static that copies the dependency's constant: no read and no file name of this
/// compile carries the path, only the value.
const FROM_DEP: &str = "extern crate pathdep;\npub static DIR: &str = pathdep::DIR;\n";

const PM: &str = r#"
#![feature(proc_macro_tracked_env)]
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro]
pub fn untracked(_: TokenStream) -> TokenStream {
    format!("{:?}", std::env::var("TRUST_PATH_FREE_UNTRACKED").unwrap()).parse().unwrap()
}

#[proc_macro]
pub fn tracked(_: TokenStream) -> TokenStream {
    let value = proc_macro::tracked::env_var("TRUST_PATH_FREE_TRACKED").unwrap();
    format!("{value:?}").parse().unwrap()
}
"#;

const FROM_PM_UNTRACKED: &str = "extern crate pm;\npub static S: &str = pm::untracked!();\n";
const FROM_PM_TRACKED: &str = "extern crate pm;\npub static S: &str = pm::tracked!();\n";

const ENV_VARS: [&str; 4] = [
    "TRUST_PATH_FREE_DIR",
    "TRUST_PATH_FREE_OPT",
    "TRUST_PATH_FREE_UNTRACKED",
    "TRUST_PATH_FREE_TRACKED",
];

/// A dependency, compiled without the option into `deps/`.
fn dependency(input: &str, name: &str, crate_type: &str, env: &[(&str, &str)]) {
    let mut rustc = rustc();
    rustc
        .input(input)
        .crate_name(name)
        .crate_type(crate_type)
        .out_dir(cwd().join("deps"))
        .arg("-Ztrust-verify=off");
    for var in ENV_VARS {
        rustc.env_remove(var);
    }
    for (key, value) in env {
        rustc.env(key, value);
    }
    rustc.run();
}

/// One compile of `input`, from the directory `dir`, as an rlib with its rmeta into
/// `out/` (emptied first).
fn compile_in(
    dir: &Path,
    input: &str,
    args: &[&str],
    env: &[(&str, &str)],
) -> run_make_support::CompletedProcess {
    if Path::new("out").exists() {
        rfs::remove_dir_all("out");
    }
    rfs::create_dir("out");
    let mut rustc = rustc();
    rustc
        .current_dir(dir)
        .input(input)
        .crate_name("subject")
        .crate_type("rlib")
        .emit("metadata,link")
        .out_dir(cwd().join("out"))
        .error_format("json")
        .arg("-Ztrust-verify=off")
        .args(args);
    for var in ENV_VARS {
        rustc.env_remove(var);
    }
    for (key, value) in env {
        rustc.env(key, value);
    }
    rustc.run_unchecked()
}

fn compile(input: &str, args: &[&str], env: &[(&str, &str)]) -> run_make_support::CompletedProcess {
    compile_in(&cwd(), input, args, env)
}

fn outputs() -> Vec<String> {
    let mut names: Vec<String> = rfs::read_dir("out")
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// The rlib's and the rmeta's bytes after a compile that must succeed.
fn artifacts(output: &run_make_support::CompletedProcess, leg: &str) -> (Vec<u8>, Vec<u8>) {
    assert!(output.status().success(), "{leg}: compile failed:\n{}", output.stderr_utf8());
    assert!(
        !output.stderr_utf8().contains(RECORD_PREFIX),
        "{leg}: a passing compile printed a refusal:\n{}",
        output.stderr_utf8()
    );
    (rfs::read("out/libsubject.rlib"), rfs::read("out/libsubject.rmeta"))
}

/// The one refusal of a compile that must fail: its record, after checking that it is
/// the only error, that it says what the record says, and that nothing was written.
fn refusal(output: &run_make_support::CompletedProcess, leg: &str) -> Value {
    assert!(!output.status().success(), "{leg}: compile was not refused");
    let stderr = output.stderr_utf8();
    let errors: Vec<Value> = stderr
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|diag| diag["$message_type"] == "diagnostic" && diag["level"] == "error")
        .filter(|diag| !diag["message"].as_str().unwrap().starts_with("aborting due to"))
        .collect();
    assert_eq!(errors.len(), 1, "{leg}: expected one error:\n{stderr}");
    let error = &errors[0];
    let message = error["message"].as_str().unwrap();
    let records: Vec<&str> = error["children"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|child| child["level"] == "note")
        .filter_map(|child| child["message"].as_str()?.strip_prefix(RECORD_PREFIX))
        .collect();
    assert_eq!(records.len(), 1, "{leg}: expected one record:\n{stderr}");
    let record: Value = serde_json::from_str(records[0]).unwrap();
    let path = record["path"].as_str().unwrap();
    assert!(Path::new(path).is_absolute(), "{leg}: {record}");
    assert!(message.contains(&format!("`{path}`")), "{leg}: message does not name {path}");
    assert_eq!(outputs(), Vec::<String>::new(), "{leg}: a refused compile left outputs");
    record
}

fn assert_record(record: &Value, origin: &str, var: Option<&str>, path: &Path, further: u64) {
    assert_eq!(record["origin"], origin, "{record}");
    assert_eq!(record["var"].as_str(), var, "{record}");
    assert_eq!(record["path"].as_str(), path.to_str(), "{record}");
    assert_eq!(record["further"], further, "{record}");
}

/// A `metadata` refusal: the value found under the host directory `prefix` starts with
/// `path` (what follows it in the rmeta is whatever the encoder wrote next).
fn assert_metadata_record(record: &Value, prefix: &Path, path: &str) {
    assert_eq!(record["origin"], "metadata", "{record}");
    assert_eq!(record["output"], "full.rmeta", "{record}");
    assert_eq!(record["prefix"].as_str(), prefix.to_str(), "{record}");
    assert!(record["path"].as_str().unwrap().starts_with(path), "{record}");
}

/// Today's behaviour without the option: the leg compiles, its rmeta carries `host`
/// as it is, and `-Ztrust-path-free=no` writes the same bytes.
fn unchanged_without_option_in(
    dir: &Path,
    input: &str,
    args: &[&str],
    env: &[(&str, &str)],
    host: &Path,
    leg: &str,
) {
    let (rlib, rmeta) = artifacts(&compile_in(dir, input, args, env), leg);
    assert!(
        rmeta.find(host.to_str().unwrap().as_bytes()).is_some(),
        "{leg}: the option-less rmeta no longer carries {}",
        host.display()
    );
    let explicit_no: Vec<&str> = args.iter().copied().chain(["-Ztrust-path-free=no"]).collect();
    let (no_rlib, no_rmeta) = artifacts(&compile_in(dir, input, &explicit_no, env), leg);
    assert!(rlib == no_rlib && rmeta == no_rmeta, "{leg}: `=no` changed the bytes");
}

fn unchanged_without_option(
    input: &str,
    args: &[&str],
    env: &[(&str, &str)],
    host: &Path,
    leg: &str,
) {
    unchanged_without_option_in(&cwd(), input, args, env, host, leg)
}

/// A passing leg: it compiles under the option to exactly the bytes it has without it.
fn passes_unchanged_in(dir: &Path, input: &str, args: &[&str], env: &[(&str, &str)], leg: &str) {
    let without = artifacts(&compile_in(dir, input, args, env), leg);
    let with: Vec<&str> = args.iter().copied().chain(["-Ztrust-path-free"]).collect();
    let with = artifacts(&compile_in(dir, input, &with, env), leg);
    assert!(without == with, "{leg}: the option changed the rlib or the rmeta");
}

fn passes_unchanged(input: &str, args: &[&str], env: &[(&str, &str)], leg: &str) {
    passes_unchanged_in(&cwd(), input, args, env, leg)
}

fn main() {
    let work = cwd();
    let work_str = work.to_str().unwrap().to_owned();
    let remap_work = format!("--remap-path-prefix={work_str}=/remapped");

    rfs::write("plain.rs", PLAIN);
    rfs::write("env.rs", ENV);
    rfs::create_dir("elsewhere");
    let module = work.join("elsewhere/module.rs");
    rfs::write(&module, "pub fn inner() -> u32 { 7 }\n");
    rfs::write(
        "absolute.rs",
        format!(
            "#[path = {:?}]\npub mod module;\npub fn outer() -> u32 {{ module::inner() }}\n",
            module
        ),
    );

    // (1) The working directory: no rule.
    let record = refusal(&compile("plain.rs", &["-Ztrust-path-free"], &[]), "cwd");
    assert_record(&record, "working-directory", None, &work, 0);
    unchanged_without_option("plain.rs", &[], &[], &work, "cwd");
    passes_unchanged("plain.rs", &[&remap_work], &[], "cwd remapped");
    // Remapped only in the macro scope, the local name stays in the metadata.
    let record = refusal(
        &compile("plain.rs", &[&remap_work, "--remap-path-scope=macro", "-Ztrust-path-free"], &[]),
        "cwd macro scope",
    );
    assert_record(&record, "working-directory", None, &work, 0);

    // (2) A source-file name outside every rule while the working directory, `wd/`, is
    // remapped: the crate root `absolute.rs` and its `#[path]` module both sit above it.
    rfs::create_dir("wd");
    let wd = work.join("wd");
    let remap_wd = format!("--remap-path-prefix={}=/remapped", wd.display());
    let root = work.join("absolute.rs");
    let root_str = root.to_str().unwrap();
    let record =
        refusal(&compile_in(&wd, root_str, &[&remap_wd, "-Ztrust-path-free"], &[]), "source file");
    // Both names are refused; which one the encoder meets first is its span order.
    let first = if record["path"].as_str() == root.to_str() { &root } else { &module };
    assert_record(&record, "source-file", None, first, 1);
    unchanged_without_option_in(&wd, root_str, &[&remap_wd], &[], &module, "source file");
    // Twin: a later rule for the whole test directory rewrites both files.
    passes_unchanged_in(&wd, root_str, &[&remap_wd, &remap_work], &[], "source file remapped");

    // (3) `env!` and `option_env!` values.
    let host =
        [("TRUST_PATH_FREE_DIR", work_str.as_str()), ("TRUST_PATH_FREE_OPT", work_str.as_str())];
    let record = refusal(&compile("env.rs", &[&remap_work, "-Ztrust-path-free"], &host), "env");
    assert_record(&record, "env", Some("TRUST_PATH_FREE_DIR"), &work, 1);
    let option_only =
        [("TRUST_PATH_FREE_DIR", "relative/dir"), ("TRUST_PATH_FREE_OPT", work_str.as_str())];
    let record = refusal(
        &compile("env.rs", &[&remap_work, "-Ztrust-path-free"], &option_only),
        "option_env",
    );
    assert_record(&record, "env", Some("TRUST_PATH_FREE_OPT"), &work, 0);
    unchanged_without_option("env.rs", &[&remap_work], &host, &work, "env");
    passes_unchanged(
        "env.rs",
        &[&remap_work],
        &[("TRUST_PATH_FREE_DIR", "relative/dir"), ("TRUST_PATH_FREE_OPT", "relative/opt")],
        "env relative",
    );

    // A rule that rewrites the working directory into another spelling of it: the name
    // changed, but its root is a directory of this host.
    let respelled = work.join("..").join(work.file_name().unwrap());
    let remap_respelled = format!("--remap-path-prefix={work_str}={}", respelled.display());
    let record =
        refusal(&compile("plain.rs", &[&remap_respelled, "-Ztrust-path-free"], &[]), "respelled");
    assert_record(&record, "working-directory", None, &respelled, 0);
    assert_eq!(record["file"], "plain.rs", "{record}");
    // `-Csave-temps` keeps no metadata a refusal stopped.
    let record =
        refusal(&compile("plain.rs", &["-Csave-temps", "-Ztrust-path-free"], &[]), "save-temps");
    assert_record(&record, "working-directory", None, &work, 0);

    // A value that holds a host path without being one, and one under `-Csave-temps`.
    let embedded = [("TRUST_PATH_FREE_DIR", "--flag=/opt/trust-path-free-nowhere/x")];
    let record = refusal(
        &compile("env.rs", &[&remap_work, "-Csave-temps", "-Ztrust-path-free"], &embedded),
        "env embedded",
    );
    assert_record(
        &record,
        "env",
        Some("TRUST_PATH_FREE_DIR"),
        Path::new("/opt/trust-path-free-nowhere/x"),
        0,
    );
    assert_eq!(record["read"], "env!", "{record}");

    // (5) A native library named by an absolute path.
    let record = refusal(
        &compile(
            "plain.rs",
            &[&remap_work, "-l", "dylib:+verbatim=/opt/trust-path-free-nowhere/libx.dylib", "-Ztrust-path-free"],
            &[],
        ),
        "native library",
    );
    assert_record(
        &record,
        "native-library",
        None,
        Path::new("/opt/trust-path-free-nowhere/libx.dylib"),
        0,
    );
    passes_unchanged("plain.rs", &[&remap_work, "-l", "dylib=x"], &[], "native library by name");

    // (6) Values: a static copied from a dependency compiled without the option.
    rfs::create_dir("deps");
    let deps = work.join("deps");
    let search = format!("-L{}", deps.display());
    rfs::write("pathdep.rs", PATHDEP);
    rfs::write("from_dep.rs", FROM_DEP);
    let dep_value = format!("{work_str}/dep-data");
    dependency("pathdep.rs", "pathdep", "rlib", &[("TRUST_PATH_FREE_DIR", &dep_value)]);
    let record = refusal(
        &compile("from_dep.rs", &[&remap_work, &search, "-Ztrust-path-free"], &[]),
        "static from a dependency",
    );
    assert_metadata_record(&record, &work, &dep_value);
    let record = refusal(
        &compile("from_dep.rs", &[&remap_work, &search, "-Csave-temps", "-Ztrust-path-free"], &[]),
        "static from a dependency, save-temps",
    );
    assert_metadata_record(&record, &work, &dep_value);
    unchanged_without_option(
        "from_dep.rs",
        &[&remap_work, &search],
        &[],
        Path::new(&dep_value),
        "static from a dependency",
    );
    dependency("pathdep.rs", "pathdep", "rlib", &[("TRUST_PATH_FREE_DIR", "relative/dir")]);
    passes_unchanged("from_dep.rs", &[&remap_work, &search], &[], "static from a dependency");

    // A proc macro's output: from an untracked read, found in the encoded value; from a
    // tracked read, refused as the read.
    rfs::write("pm.rs", PM);
    rfs::write("from_pm_untracked.rs", FROM_PM_UNTRACKED);
    rfs::write("from_pm_tracked.rs", FROM_PM_TRACKED);
    dependency("pm.rs", "pm", "proc-macro", &[]);
    assert!(deps.join(dynamic_lib_name("pm")).exists());
    let untracked_value = format!("{work_str}/untracked");
    let record = refusal(
        &compile(
            "from_pm_untracked.rs",
            &[&remap_work, &search, "-Ztrust-path-free"],
            &[("TRUST_PATH_FREE_UNTRACKED", &untracked_value)],
        ),
        "proc macro untracked",
    );
    assert_metadata_record(&record, &work, &untracked_value);
    passes_unchanged(
        "from_pm_untracked.rs",
        &[&remap_work, &search],
        &[("TRUST_PATH_FREE_UNTRACKED", "relative/dir")],
        "proc macro untracked",
    );
    let tracked_value = format!("{work_str}/tracked");
    let record = refusal(
        &compile(
            "from_pm_tracked.rs",
            &[&remap_work, &search, "-Ztrust-path-free"],
            &[("TRUST_PATH_FREE_TRACKED", &tracked_value)],
        ),
        "proc macro tracked",
    );
    assert_record(&record, "env", Some("TRUST_PATH_FREE_TRACKED"), Path::new(&tracked_value), 0);
    assert_eq!(record["read"], "tracked", "{record}");
    passes_unchanged(
        "from_pm_tracked.rs",
        &[&remap_work, &search],
        &[("TRUST_PATH_FREE_TRACKED", "relative/dir")],
        "proc macro tracked",
    );

    // (4) Incremental reuse: an rmeta an option-less session encoded is not reused.
    let incremental = format!("-Cincremental={}", work.join("incr").display());
    let (_, rmeta) = artifacts(&compile("plain.rs", &[&incremental], &[]), "incremental");
    assert!(rmeta.find(work_str.as_bytes()).is_some());
    let record =
        refusal(&compile("plain.rs", &[&incremental, "-Ztrust-path-free"], &[]), "incremental");
    assert_record(&record, "working-directory", None, &work, 0);
}
