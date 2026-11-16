// Trust (TG4): measure the ordinary compiler checking path itself. Enabling
// the separate kernel census would change its recipe and disable the handoff.
// JSON time-pass events count work, never impose a latency/speedup threshold.
// Text output suppresses short passes that leave RSS unchanged.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off

use run_make_support::{bin_name, rfs, run, rustc, serde_json};

const CHECK: &str = "trust_clean_environment_resolver_check";
const PUBLISH: &str = "trust_clean_environment_resolver_publish";
const HIT: &str = "trust_clean_environment_cache_hit";
const RECHECK: &str = "trust_clean_environment_recheck";
const HIR_FINISH: &str = "trust_clean_environment_hir_finish";
const HIR_RECHECK: &str = "trust_clean_environment_hir_recheck";

fn count(stderr: &str, event: &str) -> usize {
    stderr
        .lines()
        .filter_map(|line| line.strip_prefix("time: "))
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("JSON time-pass event"))
        .filter(|row| row["pass"] == event)
        .count()
}

fn assert_proof_type_error(stderr: &str) {
    assert!(
        stderr.lines().any(|line| {
            line.starts_with("error:")
                && (line.to_ascii_lowercase().contains("type mismatch")
                    || line.contains("TypeMismatch"))
        }),
        "expected an actual proof type error, not a parser/transport/fallback failure: {stderr}",
    );
}

fn compile(input: &str, output: &str, census: bool, rejected: bool) -> String {
    let mut command = rustc();
    command
        .input(input)
        .output(bin_name(output))
        .arg("-Ztrust-verify=off")
        .arg("-Ztime-passes")
        .arg("-Ztime-passes-format=json")
        .env_remove("TRUST_NO_VERIFY");
    if census {
        command.arg("-Ztrust-lean-census=census.jsonl").arg("-Zchecksum-hash-algorithm=sha256");
    }
    let result = if rejected { command.run_fail() } else { command.run() };
    let stderr = result.stderr_utf8();
    rfs::write(format!("{output}.stderr"), &stderr);
    stderr
}

fn main() {
    let ordinary = compile("subject.rs", "ordinary", false, false);
    assert_eq!(count(&ordinary, CHECK), 1, "{ordinary}");
    assert_eq!(count(&ordinary, PUBLISH), 1, "{ordinary}");
    assert!(count(&ordinary, HIT) > 0, "{ordinary}");
    assert_eq!(count(&ordinary, RECHECK), 0, "{ordinary}");
    assert_eq!(count(&ordinary, HIR_FINISH), 1, "{ordinary}");
    assert_eq!(count(&ordinary, HIR_RECHECK), 0, "{ordinary}");
    run("ordinary");

    // Model checking finishes on the retained original declaration delta.
    // Its mutant must fail at HIR even though resolver declaration checking
    // accepted both versions. Losing the baseline would silently skip it.
    let model = compile("model.rs", "model", false, false);
    assert_eq!(count(&model, CHECK), 1, "{model}");
    assert_eq!(count(&model, PUBLISH), 1, "{model}");
    assert_eq!(count(&model, HIR_FINISH), 1, "{model}");
    assert_eq!(count(&model, HIR_RECHECK), 0, "{model}");
    run("model");
    let model_source = rfs::read_to_string("model.rs");
    let bad_model_source = model_source.replace("ScalarExpr.le X One", "ScalarExpr.le X Zero");
    assert_ne!(bad_model_source, model_source);
    rfs::write("bad_model.rs", bad_model_source);
    let bad_model = compile("bad_model.rs", "bad_model", false, true);
    assert_eq!(count(&bad_model, PUBLISH), 1, "{bad_model}");
    assert_eq!(count(&bad_model, HIR_FINISH), 1, "{bad_model}");
    assert_eq!(count(&bad_model, HIR_RECHECK), 0, "{bad_model}");
    assert!(bad_model.contains("Tiny.Model") && bad_model.contains("bounded"), "{bad_model}");
    assert!(bad_model.contains("finite model `Tiny.Model` is unsafe"), "{bad_model}");
    assert!(!bad_model.contains("rejected during resolver checking"), "{bad_model}");
    assert!(!bad_model.contains("internal compiler error"), "{bad_model}");
    assert!(!std::path::Path::new(&bin_name("bad_model")).exists());

    // A macro contributes an additional island after the root inventory.
    // The accepted resolver prefix cannot satisfy the whole MIR/export key.
    let source = rfs::read_to_string("subject.rs");
    let extra = format!(
        "{source}\nmacro_rules! add_island {{ () => {{ clean {{ theorem extra : true = true := rfl }} }} }}\nadd_island!();\n"
    );
    rfs::write("expanded.rs", &extra);
    let expanded = compile("expanded.rs", "expanded", false, false);
    assert_eq!(count(&expanded, CHECK), 1, "{expanded}");
    assert_eq!(count(&expanded, PUBLISH), 1, "{expanded}");
    assert_eq!(count(&expanded, RECHECK), 1, "{expanded}");
    run("expanded");

    // This prefix has a theorem but NO callable Clean definition, so a bad
    // macro proof must fail at HIR, without a MIR/export fallback doing it.
    let macro_only = "clean { theorem prefix_ok : true = true := rfl }\n\
        macro_rules! add_island { () => { clean { theorem extra : true = true := rfl } } }\n\
        add_island!();\nfn main() {}\n";
    rfs::write("macro_only.rs", macro_only);
    let macro_only_result = compile("macro_only.rs", "macro_only", false, false);
    assert_eq!(count(&macro_only_result, HIR_FINISH), 0, "{macro_only_result}");
    assert_eq!(count(&macro_only_result, HIR_RECHECK), 1, "{macro_only_result}");
    run("macro_only");
    rfs::write(
        "bad_macro.rs",
        macro_only.replace("theorem extra : true = true", "theorem extra : true = false"),
    );
    let bad_macro = compile("bad_macro.rs", "bad_macro", false, true);
    assert_eq!(count(&bad_macro, PUBLISH), 1, "{bad_macro}");
    assert_eq!(count(&bad_macro, RECHECK), 0, "{bad_macro}");
    assert_eq!(count(&bad_macro, HIR_FINISH), 0, "{bad_macro}");
    assert_eq!(count(&bad_macro, HIR_RECHECK), 1, "{bad_macro}");
    assert_proof_type_error(&bad_macro);
    assert!(bad_macro.contains("extra"), "{bad_macro}");
    assert!(!bad_macro.contains("rejected during resolver checking"), "{bad_macro}");
    assert!(!bad_macro.contains("internal:"), "{bad_macro}");
    assert!(!bad_macro.contains("internal compiler error"), "{bad_macro}");
    assert!(!std::path::Path::new(&bin_name("bad_macro")).exists());

    // E9-DEFERRED-SUFFIX-ENV-1: an island naming `trust_import_*` is checked
    // only after program admission, so the resolver mints `cleanFirst` from
    // the islands before it. The MIR/export environment is that same prefix,
    // so it is the resolver's own snapshot: a hit, never a recheck of the
    // suffix in a session with no admission (which refused the environment
    // and stopped the build at `cleanFirst`). The suffix is still checked, by
    // the kernel-only lane here, and a false theorem in it fails the build.
    let deferred_source = format!(
        "{source}\npub fn first(a: u64, _b: u64) -> u64 {{\n    a\n}}\n\
         clean {{\n    theorem first_is_first (a b : UInt64) :\n        \
         trust_import_deferred__first a b = a := rfl\n}}\n"
    );
    rfs::write("deferred.rs", &deferred_source);
    let deferred = compile("deferred.rs", "deferred", false, false);
    assert_eq!(count(&deferred, CHECK), 1, "{deferred}");
    assert_eq!(count(&deferred, PUBLISH), 1, "{deferred}");
    assert!(count(&deferred, HIT) > 0, "{deferred}");
    assert_eq!(count(&deferred, RECHECK), 0, "{deferred}");
    assert!(deferred.contains("kernel-checked after program admission"), "{deferred}");
    assert!(!deferred.contains("internal:"), "{deferred}");
    run("deferred");
    rfs::write(
        "deferred_false.rs",
        deferred_source.replace(
            "trust_import_deferred__first a b = a",
            "trust_import_deferred_false__first a b = b",
        ),
    );
    let deferred_false = compile("deferred_false.rs", "deferred_false", false, true);
    assert!(
        deferred_false.contains("this island names the kernel-import namespace"),
        "{deferred_false}"
    );
    assert!(!deferred_false.contains("internal:"), "{deferred_false}");
    assert!(!deferred_false.contains("internal compiler error"), "{deferred_false}");
    assert!(!std::path::Path::new(&bin_name("deferred_false")).exists());

    // No environment from a rejected root batch is published, even when
    // one of its sibling declarations was valid.
    rfs::write(
        "rejected.rs",
        format!("{source}\nclean {{ theorem rejected : true = false := rfl }}\n"),
    );
    let rejected = compile("rejected.rs", "rejected", false, true);
    assert_eq!(count(&rejected, CHECK), 1, "{rejected}");
    assert_eq!(count(&rejected, PUBLISH), 0, "{rejected}");
    // A rejected batch is a front-end error: nothing elaborates the crate
    // again, and the island's error is reported once, by the resolver.
    for later in [RECHECK, HIR_FINISH, HIR_RECHECK] {
        assert_eq!(count(&rejected, later), 0, "{later}: {rejected}");
    }
    let errors: Vec<&str> = rejected.lines().filter(|line| line.starts_with("error")).collect();
    assert!(!errors.is_empty(), "{rejected}");
    for error in &errors {
        assert_eq!(
            errors.iter().filter(|other| *other == error).count(),
            1,
            "`{error}` is reported more than once: {rejected}"
        );
    }
    assert_proof_type_error(&rejected);
    assert!(rejected.contains("rejected during resolver checking"), "{rejected}");
    assert!(!rejected.contains("internal compiler error"), "{rejected}");
    assert!(!std::path::Path::new(&bin_name("rejected")).exists());

    // A census is a different recipe: retain its own resolver/HIR reports
    // and the ordinary MIR fallback, rather than laundering a census hit.
    let census = compile("subject.rs", "census", true, false);
    assert_eq!(count(&census, CHECK), 0, "{census}");
    assert_eq!(count(&census, PUBLISH), 0, "{census}");
    assert_eq!(count(&census, RECHECK), 1, "{census}");
    assert_eq!(count(&census, HIR_FINISH), 0, "{census}");
    let events: Vec<serde_json::Value> = rfs::read_to_string("census.jsonl")
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(events.iter().filter(|event| event["event"] == "resolver_check").count(), 1);
    assert!(events.iter().any(|event| event["event"] == "check"));
    run("census");
}
