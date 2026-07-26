use std::collections::BTreeSet;
use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rust_lib_name, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    // Both artifacts deliberately have the same internal crate name and item
    // path. Distinct metadata produces distinct StableCrateIds, exactly as two
    // Cargo-resolved versions of one package do.
    for (source, suffix) in [("dep-a.rs", "a"), ("dep-b.rs", "b")] {
        cmd(&trustc)
            .arg("-Ztrust-verify=off")
            .arg("--crate-name=shared")
            .arg("--crate-type=rlib")
            .arg(format!("-Cmetadata={suffix}"))
            .arg(format!("-Cextra-filename=-{suffix}"))
            .arg(source)
            .run();
    }

    cmd(&trustc)
        .env_remove("TRUST_DUMP_MONO")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-dump=mir-only:dumps")
        .arg("--crate-name=duplicate_call_identity")
        .arg("--crate-type=lib")
        // `--extern` directly: this drives the raw `cmd(&trustc)` base Command
        // (needed for the custom trustc path), which has no typed `.extern_()`
        // helper — that lives on the `Rustc`/`Rustdoc` wrappers. Mirrors
        // `run_make_support::Rustc::extern_` (`--extern crate=path`).
        .arg("--extern")
        .arg(format!("shared_a={}", rust_lib_name("shared-a")))
        .arg("--extern")
        .arg(format!("shared_b={}", rust_lib_name("shared-b")))
        .arg("main.rs")
        .run();

    let mut direct_keys = BTreeSet::new();
    for entry in rfs::read_dir("dumps") {
        let entry = entry.expect("read MIR dump directory entry");
        let json = rfs::read_to_string(entry.path());
        for line in json.lines() {
            if line.contains("\"func\":")
                && line.trim().ends_with("::contracted\",")
            {
                direct_keys.insert(line.trim().to_string());
            }
        }
    }

    assert_eq!(
        direct_keys.len(),
        2,
        "same-name dependency calls must have two exact identities, got {direct_keys:#?}"
    );
    let mut crate_tags = BTreeSet::new();
    for key in &direct_keys {
        assert!(
            key.contains("__trust_crate@") && key.ends_with("::contracted\","),
            "ambiguous external call lacks its unforgeable stable-crate tag: {key}"
        );
        let tag = key
            .split_once("__trust_crate@")
            .and_then(|(_, rest)| rest.get(..16))
            .unwrap_or_else(|| panic!("stable-crate tag is not `@<hex16>`: {key}"));
        assert!(
            tag.chars().all(|c| c.is_ascii_hexdigit()),
            "stable-crate tag is not 16 hex digits: {key}"
        );
        crate_tags.insert(tag.to_string());
    }
    assert_eq!(
        crate_tags.len(),
        2,
        "same-name dependencies must carry distinct stable-crate tags: {direct_keys:#?}"
    );

    let default_paths = top_level_def_paths("dumps");
    assert!(
        default_paths.iter().all(|path| !path.contains("shared::generic::<i32>")),
        "unset TRUST_DUMP_MONO emitted foreign generic instances: {default_paths:#?}"
    );

    cmd(&trustc)
        .env("TRUST_DUMP_MONO", "1")
        .arg("-Zno-codegen")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-dump=mir-only:no-codegen-dumps")
        .arg("--crate-name=duplicate_call_identity")
        .arg("--crate-type=lib")
        .arg("--extern")
        .arg(format!("shared_a={}", rust_lib_name("shared-a")))
        .arg("--extern")
        .arg(format!("shared_b={}", rust_lib_name("shared-b")))
        .arg("main.rs")
        .run();
    let mut no_codegen_paths = top_level_def_paths("no-codegen-dumps");
    let mut default_inventory = default_paths.clone();
    no_codegen_paths.sort();
    default_inventory.sort();
    assert_eq!(
        no_codegen_paths, default_inventory,
        "-Zno-codegen must leave exactly the ordinary local dump inventory"
    );

    cmd(&trustc)
        .env("TRUST_DUMP_MONO", "1")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-dump=mir-only:mono-dumps")
        .arg("--crate-name=duplicate_call_identity")
        .arg("--crate-type=lib")
        .arg("--extern")
        .arg(format!("shared_a={}", rust_lib_name("shared-a")))
        .arg("--extern")
        .arg(format!("shared_b={}", rust_lib_name("shared-b")))
        .arg("-o")
        .arg("mono-probe.rlib")
        .arg("main.rs")
        .run();

    let mono_paths = top_level_def_paths("mono-dumps");
    let mut default_locals = default_paths
        .iter()
        .filter(|path| path.starts_with("duplicate_call_identity::"))
        .cloned()
        .collect::<Vec<_>>();
    let mut mono_locals = mono_paths
        .iter()
        .filter(|path| path.starts_with("duplicate_call_identity::"))
        .cloned()
        .collect::<Vec<_>>();
    default_locals.sort();
    mono_locals.sort();
    assert_eq!(
        mono_locals, default_locals,
        "the mono lane must not duplicate or change the ordinary local dump inventory"
    );

    let duplicate_generics = mono_paths
        .iter()
        .filter(|path| path.contains("shared::generic::<i32>"))
        .collect::<Vec<_>>();
    assert_eq!(
        duplicate_generics.len(),
        2,
        "both same-name dependency instances must survive exact Instance dedup: {mono_paths:#?}"
    );
    assert_ne!(duplicate_generics[0], duplicate_generics[1]);
    for path in duplicate_generics {
        assert!(
            path.contains("__trust_crate@") && path.contains("__trust_args@"),
            "monomorphic duplicate-crate identity lacks stable crate/argument binding: {path}"
        );
    }

    let rendered_arg_instances = mono_paths
        .iter()
        .filter(|path| path.contains("shared::arg_identity::<shared::Marker>"))
        .collect::<Vec<_>>();
    assert_eq!(
        rendered_arg_instances.len(),
        2,
        "two distinct same-rendered dependency types must produce two instances: {mono_paths:#?}"
    );
    assert_ne!(rendered_arg_instances[0], rendered_arg_instances[1]);
    let arg_fingerprints = rendered_arg_instances
        .iter()
        .map(|path| {
            path.rsplit_once("::<__trust_args@")
                .and_then(|(_, suffix)| suffix.strip_suffix('>'))
                .unwrap_or_else(|| panic!("instance lacks exact argument identity: {path}"))
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        arg_fingerprints.len(),
        2,
        "distinct same-rendered dependency types must have distinct argument fingerprints"
    );

    assert!(
        mono_paths
            .iter()
            .all(|path| !path.contains("shared::contracted_generic")),
        "a foreign generic with a non-empty Trust contract bundle must be excluded: {mono_paths:#?}"
    );

    for expected in [
        "<i32 as core::cmp::Ord>::max",
        "<i32 as core::cmp::Ord>::min",
        "<u8 as core::cmp::Ord>::max",
        "<u8 as core::cmp::Ord>::min",
        "core::cmp::max::<i32>",
        "core::cmp::min::<i32>",
    ] {
        let matches = mono_paths.iter().filter(|path| path.contains(expected)).count();
        assert_eq!(
            matches, 1,
            "expected exactly one concrete foreign `{expected}` instance: {mono_paths:#?}"
        );
    }
}

fn top_level_def_paths(directory: &str) -> Vec<String> {
    let mut paths = Vec::new();
    for entry in rfs::read_dir(directory) {
        let entry = entry.expect("read MIR dump directory entry");
        let json = rfs::read_to_string(entry.path());
        let line = json
            .lines()
            .find(|line| line.starts_with("  \"def_path\": "))
            .unwrap_or_else(|| {
                panic!("MIR dump has no top-level def_path: {}", entry.path().display())
            });
        let path = line
            .trim()
            .strip_prefix("\"def_path\": \"")
            .and_then(|value| value.strip_suffix("\","))
            .unwrap_or_else(|| panic!("non-canonical top-level def_path line: {line}"));
        paths.push(path.to_string());
    }
    paths
}
