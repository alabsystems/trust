use super::*;
use std::time::{SystemTime, UNIX_EPOCH};

fn empty_manifest() -> Manifest {
    Manifest {
        manifest_version: "2".to_string(),
        date: "2026-04-23".to_string(),
        pkg: BTreeMap::new(),
        artifacts: BTreeMap::new(),
        renames: BTreeMap::new(),
        profiles: BTreeMap::new(),
    }
}

fn test_builder(input: PathBuf) -> Builder {
    Builder {
        versions: Versions::new("nightly", &input).unwrap(),
        checksums: Checksums::new().unwrap(),
        shipped_files: HashSet::new(),
        input: input.clone(),
        output: input,
        s3_address: "https://static.example.test/dist".to_string(),
        date: "2026-04-23".to_string(),
    }
}

fn temp_dist_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let dir =
        env::temp_dir().join(format!("build-manifest-{test_name}-{}-{nanos}", std::process::id()));
    fs::create_dir(&dir).unwrap();
    dir
}

fn package_available_for(target: &str) -> Package {
    Package {
        version: String::new(),
        git_commit_hash: None,
        target: BTreeMap::from([(
            target.to_string(),
            Target { available: true, ..Target::default() },
        )]),
    }
}

fn has_component(components: &[Component], pkg: &str, target: &str) -> bool {
    components.iter().any(|component| component.pkg == pkg && component.target == target)
}

fn assert_profile_has_no_duplicates(name: &str, components: &[String]) {
    let mut seen = HashSet::new();
    for component in components {
        assert!(
            seen.insert(component),
            "{name} profile contains duplicate component {component}: {components:?}"
        );
    }
}

#[test]
fn default_profile_contains_daily_driver_tools() {
    let mut builder = test_builder(PathBuf::new());
    let mut manifest = empty_manifest();

    builder.add_profiles_to(&mut manifest);

    let default = manifest.profiles.get("default").expect("default profile");
    assert_profile_has_no_duplicates("default", default);
    for component in [
        "trustc",
        "targo",
        "trust-std",
        "trust-docs",
        "targo-trust",
        "trustfmt-preview",
        "tippy-preview",
        "trust-analyzer-preview",
        "trust-src",
        "trust-llvm-tools-preview",
    ] {
        assert!(
            default.iter().any(|actual| actual == component),
            "default profile is missing {component}; components: {default:?}"
        );
    }

    let complete = manifest.profiles.get("complete").expect("complete profile");
    assert_profile_has_no_duplicates("complete", complete);
    assert!(
        complete.iter().any(|actual| actual == "trust-miri-preview"),
        "complete profile is missing trust-miri-preview; components: {complete:?}"
    );
    assert!(
        complete.iter().all(|actual| actual != "miri-preview"),
        "complete profile exposes inherited miri-preview component: {complete:?}"
    );
}

#[test]
fn rust_component_spellings_rename_to_trust_components() {
    let builder = test_builder(PathBuf::new());
    let mut manifest = empty_manifest();

    builder.add_renames_to(&mut manifest);

    for (from, to) in [
        ("rustc", "trustc"),
        ("cargo", "targo"),
        ("rust-std", "trust-std"),
        ("rust-docs", "trust-docs"),
        ("rustc-docs", "trustc-docs"),
        ("rustc-dev", "trustc-dev"),
        ("rust-mingw", "trust-mingw"),
        ("rust-analysis", "trust-analysis"),
        ("rust-src", "trust-src"),
        ("llvm-tools", "trust-llvm-tools-preview"),
        ("rustfmt", "trustfmt-preview"),
        ("clippy", "tippy-preview"),
        ("rust-analyzer", "trust-analyzer-preview"),
        ("miri", "trust-miri-preview"),
    ] {
        assert_eq!(
            manifest.renames.get(from).map(|rename| rename.to.as_str()),
            Some(to),
            "missing component rename {from} -> {to}; renames: {:?}",
            manifest.renames
        );
    }
}

#[test]
fn rust_package_host_extensions_contain_targo_trust() {
    let host = HOSTS[0];
    let input = temp_dist_dir("targo-trust-extension");
    let mut builder = test_builder(input.clone());
    let rust_tarball = builder.versions.tarball_name(&PkgType::Rust, host).unwrap();
    fs::write(input.join(rust_tarball), b"").unwrap();

    let mut manifest = empty_manifest();
    manifest.pkg.insert("targo-trust".to_string(), package_available_for(host));

    let target = builder
        .target_host_combination(host, &manifest)
        .expect("trust package target is available");
    let extensions = target.extensions.expect("trust package extensions");

    assert!(
        has_component(&extensions, "targo-trust", host),
        "trust package extensions for {host}: {:?}",
        extensions.iter().map(|component| (&component.pkg, &component.target)).collect::<Vec<_>>()
    );

    fs::remove_dir_all(input).unwrap();
}
