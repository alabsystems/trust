//! Trust: Targo's feature sandbox allows every crate-level unstable feature that the
//! first-party crates Targo links enable (STAGE1-TARGO-AY-FEATURES-1).
//!
//! `x.py build --stage 1 targo-build-tool`, and every `x.py check` that builds that Targo
//! first, stopped compiling on 2026-11-09: a6a809eb08 and bc24b82698 linked
//! `trust-certify`, and through it AY's solver crates, into Targo. `ay-sat` enables
//! `allocator_api`, and the sandbox refused it (E0725) in a gate, not in a test.
//!
//! The census walks Targo's lockfile from `targo` along its resolved edges. Each
//! path-sourced package is found where its dependent's manifest, or Targo's `[patch]`,
//! names it, and its library, build-script and (for Targo) binary roots are read for
//! `#![feature(..)]` and `#![cfg_attr(<condition>, feature(..))]`. A crate newly linked
//! into Targo, or a feature a linked crate adds, therefore fails here. Registry crates
//! are not read: their nightly probes are what `min_specialization` and `specialization`
//! are allowed for (`BUILD_SCRIPT_PROBED`).

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};
use std::path::{Path, PathBuf};

use ::toml::Value;

use super::*;

/// Allowed for registry crates whose build scripts probe the compiler channel (the
/// comment on `targo_tool_build_recipe`); no first-party root asks for them.
const BUILD_SCRIPT_PROBED: &[&str] = &["min_specialization", "specialization"];

const TEST_ONLY: &str = "cfg(test) holds only for the crate under test; Targo links the library";
const DOCS_RS: &str = "cfg(docsrs) is set only by docs.rs builds";
const FOREIGN_TARGET: &str = "Targo is not built for an SGX or wasm target";
const MANUAL_CFG: &str = "cfg(trust_contracts) is a manual opt-in \
     (scripts/trust_self_verify_crate.sh passes it in RUSTFLAGS); bootstrap never sets it";
const CARGO_FEATURE_OFF: &str = "no first-party manifest in Targo's graph turns this Cargo \
     feature on (checked by every_inert_row_..), and `targo metadata --locked` of src/tools/targo \
     resolves it off (STAGE1-TARGO-AY-FEATURES-1)";

/// Conditional crate-level features of Targo's linked crates whose condition does not
/// hold when bootstrap builds Targo: (package, condition without whitespace, feature,
/// why). A conditional feature that is neither allowed nor listed here fails the census,
/// so a new one is classified before it reaches a gate.
const INERT: &[(&str, &str, &str, &str)] = &[
    ("bootstrap", "test", "test", TEST_ONLY),
    ("bootstrap", "test", "custom_test_frameworks", TEST_ONLY),
    ("bootstrap", "test", "exitcode_exit_method", TEST_ONLY),
    ("build-rs", "all(docsrs,feature=\"unstable\")", "doc_cfg", DOCS_RS),
    ("sha2", "docsrs", "doc_cfg", DOCS_RS),
    ("tla-lock-api", "docsrs", "doc_cfg", DOCS_RS),
    ("tla-smallvec", "docsrs", "doc_cfg", DOCS_RS),
    (
        "tla-lock-core",
        "all(target_env=\"sgx\",target_vendor=\"fortanix\")",
        "sgx_platform",
        FOREIGN_TARGET,
    ),
    (
        "tla-lock-core",
        "all(feature=\"nightly\",target_family=\"wasm\",target_feature=\"atomics\")",
        "stdarch_wasm_atomic_wait",
        FOREIGN_TARGET,
    ),
    ("trust-semantics", "trust_contracts", "contracts", MANUAL_CFG),
    ("rustc-hash", "feature=\"nightly\"", "const_default", CARGO_FEATURE_OFF),
    ("rustc-hash", "feature=\"nightly\"", "const_trait_impl", CARGO_FEATURE_OFF),
    ("rustc-hash", "feature=\"nightly\"", "derive_const", CARGO_FEATURE_OFF),
    ("rustc-hash", "feature=\"nightly\"", "hasher_prefixfree_extras", CARGO_FEATURE_OFF),
    ("tla-smallvec", "feature=\"may_dangle\"", "dropck_eyepatch", CARGO_FEATURE_OFF),
    ("tla-smallvec", "feature=\"debugger_visualizer\"", "debugger_visualizer", CARGO_FEATURE_OFF),
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn canonical(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn read_toml(path: &Path) -> Value {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    ::toml::from_str(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn str_at<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct PackageId {
    name: String,
    version: String,
    source: Option<String>,
}

struct Lock {
    packages: Vec<(PackageId, Vec<String>)>,
}

impl Lock {
    fn read(path: &Path) -> Self {
        let lock = read_toml(path);
        let packages = lock["package"]
            .as_array()
            .expect("a lockfile lists packages")
            .iter()
            .map(|package| {
                let id = PackageId {
                    name: str_at(package, "name").expect("a locked package has a name").into(),
                    version: str_at(package, "version").expect("and a version").into(),
                    source: str_at(package, "source").map(String::from),
                };
                let dependencies = package
                    .get("dependencies")
                    .and_then(Value::as_array)
                    .map(|deps| deps.iter().filter_map(Value::as_str).map(String::from).collect())
                    .unwrap_or_default();
                (id, dependencies)
            })
            .collect();
        Lock { packages }
    }

    /// The package a lockfile dependency entry names: `name`, `name version` or
    /// `name version (source)`. Cargo writes no source for a path package, so an entry
    /// without one that matches a path package and a sourced one names the path package.
    fn resolve(&self, entry: &str) -> &(PackageId, Vec<String>) {
        let mut parts = entry.splitn(3, ' ');
        let name = parts.next().unwrap();
        let version = parts.next();
        let source = parts.next().map(|s| s.trim_start_matches('(').trim_end_matches(')'));
        let mut found: Vec<_> = self
            .packages
            .iter()
            .filter(|(id, _)| {
                id.name == name
                    && version.is_none_or(|v| id.version == v)
                    && source.is_none_or(|s| id.source.as_deref() == Some(s))
            })
            .collect();
        if source.is_none() && found.len() > 1 {
            found.retain(|(id, _)| id.source.is_none());
        }
        assert_eq!(found.len(), 1, "lockfile entry `{entry}` names {} packages", found.len());
        found[0]
    }
}

/// The workspace manifest a package's `workspace = true` entries read: its explicit
/// `package.workspace`, else the nearest enclosing manifest with a `[workspace]` table.
fn workspace_of(dir: &Path, manifest: &Value) -> (PathBuf, Value) {
    if let Some(root) = manifest.get("package").and_then(|p| str_at(p, "workspace")) {
        let root = canonical(&dir.join(root));
        let value = read_toml(&root.join("Cargo.toml"));
        return (root, value);
    }
    let mut at = Some(dir);
    while let Some(candidate) = at {
        let path = candidate.join("Cargo.toml");
        if path.is_file() {
            let value = read_toml(&path);
            if value.get("workspace").is_some() {
                return (candidate.to_path_buf(), value);
            }
        }
        at = candidate.parent();
    }
    panic!("{} names a workspace dependency outside any workspace", dir.display())
}

/// One dependency entry of a manifest, with `workspace = true` resolved.
struct DependencyEntry {
    /// The key the manifest names it by (a `"<key>/<feature>"` entry uses it).
    key: String,
    /// The package it names.
    package: String,
    /// Its `path`, resolved against the manifest that spells it.
    path: Option<PathBuf>,
    /// The Cargo features it turns on: its own and the workspace entry's.
    features: BTreeSet<String>,
}

/// The strings of a TOML array (nothing when it is absent).
fn strings(value: Option<&Value>) -> impl Iterator<Item = &str> {
    value.and_then(Value::as_array).into_iter().flatten().filter_map(Value::as_str)
}

/// Every dependency entry of a manifest (normal, build and dev, and per target). A
/// `workspace = true` entry reads the workspace's own entry, which may rename it.
fn dependency_entries(
    dir: &Path,
    manifest: &Value,
    workspace: &mut Option<(PathBuf, Value)>,
) -> Vec<DependencyEntry> {
    let mut tables = Vec::new();
    for kind in ["dependencies", "build-dependencies", "dev-dependencies"] {
        tables.extend(manifest.get(kind));
        if let Some(targets) = manifest.get("target").and_then(Value::as_table) {
            tables.extend(targets.values().filter_map(|target| target.get(kind)));
        }
    }
    let mut entries = Vec::new();
    for (key, spec) in tables.into_iter().filter_map(Value::as_table).flatten() {
        let mut features: BTreeSet<String> =
            strings(spec.get("features")).map(String::from).collect();
        let (base, spec) = if spec.get("workspace").and_then(Value::as_bool) == Some(true) {
            let (root, value) = workspace.get_or_insert_with(|| workspace_of(dir, manifest));
            let entry = value.get("workspace").and_then(|w| w.get("dependencies"));
            match entry.and_then(|entries| entries.get(key.as_str())) {
                Some(entry) => (root.as_path(), entry),
                None => panic!("{} inherits {key}, which its workspace lacks", dir.display()),
            }
        } else {
            (dir, spec)
        };
        features.extend(strings(spec.get("features")).map(String::from));
        entries.push(DependencyEntry {
            key: key.clone(),
            package: str_at(spec, "package").unwrap_or(key.as_str()).into(),
            path: str_at(spec, "path").map(|path| base.join(path)),
            features,
        });
    }
    entries
}

/// The directories a manifest's path dependencies on package `name` point at.
fn path_dependency(
    dir: &Path,
    manifest: &Value,
    workspace: &mut Option<(PathBuf, Value)>,
    name: &str,
) -> BTreeSet<PathBuf> {
    let entries = dependency_entries(dir, manifest, workspace).into_iter();
    entries
        .filter(|entry| entry.package == name)
        .filter_map(|e| e.path)
        .map(|p| canonical(&p))
        .collect()
}

/// Where a manifest of Targo's path graph turns on Cargo feature `feature` of `package`:
/// the package's own `default` set (transitively), a dependency entry's `features`, or a
/// `"<dep>/<feature>"` or `"<dep>?/<feature>"` feature entry. Registry manifests are not
/// read, so this answers for the first-party graph only.
fn graph_enables(
    packages: &BTreeMap<PackageId, PathBuf>,
    package: &str,
    feature: &str,
) -> Vec<String> {
    let mut found = Vec::new();
    for (id, dir) in packages {
        let manifest = read_toml(&dir.join("Cargo.toml"));
        let table = manifest.get("features").and_then(Value::as_table);
        if id.name == package {
            let mut reached = BTreeSet::new();
            let mut queue = vec!["default".to_owned()];
            while let Some(name) = queue.pop() {
                if reached.insert(name.clone()) {
                    let members = strings(table.and_then(|t| t.get(name.as_str())));
                    queue.extend(members.map(String::from));
                }
            }
            if reached.contains(feature) {
                found.push(format!("{}'s default features", id.name));
            }
        }
        let mut workspace = None;
        for entry in dependency_entries(dir, &manifest, &mut workspace) {
            if entry.package != package {
                continue;
            }
            if entry.features.contains(feature) {
                found.push(format!("{}'s dependency `{}`", id.name, entry.key));
            }
            let spelled = [format!("{}/{feature}", entry.key), format!("{}?/{feature}", entry.key)];
            for (name, members) in table.into_iter().flatten() {
                if strings(Some(members)).any(|member| spelled.iter().any(|s| s == member)) {
                    found.push(format!("{}'s feature `{name}`", id.name));
                }
            }
        }
    }
    found
}

/// Targo's `[patch.<source>]` path entries, by package name.
fn patch_paths(targo: &Path, manifest: &Value) -> BTreeMap<String, BTreeSet<PathBuf>> {
    let mut paths: BTreeMap<String, BTreeSet<PathBuf>> = BTreeMap::new();
    let tables = manifest.get("patch").and_then(Value::as_table).into_iter().flatten();
    for (key, spec) in tables.filter_map(|(_, table)| table.as_table()).flatten() {
        if let Some(path) = str_at(spec, "path") {
            let name = str_at(spec, "package").unwrap_or(key.as_str());
            paths.entry(name.into()).or_default().insert(canonical(&targo.join(path)));
        }
    }
    paths
}

/// Every path-sourced package Targo's lockfile reaches from `targo`, with its directory.
fn targo_path_packages(root: &Path) -> BTreeMap<PackageId, PathBuf> {
    let targo = canonical(&root.join("src/tools/targo"));
    let lock = Lock::read(&targo.join("Cargo.lock"));
    let patches = patch_paths(&targo, &read_toml(&targo.join("Cargo.toml")));
    let start = lock.resolve("targo");
    assert!(start.0.source.is_none(), "Targo is the workspace's own package: {:?}", start.0);
    let mut dirs = BTreeMap::from([(start.0.clone(), targo)]);
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([start]);
    while let Some((id, dependencies)) = queue.pop_front() {
        if !seen.insert(id.clone()) {
            continue;
        }
        let dependent = dirs.get(id).map(|dir| (dir.clone(), read_toml(&dir.join("Cargo.toml"))));
        let mut workspace = None;
        for entry in dependencies {
            let dependency = lock.resolve(entry);
            queue.push_back(dependency);
            if dependency.0.source.is_some() {
                continue;
            }
            let name = &dependency.0.name;
            let mut found = dependent
                .as_ref()
                .map(|(dir, manifest)| path_dependency(dir, manifest, &mut workspace, name))
                .unwrap_or_default();
            if found.is_empty() {
                found = patches.get(name).cloned().unwrap_or_default();
            }
            assert_eq!(found.len(), 1, "{id:?} names path package {name} at {found:?}");
            let dir = found.pop_first().unwrap();
            let manifest = read_toml(&dir.join("Cargo.toml"));
            assert_eq!(
                manifest.get("package").and_then(|p| str_at(p, "name")),
                Some(name.as_str()),
                "{} is not the package {name}",
                dir.display()
            );
            if let Some(previous) = dirs.insert(dependency.0.clone(), dir.clone()) {
                assert_eq!(previous, dir, "{name} resolves to two directories");
            }
        }
    }
    dirs
}

/// The crate roots of a package that the Targo build compiles: its library, its build
/// script and, for Targo itself, its binaries.
fn crate_roots(dir: &Path, with_bins: bool) -> Vec<PathBuf> {
    let manifest = read_toml(&dir.join("Cargo.toml"));
    let mut roots = Vec::new();
    match manifest.get("lib").and_then(|lib| str_at(lib, "path")) {
        Some(path) => roots.push(dir.join(path)),
        None if dir.join("src/lib.rs").is_file() => roots.push(dir.join("src/lib.rs")),
        None => {}
    }
    match manifest.get("package").and_then(|p| p.get("build")) {
        Some(Value::String(path)) => roots.push(dir.join(path)),
        Some(Value::Boolean(false)) => {}
        _ if dir.join("build.rs").is_file() => roots.push(dir.join("build.rs")),
        _ => {}
    }
    if with_bins {
        let bins = manifest.get("bin").and_then(Value::as_array).into_iter().flatten();
        roots.extend(bins.filter_map(|bin| str_at(bin, "path")).map(|path| dir.join(path)));
    }
    roots
}

/// The text of an inner attribute, from after `#![` up to its closing `]`.
fn attribute_body(text: &str) -> &str {
    let (mut depth, mut in_string, mut escaped) = (0usize, false, false);
    for (at, c) in text.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' => depth += 1,
            ')' => depth -= 1,
            ']' if depth == 0 => return &text[..at],
            ']' => depth -= 1,
            _ => {}
        }
    }
    panic!("an inner attribute does not close: {text:.80}")
}

/// `text` split at its top-level commas.
fn split_top_level(text: &str) -> Vec<&str> {
    let (mut parts, mut depth, mut start, mut in_string) = (Vec::new(), 0usize, 0, false);
    for (at, c) in text.char_indices() {
        match c {
            '"' => in_string = !in_string,
            _ if in_string => {}
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(&text[start..at]);
                start = at + 1;
            }
            _ => {}
        }
    }
    parts.push(&text[start..]);
    parts
}

/// `name(args)` gives `args`.
fn call_args<'a>(attribute: &'a str, name: &str) -> Option<&'a str> {
    attribute.strip_prefix(name)?.trim_start().strip_prefix('(')?.strip_suffix(')')
}

fn collect(attribute: &str, condition: Option<&str>, found: &mut Vec<(Option<String>, String)>) {
    let attribute = attribute.trim();
    if let Some(features) = call_args(attribute, "feature") {
        let features = split_top_level(features).into_iter().map(str::trim);
        found.extend(
            features.filter(|f| !f.is_empty()).map(|f| (condition.map(String::from), f.into())),
        );
    } else if let Some(arguments) = call_args(attribute, "cfg_attr") {
        let mut parts = split_top_level(arguments).into_iter();
        let inner: String = parts.next().unwrap_or_default().split_whitespace().collect();
        let combined = match condition {
            Some(outer) => format!("all({outer},{inner})"),
            None => inner,
        };
        for part in parts {
            collect(part, Some(&combined), found);
        }
    }
}

/// The crate-level `feature(..)`s of a crate root, each with its `cfg_attr` condition
/// (whitespace removed), `None` when unconditional. Only an inner attribute that starts
/// a line counts, so comments and doc text quoting one do not.
fn crate_level_features(source: &str) -> Vec<(Option<String>, String)> {
    let mut found = Vec::new();
    let mut offset = 0;
    for line in source.split_inclusive('\n') {
        let trimmed = line.trim_start();
        let start = offset + (line.len() - trimmed.len());
        offset += line.len();
        if trimmed.starts_with("#![") {
            collect(attribute_body(&source[start + "#![".len()..]), None, &mut found);
        }
    }
    found
}

/// One crate-level feature a crate Targo links enables.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Enabled {
    package: String,
    root: PathBuf,
    condition: Option<String>,
    feature: String,
}

fn census() -> Vec<Enabled> {
    let root = canonical(&repo_root());
    let mut enabled = Vec::new();
    for (id, dir) in targo_path_packages(&root) {
        for path in crate_roots(&dir, id.name == "targo") {
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("{} is readable: {e}", path.display()));
            let root_path = path.strip_prefix(&root).unwrap_or(&path).to_path_buf();
            for (condition, feature) in crate_level_features(&source) {
                enabled.push(Enabled {
                    package: id.name.clone(),
                    root: root_path.clone(),
                    condition,
                    feature,
                });
            }
        }
    }
    enabled.sort();
    enabled
}

/// The sandbox the Targo build's compiler receives: `RUSTC_ALLOW_FEATURES` of the
/// prepared recipe command, which is `TARGO_ALLOW_FEATURES` plus what bootstrap adds to
/// every non-empty list (`builder/cargo.rs`).
fn sandbox() -> BTreeSet<String> {
    let context = crate::utils::tests::TestCtx::new();
    let build =
        crate::core::session::Session::new(context.config("build").stage(1).create_config());
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let recipe =
        targo_tool_build_recipe(Compiler::new(0, target), Compiler::new(1, target), target);
    assert_eq!(recipe.allow_features, TARGO_ALLOW_FEATURES);
    let mut cargo = prepare_tool_cargo(
        &builder,
        recipe.build_compiler,
        recipe.mode,
        target,
        Kind::Build,
        recipe.path,
        recipe.source_type.clone(),
        &recipe.extra_features,
    );
    cargo.allow_features(recipe.allow_features);
    let mut command = cargo.into_cmd();
    command.mark_as_executed();
    let features = command
        .get_envs()
        .find(|(key, _)| *key == "RUSTC_ALLOW_FEATURES")
        .and_then(|(_, value)| value)
        .expect("the Targo recipe keeps an explicit feature sandbox")
        .to_str()
        .unwrap()
        .to_owned();
    features.split(',').map(String::from).collect()
}

fn is_inert(enabled: &Enabled) -> bool {
    let condition = enabled.condition.as_deref();
    INERT.iter().any(|&(package, inert_condition, feature, _)| {
        package == enabled.package
            && Some(inert_condition) == condition
            && feature == enabled.feature
    })
}

#[test]
fn the_census_reads_line_start_attributes_with_their_conditions() {
    let source = "//! #![feature(quoted_in_docs)]\n// #![feature(commented_out)]\n\
                  #![feature(a, b)]\n  #![cfg_attr(test, feature(c), allow(dead_code))]\n\
                  #![cfg_attr(\n    all(feature = \"client\", x),\n    feature(d)\n)]\n\
                  #![cfg_attr(not(test), cfg_attr(y, feature(e)))]\n\
                  #![register_tool(trust)]\n#![cfg_attr(z, doc = \"feature(f)]\")]\n\
                  fn f() { let _ = \"#![feature(g)]\"; }\n";
    let found = crate_level_features(source);
    let expected: Vec<(Option<String>, String)> = vec![
        (None, "a".into()),
        (None, "b".into()),
        (Some("test".into()), "c".into()),
        (Some("all(feature=\"client\",x)".into()), "d".into()),
        (Some("all(not(test),y)".into()), "e".into()),
    ];
    assert_eq!(found, expected);
}

#[test]
fn the_walk_reaches_ay_sat_and_the_controller_client_where_targo_names_them() {
    let root = canonical(&repo_root());
    let packages = targo_path_packages(&root);
    let dir_of = |name: &str| {
        packages
            .iter()
            .find(|(id, _)| id.name == name)
            .map(|(_, dir)| dir.strip_prefix(&root).unwrap().to_path_buf())
    };
    // Positive controls: the walk follows a patched Git edge (clean-auto's AY), a
    // workspace-inherited edge inside AY, and a target-specific Targo edge.
    assert_eq!(dir_of("ay-sat"), Some(PathBuf::from("first-party/ay/crates/ay-sat")));
    assert_eq!(dir_of("ay-core"), Some(PathBuf::from("first-party/ay/crates/ay-core")));
    assert_eq!(
        dir_of("trust-resource-controller"),
        Some(PathBuf::from("crates/trust-resource-controller"))
    );
    // ay-sys names AY's own vendored copy, not the root crate of the same name.
    assert_eq!(
        dir_of("trust-exec-policy"),
        Some(PathBuf::from("first-party/ay/vendor/trust-exec-policy"))
    );
}

/// The census's features that the Targo build compiles with: unconditional ones, and
/// conditional ones `INERT` does not rule out.
fn taken(census: &[Enabled]) -> Vec<&Enabled> {
    census.iter().filter(|e| e.condition.is_none() || !is_inert(e)).collect()
}

#[test]
fn targo_allows_every_feature_its_linked_first_party_crates_enable() {
    let census = census();
    // Positive controls: the unconditional feature this red was, and two conditional
    // ones the build takes (a build-script cfg and a default Cargo feature).
    for (package, feature) in [
        ("ay-sat", "allocator_api"),
        ("trust-resource-controller", "trust_process_inherit_fds"),
        ("trust-types", "try_trait_v2"),
    ] {
        assert!(
            taken(&census).iter().any(|e| e.package == package && e.feature == feature),
            "the census did not find {package}'s {feature}: {census:#?}"
        );
    }
    let sandbox = sandbox();
    let refused: Vec<&Enabled> =
        taken(&census).into_iter().filter(|e| !sandbox.contains(&e.feature)).collect();
    assert!(
        refused.is_empty(),
        "Targo links crates enabling features its sandbox ({sandbox:?}) refuses; add each to \
         TARGO_ALLOW_FEATURES, naming the crate, or, for a condition the Targo build never \
         meets, list it in INERT with why: {refused:#?}"
    );
}

#[test]
fn every_inert_row_names_a_refused_conditional_feature_targo_links() {
    let census = census();
    let sandbox = sandbox();
    let packages = targo_path_packages(&canonical(&repo_root()));
    // Positive controls for the Cargo-feature reading: a default feature, and a feature a
    // dependency entry turns on.
    assert!(!graph_enables(&packages, "trust-types", "try-sugar").is_empty());
    assert!(!graph_enables(&packages, "trust-resource-controller", "client").is_empty());
    for row @ &(package, condition, feature, why) in INERT {
        assert!(
            census.iter().any(|e| e.package == package
                && e.condition.as_deref() == Some(condition)
                && e.feature == feature),
            "stale INERT row {row:?}: no crate Targo links enables it so"
        );
        assert!(!sandbox.contains(feature), "INERT row {row:?} names an allowed feature");
        if why == CARGO_FEATURE_OFF {
            let cargo_feature = condition
                .strip_prefix("feature=\"")
                .and_then(|rest| rest.strip_suffix('"'))
                .unwrap_or_else(|| panic!("{row:?} is not a plain Cargo-feature condition"));
            let enabled_by = graph_enables(&packages, package, cargo_feature);
            assert!(
                enabled_by.is_empty(),
                "INERT row {row:?}: Targo's graph turns `{cargo_feature}` on: {enabled_by:?}"
            );
        }
    }
}

#[test]
fn targo_allows_nothing_its_graph_does_not_need() {
    let census = census();
    let listed: BTreeSet<String> = TARGO_ALLOW_FEATURES.split(',').map(String::from).collect();
    // What bootstrap adds to every list (register_tool among them) is not Targo's to list.
    let added: BTreeSet<String> = sandbox().difference(&listed).cloned().collect();
    assert!(added.contains("register_tool"), "{added:?}");
    let needed: BTreeSet<String> = taken(&census)
        .into_iter()
        .map(|e| e.feature.clone())
        .filter(|feature| !added.contains(feature))
        .chain(BUILD_SCRIPT_PROBED.iter().map(|f| f.to_string()))
        .collect();
    assert_eq!(listed, needed, "{TARGO_ALLOW_FEATURES}");
}
