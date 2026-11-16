#![cfg(any(target_os = "linux", target_os = "macos"))]

// Trust: `targo test --plan` builds several test requests in one graph. Each
// request must get the units its own `targo test -p ..` command gets.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::process::{Command, Output};

use serde_json::Value;

// Trust: under x.py the test process's RUSTC is bootstrap's wrapper, which
// needs bootstrap's environment; `env_clear` drops it. Bootstrap names a
// self-contained fixture shim directory for exactly this.
fn fixture_rustc() -> std::ffi::OsString {
    std::env::var_os("TEST_TRUST_SHIM_DIR")
        .map(|dir| Path::new(&dir).join("rustc").into_os_string())
        .or_else(|| std::env::var_os("RUSTC"))
        .expect("test requires an explicit compiler or bootstrap fixture shim")
}

fn targo(root: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target.noindex"))
        .env("RUSTC", fixture_rustc())
        .env("PATH", std::env::var_os("PATH").unwrap())
        .args(["--unverified", "test", "--offline"]);
    command
}

fn world(name: &str) -> tempfile::TempDir {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd")
        .join(format!("{name}.noindex"));
    fs::create_dir_all(&base).unwrap();
    tempfile::tempdir_in(base).unwrap()
}

fn write(root: &Path, path: &str, text: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn package(root: &Path, name: &str, manifest: &str, lib: &str) {
    write(
        root,
        &format!("{name}/Cargo.toml"),
        &format!("[package]\nname='{name}'\nversion='0.0.0'\nedition='2024'\n{manifest}"),
    );
    write(root, &format!("{name}/src/lib.rs"), lib);
}

/// The arguments of a plan run, with `--whole-plan` where they name no
/// change: an invocation says what it judges.
fn or_whole<'a>(arguments: &[&'a str]) -> Vec<&'a str> {
    let names_a_change = arguments.iter().any(|argument| {
        matches!(
            *argument,
            "-p" | "--changed-paths"
                | "--changed-range"
                | "--changed-pushed-refs"
                | "--reached"
                | "--whole-plan"
        )
    });
    let mut all = arguments.to_vec();
    if !names_a_change {
        all.push("--whole-plan");
    }
    all
}

/// The closing record of a run that ended without a verdict of its own (a
/// refusal, a failed build, a stop at the first failure): the short form,
/// with how the run ended and no row of the plan.
fn closed_without_verdict(record: Option<&Value>, outcome: &str, output: &Output) {
    let record = record.unwrap_or_else(|| panic!("no closing record: {}", text(output)));
    assert_eq!(record["reason"], "test-plan-result", "{}", text(output));
    assert_eq!(record["schema"], "targo.test-plan-result.v1");
    assert_eq!(record["outcome"], outcome, "{}", text(output));
    assert_eq!(record["passed"], false);
    assert_eq!(
        record["exit_status"].as_i64().map(|status| status as i32),
        output.status.code(),
        "{}",
        text(output)
    );
    assert!(!record["why"].as_str().unwrap().is_empty(), "{record}");
    assert!(record.get("requests").is_none(), "{record}");
    // The plan is spelled as every other record of the run spells it: from
    // the working directory, not as it was typed.
    assert!(
        Path::new(record["plan"].as_str().unwrap()).is_absolute(),
        "{record}"
    );
}

/// The one record on the standard output of a run refused before it wrote
/// anything else: its closing record.
fn refused_record(output: &Output) -> Value {
    let rows = stream(output);
    assert_eq!(rows.len(), 1, "{}", text(output));
    closed_without_verdict(rows.last(), "cannot-judge", output);
    rows[0].clone()
}

fn text(output: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn refusal(mut command: Command) -> String {
    let output = command.output().unwrap();
    assert!(!output.status.success(), "{}", text(&output));
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// A unit graph with each unit named by everything `--unit-graph` prints
/// about it and, transitively, about its dependencies. The printed graph
/// omits `dep_hash`, so two units that differ only below themselves are told
/// apart by this name and nothing else.
struct Graph {
    units: BTreeSet<String>,
    roots: Vec<String>,
}

fn unit_graph(mut command: Command) -> Graph {
    let output = command
        .args(["--unit-graph", "-Zunstable-options"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", text(&output));
    let graph: Value = serde_json::from_slice(&output.stdout).unwrap();
    let units = graph["units"].as_array().unwrap();
    fn name(index: usize, units: &[Value], names: &mut BTreeMap<usize, String>) -> String {
        if let Some(name) = names.get(&index) {
            return name.clone();
        }
        let mut own = units[index].clone();
        let dependencies = own["dependencies"]
            .as_array()
            .unwrap()
            .iter()
            .map(|dependency| {
                let mut edge = dependency.clone();
                let target = edge["index"].as_u64().unwrap() as usize;
                edge["index"] = Value::String(name(target, units, names));
                edge.to_string()
            })
            .collect::<BTreeSet<_>>();
        own["dependencies"] = dependencies.into_iter().collect();
        // A name of bounded size: the fields, and the names below by digest.
        let digest = {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            own["dependencies"].to_string().hash(&mut hasher);
            hasher.finish()
        };
        let mut shown = own.clone();
        shown["dependencies"] = Value::String(format!("{digest:016x}"));
        // Target name and features lead, for the fixture-shape checks.
        let named = format!("{} {} {}", own["target"]["name"], own["features"], shown);
        names.insert(index, named.clone());
        named
    }
    let mut names = BTreeMap::new();
    let all = (0..units.len())
        .map(|index| name(index, units, &mut names))
        .collect::<BTreeSet<_>>();
    assert_eq!(all.len(), units.len(), "two printed units share one name");
    let roots = graph["roots"]
        .as_array()
        .unwrap()
        .iter()
        .map(|root| names[&(root.as_u64().unwrap() as usize)].clone())
        .collect();
    Graph { units: all, roots }
}

fn difference(left: &BTreeSet<String>, right: &BTreeSet<String>) -> String {
    let only = |a: &BTreeSet<String>, b: &BTreeSet<String>| {
        a.difference(b).cloned().collect::<Vec<_>>().join("\n  ")
    };
    format!(
        "only in the plan:\n  {}\nonly standalone:\n  {}",
        only(left, right),
        only(right, left)
    )
}

/// The trust-lift / trust-machine-sem / trust-disasm shape, plus a member
/// tested under two feature sets and one another lane owns.
///
/// `zgen` has a build script and is reached two ways: as a normal dependency
/// of `lift` and `leaf`, and as `disasm`'s build dependency. Its build-script
/// run is one unit either way, with an edge that records the way it was
/// reached first: through the host in the default request, where `disasm`
/// sorts ahead of `zgen`, and never through the host in `router-ay`. That
/// record is not part of what gets built, and two requests may differ in it;
/// a union that compared it would refuse this plan.
///
/// `sem` is in `lift`'s closure and its dev-dependency turns on
/// `disasm/construct`. `targo test -p lift --lib` builds no dev unit of `sem`,
/// so its `disasm` has no features. A dependency resolve shared with a
/// request that selects `sem` carries that dev edge, and the feature resolver
/// walks it for every request.
fn parity_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['lift','sem','disasm','router','leaf','zgen','away']\nresolver='3'\n",
    );
    package(
        root,
        "lift",
        "[features]\nverify=[]\n[dependencies]\nsem={path='../sem'}\nzgen={path='../zgen'}\n",
        "pub fn lifted() -> bool { sem::constructed() && zgen::VALUE }\n#[test] fn t() {}\n",
    );
    package(
        root,
        "sem",
        "[dependencies]\ndisasm={path='../disasm'}\n\
         [dev-dependencies]\ndisasm={path='../disasm',features=['construct']}\n",
        "pub fn constructed() -> bool { disasm::CONSTRUCT }\n#[test] fn t() {}\n",
    );
    package(
        root,
        "disasm",
        "[features]\nconstruct=[]\n[build-dependencies]\nzgen={path='../zgen'}\n",
        "pub const CONSTRUCT: bool = cfg!(feature = \"construct\");\n#[test] fn t() {}\n",
    );
    write(
        root,
        "disasm/build.rs",
        "fn main() { let _ = zgen::VALUE; }\n",
    );
    package(
        root,
        "router",
        "[features]\nay=['leaf/deep']\ncertify=[]\n[dependencies]\nleaf={path='../leaf'}\n",
        "pub fn route() -> bool { leaf::DEEP }\n#[test] fn t() {}\n",
    );
    write(root, "router/tests/setter.rs", "#[test] fn t() {}\n");
    write(root, "router/tests/other.rs", "#[test] fn t() {}\n");
    write(root, "router/src/main.rs", "fn main() {}\n");
    package(
        root,
        "leaf",
        "[features]\ndeep=[]\n[dependencies]\nzgen={path='../zgen'}\n",
        "pub const DEEP: bool = cfg!(feature = \"deep\") && zgen::VALUE;\n#[test] fn t() {}\n",
    );
    package(
        root,
        "zgen",
        "",
        "pub const VALUE: bool = true;\n#[test] fn t() {}\n",
    );
    write(root, "zgen/build.rs", "fn main() {}\n");
    package(root, "away", "", "#[test] fn t() {}\n");
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[select.elsewhere]
away = "another lane"
[default]
targets = "tests"
[[variant]]
id = "lift-verify"
package = "lift"
features = ["verify"]
lib = true
[[variant]]
id = "router-ay"
package = "router"
features = ["ay"]
lib = true
[[variant]]
id = "router-certify"
package = "router"
features = ["ay", "certify"]
lib = true
[[variant]]
id = "router-setter"
package = "router"
features = ["ay"]
test = ["setter"]
[[instrument]]
id = "leaf-digest"
package = "leaf"
lib = true
args = ["t"]
[[instrument]]
id = "disasm-alone"
package = "disasm"
lib = true
"#,
    );
}

/// Each request of `parity_workspace`'s plan as the command a lane would run.
const STANDALONE: [(&str, &[&str]); 7] = [
    (
        "default",
        &[
            "-p", "lift", "-p", "sem", "-p", "disasm", "-p", "router", "-p", "leaf", "-p", "zgen",
            "--tests",
        ],
    ),
    (
        "lift-verify",
        &["-p", "lift", "--features", "verify", "--lib"],
    ),
    ("router-ay", &["-p", "router", "--features", "ay", "--lib"]),
    (
        "router-certify",
        &["-p", "router", "--features", "ay,certify", "--lib"],
    ),
    (
        "router-setter",
        &["-p", "router", "--features", "ay", "--test", "setter"],
    ),
    ("leaf-digest", &["-p", "leaf", "--lib"]),
    ("disasm-alone", &["-p", "disasm", "--lib"]),
];

fn host_triple() -> String {
    let output = Command::new(fixture_rustc()).arg("-vV").output().unwrap();
    assert!(output.status.success(), "{}", text(&output));
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("rustc -vV names its host")
        .to_owned()
}

#[test]
fn a_plan_request_gets_the_unit_graph_of_its_standalone_command() {
    let world = world("test-plan-parity");
    let root = world.path();
    parity_workspace(root);
    // Without `--target`, host and target units are one kind and build
    // dependencies are shared with normal ones; with it they are apart. The
    // plan decides which per request, as the standalone command does.
    parity(root, &[]);
    parity(root, &["--target", &host_triple()]);

    // Features unify per request whatever the configuration says: under
    // workspace-wide unification a request would see every member's features.
    let unified = [
        "-Zfeature-unification",
        "--config",
        "resolver.feature-unification=\"workspace\"",
    ];
    // `lift-verify` is the request another member's dev-dependency would
    // change; `leaf-digest` one that nothing would.
    for (id, arguments) in STANDALONE {
        if !["lift-verify", "leaf-digest"].contains(&id) {
            continue;
        }
        let mut standalone = targo(root);
        standalone.args(arguments);
        let mut request = targo(root);
        request
            .args(["--plan", "plan.toml", "--whole-plan", "--request", id])
            .args(unified);
        assert!(
            unit_graph(request).units == unit_graph(standalone).units,
            "request `{id}` under workspace feature unification"
        );
    }

    // The default request links bin `router` without features and
    // `router-setter` links it against `leaf` with `deep`, both to
    // `debug/router`. The graph is right; the build is refused, before
    // anything compiles.
    let mut build = targo(root);
    build.args(["--plan", "plan.toml", "--whole-plan", "--no-run"]);
    let message = refusal(build);
    assert!(
        message.contains("builds bin \"router\" of package `router` two ways into one file")
            && message.contains("request `default` builds it")
            && message.contains("request `router-setter` builds it")
            && !message.contains("Compiling"),
        "{message}"
    );
}

fn parity(root: &Path, extra: &[&str]) {
    let mut union = BTreeSet::new();
    let mut union_roots = BTreeSet::new();
    let mut lift_roots = Vec::new();
    for (id, arguments) in STANDALONE {
        let mut standalone = targo(root);
        standalone.args(arguments).args(extra);
        let standalone = unit_graph(standalone);
        let mut request = targo(root);
        request
            .args(["--plan", "plan.toml", "--whole-plan", "--request", id])
            .args(extra);
        let request = unit_graph(request);
        assert!(
            request.units == standalone.units,
            "request `{id}` differs from its standalone command ({extra:?})\n{}",
            difference(&request.units, &standalone.units)
        );
        assert_eq!(request.roots, standalone.roots, "roots of request `{id}`");
        if id == "lift-verify" {
            lift_roots = standalone.roots.clone();
        }
        union.extend(standalone.units);
        union_roots.extend(standalone.roots);
    }

    let mut plan = targo(root);
    plan.args(["--plan", "plan.toml", "--whole-plan"])
        .args(extra);
    let plan = unit_graph(plan);
    assert!(
        plan.units == union,
        "the plan's graph is not the union of its requests' standalone graphs\n{}",
        difference(&plan.units, &union)
    );
    // A root two requests share is one unit, built and listed once.
    let roots = plan.roots.iter().cloned().collect::<BTreeSet<_>>();
    assert_eq!(roots.len(), plan.roots.len(), "a root is listed twice");
    assert_eq!(roots, union_roots);

    // The fixture has the shape that tells a shared dependency resolve from
    // one per request: `disasm` with and without the feature only `sem`'s
    // dev-dependency names, and the featureless one below `lift-verify`.
    let disasm = |features: &str| {
        plan.units
            .iter()
            .filter(|unit| unit.starts_with(&format!("\"disasm\" {features} ")))
            .count()
    };
    assert!(disasm("[\"construct\"]") > 0 && disasm("[]") > 0);
    // A unit's name covers everything below it, so the standalone root being
    // a root of the whole plan says `lift-verify` kept its featureless
    // `disasm` beside the default request's.
    assert_eq!(lift_roots.len(), 1);
    assert!(
        roots.contains(&lift_roots[0]),
        "`lift-verify` got a feature that only another member's dev-dependency enables"
    );
    // `leaf-digest` selects the default request's own `leaf` test; `router-ay`
    // and `router-setter` build `leaf` with a feature the default run lacks.
    assert!(
        plan.units
            .iter()
            .any(|unit| unit.starts_with("\"leaf\" [\"deep\"] "))
    );
}

/// `left` and `right` both depend on `shared`, which depends on `core`; only
/// `left` turns on `core/flag`. Before `dep_hash` is filled in, `shared` is
/// one unit key with two dependency lists.
fn overwrite_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['left','right','shared','core']\nresolver='3'\n",
    );
    package(
        root,
        "left",
        "[dependencies]\nshared={path='../shared'}\ncore={path='../core',features=['flag']}\n",
        "#[test] fn shared_sees_the_flag() { assert!(core::FLAG); assert!(shared::flag()); }\n",
    );
    package(
        root,
        "right",
        "[dependencies]\nshared={path='../shared'}\n",
        "#[test] fn shared_sees_no_flag() { assert!(!shared::flag()); }\n",
    );
    package(
        root,
        "shared",
        "[dependencies]\ncore={path='../core'}\n",
        "pub fn flag() -> bool { core::FLAG }\n",
    );
    package(
        root,
        "core",
        "[features]\nflag=[]\n",
        "pub const FLAG: bool = cfg!(feature = \"flag\");\n",
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[[variant]]
id = "left"
package = "left"
lib = true
[[variant]]
id = "right"
package = "right"
lib = true
"#,
    );
}

#[test]
fn a_crate_two_requests_share_is_built_against_each_requests_features() {
    let world = world("test-plan-overwrite");
    let root = world.path();
    overwrite_workspace(root);

    let output = targo(root)
        .args([
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--no-run",
            "--message-format=json",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", text(&output));
    let artifacts = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect::<Vec<_>>();
    // One `shared` and one `core` per request, in distinct files.
    for name in ["shared", "core"] {
        let files = artifacts
            .iter()
            .filter(|row| row["target"]["name"] == name)
            .map(|row| row["filenames"].to_string())
            .collect::<BTreeSet<_>>();
        assert_eq!(files.len(), 2, "{name}: {files:?}");
    }
    let harness = |name: &str| {
        let found = artifacts
            .iter()
            .filter(|row| row["target"]["name"] == name && row["profile"]["test"] == true)
            .filter_map(|row| row["executable"].as_str())
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "{name}: {found:?}");
        found[0].to_owned()
    };
    // Each harness asserts the `cfg` its own request gives `core`, both
    // directly and through `shared`.
    for (name, test) in [
        ("left", "shared_sees_the_flag"),
        ("right", "shared_sees_no_flag"),
    ] {
        let output = Command::new(harness(name)).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.contains(&format!("test {test} ... ok")),
            "{name}: {}",
            text(&output)
        );
    }
}

/// A bin and the integration test that runs it, under two feature sets. The
/// bin prints whether it has the feature; the test asserts that the bin it
/// was handed agrees with its own `cfg`.
fn two_way_bin_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['a']\nresolver='3'\n",
    );
    package(root, "a", "[features]\nf=[]\n", "");
    write(
        root,
        "a/src/bin/a.rs",
        "fn main() { print!(\"{}\", cfg!(feature = \"f\")); }\n",
    );
    write(
        root,
        "a/tests/it.rs",
        "#[test] fn the_bin_is_this_requests() {\n\
         let out = std::process::Command::new(env!(\"CARGO_BIN_EXE_a\")).output().unwrap();\n\
         assert_eq!(String::from_utf8(out.stdout).unwrap(), cfg!(feature = \"f\").to_string());\n\
         }\n",
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
[[variant]]
id = "a-f"
package = "a"
features = ["f"]
test = ["it"]
"#,
    );
}

#[test]
fn one_bin_built_two_ways_into_one_file_is_refused_with_both_requests() {
    let world = world("test-plan-two-way-bin");
    let root = world.path();
    two_way_bin_workspace(root);

    let mut both = targo(root);
    both.args(["--plan", "plan.toml", "--whole-plan", "--no-run"]);
    let message = refusal(both);
    let linked = root.join("target.noindex").join("debug").join("a");
    assert!(
        message.contains("plan.toml` builds bin \"a\" of package `a` two ways into one file, `")
            && message.contains("request `default` builds it with features []")
            && message.contains("request `a-f` builds it with features [f]"),
        "{message}"
    );
    // Refused before anything is compiled or linked.
    assert!(!message.contains("Compiling"), "{message}");
    assert!(!linked.exists());

    // Either request alone builds, and its test gets its own bin.
    for (id, has_feature) in [("a-f", "true"), ("default", "false")] {
        let output = targo(root)
            .args(["--plan", "plan.toml", "--whole-plan", "--request", id])
            .args(["--no-run", "--message-format=json"])
            .output()
            .unwrap();
        assert!(output.status.success(), "{id}: {}", text(&output));
        let harness = String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
            .filter(|row| row["reason"] == "compiler-artifact" && row["target"]["name"] == "it")
            .find_map(|row| row["executable"].as_str().map(str::to_owned))
            .expect("the request builds `it`");
        let bin = Command::new(&linked).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&bin.stdout), has_feature, "{id}");
        let output = Command::new(harness).output().unwrap();
        assert!(output.status.success(), "{id}: {}", text(&output));
    }
}

/// One lib whose tests sit in two modules, selected by four requests: two
/// instruments with different filters, a third instrument repeating the
/// first one's filter, and a variant under a feature.
///
/// Every test takes the package's one lock for as long as it runs, and fails
/// when the lock is already held: two processes of this lib's tests running
/// together fail here, whatever the scheduler reported. The variant's
/// executable is another file, but it is the same tests writing the same
/// files in the same package directory, so it takes the same lock.
fn filters_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "[features]\nflag=[]\n",
        r#"
#[cfg(test)]
fn alone(name: &str) {
    let lock = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lock");
    std::fs::create_dir(&lock)
        .unwrap_or_else(|error| panic!("{name}: these tests are already running: {error}"));
    std::thread::sleep(std::time::Duration::from_millis(400));
    std::fs::remove_dir(&lock).unwrap();
}
#[cfg(test)]
mod alpha {
    #[test] fn one() { super::alone("alpha::one") }
    #[test] fn two() { super::alone("alpha::two") }
}
#[cfg(test)]
mod beta {
    #[test] fn one() { super::alone("beta::one") }
}
#[cfg(feature = "flag")]
#[test] fn flagged() { alone("flagged") }
"#,
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[[instrument]]
id = "alpha"
package = "host"
lib = true
args = ["alpha::"]
[[instrument]]
id = "beta"
package = "host"
lib = true
args = ["beta::"]
[[instrument]]
id = "alpha-again"
package = "host"
lib = true
args = ["alpha::"]
[[variant]]
id = "flagged"
package = "host"
features = ["flag"]
lib = true
"#,
    );
}

/// What one invocation said about its test actions, from its JSON records.
struct Run {
    output: Output,
    /// Every `test-execution` record, in the order written.
    records: Vec<Value>,
    /// Each action's `test <name> ... <result>` lines, by action index.
    tests: BTreeMap<u64, BTreeSet<String>>,
    /// The `test-plan-result` record, which is the last line when present.
    result: Option<Value>,
}

impl Run {
    /// The action whose `requests` are exactly `requests`.
    fn action(&self, requests: &[&str]) -> u64 {
        let found = self
            .records
            .iter()
            .filter(|row| row["requests"] == serde_json::json!(requests))
            .map(|row| row["index"].as_u64().unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(found.len(), 1, "{requests:?}: {}", text(&self.output));
        *found.first().unwrap()
    }

    /// Where action `index`'s record in `state` is in the record stream.
    fn at(&self, index: u64, state: &str) -> Option<usize> {
        self.records
            .iter()
            .position(|row| row["index"] == index && row["state"] == state)
    }

    fn terminal(&self, index: u64) -> &Value {
        let found = self
            .records
            .iter()
            .filter(|row| {
                row["index"] == index
                    && ["passed", "failed", "blocked"].contains(&row["state"].as_str().unwrap())
            })
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "action {index}: {}", text(&self.output));
        found[0]
    }

    fn ran(&self, index: u64) -> Vec<&str> {
        self.tests
            .get(&index)
            .map(|lines| lines.iter().map(String::as_str).collect())
            .unwrap_or_default()
    }
}

fn run(root: &Path, arguments: &[&str]) -> Run {
    // The fixtures count on every credit of the pool; see SERIAL_FRONTEND in
    // test_scheduling.rs.
    let output = targo(root)
        .env("RUSTFLAGS", "-Zthreads=1")
        .args(["--message-format=json"])
        .args(arguments)
        .output()
        .unwrap();
    let rows = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .collect::<Vec<_>>();
    let mut tests: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for row in rows.iter().filter(|row| row["reason"] == "test-output") {
        let line = row["line"].as_str().unwrap();
        if line.starts_with("test ") && line.contains(" ... ") {
            let fresh = tests
                .entry(row["index"].as_u64().unwrap())
                .or_default()
                .insert(line.to_owned());
            assert!(fresh, "{line} was reported twice by one action");
        }
    }
    let results = rows
        .iter()
        .filter(|row| row["reason"] == "test-plan-result")
        .count();
    let result = rows
        .last()
        .filter(|row| row["reason"] == "test-plan-result")
        .cloned();
    assert_eq!(
        results,
        usize::from(result.is_some()),
        "a plan's result is written once, last: {}",
        text(&output)
    );
    let records = rows
        .into_iter()
        .filter(|row| row["reason"] == "test-execution")
        .collect();
    Run {
        output,
        records,
        tests,
        result,
    }
}

/// A terminal record's `tests`: passed, failed, ignored, filtered out.
fn counts(passed: u64, failed: u64, ignored: u64, filtered_out: u64) -> Value {
    serde_json::json!({
        "passed": passed,
        "failed": failed,
        "ignored": ignored,
        "filtered_out": filtered_out,
    })
}

/// The keys of a v2 record, and those v3 adds.
const V2_KEYS: [&str; 16] = [
    "reason",
    "schema",
    "index",
    "total",
    "prerequisite_artifact",
    "package_id",
    "package",
    "target",
    "kind",
    "harness",
    "weight",
    "exclusive",
    "state",
    "elapsed_ms",
    "exit_code",
    "signal",
];
const V3_KEYS: [&str; 6] = [
    "requests",
    "features",
    "args",
    "memory_mib",
    "expected_seconds",
    "tests",
];

fn keys(row: &Value) -> BTreeSet<&str> {
    row.as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect()
}

#[test]
fn requests_on_one_lib_each_run_their_own_filter_and_never_together() {
    let world = world("test-plan-filters");
    let root = world.path();
    filters_workspace(root);
    let both_alpha = ["test alpha::one ... ok", "test alpha::two ... ok"];

    // Four credits and three actions: nothing but the same-target order
    // keeps the three runs of the lib apart.
    let parallel = run(
        root,
        &[
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--no-fail-fast",
            "-j4",
            "--config",
            "build.test-jobs=4",
        ],
    );
    assert!(
        parallel.output.status.success(),
        "{}",
        text(&parallel.output)
    );
    let alpha = parallel.action(&["alpha", "alpha-again"]);
    let beta = parallel.action(&["beta"]);
    let flagged = parallel.action(&["flagged"]);
    // Requests with one argument list share one action; that is all of them.
    let indices = parallel
        .records
        .iter()
        .map(|row| row["index"].as_u64().unwrap())
        .collect::<BTreeSet<_>>();
    assert_eq!(indices, BTreeSet::from([alpha, beta, flagged]));

    // Each action ran its own filter and nothing else.
    assert_eq!(parallel.ran(alpha), both_alpha);
    assert_eq!(parallel.ran(beta), ["test beta::one ... ok"]);
    assert_eq!(
        parallel.ran(flagged),
        [
            "test alpha::one ... ok",
            "test alpha::two ... ok",
            "test beta::one ... ok",
            "test flagged ... ok"
        ]
    );

    // Every record is v3 with the closed v3 key set, and says what ran.
    for row in &parallel.records {
        assert_eq!(row["schema"], "targo.test-execution.v3", "{row}");
        let expected = V2_KEYS.into_iter().chain(V3_KEYS).collect::<BTreeSet<_>>();
        assert_eq!(keys(row), expected, "{row}");
        assert_eq!(row["total"], 3, "{row}");
        assert_eq!(row["package"], "host", "{row}");
        // An action's tests are counted when it ends.
        if row["state"] != "passed" {
            assert_eq!(row["tests"], Value::Null, "{row}");
        }
    }
    for (index, args, features, tests) in [
        (alpha, &["alpha::"][..], &[][..], counts(2, 0, 0, 1)),
        (beta, &["beta::"], &[], counts(1, 0, 0, 2)),
        (flagged, &[], &["flag"], counts(4, 0, 0, 0)),
    ] {
        let row = parallel.terminal(index);
        assert_eq!(row["tests"], tests, "{row}");
        assert_eq!(row["state"], "passed", "{row}");
        assert_eq!(row["exit_code"], 0, "{row}");
        assert_eq!(row["args"], serde_json::json!(args), "{row}");
        assert_eq!(row["features"], serde_json::json!(features), "{row}");
    }

    // The two filtered runs are one file; the variant's is another.
    let artifact = |index| parallel.terminal(index)["prerequisite_artifact"].clone();
    assert_eq!(artifact(alpha), artifact(beta));
    assert_ne!(artifact(alpha), artifact(flagged));
    // Each of the three ended before the next was started, the variant's
    // other executable included.
    let mut order = [alpha, beta, flagged];
    order.sort_unstable();
    for pair in order.windows(2) {
        let (first, second) = (pair[0], pair[1]);
        let ended = parallel.at(first, "passed").unwrap();
        for state in ["ready", "running"] {
            assert!(
                ended < parallel.at(second, state).unwrap(),
                "action {second} was {state} before action {first} ended: {}",
                text(&parallel.output)
            );
        }
    }

    // Without JSON, each `Running` line says which requests the run is for:
    // two runs of one executable print the same path.
    let human = targo(root)
        .env("RUSTFLAGS", "-Zthreads=1")
        .args(["--plan", "plan.toml", "--whole-plan"])
        .output()
        .unwrap();
    assert!(human.status.success(), "{}", text(&human));
    let stderr = String::from_utf8_lossy(&human.stderr);
    let running = stderr
        .lines()
        .filter(|line| line.trim_start().starts_with("Running "))
        .map(|line| line.rsplit_once(") ").map_or("", |(_, requests)| requests))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        running,
        BTreeSet::from(["[alpha, alpha-again]", "[beta]", "[flagged]"]),
        "{stderr}"
    );

    // A plan runs in the graph whatever `build.test-jobs` says: the
    // sequential runner has one argument list and writes no record.
    let serial = run(root, &["--plan", "plan.toml", "--whole-plan"]);
    assert!(serial.output.status.success(), "{}", text(&serial.output));
    assert_eq!(
        serial.ran(serial.action(&["alpha", "alpha-again"])),
        both_alpha
    );
    assert_eq!(
        serial.ran(serial.action(&["beta"])),
        ["test beta::one ... ok"]
    );
    assert_eq!(serial.ran(serial.action(&["flagged"])).len(), 4);

    // `--request` narrows the run, and the action credits what is left.
    let narrowed = run(
        root,
        &[
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--request",
            "alpha-again",
        ],
    );
    assert!(
        narrowed.output.status.success(),
        "{}",
        text(&narrowed.output)
    );
    assert_eq!(narrowed.ran(narrowed.action(&["alpha-again"])), both_alpha);
    assert!(narrowed.records.iter().all(|row| row["total"] == 1));

    // Without a plan the same executable's records are v2, key for key, and
    // the invocation's arguments still reach the harness.
    let plain = run(
        root,
        &[
            "-p",
            "host",
            "--lib",
            "--config",
            "build.test-jobs=2",
            "--",
            "beta::",
        ],
    );
    assert!(plain.output.status.success(), "{}", text(&plain.output));
    assert!(!plain.records.is_empty());
    for row in &plain.records {
        assert_eq!(row["schema"], "targo.test-execution.v2", "{row}");
        assert_eq!(keys(row), V2_KEYS.into_iter().collect(), "{row}");
    }
    assert_eq!(plain.ran(0), ["test beta::one ... ok"]);
}

/// Two requests on one lib, the first of which fails.
fn failing_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "",
        "#[cfg(test)] mod first { #[test] fn bad() { panic!(\"first fails\") } }\n\
         #[cfg(test)] mod second { #[test] fn good() {} }\n",
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[[instrument]]
id = "first"
package = "host"
lib = true
args = ["first::"]
[[instrument]]
id = "second"
package = "host"
lib = true
args = ["second::"]
"#,
    );
}

#[test]
fn a_failed_run_of_an_executable_releases_the_next_unless_it_stops_the_run() {
    let world = world("test-plan-failed-first");
    let root = world.path();
    failing_workspace(root);
    let jobs = ["-j2", "--config", "build.test-jobs=2"];

    // `--no-fail-fast`: the failure is one action's, and the action queued
    // behind it on the same executable still runs.
    let mut arguments = vec!["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"];
    arguments.extend(jobs);
    let kept = run(root, &arguments);
    assert!(!kept.output.status.success(), "{}", text(&kept.output));
    let (first, second) = (kept.action(&["first"]), kept.action(&["second"]));
    assert_eq!(kept.terminal(first)["state"], "failed");
    assert_eq!(kept.terminal(first)["exit_code"], 101);
    assert_eq!(kept.terminal(second)["state"], "passed");
    assert_eq!(kept.ran(first), ["test first::bad ... FAILED"]);
    assert_eq!(kept.ran(second), ["test second::good ... ok"]);
    assert!(
        kept.at(first, "failed").unwrap() < kept.at(second, "running").unwrap(),
        "{}",
        text(&kept.output)
    );
    // The failure is reported by the request that reruns it, not by flags
    // that would drop the request's arguments.
    let stderr = String::from_utf8_lossy(&kept.output.stderr);
    assert!(
        stderr.contains("test failed, to rerun pass `--plan ")
            && stderr.contains("plan.toml --request first`")
            && stderr.contains("1 target failed:\n    `--plan "),
        "{stderr}"
    );
    // A request may cover many targets, so the failed one is named too.
    assert!(
        stderr.contains("error: lib of `host`: test failed, to rerun pass `--plan ")
            && stderr.contains("plan.toml --request first` (lib of `host`)\n"),
        "{stderr}"
    );
    assert!(!stderr.contains("--request second"), "{stderr}");
    assert!(!stderr.contains("-p host"), "{stderr}");

    // Fail-fast: the failure stops the run, and the action behind it is
    // reported as never run.
    let mut arguments = vec!["--plan", "plan.toml", "--whole-plan"];
    arguments.extend(jobs);
    let stopped = run(root, &arguments);
    assert_eq!(stopped.output.status.code(), Some(101));
    let (first, second) = (stopped.action(&["first"]), stopped.action(&["second"]));
    assert_eq!(stopped.terminal(first)["state"], "failed");
    assert_eq!(stopped.terminal(second)["state"], "blocked");
    assert!(stopped.ran(second).is_empty());
    assert!(stopped.at(second, "running").is_none());
}

/// A failing test prints one line of 2 MiB, twice the limit on a harness
/// line. The harness is not stopped for it: the line is cut, and the action
/// is judged by what its tests reported, as a runner with no limit judges it.
#[test]
fn a_long_output_line_is_cut_and_its_harness_reports_every_test() {
    let world = world("test-plan-long-line");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "",
        "#[test] fn long() { println!(\"{}\", \"x\".repeat(2 * 1024 * 1024)); panic!(\"no\") }\n\
         #[test] fn fine() {}\n",
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
"#,
    );
    let failed = run(
        root,
        &["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"],
    );
    assert_eq!(
        failed.output.status.code(),
        Some(101),
        "{}",
        text(&failed.output)
    );
    let action = failed.action(&["default"]);
    let host = failed.terminal(action);
    // The failure is the test's own: its exit and its counts are recorded.
    assert_eq!(host["state"], "failed");
    assert_eq!(host["exit_code"], 101);
    assert_eq!(host["tests"]["passed"], 1);
    assert_eq!(host["tests"]["failed"], 1);
    // The long line is one record, cut to the limit behind its mark.
    let mark = "[line cut: it is longer than 1048576 bytes] ";
    let stdout = String::from_utf8_lossy(&failed.output.stdout);
    let lines: Vec<Value> = stdout
        .lines()
        .filter_map(|row| serde_json::from_str::<Value>(row).ok())
        .filter(|row| row["reason"] == "test-output" && row["index"] == action)
        .collect();
    let cut: Vec<&str> = lines
        .iter()
        .filter_map(|row| row["line"].as_str())
        .filter(|line| line.len() > 1024)
        .collect();
    assert_eq!(cut.len(), 1, "{}", text(&failed.output));
    assert_eq!(cut[0].len(), 1024 * 1024);
    assert_eq!(
        cut[0]
            .strip_prefix(mark)
            .map(|rest| rest.bytes().all(|b| b == b'x')),
        Some(true)
    );
    let stderr = String::from_utf8_lossy(&failed.output.stderr);
    assert!(
        stderr.contains("error: lib of `host`: test failed, to rerun pass `--plan ")
            && !stderr.contains("safety limit"),
        "{stderr}"
    );
    assert!(!stderr.contains("test exited abnormally"), "{stderr}");
    assert_eq!(failed.result.as_ref().unwrap()["passed"], false);
}

/// One package whose lib test fails, selected by `[default]` and by a variant
/// with no feature: one action for both. The plan is in a directory whose
/// name a shell would split.
#[test]
fn a_failure_is_reported_by_its_target_and_a_pasteable_narrowest_request() {
    let world = world("test-plan-hint");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host','other']\nresolver='3'\n",
    );
    package(root, "host", "", "#[test] fn bad() { panic!(\"no\") }\n");
    package(root, "other", "", "#[test] fn good() {}\n");
    write(
        root,
        "a dir/plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
[[variant]]
id = "host-again"
package = "host"
lib = true
"#,
    );
    let failed = run(
        root,
        &[
            "--plan",
            "a dir/plan.toml",
            "--whole-plan",
            "--no-fail-fast",
        ],
    );
    assert!(!failed.output.status.success(), "{}", text(&failed.output));
    let host = failed.action(&["default", "host-again"]);
    assert_eq!(failed.terminal(host)["state"], "failed");
    assert_eq!(
        failed.terminal(failed.action(&["default"]))["state"],
        "passed"
    );
    let stderr = String::from_utf8_lossy(&failed.output.stderr);
    // `--request default` would rerun `other` too; the path is one word.
    let hint = "a dir/plan.toml' --request host-again`";
    assert!(
        stderr.contains("error: lib of `host`: test failed, to rerun pass `--plan '")
            && stderr.contains(hint)
            && stderr.contains(&format!("{hint} (lib of `host`)\n")),
        "{stderr}"
    );
    assert!(!stderr.contains("--request default"), "{stderr}");
}

/// An instrument judges something outside its host package, so a run of it
/// that judged no test is a failure, though the harness exits 0.
#[test]
fn an_instrument_that_judges_no_test_fails() {
    let world = world("test-plan-judged");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "[[test]]\nname='plain'\nharness=false\n",
        "#[cfg(test)] mod real { #[test] fn one() {} }\n\
         #[cfg(test)] mod slow { #[test] #[ignore] fn two() {} }\n",
    );
    write(root, "host/tests/plain.rs", "fn main() {}\n");
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[[instrument]]
id = "nomatch"
package = "host"
lib = true
args = ["zzz_no_such_test"]
[[instrument]]
id = "ignored"
package = "host"
lib = true
args = ["slow::"]
[[instrument]]
id = "real"
package = "host"
lib = true
args = ["real::"]
[[instrument]]
id = "plain"
package = "host"
test = ["plain"]
[[variant]]
id = "filtered-variant"
package = "host"
test = ["plain"]
"#,
    );
    let judged = run(
        root,
        &["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"],
    );
    assert_eq!(
        judged.output.status.code(),
        Some(101),
        "{}",
        text(&judged.output)
    );
    let stderr = String::from_utf8_lossy(&judged.output.stderr);
    for id in ["nomatch", "ignored"] {
        let row = judged.terminal(judged.action(&[id]));
        // The harness exited 0 by itself; Targo judged the run.
        assert_eq!(row["state"], "failed", "{row}");
        assert_eq!(row["exit_code"], 0, "{row}");
        // The harness closed its run with nothing judged.
        let tests = if id == "nomatch" {
            counts(0, 0, 0, 2)
        } else {
            counts(0, 0, 1, 1)
        };
        assert_eq!(row["tests"], tests, "{row}");
        assert!(
            stderr.contains(&format!("instrument `{id}` reported no passing tests")),
            "{stderr}"
        );
        assert!(
            stderr.contains(&format!("plan.toml --request {id}` (lib of `host`)")),
            "{stderr}"
        );
    }
    assert!(stderr.contains("2 targets failed:"), "{stderr}");
    assert_eq!(judged.terminal(judged.action(&["real"]))["state"], "passed");
    // An unharnessed target prints no summary: its exit is its verdict, and
    // the instrument shares the variant's action.
    let plain = judged.terminal(judged.action(&["filtered-variant", "plain"]));
    assert_eq!(plain["state"], "passed", "{plain}");
    assert_eq!(plain["harness"], false, "{plain}");
    // It counts as one test, judged by that exit.
    assert_eq!(plain["tests"], counts(1, 0, 0, 0), "{plain}");
}

/// One member whose test targets end every way a plan run tells apart.
fn counting_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "[[test]]\nname='plain'\nharness=false\n[[test]]\nname='plain_fails'\nharness=false\n",
        "#[cfg(test)] mod unit {\n\
         #[test] fn one() {}\n\
         #[test] fn two() {}\n\
         #[test] #[ignore] fn later() {}\n\
         }\n",
    );
    write(root, "host/tests/plain.rs", "fn main() {}\n");
    write(
        root,
        "host/tests/plain_fails.rs",
        "fn main() { std::process::exit(3) }\n",
    );
    write(
        root,
        "host/tests/fails.rs",
        "#[test] fn holds() {}\n#[test] fn breaks() { panic!(\"broken\") }\n",
    );
    // Exits 0 from inside a test: libtest never closes the run, and the two
    // tests after it in name order are never judged.
    write(
        root,
        "host/tests/quits.rs",
        "#[test] fn a_quits() { std::process::exit(0) }\n\
         #[test] fn b_unjudged() { panic!(\"never reached\") }\n\
         #[test] fn c_unjudged() {}\n",
    );
    // Prints a closing line of its own and exits 0 with a failure counted.
    write(
        root,
        "host/tests/claims.rs",
        r#"#[test] fn claims() {
    use std::io::Write as _;
    // Written past libtest's capture, as a child process's output would be.
    std::io::stdout()
        .write_all(b"\ntest result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n")
        .unwrap();
    std::process::exit(0)
}
"#,
    );
    // Prints an `ok` closing line of its own and exits 0 before libtest judged
    // the second of the two tests it announced.
    write(
        root,
        "host/tests/forges.rs",
        r#"#[test] fn a_forges() {
    use std::io::Write as _;
    std::io::stdout()
        .write_all(b"\ntest result: ok. 7 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n")
        .unwrap();
    std::process::exit(0)
}
#[test] fn z_unjudged() { panic!("never reached") }
"#,
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
"#,
    );
}

/// Each terminal record carries what its harness reported, an exit of 0 is
/// held to libtest's closing line, a `harness = false` target counts as one
/// test, and the run ends with one `test-plan-result` record.
#[test]
fn a_run_counts_what_each_harness_reported_and_holds_exit_0_to_its_closing_line() {
    let world = world("test-plan-counts");
    let root = world.path();
    counting_workspace(root);
    let counted = run(
        root,
        &[
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--no-fail-fast",
            "--config",
            "build.test-jobs=1",
        ],
    );
    assert_eq!(
        counted.output.status.code(),
        Some(101),
        "{}",
        text(&counted.output)
    );
    let stderr = String::from_utf8_lossy(&counted.output.stderr);
    let terminal = |target: &str| {
        let found = counted
            .records
            .iter()
            .filter(|row| row["target"] == target && row["elapsed_ms"] != Value::Null)
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "{target}: {}", text(&counted.output));
        found[0]
    };
    for (target, state, exit_code, tests) in [
        ("host", "passed", 0, counts(2, 0, 1, 0)),
        ("plain", "passed", 0, counts(1, 0, 0, 0)),
        ("plain_fails", "failed", 3, counts(0, 1, 0, 0)),
        ("fails", "failed", 101, counts(1, 1, 0, 0)),
        // No count stands where the exit and the closing line disagree.
        ("quits", "failed", 0, Value::Null),
        ("claims", "failed", 0, Value::Null),
        // Nor on an `ok` line that does not close the run libtest announced.
        ("forges", "failed", 0, Value::Null),
    ] {
        let row = terminal(target);
        assert_eq!(row["state"], state, "{row}");
        assert_eq!(row["exit_code"], exit_code, "{row}");
        assert_eq!(row["tests"], tests, "{row}");
    }
    // Before an action ends nothing is counted.
    for row in &counted.records {
        if row["elapsed_ms"] == Value::Null {
            assert_eq!(row["tests"], Value::Null, "{row}");
        }
    }
    assert!(
        stderr.contains(
            "the test harness exited 0 without libtest's closing `test result: ok.` line: it \
             ended mid-run"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("the test harness exited 0 after a closing `test result: FAILED.` line"),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "the test harness exited 0 with a closing `test result: ok.` line that does not \
             close its own run: it accounts for 7 tests and the harness announced `running 2 \
             tests`"
        ),
        "{stderr}"
    );
    assert!(stderr.contains("5 targets failed:"), "{stderr}");

    let result = counted.result.as_ref().expect("a test-plan-result record");
    let plan = result["plan"].as_str().unwrap();
    assert!(Path::new(plan).ends_with("plan.toml"), "{result}");
    assert_eq!(
        *result,
        serde_json::json!({
            "reason": "test-plan-result",
            "schema": "targo.test-plan-result.v1",
            "plan": plan,
            "phase": null,
            "passed": false,
            "outcome": "failed",
            "exit_status": 101,
            "narrowed": false,
            "min_tests_skipped": false,
            "requests": [{
                "id": "default",
                "actions": 7,
                "failed": 5,
                "excused": 0,
                // 2 + 1 + 1 + 2, and nothing for the three that disagreed.
                "tests": 6,
                "passed": false,
            }],
            "members": [],
            "unmet": [],
            "known_red": null,
            "phases": [],
        }),
        "{}",
        text(&counted.output)
    );

    // A run that stops at its first failure has no verdict to record.
    let stopped = run(
        root,
        &[
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--config",
            "build.test-jobs=1",
        ],
    );
    assert_eq!(stopped.output.status.code(), Some(101));
    closed_without_verdict(stopped.result.as_ref(), "failed", &stopped.output);
}

/// `seen` has a test; `hidden`'s only test is behind feature `f`, so the
/// default run compiles it out and reports `running 0 tests`.
fn hidden_tests_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['seen', 'hidden']\nresolver='3'\n",
    );
    package(root, "seen", "", "#[test] fn seen() {}\n");
    package(
        root,
        "hidden",
        "[features]\nf=[]\ng=[]\n",
        "#[cfg(feature = \"f\")]\n#[test] fn behind_f() {}\n",
    );
    let default = "schema = \"targo.test-plan.v1\"\n\
                   [select]\nmembers = \"default-members\"\n\
                   [default]\ntargets = \"tests\"\n";
    let variant = "[[variant]]\nid = \"hidden-f\"\npackage = \"hidden\"\n\
                   features = [\"f\"]\nlib = true\n";
    // An instrument judges something outside its host: it credits no member.
    let instrument = "[[instrument]]\nid = \"probe\"\npackage = \"seen\"\nlib = true\n\
                      args = [\"seen\"]\n";
    write(root, "unjudged.toml", default);
    write(root, "plan.toml", &format!("{default}min-tests = 1\n"));
    write(
        root,
        "with-variant.toml",
        &format!("{default}min-tests = 1\n{variant}"),
    );
    write(
        root,
        "two.toml",
        &format!("{default}min-tests = 2\n{variant}{instrument}"),
    );
    // A variant whose feature compiles no test in.
    let empty = "[[variant]]\nid = \"hidden-g\"\npackage = \"hidden\"\n\
                 features = [\"g\"]\nlib = true\n";
    write(
        root,
        "empty-variant.toml",
        &format!("{default}min-tests = 1\n{variant}{empty}"),
    );
}

/// A member whose tests sit behind a feature no request enables exits 0 on
/// `running 0 tests`; `min-tests` fails the run, and a variant that enables
/// the feature credits the member.
#[test]
fn a_member_that_reports_fewer_tests_than_min_tests_fails_the_run() {
    let world = world("test-plan-min-tests");
    let root = world.path();
    hidden_tests_workspace(root);
    let member = |run: &Run, package: &str| {
        let members = run.result.as_ref().expect("a result record")["members"]
            .as_array()
            .unwrap()
            .clone();
        members
            .into_iter()
            .find(|row| row["package"] == package)
            .unwrap_or_else(|| panic!("no member row for {package}: {}", text(&run.output)))
    };

    // Without `min-tests` the plan asks nothing of the member, and passes.
    let unjudged = run(
        root,
        &["--plan", "unjudged.toml", "--whole-plan", "--no-fail-fast"],
    );
    assert!(
        unjudged.output.status.success(),
        "{}",
        text(&unjudged.output)
    );
    let result = unjudged.result.as_ref().unwrap();
    assert_eq!(result["passed"], true, "{result}");
    assert_eq!(result["members"], serde_json::json!([]), "{result}");

    let short = run(
        root,
        &["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"],
    );
    // No test failed: a member the run could not judge is no red test.
    assert_eq!(
        short.output.status.code(),
        Some(2),
        "{}",
        text(&short.output)
    );
    assert_eq!(short.result.as_ref().unwrap()["outcome"], "cannot-judge");
    assert_eq!(short.result.as_ref().unwrap()["exit_status"], 2);
    // Every action passed: only the plan's requirement fails the run.
    for row in &short.records {
        assert_ne!(row["state"], "failed", "{row}");
    }
    let stderr = String::from_utf8_lossy(&short.output.stderr);
    assert!(
        stderr.contains("plan.toml`: 1 requirement not met:")
            && stderr.contains(
                "member `hidden` reported 0 tests (passed + failed) over `[default]` and its \
                 variants; `min-tests` is 1."
            ),
        "{stderr}"
    );
    assert!(!stderr.contains("member `seen`"), "{stderr}");
    assert_eq!(
        member(&short, "hidden"),
        serde_json::json!({"package": "hidden", "tests": 0, "min_tests": 1, "passed": false})
    );
    assert_eq!(
        member(&short, "seen"),
        serde_json::json!({"package": "seen", "tests": 1, "min_tests": 1, "passed": true})
    );
    let result = short.result.as_ref().unwrap();
    assert_eq!(result["passed"], false, "{result}");
    assert_eq!(result["unmet"].as_array().unwrap().len(), 1, "{result}");

    // The sum is over the default run and the member's variants.
    let credited = run(
        root,
        &[
            "--plan",
            "with-variant.toml",
            "--whole-plan",
            "--no-fail-fast",
        ],
    );
    assert!(
        credited.output.status.success(),
        "{}",
        text(&credited.output)
    );
    assert_eq!(member(&credited, "hidden")["tests"], 1);
    assert_eq!(credited.result.as_ref().unwrap()["passed"], true);

    // An instrument's tests credit nobody: `seen` has one test of its own,
    // however often the instrument runs it again.
    let two = run(
        root,
        &["--plan", "two.toml", "--whole-plan", "--no-fail-fast"],
    );
    assert_eq!(two.output.status.code(), Some(2), "{}", text(&two.output));
    assert_eq!(member(&two, "seen")["tests"], 1);
    assert_eq!(member(&two, "seen")["passed"], false);
    let stderr = String::from_utf8_lossy(&two.output.stderr);
    assert!(
        stderr.contains("2 requirements not met:")
            && stderr.contains("member `seen` reported 1 test (passed + failed)")
            && stderr.contains("member `hidden` reported 1 test (passed + failed)"),
        "{stderr}"
    );

    // A narrowed run has only part of the sum: it judges none of it and
    // says so.
    let narrowed = run(
        root,
        &[
            "--plan",
            "with-variant.toml",
            "--whole-plan",
            "--request",
            "default",
            "--no-fail-fast",
        ],
    );
    assert!(
        narrowed.output.status.success(),
        "{}",
        text(&narrowed.output)
    );
    assert!(
        String::from_utf8_lossy(&narrowed.output.stderr).contains(
            "--request leaves requests out of this run, so `[default] min-tests` is not judged"
        ),
        "{}",
        text(&narrowed.output)
    );
    let result = narrowed.result.as_ref().unwrap();
    assert_eq!(result["members"], serde_json::json!([]));
    // The record does not read as the gate's pass.
    assert_eq!(result["passed"], true, "{result}");
    assert_eq!(result["narrowed"], true, "{result}");
    assert_eq!(result["min_tests_skipped"], true, "{result}");
    let whole = credited.result.as_ref().unwrap();
    assert_eq!(whole["narrowed"], false, "{whole}");
    assert_eq!(whole["min_tests_skipped"], false, "{whole}");

    // Leaving out only an instrument takes nothing from any member's sum:
    // `min-tests` is judged, and fails as it does in the whole run.
    let uninstrumented = run(
        root,
        &[
            "--plan",
            "two.toml",
            "--whole-plan",
            "--request",
            "default",
            "--request",
            "hidden-f",
            "--no-fail-fast",
        ],
    );
    assert_eq!(
        uninstrumented.output.status.code(),
        Some(2),
        "{}",
        text(&uninstrumented.output)
    );
    let stderr = String::from_utf8_lossy(&uninstrumented.output.stderr);
    assert!(!stderr.contains("is not judged"), "{stderr}");
    assert!(stderr.contains("2 requirements not met:"), "{stderr}");
    assert_eq!(member(&uninstrumented, "seen")["passed"], false);
    let result = uninstrumented.result.as_ref().unwrap();
    assert_eq!(result["narrowed"], true, "{result}");
    assert_eq!(result["min_tests_skipped"], false, "{result}");

    // A variant that reports no test fails, though its member's `min-tests`
    // is met by another variant.
    let empty = run(
        root,
        &[
            "--plan",
            "empty-variant.toml",
            "--whole-plan",
            "--no-fail-fast",
        ],
    );
    assert_eq!(
        empty.output.status.code(),
        Some(2),
        "{}",
        text(&empty.output)
    );
    for row in &empty.records {
        assert_ne!(row["state"], "failed", "{row}");
    }
    assert_eq!(member(&empty, "hidden")["passed"], true);
    let stderr = String::from_utf8_lossy(&empty.output.stderr);
    assert!(
        stderr.contains("1 requirement not met:")
            && stderr.contains("variant `hidden-g` reported no test (passed + failed)"),
        "{stderr}"
    );
    let requests = empty.result.as_ref().unwrap()["requests"].clone();
    let passed = requests
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap(),
                row["passed"].as_bool().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        passed,
        [("default", true), ("hidden-f", true), ("hidden-g", false)]
    );
}

/// An instrument's `require-pass` names tests that must have run and passed.
#[test]
fn a_required_test_that_did_not_run_and_pass_fails_its_instrument() {
    let world = world("test-plan-require-pass");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "",
        "#[cfg(test)] mod digest {\n\
         #[test] fn matches() {}\n\
         #[test] fn other() {}\n\
         #[test] #[ignore] fn slow() {}\n\
         #[test] #[should_panic] fn boom() { panic!(\"as it should\") }\n\
         }\n",
    );
    write(root, "host/tests/more.rs", "#[test] fn elsewhere() {}\n");
    // `slow` is ignored; another test prints, past libtest's capture, that
    // it passed.
    write(
        root,
        "host/tests/forge.rs",
        r#"#[test] #[ignore] fn slow() {}
#[test] fn real() {}
#[test] fn forger() {
    use std::io::Write as _;
    std::io::stdout().write_all(b"\ntest slow ... ok\n").unwrap();
}
"#,
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[[instrument]]
id = "needs-ignored"
package = "host"
lib = true
args = ["digest::"]
require-pass = ["digest::matches", "digest::slow"]
[[instrument]]
id = "needs-real"
package = "host"
lib = true
args = ["digest::"]
require-pass = ["digest::matches"]
[[instrument]]
id = "needs-filtered"
package = "host"
lib = true
args = ["digest::other"]
require-pass = ["digest::matches"]
[[instrument]]
id = "in-either"
package = "host"
lib = true
test = ["more"]
require-pass = ["elsewhere"]
[[instrument]]
id = "needs-prefix"
package = "host"
lib = true
args = ["digest::"]
require-pass = ["digest::match"]
[[instrument]]
id = "needs-boom"
package = "host"
lib = true
args = ["digest::"]
require-pass = ["digest::boom"]
[[instrument]]
id = "needs-forged"
package = "host"
test = ["forge"]
require-pass = ["slow"]
"#,
    );
    let judged = run(
        root,
        &["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"],
    );
    assert_eq!(
        judged.output.status.code(),
        Some(2),
        "{}",
        text(&judged.output)
    );
    assert_eq!(judged.result.as_ref().unwrap()["outcome"], "cannot-judge");
    // Every harness passed by itself, the ignored test's included.
    for row in &judged.records {
        assert_ne!(row["state"], "failed", "{row}");
    }
    let shared = judged.action(&["needs-ignored", "needs-real", "needs-prefix", "needs-boom"]);
    assert_eq!(
        judged.terminal(shared)["tests"],
        counts(3, 0, 1, 0),
        "{}",
        text(&judged.output)
    );
    let stderr = String::from_utf8_lossy(&judged.output.stderr);
    assert!(
        stderr.contains("plan.toml`: 4 requirements not met:"),
        "{stderr}"
    );
    // The forged line is on the harness's stdout, and passes nothing: the
    // harness printed one more `ok` line than it counted passes, or (where
    // libtest prints a test's name before running it) two results for `slow`.
    let forged = judged.action(&["needs-forged"]);
    assert_eq!(judged.terminal(forged)["tests"], counts(2, 0, 1, 0));
    assert!(
        judged.ran(forged).contains(&"test slow ... ok"),
        "{}",
        text(&judged.output)
    );
    let unmet = "instrument `needs-forged` requires `slow` to pass, and none of its test \
                 executables printed `test slow ... ok`: ";
    assert!(
        stderr.contains(&format!(
            "{unmet}the harness printed 3 `test <name> ... ok` lines and closed its run with 2 \
             passed, so its result lines are not read"
        )) || stderr.contains(&format!(
            "{unmet}a harness that printed it also printed another result for that test"
        )),
        "{stderr}"
    );
    for (id, name) in [
        ("needs-ignored", "digest::slow"),
        ("needs-filtered", "digest::matches"),
        // A name is a whole test path, never a prefix of one.
        ("needs-prefix", "digest::match"),
    ] {
        assert!(
            stderr.contains(&format!(
                "instrument `{id}` requires `{name}` to pass, and none of its test executables \
                 printed `test {name} ... ok`"
            )),
            "{id}: {stderr}"
        );
    }
    assert!(!stderr.contains("instrument `needs-real`"), "{stderr}");
    assert!(!stderr.contains("instrument `in-either`"), "{stderr}");
    assert!(!stderr.contains("targets failed"), "{stderr}");
    let result = judged.result.as_ref().expect("a result record");
    let passed = result["requests"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap(),
                row["passed"].as_bool().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        passed,
        [
            ("needs-ignored", false),
            ("needs-real", true),
            ("needs-filtered", false),
            // The lib's executable does not print it; the other one does.
            ("in-either", true),
            ("needs-prefix", false),
            // `test digest::boom - should panic ... ok` is that test passing.
            ("needs-boom", true),
            ("needs-forged", false),
        ]
    );
    assert_eq!(result["passed"], false, "{result}");

    // The requests whose required tests passed pass on their own.
    let real = run(
        root,
        &[
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--no-fail-fast",
            "--request",
            "needs-real",
            "--request",
            "in-either",
            "--request",
            "needs-boom",
        ],
    );
    assert!(real.output.status.success(), "{}", text(&real.output));
    assert_eq!(real.result.as_ref().unwrap()["passed"], true);
    // That pass is of three requests, and the record says so.
    assert_eq!(real.result.as_ref().unwrap()["narrowed"], true);
}

/// A request that selects no test executable is refused: a run of nothing
/// would pass.
#[test]
fn a_request_that_selects_no_test_executable_is_refused() {
    let world = world("test-plan-idle");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host','quiet']\ndefault-members=['quiet']\nresolver='3'\n",
    );
    package(root, "host", "", "#[test] fn one() {}\n");
    package(root, "quiet", "[lib]\ntest=false\n", "");
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    let instrument = "[[instrument]]\nid = \"host-lib\"\npackage = \"host\"\nlib = true\n";
    for (text_of_plan, ran) in [
        (plan.to_owned(), false),
        // Another request's action does not stand in for the idle one.
        (format!("{plan}{instrument}"), false),
    ] {
        write(root, "plan.toml", &text_of_plan);
        let output = targo(root)
            .args(["--plan", "plan.toml", "--whole-plan"])
            .output()
            .unwrap();
        let message = text(&output);
        assert!(!output.status.success(), "{message}");
        assert!(
            message.contains(
                "plan.toml`: no test executable was selected for request `default`; a run of \
                 nothing would pass"
            ),
            "{message}"
        );
        assert_eq!(message.contains("Running"), ran, "{message}");
        // The build of such a plan is still a build.
        let built = targo(root)
            .args(["--plan", "plan.toml", "--whole-plan", "--no-run"])
            .output()
            .unwrap();
        assert!(built.status.success(), "{}", text(&built));
    }
}

#[test]
fn a_plan_owns_selection_and_refuses_what_it_cannot_honor() {
    let world = world("test-plan-refusals");
    let root = world.path();
    overwrite_workspace(root);
    let plan = |arguments: &[&str]| {
        let mut command = targo(root);
        command
            .args(["--plan", "plan.toml", "--no-run"])
            .args(or_whole(arguments));
        refusal(command)
    };

    for (arguments, spelling) in [
        (&["--features", "flag"][..], "--features"),
        (&["--all-features"], "--all-features"),
        (&["--no-default-features"], "--no-default-features"),
        (&["--lib"], "--lib"),
        (&["--bins"], "--bins"),
        (&["--bin", "x"], "--bin"),
        (&["--examples"], "--examples"),
        (&["--example", "x"], "--example"),
        (&["--tests"], "--tests"),
        (&["--test", "x"], "--test"),
        (&["--benches"], "--benches"),
        (&["--bench", "x"], "--bench"),
        (&["--all-targets"], "--all-targets"),
        (&["--workspace"], "--workspace"),
        (&["--workspace", "--exclude", "left"], "--exclude"),
        (&["some_test"], "a test name"),
        (&["--", "--nocapture"], "arguments after `--`"),
    ] {
        let message = plan(arguments);
        assert!(
            message.contains(&format!("--plan cannot be combined with {spelling}:")),
            "{arguments:?}: {message}"
        );
    }
    // `--doc` and `--require-test-bin` already conflict with `--no-run`.
    for (arguments, spelling) in [
        (&["--doc"][..], "--doc"),
        (&["--require-test-bin", "x"], "--require-test-bin"),
    ] {
        let mut command = targo(root);
        command
            .args(["--plan", "plan.toml"])
            .args(or_whole(arguments));
        let message = refusal(command);
        assert!(
            message.contains(&format!("--plan cannot be combined with {spelling}:")),
            "{arguments:?}: {message}"
        );
    }

    // `-p` selects: it names plan members a change reaches, and nothing the
    // plan does not test.
    let mut command = targo(root);
    command.args(["--plan", "plan.toml", "-p", "left"]);
    unit_graph(command);
    for (arguments, expected) in [
        (
            &["-p", "absent"][..],
            "-p `absent` names 0 workspace members",
        ),
        (
            &["-p", "le*"],
            "-p `le*`: a plan run names each reached member exactly",
        ),
        (
            &["--changed-paths", "absent.txt"],
            "failed to read --changed-paths",
        ),
    ] {
        let message = plan(arguments);
        assert!(message.contains(expected), "{arguments:?}: {message}");
    }
    let mut command = targo(root);
    command.args(["--changed-paths", "paths.txt"]);
    assert!(refusal(command).contains("--plan"));

    let message = plan(&["--request", "middle"]);
    assert!(
        message.contains("--request `middle` is not a request of the plan; it has: left, right"),
        "{message}"
    );
    let mut command = targo(root);
    command.args(["--request", "left"]);
    assert!(refusal(command).contains("--plan"));

    // One target directory serves every request, so naming it is the
    // invocation's business, by flag as by `CARGO_TARGET_DIR`.
    let mut command = targo(root);
    command.args([
        "--plan",
        "plan.toml",
        "--whole-plan",
        "--target-dir",
        "elsewhere.noindex",
    ]);
    unit_graph(command);

    let original = fs::read_to_string(root.join("plan.toml")).unwrap();
    let left = "id = \"left\"\npackage = \"left\"\nlib = true\n";
    let right = "id = \"right\"\npackage = \"right\"\nlib = true\n";
    assert!(original.contains(left) && original.contains(right));
    let elsewhere = |members: &[&str]| {
        let mut table = String::from("[select.elsewhere]\n");
        for member in members {
            table.push_str(&format!("{member} = \"the {member} lane\"\n"));
        }
        table
    };
    let mut wrong = Vec::new();
    for (replacement, expected) in [
        // A failure inside one request says which request, and which plan.
        (
            original.replace(left, &format!("{left}features = [\"nope\"]\n")),
            "plan.toml`, request `left`",
        ),
        (
            original.replace(left, &format!("{left}features = [\"shared/nope\"]\n")),
            "plan.toml`, request `left`",
        ),
        (
            original.replace(right, &right.replace("lib = true", "test = [\"absent\"]")),
            "plan.toml`, request `right`",
        ),
        // A test is named exactly.
        (
            original.replace(right, &right.replace("lib = true", "test = [\"abs*\"]")),
            "variant `right` names test `abs*`; a plan names each test target exactly",
        ),
        (
            original.replace(right, &right.replace("lib = true", "test = [\"\"]")),
            "variant `right` names an empty `test`",
        ),
        // A member another lane owns is not built here, as an instrument's
        // host either.
        (
            format!(
                "{original}[[instrument]]\nid = \"i\"\npackage = \"core\"\nlib = true\n{}",
                elsewhere(&["core"])
            ),
            "instrument `i` names package `core`, which `select.elsewhere` leaves to \
             `the core lane`",
        ),
        (
            format!("{original}[[instrument]]\nid = \"i\"\npackage = \"absent\"\nlib = true\n"),
            "instrument `i` names package `absent`, which is not a workspace member",
        ),
        // `[default]` with every member elsewhere tests nothing.
        (
            format!(
                "{}[default]\ntargets = \"tests\"\n{}",
                original
                    .replace(left, "")
                    .replace(right, "")
                    .replace("[[variant]]\n", ""),
                elsewhere(&["left", "right", "shared", "core"])
            ),
            "`[default]` selects no member",
        ),
        // A harness entry names a package and a target that exist.
        (
            format!("{original}[harness.absent.lib]\nweight = 2\n"),
            "`[harness.absent]` names package `absent`, which is not a workspace member",
        ),
        (
            format!("{original}[harness.left.test.nope]\nexclusive = true\n"),
            "`[harness.left.test.nope]`: package `left` has no test target `nope`",
        ),
        (
            format!("{original}[harness.left.bin.left]\nweight = 2\n"),
            "`[harness.left.bin.left]`: package `left` has no bin target `left`",
        ),
        (
            format!(
                "{original}[harness.core.lib]\nweight = 2\n{}",
                elsewhere(&["core"])
            ),
            "`[harness.core]` names package `core`, which `select.elsewhere` leaves to",
        ),
        // A build outside this workspace's graph is a phase of its own
        // manifest; an entry that names none, or a tool for a member no
        // request can test, must not pass as a plan that built it.
        (
            format!(
                "{original}[[tool]]\nmanifest = \"m\"\nbin = \"b\"\nenv = \"E\"\n\
                 needed-by = [\"left\"]\n"
            ),
            "`[[tool]]` manifest `m` is not a `Cargo.toml` named by a normal path",
        ),
        (
            format!("{original}[[workspace]]\nmanifest = \"m\"\n[[workspace]]\nmanifest = \"n\"\n"),
            "`[[workspace]]` manifest `m` is not a `Cargo.toml` named by a normal path",
        ),
        (
            format!(
                "{original}[[tool]]\nmanifest = \"tool/Cargo.toml\"\nbin = \"b\"\nenv = \"E\"\n"
            ),
            "`[[tool]]` `tool/Cargo.toml` names no member in `needed-by`",
        ),
        (
            format!(
                "{original}[[tool]]\nmanifest = \"tool/Cargo.toml\"\nbin = \"b\"\nenv = \"E\"\n\
                 needed-by = [\"absent\"]\n"
            ),
            "`[[tool]]` `tool/Cargo.toml`: `needed-by` names package `absent`, which is not a \
             workspace member",
        ),
        (
            format!(
                "{original}[[tool]]\nmanifest = \"tool/Cargo.toml\"\nbin = \"b\"\nenv = \"E\"\n\
                 needed-by = [\"core\"]\n{}",
                elsewhere(&["core"])
            ),
            "`needed-by` names package `core`, which `select.elsewhere` leaves to",
        ),
        (
            original.replace(
                "lib = true\n[[variant]]",
                "lib = true\nlibs = true\n[[variant]]",
            ),
            "unknown field `libs`",
        ),
        (original.replace("v1", "v0"), "is not `targo.test-plan.v1`"),
        (
            original.replace("package = \"right\"", "package = \"absent\""),
            "variant `right` names package `absent`, which is not a plan member",
        ),
        (
            original.replace("id = \"right\"", "id = \"left\""),
            "request id `left` is used twice",
        ),
        // A condition on changed paths that every path meets.
        (
            original.replace("[select]\n", "[select]\nattribute-under = [\"\"]\n"),
            "`select.attribute-under` has an empty entry, which every path matches",
        ),
        (
            format!(
                "{original}[[instrument]]\nid = \"i\"\npackage = \"left\"\nlib = true\n\
                 when-changed = [\"\"]\n"
            ),
            "instrument `i`: `when-changed` has an empty entry",
        ),
        (
            format!(
                "{original}[[instrument]]\nid = \"i\"\npackage = \"left\"\nlib = true\n\
                 when-changed-suffix = \"\"\n"
            ),
            "instrument `i`: `when-changed-suffix` has an empty entry",
        ),
        (
            format!(
                "{original}[[instrument]]\nid = \"i\"\npackage = \"left\"\nlib = true\n\
                 not-under = [\"\"]\n"
            ),
            "instrument `i`: `not-under` has an empty entry",
        ),
        // A requirement of nothing is not written as one.
        (
            format!("{original}[default]\ntargets = \"tests\"\nmin-tests = 0\n"),
            "`[default] min-tests = 0` requires nothing",
        ),
        // An id is pasted into a shell after `--request`.
        (
            original.replace("id = \"right\"", "id = \"my id; rm -rf x\""),
            "variant id `my id; rm -rf x` is not a plain word",
        ),
        (
            original.replace("id = \"right\"", "id = \"--no-run\""),
            "variant id `--no-run` is not a plain word",
        ),
    ] {
        assert_ne!(replacement, original);
        fs::write(root.join("plan.toml"), replacement).unwrap();
        let output = targo(root)
            .args(["--plan", "plan.toml", "--whole-plan", "--no-run"])
            .output()
            .unwrap();
        let message = text(&output);
        // Every row is judged, so one run names every plan wrongly accepted.
        if output.status.success() || !message.contains(expected) {
            wrong.push(format!("expected `{expected}`, got: {message}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n---\n"));
    // What a run reads is checked by a build too: a harness policy no
    // target could hold, and a known-red file that is not there.
    // A `[[tool]]` whose manifest is not there is refused by a run as by a
    // build.
    let instrument = "[[instrument]]\nid = \"i\"\npackage = \"left\"\nlib = true\n";
    let mut wrong = Vec::new();
    for (replacement, expected, builds) in [
        (
            format!("{original}[harness.left.lib]\nweight = 0\n"),
            "harness.left.lib.weight must be positive",
            false,
        ),
        (
            format!("{original}[expect]\nknown-red = \"red.txt\"\n"),
            "failed to read `[expect] known-red` file",
            false,
        ),
        (
            format!("{original}[expect]\nknown-red = \"../red.txt\"\n"),
            "`[expect] known-red = \"../red.txt\"` is not a path under the workspace root",
            false,
        ),
        // A required name is one whole test path.
        (
            format!("{original}{instrument}require-pass = [\"\"]\n"),
            "instrument `i` has a `require-pass` entry `` that is not a test's full path",
            false,
        ),
        (
            format!("{original}{instrument}require-pass = [\"a ... ok\"]\n"),
            "instrument `i` has a `require-pass` entry `a ... ok` that is not a test's full path",
            false,
        ),
        (
            format!("{original}{instrument}args = [\"--test-threads=2\"]\n"),
            "plan.toml`, request `i`\n\nCaused by:\n  build.test-jobs owns libtest's thread budget",
            false,
        ),
        (
            format!(
                "{original}[[tool]]\nmanifest = \"tool/Cargo.toml\"\nbin = \"b\"\nenv = \"E\"\n\
                 needed-by = [\"left\"]\n"
            ),
            "tool `b` of `tool/Cargo.toml` failed to build; the tests of left that run it \
             cannot run",
            false,
        ),
        (
            format!("{original}[[workspace]]\nmanifest = \"own/Cargo.toml\"\n"),
            "plan.toml`, workspace `own/Cargo.toml`",
            false,
        ),
        // Arguments with which a harness exits 0 and runs no test.
        (
            format!("{original}{instrument}args = [\"--list\"]\n"),
            "plan.toml`, request `i`\n\nCaused by:\n  `--list` makes a test harness exit \
             successfully without running a test",
            false,
        ),
        (
            format!("{original}{instrument}args = [\"shared_\", \"--help\"]\n"),
            "request `i`\n\nCaused by:\n  `--help` makes a test harness exit successfully",
            false,
        ),
        (
            format!("{original}{instrument}args = [\"-h\"]\n"),
            "request `i`\n\nCaused by:\n  `-h` makes a test harness exit successfully",
            false,
        ),
        // A format without the lines a plan run reads.
        (
            format!("{original}{instrument}args = [\"--format\", \"json\"]\n"),
            "request `i`\n\nCaused by:\n  `--format json` replaces the result lines a plan \
             run reads",
            false,
        ),
        (
            format!("{original}{instrument}args = [\"--format=junit\"]\n"),
            "request `i`\n\nCaused by:\n  `--format junit` replaces the result lines",
            false,
        ),
    ] {
        fs::write(root.join("plan.toml"), replacement).unwrap();
        let output = targo(root)
            .args(["--plan", "plan.toml", "--whole-plan"])
            .output()
            .unwrap();
        let message = text(&output);
        if output.status.success() || !message.contains(expected) {
            wrong.push(format!("expected `{expected}`, got: {message}"));
        }
        // Refused before any test ran.
        if message.contains("Running") {
            wrong.push(format!("`{expected}`: a test ran: {message}"));
        }
        let built = targo(root)
            .args(["--plan", "plan.toml", "--whole-plan", "--no-run"])
            .output()
            .unwrap();
        if built.status.success() != builds {
            wrong.push(format!("`{expected}`: --no-run: {}", text(&built)));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n---\n"));
    // The graph of such a plan is still this workspace's graph, and says so.
    fs::write(
        root.join("plan.toml"),
        format!(
            "{original}[[tool]]\nmanifest = \"tool/Cargo.toml\"\nbin = \"b\"\nenv = \"E\"\n\
             needed-by = [\"left\"]\n[harness.left.lib]\nweight = 2\n"
        ),
    )
    .unwrap();
    let output = targo(root)
        .args([
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--unit-graph",
            "-Zunstable-options",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", text(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("the unit graph leaves out its [[tool]] entries (1)"),
        "{}",
        text(&output)
    );
    fs::write(root.join("plan.toml"), &original).unwrap();
    let mut missing = targo(root);
    missing.args(["--plan", "absent.toml", "--whole-plan", "--no-run"]);
    assert!(refusal(missing).contains("failed to read test plan"));

    // Resolver 1 unifies features over the workspace; no request could equal
    // its standalone command.
    let manifest = fs::read_to_string(root.join("Cargo.toml")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        manifest.replace("resolver='3'", "resolver='1'"),
    )
    .unwrap();
    assert!(plan(&[]).contains("a test plan requires feature resolver 2 or later"));
}

/// A workspace whose directories are not its package names: `outer` holds a
/// nested member, `far` is another lane's, and `stray` is nobody's.
fn selection_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['crates/outer','crates/outer/inner','crates/host','crates/far',\
         'crates/stray']\ndefault-members=['crates/outer','crates/outer/inner','crates/host']\n\
         resolver='3'\n",
    );
    let member = |dir: &str, name: &str, manifest: &str, lib: &str| {
        write(
            root,
            &format!("{dir}/Cargo.toml"),
            &format!("[package]\nname='{name}'\nversion='0.0.0'\nedition='2024'\n{manifest}"),
        );
        write(root, &format!("{dir}/src/lib.rs"), lib);
    };
    let extra = "#[test] fn plain() {}\n#[cfg(feature = \"extra\")]\n#[test] fn extra() {}\n";
    member("crates/outer", "outer", "[features]\nextra=[]\n", extra);
    member(
        "crates/outer/inner",
        "inner",
        "[features]\nextra=[]\n",
        extra,
    );
    member(
        "crates/host",
        "host",
        "",
        "#[test] fn plain() {}\n#[test] fn fixture_reads() {}\n",
    );
    write(
        root,
        "crates/host/tests/docs.rs",
        "#[test] fn documents() {}\n",
    );
    member("crates/far", "far", "", "#[test] fn plain() {}\n");
    member("crates/stray", "stray", "", "#[test] fn plain() {}\n");
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
attribute-under = ["crates/"]
[select.elsewhere]
far = "the far lane"
[default]
targets = "tests"
min-tests = 1
[[variant]]
id = "outer-extra"
package = "outer"
features = ["extra"]
lib = true
[[variant]]
id = "inner-extra"
package = "inner"
features = ["extra"]
lib = true
[[instrument]]
id = "host-fixtures"
package = "host"
lib = true
args = ["fixture_"]
when-changed = ["fixtures/", "crates/outer/src/gen"]
[[instrument]]
id = "host-docs"
package = "host"
test = ["docs"]
when-changed-suffix = ".json"
not-under = ["vendor/"]
"#,
    );
}

/// The first line an invocation wrote, which under a plan is its
/// `test-plan` record.
fn first_record(output: &Output) -> Value {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let first = stdout.lines().next().unwrap_or_default();
    let record: Value = serde_json::from_str(first)
        .unwrap_or_else(|error| panic!("{error}: first line `{first}`: {}", text(output)));
    assert_eq!(record["reason"], "test-plan", "{}", text(output));
    assert_eq!(record["schema"], "targo.test-plan-selection.v1");
    record
}

fn names(list: &Value) -> Vec<&str> {
    list.as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap())
        .collect()
}

/// The ids of the requests a `test-plan` record says the run performs, and
/// the members its default run tests.
fn performed(record: &Value) -> (Vec<&str>, Vec<&str>) {
    let rows = record["requests"].as_array().unwrap();
    // Every request of the file is in the record, performed or not.
    assert_eq!(
        rows.iter().map(|row| &row["id"]).collect::<Vec<_>>(),
        [
            "default",
            "outer-extra",
            "inner-extra",
            "host-fixtures",
            "host-docs"
        ]
    );
    let active = rows
        .iter()
        .filter(|row| row["active"] == true)
        .map(|row| row["id"].as_str().unwrap())
        .collect();
    (active, names(&rows[0]["packages"]))
}

#[test]
fn changed_paths_and_reached_members_select_exactly_the_requests_that_test_them() {
    let world = world("test-plan-selection");
    let root = world.path();
    selection_workspace(root);
    let select = |paths: Option<&str>, arguments: &[&str]| {
        let mut command = targo(root);
        command.args(["--plan", "plan.toml", "--no-run", "--message-format=json"]);
        if let Some(paths) = paths {
            write(root, "paths.txt", paths);
            command.args(["--changed-paths", "paths.txt"]);
        } else if !arguments.contains(&"-p") {
            command.arg("--whole-plan");
        }
        command.args(arguments).output().unwrap()
    };
    let every = [
        "default",
        "outer-extra",
        "inner-extra",
        "host-fixtures",
        "host-docs",
    ];

    // (changed paths, other arguments, requests performed, members of the
    // default run, the reason of one request).
    type Row<'a> = (
        Option<&'a str>,
        &'a [&'a str],
        &'a [&'a str],
        &'a [&'a str],
        (&'a str, &'a str),
    );
    let table: [Row<'_>; 13] = [
        // Neither input: the whole plan.
        (
            None,
            &[],
            &every,
            &["host", "inner", "outer"],
            ("host-docs", "--whole-plan: every request runs"),
        ),
        // A touched member: its default run and its variants, no other's.
        (
            Some("crates/outer/src/lib.rs\n"),
            &[],
            &["default", "outer-extra"],
            &["outer"],
            ("inner-extra", "package `inner` is not selected"),
        ),
        // A nested member's path is its own, never its parent's.
        (
            Some("crates/outer/inner/src/lib.rs\n"),
            &[],
            &["default", "inner-extra"],
            &["inner"],
            ("outer-extra", "package `outer` is not selected"),
        ),
        // A member's directory alone, as a moved gitlink is named.
        (
            Some("crates/outer\n"),
            &[],
            &["default", "outer-extra"],
            &["outer"],
            ("default", "1 member selected (1 touched, 0 reached)"),
        ),
        // An instrument's subject moved and its host is untouched.
        (
            Some("fixtures/a.bin\n"),
            &[],
            &["host-fixtures"],
            &[],
            (
                "host-fixtures",
                "changed path `fixtures/a.bin` is under `fixtures/`",
            ),
        ),
        // The host is touched too: its default run tests the instrument.
        (
            Some("fixtures/a.bin\ncrates/host/src/lib.rs\n"),
            &[],
            &["default"],
            &["host"],
            (
                "host-fixtures",
                "its host `host` is touched, so the default run tests it",
            ),
        ),
        // The host is only reached: the instrument still runs.
        (
            Some("fixtures/a.bin\n"),
            &["-p", "host"],
            &["default", "host-fixtures"],
            &["host"],
            ("default", "1 member selected (0 touched, 1 reached)"),
        ),
        // A condition is a prefix of the path as text, and may lie inside a
        // member: that member is touched and the instrument's host is not.
        (
            Some("crates/outer/src/generated.rs\n"),
            &[],
            &["default", "outer-extra", "host-fixtures"],
            &["outer"],
            ("outer-extra", "package `outer` is touched"),
        ),
        // A suffix condition, and the directories it does not reach into.
        (
            Some("docs/a.json\n"),
            &[],
            &["host-docs"],
            &[],
            ("host-docs", "changed path `docs/a.json` ends with `.json`"),
        ),
        (
            Some("vendor/a.json\n"),
            &[],
            &[],
            &[],
            (
                "host-docs",
                "no changed path meets its `when-changed` conditions",
            ),
        ),
        // Reached members without any path; `-p` takes a full spec too.
        (
            None,
            &["-p", "inner", "-p", "outer@0.0.0"],
            &["default", "outer-extra", "inner-extra"],
            &["inner", "outer"],
            ("inner-extra", "package `inner` is reached"),
        ),
        // `--request` narrows what the selection performs.
        (
            Some("crates/outer/src/lib.rs\n"),
            &["--request", "outer-extra"],
            &["outer-extra"],
            &["outer"],
            ("default", "left out by --request"),
        ),
        // NUL-separated: a path may then hold a newline.
        (
            Some("crates/host/src/a\nb.rs\0fixtures/x\0"),
            &[],
            &["default"],
            &["host"],
            ("default", "1 member selected (1 touched, 0 reached)"),
        ),
    ];
    let mut wrong = Vec::new();
    for (paths, arguments, requests, members, (id, why)) in table {
        let output = select(paths, arguments);
        let record = first_record(&output);
        let (active, default_members) = performed(&record);
        let row = record["requests"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["id"] == id)
            .unwrap();
        if !output.status.success()
            || active != requests
            || default_members != members
            || row["why"] != why
            || record["unattributed"] != serde_json::json!([])
        {
            wrong.push(format!(
                "{paths:?} {arguments:?}: expected {requests:?} over {members:?} and `{id}` \
                 because `{why}`; got {active:?} over {default_members:?}, `{}`\n{}",
                row["why"],
                text(&output)
            ));
        }
        // A selection that performs nothing builds nothing and says so.
        let idle = String::from_utf8_lossy(&output.stderr).contains("performs no request");
        if idle != requests.is_empty() {
            wrong.push(format!("{paths:?} {arguments:?}: idle is {idle}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n---\n"));

    // The wall bound's per-member product counts every crate the run tests:
    // here the touched member `outer` and the instrument's host `host`,
    // which is no selected member (the script lane's `Plan.crates()`).
    let output = select(Some("crates/outer/src/generated.rs\n"), &[]);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        stderr.contains(
            "test plan time bound: no bound for the whole run (2 members), no bound without a line"
        ),
        "{stderr}"
    );

    // A change to the lane's own policy runs every request: a path under
    // `[select] whole-plan-when-changed`, here the plan file itself. Without
    // the key the same path selects nothing and the run exits 0.
    let policy = fs::read_to_string(root.join("plan.toml")).unwrap().replace(
        "attribute-under = [\"crates/\"]\n",
        "attribute-under = [\"crates/\"]\nwhole-plan-when-changed = [\"policy.toml\"]\n",
    );
    assert!(policy.contains("whole-plan-when-changed"));
    write(root, "policy.toml", &policy);
    write(root, "paths.txt", "policy.toml\n");
    let whole = |plan: &str| {
        let output = targo(root)
            .args(["--plan", plan, "--no-run", "--message-format=json"])
            .args(["--changed-paths", "paths.txt"])
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", text(&output));
        let record = first_record(&output);
        let (active, members) = performed(&record);
        (
            record["selection"]["whole_plan"].as_bool().unwrap(),
            active.len(),
            members.into_iter().map(str::to_owned).collect::<Vec<_>>(),
            record["requests"][0]["why"].as_str().unwrap().to_owned(),
        )
    };
    let (is_whole, active, members, why) = whole("policy.toml");
    assert!(is_whole);
    assert_eq!(members, ["host", "inner", "outer"]);
    assert_eq!(active, 5, "every request of the fixture's plan");
    assert_eq!(
        why,
        "changed path `policy.toml` is under `policy.toml`, which \
         `select.whole-plan-when-changed` names: every request runs"
    );
    let (is_whole, active, members, _) = whole("plan.toml");
    assert!(!is_whole);
    assert_eq!((active, members), (0, Vec::new()));

    // The record says what was read and what was given.
    let output = select(
        Some("crates/far/src/lib.rs\ncrates/far/Cargo.toml\nREADME.md\n"),
        &["-p", "host"],
    );
    assert!(output.status.success(), "{}", text(&output));
    let record = first_record(&output);
    assert_eq!(
        keys(&record),
        BTreeSet::from([
            "reason",
            "schema",
            "plan",
            "sha256",
            "selection",
            "members",
            "requests",
            "elsewhere",
            "workspaces",
            "tools",
            "unattributed",
        ])
    );
    assert_eq!(
        record["sha256"].as_str().unwrap(),
        cargo_util::Sha256::new()
            .update(&fs::read(root.join("plan.toml")).unwrap())
            .finish_hex()
    );
    assert_eq!(
        record["selection"],
        serde_json::json!({
            "changed_paths": ["README.md", "crates/far/Cargo.toml", "crates/far/src/lib.rs"],
            "changed_ranges": [],
            "packages": ["host"],
            "reached": [],
            "whole_plan": false,
            "requests": [],
        })
    );
    assert_eq!(
        record["members"],
        serde_json::json!({"touched": [], "reached": ["host"], "selected": ["host"]})
    );
    // A member another lane tests is named with that lane, in the record
    // and to the person; its paths are accounted for.
    assert_eq!(
        record["elsewhere"],
        serde_json::json!([{
            "member": "far",
            "command": "the far lane",
            "paths": ["crates/far/Cargo.toml", "crates/far/src/lib.rs"],
        }])
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "`far` changed (2 paths) and this plan does not test it; `the far lane` does"
        ) && stderr.contains("Selected 1 of 5 plan requests: default"),
        "{stderr}"
    );
    let whole = first_record(&select(None, &[]));
    assert_eq!(whole["selection"]["changed_paths"], Value::Null);

    // A changed path under `attribute-under` that nothing here tests and no
    // other lane is named for: exit 2, after the record that lists it, and
    // before anything is built.
    for (paths, listed) in [
        (
            "crates/nobody/src/lib.rs\ncrates/outer/src/lib.rs\n",
            serde_json::json!([{
                "path": "crates/nobody/src/lib.rs",
                "why": "no workspace member owns it",
            }]),
        ),
        // A name that only starts with a member's directory is not under it.
        (
            "crates/outer-notes.md\n",
            serde_json::json!([{
                "path": "crates/outer-notes.md",
                "why": "no workspace member owns it",
            }]),
        ),
        (
            "crates/stray/src/lib.rs\n",
            serde_json::json!([{
                "path": "crates/stray/src/lib.rs",
                "why": "its owner `stray` is a workspace member that is neither a plan \
                        member nor in `select.elsewhere`",
            }]),
        ),
    ] {
        let output = select(Some(paths), &[]);
        assert_eq!(output.status.code(), Some(2), "{}", text(&output));
        assert_eq!(first_record(&output)["unattributed"], listed);
        // The selection record and the closing record, and nothing built.
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(stdout.lines().count(), 2, "nothing was built: {stdout}");
        closed_without_verdict(stream(&output).last(), "cannot-judge", &output);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("under `select.attribute-under` is tested by no request")
                && stderr.contains(listed[0]["path"].as_str().unwrap())
                && !stderr.contains("Compiling"),
            "{stderr}"
        );
    }
    // Without JSON the refusal is the same.
    write(root, "paths.txt", "crates/nobody/x\n");
    let mut command = targo(root);
    command.args(["--plan", "plan.toml", "--changed-paths", "paths.txt"]);
    let output = command.output().unwrap();
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(output.stdout.is_empty(), "{}", text(&output));

    // What a selection cannot mean is an error, not a narrower run.
    for (paths, arguments, expected) in [
        (
            Some("crates/outer/inner/src/lib.rs\n"),
            &["--request", "outer-extra"][..],
            "--request `outer-extra` is not performed under this selection: package `outer` \
             is not selected",
        ),
        (
            None,
            &["-p", "far"],
            "-p `far`: `select.elsewhere` leaves `far` to `the far lane`; this plan does not \
             test it",
        ),
        (
            None,
            &["-p", "stray"],
            "-p `stray`: `stray` is not a plan member, so this plan does not test it",
        ),
        (
            Some("crates/outer/../host/src/lib.rs\n"),
            &[],
            "changed path `crates/outer/../host/src/lib.rs` is not a normal path relative to \
             the workspace root",
        ),
        (
            Some("/crates/outer/src/lib.rs\n"),
            &[],
            "is not a normal path relative to the workspace root",
        ),
        (
            Some("./crates/outer/src/lib.rs\n"),
            &[],
            "is not a normal path",
        ),
    ] {
        let output = select(paths, arguments);
        let message = text(&output);
        assert_eq!(output.status.code(), Some(2), "{message}");
        assert!(message.contains(expected), "{message}");
        refused_record(&output);
    }

    // A run performs the selected requests and no other: the paths arrive
    // on standard input, the default run tests the selected member alone,
    // and `min-tests` is asked of that member alone.
    let mut child = targo(root)
        .env("RUSTFLAGS", "-Zthreads=1")
        .args(["--plan", "plan.toml", "--message-format=json"])
        .args(["--no-fail-fast", "--changed-paths", "-", "-p", "host"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    {
        use std::io::Write as _;
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"fixtures/a.bin\0crates/outer/inner/Cargo.toml\0")
            .unwrap();
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", text(&output));
    let record = first_record(&output);
    assert_eq!(
        performed(&record),
        (
            vec!["default", "inner-extra", "host-fixtures"],
            vec!["host", "inner"]
        )
    );
    let rows = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .collect::<Vec<_>>();
    let ran = rows
        .iter()
        .filter(|row| row["reason"] == "test-execution" && row["state"] == "passed")
        .map(|row| {
            format!(
                "{} {} {} {}",
                row["package"].as_str().unwrap(),
                row["kind"].as_str().unwrap(),
                row["target"].as_str().unwrap(),
                names(&row["requests"]).join("+")
            )
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        ran,
        BTreeSet::from([
            "host lib host default".to_owned(),
            "host lib host host-fixtures".to_owned(),
            "host test docs default".to_owned(),
            "inner lib inner default".to_owned(),
            "inner lib inner inner-extra".to_owned(),
        ]),
        "{}",
        text(&output)
    );
    let result = rows.last().unwrap();
    assert_eq!(result["reason"], "test-plan-result", "{}", text(&output));
    assert_eq!(result["passed"], true);
    assert_eq!(result["narrowed"], false);
    assert_eq!(result["min_tests_skipped"], false);
    assert_eq!(
        result["members"]
            .as_array()
            .unwrap()
            .iter()
            .map(|member| member["package"].as_str().unwrap())
            .collect::<Vec<_>>(),
        ["host", "inner"]
    );
    assert_eq!(
        result["requests"]
            .as_array()
            .unwrap()
            .iter()
            .map(|request| request["id"].as_str().unwrap())
            .collect::<Vec<_>>(),
        ["default", "inner-extra", "host-fixtures"]
    );

    // A run of nothing exits 0 with both records, so a reader can tell it
    // from a run that was cut off; a build of nothing has no verdict.
    write(root, "paths.txt", "README.md\n");
    let idle = run(
        root,
        &["--plan", "plan.toml", "--changed-paths", "paths.txt"],
    );
    assert!(idle.output.status.success(), "{}", text(&idle.output));
    assert!(idle.records.is_empty(), "{}", text(&idle.output));
    assert_eq!(performed(&first_record(&idle.output)).0, [""; 0]);
    let result = idle.result.expect("a run of nothing still has a result");
    assert_eq!(result["passed"], true);
    assert_eq!(result["requests"], serde_json::json!([]));
    assert_eq!(result["members"], serde_json::json!([]));
    let built = select(Some("README.md\n"), &[]);
    assert_eq!(
        String::from_utf8_lossy(&built.stdout).lines().count(),
        1,
        "{}",
        text(&built)
    );
    // `--unit-graph` prints one document of its own; the record is left out.
    let mut command = targo(root);
    command.args(["--plan", "plan.toml", "--changed-paths", "paths.txt"]);
    command.args(["--unit-graph", "-Zunstable-options"]);
    let output = command.output().unwrap();
    assert!(output.status.success(), "{}", text(&output));
    assert!(output.stdout.is_empty(), "{}", text(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("the selection performs no request, so there is no unit graph"),
        "{}",
        text(&output)
    );
    write(root, "paths.txt", "crates/host/src/lib.rs\n");
    let mut command = targo(root);
    command.args(["--plan", "plan.toml", "--changed-paths", "paths.txt"]);
    // Also with JSON messages asked for: the helper parses standard output
    // as the one document.
    command.arg("--message-format=json");
    let graph = unit_graph(command);
    assert!(
        graph.units.iter().any(|unit| unit.starts_with("\"host\""))
            && !graph.units.iter().any(|unit| unit.starts_with("\"outer\"")),
        "only the selected member is in the graph"
    );
}

/// The members and exit status a selection gave, and the reason of each
/// request it performs.
fn decided(output: &Output) -> (Option<i32>, Vec<(String, String)>) {
    let record = first_record(output);
    let active = record["requests"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["active"] == true)
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["why"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    (output.status.code(), active)
}

#[test]
fn a_selection_never_exits_0_over_a_change_that_no_request_of_the_run_tests() {
    let world = world("test-plan-selection-holes");
    let root = world.path();
    selection_workspace(root);
    let select = |plan: &str, paths: Option<&str>, arguments: &[&str]| {
        let mut command = targo(root);
        command.args(["--plan", plan, "--message-format=json"]);
        if let Some(paths) = paths {
            write(root, "paths.txt", paths);
            command.args(["--changed-paths", "paths.txt"]);
        } else if !arguments.contains(&"-p") {
            command.arg("--whole-plan");
        }
        command.args(arguments).output().unwrap()
    };
    let header = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                  attribute-under = [\"crates/\"]\n[select.elsewhere]\nfar = \"the far lane\"\n";

    // A crate that is its own workspace: a change in it selects no request
    // of this workspace, and is tested by the phase of its own manifest.
    // That phase's failure is the run's, never a run of nothing.
    write(
        root,
        "crates/own/Cargo.toml",
        "[package]\nname='own'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    );
    write(
        root,
        "crates/own/src/lib.rs",
        "#[test] fn red() { panic!() }\n",
    );
    write(
        root,
        "plan-own.toml",
        &format!(
            "{header}[default]\ntargets = \"tests\"\n[[workspace]]\n\
             manifest = \"crates/own/Cargo.toml\"\n"
        ),
    );
    for (arguments, code, result) in [
        (&[][..], Some(101), false),
        (&["--no-fail-fast"], Some(101), true),
        (&["--no-run"], Some(0), false),
    ] {
        let output = select("plan-own.toml", Some("crates/own/src/lib.rs\n"), arguments);
        let record = first_record(&output);
        assert_eq!(
            record["workspaces"],
            serde_json::json!(["crates/own/Cargo.toml"])
        );
        assert_eq!(record["unattributed"], serde_json::json!([]));
        assert!(
            record["requests"]
                .as_array()
                .unwrap()
                .iter()
                .all(|row| row["active"] == false),
            "{}",
            text(&output)
        );
        assert_eq!(
            output.status.code(),
            code,
            "{arguments:?}: {}",
            text(&output)
        );
        let message = text(&output);
        // The workspace's own test ran and failed, unless nothing runs.
        assert_eq!(
            message.contains("test red ... FAILED"),
            code != Some(0),
            "{arguments:?}: {message}"
        );
        // Only a run that ran to its end has the plan's verdict, and it
        // counts the failed workspace.
        let verdict = stream(&output)
            .iter()
            .any(|row| row["reason"] == "test-plan-result" && row.get("requests").is_some());
        assert_eq!(verdict, result, "{arguments:?}: {message}");
        assert_eq!(
            message.contains(
                "workspace `crates/own/Cargo.toml` failed: 1 target failed: (its own records \
                 name the failures)"
            ),
            result,
            "{arguments:?}: {message}"
        );
    }

    // A plan without `[default]` tests only the members its variants name.
    // Any other member's path is unattributed and its `-p` is refused; a
    // touched host keeps its instrument, since no default run tests it.
    write(
        root,
        "plan-variants.toml",
        &format!(
            "{header}[[variant]]\nid = \"outer-extra\"\npackage = \"outer\"\n\
             features = [\"extra\"]\nlib = true\n\
             [[variant]]\nid = \"host-lib\"\npackage = \"host\"\nlib = true\n\
             [[instrument]]\nid = \"host-fixtures\"\npackage = \"host\"\nlib = true\n\
             args = [\"fixture_\"]\nwhen-changed = [\"fixtures/\"]\n"
        ),
    );
    let output = select(
        "plan-variants.toml",
        Some("crates/outer/inner/src/lib.rs\ncrates/outer/src/lib.rs\n"),
        &["--no-run"],
    );
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    let record = first_record(&output);
    assert_eq!(
        record["unattributed"],
        serde_json::json!([{
            "path": "crates/outer/inner/src/lib.rs",
            "why": "its owner `inner` is a plan member that no request tests: the plan has no \
                    `[default]` and no variant names `inner`",
        }])
    );
    assert_eq!(record["members"]["touched"], serde_json::json!(["outer"]));
    let output = select("plan-variants.toml", None, &["--no-run", "-p", "inner"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(
        text(&output).contains(
            "-p `inner`: no request of the plan tests `inner`: the plan has no `[default]` and \
             no variant names `inner`"
        ),
        "{}",
        text(&output)
    );
    assert_eq!(
        decided(&select(
            "plan-variants.toml",
            Some("fixtures/a.bin\ncrates/host/src/lib.rs\n"),
            &["--no-run"]
        )),
        (
            Some(0),
            vec![
                (
                    "host-lib".to_owned(),
                    "package `host` is touched".to_owned()
                ),
                (
                    "host-fixtures".to_owned(),
                    "changed path `fixtures/a.bin` is under `fixtures/`; its host `host` is \
                     touched, but no default run tests it"
                        .to_owned()
                ),
            ]
        )
    );
    assert_eq!(
        decided(&select(
            "plan-variants.toml",
            None,
            &["--no-run", "-p", "outer"]
        ))
        .0,
        Some(0)
    );

    // A touched host stands in for its instrument only if the default run
    // performs all the instrument would judge.
    write(
        root,
        "crates/host/Cargo.toml",
        "[package]\nname='host'\nversion='0.0.0'\nedition='2024'\n[features]\nextra=[]\n\
         [[test]]\nname='gate'\ntest=false\n\
         [[test]]\nname='needs'\nrequired-features=['extra']\n",
    );
    write(
        root,
        "crates/host/src/lib.rs",
        "#[test] fn plain() {}\n#[test] fn fixture_reads() {}\n\
         #[test] #[ignore] fn must_pass() {}\n",
    );
    write(
        root,
        "crates/host/tests/gate.rs",
        "#[test] fn gate() { panic!() }\n",
    );
    write(
        root,
        "crates/host/tests/needs.rs",
        "#[test] fn needs() {}\n",
    );
    let instrument = |id: &str, rest: &str| {
        format!(
            "[[instrument]]\nid = \"{id}\"\npackage = \"host\"\nwhen-changed = [\"fixtures/\"]\n\
             {rest}\n"
        )
    };
    write(
        root,
        "plan-cover.toml",
        &format!(
            "{header}[default]\ntargets = \"tests\"\n{}{}{}{}",
            instrument("plain", "lib = true\nargs = [\"fixture_\"]"),
            instrument("gate", "test = [\"gate\"]"),
            instrument(
                "must",
                "lib = true\nargs = [\"must_\"]\nrequire-pass = [\"must_pass\"]"
            ),
            instrument(
                "flagged",
                "lib = true\nargs = [\"--include-ignored\", \"must_\"]"
            ),
        ),
    );
    let moved = "changed path `fixtures/a.bin` is under `fixtures/`";
    let touched = "fixtures/a.bin\ncrates/host/src/lib.rs\n";
    let but = |left_out: &str| format!("{moved}; its host `host` is touched, but {left_out}");
    let (status, active) = decided(&select("plan-cover.toml", Some(touched), &["--no-run"]));
    assert_eq!(status, Some(0));
    assert_eq!(
        active,
        [
            (
                "default".to_owned(),
                "1 member selected (1 touched, 0 reached)".to_owned()
            ),
            (
                "gate".to_owned(),
                but(
                    "the default run does not run test target `gate` (`test = false` or \
                     `required-features`)"
                )
            ),
            (
                "must".to_owned(),
                but("the default run is not held to its `require-pass`")
            ),
            (
                "flagged".to_owned(),
                but("the default run does not pass its argument `--include-ignored`")
            ),
        ]
    );
    // The record alone: a target behind a feature does not build without it.
    write(
        root,
        "plan-needs.toml",
        &format!(
            "{header}[default]\ntargets = \"tests\"\n{}",
            instrument("needs", "test = [\"needs\"]")
        ),
    );
    assert_eq!(
        decided(&select("plan-needs.toml", Some(touched), &["--no-run"])).1[1],
        (
            "needs".to_owned(),
            but(
                "the default run does not run test target `needs` (`test = false` or \
                 `required-features`)"
            )
        )
    );
    // The run: the default run passes, and the instruments it does not stand
    // in for still fail it.
    write(root, "paths.txt", touched);
    let judged = run(
        root,
        &[
            "--plan",
            "plan-cover.toml",
            "--no-fail-fast",
            "--changed-paths",
            "paths.txt",
        ],
    );
    assert_eq!(
        judged.output.status.code(),
        Some(101),
        "{}",
        text(&judged.output)
    );
    let failed = judged
        .records
        .iter()
        .filter(|row| row["state"] == "failed")
        .map(|row| names(&row["requests"]).join("+"))
        .collect::<BTreeSet<_>>();
    assert!(failed.contains("gate"), "{}", text(&judged.output));
    assert!(
        text(&judged.output).contains("must_pass"),
        "{}",
        text(&judged.output)
    );
    assert_eq!(judged.result.unwrap()["passed"], false);

    // What the file may say does not depend on what changed: a request the
    // selection leaves out is still held to the plan's rules.
    write(
        root,
        "plan-inert.toml",
        &format!(
            "{header}[default]\ntargets = \"tests\"\n{}",
            instrument("lists", "lib = true\nargs = [\"--list\"]")
        ),
    );
    for paths in ["README.md\n", "crates/outer/src/lib.rs\n"] {
        let output = select("plan-inert.toml", Some(paths), &["--no-run"]);
        assert_eq!(output.status.code(), Some(2), "{}", text(&output));
        assert!(
            text(&output)
                .contains("`--list` makes a test harness exit successfully without running a test")
                && text(&output).contains("request `lists`"),
            "{}",
            text(&output)
        );
    }

    // A newline-separated line some tool altered names no file; matched as
    // written it would own nothing, meet no condition and leave a green run.
    for paths in [
        "docs/a.json\r\n",
        "\"crates/outer/src/caf\\303\\251.rs\"\n",
        "docs/a.json \n",
    ] {
        let output = select("plan.toml", Some(paths), &["--no-run"]);
        assert_eq!(
            output.status.code(),
            Some(2),
            "{paths:?}: {}",
            text(&output)
        );
        refused_record(&output);
        assert!(
            text(&output).contains("pass the paths NUL-separated"),
            "{}",
            text(&output)
        );
    }
    // NUL-separated, the same bytes are a path as written.
    let (status, active) = decided(&select("plan.toml", Some("docs/a.json\0"), &["--no-run"]));
    assert_eq!(status, Some(0));
    assert_eq!(active[0].0, "host-docs");
}

#[test]
fn a_plan_member_outside_the_workspace_root_is_tested_and_never_selected_by_path() {
    let world = world("test-plan-outside-root");
    let root = world.path().join("w");
    write(
        &root,
        "Cargo.toml",
        "[workspace]\nmembers=['a','../out']\nresolver='3'\n",
    );
    package(&root, "a", "", "#[test] fn plain() {}\n");
    package(
        world.path(),
        "out",
        "workspace='../w'\n",
        "#[test] fn plain() {}\n",
    );
    write(
        &root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [default]\ntargets = \"tests\"\n",
    );
    let select = |arguments: &[&str]| {
        let mut command = targo(&root);
        command.args(["--plan", "plan.toml", "--no-run", "--message-format=json"]);
        command.args(or_whole(arguments)).output().unwrap()
    };
    // The whole plan tests every member, whatever directory it is in.
    for arguments in [&[][..], &["-p", "out", "-p", "a"]] {
        let output = select(arguments);
        assert!(output.status.success(), "{}", text(&output));
        let record = first_record(&output);
        assert_eq!(
            record["members"]["selected"],
            serde_json::json!(["a", "out"])
        );
        assert_eq!(
            record["requests"][0]["packages"],
            serde_json::json!(["a", "out"])
        );
    }
    // No changed path can name a file of `out`, so its changes would never
    // select it: paths cannot say what changed here.
    write(&root, "paths.txt", "a/src/lib.rs\n");
    let output = select(&["--changed-paths", "paths.txt"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    refused_record(&output);
    assert!(
        text(&output).contains(
            "--changed-paths cannot select for this plan: plan member `out` has no directory \
             under the workspace root"
        ),
        "{}",
        text(&output)
    );
}

/// Three members whose lib tests fail in three ways: `host` in one test,
/// `mixed` in two, and `crash` by leaving the process mid-run with libtest's
/// own failure status. `host` also has an integration test that passes.
fn known_red_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host','mixed','crash']\nresolver='3'\n",
    );
    package(
        root,
        "host",
        "",
        "#[cfg(test)] mod m {\n\
         #[test] fn red() { panic!(\"red\") }\n\
         #[test] fn green() {}\n}\n",
    );
    write(root, "host/tests/it.rs", "#[test] fn shaky() {}\n");
    package(
        root,
        "mixed",
        "",
        "#[cfg(test)] mod m {\n\
         #[test] fn red() { panic!(\"red\") }\n\
         #[test] fn new() { panic!(\"new\") }\n}\n",
    );
    package(
        root,
        "crash",
        "",
        "#[cfg(test)] mod m { #[test] fn dies() { std::process::exit(101) } }\n",
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
[expect]
known-red = "expect/red.txt"
"#,
    );
}

/// Members whose test binaries a known-red row cannot be read for by name
/// or by result line: `a` and `b` each have an integration test `it` with a
/// failing `m::red`, and `noisy` writes result lines of its own to stdout.
fn unjudged_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['a','b','noisy','replay']\nresolver='3'\n",
    );
    for member in ["a", "b"] {
        package(root, member, "", "");
        write(
            root,
            &format!("{member}/tests/it.rs"),
            "mod m { #[test] fn red() { panic!(\"red\") } }\n",
        );
    }
    // Past libtest's capture, as a child process's output is.
    package(
        root,
        "noisy",
        "",
        "#[cfg(test)] mod m {\n\
         #[test] fn was_red() {}\n\
         #[test] fn chatty() {\n\
         use std::io::Write as _;\n\
         std::io::stdout().write_all(b\"\\nspawned a child\\ntest child::a ... ok\\n\
         test child::b ... ok\\n\").unwrap();\n}\n}\n",
    );
    // A failing test whose captured output libtest replays.
    package(
        root,
        "replay",
        "",
        "#[cfg(test)] mod m {\n\
         #[test] fn red() { println!(\"child said:\\ntest inner ... ok\"); panic!(\"red\") }\n}\n",
    );
    write(
        root,
        "plan.toml",
        r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
[expect]
known-red = "expect/red.txt"
"#,
    );
}

/// Stage 6 review: a known-red row is one binary's, and it is judged only
/// by result lines that are read.
#[test]
fn a_known_red_row_names_one_binary_and_is_unjudged_where_no_result_line_is_read() {
    let world = world("test-plan-known-red-unjudged");
    let root = world.path();
    unjudged_workspace(root);
    let list = |value: &Value| {
        names(value)
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };

    // `it::m::red` would excuse the failure of `a` and of `b` alike. The
    // plan is refused before any test, on a run and on a build, whatever
    // the selection: `-p a` alone is not a run where the row means `a`.
    write(root, "expect/red.txt", "it::m::red  # a only\n");
    for arguments in [
        &["--no-fail-fast", "-p", "a", "-p", "b"][..],
        &["--no-fail-fast", "-p", "a"],
        &["--no-run", "-p", "noisy"],
    ] {
        let seen = run(root, &[&["--plan", "plan.toml"][..], arguments].concat());
        let message = text(&seen.output);
        assert_eq!(seen.output.status.code(), Some(2), "{message}");
        assert!(
            message.contains(
                "row `it::m::red` names the test binary `it`, and 2 test targets have that \
                 crate name: test `it` of `a`, test `it` of `b`"
            ),
            "{message}"
        );
        assert!(seen.records.is_empty(), "{message}");
        closed_without_verdict(seen.result.as_ref(), "cannot-judge", &seen.output);
    }
    // Without a row for the shared name both fail as new failures.
    write(root, "expect/red.txt", "noisy::m::was_red\n");
    let seen = run(
        root,
        &[
            "--plan",
            "plan.toml",
            "--no-fail-fast",
            "-p",
            "a",
            "-p",
            "b",
        ],
    );
    assert_eq!(
        seen.output.status.code(),
        Some(101),
        "{}",
        text(&seen.output)
    );
    let result = seen.result.clone().unwrap();
    assert_eq!(result["requests"][0]["failed"], 2, "{result}");
    assert_eq!(result["requests"][0]["excused"], 0, "{result}");

    // `noisy::m::was_red` passed, so its row is stale; but the harness
    // printed `ok` lines its closing line does not count, so none of its
    // result lines is read. The run does not pass on rows nobody checked.
    let seen = run(
        root,
        &["--plan", "plan.toml", "--no-fail-fast", "-p", "noisy"],
    );
    let message = text(&seen.output);
    // Nothing failed; rows nobody could check are no red test either.
    assert_eq!(seen.output.status.code(), Some(2), "{message}");
    let result = seen.result.clone().unwrap();
    assert_eq!(result["passed"], false, "{result}");
    assert_eq!(result["outcome"], "cannot-judge", "{result}");
    assert_eq!(
        result["requests"],
        serde_json::json!([{
            "id": "default", "actions": 1, "failed": 0, "excused": 0, "tests": 2, "passed": true,
        }])
    );
    // The forged lines may land inside one of libtest's own, so the harness
    // printed 3 or 4 `ok` lines; its closing line counts 2 either way.
    let unjudged = result["known_red"]["unjudged"].as_array().unwrap();
    assert_eq!(unjudged.len(), 1, "{result}");
    let why = unjudged[0]["why"].as_str().unwrap();
    assert!(
        ["3", "4"].iter().any(|lines| {
            why == format!(
                "the harness printed {lines} `test <name> ... ok` lines and closed its run \
                 with 2 passed, so its result lines are not read"
            )
        }),
        "{result}"
    );
    assert_eq!(
        unjudged[0],
        serde_json::json!({
            "package": "noisy", "binary": "noisy", "failed": false, "why": why,
        })
    );
    assert!(list(&result["known_red"]["stale"]).is_empty(), "{result}");
    assert_eq!(
        list(&result["unmet"]),
        [format!(
            "known-red rows of test binary `noisy` (package `noisy`) in `expect/red.txt` \
             could not be judged, so a listed test that passed would go unseen: {why}"
        )]
    );
    assert!(message.contains("1 requirement not met"), "{message}");
    // The same harness with no row of its own is not held to this.
    write(root, "expect/red.txt", "replay::m::red\n");
    let seen = run(
        root,
        &["--plan", "plan.toml", "--no-fail-fast", "-p", "noisy"],
    );
    assert_eq!(seen.output.status.code(), Some(0), "{}", text(&seen.output));

    // A listed test failed, and libtest replayed a result line from its
    // output: the counts disagree, nothing is excused, and the run says so
    // rather than only failing.
    let seen = run(
        root,
        &["--plan", "plan.toml", "--no-fail-fast", "-p", "replay"],
    );
    let message = text(&seen.output);
    assert_eq!(seen.output.status.code(), Some(101), "{message}");
    let result = seen.result.clone().unwrap();
    assert_eq!(result["requests"][0]["excused"], 0, "{result}");
    let why = "the harness printed 1 `test <name> ... FAILED` line naming 1 test and 1 `test \
               <name> ... ok` line, and closed its run with 1 failed and 0 passed, so its \
               result lines are not read";
    assert_eq!(
        result["known_red"]["unjudged"],
        serde_json::json!([{
            "package": "replay", "binary": "replay", "failed": true, "why": why,
        }])
    );
    assert!(list(&result["unmet"]).is_empty(), "{result}");
    assert!(
        String::from_utf8_lossy(&seen.output.stderr).contains(&format!(
            "`expect/red.txt` lists tests of the test binary `replay` (package `replay`), and \
             its failure names no failed test, so nothing is excused: {why}"
        )),
        "{message}"
    );
}

/// Stage 6: the plan's known-red file is a ratchet. A harness that failed
/// only in tests the file lists does not fail the run; a failure it does not
/// list does, and so does a listed test that passed, unless its row is
/// `[flaky]`.
#[test]
fn a_known_red_failure_is_excused_and_a_new_failure_or_a_stale_row_fails_the_run() {
    let world = world("test-plan-known-red");
    let root = world.path();
    known_red_workspace(root);
    let member = |rows: &str, member: &str| {
        write(root, "expect/red.txt", rows);
        let seen = run(
            root,
            &["--plan", "plan.toml", "--no-fail-fast", "-p", member],
        );
        let result = seen
            .result
            .clone()
            .unwrap_or_else(|| panic!("no test-plan-result record: {}", text(&seen.output)));
        (seen, result)
    };
    let list = |value: &Value| {
        names(value)
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };

    // The listed test fails and nothing else does: exit 0. The harness's own
    // record still says it failed.
    let (seen, result) = member(
        "# why each row is red\n\nhost::m::red  # panics\nit::shaky # under load [flaky]\n",
        "host",
    );
    assert_eq!(seen.output.status.code(), Some(0), "{}", text(&seen.output));
    let failed = seen
        .records
        .iter()
        .filter(|row| row["state"] == "failed")
        .collect::<Vec<_>>();
    assert_eq!(failed.len(), 1, "{}", text(&seen.output));
    assert_eq!(
        (
            &failed[0]["target"],
            &failed[0]["kind"],
            &failed[0]["exit_code"]
        ),
        (
            &serde_json::json!("host"),
            &serde_json::json!("lib"),
            &serde_json::json!(101)
        )
    );
    assert_eq!(failed[0]["tests"], counts(1, 1, 0, 0));
    assert_eq!(result["passed"], true, "{result}");
    assert_eq!(
        result["requests"],
        serde_json::json!([{
            "id": "default", "actions": 2, "failed": 1, "excused": 1, "tests": 3, "passed": true,
        }])
    );
    let known = &result["known_red"];
    assert_eq!(known["file"], "expect/red.txt");
    assert_eq!(known["sha256"].as_str().unwrap().len(), 64, "{known}");
    assert_eq!(list(&known["excused"]), ["host::m::red"]);
    assert!(list(&known["new_failures"]).is_empty(), "{known}");
    assert!(list(&known["stale"]).is_empty(), "{known}");
    let stderr = String::from_utf8_lossy(&seen.output.stderr);
    assert!(
        stderr.contains(
            "lib `host` of `host` failed only in known-red tests (listed in \
             `expect/red.txt`): host::m::red"
        ),
        "{stderr}"
    );
    assert!(!stderr.contains("test failed, to rerun"), "{stderr}");

    // The same failure with no row for it is a new failure.
    let (seen, result) = member("# no row\n", "host");
    assert_eq!(
        seen.output.status.code(),
        Some(101),
        "{}",
        text(&seen.output)
    );
    assert_eq!(result["passed"], false, "{result}");
    assert_eq!(result["requests"][0]["excused"], 0, "{result}");
    assert_eq!(list(&result["known_red"]["new_failures"]), ["host::m::red"]);
    assert!(list(&result["known_red"]["excused"]).is_empty(), "{result}");
    let stderr = String::from_utf8_lossy(&seen.output.stderr);
    assert!(
        stderr.contains("new failure, not listed in `expect/red.txt`: host::m::red"),
        "{stderr}"
    );

    // A row of another binary with the same test path excuses nothing.
    let (seen, result) = member("it::m::red\nmixed::m::red\n", "host");
    assert_eq!(
        seen.output.status.code(),
        Some(101),
        "{}",
        text(&seen.output)
    );
    assert_eq!(list(&result["known_red"]["new_failures"]), ["host::m::red"]);

    // A listed test that passed is a stale row: the failure is excused and
    // the run still fails, until the row is deleted or marked flaky.
    let (seen, result) = member(
        "host::m::red\nit::shaky\nhost::m::green # [flaky]\n",
        "host",
    );
    assert_eq!(
        seen.output.status.code(),
        Some(101),
        "{}",
        text(&seen.output)
    );
    assert_eq!(result["passed"], false, "{result}");
    assert_eq!(result["requests"][0]["passed"], true, "{result}");
    assert_eq!(list(&result["known_red"]["stale"]), ["it::shaky"]);
    assert_eq!(list(&result["known_red"]["excused"]), ["host::m::red"]);
    let unmet = list(&result["unmet"]);
    assert_eq!(unmet.len(), 1, "{result}");
    assert!(
        unmet[0].starts_with(
            "known-red row `it::shaky` is stale: the test passed. Delete the row from \
             `expect/red.txt`"
        ),
        "{result}"
    );
    assert!(
        String::from_utf8_lossy(&seen.output.stderr).contains("1 requirement not met"),
        "{}",
        text(&seen.output)
    );

    // One listed and one unlisted failure in one harness: the harness is
    // not excused, and each test is named for what it is.
    let (seen, result) = member("mixed::m::red\n", "mixed");
    assert_eq!(
        seen.output.status.code(),
        Some(101),
        "{}",
        text(&seen.output)
    );
    assert_eq!(
        result["requests"],
        serde_json::json!([{
            "id": "default", "actions": 1, "failed": 1, "excused": 0, "tests": 2, "passed": false,
        }])
    );
    assert!(list(&result["known_red"]["excused"]).is_empty(), "{result}");
    assert_eq!(list(&result["known_red"]["not_excused"]), ["mixed::m::red"]);
    assert_eq!(
        list(&result["known_red"]["new_failures"]),
        ["mixed::m::new"]
    );

    // A harness that left mid-run named no failed test: its row excuses
    // nothing, though the process exited with libtest's failure status.
    let (seen, result) = member("crash::m::dies\n", "crash");
    assert_eq!(
        seen.output.status.code(),
        Some(101),
        "{}",
        text(&seen.output)
    );
    assert_eq!(seen.terminal(seen.action(&["default"]))["exit_code"], 101);
    assert_eq!(result["requests"][0]["excused"], 0, "{result}");
    assert!(list(&result["known_red"]["excused"]).is_empty(), "{result}");
    assert!(
        list(&result["known_red"]["new_failures"]).is_empty(),
        "{result}"
    );
    // The row matched a binary of the run and excused nothing: the result
    // and a note say why.
    assert_eq!(
        result["known_red"]["unjudged"],
        serde_json::json!([{
            "package": "crash", "binary": "crash", "failed": true,
            "why": "the harness printed no complete closing `test result:` line, so libtest \
                    did not report its failed tests",
        }])
    );
    let stderr = String::from_utf8_lossy(&seen.output.stderr);
    assert!(
        stderr.contains(
            "`expect/red.txt` lists tests of the test binary `crash` (package `crash`), and \
             its failure names no failed test, so nothing is excused: the harness printed no \
             complete closing `test result:` line"
        ),
        "{stderr}"
    );

    // A run that stops at its first failure has no verdict, so the file is
    // not read as excusing anything there: refused before any test.
    write(root, "expect/red.txt", "host::m::red\n");
    let stopping = run(root, &["--plan", "plan.toml", "-p", "host"]);
    let message = text(&stopping.output);
    assert_eq!(stopping.output.status.code(), Some(2), "{message}");
    assert!(
        message.contains(
            "sets `[expect] known-red`, which is judged over a run that ran to its end; pass \
             --no-fail-fast"
        ),
        "{message}"
    );
    assert!(stopping.records.is_empty(), "{message}");

    // The file is read on every route: a row that could match no test, or a
    // row written twice, is refused by a build as well.
    for (rows, expected) in [
        (
            "host::m::red\nm_red\n",
            "line 2: `m_red` is not `<test binary>::<test path>`",
        ),
        (
            "host::m::red\nhost::m::red # again\n",
            "line 2: `host::m::red` is listed twice",
        ),
    ] {
        write(root, "expect/red.txt", rows);
        let mut build = targo(root);
        build.args(["--plan", "plan.toml", "--no-run", "-p", "host"]);
        let message = refusal(build);
        assert!(
            message.contains("invalid `[expect] known-red` file") && message.contains(expected),
            "{message}"
        );
    }
}

/// Stage 6: a plan's `[harness]` table is the harness policy of its run, and
/// the only one: `build.test-harnesses` beside a plan is refused on every
/// route.
#[test]
fn a_plan_harness_table_is_the_policy_of_its_run_and_the_only_one() {
    let world = world("test-plan-harness");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['left','right']\nresolver='3'\n",
    );
    let slow = "#[test] fn slow() { std::thread::sleep(std::time::Duration::from_millis(600)) }\n";
    package(root, "left", "", slow);
    package(root, "right", "", slow);
    write(root, "right/tests/it.rs", slow);
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    let table = "[harness.left.lib]\nexclusive = true\n[harness.right.test.it]\nweight = 2\n";
    write(root, "plan.toml", &format!("{plan}{table}"));
    let jobs = ["-j4", "--config", "build.test-jobs=4"];

    let mut arguments = vec!["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"];
    arguments.extend(jobs);
    let applied = run(root, &arguments);
    assert!(applied.output.status.success(), "{}", text(&applied.output));
    let admission = |run: &Run, package: &str, kind: &str| {
        let rows = run
            .records
            .iter()
            .filter(|row| row["package"] == package && row["kind"] == kind)
            .collect::<Vec<_>>();
        assert!(!rows.is_empty(), "{package} {kind}: {}", text(&run.output));
        let admissions = rows
            .iter()
            .map(|row| (row["weight"].as_u64().unwrap(), row["exclusive"] == true))
            .collect::<BTreeSet<_>>();
        assert_eq!(admissions.len(), 1, "{}", text(&run.output));
        (
            rows[0]["index"].as_u64().unwrap(),
            *admissions.first().unwrap(),
        )
    };
    let (left, left_admission) = admission(&applied, "left", "lib");
    let (right, right_admission) = admission(&applied, "right", "lib");
    let (it, it_admission) = admission(&applied, "right", "test");
    assert_eq!(left_admission, (1, true));
    assert_eq!(right_admission, (1, false));
    assert_eq!(it_admission, (2, false));
    // The exclusive harness ran with nothing beside it: no other action's
    // `running` record lies between its own `running` and `passed`.
    let (began, ended) = (
        applied.at(left, "running").unwrap(),
        applied.at(left, "passed").unwrap(),
    );
    for other in [right, it] {
        let started = applied.at(other, "running").unwrap();
        let finished = applied.at(other, "passed").unwrap();
        assert!(
            finished < began || started > ended,
            "action {other} ran beside the exclusive one: {}",
            text(&applied.output)
        );
    }

    // Without the table the same run has no such policy.
    write(root, "plan.toml", plan);
    let plain = run(root, &arguments);
    assert!(plain.output.status.success(), "{}", text(&plain.output));
    assert_eq!(admission(&plain, "left", "lib").1, (1, false));
    assert_eq!(admission(&plain, "right", "test").1, (1, false));

    // A second source of policy is refused, with a `[harness]` table in the
    // plan or without one, by a run, by a build and by a selection that
    // performs nothing.
    write(root, "changed", "README.md\n");
    for text_of_plan in [format!("{plan}{table}"), plan.to_owned()] {
        write(root, "plan.toml", &text_of_plan);
        for route in [
            &["--no-fail-fast"][..],
            &["--no-run"],
            &["--changed-paths", "changed"],
        ] {
            let second = run(
                root,
                &[
                    &["--plan", "plan.toml"][..],
                    &or_whole(route),
                    &["--config", "build.test-harnesses.right.lib.weight=2"],
                ]
                .concat(),
            );
            let message = text(&second.output);
            assert_eq!(second.output.status.code(), Some(2), "{route:?}: {message}");
            assert!(
                message.contains("build.test-harnesses.right is set beside test plan `")
                    && message.contains("a plan's `[harness]` table is the only harness policy"),
                "{route:?}: {message}"
            );
            assert!(second.records.is_empty(), "{route:?}: {message}");
            assert!(!message.contains("Compiling"), "{route:?}: {message}");
        }
    }
    // The same selection without the second source performs nothing and
    // exits 0.
    let idle = run(root, &["--plan", "plan.toml", "--changed-paths", "changed"]);
    assert_eq!(idle.output.status.code(), Some(0), "{}", text(&idle.output));
}

/// Every JSON record an invocation wrote, in order.
fn stream(output: &Output) -> Vec<Value> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .collect()
}

/// The records with `reason`, and where each is in the stream.
fn reasoned<'a>(rows: &'a [Value], reason: &str) -> Vec<(usize, &'a Value)> {
    rows.iter()
        .enumerate()
        .filter(|(_, row)| row["reason"] == reason)
        .collect()
}

/// The last record, which a run that ran to its end closes with.
fn plan_result(rows: &[Value], output: &Output) -> Value {
    let results = reasoned(rows, "test-plan-result");
    assert_eq!(results.len(), 1, "{}", text(output));
    assert_eq!(results[0].0, rows.len() - 1, "{}", text(output));
    results[0].1.clone()
}

/// A member `shared` that depends on a member `helper`, and under
/// `crates/own` a workspace of its own whose package is also `shared` and
/// whose `helper` is another crate of that name.
fn own_workspace_fixture(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nresolver='3'\nmembers=['shared','helper']\n",
    );
    package(
        root,
        "helper",
        "",
        "pub const WHO: &str = \"root\";\n#[test] fn helper_side() {}\n",
    );
    package(
        root,
        "shared",
        "[dependencies]\nhelper={path='../helper'}\n",
        "#[test] fn root_side() { assert_eq!(helper::WHO, \"root\"); }\n",
    );
    write(
        root,
        "crates/own/Cargo.toml",
        "[package]\nname='shared'\nversion='9.0.0'\nedition='2024'\n[workspace]\n\
         [dependencies]\nhelper={path='helper'}\n",
    );
    write(
        root,
        "crates/own/helper/Cargo.toml",
        "[package]\nname='helper'\nversion='9.0.0'\nedition='2024'\n",
    );
    write(
        root,
        "crates/own/helper/src/lib.rs",
        "pub const WHO: &str = \"own\";\n",
    );
    own_lib(
        root,
        "#[test] fn own_side() { assert_eq!(helper::WHO, \"own\"); }\n",
    );
    own_plan(root, "");
}

fn own_lib(root: &Path, lib: &str) {
    write(root, "crates/own/src/lib.rs", lib);
    gate_own(root);
}

fn own_plan(root: &Path, cfg: &str) {
    write(
        root,
        "plan.toml",
        &format!(
            "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
             attribute-under = [\"crates/\", \"shared/\"]\n\
             [default]\ntargets = \"tests\"\nmin-tests = 1\n\
             [[workspace]]\nmanifest = \"crates/own/Cargo.toml\"\n{cfg}"
        ),
    );
    gate_own(root);
}

/// Gates the fixture's own-workspace library as its plan's entry says: an
/// entry's `cfg` is the crate-level `#![cfg(..)]` its library carries, and a
/// run refuses an entry that states another.
fn gate_own(root: &Path) {
    let plan = fs::read_to_string(root.join("plan.toml")).unwrap_or_default();
    let cfg = plan
        .lines()
        .find_map(|line| line.strip_prefix("cfg = '")?.strip_suffix('\''));
    let lib = root.join("crates/own/src/lib.rs");
    let Ok(text) = fs::read_to_string(&lib) else {
        return;
    };
    let body = text
        .lines()
        .filter(|line| !line.starts_with("#![cfg("))
        .map(|line| format!("{line}\n"))
        .collect::<String>();
    let gated = match cfg {
        Some(cfg) => format!("#![cfg({cfg})]\n{body}"),
        None => body,
    };
    if gated != text {
        fs::write(&lib, gated).unwrap();
    }
}

const OWN: &str = "crates/own/Cargo.toml";

/// The one `phases` row of the fixture's plan, as `(state, tests)`.
fn own_phase(result: &Value, output: &Output) -> (String, Value) {
    let phases = result["phases"].as_array().unwrap();
    assert_eq!(phases.len(), 1, "{}", text(output));
    assert_eq!(phases[0]["kind"], "workspace", "{}", text(output));
    assert_eq!(phases[0]["manifest"], OWN, "{}", text(output));
    assert_eq!(phases[0]["env"], Value::Null, "{}", text(output));
    (
        phases[0]["state"].as_str().unwrap().to_owned(),
        phases[0]["tests"].clone(),
    )
}

/// A plan runs inside a build-slot job. There the compiler refuses any
/// invocation that brings no scheduler (`BUILD_SLOT_CPU_PROTOCOL` makes its
/// context strict), and the query that holds a `[[workspace]]` `cfg` to the
/// values the compiler knows was run bare: the crates plan, whose
/// trust-worker-linux row has a `cfg`, was refused there before it built
/// anything.
#[test]
fn a_workspace_cfg_is_checked_inside_a_build_slot_job() {
    let world = world("test-plan-own-slot");
    let root = world.path();
    own_workspace_fixture(root);
    own_plan(root, "cfg = 'target_os = \"none\"'\n");
    let output = targo(root)
        .env("RUSTFLAGS", "-Zthreads=1")
        .env("BUILD_SLOT_CPU_PROTOCOL", "1")
        .args([
            "--plan",
            "plan.toml",
            "--whole-plan",
            "--message-format=json",
        ])
        .args(["--no-fail-fast", "-j2", "--config", "build.test-jobs=2"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    let result = plan_result(&rows, &output);
    assert_eq!(result["passed"], true);
    assert_eq!(
        own_phase(&result, &output),
        ("not-applicable".to_owned(), Value::Null)
    );
}

/// An entry's `cfg` is its library's gate. The crates plan's
/// trust-worker-linux row says `target_os = "linux"` because its library is
/// `#![cfg(target_os = "linux")]`; had the library lost that line, the plan's
/// stale `cfg` took the workspace out of every run on macOS and the run
/// passed with SKIPPED, its tests never run by any lane. The run refuses an
/// entry whose `cfg` is not its library's, whichever way they differ, and
/// before it builds anything; a listing refuses it too.
#[test]
fn a_workspace_cfg_that_is_not_its_librarys_gate_is_refused() {
    let world = world("test-plan-own-stale-cfg");
    let root = world.path();
    own_workspace_fixture(root);
    let run = |arguments: &[&str]| {
        write(root, "paths.txt", "crates/own/src/lib.rs\n");
        targo(root)
            .env("RUSTFLAGS", "-Zthreads=1")
            .args(["--plan", "plan.toml", "--message-format=json"])
            .args(["--changed-paths", "paths.txt", "--no-fail-fast"])
            .args(arguments)
            .output()
            .unwrap()
    };
    let refused = |output: &Output, stated: &str, gate: &str| {
        assert_eq!(output.status.code(), Some(2), "{}", text(output));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(&format!(
                "the entry states {stated} and the library of `shared` is gated on {gate}"
            )) && !stderr.contains("SKIPPED")
                && !stderr.contains("NOT RUN")
                && !stderr.contains("Compiling"),
            "{}",
            text(output)
        );
    };
    // The plan says the workspace is for no target here, and its library
    // says nothing of the kind: its tests would run here.
    own_plan(root, "cfg = 'target_os = \"none\"'\n");
    let unit = "#[test] fn own_side() { assert_eq!(helper::WHO, \"own\"); }\n";
    write(root, "crates/own/src/lib.rs", unit);
    let output = run(&[]);
    refused(&output, "`cfg = 'target_os = \"none\"'`", "no `cfg`");
    closed_without_verdict(stream(&output).last(), "cannot-judge", &output);
    let listed = targo(root)
        .args([
            "--plan",
            "plan.toml",
            "--select-only",
            "--reached",
            "crates/own",
        ])
        .output()
        .unwrap();
    assert_eq!(listed.status.code(), Some(2), "{}", text(&listed));
    // The other way: a gated library the entry does not gate.
    own_plan(root, "");
    write(
        root,
        "crates/own/src/lib.rs",
        &format!("#![cfg(target_os = \"none\")]\n{unit}"),
    );
    refused(&run(&[]), "no `cfg`", "`cfg = 'target_os = \"none\"'`");
    // Another predicate is another gate, even one that holds here too.
    own_plan(root, "cfg = 'unix'\n");
    write(
        root,
        "crates/own/src/lib.rs",
        &format!("#![cfg(not(windows))]\n{unit}"),
    );
    refused(&run(&[]), "`cfg = 'unix'`", "`cfg = 'not(windows)'`");
    // The entry and its library agree: not run on this target, and said so.
    own_plan(root, "cfg = 'target_os = \"none\"'\n");
    let output = run(&[]);
    assert!(output.status.success(), "{}", text(&output));
    let result = plan_result(&stream(&output), &output);
    assert_eq!(
        own_phase(&result, &output),
        ("not-applicable".to_owned(), Value::Null)
    );
}

// Stage 8: a crate that is its own workspace is tested under its own
// manifest, as a phase before the plan's requests. Its package may carry the
// name of a member, and its dependencies are its own.
/// A `[[workspace]]` phase is part of the lane, and runs in the lane's pool:
/// the plan's `[run] test-jobs` and `test-weight` are its harnesses' credits
/// too. It ran them one at a time at weight 1, whatever the plan said: the
/// crates plan's trust-spec-temporal phase took its four executables in turn.
#[test]
fn a_workspace_of_its_own_runs_in_the_plans_pool() {
    let world = world("test-plan-own-workspace-pool");
    let root = world.path();
    own_workspace_fixture(root);
    own_plan(root, "[run]\ntest-jobs = 4\ntest-weight = 2\n");
    let output = targo(root)
        .env("RUSTFLAGS", "-Zthreads=1")
        .args(["--plan", "plan.toml", "--message-format=json"])
        .args(or_whole(&["--no-fail-fast"]))
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    let executions = reasoned(&rows, "test-execution");
    let passed = executions
        .iter()
        .filter(|(_, row)| row["state"] == "passed")
        .collect::<Vec<_>>();
    assert_eq!(passed.len(), 3, "{}", text(&output));
    assert!(
        passed
            .iter()
            .any(|(_, row)| row["package_id"].as_str().unwrap().contains("crates/own")),
        "{}",
        text(&output)
    );
    for (_, row) in &passed {
        assert_eq!(row["weight"], 2, "{row}");
    }
}

#[test]
fn a_workspace_of_its_own_is_tested_under_its_own_manifest_beside_a_same_named_member() {
    let world = world("test-plan-own-workspace");
    let root = world.path();
    own_workspace_fixture(root);
    let plan = |arguments: &[&str]| {
        targo(root)
            .env("RUSTFLAGS", "-Zthreads=1")
            .args(["--plan", "plan.toml", "--message-format=json"])
            .args(or_whole(arguments))
            .output()
            .unwrap()
    };
    let changed = |paths: &str, arguments: &[&str]| {
        write(root, "paths.txt", paths);
        let mut all = vec!["--changed-paths", "paths.txt"];
        all.extend(arguments);
        plan(&all)
    };
    // The test lines of the two packages named `shared`: (own, root).
    let ran = |rows: &[Value]| {
        let lines = |wanted: &str| {
            reasoned(rows, "test-output")
                .iter()
                .filter_map(|(_, row)| row["line"].as_str())
                .any(|line| line.starts_with(wanted))
        };
        (lines("test own_side ... "), lines("test root_side ... "))
    };

    // The whole plan: the workspace first, then the requests, one verdict.
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(rows[0]["reason"], "test-plan", "{}", text(&output));
    assert_eq!(rows[0]["workspaces"], serde_json::json!([OWN]));
    let phase = reasoned(&rows, "test-plan-phase");
    assert_eq!(phase.len(), 2, "{}", text(&output));
    let (start, end) = (phase[0].0, phase[1].0);
    for (_, row) in &phase {
        assert_eq!(row["schema"], "targo.test-plan-phase.v1");
        assert_eq!(row["kind"], "workspace");
        assert_eq!(row["manifest"], OWN);
    }
    assert_eq!(phase[0].1["state"], "started");
    assert_eq!(phase[1].1["state"], "passed");
    assert_eq!(phase[1].1["tests"], 1);
    // Two packages named `shared` ran, each one test executable: the
    // workspace's own inside its phase, the member's after it.
    let executions = reasoned(&rows, "test-execution");
    let shared = executions
        .iter()
        .filter(|(_, row)| row["state"] == "passed" && row["package"] == "shared")
        .collect::<Vec<_>>();
    assert_eq!(shared.len(), 2, "{}", text(&output));
    for (at, row) in &executions {
        assert_eq!(row["schema"], "targo.test-execution.v3");
        assert_eq!(row["requests"], serde_json::json!(["default"]));
        let id = row["package_id"].as_str().unwrap();
        let own = id.contains("crates/own");
        assert_eq!(own, start < *at && *at < end, "{row}");
        assert_eq!(own, id.contains("9.0.0"), "{row}");
        assert!(own || row["package"] == "shared" || row["package"] == "helper");
    }
    assert_eq!(ran(&rows), (true, true), "{}", text(&output));
    // The phase's verdict is its own record, inside the phase; it asks the
    // plan's `min-tests` of the workspace's member.
    let verdicts = reasoned(&rows, "test-plan-phase-result");
    assert_eq!(verdicts.len(), 1, "{}", text(&output));
    assert!(start < verdicts[0].0 && verdicts[0].0 < end);
    let verdict = verdicts[0].1;
    assert_eq!(verdict["phase"], OWN);
    assert_eq!(verdict["passed"], true);
    assert_eq!(
        verdict["members"],
        serde_json::json!([{"package": "shared", "tests": 1, "min_tests": 1, "passed": true}])
    );
    assert_eq!(verdict["phases"], serde_json::json!([]));
    let result = plan_result(&rows, &output);
    assert_eq!(result["phase"], Value::Null);
    assert_eq!(result["passed"], true);
    assert_eq!(result["narrowed"], false);
    assert_eq!(own_phase(&result, &output), ("passed".to_owned(), 1.into()));
    // The workspace's test is not credited to the member of its name.
    assert_eq!(
        result["members"],
        serde_json::json!([
            {"package": "helper", "tests": 1, "min_tests": 1, "passed": true},
            {"package": "shared", "tests": 1, "min_tests": 1, "passed": true},
        ]),
        "{}",
        text(&output)
    );

    // A change in the workspace alone runs the workspace alone; a change in
    // the member alone leaves the workspace out, and says so.
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (true, false), "{}", text(&output));
    let result = plan_result(&rows, &output);
    assert_eq!(result["requests"], serde_json::json!([]));
    assert_eq!(own_phase(&result, &output), ("passed".to_owned(), 1.into()));
    let output = changed("shared/src/lib.rs\n", &["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (false, true), "{}", text(&output));
    let result = plan_result(&rows, &output);
    assert_eq!(
        own_phase(&result, &output),
        ("not-selected".to_owned(), Value::Null)
    );
    assert_eq!(reasoned(&rows, "test-plan-phase").len(), 1);

    // `--request` reproduces named requests; the workspace is none of them,
    // and the result says the run is not the selection's verdict.
    let output = plan(&["--no-fail-fast", "--request", "default"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (false, true), "{}", text(&output));
    let result = plan_result(&rows, &output);
    assert_eq!(
        own_phase(&result, &output),
        ("left-out".to_owned(), Value::Null)
    );
    assert_eq!(result["narrowed"], true);
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--request leaves workspace `crates/own/Cargo.toml` out of this run"),
        "{}",
        text(&output)
    );

    // `--no-run` builds the workspace's tests and runs none.
    let output = plan(&["--no-run"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (false, false), "{}", text(&output));
    let phase = reasoned(&rows, "test-plan-phase");
    assert_eq!(phase.len(), 2, "{}", text(&output));
    assert_eq!(phase[1].1["state"], "built");
    assert!(
        rows.iter().any(|row| row["reason"] == "compiler-artifact"
            && row["package_id"].as_str().unwrap().contains("crates/own")
            && row["profile"]["test"] == true),
        "{}",
        text(&output)
    );

    // A cfg that does not hold for the target: the workspace is not built
    // and not run, and is never counted as tested. One that holds runs it.
    own_plan(root, "cfg = 'target_os = \"none\"'\n");
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (false, true), "{}", text(&output));
    assert!(
        !rows
            .iter()
            .filter_map(|row| row["package_id"].as_str())
            .any(|id| id.contains("crates/own")),
        "{}",
        text(&output)
    );
    let result = plan_result(&rows, &output);
    assert_eq!(result["passed"], true);
    assert_eq!(
        own_phase(&result, &output),
        ("not-applicable".to_owned(), Value::Null)
    );
    let host = host_triple();
    assert_eq!(
        result["phases"][0]["why"],
        format!("its `cfg = 'target_os = \"none\"'` does not hold for {host}")
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("workspace `crates/own/Cargo.toml` was NOT RUN"),
        "{}",
        text(&output)
    );
    own_plan(root, "cfg = 'all(unix, not(target_os = \"none\"))'\n");
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (true, false), "{}", text(&output));
    own_plan(root, "");

    // A failing workspace fails the run. With `--no-fail-fast` the requests
    // still run and the one verdict counts it; without, the run stops there.
    own_lib(
        root,
        "#[test] fn own_side() { assert_eq!(helper::WHO, \"root\"); }\n",
    );
    let output = plan(&["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (true, true), "{}", text(&output));
    let result = plan_result(&rows, &output);
    assert_eq!(result["passed"], false);
    assert_eq!(own_phase(&result, &output), ("failed".to_owned(), 1.into()));
    assert_eq!(
        result["unmet"],
        serde_json::json!([
            "workspace `crates/own/Cargo.toml` failed: 1 target failed: (its own records name \
             the failures)"
        ])
    );
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    // The failure is reported where it is, rerun by a command of its own:
    // `--manifest-path` added to this invocation would run the plan against
    // that workspace.
    let manifest = root.join(OWN);
    let command = format!(
        "to rerun run `targo --unverified test --manifest-path {} --tests`",
        manifest.display()
    );
    assert!(
        stderr.contains(&command)
            && !stderr.contains("to rerun pass `--manifest-path")
            && stderr.contains("workspace `crates/own/Cargo.toml` failed: 1 target failed:"),
        "{stderr}"
    );
    // The phase's one request is not the plan's `[default]`: its lines are
    // labelled with the workspace, the member's with its request.
    let running = |label: &str| {
        stderr
            .lines()
            .filter(|line| line.trim_start().starts_with("Running") && line.ends_with(label))
            .count()
    };
    assert_eq!(running(" [workspace crates/own/Cargo.toml]"), 1, "{stderr}");
    assert_eq!(running(" [default]"), 2, "{stderr}");
    let output = plan(&[]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (true, false), "{}", text(&output));
    closed_without_verdict(rows.last(), "failed", &output);
    assert_eq!(reasoned(&rows, "test-plan-result").len(), 1);
    // The invocation ends in the phase, and the phase's `started` record is
    // still closed: an unclosed one is a run that was cut off.
    let phase = reasoned(&rows, "test-plan-phase");
    assert_eq!(phase.len(), 2, "{}", text(&output));
    assert_eq!(phase[0].1["state"], "started");
    assert_eq!(phase[1].1["state"], "failed");
    // It stopped at its first failure, so it has no count.
    assert_eq!(phase[1].1["tests"], Value::Null);
    // Only the invocation's closing record follows it.
    assert_eq!(phase[1].0, rows.len() - 2, "{}", text(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("plan.toml`, workspace `crates/own/Cargo.toml`"),
        "{}",
        text(&output)
    );
    // With no request to run, the failed workspace is still the verdict.
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let rows = stream(&output);
    let result = plan_result(&rows, &output);
    assert_eq!(result["passed"], false);
    assert_eq!(own_phase(&result, &output), ("failed".to_owned(), 1.into()));

    // What the plan asks of each member it asks of the workspace's: one
    // that reports no test has not been tested.
    own_lib(root, "pub fn nothing() {}\n");
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let rows = stream(&output);
    let verdict = reasoned(&rows, "test-plan-phase-result")[0].1.clone();
    assert_eq!(
        verdict["members"],
        serde_json::json!([{"package": "shared", "tests": 0, "min_tests": 1, "passed": false}])
    );
    let result = plan_result(&rows, &output);
    assert_eq!(own_phase(&result, &output), ("failed".to_owned(), 0.into()));

    // A workspace is listed to be tested: one whose run reports no test at
    // all fails whether or not the plan sets a `min-tests`.
    let floorless = |cfg: &str| {
        write(
            root,
            "plan.toml",
            &format!(
                "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                 [default]\ntargets = \"tests\"\n\
                 [[workspace]]\nmanifest = \"crates/own/Cargo.toml\"\n{cfg}"
            ),
        );
        gate_own(root);
    };
    floorless("");
    let output = plan(&["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let rows = stream(&output);
    // The requests after it still ran.
    assert_eq!(ran(&rows), (false, true), "{}", text(&output));
    let result = plan_result(&rows, &output);
    assert_eq!(own_phase(&result, &output), ("failed".to_owned(), 0.into()));
    assert_eq!(
        result["phases"][0]["why"],
        "its run reported 0 tests; a workspace that judges no test has not been tested"
    );
    assert_eq!(
        result["unmet"],
        serde_json::json!([
            "workspace `crates/own/Cargo.toml` failed: its run reported 0 tests; a workspace \
             that judges no test has not been tested (its own records name the failures)"
        ])
    );
    let output = plan(&[]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(ran(&rows), (false, false), "{}", text(&output));
    let phase = reasoned(&rows, "test-plan-phase");
    assert_eq!(phase[phase.len() - 1].1["state"], "failed");
    assert_eq!(phase[phase.len() - 1].1["tests"], 0);
    // With one test it passes under the same plan.
    own_lib(
        root,
        "#[test] fn own_side() { assert_eq!(helper::WHO, \"own\"); }\n",
    );
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));

    // A `cfg` says for which targets the workspace is tested. One that can
    // hold for no target, or that something other than the target decides,
    // would report the workspace as not for this target on every host and
    // let the run pass: each is refused, and nothing is built.
    let never_built =
        |output: &Output| {
            assert_eq!(output.status.code(), Some(2), "{}", text(output));
            let rows = stream(output);
            assert!(
                !rows.iter().any(|row| row["reason"] == "compiler-artifact"
                    || row["reason"] == "test-plan-phase"),
                "{}",
                text(output)
            );
            closed_without_verdict(rows.last(), "cannot-judge", output);
        };
    for (cfg, atom) in [
        ("linux", "`linux`"),
        ("feature = \"x\"", "`feature = \"x\"`"),
        ("test", "`test`"),
        ("debug_assertions", "`debug_assertions`"),
        ("not(any(unix, macos))", "`macos`"),
    ] {
        floorless(&format!("cfg = '{cfg}'\n"));
        let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
        never_built(&output);
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(
            stderr.contains(&format!("{atom} is not a cfg of the target")),
            "{cfg}: {stderr}"
        );
    }
    // A value the compiler knows of no target, whichever way it is used and
    // whether or not this run selects the workspace.
    for cfg in [
        "target_os = \"Linux\"",
        "not(target_os = \"Linux\")",
        "all(unix, target_env = \"gnoo\")",
    ] {
        floorless(&format!("cfg = '{cfg}'\n"));
        for paths in ["crates/own/src/lib.rs\n", "shared/src/lib.rs\n"] {
            let output = changed(paths, &["--no-fail-fast"]);
            never_built(&output);
            let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
            assert!(
                stderr.contains("holds for no target the compiler knows"),
                "{cfg}: {stderr}"
            );
        }
    }
    // A value it knows is held against the target as before.
    floorless("cfg = 'not(target_os = \"none\")'\n");
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(ran(&stream(&output)), (true, false), "{}", text(&output));

    // A manifest is written one way. Another spelling of the same file
    // would own no changed path, and the change would exit 0 untested.
    for manifest in ["crates/own/./Cargo.toml", "crates/own//Cargo.toml"] {
        write(
            root,
            "plan.toml",
            &format!(
                "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                 [default]\ntargets = \"tests\"\n[[workspace]]\nmanifest = \"{manifest}\"\n"
            ),
        );
        let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
        never_built(&output);
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("is not a `Cargo.toml` named by a normal path"),
            "{}",
            text(&output)
        );
    }

    // Configuration in the workspace's directory is read by a run inside
    // it and not by this invocation: the phase would test another build.
    floorless("");
    write(
        root,
        "crates/own/.cargo/config.toml",
        "[env]\nOWN_CONFIG = '1'\n",
    );
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    never_built(&output);
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("is not read by a phase of this invocation"),
        "{}",
        text(&output)
    );
    // Where the run does not select the workspace, nothing reads it.
    let output = changed("shared/src/lib.rs\n", &["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    fs::remove_dir_all(root.join("crates/own/.cargo")).unwrap();
    let output = changed("crates/own/src/lib.rs\n", &["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));

    // A manifest that is a member of the invocation's workspace is tested
    // by a request, never by a phase.
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [default]\ntargets = \"tests\"\n[[workspace]]\nmanifest = \"shared/Cargo.toml\"\n",
    );
    let output = plan(&["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("belongs to the invocation's own workspace; test it by a request"),
        "{}",
        text(&output)
    );
}

// Trust: crates/trust-sha2-compat is the member `sha2`, and the registry's
// `sha2` is in the same resolve. The script lane named it `-p sha2`, which
// was refused as ambiguous, and the whole run recorded no test executable
// (the landing gate, 2026-10-14). A plan names each member by its package
// id, which no dependency shares.
#[test]
fn a_member_whose_name_a_dependency_carries_is_tested_by_its_package_id() {
    let world = world("test-plan-same-name");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nresolver='3'\nmembers=['dup','user']\nexclude=['vendor/dup']\n",
    );
    package(root, "dup", "", "#[test] fn member_side() {}\n");
    write(
        root,
        "vendor/dup/Cargo.toml",
        "[package]\nname='dup'\nversion='0.2.0'\nedition='2024'\n",
    );
    write(
        root,
        "vendor/dup/src/lib.rs",
        "pub const WHO: &str = \"vendored\";\n#[test] fn vendored_side() {}\n",
    );
    package(
        root,
        "user",
        "[dependencies]\nother={package='dup',path='../vendor/dup'}\n",
        "#[test] fn user_side() { assert_eq!(other::WHO, \"vendored\"); }\n",
    );
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [default]\ntargets = \"tests\"\n",
    );
    // Control: by its name the member is ambiguous wherever the run also
    // tests a member that depends on the other `dup`.
    let named = targo(root)
        .args(["-p", "dup", "-p", "user", "--no-run"])
        .output()
        .unwrap();
    assert!(!named.status.success(), "{}", text(&named));
    assert!(text(&named).contains("is ambiguous"), "{}", text(&named));

    for (change, reached) in [
        ("dup/src/lib.rs\nuser/src/lib.rs\n", &[][..]),
        ("README.md\n", &["--reached", "dup", "--reached", "user"][..]),
    ] {
        write(root, "paths.txt", change);
        let output = targo(root)
            .args(["--plan", "plan.toml", "--message-format=json"])
            .args(["--changed-paths", "paths.txt"])
            .args(reached)
            .output()
            .unwrap();
        assert!(output.status.success(), "{change:?}: {}", text(&output));
        let rows = stream(&output);
        assert_eq!(
            rows[0]["members"]["selected"],
            serde_json::json!(["dup", "user"])
        );
        let ran = |wanted: &str| {
            reasoned(&rows, "test-output")
                .iter()
                .filter_map(|(_, row)| row["line"].as_str())
                .any(|line| line.starts_with(wanted))
        };
        assert!(ran("test member_side ... ok"), "{change:?}: {}", text(&output));
        assert!(ran("test user_side ... ok"), "{change:?}: {}", text(&output));
        assert!(!ran("test vendored_side ... "), "{change:?}: {}", text(&output));
        assert_eq!(plan_result(&rows, &output)["passed"], true);
    }
}

/// Members `consumer`, whose test runs the tool the variable names, and
/// `bystander`, whose test requires the variable to be unset; and under
/// `tools/gadget` a workspace of its own that builds the bin `gadget`.
fn tool_fixture(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nresolver='3'\nmembers=['consumer','bystander']\n",
    );
    package(
        root,
        "consumer",
        "",
        r#"
#[test]
fn runs_the_tool() {
    let path = std::path::PathBuf::from(
        std::env::var_os("TOOL_GADGET_BIN").expect("TOOL_GADGET_BIN is set for a consumer"),
    );
    // The private copy, not the file a later build may relink.
    let directory = path.parent().unwrap().file_name().unwrap().to_str().unwrap();
    assert!(directory.starts_with(".targo-plan-tool-"), "{}", path.display());
    let output = std::process::Command::new(&path).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&output.stdout), "gadget of its own workspace\n");
}
"#,
    );
    package(
        root,
        "bystander",
        "",
        "#[test] fn sees_no_tool() { assert!(std::env::var_os(\"TOOL_GADGET_BIN\").is_none()); }\n",
    );
    write(
        root,
        "tools/gadget/Cargo.toml",
        "[package]\nname='gadget'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    );
    gadget(
        root,
        "fn main() { println!(\"gadget of its own workspace\"); }\n",
    );
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         attribute-under = [\"consumer/\", \"bystander/\", \"tools/\"]\n\
         [default]\ntargets = \"tests\"\nmin-tests = 1\n\
         [[tool]]\nmanifest = \"tools/gadget/Cargo.toml\"\nbin = \"gadget\"\n\
         env = \"TOOL_GADGET_BIN\"\nneeded-by = [\"consumer\"]\n",
    );
}

fn gadget(root: &Path, main: &str) {
    write(root, "tools/gadget/src/main.rs", main);
}

// Stage 8: a tool another workspace builds is built under its own manifest
// when a request tests a member that needs it, and its path is handed to
// that member's test executables and to no other.
#[test]
fn a_tool_is_built_under_its_own_manifest_for_the_tests_that_need_it_and_no_other() {
    let world = world("test-plan-tool");
    let root = world.path();
    tool_fixture(root);
    // The invocation's environment already carries the tool's variable, as
    // a lane that built the tool itself would leave it: no test may run
    // that file, so every test executable but a consumer's has it removed.
    let plan = |arguments: &[&str]| {
        targo(root)
            .env("RUSTFLAGS", "-Zthreads=1")
            .env("TOOL_GADGET_BIN", "/bin/echo")
            .args(["--plan", "plan.toml", "--message-format=json"])
            .args(or_whole(arguments))
            .output()
            .unwrap()
    };
    let passed = |rows: &[Value]| {
        reasoned(rows, "test-execution")
            .iter()
            .filter(|(_, row)| row["state"] == "passed")
            .map(|(_, row)| row["package"].as_str().unwrap().to_owned())
            .collect::<BTreeSet<_>>()
    };
    let tool = |result: &Value, output: &Output| {
        let phases = result["phases"].as_array().unwrap();
        assert_eq!(phases.len(), 1, "{}", text(output));
        assert_eq!(phases[0]["kind"], "tool", "{}", text(output));
        assert_eq!(phases[0]["manifest"], "tools/gadget/Cargo.toml");
        assert_eq!(phases[0]["env"], "TOOL_GADGET_BIN");
        assert_eq!(phases[0]["tests"], Value::Null);
        phases[0]["state"].as_str().unwrap().to_owned()
    };
    let built_gadget = |rows: &[Value]| {
        rows.iter()
            .any(|row| row["reason"] == "compiler-artifact" && row["target"]["name"] == "gadget")
    };
    let copies = || {
        fs::read_dir(root.join("target.noindex/debug"))
            .unwrap()
            .filter_map(|entry| entry.unwrap().file_name().into_string().ok())
            .filter(|name| name.starts_with(".targo-plan-tool-"))
            .count()
    };

    // No request of the run tests a member that needs the tool: it is not
    // built, and the member that does not need it sees no variable.
    let output = plan(&["--no-fail-fast", "-p", "bystander"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert!(!built_gadget(&rows), "{}", text(&output));
    let result = plan_result(&rows, &output);
    assert_eq!(tool(&result, &output), "not-needed");
    assert_eq!(reasoned(&rows, "test-plan-phase").len(), 1);

    // A change to the tool alone is tested by the tests that run it: the
    // tool is built and its consumer's tests run, though no path of the
    // consumer changed; no member owns the path, and it is accounted for.
    write(root, "paths.txt", "tools/gadget/src/main.rs\n");
    let output = plan(&["--no-fail-fast", "--changed-paths", "paths.txt"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert!(built_gadget(&rows), "{}", text(&output));
    assert_eq!(passed(&rows), BTreeSet::from(["consumer".to_owned()]));
    assert_eq!(
        rows[0]["tools"],
        serde_json::json!([{
            "manifest": "tools/gadget/Cargo.toml",
            "members": ["consumer"],
            "paths": ["tools/gadget/src/main.rs"],
        }])
    );
    assert_eq!(rows[0]["unattributed"], serde_json::json!([]));
    assert_eq!(rows[0]["members"]["touched"], serde_json::json!([]));
    assert_eq!(
        rows[0]["members"]["selected"],
        serde_json::json!(["consumer"])
    );
    assert_eq!(
        rows[0]["requests"][0]["why"],
        "1 member selected (0 touched, 0 reached); tool `tools/gadget/Cargo.toml` changed, \
         which the tests of consumer run"
    );
    let result = plan_result(&rows, &output);
    assert_eq!(result["passed"], true);
    assert_eq!(tool(&result, &output), "built");
    // A path beside the tool's directory is nobody's.
    write(root, "paths.txt", "tools/gadgets/x\n");
    let output = plan(&["--no-fail-fast", "--changed-paths", "paths.txt"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));

    // The whole plan: the tool is built first, under its own manifest, and
    // the consumer's test runs the copy; the bystander still sees nothing.
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    let phase = reasoned(&rows, "test-plan-phase");
    assert_eq!(phase.len(), 2, "{}", text(&output));
    assert_eq!(phase[0].1["state"], "started");
    assert_eq!(phase[1].1["state"], "built");
    let artifact = rows
        .iter()
        .position(|row| {
            row["reason"] == "compiler-artifact"
                && row["target"]["name"] == "gadget"
                && row["package_id"].as_str().unwrap().contains("tools/gadget")
                && row["profile"]["test"] == false
        })
        .unwrap_or_else(|| panic!("{}", text(&output)));
    assert!(phase[0].0 < artifact && artifact < phase[1].0);
    let executions = reasoned(&rows, "test-execution");
    assert!(executions.iter().all(|(at, _)| *at > phase[1].0));
    assert_eq!(
        passed(&rows),
        BTreeSet::from(["bystander".to_owned(), "consumer".to_owned()])
    );
    let result = plan_result(&rows, &output);
    assert_eq!(result["passed"], true);
    assert_eq!(tool(&result, &output), "built");
    // The copies do not outlive the run.
    assert_eq!(copies(), 0);

    // `--no-run` builds the tool, since the run that follows would.
    gadget(root, "fn main() { println!(\"gadget, changed\"); }\n");
    let output = plan(&["--no-run"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert!(built_gadget(&rows), "{}", text(&output));
    assert_eq!(reasoned(&rows, "test-plan-phase")[1].1["state"], "built");
    assert_eq!(copies(), 0);
    // The consumer's test now runs what the tree builds, and fails on it.
    let output = plan(&["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    assert!(
        text(&output).contains("gadget, changed"),
        "{}",
        text(&output)
    );
    assert_eq!(copies(), 0);
    // So does a run told only that the tool changed: it never exits 0 over
    // a tool change that breaks the tests that run the tool.
    write(root, "paths.txt", "tools/gadget/src/main.rs\n");
    let output = plan(&["--no-fail-fast", "--changed-paths", "paths.txt"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    assert!(
        text(&output).contains("gadget, changed"),
        "{}",
        text(&output)
    );

    // A tool that does not build fails the run before any test: the tests
    // that need it are never skipped, and never run without it.
    gadget(root, "fn main() { not rust }\n");
    for arguments in [&["--no-fail-fast"][..], &["--no-run"]] {
        let output = plan(arguments);
        assert_eq!(output.status.code(), Some(101), "{}", text(&output));
        let rows = stream(&output);
        assert!(
            reasoned(&rows, "test-execution").is_empty(),
            "{}",
            text(&output)
        );
        // A tool that does not build is a red build, and the run has no
        // verdict of its own.
        closed_without_verdict(rows.last(), "failed", &output);
        assert_eq!(reasoned(&rows, "test-plan-result").len(), 1);
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(
                "tool `gadget` of `tools/gadget/Cargo.toml` failed to build; the tests of \
                 consumer that run it cannot run"
            ),
            "{}",
            text(&output)
        );
        // The phase the invocation ends in is closed, as failed.
        let phase = reasoned(&rows, "test-plan-phase");
        assert_eq!(phase.len(), 2, "{}", text(&output));
        assert_eq!(phase[0].1["state"], "started");
        assert_eq!(phase[1].1["state"], "failed");
        assert_eq!(phase[1].1["kind"], "tool");
        // Only the invocation's closing record follows it.
        assert_eq!(phase[1].0, rows.len() - 2, "{}", text(&output));
    }
    // The bystander's run needs no tool, so a broken one does not stop it.
    let output = plan(&["--no-fail-fast", "-p", "bystander"]);
    assert!(output.status.success(), "{}", text(&output));

    // A bin the manifest does not have is no tool.
    gadget(
        root,
        "fn main() { println!(\"gadget of its own workspace\"); }\n",
    );
    let text_of = fs::read_to_string(root.join("plan.toml")).unwrap();
    write(
        root,
        "plan.toml",
        &text_of.replace("bin = \"gadget\"", "bin = \"widget\""),
    );
    let output = plan(&["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("no bin target named `widget`"),
        "{}",
        text(&output)
    );

    // An instrument hosted on a member that needs the tool builds it too.
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [[instrument]]\nid = \"tool-check\"\npackage = \"consumer\"\nlib = true\n\
         args = [\"runs_the_tool\"]\n\
         [[tool]]\nmanifest = \"tools/gadget/Cargo.toml\"\nbin = \"gadget\"\n\
         env = \"TOOL_GADGET_BIN\"\nneeded-by = [\"consumer\"]\n",
    );
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let result = plan_result(&stream(&output), &output);
    assert_eq!(tool(&result, &output), "built");

    // A tool may be a member of the invocation's own workspace: it is still
    // built as `targo build` builds it, not as a unit of the tests' graph.
    write(
        root,
        "Cargo.toml",
        "[workspace]\nresolver='3'\nmembers=['consumer','bystander','kit']\n",
    );
    package(root, "kit", "", "");
    write(
        root,
        "kit/src/main.rs",
        "fn main() { println!(\"gadget of its own workspace\"); }\n",
    );
    let text_of = fs::read_to_string(root.join("plan.toml")).unwrap();
    write(
        root,
        "plan.toml",
        &text_of
            .replace("tools/gadget/Cargo.toml", "kit/Cargo.toml")
            .replace("bin = \"gadget\"", "bin = \"kit\""),
    );
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert!(
        rows.iter().any(|row| row["reason"] == "compiler-artifact"
            && row["target"]["name"] == "kit"
            && row["target"]["kind"] == serde_json::json!(["bin"])
            && row["profile"]["test"] == false),
        "{}",
        text(&output)
    );
    let result = plan_result(&rows, &output);
    assert_eq!(result["phases"][0]["manifest"], "kit/Cargo.toml");
    assert_eq!(result["phases"][0]["state"], "built");

    // A consumer that only a conditional instrument tests: a change to the
    // tool runs that instrument, since nothing else of the run would.
    let conditional = fs::read_to_string(root.join("plan.toml")).unwrap().replace(
        "args = [\"runs_the_tool\"]\n",
        "args = [\"runs_the_tool\"]\nwhen-changed = [\"fixtures/\"]\n",
    );
    write(root, "plan.toml", &conditional);
    write(root, "paths.txt", "kit/src/main.rs\n");
    let output = plan(&["--no-fail-fast", "--changed-paths", "paths.txt"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(passed(&rows), BTreeSet::from(["consumer".to_owned()]));
    assert_eq!(
        rows[0]["requests"][0]["why"],
        "its host `consumer` runs tool `kit/Cargo.toml`, which changed, and no default run \
         tests it"
    );
    write(root, "paths.txt", "bystander/src/lib.rs\n");
    let output = plan(&["--no-fail-fast", "--changed-paths", "paths.txt"]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(passed(&stream(&output)), BTreeSet::new());

    // A changed tool whose consumer no request of the plan tests is
    // refused: the run would be read as having tested the change.
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [[variant]]\nid = \"other\"\npackage = \"bystander\"\nlib = true\n\
         [[tool]]\nmanifest = \"kit/Cargo.toml\"\nbin = \"kit\"\n\
         env = \"TOOL_GADGET_BIN\"\nneeded-by = [\"consumer\"]\n",
    );
    write(root, "paths.txt", "kit/src/main.rs\n");
    let output = plan(&["--no-fail-fast", "--changed-paths", "paths.txt"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "`kit/src/main.rs` changed, in the directory of tool `kit/Cargo.toml`, and no \
             request of the plan tests a member that runs it (consumer)"
        ),
        "{}",
        text(&output)
    );

    // A workspace of its own is no tool's `needed-by` member: its tests see
    // no tool's variable either, whatever the invocation's environment has.
    write(
        root,
        "crates/aside/Cargo.toml",
        "[package]\nname='aside'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    );
    write(
        root,
        "crates/aside/src/lib.rs",
        "#[test] fn sees_no_tool() { assert!(std::env::var_os(\"TOOL_GADGET_BIN\").is_none()); }\n",
    );
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [default]\ntargets = \"tests\"\n\
         [[tool]]\nmanifest = \"tools/gadget/Cargo.toml\"\nbin = \"gadget\"\n\
         env = \"TOOL_GADGET_BIN\"\nneeded-by = [\"consumer\"]\n\
         [[workspace]]\nmanifest = \"crates/aside/Cargo.toml\"\n",
    );
    let output = plan(&["--no-fail-fast"]);
    assert!(output.status.success(), "{}", text(&output));
    let rows = stream(&output);
    assert_eq!(
        passed(&rows),
        BTreeSet::from([
            "aside".to_owned(),
            "bystander".to_owned(),
            "consumer".to_owned(),
            "kit".to_owned(),
        ])
    );
}

fn git(root: &Path, arguments: &[&str]) -> String {
    let output = Command::new("git")
        .current_dir(root)
        .env("HOME", root)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .args([
            "-c",
            "user.name=plan",
            "-c",
            "user.email=plan@example.invalid",
        ])
        .args([
            "-c",
            "commit.gpgsign=false",
            "-c",
            "init.defaultBranch=main",
        ])
        .args(arguments)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "git {arguments:?}: {}",
        text(&output)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_owned()
}

/// The selection workspace as a git repository with one crate that is its
/// own workspace, and three commits after the first: `outer` changes; a file
/// moves out of `host` into `docs/`; and, on a branch `side` cut before
/// both, `inner` changes.
fn ranged_workspace(root: &Path) {
    selection_workspace(root);
    write(
        root,
        "crates/own/Cargo.toml",
        "[package]\nname='own'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    );
    write(root, "crates/own/src/lib.rs", "#[test] fn own_side() {}\n");
    let plan = fs::read_to_string(root.join("plan.toml")).unwrap();
    // `base` is a key of `[select]`, the first table of the fixture's plan.
    let plan = plan.replace(
        "attribute-under = [\"crates/\"]\n",
        "attribute-under = [\"crates/\"]\nbase = \"main\"\n",
    );
    write(
        root,
        "plan.toml",
        &format!("{plan}[[workspace]]\nmanifest = \"crates/own/Cargo.toml\"\n"),
    );
    write(root, "crates/host/src/moved.rs", "// moves out\n");
    write(
        root,
        ".gitignore",
        "target.noindex\nhome\npaths.txt\nrefs.txt\n",
    );
    git(root, &["init", "-q"]);
    git(root, &["add", "-A"]);
    git(root, &["commit", "-q", "-m", "first"]);
    git(root, &["branch", "side"]);
    write(root, "crates/outer/src/extra.rs", "// outer changes\n");
    git(root, &["add", "-A"]);
    git(root, &["commit", "-q", "-m", "outer"]);
    fs::create_dir_all(root.join("docs")).unwrap();
    git(root, &["mv", "crates/host/src/moved.rs", "docs/moved.rs"]);
    git(root, &["commit", "-q", "-m", "a file leaves host"]);
    git(root, &["checkout", "-q", "side"]);
    write(
        root,
        "crates/outer/inner/src/extra.rs",
        "// inner changes\n",
    );
    git(root, &["add", "-A"]);
    git(root, &["commit", "-q", "-m", "inner"]);
    git(root, &["checkout", "-q", "main"]);
}

/// A `--no-run` selection under the plan file `plan`.
fn select_plan(root: &Path, plan: &str, arguments: &[&str]) -> Output {
    targo(root)
        .args(["--plan", plan, "--no-run", "--message-format=json"])
        .args(arguments)
        .output()
        .unwrap()
}

// Trust: the change is named as git names it, and Targo asks git itself.
// The script lane this replaces diffed the range and handed over nothing but
// the members; a caller of a plan hands over the range.
#[test]
fn a_git_range_selects_what_it_changed_and_a_run_says_what_it_judges() {
    let world = world("test-plan-range");
    let root = world.path();
    ranged_workspace(root);
    let select = |arguments: &[&str]| {
        targo(root)
            .args(["--plan", "plan.toml", "--no-run", "--message-format=json"])
            .args(arguments)
            .output()
            .unwrap()
    };
    let touched = |output: &Output| {
        let record = first_record(output);
        (
            names(&record["selection"]["changed_paths"])
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>(),
            names(&record["members"]["touched"]).join(","),
        )
    };

    // Two trees: the file that left `host` is listed under its old path as
    // well as its new one, so the member it left is tested. With rename
    // detection it would be listed under `docs/` alone.
    let moved = select(&["--changed-range", "HEAD~1..HEAD"]);
    assert!(moved.status.success(), "{}", text(&moved));
    assert_eq!(
        touched(&moved),
        (
            vec![
                "crates/host/src/moved.rs".to_owned(),
                "docs/moved.rs".to_owned()
            ],
            "host".to_owned()
        )
    );
    let record = first_record(&moved);
    assert_eq!(record["selection"]["changed_ranges"][0], "HEAD~1..HEAD");
    assert_eq!(record["selection"]["whole_plan"], false);

    // Several ranges are one change: the union of their paths.
    let both = select(&[
        "--changed-range",
        "HEAD~2..HEAD~1",
        "--changed-range",
        "HEAD~1..HEAD",
    ]);
    assert_eq!(touched(&both).1, "host,outer", "{}", text(&both));

    // `A..B` is tree against tree: `side` lacks what `main` added and has
    // its own change. `A...B` is what `side` changed since it left `main`.
    let trees = select(&["--changed-range", "main..side"]);
    assert_eq!(touched(&trees).1, "host,inner,outer", "{}", text(&trees));
    let since = select(&["--changed-range", "main...side"]);
    assert_eq!(
        touched(&since),
        (
            vec!["crates/outer/inner/src/extra.rs".to_owned()],
            "inner".to_owned()
        ),
        "{}",
        text(&since)
    );

    // A range and a list of paths are one change too.
    write(root, "paths.txt", "crates/outer/src/lib.rs\n");
    let mixed = select(&[
        "--changed-range",
        "main...side",
        "--changed-paths",
        "paths.txt",
    ]);
    assert_eq!(touched(&mixed).1, "inner,outer", "{}", text(&mixed));

    // A range that changes nothing selects nothing, and says so: exit 0.
    let nothing = select(&["--changed-range", "HEAD..HEAD"]);
    assert!(nothing.status.success(), "{}", text(&nothing));
    let record = first_record(&nothing);
    assert_eq!(record["selection"]["changed_paths"], serde_json::json!([]));
    assert!(
        record["requests"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["active"] == false)
    );

    // A range git cannot read is never an empty change.
    for (range, why) in [
        ("no-such-rev..HEAD", "git could not diff the range"),
        ("HEAD", "is not a range"),
        ("..HEAD", "leaves a side out"),
        ("a..--output=x", "is not a revision"),
    ] {
        let refused = select(&["--changed-range", range]);
        assert_eq!(refused.status.code(), Some(2), "{range}");
        refused_record(&refused);
        let stderr = String::from_utf8_lossy(&refused.stderr);
        assert!(stderr.contains(why), "{range}: {stderr}");
        assert!(!root.join("x").exists());
    }

    // The refs of a push, as git gives them to a pre-push hook: an update is
    // the remote tree against the pushed tree, a branch the remote lacks is
    // what it adds since the plan's `[select] base`, a deletion is nothing.
    let sha = |rev: &str| git(root, &["rev-parse", rev]);
    let zero = "0".repeat(40);
    write(
        root,
        "refs.txt",
        &format!(
            "refs/heads/main {} refs/heads/main {}\n\
             refs/heads/side {} refs/heads/side {zero}\n\
             (delete) {zero} refs/heads/gone {}\n",
            sha("main"),
            sha("main~1"),
            sha("side"),
            sha("main~2"),
        ),
    );
    let pushed = select(&["--changed-pushed-refs", "refs.txt"]);
    assert_eq!(touched(&pushed).1, "host,inner", "{}", text(&pushed));
    assert_eq!(
        names(&first_record(&pushed)["selection"]["changed_ranges"]),
        [
            format!("{}..{}", sha("main~1"), sha("main")),
            format!("main...{}", sha("side")),
        ]
    );
    write(
        root,
        "refs.txt",
        &format!("(delete) {zero} refs/heads/gone {}\n", sha("main")),
    );
    // Input that names no pushed tree (deletions only, or nothing at all:
    // a hook that lost its standard input) is judged as the standing change
    // since the plan's base, as the script lane judged it, and never as a
    // push that changes nothing, which would exit 0 over a change no test
    // ran for. On `side` the standing change is `inner`'s.
    git(root, &["checkout", "-q", "side"]);
    let deleted = select(&["--changed-pushed-refs", "refs.txt"]);
    write(root, "refs.txt", "");
    let empty = select(&["--changed-pushed-refs", "refs.txt"]);
    let lost = targo(root)
        .args(["--plan", "plan.toml", "--no-run", "--message-format=json"])
        .args(["--changed-pushed-refs", "-"])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    git(root, &["checkout", "-q", "main"]);
    for standing in [&deleted, &empty, &lost] {
        assert!(standing.status.success(), "{}", text(standing));
        assert_eq!(
            touched(standing),
            (
                vec!["crates/outer/inner/src/extra.rs".to_owned()],
                "inner".to_owned()
            ),
            "{}",
            text(standing)
        );
        assert_eq!(
            names(&first_record(standing)["selection"]["changed_ranges"]),
            ["main...HEAD"]
        );
    }
    // Where git cannot say what the standing change is (no repository, no
    // such base), the run is refused: exit 2, never a pass.
    write(
        root,
        "nobase.toml",
        &fs::read_to_string(root.join("plan.toml"))
            .unwrap()
            .replace("base = \"main\"", "base = \"no-such-base\""),
    );
    let unknown = targo(root)
        .args(["--plan", "nobase.toml", "--no-run", "--message-format=json"])
        .args(["--changed-pushed-refs", "-"])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    assert_eq!(unknown.status.code(), Some(2), "{}", text(&unknown));
    refused_record(&unknown);
    // A plan that does not parse says so, not that it lacks `base`.
    write(
        root,
        "broken.toml",
        "schema = \"targo.test-plan.v1\"\n[select\n",
    );
    let broken = select_plan(root, "broken.toml", &["--changed-pushed-refs", "refs.txt"]);
    assert_eq!(broken.status.code(), Some(2), "{}", text(&broken));
    let stderr = String::from_utf8_lossy(&broken.stderr);
    assert!(stderr.contains("invalid test plan"), "{stderr}");
    assert!(
        !stderr.contains("needs the plan's `[select] base`"),
        "{stderr}"
    );

    // An invocation says what it judges. Naming no change is refused rather
    // than read as the whole plan (or as nothing), and the whole plan is
    // asked for by name and beside no change.
    let unnamed = select(&[]);
    assert!(!unnamed.status.success());
    let stderr = String::from_utf8_lossy(&unnamed.stderr);
    assert!(
        stderr.contains("pass --whole-plan to run every request"),
        "{stderr}"
    );
    assert_eq!(unnamed.status.code(), Some(2));
    refused_record(&unnamed);
    let whole = select(&["--whole-plan"]);
    assert!(whole.status.success(), "{}", text(&whole));
    let record = first_record(&whole);
    assert_eq!(record["selection"]["whole_plan"], true);
    assert_eq!(
        names(&record["members"]["selected"]),
        ["host", "inner", "outer"]
    );
    for beside in [
        &["--whole-plan", "--changed-range", "HEAD~1..HEAD"][..],
        &["--whole-plan", "-p", "host"],
        &["--whole-plan", "--reached", "crates/host"],
        &["--whole-plan", "--changed-paths", "paths.txt"],
    ] {
        let refused = select(beside);
        assert!(!refused.status.success(), "{beside:?}");
        let stderr = String::from_utf8_lossy(&refused.stderr);
        assert!(
            stderr.contains("--whole-plan runs every request"),
            "{stderr}"
        );
    }
}

// Trust: what the script lane's real-git tests held of the diff and no native
// test did. A setting or a byte must not hide a changed path: a path git
// quotes (`core.quotePath`), a gitlink a submodule setting ignores
// (`diff.ignoreSubmodules`) and a file moved from one member into another
// each select the members they lie in. And one range git cannot diff refuses
// the whole push, whatever range beside it reads.
#[test]
fn a_git_range_lists_every_path_a_setting_or_a_byte_could_hide() {
    let world = world("test-plan-range-hidden");
    let root = world.path();
    ranged_workspace(root);
    // git's defaults, set so that the controls below cannot drift with them.
    git(root, &["config", "core.quotePath", "true"]);
    git(root, &["config", "diff.renames", "true"]);
    let touched = |arguments: &[&str]| {
        let output = select_plan(root, "plan.toml", arguments);
        assert!(output.status.success(), "{}", text(&output));
        names(&first_record(&output)["members"]["touched"]).join(",")
    };

    // A path git quotes: without `-z` it comes back as `"crates/host/...`,
    // which lies under no member's directory.
    write(root, "crates/host/src/\u{e9}.rs", "// accent\n");
    git(root, &["add", "-A"]);
    git(root, &["commit", "-q", "-m", "accent"]);
    assert!(git(root, &["diff", "--name-only", "HEAD~1..HEAD"]).starts_with('"'));
    assert_eq!(touched(&["--changed-range", "HEAD~1..HEAD"]), "host");

    // A gitlink in a member, under a setting that hides every submodule.
    let first = git(root, &["rev-list", "--max-parents=0", "HEAD"]);
    git(
        root,
        &[
            "update-index",
            "--add",
            "--cacheinfo",
            &format!("160000,{first},crates/outer/vendored"),
        ],
    );
    git(root, &["commit", "-q", "-m", "a gitlink in outer"]);
    git(root, &["config", "diff.ignoreSubmodules", "all"]);
    assert_eq!(git(root, &["diff", "--name-only", "HEAD~1..HEAD"]), "");
    assert_eq!(touched(&["--changed-range", "HEAD~1..HEAD"]), "outer");

    // A file moved from one member into another: the member it left and the
    // one it joined. With rename detection only the new path is listed.
    git(
        root,
        &["mv", "crates/host/src/\u{e9}.rs", "crates/outer/src/moved_in.rs"],
    );
    git(root, &["commit", "-q", "-m", "from host into outer"]);
    assert_eq!(
        git(root, &["-c", "core.quotePath=false", "diff", "--name-only", "HEAD~1..HEAD"]),
        "crates/outer/src/moved_in.rs"
    );
    assert_eq!(touched(&["--changed-range", "HEAD~1..HEAD"]), "host,outer");

    // A push whose second update names a remote tree this clone never
    // fetched: the readable update beside it does not make it a pass.
    let sha = |rev: &str| git(root, &["rev-parse", rev]);
    let good = format!(
        "refs/heads/main {} refs/heads/main {}\n",
        sha("HEAD"),
        sha("HEAD~1")
    );
    let bad = format!(
        "refs/heads/topic {} refs/heads/topic {}\n",
        sha("HEAD"),
        "1".repeat(40)
    );
    write(root, "refs.txt", &good);
    assert_eq!(touched(&["--changed-pushed-refs", "refs.txt"]), "host,outer");
    for refs in [format!("{good}{bad}"), format!("{bad}{good}")] {
        write(root, "refs.txt", &refs);
        let refused = select_plan(root, "plan.toml", &["--changed-pushed-refs", "refs.txt"]);
        assert_eq!(refused.status.code(), Some(2), "{refs}\n{}", text(&refused));
        refused_record(&refused);
        let stderr = String::from_utf8_lossy(&refused.stderr);
        assert!(stderr.contains("git could not diff the range"), "{stderr}");
    }
}

// Trust: a gate names the crates a change reaches by directory, and one of
// them may be its own workspace, which `-p` cannot name.
#[test]
fn a_reached_directory_names_a_member_or_an_own_workspace_and_no_other() {
    let world = world("test-plan-reached");
    let root = world.path();
    ranged_workspace(root);
    let select = |arguments: &[&str]| {
        targo(root)
            .args(["--plan", "plan.toml", "--no-run", "--message-format=json"])
            .args(arguments)
            .output()
            .unwrap()
    };
    let reached = select(&["--reached", "crates/host", "--reached", "crates/own/"]);
    assert!(reached.status.success(), "{}", text(&reached));
    let record = first_record(&reached);
    assert_eq!(names(&record["members"]["reached"]), ["host"]);
    assert_eq!(names(&record["members"]["selected"]), ["host"]);
    assert_eq!(names(&record["workspaces"]), ["crates/own/Cargo.toml"]);
    assert_eq!(
        names(&record["selection"]["reached"]),
        ["crates/host", "crates/own/"]
    );
    // The own workspace is built as a phase of the run, not skipped.
    let rows = stream(&reached);
    let phases = reasoned(&rows, "test-plan-phase");
    assert!(
        phases
            .iter()
            .any(|(_, row)| row["manifest"] == "crates/own/Cargo.toml" && row["state"] == "built"),
        "{}",
        text(&reached)
    );
    // A nested member is named by its own directory.
    let nested = select(&["--reached", "crates/outer/inner"]);
    assert_eq!(
        names(&first_record(&nested)["members"]["reached"]),
        ["inner"]
    );
    // A range and a reached directory add up.
    let both = select(&[
        "--changed-range",
        "HEAD~1..HEAD",
        "--reached",
        "crates/outer",
    ]);
    assert_eq!(
        names(&first_record(&both)["members"]["selected"]),
        ["host", "outer"]
    );

    // Any other directory is refused before anything is built: exit 0 would
    // be read as a pass for a crate no run tested.
    for (dir, why) in [
        ("crates/nope", "names no directory this plan tests"),
        ("crates", "names no directory this plan tests"),
        ("crates/host/src", "names no directory this plan tests"),
        ("crates/stray", "names no directory this plan tests"),
        (
            "crates/far",
            "`select.elsewhere` leaves `far` to `the far lane`",
        ),
        (
            "/crates/host",
            "is not a directory written from the workspace root",
        ),
        (
            "crates/../crates/host",
            "is not a directory written from the workspace root",
        ),
    ] {
        let refused = select(&["--reached", "crates/host", "--reached", dir]);
        assert!(!refused.status.success(), "{dir}");
        let stderr = String::from_utf8_lossy(&refused.stderr);
        assert!(stderr.contains(why), "{dir}: {stderr}");
        assert_eq!(refused.status.code(), Some(2), "{dir}");
        refused_record(&refused);
    }
}

// Trust: a gate reads one number, and Cargo's 101 for every failure made a
// red test, a run that judged nothing and (test_plan_clock.rs) a run stopped
// for time look alike. Each has its own status, and with JSON messages the
// last record of the invocation says the same.
#[test]
fn the_exit_status_and_the_closing_record_say_how_a_run_ended() {
    let world = world("test-plan-outcome");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['good', 'bad', 'thin', 'odd']\nresolver='3'\n",
    );
    package(root, "good", "", "#[test] fn holds() {}\n");
    package(root, "bad", "", "#[test] fn breaks() { panic!(\"red\") }\n");
    package(root, "thin", "", "pub fn nothing_tests_this() {}\n");
    // A test executable that exits 2, the status of a run that judged
    // nothing.
    package(root, "odd", "[[test]]\nname='odd'\nharness=false\n", "");
    write(
        root,
        "odd/tests/odd.rs",
        "fn main() { std::process::exit(2) }\n",
    );
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    write(root, "plan.toml", plan);
    write(root, "floor.toml", &format!("{plan}min-tests = 1\n"));
    write(root, "none.txt", "");
    let ended = |plan: &str, arguments: &[&str]| {
        let output = targo(root)
            .args(["--plan", plan, "--message-format=json"])
            .args(arguments)
            .output()
            .unwrap();
        let rows = stream(&output);
        let result = plan_result(&rows, &output);
        assert_eq!(
            result["exit_status"].as_i64().map(|status| status as i32),
            output.status.code(),
            "{}",
            text(&output)
        );
        (output, result)
    };

    // Every performed request passed: 0.
    let (output, result) = ended("plan.toml", &["-p", "good", "--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output));
    assert_eq!(result["outcome"], "passed");
    assert_eq!(result["passed"], true);
    let skipped = |output: &Output| {
        String::from_utf8_lossy(&output.stderr)
            .lines()
            .filter(|line| line.starts_with("SKIPPED: "))
            .count()
    };
    assert_eq!(skipped(&output), 0, "{}", text(&output));

    // The selection performs nothing: 0, and the record tells it from a pass.
    // So does the text, for a hook or a gate that reads the status and the
    // log: one line that starts `SKIPPED: `, as every lane here prints for a
    // run that judged nothing.
    let (output, result) = ended("plan.toml", &["--changed-paths", "none.txt"]);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output));
    assert_eq!(result["outcome"], "nothing-selected");
    assert_eq!(skipped(&output), 1, "{}", text(&output));

    // A test failed: red, Cargo's 101.
    let (output, result) = ended("plan.toml", &["-p", "bad", "--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    assert_eq!(result["outcome"], "failed");
    assert_eq!(result["passed"], false);
    assert!(!text(&output).contains("cannot judge"), "{}", text(&output));
    // A run that stops at the first failure has no verdict of its own, and is
    // closed all the same.
    let (output, result) = ended("plan.toml", &["-p", "bad"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    closed_without_verdict(Some(&result), "failed", &output);

    // A test executable's own exit status is never the run's: one that
    // exits 2 is a red test, not a run that judged nothing.
    let (output, result) = ended("plan.toml", &["-p", "odd"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    closed_without_verdict(Some(&result), "failed", &output);

    // No test failed and the plan's floor is not met: no verdict, 2.
    let (output, result) = ended("floor.toml", &["-p", "thin", "--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert_eq!(result["outcome"], "cannot-judge");
    assert_eq!(result["passed"], false);
    assert!(result.get("requests").is_some(), "{result}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("cannot judge (exit status 2)"),
        "{}",
        text(&output)
    );

    // Red wins where a run shows both.
    let (output, result) = ended("floor.toml", &["-p", "thin", "-p", "bad", "--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    assert_eq!(result["outcome"], "failed");

    // A refused invocation judged nothing: 2, with the one record.
    let (output, _) = ended("plan.toml", &["--no-fail-fast"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    refused_record(&output);
    // Without JSON messages the status alone says it, and nothing is on the
    // standard output.
    let output = targo(root)
        .args(["--plan", "plan.toml", "--no-fail-fast"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(output.stdout.is_empty(), "{}", text(&output));
}

/// A member `slow` whose one test starts a descendant, leaves its pid in
/// `slow/descendant.pid`, prints nothing and sleeps for minutes; and a
/// member `steady` whose three tests each take three seconds, so that its
/// harness prints a line every three seconds for nine.
fn clocked_workspace(root: &Path) {
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['slow', 'steady']\nresolver='3'\n",
    );
    package(
        root,
        "slow",
        "",
        "#[test] fn hangs() {\n\
             let child = std::process::Command::new(\"sleep\").arg(\"120\").spawn().unwrap();\n\
             std::fs::write(\n\
                 concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/descendant.pid\"),\n\
                 child.id().to_string(),\n\
             ).unwrap();\n\
             std::thread::sleep(std::time::Duration::from_secs(120));\n\
         }\n",
    );
    let nap = "std::thread::sleep(std::time::Duration::from_secs(3));";
    package(
        root,
        "steady",
        "",
        &format!(
            "#[test] fn a() {{ {nap} }}\n#[test] fn b() {{ {nap} }}\n#[test] fn c() {{ {nap} }}\n"
        ),
    );
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    write(root, "unbounded.toml", plan);
    write(
        root,
        "stall.toml",
        &format!("{plan}[run]\nstall-seconds = 6\n"),
    );
    write(
        root,
        "wall.toml",
        &format!("{plan}[run]\nwall-seconds = 3600\nwall-seconds-per-member = 900\n"),
    );
}

/// Whether the process `pid` exists.
fn alive(pid: &str) -> bool {
    Command::new("kill")
        .args(["-0", pid])
        .stderr(std::process::Stdio::null())
        .status()
        .unwrap()
        .success()
}

/// Waits for the descendant `slow`'s test started to be gone, and says
/// whether it is.
fn descendant_gone(root: &Path) -> bool {
    let pid = fs::read_to_string(root.join("slow/descendant.pid")).unwrap();
    for _ in 0..100 {
        if !alive(&pid) {
            return true;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    // Do not leave it behind a failed test.
    let _ = Command::new("kill").args(["-KILL", &pid]).status();
    false
}

// Trust: the script lane bounded its run and its silence (a ceiling for the
// run, 1800 s without progress) and killed the tree it had started. A plan
// states both bounds; Targo stops the run itself, with every test executable
// and its descendants, exits 3 and says what was running.
#[test]
fn a_run_out_of_time_is_stopped_with_its_descendants_and_says_what_was_running() {
    let world = world("test-plan-clock");
    let root = world.path();
    clocked_workspace(root);
    let ended = |arguments: &[&str]| {
        let _ = fs::remove_file(root.join("slow/descendant.pid"));
        let began = std::time::Instant::now();
        let output = targo(root)
            .args(["--message-format=json", "--no-fail-fast"])
            .args(arguments)
            .output()
            .unwrap();
        assert!(
            began.elapsed() < std::time::Duration::from_secs(90),
            "the run was not stopped: {}",
            text(&output)
        );
        let rows = stream(&output);
        let result = plan_result(&rows, &output);
        (output, result)
    };

    // A harness that prints a line every three seconds for nine is within a
    // six second bound on silence: each line is progress.
    let (output, result) = ended(&["--plan", "stall.toml", "-p", "steady"]);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output));
    assert_eq!(result["outcome"], "passed");

    // One that prints nothing is stopped at the bound, with what it started.
    let (output, result) = ended(&["--plan", "stall.toml", "-p", "slow"]);
    assert_eq!(output.status.code(), Some(3), "{}", text(&output));
    closed_without_verdict(Some(&result), "out-of-time", &output);
    let why = result["why"].as_str().unwrap();
    assert!(
        why.starts_with(
            "lib `slow` of `slow` printed nothing for 6 s, the bound on a test executable's \
             silence; running when stopped: lib `slow` of `slow` (running "
        ),
        "{why}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        stderr.contains("Targo stopped this test plan run"),
        "{stderr}"
    );
    // The harness Targo stopped is reported by its target, with the reason.
    let stopped = stderr
        .split("error: lib of `slow`: test failed, to rerun pass `--plan ")
        .nth(1)
        .unwrap_or_else(|| panic!("{stderr}"));
    assert!(
        stopped.contains("the test process was stopped by Targo's cancellation"),
        "{stderr}"
    );
    assert!(descendant_gone(root), "a descendant outlived the run");

    // The wall bound covers the whole invocation, and the configuration's
    // bound stands over the plan's: an hour in the file, seconds here.
    let built = targo(root)
        .args(["--plan", "wall.toml", "-p", "slow", "--no-run"])
        .output()
        .unwrap();
    assert!(built.status.success(), "{}", text(&built));
    let (output, result) = ended(&[
        "--plan",
        "wall.toml",
        "-p",
        "slow",
        "--config",
        // Wide enough that the prebuilt harness is running when it runs
        // out on a loaded host (10 s was not, at a load average of 41-62).
        "build.test-wall-seconds=30",
    ]);
    assert_eq!(output.status.code(), Some(3), "{}", text(&output));
    closed_without_verdict(Some(&result), "out-of-time", &output);
    let why = result["why"].as_str().unwrap();
    assert!(
        why.starts_with(
            "the run's wall bound of 30 s ran out; running when stopped: lib `slow` of `slow` \
             (running "
        ),
        "{why}"
    );
    assert!(descendant_gone(root), "a descendant outlived the run");

    // A bound of nothing is refused, in the file and in the configuration.
    write(
        root,
        "zero.toml",
        &fs::read_to_string(root.join("stall.toml"))
            .unwrap()
            .replace("stall-seconds = 6", "stall-seconds = 0"),
    );
    let (output, _) = ended(&["--plan", "zero.toml", "-p", "steady"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(
        text(&output).contains("`[run] stall-seconds` must be 1 or more"),
        "{}",
        text(&output)
    );
    let (output, _) = ended(&[
        "--plan",
        "stall.toml",
        "-p",
        "steady",
        "--config",
        "build.test-wall-seconds=0",
    ]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(
        text(&output).contains("build.test-wall-seconds must be 1 or more"),
        "{}",
        text(&output)
    );
}

// Trust: a signal to Targo stops the whole tree it started, as the script
// lane's handler did, and the run says it was interrupted: no verdict.
#[test]
fn a_signal_stops_every_harness_and_descendant_and_the_run_says_interrupted() {
    let world = world("test-plan-signal");
    let root = world.path();
    clocked_workspace(root);
    for (signal, number) in [("-TERM", 15), ("-INT", 2)] {
        let _ = fs::remove_file(root.join("slow/descendant.pid"));
        let child = targo(root)
            .args(["--message-format=json", "--no-fail-fast"])
            .args(["--plan", "unbounded.toml", "-p", "slow"])
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        // The harness is running once its test has left the pid.
        let began = std::time::Instant::now();
        while !root.join("slow/descendant.pid").exists() {
            assert!(
                began.elapsed() < std::time::Duration::from_secs(300),
                "the test never started"
            );
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        std::thread::sleep(std::time::Duration::from_millis(300));
        assert!(
            Command::new("kill")
                .args([signal, &child.id().to_string()])
                .status()
                .unwrap()
                .success()
        );
        let stopped = std::time::Instant::now();
        let output = child.wait_with_output().unwrap();
        assert!(
            stopped.elapsed() < std::time::Duration::from_secs(60),
            "{signal}: {}",
            text(&output)
        );
        assert_eq!(output.status.code(), Some(2), "{signal}: {}", text(&output));
        let rows = stream(&output);
        let result = plan_result(&rows, &output);
        closed_without_verdict(Some(&result), "interrupted", &output);
        let why = result["why"].as_str().unwrap();
        assert!(
            why.starts_with(&format!(
                "signal {number} stopped the run; running when stopped: lib `slow` of `slow` \
                 (running "
            )),
            "{why}"
        );
        assert!(
            descendant_gone(root),
            "{signal}: a descendant outlived the run"
        );
    }
}

// Trust: a job queue reads the plan's clock only while it drains, and a run
// spends time outside every queue. A run blocked on a build-directory lock
// another process holds took SIGINT, noted it, and waited (96 s in the
// review's run) until the other holder let go; a wall bound that ran out
// there ended nothing either. The clock's watcher ends such a run: the stop
// is recorded as a queue records it and, with no queue left to end the run,
// the invocation ends with the stop's status and closing record. And a run
// whose work finished after a stop (a `--unit-graph-parity` check, which
// starts no queue) is never a pass.
#[test]
fn a_stop_outside_every_job_queue_ends_the_run() {
    let world = world("test-plan-stop-outside-queues");
    let root = world.path();
    clocked_workspace(root);
    // Holds the lock on `path` until the returned sender is dropped, or for
    // 60 s at most: a run that waits for it instead of ending then fails the
    // time assertion below rather than hanging the test.
    let lock = |path: &Path| {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        let file = fs::File::create(path).unwrap();
        file.lock().unwrap();
        let (release, released) = std::sync::mpsc::channel::<()>();
        std::thread::spawn(move || {
            let _ = released.recv_timeout(std::time::Duration::from_secs(60));
            drop(file);
        });
        release
    };
    // Starts `command`, waits until it says it is blocked on a lock, and
    // returns it with the reader of its stderr.
    let blocked = |command: &mut Command| {
        let mut child = command
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let stderr = child.stderr.take().unwrap();
        let (blocking, said) = std::sync::mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut seen = Vec::new();
            for line in std::io::BufRead::split(std::io::BufReader::new(stderr), b'\n') {
                let line = line.unwrap();
                if String::from_utf8_lossy(&line).contains("Blocking") {
                    let _ = blocking.send(());
                }
                seen.extend_from_slice(&line);
                seen.push(b'\n');
            }
            seen
        });
        if let Err(error) = said.recv_timeout(std::time::Duration::from_secs(300)) {
            let _ = child.kill();
            let status = child.wait().unwrap();
            let seen = reader.join().unwrap();
            panic!(
                "the run never said it was blocked on a lock ({error:?}; {status}): {}",
                String::from_utf8_lossy(&seen)
            );
        }
        (child, reader)
    };
    let ended = |child: std::process::Child,
                 reader: std::thread::JoinHandle<Vec<u8>>,
                 began: std::time::Instant| {
        let mut output = child.wait_with_output().unwrap();
        output.stderr = reader.join().unwrap();
        assert!(
            began.elapsed() < std::time::Duration::from_secs(30),
            "the run waited for the lock instead of ending: {}",
            text(&output)
        );
        output
    };

    // A signal while the run waits for the build directory.
    let held = lock(&root.join("target.noindex/debug/.cargo-build-lock"));
    let (child, reader) = blocked(
        targo(root)
            .args(["--message-format=json", "--no-fail-fast"])
            .args(["--plan", "unbounded.toml", "-p", "steady"]),
    );
    assert!(
        Command::new("kill")
            .args(["-INT", &child.id().to_string()])
            .status()
            .unwrap()
            .success()
    );
    let output = ended(child, reader, std::time::Instant::now());
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    let result = plan_result(&stream(&output), &output);
    closed_without_verdict(Some(&result), "interrupted", &output);
    let why = result["why"].as_str().unwrap();
    assert!(
        why.starts_with("signal 2 stopped the run; no test executable was running"),
        "{why}"
    );

    // The wall bound runs out while it waits. The bound is counted from the
    // run's start, so it must outlast the way to the lock on a loaded host
    // (3 s did not, at a load average of 43): a run that ends before it
    // blocks proves nothing here, and `blocked` names it.
    let (child, reader) = blocked(
        targo(root)
            .args(["--message-format=json", "--no-fail-fast"])
            .args(["--plan", "unbounded.toml", "-p", "steady"])
            .args(["--config", "build.test-wall-seconds=20"]),
    );
    let output = ended(child, reader, std::time::Instant::now());
    assert_eq!(output.status.code(), Some(3), "{}", text(&output));
    let result = plan_result(&stream(&output), &output);
    closed_without_verdict(Some(&result), "out-of-time", &output);
    assert!(
        result["why"]
            .as_str()
            .unwrap()
            .starts_with("the run's wall bound of 20 s ran out"),
        "{result}"
    );
    drop(held);

    // A parity check stopped while it waits for the package cache, which
    // then comes free: the check finishes, and the run is still the
    // signal's, never exit 0.
    let held = lock(&root.join("home/.package-cache"));
    let (child, reader) = blocked(targo(root).args([
        "--plan",
        "unbounded.toml",
        "--whole-plan",
        "--unit-graph-parity",
    ]));
    assert!(
        Command::new("kill")
            .args(["-TERM", &child.id().to_string()])
            .status()
            .unwrap()
            .success()
    );
    let began = std::time::Instant::now();
    // The watcher has seen the signal well before its grace runs out.
    std::thread::sleep(std::time::Duration::from_millis(400));
    drop(held);
    let output = ended(child, reader, began);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Targo stopped this test plan run: signal 15 stopped the run"),
        "{}",
        text(&output)
    );
}

// Trust: two cases the script lane's own tests held and no native test did.
// A run that waits at its barrier ends on a signal, having started no test
// executable (the push hook interrupts the lane it holds when the destination
// moves), and its record says what was running even when the signal came
// before the queue first looked. And a run that starts with SIGINT ignored, as
// bash starts a `... &` job without job control, still ends on a signal with
// nothing left running. A plan run takes SIGINT whatever disposition it
// inherited, so a caller that stops a lane it started in the background
// reaches it; the script lane kept an inherited ignore, and its callers had to
// hand it the default.
#[test]
fn a_signal_ends_a_run_at_its_barrier_and_a_run_that_inherited_an_ignored_interrupt() {
    let world = world("test-plan-signal-barrier");
    let root = world.path();
    clocked_workspace(root);
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n[run]\nrun-after-seconds = 90\n";
    write(root, "held.toml", plan);
    let built = targo(root)
        .args(["--plan", "held.toml", "-p", "slow", "--no-run"])
        .output()
        .unwrap();
    assert!(built.status.success(), "{}", text(&built));
    let signal = |name: &str, pid: u32| {
        assert!(
            Command::new("kill")
                .args([name, &pid.to_string()])
                .status()
                .unwrap()
                .success()
        );
    };
    let interrupted = |output: Output, began: std::time::Instant, number: u32| {
        assert!(
            began.elapsed() < std::time::Duration::from_secs(60),
            "{}",
            text(&output)
        );
        assert_eq!(output.status.code(), Some(2), "{}", text(&output));
        let result = plan_result(&stream(&output), &output);
        closed_without_verdict(Some(&result), "interrupted", &output);
        let why = result["why"].as_str().unwrap().to_owned();
        assert!(
            why.starts_with(&format!("signal {number} stopped the run")),
            "{why}"
        );
        why
    };

    // At the barrier: everything is built, the file never comes. The signal
    // comes as soon as the run says it holds its tests, which it says when
    // the plan is selected: before the queue has looked at anything.
    let pid_file = root.join("slow/descendant.pid");
    let _ = fs::remove_file(&pid_file);
    let mut child = targo(root)
        .args(["--message-format=json", "--no-fail-fast"])
        .args(["--plan", "held.toml", "-p", "slow", "--run-after", "barrier"])
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let stderr = child.stderr.take().unwrap();
    let (holding, held) = std::sync::mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut seen = Vec::new();
        for line in std::io::BufRead::split(std::io::BufReader::new(stderr), b'\n') {
            let line = line.unwrap();
            if String::from_utf8_lossy(&line).contains("Holding") {
                let _ = holding.send(());
            }
            seen.extend_from_slice(&line);
            seen.push(b'\n');
        }
        seen
    });
    held.recv_timeout(std::time::Duration::from_secs(300))
        .expect("the run never said that it holds its tests");
    signal("-TERM", child.id());
    let began = std::time::Instant::now();
    let mut output = child.wait_with_output().unwrap();
    output.stderr = reader.join().unwrap();
    let why = interrupted(output, began, 15);
    assert!(
        why.ends_with("no test executable was running (the run's tests were held at its barrier)"),
        "{why}"
    );
    assert!(
        !pid_file.exists(),
        "a test executable ran at a barrier nobody released"
    );

    // Started with SIGINT ignored: the shell sets the disposition and execs
    // Targo, which inherits it.
    for (name, number) in [("-INT", 2), ("-TERM", 15)] {
        let _ = fs::remove_file(&pid_file);
        let mut ignoring = Command::new("sh");
        ignoring
            .args(["-c", "trap '' INT; exec \"$0\" \"$@\""])
            .arg(env!("CARGO_BIN_EXE_targo"))
            .current_dir(root)
            .env_clear()
            .env("HOME", root)
            .env("CARGO_HOME", root.join("home"))
            .env("CARGO_TARGET_DIR", root.join("target.noindex"))
            .env("RUSTC", fixture_rustc())
            .env("PATH", std::env::var_os("PATH").unwrap())
            .args(["--unverified", "test", "--offline"])
            .args(["--message-format=json", "--no-fail-fast"])
            .args(["--plan", "unbounded.toml", "-p", "slow"])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        let child = ignoring.spawn().unwrap();
        let began = std::time::Instant::now();
        while !pid_file.exists() {
            assert!(
                began.elapsed() < std::time::Duration::from_secs(300),
                "the test never started"
            );
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        std::thread::sleep(std::time::Duration::from_millis(300));
        signal(name, child.id());
        let began = std::time::Instant::now();
        let why = interrupted(child.wait_with_output().unwrap(), began, number);
        assert!(why.contains("running when stopped: lib `slow`"), "{why}");
        assert!(
            descendant_gone(root),
            "{name}: a descendant outlived the run"
        );
    }
}

/// A member `hang` whose build script leaves its pid and a descendant's,
/// then sleeps far past any bound of these tests; and a tool of its own
/// workspace whose build script does the same, needed by `hang`.
fn hung_build_workspace(root: &Path) {
    let build = |name: &str| {
        format!(
            "fn main() {{\n\
                 let out = concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/\");\n\
                 let child = std::process::Command::new(\"sleep\").arg(\"600\").spawn().unwrap();\n\
                 std::fs::write(format!(\"{{out}}descendant.pid\"), child.id().to_string()).unwrap();\n\
                 std::fs::write(format!(\"{{out}}{name}.pid.part\"), std::process::id().to_string()).unwrap();\n\
                 std::fs::rename(format!(\"{{out}}{name}.pid.part\"), format!(\"{{out}}{name}.pid\")).unwrap();\n\
                 std::thread::sleep(std::time::Duration::from_secs(600));\n\
             }}\n"
        )
    };
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['hang', 'quick']\nresolver='3'\n",
    );
    package(root, "hang", "build='build.rs'\n", "#[test] fn t() {}\n");
    write(root, "hang/build.rs", &build("build"));
    package(root, "quick", "", "#[test] fn t() {}\n");
    write(
        root,
        "tools/gadget/Cargo.toml",
        "[package]\nname='gadget'\nversion='0.0.0'\nedition='2024'\nbuild='build.rs'\n[workspace]\n",
    );
    write(root, "tools/gadget/src/main.rs", "fn main() {}\n");
    write(root, "tools/gadget/build.rs", &build("build"));
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    write(root, "plan.toml", plan);
    write(
        root,
        "tool.toml",
        &format!(
            "{plan}[[tool]]\nmanifest = \"tools/gadget/Cargo.toml\"\nbin = \"gadget\"\n\
             env = \"TOOL_GADGET_BIN\"\nneeded-by = [\"quick\"]\n"
        ),
    );
}

/// Waits until the process whose pid `file` holds is gone, and says whether
/// it is; kills it otherwise, so that a failed test leaves nothing behind.
fn gone(file: &Path) -> bool {
    let pid = fs::read_to_string(file).unwrap();
    for _ in 0..100 {
        if !alive(&pid) {
            return true;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    let _ = Command::new("kill").args(["-KILL", &pid]).status();
    false
}

/// Starts a plan run of the hung-build fixture and waits until the build
/// script under `dir` runs.
fn start_hung_build(root: &Path, dir: &str, arguments: &[&str]) -> std::process::Child {
    for file in ["build.pid", "descendant.pid"] {
        let _ = fs::remove_file(root.join(dir).join(file));
    }
    let mut child = targo(root)
        .args(["--message-format=json", "--no-fail-fast"])
        .args(arguments)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let began = std::time::Instant::now();
    while !root.join(dir).join("build.pid").exists() {
        if child.try_wait().unwrap().is_some() {
            let output = child.wait_with_output().unwrap();
            panic!(
                "the run ended before its build script started: {}",
                text(&output)
            );
        }
        assert!(
            began.elapsed() < std::time::Duration::from_secs(300),
            "the build script never started"
        );
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
    child
}

// Trust: the script lane's ceiling bounded a build that never ends, and
// either bound running out killed everything the lane had started. A plan's
// wall bound does the same: a build script (as a proc macro or a compiler)
// that never ends is killed with its descendants, in the plan's own build
// and in a `[[tool]]`'s, and the run exits 3 at the bound, not when the
// build ends by itself. A build is exempt from the stall bound (it bounds a
// running test executable's silence): the build script prints nothing for
// far longer than the 5 s stall bound, and the run still ends at the wall.
#[test]
fn a_build_that_never_ends_is_killed_at_the_wall_bound_with_its_descendants() {
    let world = world("test-plan-build-bound");
    let root = world.path();
    hung_build_workspace(root);
    for (plan, package, dir) in [
        ("plan.toml", "hang", "hang"),
        ("tool.toml", "quick", "tools/gadget"),
    ] {
        let began = std::time::Instant::now();
        let child = start_hung_build(
            root,
            dir,
            &[
                "--plan",
                plan,
                "-p",
                package,
                "--config",
                "build.test-wall-seconds=60",
                "--config",
                "build.test-stall-seconds=5",
            ],
        );
        let output = child.wait_with_output().unwrap();
        // The build script sleeps 600 s: a run that waited for it is not
        // stopped. (The bound is 60 s, which the build script's own
        // compilation fits in on a host loaded to a load average of 70; 25 s
        // did not.)
        assert!(
            began.elapsed() < std::time::Duration::from_secs(240),
            "{plan}: the run waited for its build: {}",
            text(&output)
        );
        assert_eq!(output.status.code(), Some(3), "{plan}: {}", text(&output));
        let rows = stream(&output);
        let result = plan_result(&rows, &output);
        closed_without_verdict(Some(&result), "out-of-time", &output);
        assert_eq!(
            result["why"],
            "the run's wall bound of 60 s ran out; no test executable was running (the build was)",
            "{plan}"
        );
        assert!(
            gone(&root.join(dir).join("build.pid")),
            "{plan}: the build script outlived the run"
        );
        assert!(
            gone(&root.join(dir).join("descendant.pid")),
            "{plan}: a descendant outlived the run"
        );
    }
}

// Trust: a signal to Targo's own pid stops the tree it started while that
// tree is a build, as the script lane's handler signalled every group it had
// started: the build script and its descendant are gone, at once and not
// when the build would have ended, and the run says it was interrupted, in
// the plan's own build and in a `[[tool]]`'s.
#[test]
fn a_signal_during_a_build_kills_it_and_the_run_says_interrupted() {
    let world = world("test-plan-build-signal");
    let root = world.path();
    hung_build_workspace(root);
    for (plan, package, dir, signal, number) in [
        ("plan.toml", "hang", "hang", "-TERM", 15),
        ("tool.toml", "quick", "tools/gadget", "-TERM", 15),
        ("tool.toml", "quick", "tools/gadget", "-HUP", 1),
    ] {
        let child = start_hung_build(root, dir, &["--plan", plan, "-p", package]);
        std::thread::sleep(std::time::Duration::from_millis(300));
        assert!(
            Command::new("kill")
                .args([signal, &child.id().to_string()])
                .status()
                .unwrap()
                .success()
        );
        let signalled = std::time::Instant::now();
        let output = child.wait_with_output().unwrap();
        assert!(
            signalled.elapsed() < std::time::Duration::from_secs(30),
            "{plan} {signal}: the run waited for its build: {}",
            text(&output)
        );
        assert_eq!(
            output.status.code(),
            Some(2),
            "{plan} {signal}: {}",
            text(&output)
        );
        let rows = stream(&output);
        let result = plan_result(&rows, &output);
        closed_without_verdict(Some(&result), "interrupted", &output);
        assert_eq!(
            result["why"],
            format!(
                "signal {number} stopped the run; no test executable was running (the build was)"
            ),
            "{plan} {signal}"
        );
        assert!(
            gone(&root.join(dir).join("build.pid")),
            "{plan} {signal}: the build script outlived the run"
        );
        assert!(
            gone(&root.join(dir).join("descendant.pid")),
            "{plan} {signal}: a descendant outlived the run"
        );
    }
}

// Trust: the push hook overlaps this lane's build with the lanes before it,
// which rebuild the compiler some of these tests execute, and holds every
// test binary at a barrier file until they have ended (the script lane's
// TRUST_CRATES_TESTS_RUN_AFTER). A plan run is held the same way: it builds,
// starts no test executable until the file says `run`, does not charge the
// wait to its wall bound, and stops without a verdict when the file says
// anything else, when its writer is gone, or when the wait outlasts the
// plan's own bound on it.
#[test]
fn a_run_held_at_a_barrier_builds_and_starts_no_test_until_it_says_run() {
    let world = world("test-plan-barrier");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['held']\nresolver='3'\n",
    );
    package(
        root,
        "held",
        "",
        "#[test] fn ran() {\n\
             std::fs::write(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/ran\"), \"\").unwrap();\n\
         }\n",
    );
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    write(
        root,
        "plan.toml",
        &format!("{plan}[run]\nrun-after-seconds = 600\n"),
    );
    write(
        root,
        "brief.toml",
        &format!("{plan}[run]\nrun-after-seconds = 3\n"),
    );
    write(root, "unbounded.toml", plan);
    let ran = root.join("held/ran");
    let barrier = root.join("barrier");
    let start = |plan: &str, arguments: &[&str]| {
        let _ = fs::remove_file(&ran);
        let _ = fs::remove_file(&barrier);
        targo(root)
            .args(["--message-format=json", "--no-fail-fast"])
            .args(["--plan", plan, "-p", "held", "--run-after", "barrier"])
            .args(arguments)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap()
    };
    let release = |text: &str| {
        // Whole, by rename: a half-written barrier is never read.
        fs::write(root.join("barrier.part"), text).unwrap();
        fs::rename(root.join("barrier.part"), &barrier).unwrap();
    };
    let built = targo(root)
        .args(["--plan", "plan.toml", "-p", "held", "--no-run"])
        .output()
        .unwrap();
    assert!(built.status.success(), "{}", text(&built));

    // Held for longer than the wall bound: the run is neither out of time
    // nor running a test. Released, it runs them and passes.
    // The bound is wide enough for the run's own start before the barrier
    // (charged) on a loaded host; the hold outlasts it, which is the claim.
    let mut child = start("plan.toml", &["--config", "build.test-wall-seconds=20"]);
    std::thread::sleep(std::time::Duration::from_secs(30));
    if child.try_wait().unwrap().is_some() {
        let output = child.wait_with_output().unwrap();
        panic!("the run did not wait at its barrier: {}", text(&output));
    }
    assert!(
        !ran.exists(),
        "a test executable ran before the barrier said `run`"
    );
    release("run\n");
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", text(&output));
    assert_eq!(plan_result(&stream(&output), &output)["outcome"], "passed");
    assert!(ran.exists(), "{}", text(&output));
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        stderr.contains("Holding every test executable until"),
        "{stderr}"
    );
    assert!(
        stderr.contains("Released the run's test executables"),
        "{stderr}"
    );

    // Whatever ends the wait otherwise ends the run with no verdict and no
    // test executable started.
    let stopped = |child: std::process::Child, status: i32, outcome: &str, why: &str| {
        let began = std::time::Instant::now();
        let output = child.wait_with_output().unwrap();
        assert!(
            began.elapsed() < std::time::Duration::from_secs(60),
            "{why}: {}",
            text(&output)
        );
        assert_eq!(
            output.status.code(),
            Some(status),
            "{why}: {}",
            text(&output)
        );
        let result = plan_result(&stream(&output), &output);
        closed_without_verdict(Some(&result), outcome, &output);
        let said = result["why"].as_str().unwrap();
        assert!(said.contains(why), "{said}");
        assert!(said.ends_with("no test executable was started"), "{said}");
        assert!(!ran.exists(), "{why}: a test executable ran");
    };
    // The caller's stop.
    let child = start("plan.toml", &[]);
    std::thread::sleep(std::time::Duration::from_secs(2));
    release("stop\n");
    stopped(child, 2, "interrupted", "says `stop`, not `run`");
    // A writer that is gone.
    let mut writer = Command::new("true").spawn().unwrap();
    writer.wait().unwrap();
    let child = start(
        "plan.toml",
        &["--run-after-owner", &writer.id().to_string()],
    );
    stopped(child, 2, "interrupted", "is gone and never did");
    // A wait past the plan's bound on it.
    let child = start("brief.toml", &[]);
    stopped(
        child,
        3,
        "out-of-time",
        "did not appear in the 3 s the run waited for it",
    );

    // A plan that does not bound the wait is refused, and so is an owner
    // without a barrier.
    let unbounded = start("unbounded.toml", &[]).wait_with_output().unwrap();
    assert_eq!(unbounded.status.code(), Some(2), "{}", text(&unbounded));
    assert!(
        text(&unbounded).contains("--run-after needs the plan's `[run] run-after-seconds`"),
        "{}",
        text(&unbounded)
    );
    assert!(!ran.exists());
}

// Trust: the script lane sized its pool by memory (16 GiB a binary against
// what the host had available, less a reserve) and started its biggest
// binary first. A plan states both: what a harness is counted for, and how
// long one is expected to run. The queue admits by credits and by memory,
// and starts the longest expected harness first.
#[test]
fn tests_are_admitted_by_memory_and_the_longest_expected_harness_starts_first() {
    let world = world("test-plan-memory");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['a','b','c']\nresolver='3'\n",
    );
    let slow = "#[test] fn slow() { std::thread::sleep(std::time::Duration::from_millis(1500)) }\n";
    for member in ["a", "b", "c"] {
        package(root, member, "", slow);
    }
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    write(root, "plain.toml", plan);
    write(
        root,
        "plan.toml",
        &format!(
            "{plan}[run]\nharness-memory-mib = 100\n[harness.b.lib]\nmemory-mib = 10\n\
             [harness.c.lib]\nseconds = 600\n"
        ),
    );
    // Every executable is built first, so that all three are ready at once
    // and the queue's order is the policy's, not the compiler's.
    let built = targo(root)
        .args(["--plan", "plan.toml", "--whole-plan", "--no-run"])
        .output()
        .unwrap();
    assert!(built.status.success(), "{}", text(&built));
    let ran_with = |plan: &str, budget: Option<&str>, jobs: &'static str| {
        let mut arguments = vec![
            "--plan",
            plan,
            "--whole-plan",
            "--no-fail-fast",
            "-j4",
            "--config",
            jobs,
        ];
        if let Some(budget) = budget {
            arguments.extend(["--config", budget]);
        }
        let run = run(root, &arguments);
        assert!(run.output.status.success(), "{}", text(&run.output));
        run
    };
    let ran = |plan: &str, budget: Option<&str>| ran_with(plan, budget, "build.test-jobs=4");
    // Where each member's harness began and ended in the record stream, and
    // what its records say it was counted for and expected to take.
    let span = |run: &Run, package: &str| {
        let row = run
            .records
            .iter()
            .find(|row| row["package"] == package)
            .unwrap_or_else(|| panic!("{package}: {}", text(&run.output)));
        let index = row["index"].as_u64().unwrap();
        (
            run.at(index, "running").unwrap(),
            run.at(index, "passed").unwrap(),
            row["memory_mib"].as_u64().unwrap(),
            row["expected_seconds"].as_u64().unwrap(),
        )
    };
    let beside = |left: (usize, usize, u64, u64), right: (usize, usize, u64, u64)| {
        left.0 < right.1 && right.0 < left.1
    };

    // A budget of 150 MiB: `a` and `c` are counted for 100 each and never
    // run together, though three credits are free; `b`, counted for 10,
    // runs beside either.
    let tight = ran("plan.toml", Some("build.test-memory-mib=150"));
    let (a, b, c) = (span(&tight, "a"), span(&tight, "b"), span(&tight, "c"));
    assert_eq!((a.2, b.2, c.2), (100, 10, 100), "{}", text(&tight.output));
    assert_eq!((a.3, b.3, c.3), (0, 0, 600), "{}", text(&tight.output));
    assert!(!beside(a, c), "{}", text(&tight.output));
    assert!(beside(b, a) || beside(b, c), "{}", text(&tight.output));
    assert!(
        String::from_utf8_lossy(&tight.output.stderr)
            .contains("tests within 150 MiB of memory (build.test-memory-mib)"),
        "{}",
        text(&tight.output)
    );

    // With room for all three they run together.
    let roomy = ran("plan.toml", Some("build.test-memory-mib=1000"));
    let (a, b, c) = (span(&roomy, "a"), span(&roomy, "b"), span(&roomy, "c"));
    assert!(beside(a, c) && beside(b, c), "{}", text(&roomy.output));

    // The harness expected to run longest starts first among those ready.
    // With one credit, whichever harness is ready first runs alone while
    // the others become ready; of those, `c` is next, though it is last in
    // inventory order. So `c` is the first or the second to start, and
    // without its expectation the last unless it was the first one ready.
    let rank = |run: &Run| {
        let c = span(run, "c").0;
        usize::from(span(run, "a").0 < c) + usize::from(span(run, "b").0 < c)
    };
    let one = "build.test-jobs=1";
    let ordered = ran_with("plan.toml", Some("build.test-memory-mib=1000"), one);
    assert!(rank(&ordered) <= 1, "{}", text(&ordered.output));
    let unordered = ran_with("plain.toml", None, one);
    assert_ne!(rank(&unordered), 1, "{}", text(&unordered.output));

    // Without a configured budget Targo measures the host itself, and says
    // what it found.
    let measured = ran("plan.toml", None);
    let stderr = String::from_utf8_lossy(&measured.output.stderr).into_owned();
    assert!(
        stderr.contains("MiB available now less a reserve of "),
        "{stderr}"
    );

    // A plan that states neither counts nothing.
    let plain = ran("plain.toml", Some("build.test-memory-mib=150"));
    let (a, b, c) = (span(&plain, "a"), span(&plain, "b"), span(&plain, "c"));
    assert_eq!((a.2, b.2, c.2), (0, 0, 0), "{}", text(&plain.output));
    assert!(beside(a, c) && beside(a, b), "{}", text(&plain.output));
    assert!(
        !String::from_utf8_lossy(&plain.output.stderr).contains("of memory"),
        "{}",
        text(&plain.output)
    );

    // A count or an expectation of nothing is refused.
    write(
        root,
        "zero.toml",
        &format!("{plan}[harness.a.lib]\nmemory-mib = 0\n"),
    );
    let zero = run(
        root,
        &["--plan", "zero.toml", "--whole-plan", "--no-fail-fast"],
    );
    assert_eq!(zero.output.status.code(), Some(2), "{}", text(&zero.output));
    assert!(
        text(&zero.output).contains("harness.a.lib: `memory-mib` and `seconds` must be 1 or more"),
        "{}",
        text(&zero.output)
    );
}

// Trust: the script lane's pool was host knobs a caller had to remember
// (TRUST_CRATES_TESTS_JOBS, RUST_TEST_THREADS). A plan states its lane's
// pool, the configuration stands over it, and a build-slot job's admitted
// share bounds both. A harness gets as many libtest threads as credits,
// whatever RUST_TEST_THREADS the caller exported.
#[test]
fn a_plan_states_its_pool_and_the_configuration_and_the_admitted_share_bound_it() {
    let world = world("test-plan-pool");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['one','two']\nresolver='3'\n",
    );
    // Each test leaves the thread count libtest was given.
    let lib = "#[test] fn threads() {\n\
                   std::fs::write(\n\
                       concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/threads\"),\n\
                       std::env::var(\"RUST_TEST_THREADS\").unwrap_or_default(),\n\
                   ).unwrap();\n\
                   std::thread::sleep(std::time::Duration::from_millis(800));\n\
               }\n";
    package(root, "one", "", lib);
    package(root, "two", "", lib);
    let plan = "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
                [default]\ntargets = \"tests\"\n";
    write(
        root,
        "plan.toml",
        &format!("{plan}[run]\ntest-jobs = 4\ntest-weight = 2\n"),
    );
    write(
        root,
        "explicit.toml",
        &format!("{plan}[run]\ntest-jobs = 4\n[harness.one.lib]\nweight = 2\n"),
    );
    // What each harness held and was given, and whether the two ran beside
    // each other.
    let pool = |output: &Output| {
        let rows = stream(output);
        let weights = ["one", "two"].map(|package| {
            let row = rows
                .iter()
                .find(|row| row["reason"] == "test-execution" && row["package"] == package)
                .unwrap_or_else(|| panic!("{package}: {}", text(output)));
            row["weight"].as_u64().unwrap()
        });
        let threads = ["one", "two"]
            .map(|package| fs::read_to_string(root.join(package).join("threads")).unwrap());
        let position = |package: &str, state: &str| {
            rows.iter()
                .position(|row| {
                    row["reason"] == "test-execution"
                        && row["package"] == package
                        && row["state"] == state
                })
                .unwrap()
        };
        let together = position("one", "running") < position("two", "passed")
            && position("two", "running") < position("one", "passed");
        (weights, threads, together)
    };
    let planned = |plan: &str, environment: &[(&str, &str)], arguments: &[&str]| {
        targo(root)
            .envs(environment.iter().copied())
            // A caller's own libtest wish is not the lane's.
            .env("RUST_TEST_THREADS", "7")
            .args(["--plan", plan, "--whole-plan", "--no-fail-fast"])
            .args(["--message-format=json"])
            .args(arguments)
            .output()
            .unwrap()
    };
    let built = planned("plan.toml", &[], &["--no-run"]);
    assert!(built.status.success(), "{}", text(&built));
    let two = || ["2".to_owned(), "2".to_owned()];
    let one = || ["1".to_owned(), "1".to_owned()];

    // No flag: four credits, two a harness, so both run together with two
    // libtest threads each.
    let output = planned("plan.toml", &[], &[]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(pool(&output), ([2, 2], two(), true), "{}", text(&output));

    // The configuration stands over the plan: by flag, and by environment.
    let output = planned("plan.toml", &[], &["--config", "build.test-weight=1"]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(pool(&output), ([1, 1], one(), true), "{}", text(&output));
    let output = planned("plan.toml", &[("CARGO_BUILD_TEST_JOBS", "2")], &[]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(pool(&output), ([2, 2], two(), false), "{}", text(&output));

    // A build-slot job's admitted share bounds the pool and each weight.
    let slot = |jobs: &'static str| [("BUILD_SLOT_HELD", "1"), ("CARGO_BUILD_JOBS", jobs)];
    let output = planned("plan.toml", &slot("3"), &[]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(pool(&output), ([2, 2], two(), false), "{}", text(&output));
    let output = planned("plan.toml", &slot("1"), &[]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(pool(&output), ([1, 1], one(), false), "{}", text(&output));

    // A pool Targo did not make grants one credit at a time. The plan's
    // weight for every harness lowers to 1 there, and says so; a weight a
    // harness entry asks for is refused, as before: the run judged nothing.
    write(
        root,
        "Makefile",
        "run:\n\t+@$(TARGO) --unverified test --offline --plan $(PLAN) --whole-plan \
         --no-fail-fast --message-format=json > make.out 2> make.err; echo $$? > make.status\n",
    );
    let under_make = |plan: &str| {
        let made = Command::new("make")
            .current_dir(root)
            .env_clear()
            .env("HOME", root)
            .env("CARGO_HOME", root.join("home"))
            .env("CARGO_TARGET_DIR", root.join("target.noindex"))
            .env("RUSTC", fixture_rustc())
            .env("PATH", std::env::var_os("PATH").unwrap())
            .args(["-j4", "run"])
            .arg(format!("TARGO={}", env!("CARGO_BIN_EXE_targo")))
            .arg(format!("PLAN={plan}"))
            .output()
            .unwrap();
        assert!(made.status.success(), "{}", text(&made));
        let read = |file: &str| fs::read_to_string(root.join(file)).unwrap();
        (
            read("make.status").trim().to_owned(),
            read("make.out"),
            read("make.err"),
        )
    };
    let (status, out, err) = under_make("plan.toml");
    assert_eq!(status, "0", "{out}\n{err}");
    assert!(
        err.contains(
            "the test plan's `[run] test-weight` is lowered to 1 for this run, and its pool to \
             2 test executables at once: the inherited jobserver's capacity is unknown"
        ),
        "{err}"
    );
    assert_eq!(
        ["one", "two"]
            .map(|package| fs::read_to_string(root.join(package).join("threads")).unwrap()),
        one(),
        "{out}\n{err}"
    );
    // The pool lowers with the weight. Two credits at two a harness are one
    // harness at a time, in a pool Targo made and in one it did not: with
    // the weight lowered to 1 and the two credits kept, both would run
    // together, twice the executables the plan asked for at once.
    write(
        root,
        "single.toml",
        &format!("{plan}[run]\ntest-jobs = 2\ntest-weight = 2\n"),
    );
    let output = planned("single.toml", &[], &[]);
    assert!(output.status.success(), "{}", text(&output));
    assert_eq!(pool(&output), ([2, 2], two(), false), "{}", text(&output));
    let (status, out, err) = under_make("single.toml");
    assert_eq!(status, "0", "{out}\n{err}");
    assert!(
        err.contains("is lowered to 1 for this run, and its pool to 1 test executable at once"),
        "{err}"
    );
    let made = Output {
        status: std::process::ExitStatus::default(),
        stdout: out.clone().into_bytes(),
        stderr: err.clone().into_bytes(),
    };
    assert_eq!(pool(&made), ([1, 1], one(), false), "{out}\n{err}");
    let (status, out, err) = under_make("explicit.toml");
    assert_eq!(status, "2", "{out}\n{err}");
    assert!(
        err.contains("test target `one` of `one` asks for weight 2, but the inherited jobserver's capacity is unknown"),
        "{err}"
    );

    // A pool of nothing is refused.
    write(root, "zero.toml", &format!("{plan}[run]\ntest-jobs = 0\n"));
    let output = planned("zero.toml", &[], &[]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output));
    assert!(
        text(&output).contains("`[run] test-jobs` must be 1 or more"),
        "{}",
        text(&output)
    );
}

// Trust: a harness Targo itself stops is reported with Targo's reason, even
// where the process had exited 101 by then (afa51423c2c). The first case of
// it, a line past the streaming limit, no longer stops a harness (the line
// is cut), so this holds the rule to a stop that remains: Targo cannot write
// the harness's output on. Targo's standard output here is a pipe nobody
// reads. The test executable prints one unterminated line and exits 101;
// Targo reads the line at the end of the stream, when the process has
// exited, fails to write it, and stops there. The failure is then an exit
// 101 beneath Targo's reason: read by `downcast_ref` at the call site it was
// a plain "test failed", with the reason dropped.
#[cfg(unix)]
#[test]
fn a_harness_targo_stops_is_reported_with_targos_reason_whatever_its_exit() {
    let world = world("test-plan-stopped-harness");
    let root = world.path();
    write(
        root,
        "Cargo.toml",
        "[workspace]\nmembers=['host']\nresolver='3'\n",
    );
    package(root, "host", "[[test]]\nname='stops'\nharness=false\n", "");
    write(
        root,
        "host/tests/stops.rs",
        "fn main() {\n\
             use std::io::Write as _;\n\
             let mut out = std::io::stdout();\n\
             out.write_all(b\"one line with no end\").unwrap();\n\
             out.flush().unwrap();\n\
             std::process::exit(101)\n\
         }\n",
    );
    write(
        root,
        "plan.toml",
        "schema = \"targo.test-plan.v1\"\n[select]\nmembers = \"default-members\"\n\
         [default]\ntargets = \"tests\"\n",
    );
    let built = targo(root)
        .args(["--plan", "plan.toml", "--whole-plan", "--no-run"])
        .output()
        .unwrap();
    assert!(built.status.success(), "{}", text(&built));
    // A pipe whose reading end is closed: every write to it fails.
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let output = targo(root)
        .args(["--plan", "plan.toml", "--whole-plan", "--no-fail-fast"])
        .stdout(writer)
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap()
        .wait_with_output()
        .unwrap();
    // The test executable did fail: the run is red.
    assert_eq!(output.status.code(), Some(101), "{}", text(&output));
    let stderr = String::from_utf8_lossy(&output.stderr);
    let failure = stderr
        .split("error: test \"stops\" of `host`: test failed, to rerun pass `--plan ")
        .nth(1)
        .unwrap_or_else(|| panic!("{stderr}"));
    // Targo's reason is printed with the failure it explains, above the
    // exit it found beneath.
    let reason = failure
        .find("Broken pipe")
        .unwrap_or_else(|| panic!("{stderr}"));
    let exit = failure
        .find("(exit status: 101)")
        .unwrap_or_else(|| panic!("{stderr}"));
    assert!(reason < exit, "{stderr}");
}

// Trust: a gate that plans around the lane (which members it hands it, which
// of them the lane tests on this host, which instruments a change moves)
// asks the lane. `--select-only` answers with the record a run of the same
// arguments would begin with, and what that run would do with each tool and
// workspace of its own, and builds nothing.
#[test]
fn a_select_only_listing_is_the_selection_of_a_run_and_builds_nothing() {
    let world = world("test-plan-select-only");
    let root = world.path();
    selection_workspace(root);
    let listing = |root: &Path, arguments: &[&str]| {
        targo(root)
            .args(["--plan", "plan.toml", "--select-only"])
            .args(arguments)
            .output()
            .unwrap()
    };
    // The whole of the standard output is one record, with or without JSON
    // messages asked for, and it is the run's own.
    write(
        root,
        "paths.txt",
        "crates/outer/src/gen/a.rs\nfixtures/one.txt\n",
    );
    let listed = listing(
        root,
        &["--changed-paths", "paths.txt", "--reached", "crates/host"],
    );
    assert_eq!(listed.status.code(), Some(0), "{}", text(&listed));
    let stdout = String::from_utf8_lossy(&listed.stdout);
    assert_eq!(stdout.lines().count(), 1, "{}", text(&listed));
    let record = first_record(&listed);
    assert_eq!(names(&record["members"]["touched"]), ["outer"]);
    assert_eq!(names(&record["members"]["reached"]), ["host"]);
    assert_eq!(names(&record["members"]["selected"]), ["host", "outer"]);
    // `host` is reached, not touched, so its instrument is kept.
    assert_eq!(
        performed(&record).0,
        ["default", "outer-extra", "host-fixtures"]
    );
    let instrument = &record["requests"][3];
    assert_eq!(instrument["role"], "instrument");
    assert_eq!(names(&instrument["packages"]), ["host"]);
    // No tool and no workspace of its own in this plan.
    assert_eq!(record["phases"], serde_json::json!([]));
    // Nothing was built, bounded or judged.
    let stderr = String::from_utf8_lossy(&listed.stderr);
    assert!(
        !root.join("target.noindex").join("debug").exists()
            && !stderr.contains("Compiling")
            && !stderr.contains("Bounded")
            && !stderr.contains("Finished"),
        "{}",
        text(&listed)
    );
    // The run of the same arguments begins with the same record, less the
    // key only a listing has.
    let run = targo(root)
        .args(["--plan", "plan.toml", "--no-run", "--message-format=json"])
        .args(["--changed-paths", "paths.txt", "--reached", "crates/host"])
        .output()
        .unwrap();
    assert!(run.status.success(), "{}", text(&run));
    let mut expected = first_record(&run);
    assert!(expected.get("phases").is_none(), "{expected}");
    expected["phases"] = serde_json::json!([]);
    assert_eq!(record, expected);

    // A change that selects nothing is listed as that, exit 0.
    write(root, "paths.txt", "README.md\n");
    let nothing = listing(root, &["--changed-paths", "paths.txt"]);
    assert_eq!(nothing.status.code(), Some(0), "{}", text(&nothing));
    assert!(performed(&first_record(&nothing)).0.is_empty());

    // What a run refuses, the listing refuses with the same status, after
    // the record that says why.
    write(root, "paths.txt", "crates/nobody/src/lib.rs\n");
    let refused = listing(root, &["--changed-paths", "paths.txt"]);
    assert_eq!(refused.status.code(), Some(2), "{}", text(&refused));
    assert_eq!(
        first_record(&refused)["unattributed"][0]["path"],
        "crates/nobody/src/lib.rs"
    );
    let unknown = listing(root, &["--reached", "crates/nope"]);
    assert_eq!(unknown.status.code(), Some(2), "{}", text(&unknown));
    assert!(unknown.stdout.is_empty(), "{}", text(&unknown));
    // It says what it lists: no change named is refused, as for a run.
    let unnamed = listing(root, &[]);
    assert_eq!(unnamed.status.code(), Some(2), "{}", text(&unnamed));
    // A listing runs nothing, so what steers a run is refused beside it.
    for flag in ["--no-run", "--unit-graph", "--unit-graph-parity"] {
        let both = listing(root, &["--whole-plan", flag]);
        assert_eq!(both.status.code(), Some(1), "{flag}: {}", text(&both));
    }

    // A workspace of its own: what the run would do with it on this target.
    let own = world.path().join("own");
    fs::create_dir_all(&own).unwrap();
    own_workspace_fixture(&own);
    let state = |cfg: &str, arguments: &[&str]| {
        own_plan(&own, cfg);
        let listed = listing(&own, arguments);
        assert_eq!(listed.status.code(), Some(0), "{}", text(&listed));
        let record = first_record(&listed);
        let phases = record["phases"].as_array().unwrap().clone();
        assert_eq!(phases.len(), 1, "{record}");
        assert_eq!(phases[0]["kind"], "workspace");
        assert_eq!(phases[0]["manifest"], OWN);
        (
            phases[0]["state"].as_str().unwrap().to_owned(),
            phases[0]["why"].as_str().unwrap().to_owned(),
        )
    };
    assert_eq!(state("", &["--reached", "crates/own"]).0, "selected");
    assert_eq!(state("", &["--reached", "shared"]).0, "not-selected");
    assert_eq!(
        state("cfg = 'unix'\n", &["--reached", "crates/own"]).0,
        "selected"
    );
    let (limited, why) = state("cfg = 'windows'\n", &["--reached", "crates/own"]);
    assert_eq!(limited, "not-applicable");
    assert!(why.contains("`cfg = 'windows'` does not hold for"), "{why}");
    // Unselected, its cfg is not asked: the row says what a run would.
    assert_eq!(
        state("cfg = 'windows'\n", &["--reached", "shared"]).0,
        "not-selected"
    );
    assert!(!own.join("target.noindex").join("debug").exists());
}

// Trust: the land gate plans its crates leg around this record (land_gate.py
// `lane_record` and `lane_selection`: the touched members, the active
// instruments and their hosts, the workspaces this target does not test, the
// paths the lane refuses). Its tests read the records below from
// `scripts/tests/fixtures/crates_lane_select_only.json`, so a field renamed or
// a state respelled here fails this test until that file says the same, and
// the gate's tests then hold the gate to the file.
#[test]
fn the_select_only_records_are_the_ones_the_land_gate_reads() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../scripts/tests/fixtures/crates_lane_select_only.json");
    let world = world("test-plan-select-only-gate");
    let listing = |root: &Path, arguments: &[&str], status: i32| {
        let output = targo(root)
            .args(["--plan", "plan.toml", "--select-only", "--locked"])
            .args(arguments)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(status), "{}", text(&output));
        let mut record = first_record(&output);
        // What depends on where the test runs.
        record["plan"] = "<plan>".into();
        record["sha256"] = "<sha256>".into();
        record
    };
    let root = world.path().join("selection");
    fs::create_dir_all(&root).unwrap();
    selection_workspace(&root);
    write(
        &root,
        "paths.txt",
        "crates/outer/src/gen/a.rs\nfixtures/one.txt\n",
    );
    let selected = listing(
        &root,
        &["--changed-paths", "paths.txt", "--reached", "crates/host"],
        0,
    );
    write(&root, "paths.txt", "crates/nobody/src/lib.rs\n");
    let refused = listing(&root, &["--changed-paths", "paths.txt"], 2);
    let own = world.path().join("own");
    fs::create_dir_all(&own).unwrap();
    own_workspace_fixture(&own);
    own_plan(&own, "cfg = 'windows'\n");
    let limited = listing(&own, &["--reached", "crates/own"], 0);
    let actual = serde_json::json!({
        "selected": selected,
        "refused": refused,
        "limited": limited,
    });
    // A not-applicable row names the target it does not hold for.
    let actual: Value =
        serde_json::from_str(&actual.to_string().replace(&host_triple(), "<host>")).unwrap();
    let expected: Value = serde_json::from_str(&fs::read_to_string(&fixture).unwrap_or_default())
        .unwrap_or(Value::Null);
    assert_eq!(
        actual,
        expected,
        "{} is not what --select-only prints; the land gate's tests read it. What it prints:\n{}",
        fixture.display(),
        serde_json::to_string_pretty(&actual).unwrap()
    );
}

// Trust: the plan builds every request in one graph, and is sound only if
// each request gets the units its own command gets. `--unit-graph-parity`
// holds the plan to that on the tree at hand, in one invocation: it is what
// a gate runs when the plan, a manifest or Targo's plan code changes.
#[test]
fn the_parity_check_holds_a_plan_to_its_requests_standalone_graphs() {
    let world = world("test-plan-parity-check");
    let root = world.path();
    parity_workspace(root);
    let check = |arguments: &[&str]| {
        targo(root)
            .args(["--plan", "plan.toml", "--unit-graph-parity"])
            .args(arguments)
            .output()
            .unwrap()
    };
    // The fixture's requests differ in features, in dev-dependency features
    // and in what a build dependency shares; the plan keeps each apart.
    for extra in [&[][..], &["--target", &host_triple()][..]] {
        let mut arguments = vec!["--whole-plan"];
        arguments.extend(extra);
        let checked = check(&arguments);
        let stderr = String::from_utf8_lossy(&checked.stderr);
        assert_eq!(checked.status.code(), Some(0), "{}", text(&checked));
        assert!(
            stderr.contains("Checked test plan")
                && stderr.contains("are those of its 7 requests' standalone graphs")
                && !stderr.contains("Compiling"),
            "{stderr}"
        );
        assert!(checked.stdout.is_empty(), "{}", text(&checked));
    }
    assert!(!root.join("target.noindex").join("debug").exists());
    // A narrowed run compares the requests it performs.
    let narrowed = check(&["--whole-plan", "--request", "lift-verify"]);
    assert!(
        String::from_utf8_lossy(&narrowed.stderr)
            .contains("are those of its 1 requests' standalone graphs"),
        "{}",
        text(&narrowed)
    );
    // A selection with no request has no graph, and says so: exit 2, never
    // a check that passed over nothing.
    let other = world.path().join("selection");
    fs::create_dir_all(&other).unwrap();
    selection_workspace(&other);
    write(&other, "paths.txt", "README.md\n");
    let nothing = targo(&other)
        .args(["--plan", "plan.toml", "--unit-graph-parity"])
        .args(["--changed-paths", "paths.txt"])
        .output()
        .unwrap();
    assert_eq!(nothing.status.code(), Some(2), "{}", text(&nothing));
    assert!(
        String::from_utf8_lossy(&nothing.stderr).contains("the selection performs no request"),
        "{}",
        text(&nothing)
    );
}
