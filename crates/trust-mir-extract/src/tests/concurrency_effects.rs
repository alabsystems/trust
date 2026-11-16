// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The spawn census end to end, in process: the fixture is compiled to
//! analysis and the `trust_spawn_census` query (the MIR adapter in
//! `concurrency_effects` over trust-ir's reachability engine) is asked for
//! every local body's verdict and rows. The fixture has no coroutine, so no
//! fn body is stolen before the query borrows it (with verification enabled
//! the analysis seam guarantees that for every crate).

use rustc_middle::mir::trust_proof::TrustSpawnVerdict;

use super::*;
use crate::concurrency_effects::{SpawnRowKind, is_std_thread_spawn};

const FIXTURE_PATH: &str = "concurrency_effects_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(fn_traits)]

// S1: a call of a std thread-creation entry point.
#[inline(never)]
pub fn launch() {
    let _handle = std::thread::spawn(|| {});
}
pub fn builder() {
    let _handle = std::thread::Builder::new().spawn(|| {});
}
pub fn scoped() {
    std::thread::scope(|s| {
        s.spawn(|| {});
    });
}
pub fn scoped_quiet() {
    std::thread::scope(|_s| {});
}

// S2: calls that exactly run a spawning body, at any depth, through cycles.
pub fn middle() { launch(); }
pub fn deeper_caller() { middle(); }
pub fn cycle_spawner(n: bool) {
    if n { cycle_wrapper(false); } else { launch(); }
}
pub fn cycle_wrapper(n: bool) { cycle_spawner(n); }
pub fn quiet_cycle_a(n: bool) {
    if n { quiet_cycle_b(false); }
}
pub fn quiet_cycle_b(n: bool) { quiet_cycle_a(n); }

macro_rules! chain { ($name:ident => $next:ident) => {
    #[inline(never)]
    pub fn $name() { $next(); }
} }
chain!(chain_01 => chain_02);
chain!(chain_02 => chain_03);
chain!(chain_03 => chain_04);
chain!(chain_04 => chain_05);
chain!(chain_05 => chain_06);
chain!(chain_06 => chain_07);
chain!(chain_07 => chain_08);
chain!(chain_08 => chain_09);
chain!(chain_09 => chain_10);
chain!(chain_10 => chain_11);
chain!(chain_11 => chain_12);
chain!(chain_12 => chain_13);
chain!(chain_13 => chain_14);
chain!(chain_14 => chain_15);
chain!(chain_15 => chain_16);
chain!(chain_16 => chain_17);
chain!(chain_17 => launch);
chain!(quiet_01 => quiet_02);
chain!(quiet_02 => quiet_03);
chain!(quiet_03 => quiet_leaf);
#[inline(never)]
pub fn quiet_leaf() {}

// The resolved instance, not the syntactic callee: a local impl of a foreign
// trait, a local fn named `spawn`, `let f = launch; f()` (S2 at every opt
// level), callable-trait calls on a closure and on a fn item.
pub struct Spawner;
impl Default for Spawner {
    fn default() -> Self { launch(); Spawner }
}
pub fn via_foreign_trait_impl() -> Spawner { Spawner::default() }
pub mod counterfeit {
    #[inline(never)]
    pub fn spawn() {}
}
pub fn lookalike() { counterfeit::spawn(); }
pub fn call_local_fndef() { let f = launch; f() }
pub fn closure_fn_call() {
    let f = || { let _ = std::thread::spawn(|| {}); };
    f();
}
pub fn fn_item_call_once() {
    std::ops::FnOnce::call_once(launch, ());
}

// Generics: an instance reached in this crate is exact; reach only through a
// definition's own type parameter is PARAM (R1).
pub trait Run { fn run(&self); }
pub struct Loud;
impl Run for Loud { fn run(&self) { launch() } }
pub struct Soft;
impl Run for Soft { fn run(&self) {} }
pub fn go<T: Run>(t: &T) { t.run() }
pub fn go_loud() { go(&Loud) }
pub fn go_soft() { go(&Soft) }
pub fn go_param<T: Run>(t: &T) { t.run() }
fn run_value<F: FnOnce()>(f: F) { f() }
pub fn fn_item_to_generic() { run_value(launch); }

// Drops: S3 through an owned value, a `Vec` (std's own drop glue), never
// through `PhantomData` or a type with no drop glue.
pub struct DropSpawner;
impl Drop for DropSpawner { fn drop(&mut self) { launch(); } }
pub fn drops_spawner(_s: DropSpawner) {}
pub fn drops_vec(_v: Vec<DropSpawner>) {}
pub fn phantom(_p: std::marker::PhantomData<DropSpawner>) {}

// A const-generic body walked at a concrete instance (ay-chc's `dt`): its MIR
// drops a `[_; N]` of a type that needs a drop, and the instance's environment
// holds no `N`. Each drop is judged at the instance's type, `[_; 2]`.
pub struct QuietDrop;
impl Drop for QuietDrop { fn drop(&mut self) {} }
fn drop_quiet<const N: usize>(_items: [QuietDrop; N]) {}
pub fn drops_quiet() { drop_quiet([QuietDrop, QuietDrop]) }
fn drop_spawners<const N: usize>(_items: [DropSpawner; N]) {}
pub fn drops_spawners(items: [DropSpawner; 2]) { drop_spawners(items) }

// Callables made into values: ESCAPES where named, INDIRECT where called.
fn run_ptr(f: fn()) { f() }
pub fn fn_item_reified() -> fn() { launch }
pub fn std_spawn_as_value() -> fn(fn()) -> std::thread::JoinHandle<()> {
    std::thread::spawn::<fn(), ()>
}
pub trait Job { fn work(&self); }
impl Job for Loud { fn work(&self) { launch() } }
pub fn erase(l: &'static Loud) -> &'static dyn Job { l }
pub fn work_dyn(j: &dyn Job) { j.work() }
pub const HOOK: fn() = launch;
pub fn reads_hook() -> fn() { HOOK }

// Foreign code is opaque (R3).
unsafe extern "C" {
    fn ffi_quiet();
}
pub fn calls_ffi() { unsafe { ffi_quiet() } }
"#;

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected spawn-census fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary reads are not supported in the spawn-census fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Default)]
struct CensusCallbacks {
    checked: bool,
}

impl rustc_driver::Callbacks for CensusCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        let census = tcx.trust_spawn_census(());
        assert_eq!(census.fallback, None, "the certificate must be accepted");
        let by_name: BTreeMap<String, &rustc_middle::mir::trust_proof::TrustSpawnSites<'tcx>> =
            census
                .definitions
                .iter()
                .filter(|(def, _)| {
                    matches!(
                        tcx.def_kind(def.to_def_id()),
                        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
                    )
                })
                .map(|(def, sites)| (tcx.def_path_str(def.to_def_id()), sites))
                .collect();
        let verdict = |name: &str| -> TrustSpawnVerdict {
            by_name.get(name).unwrap_or_else(|| panic!("no census answer for {name}")).verdict
        };
        let texts = |name: &str| -> Vec<String> {
            by_name[name].rows.iter().map(|row| row.text.clone()).collect()
        };

        use TrustSpawnVerdict::*;
        let expected: &[(&str, TrustSpawnVerdict)] = &[
            ("launch", Spawns),
            ("builder", Spawns),
            ("scoped", Spawns),
            ("middle", Spawns),
            ("deeper_caller", Spawns),
            ("cycle_spawner", Spawns),
            ("cycle_wrapper", Spawns),
            ("chain_01", Spawns),
            ("via_foreign_trait_impl", Spawns),
            ("call_local_fndef", Spawns),
            ("closure_fn_call", Spawns),
            ("fn_item_call_once", Spawns),
            ("go", Spawns),
            ("go_loud", Spawns),
            ("fn_item_to_generic", Spawns),
            ("drops_spawner", Spawns),
            ("drops_vec", Spawns),
            ("drop_spawners", Spawns),
            ("drops_spawners", Spawns),
            ("fn_item_reified", Escapes),
            ("std_spawn_as_value", Escapes),
            ("erase", Escapes),
            ("reads_hook", Escapes),
            ("run_ptr", Indirect),
            ("work_dyn", Indirect),
            ("quiet_cycle_a", Quiet),
            ("quiet_cycle_b", Quiet),
            ("quiet_01", Quiet),
            ("quiet_leaf", Quiet),
            ("lookalike", Quiet),
            ("counterfeit::spawn", Quiet),
            ("go_soft", Quiet),
            ("go_param", Quiet),
            ("phantom", Quiet),
            ("drop_quiet", Quiet),
            ("drops_quiet", Quiet),
            ("calls_ffi", Quiet),
            // A scope that starts no thread claims nothing, but its join path
            // (`thread::park`) reaches std's thread-local accessor, called
            // through a fn pointer of one `Unclassified` argument, and that
            // pool holds `std_spawn_as_value`'s `thread::spawn::<fn(), ()>`
            // (one thin-pointer argument): INDIRECT, the coarse keys' cost.
            ("scoped_quiet", Indirect),
        ];
        let wrong: Vec<String> = expected
            .iter()
            .filter(|(name, want)| verdict(name) != *want)
            .map(|(name, want)| format!("{name}: want {want:?}, got {:?}", verdict(name)))
            .collect();
        assert!(wrong.is_empty(), "census verdicts differ:\n{}", wrong.join("\n"));

        // Every refusing body carries a row, and only SPAWNS rows claim a spawn.
        for (name, sites) in &by_name {
            if sites.verdict != Quiet {
                assert!(!sites.rows.is_empty(), "{name} refuses with no row");
            }
            for row in &sites.rows {
                assert_ne!(row.verdict, Quiet);
                let claims =
                    row.text.contains("reaches a std thread spawn through calls and drops")
                        || row.text.starts_with("direct std thread spawn");
                assert_eq!(claims, row.verdict == Spawns, "{name}: {}", row.text);
            }
        }
        // A row's witness is rendered for the verifier, which reads the rows.
        // This test's frontend is embedded, so verification is off and no row
        // cites a path; the verified lane's witnesses are pinned by the UI
        // suite (`tests/ui/trust/thread-spawn-census/drop_glue_edge_refused.rs`).
        assert_eq!(texts("deeper_caller"), [SpawnRowKind::CallSpawns { local: true }.text("")]);
        assert!(texts("launch").iter().all(|text| !text.contains(" via ")));
        // `go` has a row, from its instance `go::<Loud>` (which only the
        // witness names); `go_soft`, whose instance starts no thread, has none.
        assert!(!texts("go").is_empty());
        assert!(texts("go_soft").is_empty());
        // ESCAPES and INDIRECT rows never claim a spawn.
        assert!(texts("work_dyn").iter().all(|text| text.starts_with("may spawn (indirect)")));
        assert!(SpawnRowKind::IndirectCallMaySpawn.text("").contains("not a spawn claim"));

        // The seeds are std's own diagnostic items, never a local look-alike.
        let counterfeit = tcx
            .hir_body_owners()
            .find(|def| tcx.def_path_str(def.to_def_id()) == "counterfeit::spawn")
            .expect("counterfeit::spawn");
        assert!(!is_std_thread_spawn(tcx, counterfeit.to_def_id()));

        // The answer is a function of the program: the projection query agrees.
        for (def, sites) in &census.definitions {
            assert_eq!(tcx.trust_spawn_sites(*def).verdict, sites.verdict);
        }
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
fn spawn_census_labels_the_fixture_by_construction() {
    check_spawn_census_fixture("globally");
}

#[test]
fn spawn_census_labels_the_fixture_with_the_old_solver() {
    check_spawn_census_fixture("coherence");
}

fn check_spawn_census_fixture(solver: &str) {
    let mut callbacks = CensusCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "concurrency_effects_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
        "-Zinline-mir=no".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        format!("-Znext-solver={solver}"),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the spawn-census fixture with {solver}");
    assert!(callbacks.checked);
}

#[test]
fn row_kinds_claim_a_spawn_only_for_s1_s3() {
    for kind in [
        SpawnRowKind::DirectSpawn,
        SpawnRowKind::CallSpawns { local: true },
        SpawnRowKind::CallSpawns { local: false },
        SpawnRowKind::DropSpawns { local_drop: true },
        SpawnRowKind::DropSpawns { local_drop: false },
    ] {
        assert!(kind.claims_spawn());
        assert_eq!(kind.verdict(), TrustSpawnVerdict::Spawns);
        assert!(!kind.text("a → b").contains("not a spawn claim"));
    }
    for kind in [
        SpawnRowKind::CreatesSpawning,
        SpawnRowKind::CreatesEscaping,
        SpawnRowKind::HandsDropGlue,
        SpawnRowKind::ReadsSpawning,
        SpawnRowKind::CalleeEscapes,
        SpawnRowKind::IndirectCallMaySpawn,
        SpawnRowKind::ReachesIndirect,
        SpawnRowKind::NotEnumerated,
    ] {
        assert!(!kind.claims_spawn());
        assert_ne!(kind.verdict(), TrustSpawnVerdict::Spawns);
        assert!(kind.text("a → b").contains("fail-closed; not a spawn claim"));
    }
    assert!(SpawnRowKind::IndirectCallMaySpawn.text("").starts_with("may spawn (indirect)"));
    assert!(
        SpawnRowKind::NotEnumerated.text("").starts_with("not enumerated (no spawn was found)")
    );
}

/// An `asm!` whose template, placeholders standing for operand text, is only
/// C block comments and whitespace runs no instruction (zmij's value barrier);
/// anything else in the template, a malformed piece, and every `naked_asm!`
/// is inline assembly that may run.
#[test]
fn a_comment_only_asm_template_runs_nothing() {
    use rustc_middle::mir::InlineAsmMacro;
    let runs_nothing = |template: &str| {
        crate::concurrency_effects::asm_executes_nothing(InlineAsmMacro::Asm, &[template], &[])
    };
    assert!(runs_nothing("/*{0}*/"));
    assert!(runs_nothing("  /* a */\n\t/* {1:x} b */ "));
    assert!(runs_nothing("/*{{*/"));
    assert!(runs_nothing(""));
    assert!(!runs_nothing("nop"));
    assert!(!runs_nothing("/*{0}*/ nop"));
    assert!(!runs_nothing("{0}"));
    assert!(!runs_nothing("/* unterminated"));
    assert!(!runs_nothing("# a comment"));
    assert!(!runs_nothing("// a comment"));
    assert!(!runs_nothing("/*}*/"));
    assert!(!crate::concurrency_effects::asm_executes_nothing(
        InlineAsmMacro::NakedAsm,
        &["/**/"],
        &[]
    ));
}
