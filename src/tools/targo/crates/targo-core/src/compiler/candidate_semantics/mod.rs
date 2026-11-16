//! The SAME resolved-graph comparison for a parent and produced coordinator.
//!
//! Digests are equality DATA. They do not authenticate a source, compiler,
//! linker, SDK, output lock, resource loan, or completed process. Their live
//! owners must be checked separately before/after capture and final dispatch.
//! In particular, a candidate's own report cannot establish these facts.

use super::{
    BuildContext, BuildRunner, Compilation, CompileKind, CompileMode, Unit, UserIntent, exact_unit,
};
use crate::context::ConfigValue;
use crate::util::CargoResult;
use cargo_util::Sha256;
use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt as _;
use std::path::{Path, PathBuf};

const MAX_UNITS: usize = 4096;
const MAX_EDGES: usize = 16384;
const MAX_GRAPH_DEPTH: usize = 128;
const MAX_ENTRIES: usize = 4096;
const MAX_BYTES: usize = 8 * 1024 * 1024;
const MAX_DEPTH: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mode {
    Build,
    Check,
}

/// Explicit selection from the original parent owners, not candidate JSON.
pub(crate) struct Selected<'a> {
    pub mode: Mode,
    pub sources: &'a [PathBuf],
    pub manifest: &'a Path,
    pub package: &'a str,
    pub binary: &'a str,
    pub output_root: &'a Path,
    pub cargo_home: &'a Path,
    pub sdk_root: &'a Path,
    pub compiler: &'a Path,
    pub compiler_sha256: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Digests {
    pub configuration_sha256: [u8; 32],
    pub coverage_sha256: [u8; 32],
}

/// The same resolved parent graph's equality and expected output DATA.
/// Neither paths nor metadata reconstruct any original output/input owner.
pub(crate) struct CandidateConfiguration {
    pub digests: Digests,
    // Retain the same complete expected output DATA used to prepare commands.
    pub _outputs: Vec<super::build_runner::CandidateOutput>,
    pub commands: super::candidate_commands::ExpectedCommands,
}

pub(crate) fn validate_child(
    runner: &BuildRunner<'_, '_>,
    selected: &Selected<'_>,
    configuration_sha256: [u8; 32],
    coverage_sha256: [u8; 32],
) -> CargoResult<()> {
    let actual = capture(runner, selected)?;
    anyhow::ensure!(
        actual
            == Digests {
                configuration_sha256,
                coverage_sha256
            },
        "candidate resolved configuration or complete graph coverage differs from parent selection"
    );
    Ok(())
}

/// Called before Layout acquisition. The parent must resolve using the exact
/// environment selected for the child, including non-Unicode native bytes.
/// There is deliberately NO transport-variable exemption: ordinary env! can
/// observe those names too. Final materialized compiler commands still need
/// original native input/environment/linker validation at dispatch.
pub(crate) fn capture(
    runner: &BuildRunner<'_, '_>,
    selected: &Selected<'_>,
) -> CargoResult<Digests> {
    validate_selection(runner.bcx, selected)?;
    preflight_graph(runner.bcx)?;
    capture_checked(runner.bcx, &runner.compilation, selected, |unit| {
        exact_unit::capture(runner, unit)
    })
}

/// Parent planning with the SAME resolved projection but without constructing
/// BuildRunner, ResourceRuntime, a credit bank, jobserver or output Layout.
/// Context resolution and any compiler probes must already use original
/// admission; this function supplies no execution or input-custody authority.
/// Expected filenames and metadata use the ordinary calculation for this SAME
/// graph. They do not establish output existence, ownership or readability.
pub(crate) fn capture_context<'a, 'gctx>(
    bcx: &'a BuildContext<'a, 'gctx>,
    selected: &Selected<'_>,
    preparation: std::sync::Arc<super::candidate_commands::Preparation>,
    jobserver: &cargo_util::Jobserver,
) -> CargoResult<CandidateConfiguration> {
    validate_selection(bcx, selected)?;
    preflight_graph(bcx)?;
    preparation.require_context(bcx)?;
    let mut compilation = Compilation::for_candidate(bcx, preparation.clone())?;
    let graph = exact_unit::Graph::new(bcx)?;
    let digests = capture_checked(bcx, &compilation, selected, |unit| graph.capture(unit))?;
    let lto = super::lto::generate(bcx)?;
    let files = super::build_runner::CompilationFiles::projected(bcx, &lto, &graph)?;
    let outputs = super::build_runner::projected_outputs(bcx, &graph, &files)?;
    // Only the ordinary runner creates directories. This shared bookkeeping
    // gives fill_env exactly the same loader/dependency locations as prepare.
    let _expected_directories = compilation.record_output_paths(bcx, &files);
    let commands = super::candidate_commands::prepare(
        bcx,
        &compilation,
        &files,
        &lto,
        &graph,
        &outputs,
        preparation,
        jobserver,
    )?;
    Ok(CandidateConfiguration {
        digests,
        _outputs: outputs,
        commands,
    })
}

/// General job DATA reuses the exact native configuration recipe, with its
/// own typed node selection/ordinary graph validation. No candidate grant or
/// binary-only selection is inferred from this equality projection.
pub(super) fn capture_native_job(
    runner: &BuildRunner<'_, '_>,
    selected: &Selected<'_>,
) -> CargoResult<Digests> {
    anyhow::ensure!(
        runner.bcx.roots.len() == 1,
        "native job requires exactly its selected root"
    );
    preflight_graph(runner.bcx)?;
    capture_checked(runner.bcx, &runner.compilation, selected, |unit| {
        exact_unit::capture(runner, unit)
    })
}

fn validate_selection(bcx: &BuildContext<'_, '_>, selected: &Selected<'_>) -> CargoResult<()> {
    let config = bcx.build_config;
    anyhow::ensure!(
        bcx.roots.len() == 1
            && !bcx.unit_graph.is_empty()
            && bcx.unit_graph.len() <= MAX_UNITS
            && config.jobs == 1
            && config.requested_kinds == [CompileKind::Host],
        "candidate requires one binary and a bounded nonempty serial graph"
    );
    let mode = match (selected.mode, config.intent) {
        (Mode::Build, UserIntent::Build) => CompileMode::Build,
        (Mode::Check, UserIntent::Check { test: false }) => CompileMode::Check { test: false },
        _ => anyhow::bail!("candidate build/check intent differs from parent selection"),
    };
    anyhow::ensure!(
        !config.keep_going
            && !config.force_rebuild
            && !config.unit_graph
            && !config.dry_run
            && !config.compile_time_deps_only
            && config.primary_unit_rustc.is_none()
            && config.export_dir.is_none()
            && config
                .rustfix_diagnostic_server
                .try_borrow()
                .is_ok_and(|server| server.is_none())
            && !config.sbom
            && !config.timing_report
            && !config.future_incompat_report,
        "candidate refuses alternate execution, export, fixing and side-report modes"
    );
    anyhow::ensure!(
        bcx.rustc().wrapper.is_none()
            && bcx.rustc().workspace_wrapper.is_none()
            && bcx.extra_compiler_args.values().all(Vec::is_empty),
        "candidate refuses compiler wrappers and extra arguments"
    );
    anyhow::ensure!(
        !bcx.gctx.network_allowed() && !bcx.gctx.lock_update_allowed(),
        "candidate requires locked offline dependency resolution"
    );
    let root = &bcx.roots[0];
    anyhow::ensure!(
        root.pkg.name().as_str() == selected.package
            && root.target.name() == selected.binary
            && root.target.is_bin()
            && root.mode == mode
            && root.pkg.manifest_path() == selected.manifest
            && bcx.ws.root_manifest() == selected.manifest,
        "candidate selected a different original standalone binary"
    );
    anyhow::ensure!(
        bcx.ws.target_dir().as_path_unlocked() == selected.output_root
            && bcx.ws.build_dir().as_path_unlocked() == selected.output_root
            && bcx.gctx.home().as_path_unlocked() == selected.cargo_home
            && bcx.rustc().path == selected.compiler
            && selected.compiler == selected.sdk_root.join("bin/trustc")
            && selected.compiler_sha256 != [0; 32],
        "candidate actual compiler, build/output directory or home differs from original selection"
    );
    anyhow::ensure!(
        !selected.sources.is_empty()
            && selected.sources.len() <= 32
            && selected.sources.iter().all(|path| path.is_absolute())
            && selected.sources.iter().collect::<BTreeSet<_>>().len() == selected.sources.len(),
        "candidate requires a bounded distinct original package source population"
    );
    let mut seen_sources = BTreeSet::new();
    for unit in bcx.unit_graph.keys() {
        anyhow::ensure!(
            unit.kind == CompileKind::Host
                && unit.mode == mode
                && !unit.target.proc_macro()
                && !unit.target.is_custom_build()
                && !unit.is_std
                && !unit.artifact.is_true()
                && unit.artifact_target_for_features.is_none(),
            "candidate refuses scripts, macros, std, artifact dependencies and non-native compile units"
        );
        anyhow::ensure!(
            selected.sources.iter().any(|path| path == unit.pkg.root()),
            "candidate graph includes an unselected original package namespace"
        );
        seen_sources.insert(unit.pkg.root());
    }
    anyhow::ensure!(
        seen_sources.len() == selected.sources.len(),
        "candidate graph omitted a selected original package namespace"
    );
    Ok(())
}

fn capture_checked(
    bcx: &BuildContext<'_, '_>,
    compilation: &Compilation<'_>,
    selected: &Selected<'_>,
    mut capture_unit: impl FnMut(&Unit) -> CargoResult<std::sync::Arc<exact_unit::Captured>>,
) -> CargoResult<Digests> {
    let root = &bcx.roots[0];
    let mut coverage = Vec::with_capacity(bcx.unit_graph.len());
    for unit in bcx.unit_graph.keys() {
        // Preserve multiplicity, even if distinct resolved units have equal
        // semantic digests. A set here could hide omitted graph work.
        coverage.push(capture_unit(unit)?.digest.clone());
    }
    coverage.sort();
    let root_digest = capture_unit(root)?.digest.clone();
    let mut graph = Encoding::new(b"trust.candidate.complete-native-graph.v1")?;
    graph.bytes(root_digest.as_bytes())?;
    graph.number(coverage.len())?;
    for digest in coverage {
        graph.bytes(digest.as_bytes())?;
    }

    let mut configuration = Encoding::new(b"trust.candidate.resolved-configuration.v1")?;
    configuration.bytes(if selected.mode == Mode::Build {
        b"build"
    } else {
        b"check"
    })?;
    for path in [
        selected.manifest,
        selected.output_root,
        selected.cargo_home,
        selected.sdk_root,
        selected.compiler,
    ] {
        configuration.os(path.as_os_str())?;
    }
    configuration.bytes(&selected.compiler_sha256)?;
    let mut sources = selected.sources.iter().collect::<Vec<_>>();
    sources.sort();
    configuration.number(sources.len())?;
    for source in sources {
        configuration.os(source.as_os_str())?;
    }
    configuration.bytes(&bcx.rustc().full_content_identity(true).ok_or_else(|| {
        anyhow::anyhow!("candidate actual compiler content identity is unavailable")
    })?)?;
    configuration.bytes(bcx.host_triple().as_bytes())?;
    configuration.bytes(bcx.source_fingerprint.as_str().as_bytes())?;
    configuration.bytes(bcx.build_config.requested_profile.as_bytes())?;
    configuration.bytes(bcx.profiles.get_dir_name().as_bytes())?;
    use super::MessageFormat;
    let message_format = match bcx.build_config.message_format {
        MessageFormat::Human => [0, 0, 0, 0],
        MessageFormat::Short => [1, 0, 0, 0],
        MessageFormat::Json {
            render_diagnostics,
            short,
            ansi,
        } => [
            2,
            u8::from(render_diagnostics),
            u8::from(short),
            u8::from(ansi),
        ],
    };
    configuration.bytes(&message_format)?;
    configuration.number(usize::from(bcx.action_sandbox))?;
    configuration.number(usize::from(bcx.gctx.extra_verbose()))?;
    configuration.number(usize::from(bcx.gctx.target_applies_to_host()?))?;
    configuration.optional_path(compilation.target_linker(CompileKind::Host))?;
    configuration.optional_path(compilation.host_linker())?;
    // All resolved file configuration and raw inherited environment, not a
    // hand-picked list of flags or Unicode-filtered display snapshot.
    let values = bcx.gctx.values()?;
    configuration.table(values, 0)?;
    configuration.environment(bcx.gctx.env_os())?;
    configuration.environment(
        bcx.gctx
            .env_config()?
            .iter()
            .map(|(key, value)| (OsStr::new(key), value.as_os_str())),
    )?;
    // Unstable CLI switches may generate compiler flags outside exact_unit.
    // These are actual parsed values, not strings from the child's report.
    let unstable = bcx.gctx.cli_unstable();
    configuration.features(unstable.allow_features.as_ref())?;
    for flag in [
        unstable.public_dependency,
        unstable.binary_dep_depinfo,
        unstable.profile_hint_mostly_unused,
        unstable.hint_msrv,
    ] {
        configuration.number(usize::from(flag))?;
    }
    Ok(Digests {
        configuration_sha256: configuration.finish(),
        coverage_sha256: graph.finish(),
    })
}

pub(super) fn preflight_graph(bcx: &BuildContext<'_, '_>) -> CargoResult<()> {
    use crate::util::data_structures::HashMap;
    let graph = &bcx.unit_graph;
    // The first exact_unit capture recursively visits the WHOLE graph. Bound
    // depth, multiplicity and serialized unit facts before entering that path.
    anyhow::ensure!(
        !graph.is_empty() && graph.len() <= MAX_UNITS,
        "candidate graph exceeds finite unit population or is empty"
    );
    let units = graph.keys().collect::<Vec<_>>();
    let indices = units
        .iter()
        .enumerate()
        .map(|(index, unit)| ((*unit).clone(), index))
        .collect::<HashMap<_, _>>();
    let mut edges = 0usize;
    let mut adjacency = Vec::with_capacity(units.len());
    // A streaming serializer checks all variable-size identity components;
    // there is no large temporary Vec preceding the finite byte limit.
    let mut serialized = LimitedSink(MAX_BYTES);
    for unit in &units {
        // Target::serialize collects feature names and clones crate types
        // internally. Bound those borrowed populations before invoking it.
        anyhow::ensure!(
            unit.target
                .required_features()
                .is_none_or(|features| features.len() <= MAX_ENTRIES),
            "candidate target exceeds finite required-feature population"
        );
        if let crate::workspace::TargetKind::Lib(types)
        | crate::workspace::TargetKind::ExampleLib(types) = unit.target.kind()
        {
            anyhow::ensure!(
                types.len() <= MAX_ENTRIES,
                "candidate target exceeds finite crate-type population"
            );
        }
        let dependencies = &graph[*unit];
        edges = edges
            .checked_add(dependencies.len())
            .ok_or_else(|| anyhow::anyhow!("candidate graph edge count overflow"))?;
        anyhow::ensure!(
            edges <= MAX_EDGES,
            "candidate graph exceeds finite edge population"
        );
        let children = dependencies
            .iter()
            .map(|dependency| {
                indices.get(&dependency.unit).copied().ok_or_else(|| {
                    anyhow::anyhow!("candidate dependency missing from complete graph")
                })
            })
            .collect::<CargoResult<Vec<_>>>()?;
        adjacency.push(children);
        serde_json::to_writer(
            &mut serialized,
            &(
                &unit.target,
                &unit.profile,
                &unit.features,
                unit.rustflags.as_ref(),
                unit.rustdocflags.as_ref(),
                unit.links_overrides.as_ref(),
                bcx.extra_args_for(unit),
            ),
        )?;
        for dependency in dependencies {
            serde_json::to_writer(
                &mut serialized,
                &(
                    dependency.extern_crate_name.as_str(),
                    dependency.dep_name.map(|name| name.as_str()),
                    dependency.public,
                    dependency.noprelude,
                    dependency.nounused,
                ),
            )?;
        }
    }
    graph_depth(&adjacency)?;
    Ok(())
}

/// Iterative postorder: no recursive graph walk before its depth is checked.
/// Longest paths, cycles and every repeated edge remain represented.
fn graph_depth(adjacency: &[Vec<usize>]) -> CargoResult<()> {
    anyhow::ensure!(
        adjacency.len() <= MAX_UNITS,
        "candidate graph exceeds finite unit population"
    );
    let mut edges = 0usize;
    for children in adjacency {
        edges = edges
            .checked_add(children.len())
            .ok_or_else(|| anyhow::anyhow!("candidate edge overflow"))?;
        anyhow::ensure!(
            edges <= MAX_EDGES && children.iter().all(|&child| child < adjacency.len()),
            "candidate graph has excessive edges or an absent child"
        );
    }
    let mut heights = vec![None; adjacency.len()];
    let mut visiting = vec![false; adjacency.len()];
    let mut pending = Vec::new();
    for index in 0..adjacency.len() {
        pending.push((index, false));
        while let Some((index, expanded)) = pending.pop() {
            if heights[index].is_some() {
                continue;
            }
            if expanded {
                let height = adjacency[index]
                    .iter()
                    .map(|&child| heights[child].unwrap())
                    .max()
                    .unwrap_or(0)
                    + 1usize;
                anyhow::ensure!(
                    height <= MAX_GRAPH_DEPTH,
                    "candidate graph exceeds finite dependency depth"
                );
                heights[index] = Some(height);
                visiting[index] = false;
            } else {
                anyhow::ensure!(!visiting[index], "cycle in selected candidate graph");
                visiting[index] = true;
                pending.push((index, true));
                for &child in &adjacency[index] {
                    pending.push((child, false));
                }
            }
        }
    }
    Ok(())
}

struct LimitedSink(usize);
impl std::io::Write for LimitedSink {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0 = self.0.checked_sub(bytes.len()).ok_or_else(|| {
            std::io::Error::other("candidate graph identity exceeds finite serialized byte limit")
        })?;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Length-delimited, bounded canonical DATA encoding. Values, including secret
/// environment entries, are hashed in memory and never emitted to diagnostics.
struct Encoding {
    hash: Sha256,
    remaining: usize,
    nodes: usize,
}
impl Encoding {
    fn new(schema: &[u8]) -> CargoResult<Self> {
        let mut result = Self {
            hash: Sha256::new(),
            remaining: MAX_BYTES,
            nodes: MAX_ENTRIES,
        };
        result.bytes(schema)?;
        Ok(result)
    }
    fn bytes(&mut self, bytes: &[u8]) -> CargoResult<()> {
        let size = bytes
            .len()
            .checked_add(8)
            .ok_or_else(|| anyhow::anyhow!("candidate encoding overflow"))?;
        self.remaining = self
            .remaining
            .checked_sub(size)
            .ok_or_else(|| anyhow::anyhow!("candidate configuration exceeds finite byte limit"))?;
        self.hash
            .update(&(bytes.len() as u64).to_be_bytes())
            .update(bytes);
        Ok(())
    }
    fn number(&mut self, number: usize) -> CargoResult<()> {
        self.bytes(&(number as u64).to_be_bytes())
    }
    fn os(&mut self, value: &OsStr) -> CargoResult<()> {
        self.bytes(value.as_bytes())
    }
    fn optional_path(&mut self, path: Option<&Path>) -> CargoResult<()> {
        self.number(usize::from(path.is_some()))?;
        if let Some(path) = path {
            self.os(path.as_os_str())?;
        }
        Ok(())
    }
    fn features(&mut self, features: Option<&BTreeSet<String>>) -> CargoResult<()> {
        self.number(usize::from(features.is_some()))?;
        if let Some(features) = features {
            anyhow::ensure!(
                features.len() <= MAX_ENTRIES,
                "candidate allowed feature population exceeds finite limit"
            );
            self.number(features.len())?;
            for feature in features {
                self.bytes(feature.as_bytes())?;
            }
        }
        Ok(())
    }
    fn environment<'a>(
        &mut self,
        entries: impl Iterator<Item = (&'a OsStr, &'a OsStr)>,
    ) -> CargoResult<()> {
        let mut entries = entries.take(MAX_ENTRIES + 1).collect::<Vec<_>>();
        anyhow::ensure!(
            entries.len() <= MAX_ENTRIES,
            "candidate environment exceeds finite entry limit"
        );
        entries.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        self.number(entries.len())?;
        for (key, value) in entries {
            self.os(key)?;
            self.os(value)?;
        }
        Ok(())
    }
    fn table(
        &mut self,
        table: &crate::util::data_structures::HashMap<String, ConfigValue>,
        depth: usize,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            depth <= MAX_DEPTH && table.len() <= MAX_ENTRIES,
            "candidate configuration exceeds finite depth/entry limit"
        );
        let mut entries = table.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.cmp(b.0));
        self.number(entries.len())?;
        for (key, value) in entries {
            self.bytes(key.as_bytes())?;
            self.value(value, depth + 1)?;
        }
        Ok(())
    }
    fn value(&mut self, value: &ConfigValue, depth: usize) -> CargoResult<()> {
        anyhow::ensure!(
            depth <= MAX_DEPTH && self.nodes > 0,
            "candidate configuration exceeds finite node/depth limit"
        );
        self.nodes -= 1;
        let definition = match value {
            ConfigValue::Integer(_, def)
            | ConfigValue::String(_, def)
            | ConfigValue::Boolean(_, def)
            | ConfigValue::List(_, def)
            | ConfigValue::Table(_, def) => def,
        };
        use crate::context::Definition;
        match definition {
            Definition::BuiltIn => self.bytes(b"builtin")?,
            Definition::Path(path) => {
                self.bytes(b"file")?;
                self.os(path.as_os_str())?;
            }
            Definition::Environment(name) => {
                self.bytes(b"environment")?;
                self.bytes(name.as_bytes())?;
            }
            Definition::Cli(path) => {
                self.bytes(b"cli")?;
                self.optional_path(path.as_deref())?;
            }
        }
        match value {
            ConfigValue::Integer(value, _) => {
                self.bytes(b"integer")?;
                self.bytes(&value.to_be_bytes())?;
            }
            ConfigValue::String(value, _) => {
                self.bytes(b"string")?;
                self.bytes(value.as_bytes())?;
            }
            ConfigValue::Boolean(value, _) => {
                self.bytes(b"boolean")?;
                self.number(usize::from(*value))?;
            }
            ConfigValue::List(values, _) => {
                anyhow::ensure!(
                    values.len() <= self.nodes,
                    "candidate configuration list exceeds remaining nodes"
                );
                self.bytes(b"list")?;
                self.number(values.len())?;
                for value in values {
                    self.value(value, depth + 1)?;
                }
            }
            ConfigValue::Table(table, _) => {
                self.bytes(b"table")?;
                self.table(table, depth + 1)?;
            }
        }
        Ok(())
    }
    fn finish(mut self) -> [u8; 32] {
        self.hash.finish()
    }
}

#[cfg(test)]
mod tests;
