//! cargo-sbom precursor files for external tools to create SBOM files from.
//! See [`build_sbom_graph`] for more.

use crate::util::data_structures::{HashMap, HashSet};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufWriter, Write};
use std::path::PathBuf;

use cargo_util_schemas::core::PackageIdSpec;
use itertools::Itertools;
use serde::Serialize;

use crate::CargoResult;
use crate::util::Rustc;
use crate::util::interning::InternedString;
use crate::workspace::TargetKind;

use super::{BuildRunner, CompileMode, Unit};

/// Typed version of a SBOM format version number.
#[derive(Serialize, Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct SbomFormatVersion(u32);

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
enum SbomDependencyType {
    /// A dependency linked to the artifact produced by this unit.
    Normal,
    /// A dependency needed to run the build for this unit (e.g. a build script or proc-macro).
    /// The dependency is not linked to the artifact produced by this unit.
    Build,
}

#[derive(Serialize, Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
struct SbomIndex(usize);

#[derive(Serialize, Clone, Debug)]
#[serde(rename_all = "snake_case")]
struct SbomDependency {
    index: SbomIndex,
    kind: SbomDependencyType,
}

#[derive(Serialize, Clone, Debug)]
#[serde(rename_all = "snake_case")]
struct SbomCrate {
    id: PackageIdSpec,
    features: Vec<String>,
    dependencies: Vec<SbomDependency>,
    kind: TargetKind,
}

impl SbomCrate {
    pub fn new(unit: &Unit) -> Self {
        let package_id = unit.pkg.package_id().to_spec();
        let features = unit.features.iter().map(|f| f.to_string()).collect_vec();
        Self {
            id: package_id,
            features,
            dependencies: Vec::new(),
            kind: unit.target.kind().clone(),
        }
    }
}

#[derive(Serialize, Clone)]
#[serde(rename_all = "snake_case")]
struct SbomRustc {
    version: String,
    wrapper: Option<PathBuf>,
    workspace_wrapper: Option<PathBuf>,
    commit_hash: Option<String>,
    host: String,
    verbose_version: String,
}

impl From<&Rustc> for SbomRustc {
    fn from(rustc: &Rustc) -> Self {
        Self {
            version: rustc.version.to_string(),
            wrapper: rustc.wrapper.clone(),
            workspace_wrapper: rustc.workspace_wrapper.clone(),
            commit_hash: rustc.commit_hash.clone(),
            host: rustc.host.to_string(),
            verbose_version: rustc.verbose_version.clone(),
        }
    }
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
pub struct Sbom {
    version: SbomFormatVersion,
    root: SbomIndex,
    crates: Vec<SbomCrate>,
    rustc: SbomRustc,
    target: InternedString,
}

/// Trust: the compiler Work's streaming writer for one Cargo-owned SBOM file.
pub(super) fn write_sbom<W: Write>(writer: W, sbom: &Sbom) -> CargoResult<()> {
    let mut writer = BufWriter::new(writer);
    serde_json::to_writer(&mut writer, sbom)?;
    writer.flush()?;
    Ok(())
}

/// Build an [`Sbom`] for the given [`Unit`].
#[tracing::instrument(skip_all)]
pub fn build_sbom(build_runner: &BuildRunner<'_, '_>, root: &Unit) -> CargoResult<Sbom> {
    let bcx = build_runner.bcx;
    let rustc: SbomRustc = bcx.rustc().into();

    let mut crates = Vec::new();
    let sbom_graph = build_sbom_graph(build_runner, root);

    // Build set of indices for each node in the graph for fast lookup.
    let indices: HashMap<&Unit, SbomIndex> = sbom_graph
        .keys()
        .enumerate()
        .map(|(i, dep)| (*dep, SbomIndex(i)))
        .collect();

    // Add a item to the crates list for each node in the graph.
    for (unit, edges) in sbom_graph {
        let mut krate = SbomCrate::new(unit);
        for (dep, kind) in edges {
            krate.dependencies.push(SbomDependency {
                index: indices[dep],
                kind: kind,
            });
        }
        crates.push(krate);
    }
    let target = match root.kind {
        super::CompileKind::Host => build_runner.bcx.host_triple(),
        super::CompileKind::Target(target) => target.rustc_target(),
    };
    Ok(Sbom {
        version: SbomFormatVersion(1),
        crates,
        root: indices[root],
        rustc,
        target,
    })
}

/// List all dependencies, including transitive ones. A dependency can also appear multiple times
/// if it's using different settings, e.g. profile, features or crate versions.
///
/// Returns a graph of dependencies.
#[tracing::instrument(skip_all)]
fn build_sbom_graph<'a>(
    build_runner: &'a BuildRunner<'_, '_>,
    root: &'a Unit,
) -> BTreeMap<&'a Unit, BTreeSet<(&'a Unit, SbomDependencyType)>> {
    tracing::trace!("building sbom graph for {}", root.pkg.package_id());

    let mut queue = Vec::new();
    let mut sbom_graph: BTreeMap<&Unit, BTreeSet<(&Unit, SbomDependencyType)>> = BTreeMap::new();
    let mut visited = HashSet::default();

    // Search to collect all dependencies of the root unit.
    queue.push((root, root, false));
    while let Some((node, parent, is_build_dep)) = queue.pop() {
        let dependencies = sbom_graph.entry(parent).or_default();
        for dep in build_runner.unit_deps(node) {
            let dep = &dep.unit;
            let (next_parent, next_is_build_dep) = if dep.mode == CompileMode::RunCustomBuild {
                // Nodes in the SBOM graph for building/running build scripts are moved on to their parent as build dependencies.
                (parent, true)
            } else {
                // Proc-macros and build scripts are marked as build dependencies.
                let dep_type = match is_build_dep || dep.target.proc_macro() {
                    false => SbomDependencyType::Normal,
                    true => SbomDependencyType::Build,
                };
                dependencies.insert((dep, dep_type));
                (dep, false)
            };
            if visited.insert(dep) {
                queue.push((dep, next_parent, next_is_build_dep));
            }
        }
    }
    sbom_graph
}

#[cfg(test)]
mod writer_tests {
    use super::*;
    use std::io;

    fn small_sbom() -> Sbom {
        Sbom {
            version: SbomFormatVersion(1),
            root: SbomIndex(0),
            crates: vec![SbomCrate {
                id: PackageIdSpec::parse("sbom-writer@0.0.0").unwrap(),
                features: Vec::new(),
                dependencies: Vec::new(),
                kind: TargetKind::Bin,
            }],
            rustc: SbomRustc {
                version: "1.101.0".into(),
                wrapper: None,
                workspace_wrapper: None,
                commit_hash: None,
                host: "fixture-host".into(),
                verbose_version: "rustc fixture\nhost: fixture-host\nrelease: 1.101.0\n".into(),
            },
            target: "fixture-host".into(),
        }
    }

    #[derive(Default)]
    struct Output {
        bytes: Vec<u8>,
        writes: usize,
        flushes: usize,
        fail_write: bool,
        fail_flush: bool,
    }

    impl Write for Output {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.writes += 1;
            if self.fail_write {
                return Err(io::Error::other("SBOM final write failed"));
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            self.flushes += 1;
            if self.fail_flush {
                return Err(io::Error::other("SBOM underlying flush failed"));
            }
            Ok(())
        }
    }

    #[test]
    fn writes_the_complete_existing_sbom_encoding() {
        let sbom = small_sbom();
        let expected = serde_json::to_vec(&sbom).unwrap();
        let mut output = Output::default();
        write_sbom(&mut output, &sbom).unwrap();
        assert_eq!(output.bytes, expected);
        assert!(output.writes > 0);
    }

    #[test]
    fn returns_the_error_when_small_sbom_fails_during_final_buffer_drain() {
        let sbom = small_sbom();
        let encoded = serde_json::to_vec(&sbom).unwrap();
        assert!(encoded.len() < BufWriter::new(Vec::<u8>::new()).capacity());
        let mut output = Output {
            fail_write: true,
            ..Output::default()
        };
        let result = write_sbom(&mut output, &sbom);
        // Serialization fits in memory; the failure must actually reach the
        // underlying writer when the helper drains its final buffer.
        assert!(output.writes > 0);
        assert!(output.bytes.is_empty());
        assert!(result.is_err(), "the final write error was discarded");
    }

    #[test]
    fn returns_the_underlying_flush_error_after_writing_the_encoding() {
        let sbom = small_sbom();
        let encoded = serde_json::to_vec(&sbom).unwrap();
        assert!(encoded.len() < BufWriter::new(Vec::<u8>::new()).capacity());
        let mut output = Output {
            fail_flush: true,
            ..Output::default()
        };
        let result = write_sbom(&mut output, &sbom);
        assert_eq!(output.bytes, encoded);
        assert!(
            output.flushes > 0,
            "the underlying flush was never attempted"
        );
        assert!(result.is_err(), "the underlying flush error was discarded");
    }
}
