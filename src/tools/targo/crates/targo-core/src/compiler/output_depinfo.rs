//! dep-info files for external build system integration.
//! See [`output_depinfo`] for more.

use crate::util::data_structures::HashSet;
use cargo_util::paths::normalize_path;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};

use super::{BuildRunner, FileFlavor, Unit, fingerprint};
use crate::util::{CargoResult, internal};
use cargo_util::paths;
use tracing::debug;

/// Basically just normalizes a given path and converts it to a string.
fn render_filename<P: AsRef<Path>>(path: P, basedir: Option<&str>) -> CargoResult<String> {
    fn wrap_path(path: &Path) -> CargoResult<String> {
        path.to_str()
            .ok_or_else(|| internal(format!("path `{:?}` not utf-8", path)))
            .map(|f| f.replace(" ", "\\ "))
    }

    let path = path.as_ref();
    if let Some(basedir) = basedir {
        let norm_path = normalize_path(path);
        let norm_basedir = normalize_path(basedir.as_ref());
        match norm_path.strip_prefix(norm_basedir) {
            Ok(relpath) => wrap_path(relpath),
            _ => wrap_path(path),
        }
    } else {
        wrap_path(path)
    }
}

// Trust: avoid ordered comparisons on every repeated transitive path. HashSet
// retains the first equal PathBuf representative, like BTreeSet; sort with the
// same PathBuf ordering before rendering or escaping any dependency filename.
fn sorted_dependency_paths(paths: HashSet<PathBuf>) -> Vec<PathBuf> {
    let mut paths: Vec<_> = paths.into_iter().collect();
    paths.sort_unstable();
    paths
}

/// Collects all dependencies of the `unit` for the output dep info file.
///
/// Dependencies will be stored in `deps`, including:
///
/// * dependencies from [fingerprint dep-info]
/// * paths from `rerun-if-changed` build script instruction
/// * ...and traverse transitive dependencies recursively
///
/// [fingerprint dep-info]: super::fingerprint#fingerprint-dep-info-files
fn add_deps_for_unit(
    deps: &mut HashSet<PathBuf>,
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    visited: &mut HashSet<Unit>,
) -> CargoResult<()> {
    if !visited.insert(unit.clone()) {
        return Ok(());
    }

    // units representing the execution of a build script don't actually
    // generate a dep info file, so we just keep on going below
    if !unit.mode.is_run_custom_build() {
        // Add dependencies from rustc dep-info output (stored in fingerprint directory)
        let dep_info_loc = fingerprint::dep_info_loc(build_runner, unit);
        match fingerprint::parse_dep_info(
            unit.pkg.root(),
            build_runner.files().host_build_root(),
            build_runner.bcx.ws.root(),
            &dep_info_loc,
            // Trust: expand EW-9 relocation root tokens with the current roots.
            build_runner
                .bcx
                .gctx
                .cli_unstable()
                .trust_relocation_roots
                .as_ref(),
        ) {
            Ok(paths) => {
                for path in paths.files.into_keys() {
                    deps.insert(path);
                }
            }
            Err(reason) => {
                debug!(
                    "can't use dep_info for {:?} {}: {}",
                    unit.pkg.package_id(),
                    unit.target,
                    reason
                );
                return Err(internal(format!("dep_info unavailable: {reason}")));
            }
        }
    }

    // Add rerun-if-changed dependencies
    if let Some(metadata_vec) = build_runner.find_build_script_metadatas(unit) {
        for metadata in metadata_vec {
            if let Some(output) = build_runner
                .build_script_outputs
                .lock()
                .unwrap()
                .get(metadata)
            {
                for path in &output.rerun_if_changed {
                    let package_root = unit.pkg.root();

                    let path = if path.as_os_str().is_empty() {
                        // Joining with an empty path causes Rust to add a trailing path separator.
                        // On Windows, this would add an invalid trailing backslash to the .d file.
                        package_root.to_path_buf()
                    } else {
                        // The paths we have saved from the unit are of arbitrary relativeness and
                        // may be relative to the crate root of the dependency.
                        package_root.join(path)
                    };

                    deps.insert(path);
                }
            }
        }
    }

    // Recursively traverse all transitive dependencies
    let unit_deps = Vec::from(build_runner.unit_deps(unit)); // Create vec due to mutable borrow.
    for dep in unit_deps {
        if dep.unit.is_local() {
            add_deps_for_unit(deps, build_runner, &dep.unit, visited)?;
        }
    }
    Ok(())
}

/// Save a `.d` dep-info file for the given unit. This is the third kind of
/// dep-info mentioned in [`fingerprint`] module.
///
/// Argument `unit` is expected to be the root unit, which will be uplifted.
///
/// Cargo emits its own dep-info files in the output directory. This is
/// only done for every "uplifted" artifact. These are intended to be used
/// with external build systems so that they can detect if Cargo needs to be
/// re-executed.
///
/// It includes all the entries from the `rustc` dep-info file, and extends it
/// with any `rerun-if-changed` entries from build scripts. It also includes
/// sources from any path dependencies. Registry dependencies are not included
/// under the assumption that changes to them can be detected via changes to
/// `Cargo.lock`.
///
/// [`fingerprint`]: super::fingerprint#dep-info-files
pub fn output_depinfo(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<()> {
    let bcx = build_runner.bcx;
    // Trust: keep configuration validation even when there is no uplifted output.
    let basedir_string;
    let basedir = match bcx.gctx.build_config()?.dep_info_basedir.clone() {
        Some(value) => {
            basedir_string = value
                .resolve_path(bcx.gctx)
                .as_os_str()
                .to_str()
                .ok_or_else(|| anyhow::format_err!("build.dep-info-basedir path not utf-8"))?
                .to_string();
            Some(basedir_string.as_str())
        }
        None => None,
    };

    // Trust: checks and tests have no uplifted outputs. Find all destinations
    // before reading and sorting the transitive dependency files for this root.
    let outputs = build_runner.outputs(unit)?;
    let destinations = outputs
        .iter()
        .filter(|o| {
            !matches!(
                o.flavor,
                FileFlavor::DebugInfo
                    | FileFlavor::Auxiliary
                    | FileFlavor::Sbom
                    | FileFlavor::Unremap
            )
        })
        .filter_map(|output| output.hardlink.as_ref())
        .collect::<Vec<_>>();
    if destinations.is_empty() {
        return Ok(());
    }

    let mut deps = HashSet::default();
    let mut visited = HashSet::default();
    let success = add_deps_for_unit(&mut deps, build_runner, unit, &mut visited).is_ok();
    let deps = sorted_dependency_paths(deps);
    let deps = deps
        .iter()
        .map(|f| render_filename(f, basedir))
        .collect::<CargoResult<Vec<_>>>()?;

    for link_dst in destinations {
        let output_path = link_dst.with_extension("d");
        if success {
            let target_fn = render_filename(link_dst, basedir)?;

            // If nothing changed don't recreate the file which could alter
            // its mtime
            if let Ok(previous) = fingerprint::parse_rustc_dep_info(&output_path) {
                if previous
                    .files
                    .iter()
                    .map(|(path, _checksum)| path)
                    .eq(deps.iter().map(Path::new))
                {
                    continue;
                }
            }

            // Otherwise write it all out
            let mut outfile = BufWriter::new(paths::create(output_path)?);
            write!(outfile, "{}:", target_fn)?;
            for dep in &deps {
                write!(outfile, " {}", dep)?;
            }
            writeln!(outfile)?;

        // dep-info generation failed, so delete output file. This will
        // usually cause the build system to always rerun the build
        // rule, which is correct if inefficient.
        } else if output_path.exists() {
            paths::remove_file(output_path)?;
        }
    }
    Ok(())
}

// Trust: differential controls retain the old collection's observable bytes,
// including the first spelling of component-equal paths and error prefixes.
#[cfg(test)]
mod tests {
    use super::{HashSet, Path, PathBuf, render_filename, sorted_dependency_paths};
    use std::collections::BTreeSet;
    use std::ffi::OsString;

    fn collect_paths(paths: &[PathBuf]) -> Vec<PathBuf> {
        let mut collected = HashSet::default();
        for path in paths {
            collected.insert(path.clone());
        }
        sorted_dependency_paths(collected)
    }

    fn raw_paths(paths: impl IntoIterator<Item = PathBuf>) -> Vec<OsString> {
        paths.into_iter().map(PathBuf::into_os_string).collect()
    }

    fn legacy_paths(paths: &[PathBuf]) -> Vec<OsString> {
        let mut collected = BTreeSet::new();
        for path in paths {
            collected.insert(path.clone());
        }
        raw_paths(collected)
    }

    #[test]
    fn first_component_equal_path_spelling_matches_legacy() {
        let mut paths: Vec<_> = [
            "shared//./leaf file",
            "z-last",
            "shared/leaf file",
            "a-first",
            "shared/leaf file/",
            "shared/../different",
            "",
            ".",
        ]
        .into_iter()
        .map(PathBuf::from)
        .collect();
        assert_eq!(paths[0], paths[2]);
        assert_ne!(paths[0].as_os_str(), paths[2].as_os_str());
        for _ in 0..paths.len() {
            let first = paths
                .iter()
                .find(|path| **path == Path::new("shared/leaf file"))
                .unwrap();
            let actual = collect_paths(&paths);
            assert_eq!(raw_paths(actual.clone()), legacy_paths(&paths));
            let retained = actual
                .iter()
                .find(|path| **path == Path::new("shared/leaf file"))
                .unwrap();
            assert_eq!(retained.as_os_str(), first.as_os_str());
            paths.rotate_left(1);
        }
    }

    #[test]
    fn path_order_precedes_space_escaping() {
        let paths = [PathBuf::from("a!b"), PathBuf::from("a b")];
        let rendered: Vec<_> = collect_paths(&paths)
            .iter()
            .map(|path| render_filename(path, None).unwrap())
            .collect();
        assert_eq!(rendered, ["a\\ b", "a!b"]);
        assert!(rendered[0] > rendered[1]);
    }

    #[test]
    fn basedir_normalization_does_not_replace_raw_representative() {
        let original = PathBuf::from("workspace")
            .join("src")
            .join(".")
            .join("leaf file");
        let alias = PathBuf::from("workspace").join("src").join("leaf file");
        assert_eq!(original, alias);
        assert_ne!(original.as_os_str(), alias.as_os_str());
        let paths = collect_paths(&[original.clone(), alias]);
        assert_eq!(raw_paths(paths.clone()), [original.into_os_string()]);
        assert_eq!(
            render_filename(&paths[0], Some("workspace")).unwrap(),
            format!("src{}leaf\\ file", std::path::MAIN_SEPARATOR),
        );
    }

    #[test]
    fn repeated_shared_paths_and_partial_prefixes_match_legacy() {
        let paths: Vec<_> = (0..4096)
            .map(|i| {
                let leaf = (i * 73) % 509;
                if i % 3 == 0 {
                    PathBuf::from(format!(
                        "workspace/shared/long prefix/group{}/./leaf{leaf}.rs",
                        leaf % 17
                    ))
                } else {
                    PathBuf::from(format!(
                        "workspace/shared/long prefix/group{}/leaf{leaf}.rs",
                        leaf % 17
                    ))
                }
            })
            .collect();
        for prefix in [0, 1, 2, 17, 508, 509, 510, 1024, 4096] {
            assert_eq!(
                raw_paths(collect_paths(&paths[..prefix])),
                legacy_paths(&paths[..prefix])
            );
        }
        let reversed: Vec<_> = paths.into_iter().rev().collect();
        assert_eq!(raw_paths(collect_paths(&reversed)), legacy_paths(&reversed));
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_dependency_is_retained_and_rendering_still_errors() {
        use std::os::unix::ffi::OsStringExt;
        let invalid = PathBuf::from(OsString::from_vec(vec![b'd', b'e', b'p', 0xff]));
        let input = [PathBuf::from("good dependency"), invalid.clone(), invalid];
        let actual = collect_paths(&input);
        assert_eq!(raw_paths(actual.clone()), legacy_paths(&input));
        let rendered = actual
            .iter()
            .map(|path| render_filename(path, None))
            .collect::<crate::util::CargoResult<Vec<_>>>();
        assert!(rendered.unwrap_err().to_string().contains("not utf-8"));
    }
}
