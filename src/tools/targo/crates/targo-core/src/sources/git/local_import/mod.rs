//! Trust: explicit, bounded Git object DATA seeding into a fresh Cargo home.
//!
//! This does not transfer source provenance, execution, SDK or persistent custody.
//! Normal locked/offline resolution still consumes and validates the result. The
//! full-revision profile retains complete parent/tree/blob DATA and recursively
//! imports selected-tree submodules. Donor refs/configuration are not copied.
//! Ordinary exact Git sources can also recover an absent database from retained
//! checkout objects; their normal resolution and checkout semantics remain.

use crate::util::CargoResult;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use crate::util::data_structures::HashMap;
use crate::util::data_structures::HashSet;
use crate::workspace::Workspace;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use crate::workspace::{GitReference, SourceId};
use anyhow::{Context as _, bail, ensure};
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::time::Instant;

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod custody;
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(super) use custody::recover_missing_database;
#[cfg(any(target_os = "macos", target_os = "linux"))]
mod pack_stream;
#[cfg(any(target_os = "macos", target_os = "linux"))]
mod submodules;

#[cfg(any(target_os = "macos", target_os = "linux"))]
const MAX_OBJECT_BYTES: usize = 64 * 1024 * 1024;
#[cfg(any(target_os = "macos", target_os = "linux"))]
const MAX_TOTAL_BYTES: u64 = 32 * 1024 * 1024 * 1024;
#[cfg(any(target_os = "macos", target_os = "linux"))]
const MAX_OBJECTS: usize = 1_000_000;
const MAX_SOURCES: usize = 64;

/// Copy locked Git closure and stored registry DATA to an absent home under
/// original donor locks. Git export reuses the full-history importer's checked
/// object/byte limits; unrelated donor objects are not output. This profile
/// accepts sparse crates.io routing only. Normal locked/offline fetching must
/// subsequently validate all selected sources and archive checksums.
pub fn snapshot_locked_cache_data(
    ws: &Workspace<'_>,
    donor: &Path,
    registry_donor: Option<&Path>,
    object_sources: &[(url::Url, PathBuf)],
) -> CargoResult<()> {
    ensure!(
        ws.gctx().locked_flag().is_some() && ws.gctx().offline_flag().is_some(),
        "local Cargo DATA snapshot requires --locked --offline"
    );
    snapshot_locked_cache_data_workspaces(ws, &[], donor, registry_donor, object_sources)
}

/// Union actual Cargo-loaded locked graphs for a bounded DATA snapshot cohort.
/// This selects bytes only; normal owning resolution/readiness remains separate.
pub fn snapshot_locked_cache_data_workspaces(
    ws: &Workspace<'_>,
    additional_manifests: &[PathBuf],
    donor: &Path,
    registry_donor: Option<&Path>,
    object_sources: &[(url::Url, PathBuf)],
) -> CargoResult<()> {
    ensure!(
        ws.gctx().locked_flag().is_some() && ws.gctx().offline_flag().is_some(),
        "local Cargo DATA snapshot requires --locked --offline"
    );
    ensure!(
        additional_manifests.len() < MAX_SOURCES,
        "too many local Cargo DATA workspace inputs"
    );
    let mut resolves = vec![
        crate::ops::load_pkg_lockfile(ws)?
            .context("local Cargo DATA snapshot requires an existing Cargo.lock")?,
    ];
    for manifest in additional_manifests {
        ensure!(
            manifest.is_absolute(),
            "local Cargo DATA manifest must be absolute"
        );
        let additional = Workspace::new(manifest, ws.gctx())?;
        resolves.push(
            crate::ops::load_pkg_lockfile(&additional)?
                .context("additional local Cargo DATA workspace requires existing Cargo.lock")?,
        );
    }
    ensure!(resolves.iter().flat_map(|resolve| resolve.iter()).all(|package| !package.source_id().is_registry() || package.source_id().is_crates_io()),
        "local Cargo DATA snapshot supports only the configured sparse crates.io registry");
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let registry = if resolves
            .iter()
            .flat_map(|resolve| resolve.iter())
            .any(|package| package.source_id().is_registry())
        {
            let selected = SourceId::crates_io_maybe_sparse_http(ws.gctx())?;
            ensure!(
                selected.is_sparse() && selected.is_crates_io(),
                "local Cargo DATA snapshot requires configured sparse crates.io"
            );
            Some(crate::sources::registry::short_name(selected, false))
        } else {
            None
        };
        let sources = resolves
            .iter()
            .flat_map(|resolve| resolve.iter())
            .map(|package| package.source_id())
            .filter(|source| source.is_git())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        let stats = custody::snapshot::import_selected(
            donor,
            ws.gctx().home().as_path_unlocked(),
            registry.as_deref(),
            registry_donor,
            sources,
            object_sources,
        )?;
        ws.gctx().shell().status("Copied", format!(
            "{} cache DATA files, {} stored bytes (cloned {}, streamed {}), plus {} selected checkout files/{} expanded bytes (cloned {}, streamed {}); {} stored namespace entries and {} expanded namespace entries; locked offline resolution still required",
            stats.files, stats.bytes, stats.cloned_bytes, stats.streamed_bytes,
            stats.checkout_files, stats.checkout_bytes, stats.checkout_cloned_bytes, stats.checkout_streamed_bytes,
            stats.stored_entries, stats.checkout_entries))?;
        Ok(())
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (donor, registry_donor);
        bail!("local Cargo DATA snapshot is supported only on native macOS/Linux")
    }
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
const MAX_SOURCE_URL_BYTES: usize = 8192;

/// Seed only the Git sources named by the existing lockfile, then let ordinary
/// `fetch --locked --offline` validate the dependency graph. The destination home
/// must not exist. Pre-commit refusal retains a marked partial sibling. A later
/// observation/durability error explicitly reports that publication already occurred.
/// No helper process is spawned by the import.
pub fn import_locked_source_data(
    ws: &Workspace<'_>,
    donor: Option<&Path>,
    object_sources: &[(url::Url, PathBuf)],
    copy_limit: Option<u64>,
    preflight: bool,
) -> CargoResult<()> {
    ensure!(
        ws.gctx().locked_flag().is_some() && ws.gctx().offline_flag().is_some(),
        "local Git source-data import requires --locked --offline"
    );
    let resolve = crate::ops::load_pkg_lockfile(ws)?
        .context("local Git source-data import requires an existing Cargo.lock")?;
    let sources = resolve
        .iter()
        .map(|package| package.source_id())
        .filter(|source| source.is_git())
        .collect::<HashSet<_>>();
    ensure!(!sources.is_empty(), "Cargo.lock names no Git source inputs");
    ensure!(
        sources.len() <= MAX_SOURCES,
        "too many locked Git source inputs"
    );
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let started = Instant::now();
        let destination = ws.gctx().home().as_path_unlocked();
        let (stats, requirements) = inspect_sources(
            donor,
            object_sources,
            destination,
            sources.into_iter().collect(),
            copy_limit.unwrap_or(MAX_TOTAL_BYTES),
            preflight,
        )?;
        if preflight {
            use std::io::Write as _;
            let mut out = std::io::stdout().lock();
            serde_json::to_writer(
                &mut out,
                &serde_json::json!({
                    "schema":"targo-git-source-preflight-v1",
                    "scope":"observed-locked-source-data-closure",
                    "destination_published":false,
                    "private_views":"closed",
                    "observed_counts":stats,
                    "required_sources":requirements,
                }),
            )?;
            writeln!(out)?;
            out.flush()?;
            return Ok(());
        }
        ws.gctx().shell().status(
            "Imported",
            format!(
                "{} locked Git sources, {} objects, {} uncompressed bytes in {:.2}s (source data only; native clones: {} files/{} bytes, streamed: {} bytes)",
                stats.sources, stats.objects, stats.bytes, started.elapsed().as_secs_f64(),
                stats.cloned_files, stats.cloned_bytes, stats.streamed_bytes
            ),
        )?;
        Ok(())
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (donor, object_sources, copy_limit, preflight);
        bail!("local Git source-data import is supported only on native macOS/Linux")
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[derive(Debug, Default, serde::Serialize)]
struct Stats {
    sources: usize,
    objects: usize,
    bytes: u64,
    view_bytes: u64,
    cloned_files: u64,
    cloned_bytes: u64,
    streamed_bytes: u64,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn locked_oid(source: SourceId) -> CargoResult<git2::Oid> {
    ensure!(
        source.url().as_str().len() <= MAX_SOURCE_URL_BYTES,
        "Git source URL exceeds its bound"
    );
    let precise = source
        .precise_git_fragment()
        .context("Git source has no locked OID")?;
    ensure!(
        precise.len() == 40
            && precise
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "local Git source import requires a full lowercase locked OID"
    );
    Ok(precise.parse()?)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn precise_oid(source: SourceId) -> CargoResult<git2::Oid> {
    let oid = locked_oid(source)?;
    let precise = source
        .precise_git_fragment()
        .context("Git source has no locked OID")?;
    ensure!(
        matches!(source.git_reference(), Some(GitReference::Rev(rev)) if rev == precise),
        "local Git source import currently requires an exact full-revision manifest source"
    );
    Ok(oid)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
struct Database {
    representative: SourceId,
    input: git2::Repository,
    output: Option<git2::Repository>,
    view: custody::OwnedView,
    original: custody::ObjectSource,
    copied: HashMap<git2::Oid, git2::ObjectType>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
enum Work {
    Enter(submodules::Source),
    Exit((SourceId, String)),
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn inspect_sources(
    donor: Option<&Path>,
    object_sources: &[(url::Url, PathBuf)],
    destination: &Path,
    mut sources: Vec<SourceId>,
    copy_limit: u64,
    preflight: bool,
) -> CargoResult<(Stats, Vec<serde_json::Value>)> {
    let mut copy_budget = custody::CopyBudget::new(copy_limit)?;
    ensure!(
        object_sources.len() <= MAX_SOURCES,
        "too many object-directory selectors"
    );
    ensure!(
        donor.is_some() || !object_sources.is_empty(),
        "no source-data input provided"
    );
    let mut objects = BTreeMap::new();
    for (url, path) in object_sources {
        ensure!(
            url.as_str().len() <= MAX_SOURCE_URL_BYTES,
            "Git source URL exceeds its bound"
        );
        let key = crate::util::CanonicalUrl::new(url)?;
        ensure!(
            path.is_absolute() && path.canonicalize()? == *path,
            "source object directory must be absolute and canonical"
        );
        ensure!(
            objects.insert(key, path).is_none(),
            "duplicate canonical object-directory URL selector"
        );
    }
    let mut used_objects = HashSet::default();
    ensure!(
        sources.len() <= MAX_SOURCES,
        "too many locked Git source inputs"
    );
    for source in &sources {
        precise_oid(*source)?;
    }
    sources.sort_by_cached_key(|source| source.to_string());
    let mut pending = sources
        .into_iter()
        .rev()
        .map(|id| {
            Work::Enter(submodules::Source {
                id,
                parent_url: id.url().to_string(),
            })
        })
        .collect::<Vec<_>>();
    let mut traversal = submodules::Traversal::default();
    let mut databases = BTreeMap::<String, Database>::new();
    let source_guard = donor.map(custody::Cache::source).transpose()?;
    let paths = donor
        .into_iter()
        .chain(objects.values().map(|path| path.as_path()))
        .collect::<Vec<_>>();
    let mut stage = custody::Stage::new(destination, &paths)?;
    let mut stats = Stats::default();
    let mut pack_reads = pack_stream::ReadBudget::default();
    let mut requirements = Vec::new();
    while let Some(work) = pending.pop() {
        let source = match work {
            Work::Exit(key) => {
                traversal.finish(key)?;
                continue;
            }
            Work::Enter(source) => source,
        };
        let key = (source.id, source.parent_url.clone());
        if !traversal.enter(&key)? {
            continue;
        }
        let revision = precise_oid(source.id)?;
        let ident = super::source::ident(&source.id);
        if !databases.contains_key(&ident) {
            let (snapshot, object_path) = if let Some(path) = objects.get(source.id.canonical_url())
            {
                used_objects.insert(source.id.canonical_url().clone());
                (
                    custody::ObjectSource::capture_objects(path)
                        .context("explicit Git object DATA unavailable")
                        .with_context(|| {
                            super::source::object_source_context(source.id, revision)
                        })?,
                    (*path).clone(),
                )
            } else {
                let repository = donor.context("selected Git source has no object-directory selector or Cargo cache fallback")?.join("git/db").join(&ident);
                (
                    custody::ObjectSource::capture(&repository)
                        .context("locked Git source-data database unavailable")
                        .with_context(|| {
                            super::source::object_source_context(source.id, revision)
                        })?,
                    repository.join("objects"),
                )
            };
            // Git opens only this private object-data view. Source files were opened
            // relative to their actual retained directory handles; no donor config,
            // alternate, graft, ref or path-selected backend reaches libgit2.
            let mut view = stage.create_view(&ident)?;
            let view_stats = snapshot
                .materialize_view(
                    &object_path,
                    &mut view,
                    MAX_TOTAL_BYTES - stats.view_bytes,
                    &mut copy_budget,
                )
                .with_context(|| super::source::object_source_context(source.id, revision))?;
            stats.view_bytes += view_stats.bytes;
            stats.cloned_files += view_stats.cloned_files;
            stats.cloned_bytes += view_stats.cloned_bytes;
            stats.streamed_bytes += view_stats.streamed_bytes;
            let input = git2::Odb::new()?;
            input.add_disk_alternate(
                view.path()
                    .to_str()
                    .context("private object-data view must be UTF-8")?,
            )?;
            let input = git2::Repository::from_odb(input)?;
            let output = if preflight {
                None
            } else {
                let output_path = stage.path().join("git/db").join(&ident);
                stage.validate_namespace()?;
                std::fs::create_dir_all(output_path.parent().expect("Git database parent"))?;
                let mut options = git2::RepositoryInitOptions::new();
                options
                    .bare(true)
                    .external_template(false)
                    .initial_head("master");
                let output = git2::Repository::init_opts(&output_path, &options)?;
                output.set_config(&git2::Config::new()?)?;
                Some(output)
            };
            databases.insert(
                ident.clone(),
                Database {
                    representative: source.id,
                    input,
                    output,
                    view,
                    original: snapshot,
                    copied: HashMap::default(),
                },
            );
            stats.sources += 1;
        }
        let database = databases.get_mut(&ident).expect("inserted source database");
        ensure!(
            database.representative.canonical_url() == source.id.canonical_url(),
            "source cache identifier collision"
        );
        stage.validate_namespace()?;
        database.original.check_current()?;
        database.view.check_current()?;
        inspect_closure(database, revision, &mut stats, &mut pack_reads)
            .with_context(|| super::source::object_source_context(source.id, revision))?;
        if let Some(output) = &database.output
            && output
                .find_reference(&format!("refs/commit/{revision}"))
                .is_err()
        {
            // Derive the precise-fetch ref from the locked input, not donor refs.
            output.reference(
                &format!("refs/commit/{revision}"),
                revision,
                false,
                "locked source data import",
            )?;
        }
        let children = submodules::selected(&database.input, revision, &source.parent_url)
            .with_context(|| super::source::object_source_context(source.id, revision))?;
        requirements.push(serde_json::json!({
            "cache_ident":ident,
            "display_url":display_url(source.id.url())?,
            "revision":revision.to_string(),
            "children":children.iter().map(|child| source_requirement(child.id)).collect::<CargoResult<Vec<_>>>()?,
        }));
        database.original.check_current()?;
        database.view.check_current()?;
        if let Some(guard) = &source_guard {
            guard.check_current()?;
        }
        ensure!(
            pending.len() + children.len() < MAX_SOURCES * 2,
            "submodule pending work bound exceeded"
        );
        pending.push(Work::Exit(key));
        pending.extend(children.into_iter().rev().map(Work::Enter));
    }
    for database in databases.values() {
        database.original.check_current()?;
        database.view.check_current()?;
    }
    ensure!(
        used_objects.len() == objects.len(),
        "unused object-directory URL selector"
    );
    if let Some(guard) = &source_guard {
        guard.check_current()?;
    }
    if preflight {
        let mut views = Vec::new();
        let mut originals = Vec::new();
        for database in databases.into_values() {
            let Database {
                input,
                output,
                original,
                view,
                ..
            } = database;
            // Destroy every actual ODB owner before finishing owned views.
            drop(input);
            drop(output);
            originals.push(original);
            views.push(view);
        }
        for original in &originals {
            original.check_current()?;
        }
        for view in &views {
            view.check_current()?;
        }
        if let Some(guard) = &source_guard {
            guard.check_current()?;
        }
        stage.finish_preflight(&mut views)?;
    } else {
        stage.publish()?;
    }
    Ok((stats, requirements))
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn display_url(url: &url::Url) -> CargoResult<String> {
    let mut display = url.clone();
    if display.password().is_some() {
        display
            .set_password(None)
            .map_err(|_| anyhow::anyhow!("cannot redact source URL"))?;
    }
    if !display.username().is_empty() {
        display
            .set_username("")
            .map_err(|_| anyhow::anyhow!("cannot redact source URL"))?;
    }
    Ok(display.to_string())
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn source_requirement(source: SourceId) -> CargoResult<serde_json::Value> {
    Ok(
        serde_json::json!({"cache_ident":super::source::ident(&source), "display_url":display_url(source.url())?, "revision":precise_oid(source)?.to_string()}),
    )
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
fn import_with_budget(
    donor: Option<&Path>,
    object_sources: &[(url::Url, PathBuf)],
    destination: &Path,
    sources: Vec<SourceId>,
    copy_limit: u64,
) -> CargoResult<Stats> {
    inspect_sources(
        donor,
        object_sources,
        destination,
        sources,
        copy_limit,
        false,
    )
    .map(|(stats, _)| stats)
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
fn import_sources(
    donor: Option<&Path>,
    object_sources: &[(url::Url, PathBuf)],
    destination: &Path,
    sources: Vec<SourceId>,
) -> CargoResult<Stats> {
    import_with_budget(donor, object_sources, destination, sources, MAX_TOTAL_BYTES)
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
fn import(donor: &Path, destination: &Path, sources: Vec<SourceId>) -> CargoResult<Stats> {
    import_sources(Some(donor), &[], destination, sources)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn inspect_closure(
    database: &mut Database,
    revision: git2::Oid,
    stats: &mut Stats,
    pack_reads: &mut pack_stream::ReadBudget,
) -> CargoResult<()> {
    inspect_closure_scope(database, revision, stats, pack_reads, true)
}

// Trust: recovery retains original ancestry metadata and the selected tree,
// without promoting selected source DATA to complete historical source.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn inspect_closure_scope(
    database: &mut Database,
    revision: git2::Oid,
    stats: &mut Stats,
    pack_reads: &mut pack_stream::ReadBudget,
    historical_trees: bool,
) -> CargoResult<()> {
    inspect_closure_objects(
        database,
        revision,
        stats,
        pack_reads,
        historical_trees,
        true,
    )
}

// Trust: the selected snapshot packs the bounded ordinary objects with native
// libgit2 after this SAME hash/closure walk. Oversized blobs keep the existing
// streaming writer; they never enter the pack builder's in-memory body path.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn inspect_closure_for_pack(
    database: &mut Database,
    revision: git2::Oid,
    stats: &mut Stats,
    pack_reads: &mut pack_stream::ReadBudget,
) -> CargoResult<()> {
    inspect_closure_objects(database, revision, stats, pack_reads, true, false)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn inspect_closure_objects(
    database: &mut Database,
    revision: git2::Oid,
    stats: &mut Stats,
    pack_reads: &mut pack_stream::ReadBudget,
    historical_trees: bool,
    write_ordinary: bool,
) -> CargoResult<()> {
    let input = &database.input;
    let source = input.odb()?;
    let sink = database
        .output
        .as_ref()
        .map(git2::Repository::odb)
        .transpose()?;
    let mut pending = vec![(revision, git2::ObjectType::Commit)];
    while let Some((oid, expected)) = pending.pop() {
        if let Some(previous) = database.copied.insert(oid, expected) {
            ensure!(
                previous == expected,
                "conflicting Git object types in source closure"
            );
            continue;
        }
        ensure!(
            stats.objects < MAX_OBJECTS,
            "Git source closure exceeds object bound"
        );
        let (bytes, kind) = source
            .read_header(oid)
            .with_context(|| format!("missing locked Git object {oid}"))?;
        ensure!(
            kind == expected,
            "locked Git object has unexpected type: {oid}"
        );
        let next_bytes = stats
            .bytes
            .checked_add(bytes as u64)
            .context("Git source byte count overflow")?;
        ensure!(
            next_bytes <= MAX_TOTAL_BYTES,
            "Git source closure exceeds 32 GiB for provider {} at locked revision {revision} \
             after verifying {} objects and {} logical bytes across providers. \
             Next object {oid} declares {bytes} logical bytes",
            crate::util::hex::short_hash(database.representative.canonical_url()),
            stats.objects,
            stats.bytes
        );
        if bytes > MAX_OBJECT_BYTES {
            ensure!(
                expected == git2::ObjectType::Blob,
                "Git source object exceeds 64 MiB: {oid}"
            );
            pack_stream::verify(&database.view, sink.as_ref(), oid, bytes, pack_reads)?;
        } else {
            let object = source.read(oid)?;
            ensure!(
                object.kind() == expected && object.data().len() == bytes,
                "Git source object changed: {oid}"
            );
            ensure!(
                git2::Oid::hash_object(expected, object.data())? == oid,
                "corrupt locked Git object: {oid}"
            );
            if write_ordinary && let Some(sink) = &sink {
                ensure!(
                    sink.write(expected, object.data())? == oid,
                    "Git source object write disagrees: {oid}"
                );
            }
        }
        stats.objects += 1;
        stats.bytes = next_bytes;
        match expected {
            git2::ObjectType::Commit => {
                let commit = input.find_commit(oid)?;
                ensure!(
                    pending.len() < MAX_OBJECTS,
                    "Git source edge bound exceeded"
                );
                if historical_trees || oid == revision {
                    pending.push((commit.tree_id(), git2::ObjectType::Tree));
                }
                for parent in commit.parent_ids() {
                    ensure!(
                        pending.len() < MAX_OBJECTS,
                        "Git source edge bound exceeded"
                    );
                    pending.push((parent, git2::ObjectType::Commit));
                }
            }
            git2::ObjectType::Tree => {
                for entry in input.find_tree(oid)?.iter() {
                    ensure!(
                        pending.len() < MAX_OBJECTS,
                        "Git source edge bound exceeded"
                    );
                    match entry.filemode() {
                        0o040000 => pending.push((entry.id(), git2::ObjectType::Tree)),
                        0o100644 | 0o100755 | 0o120000 => {
                            pending.push((entry.id(), git2::ObjectType::Blob))
                        }
                        // A gitlink is DATA inside this tree, not an object in
                        // this ODB. Only selected() derives child source recipes.
                        0o160000 => {}
                        _ => bail!("unsupported Git tree mode in locked source closure"),
                    }
                }
            }
            git2::ObjectType::Blob => {}
            _ => bail!("unsupported locked Git object type"),
        }
    }
    Ok(())
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod tests;
