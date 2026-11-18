//! Trust: selected locked object storage DATA, never provenance or readiness.
//! Reuse the original view factory, complete checked closure exporter and
//! selected-tree submodule traversal. Unreachable donor storage is not output.
use super::super::super::{
    Database as SourceDatabase, Stats as SourceStats, Work, inspect_closure_for_pack, locked_oid,
    pack_stream, submodules,
};
use super::*;
use crate::workspace::SourceId;

pub(super) type Database = SourceDatabase;

impl Output {
    // Only this original private factory creates the output namespace. libgit2
    // gets a fresh native streaming writer for oversized blobs, never donor
    // configuration or backends. Ordinary objects are packed separately.
    fn object_database(
        &mut self,
        prefix: &Path,
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<git2::Repository> {
        let objects = prefix.join("objects");
        self.directory(&objects.join("info"))?;
        self.directory(&objects.join("pack"))?;
        self.directory(&prefix.join("refs"))?;
        self.generated(
            &prefix.join("config"),
            b"[core]\nrepositoryformatversion = 0\nbare = true\n",
            stats,
            budget,
        )?;
        self.generated(
            &prefix.join("HEAD"),
            b"ref: refs/heads/master\n",
            stats,
            budget,
        )?;
        let mut repository = None;
        self.with_directory(prefix, |directory| {
            let output = git2::Repository::open_bare(&directory.path)?;
            output.set_config(&git2::Config::new()?)?;
            repository = Some(output);
            Ok(())
        })?;
        repository.context("fresh selected object database unavailable")
    }

    fn pack_objects(&self, prefix: &Path, database: &Database) -> CargoResult<()> {
        database.original.check_current()?;
        database.view.check_current()?;
        let objects = database.input.odb()?;
        let mut pack = database.input.packbuilder()?;
        pack.set_threads(1);
        let mut count = 0;
        for (oid, expected) in &database.copied {
            let (size, kind) = objects.read_header(*oid)?;
            ensure!(kind == *expected, "verified selected object type changed");
            if size <= super::super::super::MAX_OBJECT_BYTES {
                // Single-object insertion cannot widen this checked set through
                // donor refs, orphan roots or recursive native tree traversal.
                pack.insert_object(*oid, None)?;
                count += 1;
            }
        }
        ensure!(pack.object_count() == count, "native selected pack widened");
        if count != 0 {
            self.with_directory(&prefix.join("objects/pack"), |directory| {
                pack.write(&directory.path, 0o600)?;
                Ok(())
            })?;
        }
        database.view.check_current()?;
        database.original.check_current()
    }

    // Called only after destroying the actual native writer. Retain the same
    // original factory directory FD, then seal every generated object name and
    // inode through the existing sticky Tree bookends. This is not owner
    // reconstruction from an input path or a persisted receipt.
    fn finish_objects(
        &mut self,
        prefix: &Path,
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<Tree> {
        let mut stored = None;
        self.with_directory(&prefix.join("objects"), |directory| {
            let file = directory.file.try_clone()?;
            let before = file.metadata()?;
            stored = Some(Tree::capture(Directory {
                path: directory.path.clone(),
                file,
                before,
            })?);
            Ok(())
        })?;
        let stored = stored.context("generated selected objects unavailable")?;
        for path in stored.source.directories.keys() {
            let relative = path.strip_prefix(&self.root.path)?;
            if !self.directories.contains_key(relative) {
                self.entries.reserve(relative)?;
            }
        }
        for (path, metadata) in &stored.source.files {
            ensure!(
                DataKind::Objects.accepts(path.strip_prefix(&stored.source.root.path)?),
                "unsupported generated Git object layout"
            );
            self.entries.reserve(path.strip_prefix(&self.root.path)?)?;
            let next = stats
                .bytes
                .checked_add(metadata.len())
                .context("stored selected object byte overflow")?;
            ensure!(
                next <= super::super::super::MAX_TOTAL_BYTES,
                "stored DATA exceeds 32 GiB"
            );
            budget.reserve(metadata.len())?;
            stats.bytes = next;
            stats.streamed_bytes += metadata.len();
            stats.files += 1;
            stored.source.with_directory(
                path.parent()
                    .context("generated object parent unavailable")?,
                |directory| {
                    let file = File::from(rustix::fs::openat(
                        &directory.file,
                        path.file_name()
                            .context("generated object leaf unavailable")?,
                        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                        Mode::empty(),
                    )?);
                    stored.source.observe(|| {
                        ensure!(
                            stamp(metadata, &file.metadata()?),
                            "generated object changed before sync"
                        );
                        file.sync_all()?;
                        ensure!(
                            stamp(metadata, &file.metadata()?),
                            "generated object changed during sync"
                        );
                        Ok(())
                    })
                },
            )?;
        }
        for path in stored.source.directories.keys().rev() {
            stored.source.with_directory(path, |directory| {
                directory.file.sync_all()?;
                Ok(())
            })?;
        }
        stored.source.check_current()?;
        Ok(stored)
    }
}

pub(in super::super::super) fn import_selected(
    donor: &Path,
    destination: &Path,
    registry: Option<&str>,
    registry_donor: Option<&Path>,
    sources: Vec<SourceId>,
    object_sources: &[(url::Url, PathBuf)],
) -> CargoResult<Stats> {
    prepare_selected_git(
        donor,
        destination,
        registry,
        registry_donor,
        sources,
        object_sources,
    )?
    .publish()
}

// Trust: completed Git DATA retains every original guard through publication.
// The registry directory is original DATA custody only until its own phase
// acquires locks. This object supplies neither provenance nor readiness.
pub(super) struct PreparedGitData {
    cache: Cache,
    registry_name: Option<String>,
    registry_home: Option<Directory>,
    stage: Stage,
    output: Output,
    stats: Stats,
    budget: CopyBudget,
    originals: Vec<ObjectSource>,
    stored_objects: Vec<Tree>,
    checkouts: Vec<checkout::Checkout>,
}

pub(super) fn prepare_selected_git(
    donor: &Path,
    destination: &Path,
    registry: Option<&str>,
    registry_donor: Option<&Path>,
    sources: Vec<SourceId>,
    object_sources: &[(url::Url, PathBuf)],
) -> CargoResult<PreparedGitData> {
    ensure!(
        sources.len() <= super::super::super::MAX_SOURCES,
        "too many locked Git source inputs"
    );
    ensure!(
        registry.is_some() || registry_donor.is_none(),
        "registry DATA donor requires a selected registry"
    );
    let registry_donor = registry_donor.unwrap_or(donor);
    let mut homes = vec![donor, registry_donor];
    homes.sort_unstable();
    homes.dedup();
    let cache = Cache::source(donor)?;
    let registry_home = if registry.is_some() && registry_donor != donor {
        Some(Cache::capture_source_home(registry_donor)?)
    } else {
        None
    };
    let mut selectors = BTreeMap::new();
    for (url, path) in object_sources {
        ensure!(
            url.as_str().len() <= super::super::super::MAX_SOURCE_URL_BYTES,
            "Git source URL exceeds its bound"
        );
        ensure!(
            path.is_absolute() && path.canonicalize()? == *path,
            "source object directory must be absolute and canonical"
        );
        let key = crate::util::CanonicalUrl::new(url)?;
        ensure!(
            selectors.insert(key, path).is_none(),
            "duplicate canonical object-directory URL selector"
        );
    }
    ensure!(
        selectors.len() <= super::super::super::MAX_SOURCES,
        "too many object-directory selectors"
    );
    let mut paths = homes.clone();
    paths.extend(selectors.values().map(|path| path.as_path()));
    let mut stage = Stage::new(destination, &paths)?;
    let mut output = Output::new(&stage)?;
    let mut stats = Stats::default();
    let mut budget = CopyBudget::new(super::super::super::MAX_TOTAL_BYTES)?;
    let mut sources = sources;
    sources.sort_by_cached_key(|source| source.to_string());
    let checkout_sources = sources.clone();
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
    let mut used = std::collections::HashSet::new();
    let mut references = std::collections::BTreeSet::new();
    let mut view_bytes = 0;
    let mut closure_stats = SourceStats::default();
    let mut pack_reads = pack_stream::ReadBudget::default();
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
        let revision = locked_oid(source.id)?;
        let ident = crate::sources::git::source::ident(&source.id);
        if !databases.contains_key(&ident) {
            let original = if let Some(path) = selectors.get(source.id.canonical_url()) {
                used.insert(source.id.canonical_url().clone());
                ObjectSource::capture_objects(path)
            } else {
                ObjectSource::capture(&cache.home.path.join("git/db").join(&ident))
            }
            .with_context(|| {
                crate::sources::git::source::object_source_context(source.id, revision)
            })?;
            let objects = selectors
                .get(source.id.canonical_url())
                .map(|path| (*path).clone())
                .unwrap_or_else(|| cache.home.path.join("git/db").join(&ident).join("objects"));
            let mut view = stage.create_view(&ident)?;
            let copied = original
                .materialize_view(
                    &objects,
                    &mut view,
                    super::super::super::MAX_TOTAL_BYTES - view_bytes,
                    &mut budget,
                )
                .with_context(|| {
                    crate::sources::git::source::object_source_context(source.id, revision)
                })?;
            view_bytes += copied.bytes;
            let odb = git2::Odb::new()?;
            odb.add_disk_alternate(
                view.path()
                    .to_str()
                    .context("private object view must be UTF8")?,
            )?;
            let input = git2::Repository::from_odb(odb)?;
            input.set_config(&git2::Config::new()?)?;
            let prefix = PathBuf::from("git/db").join(&ident);
            let stored = output.object_database(&prefix, &mut stats, &mut budget)?;
            original.check_current()?;
            view.check_current()?;
            databases.insert(
                ident.clone(),
                Database {
                    representative: source.id,
                    original,
                    view,
                    input,
                    output: Some(stored),
                    copied: crate::util::data_structures::HashMap::default(),
                },
            );
        }
        let database = databases
            .get_mut(&ident)
            .context("selected DATA database unavailable")?;
        ensure!(
            database.representative.canonical_url() == source.id.canonical_url(),
            "source cache identifier collision"
        );
        database.original.check_current()?;
        database.view.check_current()?;
        // The same native full-history exporter as explicit source intake:
        // original parents, all their trees/bodies and hashes remain required.
        inspect_closure_for_pack(database, revision, &mut closure_stats, &mut pack_reads)
            .with_context(|| {
                crate::sources::git::source::object_source_context(source.id, revision)
            })?;
        let children = submodules::selected(&database.input, revision, &source.parent_url)
            .with_context(|| {
                crate::sources::git::source::object_source_context(source.id, revision)
            })?;
        if references.insert((ident.clone(), revision)) {
            output.generated(
                &PathBuf::from("git/db")
                    .join(&ident)
                    .join("refs/commit")
                    .join(revision.to_string()),
                format!("{revision}\n").as_bytes(),
                &mut stats,
                &mut budget,
            )?;
        }
        ensure!(
            pending.len() + children.len() < super::super::super::MAX_SOURCES * 2,
            "submodule pending work bound exceeded"
        );
        ensure!(
            stats.bytes <= super::super::super::MAX_TOTAL_BYTES,
            "stored cache DATA exceeds32GiB transaction bound"
        );
        pending.push(Work::Exit(key));
        pending.extend(children.into_iter().rev().map(Work::Enter));
    }
    ensure!(
        used.len() == selectors.len(),
        "unused object-directory URL selector"
    );
    let (checkouts, checkout_stats) = super::checkout::copy_selected(
        &cache,
        &checkout_sources,
        &databases,
        destination,
        &mut output,
        &mut budget,
    )?;
    stats.checkout_files = checkout_stats.files;
    stats.checkout_bytes = checkout_stats.bytes;
    stats.checkout_cloned_bytes = checkout_stats.cloned_bytes;
    stats.checkout_streamed_bytes = checkout_stats.streamed_bytes;
    let mut originals = Vec::new();
    let mut views = Vec::new();
    let mut stored_objects = Vec::new();
    for (ident, database) in databases {
        let revision = locked_oid(database.representative)?;
        output
            .pack_objects(&PathBuf::from("git/db").join(&ident), &database)
            .with_context(|| {
                crate::sources::git::source::object_source_context(
                    database.representative,
                    revision,
                )
            })?;
        let Database {
            original,
            view,
            input,
            output: stored,
            ..
        } = database;
        original.check_current()?;
        view.check_current()?;
        drop(input);
        drop(stored);
        stored_objects.push(output.finish_objects(
            &PathBuf::from("git/db").join(ident),
            &mut stats,
            &mut budget,
        )?);
        originals.push(original);
        views.push(view);
    }
    for original in &originals {
        original.check_current()?;
    }
    for stored in &stored_objects {
        stored.source.check_current()?;
    }
    for checkout in &checkouts {
        checkout.check_current()?;
    }
    cache.check_current()?;
    output.check_current()?;
    stage.close_views(&mut views)?;
    Ok(PreparedGitData {
        cache,
        registry_name: registry.map(str::to_owned),
        registry_home,
        stage,
        output,
        stats,
        budget,
        originals,
        stored_objects,
        checkouts,
    })
}

impl PreparedGitData {
    fn check_git_current(&self) -> CargoResult<()> {
        self.cache.check_current()?;
        for original in &self.originals {
            original.check_current()?;
        }
        for stored in &self.stored_objects {
            stored.source.check_current()?;
        }
        for checkout in &self.checkouts {
            checkout.check_current()?;
        }
        Ok(())
    }

    pub(super) fn publish(mut self) -> CargoResult<Stats> {
        self.stage.validate_namespace()?;
        self.check_git_current()?;
        // Trust: this is the SAME early captured directory, not a recreated
        // cache owner. Each cache acquisition remains nonblocking and keeps
        // Cargo's mutate-before-download ordering, so cross-cache contention
        // refuses instead of introducing a blocking ABBA wait.
        let registry_cache = self
            .registry_home
            .take()
            .map(|home| Cache::acquire_home(home, false))
            .transpose()?;
        let registry_source = registry_cache.as_ref().unwrap_or(&self.cache);
        let registry = self
            .registry_name
            .as_deref()
            .map(|name| {
                RegistryCopy::copy(
                    registry_source,
                    name,
                    &mut self.output,
                    &mut self.stats,
                    &mut self.budget,
                )
            })
            .transpose()?;
        self.check_git_current()?;
        if let Some(cache) = &registry_cache {
            cache.check_current()?;
        }
        if let Some(registry) = &registry {
            registry.check_current()?;
        }
        self.output.check_current()?;
        self.stats.stored_entries = self.output.entries.stored;
        self.stats.checkout_entries = self.output.entries.checkouts;
        self.stage.publish()?;
        Ok(self.stats)
    }
}

#[cfg(test)]
#[test]
fn generated_selected_objects_keep_sticky_original_output_bookends() {
    let world = super::super::super::tests::private_world();
    let root = world.path().canonicalize().unwrap();
    let stage = Stage::new(&root.join("destination"), &[]).unwrap();
    let mut output = Output::new(&stage).unwrap();
    let prefix = Path::new("git/db/original");
    let mut stats = Stats::default();
    let mut budget = CopyBudget::new(super::super::super::MAX_TOTAL_BYTES).unwrap();
    let repository = output
        .object_database(prefix, &mut stats, &mut budget)
        .unwrap();
    repository.blob(b"original generated output").unwrap();
    drop(repository);
    let stored = output
        .finish_objects(prefix, &mut stats, &mut budget)
        .unwrap();
    stored.source.check_current().unwrap();
    let path = &stored.source.files[0].0;
    let original = root.join("retained-original-object");
    std::fs::rename(path, &original).unwrap();
    std::fs::copy(&original, path).unwrap();
    assert!(stored.source.check_current().is_err());
    std::fs::remove_file(path).unwrap();
    std::fs::rename(original, path).unwrap();
    assert!(stored.source.check_current().is_err());
}
