//! Trust: selected locked object storage DATA, never provenance or readiness.
//! Reuse the original object-view factory and selected-tree submodule traversal;
//! keep compressed storage rather than expanding every historical object.
use super::super::super::{Work, locked_oid, submodules};
use super::*;
use crate::workspace::SourceId;

pub(super) struct Database {
    pub(super) source: SourceId,
    original: ObjectSource,
    view: OwnedView,
    pub(super) input: git2::Repository,
}

pub(in super::super::super) fn import_selected(
    donor: &Path,
    destination: &Path,
    registry: Option<&str>,
    registry_donor: Option<&Path>,
    sources: Vec<SourceId>,
    object_sources: &[(url::Url, PathBuf)],
) -> CargoResult<Stats> {
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
    let caches = homes
        .iter()
        .map(|path| Cache::source(path))
        .collect::<CargoResult<Vec<_>>>()?;
    let cache = caches
        .iter()
        .find(|cache| cache.home.path == donor)
        .context("original Git DATA cache owner unavailable")?;
    let registry_cache = caches
        .iter()
        .find(|cache| cache.home.path == registry_donor)
        .context("original registry DATA cache owner unavailable")?;
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
                ObjectSource::capture_objects(path)?
            } else {
                ObjectSource::capture(&cache.home.path.join("git/db").join(&ident))?
            };
            let objects = selectors
                .get(source.id.canonical_url())
                .map(|path| (*path).clone())
                .unwrap_or_else(|| cache.home.path.join("git/db").join(&ident).join("objects"));
            let mut view = stage.create_view(&ident)?;
            let copied = original.materialize_view(
                &objects,
                &mut view,
                super::super::super::MAX_TOTAL_BYTES - view_bytes,
                &mut budget,
            )?;
            view_bytes += copied.bytes;
            let odb = git2::Odb::new()?;
            odb.add_disk_alternate(
                view.path()
                    .to_str()
                    .context("private object view must be UTF8")?,
            )?;
            let input = git2::Repository::from_odb(odb)?;
            let prefix = PathBuf::from("git/db").join(&ident);
            let stored = Tree::capture(Directory::open(view.path())?)?;
            stored.copy(
                &mut output,
                &prefix.join("objects"),
                DataKind::Objects,
                &mut stats,
                &mut budget,
            )?;
            output.generated(
                &prefix.join("config"),
                b"[core]\nrepositoryformatversion = 0\nbare = true\n",
                &mut stats,
                &mut budget,
            )?;
            output.generated(
                &prefix.join("HEAD"),
                b"ref: refs/heads/master\n",
                &mut stats,
                &mut budget,
            )?;
            stored.source.check_current()?;
            original.check_current()?;
            view.check_current()?;
            databases.insert(
                ident.clone(),
                Database {
                    source: source.id,
                    original,
                    view,
                    input,
                },
            );
        }
        let database = databases
            .get(&ident)
            .context("selected DATA database unavailable")?;
        ensure!(
            database.source.canonical_url() == source.id.canonical_url(),
            "source cache identifier collision"
        );
        database.original.check_current()?;
        database.view.check_current()?;
        // Actual selected commit/tree parsing, never a saved presence status.
        database.input.find_commit(revision)?;
        let children = submodules::selected(&database.input, revision, &source.parent_url)?;
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
        cache,
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
    let registry = registry
        .map(|name| RegistryCopy::copy(registry_cache, name, &mut output, &mut stats, &mut budget))
        .transpose()?;
    let mut originals = Vec::new();
    let mut views = Vec::new();
    for database in databases.into_values() {
        let Database {
            original,
            view,
            input,
            ..
        } = database;
        original.check_current()?;
        view.check_current()?;
        drop(input);
        originals.push(original);
        views.push(view);
    }
    for original in &originals {
        original.check_current()?;
    }
    for checkout in &checkouts {
        checkout.check_current()?;
    }
    for cache in &caches {
        cache.check_current()?;
    }
    if let Some(registry) = &registry {
        registry.check_current()?;
    }
    output.check_current()?;
    stats.stored_entries = output.entries.stored;
    stats.checkout_entries = output.entries.checkouts;
    stage.close_views(&mut views)?;
    for original in &originals {
        original.check_current()?;
    }
    for cache in &caches {
        cache.check_current()?;
    }
    for checkout in &checkouts {
        checkout.check_current()?;
    }
    if let Some(registry) = &registry {
        registry.check_current()?;
    }
    output.check_current()?;
    stage.publish()?;
    Ok(stats)
}
