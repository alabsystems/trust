//! Trust: selected-tree submodule recipes from copied Git DATA, never a checkout
//! or donor/ambient configuration. Historical gitlinks are not selected recipes.

use super::{MAX_OBJECTS, MAX_SOURCE_URL_BYTES, MAX_SOURCES};
use crate::sources::git::utils::{absolute_submodule_url, submodule_source_id};
use crate::util::CargoResult;
use crate::util::data_structures::HashSet;
use crate::workspace::SourceId;
use anyhow::{Context as _, ensure};
use std::collections::BTreeMap;
use std::os::unix::ffi::OsStringExt as _;

const MAX_MODULE_BYTES: usize = 1024 * 1024;
const MAX_TREE_DEPTH: usize = 64;
const MAX_PATH_BYTES: usize = 4096;

/// The fetch spelling matters for resolving a nested relative SCP-like URL;
/// its normalized SourceId alone must not replace that original parent URL.
#[derive(Clone)]
pub(super) struct Source {
    pub(super) id: SourceId,
    pub(super) parent_url: String,
}

#[derive(Default)]
pub(super) struct Traversal {
    active: HashSet<(SourceId, String)>,
    complete: HashSet<(SourceId, String)>,
}

impl Traversal {
    pub(super) fn enter(&mut self, key: &(SourceId, String)) -> CargoResult<bool> {
        if self.complete.contains(key) {
            return Ok(false);
        }
        ensure!(
            !self.active.contains(key),
            "selected submodule source cycle"
        );
        ensure!(
            self.active.len() + self.complete.len() < MAX_SOURCES,
            "recursive Git source bound exceeded"
        );
        self.active.insert(key.clone());
        Ok(true)
    }

    pub(super) fn finish(&mut self, key: (SourceId, String)) -> CargoResult<()> {
        ensure!(
            self.active.remove(&key),
            "submodule traversal lost its active source"
        );
        self.complete.insert(key);
        Ok(())
    }
}

pub(super) fn selected(
    repository: &git2::Repository,
    revision: git2::Oid,
    parent_url: &str,
) -> CargoResult<Vec<Source>> {
    Ok(selected_with_paths(repository, revision, parent_url)?
        .into_iter()
        .map(|(_, source)| source)
        .collect())
}

pub(super) fn selected_with_paths(
    repository: &git2::Repository,
    revision: git2::Oid,
    parent_url: &str,
) -> CargoResult<Vec<(std::path::PathBuf, Source)>> {
    ensure!(
        parent_url.len() <= MAX_SOURCE_URL_BYTES,
        "submodule parent URL exceeds its bound"
    );
    let tree = repository.find_commit(revision)?.tree()?;
    let mut links = selected_links(repository, tree.id())?;
    let Some(entry) = tree.get_name(".gitmodules") else {
        ensure!(
            links.is_empty(),
            "selected gitlink has no .gitmodules recipe"
        );
        return Ok(Vec::new());
    };
    ensure!(
        matches!(entry.filemode(), 0o100644 | 0o100755),
        "selected .gitmodules must be a regular blob"
    );
    let (size, kind) = repository.odb()?.read_header(entry.id())?;
    ensure!(
        kind == git2::ObjectType::Blob,
        "selected .gitmodules must be a regular blob"
    );
    ensure!(size <= MAX_MODULE_BYTES, ".gitmodules exceeds 1 MiB");
    let blob = repository.find_blob(entry.id())?;
    ensure!(
        blob.size() == size,
        "selected .gitmodules changed during reading"
    );
    let empty = gix::config::File::new(gix::config::file::Metadata::from(gix::config::Source::Api));
    // This maintained parser uses from_parse_events_no_includes internally.
    // No repository/global config, path lookup or include callback is supplied.
    let modules = gix::submodule::File::from_bytes(blob.content(), None, &empty)?;
    let mut names = HashSet::default();
    let mut paths = HashSet::default();
    let mut children = Vec::new();
    for section in modules.config().sections() {
        ensure!(
            section.header().name().eq_ignore_ascii_case(b"submodule"),
            "unsupported .gitmodules section (includes are not admitted)"
        );
        let name = section
            .header()
            .subsection_name()
            .context("unnamed submodule recipe")?;
        ensure!(
            std::str::from_utf8(name).is_ok(),
            "submodule name is not UTF-8"
        );
        ensure!(
            names.len() < MAX_SOURCES && names.insert(name.to_owned()),
            "duplicate or excessive submodule recipes"
        );
        ensure!(
            gix::validate::submodule::name(name).is_ok(),
            "unsupported submodule name"
        );
        let mut fields = HashSet::default();
        for key in section.value_names() {
            let key = key.to_string().to_ascii_lowercase();
            ensure!(
                matches!(
                    key.as_str(),
                    "path"
                        | "url"
                        | "update"
                        | "branch"
                        | "ignore"
                        | "shallow"
                        | "fetchrecursesubmodules"
                ) && fields.insert(key),
                "duplicate or unsupported submodule field"
            );
        }
        let path = section
            .value("path")
            .context("submodule recipe has no path")?;
        let path = path.as_ref();
        ensure!(canonical_path(path), "submodule path is not canonical");
        ensure!(paths.insert(path.to_owned()), "duplicate submodule path");
        let url = section
            .value("url")
            .context("submodule recipe has no URL")?;
        let url = std::str::from_utf8(url.as_ref()).context("submodule URL is not UTF-8")?;
        ensure!(
            !url.is_empty()
                && url.len() <= MAX_SOURCE_URL_BYTES
                && !url.starts_with('-')
                && !url.contains('\0'),
            "unsupported submodule URL"
        );
        // Validate passive fields through the same maintained native module API.
        modules.branch(name)?;
        modules.ignore(name)?;
        modules.shallow(name)?;
        modules.fetch_recurse(name)?;
        let update = modules.update(name)?;
        ensure!(
            !matches!(update, Some(gix::submodule::config::Update::Command(_))),
            "submodule commands are not admitted"
        );
        let revision = links.remove(path);
        // Ordinary checkout obtains path/URL first, then skips update=none;
        // there is no URL resolution or child database requirement in that case.
        if update == Some(gix::submodule::config::Update::None) {
            continue;
        }
        let Some(revision) = revision else {
            continue; // .gitmodules-only declaration has no selected head_id.
        };
        let absolute = absolute_submodule_url(parent_url, url)?;
        ensure!(
            absolute.len() <= MAX_SOURCE_URL_BYTES,
            "resolved submodule URL exceeds its bound"
        );
        let (id, fetch_url) = submodule_source_id(&absolute, revision)?;
        children.push((
            std::path::PathBuf::from(std::ffi::OsString::from_vec(path.to_vec())),
            Source {
                id,
                parent_url: fetch_url.unwrap_or_else(|| id.url().to_string()),
            },
        ));
    }
    ensure!(
        links.is_empty(),
        "selected gitlink has no matching submodule recipe"
    );
    Ok(children)
}

fn canonical_path(path: &[u8]) -> bool {
    !path.is_empty()
        && path.len() <= MAX_PATH_BYTES
        && !path.starts_with(b"-")
        && !path.contains(&0)
        && !path.contains(&b'\\')
        && path.split(|byte| *byte == b'/').all(|part| {
            !part.is_empty() && part != b"." && part != b".." && !part.eq_ignore_ascii_case(b".git")
        })
}

fn selected_links(
    repository: &git2::Repository,
    root: git2::Oid,
) -> CargoResult<BTreeMap<Vec<u8>, git2::Oid>> {
    let mut pending = vec![(root, Vec::new(), 0)];
    let mut links = BTreeMap::new();
    let mut inspected = 0;
    while let Some((oid, prefix, depth)) = pending.pop() {
        ensure!(
            depth <= MAX_TREE_DEPTH,
            "selected tree depth exceeds its bound"
        );
        for entry in repository.find_tree(oid)?.iter() {
            inspected += 1;
            ensure!(
                inspected <= MAX_OBJECTS,
                "selected tree edge bound exceeded"
            );
            let mut path = prefix.clone();
            path.extend_from_slice(entry.name_bytes());
            ensure!(
                path.len() <= MAX_PATH_BYTES,
                "selected tree path bound exceeded"
            );
            match entry.filemode() {
                0o040000 => {
                    path.push(b'/');
                    pending.push((entry.id(), path, depth + 1));
                }
                0o160000 => {
                    ensure!(
                        links.len() < MAX_SOURCES,
                        "selected submodule bound exceeded"
                    );
                    ensure!(
                        links.insert(path, entry.id()).is_none(),
                        "duplicate selected gitlink"
                    );
                }
                _ => {}
            }
        }
    }
    Ok(links)
}

#[cfg(test)]
mod tests;
