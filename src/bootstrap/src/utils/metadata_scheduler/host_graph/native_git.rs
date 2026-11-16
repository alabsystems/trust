//! Native local source identity observations for the original no-fork graph.
//! No Git child, network, hook, saved commit-info or source/Manager constructor.
use std::fs::{File, OpenOptions};
use std::io;
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::path::{Path, PathBuf};
use std::time::Instant;

use super::{OriginalHostGraph, lock, time};
use crate::utils::channel::{GitInfo, Info};
const MAX_COMMIT_BYTES: u64 = 1024 * 1024;
mod tree;
pub use tree::{
    CommittedEntry, CommittedLookup, CommittedRepository, CommittedSourceReadSet,
    DependencySourceRefusal, DependencySourceSnapshot, SourceRead,
};
fn invalid(why: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, why)
}
fn error(error: impl std::fmt::Display) -> io::Error {
    io::Error::other(error.to_string())
}
type DirectoryStamp = (u64, u64, u32, u32, u32, u64, i64, i64);
fn stamp(file: &File) -> io::Result<DirectoryStamp> {
    let m = file.metadata()?;
    if !m.is_dir() {
        return Err(invalid("native Git source is not a directory"));
    }
    Ok((m.dev(), m.ino(), m.mode(), m.uid(), m.gid(), m.nlink(), m.ctime(), m.ctime_nsec()))
}
fn source_dir(path: &Path) -> io::Result<File> {
    OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
}
fn repository(path: &Path) -> io::Result<gix::Repository> {
    trust_committed_source::open_repository(path)
}
fn observe(dir: &Path, omit: bool, deadline: Instant) -> io::Result<GitInfo> {
    observe_profile(dir, omit, deadline, true)
}
pub(super) fn observe_profile(
    dir: &Path,
    omit: bool,
    deadline: Instant,
    required_source: bool,
) -> io::Result<GitInfo> {
    time(deadline)?;
    match std::fs::symlink_metadata(dir.join(".git")) {
        Ok(_) => {}
        Err(error) if !required_source && error.kind() == io::ErrorKind::NotFound => {
            // Known absence at an optional component is an observation, not a
            // declined Git child or saved identity. The first node uses none
            // of these components. Its selected source Root is always required.
            time(deadline)?;
            return Ok(GitInfo::Absent);
        }
        Err(error) => return Err(error),
    }
    let canonical = dir.canonicalize()?;
    let original = source_dir(&canonical)?;
    let before = stamp(&original)?;
    // Isolated options forbid global/system/env/include configuration and
    // binary lookup. No transport, worktree update, hook or command is called.
    let repo = repository(&canonical)?;
    if repo.workdir() != Some(canonical.as_path()) {
        return Err(invalid("native source Git root differs from selected directory"));
    }
    let head = repo.head_id().map_err(error)?;
    let id = head.detach();
    let header = repo.find_header(id).map_err(error)?;
    if header.kind() != gix::objs::Kind::Commit || header.size() > MAX_COMMIT_BYTES {
        return Err(invalid("native source HEAD is not a bounded commit"));
    }
    let commit = repo.head_commit().map_err(error)?;
    if commit.id != id
        || commit.data.len() as u64 > MAX_COMMIT_BYTES
        || gix::objs::compute_hash(id.kind(), gix::objs::Kind::Commit, &commit.data)
            .map_err(error)?
            != id
    {
        return Err(invalid("native source commit bytes differ from original HEAD"));
    }
    let info = if omit {
        GitInfo::Present(None)
    } else {
        let sha = id.to_string();
        if sha.len() != 40 {
            return Err(invalid("native source hash format unsupported"));
        }
        // Disambiguate at least nine actual hex digits, matching the normal
        // observer's --short=9 without a configuration/version override.
        let candidate =
            gix::odb::store::prefix::disambiguate::Candidate::new(id, 9).map_err(error)?;
        let short_sha = repo
            .objects
            .disambiguate_prefix(candidate)
            .map_err(error)?
            .ok_or_else(|| invalid("native commit abbreviation unavailable"))?
            .to_string();
        let commit_date =
            commit.time().map_err(error)?.format(gix::date::time::format::SHORT).map_err(error)?;
        GitInfo::Present(Some(Info { commit_date, sha, short_sha }))
    };
    if repo.head_id().map_err(error)?.detach() != id
        || stamp(&original)? != before
        || stamp(&source_dir(&canonical)?)? != before
        || dir.canonicalize()? != canonical
    {
        return Err(invalid("native source Git/root changed during observation"));
    }
    time(deadline)?;
    Ok(info)
}
/// Discover only actual local worktree metadata, without a Git child or
/// environment/global/include configuration. Paths remain observations.
pub(super) fn discover_source_directory_at(start: &Path, deadline: Instant) -> io::Result<PathBuf> {
    time(deadline)?;
    let start = start.canonicalize()?;
    let original = source_dir(&start)?;
    let before = stamp(&original)?;
    let (located, _) = gix::discover::upwards_opts(&start, Default::default()).map_err(error)?;
    let (_, worktree) = located.into_repository_and_work_tree_directories();
    let root = worktree
        .ok_or_else(|| invalid("native Bootstrap source is not a worktree"))?
        .canonicalize()?;
    let directory = source_dir(&root)?;
    let root_before = stamp(&directory)?;
    let repo = gix::open_opts(&root, gix::open::Options::isolated()).map_err(error)?;
    if repo.workdir() != Some(root.as_path()) || !root.join("src/stage0").is_file() {
        return Err(invalid("native discovered repository is not a Bootstrap source root"));
    }
    if stamp(&original)? != before
        || stamp(&source_dir(&start)?)? != before
        || stamp(&directory)? != root_before
        || stamp(&source_dir(&root)?)? != root_before
    {
        return Err(invalid("native source discovery directory changed"));
    }
    time(deadline)?;
    Ok(root)
}

impl OriginalHostGraph {
    fn observe_git(&self, dir: &Path, omit: bool, required_source: bool) -> io::Result<GitInfo> {
        self.check()?;
        let result = if required_source {
            observe(dir, omit, self.deadline)
        } else {
            observe_profile(dir, omit, self.deadline, false)
        };
        if result.is_err()
            && let Ok(mut state) = lock(&self.state, self.deadline)
        {
            state.failed = true;
        }
        let value = result?;
        self.check()?;
        Ok(value)
    }
}
pub(crate) fn native_source_directory() -> io::Result<PathBuf> {
    let graph = super::ORIGINAL
        .get()
        .and_then(std::sync::Weak::upgrade)
        .ok_or_else(|| invalid("original Host graph absent for native source discovery"))?;
    graph.check()?;
    let result = discover_source_directory_at(&std::env::current_dir()?, graph.deadline);
    if result.is_err()
        && let Ok(mut state) = lock(&graph.state, graph.deadline)
    {
        state.failed = true;
    }
    let root = result?;
    graph.check()?;
    Ok(root)
}

pub(crate) fn native_git_info(dir: &Path, omit: bool) -> io::Result<GitInfo> {
    let graph = super::ORIGINAL
        .get()
        .and_then(std::sync::Weak::upgrade)
        .ok_or_else(|| invalid("original Host graph absent for native Git observation"))?;
    graph.observe_git(dir, omit, false)
}
pub(crate) fn native_source_git_info(dir: &Path, omit: bool) -> io::Result<GitInfo> {
    let graph = super::ORIGINAL
        .get()
        .and_then(std::sync::Weak::upgrade)
        .ok_or_else(|| invalid("original Host graph absent for required native source identity"))?;
    graph.observe_git(dir, omit, true)
}

#[cfg(test)]
mod tests;
