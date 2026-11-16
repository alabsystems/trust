//! Linux-specific runtime evidence; deliberately distinct from Mach-O v2.

use serde::{Deserialize, Serialize};

pub(super) const SCHEMA: &str = "trust.trustd-runtime-closure.linux-elf.v1";
pub(super) const FORMAT: &str = "elf64-le-gnu-loader";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct FileIdentity {
    pub(super) path: String,
    pub(super) target: String,
    pub(super) device: u64,
    pub(super) inode: u64,
    pub(super) mode: u32,
    pub(super) bytes: u64,
    pub(super) sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct SystemObject {
    pub(super) name: String,
    pub(super) file: FileIdentity,
    pub(super) needed: Vec<String>,
}

/// Every cached target is retained, including entries unusable on this CPU.
/// Admission deliberately validates a superset instead of reimplementing GNU
/// cache preference/ISA ordering and accidentally omitting a possible source.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CacheEntry {
    pub(super) name: String,
    pub(super) path: String,
    pub(super) flags: u32,
    pub(super) hwcap: u64,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct LoaderSearch {
    pub(super) glibc_version: String,
    pub(super) system_directories: Vec<String>,
    pub(super) hwcaps_subdirectories: Vec<String>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum AuthorityKind {
    Directory,
    Object,
    Symlink,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct AuthorityNode {
    pub(super) path: String,
    pub(super) kind: AuthorityKind,
    pub(super) device: u64,
    pub(super) inode: u64,
    pub(super) uid: u32,
    pub(super) gid: u32,
    pub(super) mode: u32,
    pub(super) link: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct PathAuthority {
    pub(super) path: String,
    pub(super) kind: AuthorityKind,
    pub(super) target: String,
    pub(super) present: bool,
    pub(super) nodes: Vec<AuthorityNode>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct SearchAuthority {
    pub(super) loader: LoaderSearch,
    pub(super) cache_entries: Vec<CacheEntry>,
    pub(super) directory_entries: Vec<SearchDirectoryEntry>,
    pub(super) paths: Vec<PathAuthority>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct SearchDirectoryEntry {
    pub(super) directory: String,
    pub(super) name: String,
    pub(super) kind: AuthorityKind,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct LinuxRuntimeClosure {
    pub(super) machine: u16,
    pub(super) candidate_sha256: String,
    pub(super) interpreter: String,
    pub(super) needed: Vec<String>,
    pub(super) objects: Vec<SystemObject>,
    pub(super) loader_cache: Option<FileIdentity>,
    pub(super) loader_preload: Option<FileIdentity>,
    pub(super) search_authority: SearchAuthority,
}

#[cfg(target_os = "linux")]
#[path = "linux_authority.rs"]
mod authority;
#[cfg(target_os = "linux")]
#[path = "linux_cache.rs"]
mod cache;
#[cfg(target_os = "linux")]
#[path = "linux_search.rs"]
mod search;

#[cfg(target_os = "linux")]
#[path = "linux_runtime_validation.rs"]
mod validation;
#[cfg(target_os = "linux")]
pub(super) use validation::{
    host_machine, interpreter_for, loader_rows, normalized_path, system_path, validate,
};

#[cfg(not(target_os = "linux"))]
pub(super) fn validate(
    _record: &LinuxRuntimeClosure,
    _inspector: &str,
    _inspector_sha256: &str,
    _dependencies: &[String],
) -> Result<(), String> {
    Err("Linux ELF runtime evidence is not admission on this host".to_owned())
}

#[cfg(target_os = "linux")]
#[path = "linux_runtime_observe.rs"]
mod observe;
#[cfg(target_os = "linux")]
pub(super) use observe::inspect;

#[cfg(all(test, target_os = "linux"))]
#[path = "linux_runtime_tests.rs"]
mod tests;
