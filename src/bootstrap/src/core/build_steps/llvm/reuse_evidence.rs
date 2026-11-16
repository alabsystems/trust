//! Trust: the bounded evidence native CMake reuse is admitted on: the owning CMake
//! generation, observed source bytes, and recorded completed LLVM dependencies.

use std::fs;
use std::path::Path;

use super::{LLVM_CI_LINK_TYPE_PATH, LlvmKind, LlvmOutput, installed_outputs};
use crate::core::config::TargetSelection;
use crate::utils::build_stamp::BuildStamp;

// This enum records only whether the owner's existing request/provider inputs
// are reusable. A generation marker cannot manufacture this eligibility.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum CmakeGeneration {
    Known,
    Unknown,
}

fn cmake_output_root(stamp: &BuildStamp) -> std::io::Result<(&Path, bool)> {
    let root =
        stamp.path().parent().filter(|path| !path.as_os_str().is_empty()).ok_or_else(|| {
            std::io::Error::other("CMake completion has no dedicated output root")
        })?;
    match fs::symlink_metadata(root) {
        Ok(metadata) if metadata.is_dir() && !metadata.file_type().is_symlink() => Ok((root, true)),
        Ok(_) => Err(std::io::Error::other("CMake output root is not a real directory")),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok((root, false)),
        Err(error) => Err(error),
    }
}

pub(super) fn cmake_generation_record(stamp: &BuildStamp) -> std::io::Result<BuildStamp> {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish};
    let (root, _) = cmake_output_root(stamp)?;
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"trust.native-cmake-generation/v1");
    add(&mut hash, stamp.stamp().as_bytes());
    Ok(BuildStamp::new(root).with_prefix("cmake-generation").add_stamp(finish(hash)))
}

pub(super) fn cmake_generation_matches(stamp: &BuildStamp) -> bool {
    let Ok(record) = cmake_generation_record(stamp) else {
        return false;
    };
    bounded_native_evidence(record.path(), record.stamp().len() as u64)
        .is_some_and(|(bytes, _)| bytes == record.stamp().as_bytes())
}

// Validate the final root before any mutation; maintained ancestor symlinks are
// allowed. This does not promise closure against concurrent hostile path swaps.
// Completion removal is the first mutation. Membership is request data, never
// completed artifact identity, resource custody or provider readiness.
pub(super) fn begin_cmake_miss(
    stamp: &BuildStamp,
    generation: CmakeGeneration,
) -> std::io::Result<()> {
    let (root, exists) = cmake_output_root(stamp)?;
    stamp.remove()?;
    if generation == CmakeGeneration::Known && cmake_generation_matches(stamp) {
        return Ok(());
    }
    if exists {
        fs::remove_dir_all(root)?;
    }
    fs::create_dir_all(root)?;
    if generation == CmakeGeneration::Known {
        cmake_generation_record(stamp)?.write()?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
pub(super) struct ReusableCmakeInputs<'a> {
    pub(super) source: &'a str,
    pub(super) dependency: &'a str,
    pub(super) request: &'a str,
}

pub(super) fn reusable_cmake_inputs<'a>(
    source: Option<&'a str>,
    dependency: Option<&'a str>,
    request: Option<&'a str>,
) -> Option<ReusableCmakeInputs<'a>> {
    Some(ReusableCmakeInputs { source: source?, dependency: dependency?, request: request? })
}

pub(super) fn observe_cmake_sources(
    source: &Path,
    output: &Path,
) -> std::io::Result<Option<String>> {
    crate::utils::trust_repo_cache::own_cmake_source_digest(source, output)
        .map_err(std::io::Error::other)
}

// A request-membership marker never upgrades an unknown or changed source.
pub(super) fn own_source_unchanged(before: Option<&str>, after: Option<&str>) -> bool {
    before.is_some() && before == after
}

pub(super) fn complete_with_unchanged_cmake_source(
    source: &Path,
    output: &Path,
    before: Option<&str>,
    complete: impl FnOnce() -> std::io::Result<()>,
) -> std::io::Result<()> {
    let after = observe_cmake_sources(source, output)?;
    if own_source_unchanged(before, after.as_deref()) {
        complete()?;
    }
    Ok(())
}

// Strict recognition of the new completion domain. Unknown and historical values
// cannot become working-byte evidence merely by existing beside an artifact.
pub(super) struct SourceCompletion<'a> {
    pub(super) project: &'a str,
    target: &'a str,
    link_shared: bool,
}
pub(super) fn full_source_digest(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
pub(super) fn parse_source_completion(bytes: &[u8]) -> Option<SourceCompletion<'_>> {
    let text = std::str::from_utf8(bytes).ok()?;
    if !text.ends_with('\n') {
        return None;
    }
    let mut lines = text.split_terminator('\n');
    let project = match lines.next()? {
        "trust.llvm-working-source/v2" => "llvm",
        "trust.lld-working-source/v2" => "lld",
        _ => return None,
    };
    let target = lines.next()?.strip_prefix("target ")?;
    let source = lines.next()?.strip_prefix("source ")?;
    let request = lines.next()?.strip_prefix("request ")?;
    let link_shared = match lines.next()?.strip_prefix("linking ")? {
        "static" => false,
        "shared" => true,
        _ => return None,
    };
    let dependency = lines.next()?.strip_prefix("dependency ")?;
    if target.is_empty()
        || !full_source_digest(source)
        || !full_source_digest(request)
        || !(dependency == "none" || full_source_digest(dependency))
        || (project == "lld" && dependency == "none")
        || lines.next().is_some()
    {
        return None;
    }
    Some(SourceCompletion { project, target, link_shared })
}
fn working_llvm_completion(bytes: &[u8], target: &str, link_shared: bool) -> bool {
    parse_source_completion(bytes).is_some_and(|record| {
        record.project == "llvm" && record.target == target && record.link_shared == link_shared
    })
}

// Trust: selected link mode is a request field; the file bytes below are
// recorded completed evidence, not complete artifact identity or authentication.
pub(super) fn recorded_llvm_dependency_key(
    llvm: &LlvmOutput,
    target: TargetSelection,
) -> Option<String> {
    recorded_llvm_dependency_key_with_hook(llvm, target, || {})
}

pub(super) fn recorded_llvm_dependency_key_with_hook(
    llvm: &LlvmOutput,
    target: TargetSelection,
    after_classification: impl FnOnce(),
) -> Option<String> {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish, same_snapshot};

    if llvm.kind() == LlvmKind::External {
        return None;
    }
    let root = fs::canonicalize(llvm.root_dir()).ok()?;
    if !fs::metadata(&root).ok()?.is_dir() {
        return None;
    }
    let stamp = BuildStamp::new(&root).with_prefix("llvm");
    let local_stamp = if llvm.kind() == LlvmKind::BuiltLocally {
        Some(bounded_native_evidence(stamp.path(), 64 * 1024)?)
    } else {
        None
    };
    if local_stamp.as_ref().is_some_and(|(bytes, _)| {
        !working_llvm_completion(bytes, &target.triple, llvm.link_shared())
    }) {
        return None;
    }
    let installed = if let Some((bytes, _)) = &local_stamp {
        Some(installed_outputs::matches(llvm.root_dir(), std::str::from_utf8(bytes).ok()?)?)
    } else {
        None
    };
    let (kind, paths, limits) = match llvm.kind() {
        LlvmKind::BuiltLocally => (
            b"local".as_slice(),
            vec![
                stamp.path().to_owned(),
                root.join(".cmake-generation-stamp"),
                root.join("build/CMakeCache.txt"),
            ],
            vec![64 * 1024, 16 * 1024, 4 * 1024 * 1024],
        ),
        LlvmKind::DownloadedFromCi => (
            b"ci".as_slice(),
            vec![stamp.path().to_owned(), root.join(LLVM_CI_LINK_TYPE_PATH)],
            vec![64 * 1024, 16],
        ),
        LlvmKind::External => return None,
    };
    after_classification();
    let observed = paths
        .iter()
        .zip(limits)
        .enumerate()
        .map(|(index, (path, limit))| {
            if index == 0
                && let Some(evidence) = &local_stamp
            {
                Some(evidence.clone())
            } else {
                bounded_native_evidence(path, limit)
            }
        })
        .collect::<Option<Vec<_>>>()?;
    let stamp_at = observed[0].1.modified().ok()?;
    match llvm.kind() {
        LlvmKind::BuiltLocally => {
            let completed = BuildStamp::new(&root)
                .with_prefix("llvm")
                .add_stamp(std::str::from_utf8(&observed[0].0).ok()?);
            let expected = cmake_generation_record(&completed).ok()?;
            if observed[1].0 != expected.stamp().as_bytes() {
                return None;
            }
            if observed[2].1.modified().ok()? > stamp_at {
                return None;
            }
        }
        LlvmKind::DownloadedFromCi => {
            let stamp = std::str::from_utf8(&observed[0].0).ok()?;
            let source = stamp.strip_suffix(crate::core::download::CI_LLVM_COMPLETION_RECIPE)?;
            let source = source.strip_suffix("true").or_else(|| source.strip_suffix("false"))?;
            if !matches!(source.len(), 40 | 64)
                || !source
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                || observed[1].0
                    != if llvm.link_shared() { b"dynamic".as_slice() } else { b"static".as_slice() }
                || observed[1].1.modified().ok()? > stamp_at
            {
                return None;
            }
        }
        LlvmKind::External => return None,
    }
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"trust.native-llvm-dependency/v2");
    add(&mut hash, kind);
    add(&mut hash, if llvm.link_shared() { b"shared".as_slice() } else { b"static".as_slice() });
    add(&mut hash, root.as_os_str().as_encoded_bytes());
    add(&mut hash, target.triple.as_bytes());
    for (path, (bytes, metadata)) in paths.iter().zip(&observed) {
        if !same_snapshot(metadata, &fs::symlink_metadata(path).ok()?) {
            return None;
        }
        add(&mut hash, bytes);
    }
    if let Some(installed) = installed {
        if installed_outputs::matches(llvm.root_dir(), std::str::from_utf8(&observed[0].0).ok()?)?
            != installed
        {
            return None;
        }
        add(&mut hash, &installed);
    }
    (fs::canonicalize(llvm.root_dir()).ok()? == root).then(|| finish(hash))
}

pub(super) fn bounded_native_evidence(path: &Path, limit: u64) -> Option<(Vec<u8>, fs::Metadata)> {
    use std::io::Read;

    use crate::utils::trust_repo_cache::same_snapshot;

    let before = fs::symlink_metadata(path).ok()?;
    if !before.is_file() || before.len() > limit {
        return None;
    }
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let mut file = options.open(path).ok()?;
    if !same_snapshot(&before, &file.metadata().ok()?) {
        return None;
    }
    let mut bytes = Vec::new();
    (&mut file).take(limit + 1).read_to_end(&mut bytes).ok()?;
    if bytes.len() as u64 != before.len()
        || !same_snapshot(&before, &file.metadata().ok()?)
        || !same_snapshot(&before, &fs::symlink_metadata(path).ok()?)
    {
        return None;
    }
    Some((bytes, before))
}
