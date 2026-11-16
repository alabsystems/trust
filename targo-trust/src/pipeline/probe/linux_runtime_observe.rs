use std::fs::{File, Metadata, OpenOptions};
use std::io::{Read, Seek, SeekFrom};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};

use sha2::{Digest, Sha256};

use super::super::{TrustdRuntimeClosure, linux_elf};
use super::{CacheEntry, FileIdentity, LinuxRuntimeClosure, SearchAuthority, SystemObject};

enum Authority {
    System,
    Candidate,
}
enum Inspection {
    Hash,
    Elf,
    Cache,
}
struct Captured {
    file: FileIdentity,
    elf: Option<linux_elf::ElfMetadata>,
    cache: Option<Vec<CacheEntry>>,
}
struct Budget {
    remaining: u64,
}

fn identity(metadata: &Metadata) -> (u64, u64, u32, u64, i64, i64, i64, i64, u32, u32) {
    (
        metadata.dev(),
        metadata.ino(),
        metadata.mode(),
        metadata.len(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec(),
        metadata.uid(),
        metadata.gid(),
    )
}

fn root_chain(path: &Path) -> Result<(), String> {
    let text = path.to_str().ok_or("Linux runtime path is not UTF-8")?;
    if !super::normalized_path(text) {
        return Err("Linux runtime path is not normalized".into());
    }
    let mut current = PathBuf::from("/");
    let components = path.components().collect::<Vec<_>>();
    for (index, component) in components.iter().enumerate() {
        match component {
            Component::RootDir => {}
            Component::Normal(part) => current.push(part),
            _ => return Err("Linux runtime path is not absolute".into()),
        }
        let metadata = std::fs::symlink_metadata(&current)
            .map_err(|error| format!("Linux runtime authority {}: {error}", current.display()))?;
        let kind = metadata.file_type();
        if metadata.uid() != 0
            || (!kind.is_symlink() && metadata.mode() & 0o022 != 0)
            || (index + 1 == components.len() && !(kind.is_file() || kind.is_symlink()))
            || (index + 1 < components.len() && !(kind.is_dir() || kind.is_symlink()))
        {
            return Err(format!(
                "Linux runtime path {} is not immutable root authority",
                current.display()
            ));
        }
    }
    Ok(())
}

fn opened(path: &Path, authority: Authority) -> Result<(File, Metadata, PathBuf), String> {
    if matches!(authority, Authority::System) {
        root_chain(path)?;
    }
    let target =
        std::fs::canonicalize(path).map_err(|error| format!("Linux runtime path: {error}"))?;
    if matches!(authority, Authority::System) {
        root_chain(&target)?;
    }
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(&target)
        .map_err(|error| format!("Linux runtime open {}: {error}", target.display()))?;
    let metadata = file.metadata().map_err(|error| error.to_string())?;
    if !metadata.is_file()
        || metadata.len() > 512 * 1024 * 1024
        || identity(&metadata)
            != identity(&std::fs::symlink_metadata(&target).map_err(|error| error.to_string())?)
        || std::fs::canonicalize(path).map_err(|error| error.to_string())? != target
    {
        return Err("Linux runtime input is not the bounded exact opened regular file".into());
    }
    Ok((file, metadata, target))
}

fn capture(
    path: &Path,
    authority: Authority,
    inspection: Inspection,
    budget: &mut Budget,
) -> Result<Captured, String> {
    let (mut file, before, target) = opened(path, authority)?;
    budget.remaining = budget
        .remaining
        .checked_sub(before.len())
        .ok_or("Linux runtime total hash budget exceeded")?;
    let (elf, cache) = match inspection {
        Inspection::Hash => (None, None),
        Inspection::Elf => (
            Some(linux_elf::inspect(
                &mut file,
                before.len(),
                super::host_machine()?,
                linux_elf::host_page_bytes()?,
            )?),
            None,
        ),
        Inspection::Cache => {
            if before.len() > super::cache::MAX_BYTES as u64 {
                return Err("GNU loader cache exceeds its byte bound".into());
            }
            let mut bytes = Vec::new();
            bytes.try_reserve_exact(before.len() as usize).map_err(|error| error.to_string())?;
            Read::by_ref(&mut file)
                .take(before.len() + 1)
                .read_to_end(&mut bytes)
                .map_err(|error| error.to_string())?;
            if bytes.len() as u64 != before.len() {
                return Err("GNU cache changed size during capture".into());
            }
            (None, Some(super::cache::entries(&bytes)?))
        }
    };
    file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
    let mut hasher = Sha256::new();
    let mut buffer = [0; 64 * 1024];
    let mut read = 0u64;
    loop {
        let count = file.read(&mut buffer).map_err(|error| error.to_string())?;
        if count == 0 {
            break;
        }
        read = read
            .checked_add(count as u64)
            .filter(|&read| read <= before.len())
            .ok_or("Linux runtime file grew during capture")?;
        hasher.update(&buffer[..count]);
    }
    if read != before.len()
        || identity(&file.metadata().map_err(|error| error.to_string())?) != identity(&before)
        || identity(&std::fs::symlink_metadata(&target).map_err(|error| error.to_string())?)
            != identity(&before)
        || std::fs::canonicalize(path).map_err(|error| error.to_string())? != target
    {
        return Err("Linux runtime opened file changed during capture".into());
    }
    Ok(Captured {
        file: FileIdentity {
            path: path.to_str().ok_or("Linux runtime named path is not UTF-8")?.to_owned(),
            target: target.to_str().ok_or("Linux runtime target is not UTF-8")?.to_owned(),
            device: before.dev(),
            inode: before.ino(),
            mode: before.mode() & 0o7777,
            bytes: before.len(),
            sha256: format!("{:x}", hasher.finalize()),
        },
        elf,
        cache,
    })
}

fn cache_configuration(
    budget: &mut Budget,
) -> Result<(Option<FileIdentity>, Vec<CacheEntry>), String> {
    let path = Path::new("/etc/ld.so.cache");
    match std::fs::symlink_metadata(path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok((None, Vec::new())),
        Err(error) => Err(format!("GNU loader cache: {error}")),
        Ok(_) => {
            let captured = capture(path, Authority::System, Inspection::Cache, budget)?;
            Ok((Some(captured.file), captured.cache.ok_or("GNU cache inventory is absent")?))
        }
    }
}

fn loader_search(loader: &FileIdentity, interpreter: &str) -> Result<super::LoaderSearch, String> {
    let mut command = Command::new(&loader.target);
    command.arg("--list-diagnostics").env_clear().current_dir("/").stdin(Stdio::null());
    let output = crate::bounded_process::output(
        &mut command,
        "canonical GNU loader search configuration",
        super::super::TRUSTD_RUNTIME_INSPECTOR_MAX_STREAM_BYTES,
        super::super::TRUSTD_RUNTIME_INSPECTOR_TIMEOUT,
    )?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!("canonical GNU loader search diagnostics failed ({})", output.status));
    }
    let output = String::from_utf8(output.stdout)
        .map_err(|_| "GNU loader search diagnostics are not UTF-8")?;
    super::search::diagnostics(&output, interpreter)
}

fn configuration(path: &str, budget: &mut Budget) -> Result<Option<FileIdentity>, String> {
    match std::fs::symlink_metadata(path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(format!("Linux loader configuration: {error}")),
        Ok(_) => {
            let file = capture(Path::new(path), Authority::System, Inspection::Hash, budget)?.file;
            if path.ends_with("preload") && file.bytes != 0 {
                return Err(
                    "Linux release runtime requires absent or empty /etc/ld.so.preload".into()
                );
            }
            Ok(Some(file))
        }
    }
}

fn loader_output(loader: &FileIdentity, candidate: &Path) -> Result<String, String> {
    let mut command = Command::new(&loader.target);
    command.arg("--list").arg(candidate).env_clear().current_dir("/").stdin(Stdio::null());
    let output = crate::bounded_process::output(
        &mut command,
        "canonical trustd GNU loader inspection",
        super::super::TRUSTD_RUNTIME_INSPECTOR_MAX_STREAM_BYTES,
        super::super::TRUSTD_RUNTIME_INSPECTOR_TIMEOUT,
    )?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!("canonical GNU loader inspection failed ({})", output.status));
    }
    String::from_utf8(output.stdout).map_err(|_| "GNU loader listing is not UTF-8".into())
}

fn runtime_objects(
    rows: Vec<(String, String)>,
    candidate: &FileIdentity,
    loader: Captured,
    budget: &mut Budget,
) -> Result<Vec<SystemObject>, String> {
    let loader_name = Path::new(&loader.file.path)
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("Linux loader has no canonical name")?
        .to_owned();
    let loader_metadata = loader.elf.ok_or("Linux loader metadata is absent")?;
    if loader_metadata.interpreter.is_some() {
        return Err("Linux runtime loader must not have its own interpreter".into());
    }
    let mut objects = Vec::<SystemObject>::new();
    for (name, path) in rows {
        let target =
            std::fs::canonicalize(&path).map_err(|error| format!("GNU runtime object: {error}"))?;
        if target == Path::new(&candidate.target) {
            if name != candidate.path && name != candidate.target {
                return Err("GNU runtime self record has a foreign name".into());
            }
            continue;
        }
        if target == Path::new(&loader.file.target) {
            if name != loader_name && name != loader.file.path && name != loader.file.target {
                return Err("GNU runtime interpreter record has a foreign name".into());
            }
            continue;
        }
        if !super::system_path(&path)
            || !linux_elf::valid_soname(&name)
            || objects.iter().any(|object| object.name == name)
        {
            return Err("GNU runtime record is duplicate or outside system authority".into());
        }
        let captured = capture(Path::new(&path), Authority::System, Inspection::Elf, budget)?;
        if !super::system_path(&captured.file.target) {
            return Err("Linux runtime redirects outside system libraries".into());
        }
        let metadata = captured.elf.ok_or("Linux dependency ELF metadata is absent")?;
        if metadata.interpreter.is_some() {
            return Err("Linux runtime dependency has an executable interpreter".into());
        }
        objects.push(SystemObject { name, file: captured.file, needed: metadata.needed });
    }
    objects.push(SystemObject {
        name: loader_name,
        file: loader.file,
        needed: loader_metadata.needed,
    });
    Ok(objects)
}

pub(crate) fn inspect(candidate: &Path) -> Result<TrustdRuntimeClosure, String> {
    let candidate = super::super::validate_trustd_candidate_authority(candidate)?;
    let mut budget = Budget { remaining: 2 * 1024 * 1024 * 1024 };
    let (cache, cache_entries) = cache_configuration(&mut budget)?;
    let preload = configuration("/etc/ld.so.preload", &mut budget)?;
    let source = capture(&candidate, Authority::Candidate, Inspection::Elf, &mut budget)?;
    let metadata = source.elf.ok_or("Linux candidate ELF metadata is absent")?;
    let interpreter = metadata.interpreter.as_deref().ok_or(
        "Linux trustd runtime currently requires the explicit GNU system interpreter; static candidates have no admitted runtime evidence",
    )?;
    if interpreter != super::interpreter_for(metadata.machine)? {
        return Err(
            "Linux trustd candidate does not bind the supported host system interpreter".into()
        );
    }
    let loader = capture(Path::new(interpreter), Authority::System, Inspection::Elf, &mut budget)?;
    if !super::system_path(&loader.file.target) || loader.file.mode & 0o111 == 0 {
        return Err("Linux trustd system interpreter target is not admitted".into());
    }
    let loader_path = loader.file.target.clone();
    let loader_sha256 = loader.file.sha256.clone();
    let loader_configuration = loader_search(&loader.file, interpreter)?;
    let directories = super::search::directories(&loader_configuration)?;
    let directory_entries = super::authority::census(&directories)?;
    // Protect every cached target and every possible existing default/hwcaps
    // entry BEFORE asking GNU to inspect the candidate. Missing targets retain
    // their nearest immutable root parent, rather than becoming an exception.
    let initial_requests = super::search::requests(
        &loader_configuration,
        interpreter,
        &cache_entries,
        &directory_entries,
        &metadata.needed,
    )?;
    let initial_paths = super::authority::observe(&initial_requests)?;
    super::validation::validate_interpreter_authority(&initial_paths, &loader.file)?;
    let output = loader_output(&loader.file, &candidate)?;
    let rows = super::loader_rows(&output, metadata.needed.is_empty())?;
    let objects = runtime_objects(rows, &source.file, loader, &mut budget)?;
    let mut names = std::collections::BTreeSet::new();
    names.extend(metadata.needed.iter().cloned());
    for object in &objects {
        names.insert(object.name.clone());
        names.extend(object.needed.iter().cloned());
    }
    let names = names.into_iter().collect::<Vec<_>>();
    let requests = super::search::requests(
        &loader_configuration,
        interpreter,
        &cache_entries,
        &directory_entries,
        &names,
    )?;
    let paths = super::authority::observe(&requests)?;
    for object in &objects {
        let after =
            capture(Path::new(&object.file.path), Authority::System, Inspection::Elf, &mut budget)?;
        if after.file != object.file
            || after.elf.ok_or("missing final object metadata")?.needed != object.needed
        {
            return Err("Linux runtime object changed around loader inspection".into());
        }
    }
    let (final_cache, final_entries) = cache_configuration(&mut budget)?;
    let final_loader = objects
        .iter()
        .find(|object| object.file.target == loader_path)
        .ok_or("GNU runtime omitted its original loader")?;
    if final_cache != cache
        || final_entries != cache_entries
        || configuration("/etc/ld.so.preload", &mut budget)? != preload
        || capture(&candidate, Authority::Candidate, Inspection::Elf, &mut budget)?.file
            != source.file
        || loader_search(&final_loader.file, interpreter)? != loader_configuration
        || super::authority::census(&directories)? != directory_entries
        || super::authority::observe(&requests)? != paths
    {
        return Err(
            "Linux candidate or loader configuration changed during runtime inspection".into()
        );
    }
    super::super::validate_trustd_candidate_authority(&candidate)?;
    let record = LinuxRuntimeClosure {
        machine: metadata.machine,
        candidate_sha256: source.file.sha256,
        interpreter: interpreter.to_owned(),
        needed: metadata.needed,
        objects,
        loader_cache: cache,
        loader_preload: preload,
        search_authority: SearchAuthority {
            loader: loader_configuration,
            cache_entries,
            directory_entries,
            paths,
        },
    };
    TrustdRuntimeClosure::from_linux_observation(loader_path, loader_sha256, record)
}
