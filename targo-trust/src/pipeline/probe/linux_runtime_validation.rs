use std::collections::{BTreeMap, BTreeSet};

use super::super::linux_elf;
use super::{FileIdentity, LinuxRuntimeClosure};

pub(in super::super) fn normalized_path(path: &str) -> bool {
    path.starts_with('/')
        && path.len() <= 4096
        && !path.contains("//")
        && !path.chars().any(char::is_control)
        && !path.split('/').skip(1).any(|part| part.is_empty() || part == "." || part == "..")
}

pub(in super::super) fn system_path(path: &str) -> bool {
    normalized_path(path)
        && ["/lib/", "/lib64/", "/usr/lib/", "/usr/lib64/"]
            .iter()
            .any(|prefix| path.starts_with(prefix))
}

pub(in super::super) fn interpreter_for(machine: u16) -> Result<&'static str, String> {
    match machine {
        62 => Ok("/lib64/ld-linux-x86-64.so.2"),
        183 => Ok("/lib/ld-linux-aarch64.so.1"),
        _ => Err("Linux trustd runtime machine is unsupported".into()),
    }
}

pub(in super::super) fn host_machine() -> Result<u16, String> {
    match std::env::consts::ARCH {
        "aarch64" => Ok(183),
        "x86_64" => Ok(62),
        _ => Err("Linux trustd runtime host is unsupported".into()),
    }
}

fn check_file(file: &FileIdentity) -> Result<(), String> {
    if !normalized_path(&file.path)
        || !normalized_path(&file.target)
        || file.mode & !0o7777 != 0
        || file.mode & 0o022 != 0
        || file.inode == 0
        || file.bytes > 512 * 1024 * 1024
        || !trust_types::digest::is_stable_sha256_hex(&file.sha256)
    {
        return Err("Linux trustd runtime has invalid file identity".into());
    }
    Ok(())
}

fn binds_opened_file(path: &super::PathAuthority, file: &FileIdentity) -> bool {
    path.present
        && path.kind == super::AuthorityKind::Object
        && path.target == file.target
        && path.nodes.iter().any(|node| {
            node.path == path.target
                && node.kind == super::AuthorityKind::Object
                && node.device == file.device
                && node.inode == file.inode
                && node.mode == file.mode
        })
}

pub(super) fn validate_interpreter_authority(
    paths: &[super::PathAuthority],
    file: &FileIdentity,
) -> Result<(), String> {
    if !paths.iter().any(|path| path.path == file.path && binds_opened_file(path, file)) {
        return Err("GNU named interpreter authority does not bind its exact opened loader".into());
    }
    Ok(())
}

fn check_needed(needed: &[String]) -> Result<(), String> {
    if needed.len() > 256 {
        return Err("Linux runtime dependency count exceeds the bound".into());
    }
    let mut seen = BTreeSet::new();
    for name in needed {
        if !linux_elf::valid_soname(name) || !seen.insert(name) {
            return Err("Linux runtime has a duplicate or invalid SONAME".into());
        }
    }
    Ok(())
}

pub(in super::super) fn validate(
    record: &LinuxRuntimeClosure,
    inspector: &str,
    inspector_sha256: &str,
    dependencies: &[String],
) -> Result<(), String> {
    if !cfg!(target_os = "linux")
        || record.machine != host_machine()?
        || record.interpreter != interpreter_for(record.machine)?
        || !system_path(inspector)
        || !trust_types::digest::is_stable_sha256_hex(inspector_sha256)
        || !trust_types::digest::is_stable_sha256_hex(&record.candidate_sha256)
        || record.objects.is_empty()
        || record.objects.len() > 256
    {
        return Err("Linux runtime closure does not bind this host and its system loader".into());
    }
    check_needed(&record.needed)?;
    let mut objects = BTreeMap::new();
    let mut targets = BTreeSet::new();
    for object in &record.objects {
        check_file(&object.file)?;
        check_needed(&object.needed)?;
        if !linux_elf::valid_soname(&object.name)
            || !system_path(&object.file.path)
            || !system_path(&object.file.target)
            || objects.insert(object.name.as_str(), object).is_some()
            || !targets.insert(object.file.target.as_str())
        {
            return Err("Linux runtime object set has duplicate or foreign identities".into());
        }
    }
    let loader_name = record.interpreter.rsplit('/').next().ok_or("missing loader name")?;
    let loader = objects.get(loader_name).ok_or("Linux runtime omitted its loader object")?;
    if loader.file.path != record.interpreter
        || loader.file.target != inspector
        || loader.file.sha256 != inspector_sha256
        || loader.file.mode & 0o111 == 0
    {
        return Err("Linux runtime inspector and actual interpreter identities differ".into());
    }
    if !dependencies
        .iter()
        .map(String::as_str)
        .eq(record.objects.iter().map(|object| object.file.target.as_str()))
    {
        return Err(
            "Linux runtime dependency order does not bind the complete observed object set".into(),
        );
    }
    let mut pending = vec![loader_name];
    pending.extend(record.needed.iter().map(String::as_str));
    let mut reached = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if reached.insert(name) {
            let object =
                objects.get(name).ok_or("Linux runtime has an unresolved transitive SONAME")?;
            pending.extend(object.needed.iter().map(String::as_str));
        }
    }
    if reached.len() != objects.len() {
        return Err("Linux runtime has an object outside the original dependency closure".into());
    }
    for (file, expected) in
        [(&record.loader_cache, "/etc/ld.so.cache"), (&record.loader_preload, "/etc/ld.so.preload")]
    {
        if let Some(file) = file {
            check_file(file)?;
            if file.path != expected || (expected.ends_with("preload") && file.bytes != 0) {
                return Err(
                    "Linux runtime has an unbound loader configuration or preload authority".into(),
                );
            }
        }
    }
    validate_search_authority(record)?;
    Ok(())
}

fn validate_search_authority(record: &LinuxRuntimeClosure) -> Result<(), String> {
    let authority = &record.search_authority;
    if record.loader_cache.is_none() && !authority.cache_entries.is_empty() {
        return Err("GNU runtime has cached targets without a cache file".into());
    }
    let mut names = BTreeSet::new();
    names.extend(record.needed.iter().cloned());
    for object in &record.objects {
        names.insert(object.name.clone());
        names.extend(object.needed.iter().cloned());
    }
    let names = names.into_iter().collect::<Vec<_>>();
    let expected = super::search::requests(
        &authority.loader,
        &record.interpreter,
        &authority.cache_entries,
        &authority.directory_entries,
        &names,
    )?;
    if expected.len() != authority.paths.len() {
        return Err("GNU runtime omitted a positive or negative resolution source".into());
    }
    let mut total_nodes = 0usize;
    let mut total_text = 0usize;
    let mut global_nodes = BTreeMap::new();
    for ((name, kind), path) in expected.iter().zip(&authority.paths) {
        super::authority::account(path, &mut total_nodes, &mut total_text)?;
        if path.path != *name
            || path.kind != *kind
            || !super::normalized_path(&path.target)
            || path.nodes.len() > super::search::MAX_NODES
        {
            return Err("GNU runtime resolution authority has unbound paths or roles".into());
        }
        let mut nodes = BTreeMap::new();
        for node in &path.nodes {
            super::authority::validate_node(node)?;
            if let Some(previous) = global_nodes.insert(node.path.as_str(), node) {
                if previous != node {
                    return Err(
                        "GNU runtime authority has inconsistent observations of one named node"
                            .into(),
                    );
                }
            }
            if nodes.insert(node.path.as_str(), node).is_some() {
                return Err("GNU runtime resolution authority repeats a filesystem node".into());
            }
        }
        // Reconstruct the path from its recorded component observations. This
        // validates symlink traversal and the exact nearest existing parent;
        // actual filesystem authority still requires validate_for_candidate.
        let mut read = |requested: &std::path::Path| {
            Ok(nodes
                .get(requested.to_str().ok_or("GNU authority path is not UTF-8")?)
                .map(|node| (**node).clone()))
        };
        if super::authority::resolve(name, *kind, &mut read)? != *path {
            return Err("GNU runtime resolution authority does not reconstruct its path".into());
        }
    }
    for (named, identity) in
        [("/etc/ld.so.cache", &record.loader_cache), ("/etc/ld.so.preload", &record.loader_preload)]
    {
        let path = authority
            .paths
            .iter()
            .find(|path| path.path == named)
            .ok_or("GNU configuration authority is absent")?;
        if path.present != identity.is_some() {
            return Err("GNU configuration presence and path authority disagree".into());
        }
        if let Some(identity) = identity {
            if !binds_opened_file(path, identity) {
                return Err("GNU configuration digest and opened path authority disagree".into());
            }
        }
    }
    let directories = super::search::directories(&authority.loader)?;
    let loader_name =
        record.interpreter.rsplit('/').next().ok_or("GNU interpreter has no basename")?;
    for object in &record.objects {
        if object.name == loader_name {
            validate_interpreter_authority(&authority.paths, &object.file)?;
            continue;
        }
        let cached = authority
            .cache_entries
            .iter()
            .filter(|entry| entry.name == object.name)
            .map(|entry| entry.path.clone());
        let defaults = directories.iter().map(|directory| format!("{directory}/{}", object.name));
        if !cached.chain(defaults).any(|named| {
            authority
                .paths
                .iter()
                .any(|path| path.path == named && binds_opened_file(path, &object.file))
        }) {
            return Err(
                "GNU loaded object has no admitted cache or default-directory resolution source"
                    .into(),
            );
        }
    }
    Ok(())
}

/// Parse only the exact GNU loader listing grammar. Addresses are diagnostics;
/// the caller binds names to actual opened-file metadata and hashes.
pub(in super::super) fn loader_rows(
    output: &str,
    no_needed: bool,
) -> Result<Vec<(String, String)>, String> {
    let lines = output.lines().filter(|line| !line.trim().is_empty()).collect::<Vec<_>>();
    if lines.len() == 1 && lines[0].trim() == "statically linked" {
        return if no_needed {
            Ok(Vec::new())
        } else {
            Err("GNU loader marker contradicts DT_NEEDED".into())
        };
    }
    let mut result = Vec::new();
    let mut vdso = false;
    for line in lines {
        if result.len() == 256 {
            return Err("GNU loader listing exceeds the object bound".into());
        }
        let (body, address) = line.trim().rsplit_once(" (").ok_or("unknown GNU loader record")?;
        let address = address
            .strip_suffix(')')
            .and_then(|address| address.strip_prefix("0x"))
            .filter(|address| {
                !address.is_empty() && address.bytes().all(|byte| byte.is_ascii_hexdigit())
            })
            .ok_or("unknown GNU loader address record")?;
        if address.len() > 16 {
            return Err("GNU loader address width exceeds ELF64".into());
        }
        if body == "linux-vdso.so.1" {
            if std::mem::replace(&mut vdso, true) {
                return Err("duplicate GNU VDSO record".into());
            }
            continue;
        }
        let (name, path) = body.split_once(" => ").unwrap_or((body, body));
        if name.is_empty() || !normalized_path(path) || name.contains(" => ") {
            return Err("unknown, missing or ambiguous GNU loader resolution".into());
        }
        if !normalized_path(name) && !linux_elf::valid_soname(name) {
            return Err("invalid GNU loader object name".into());
        }
        result.push((name.to_owned(), path.to_owned()));
    }
    if result.is_empty() {
        return Err("GNU loader omitted its runtime object records".into());
    }
    Ok(result)
}
