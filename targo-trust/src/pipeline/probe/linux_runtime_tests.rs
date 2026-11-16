use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;

use super::super::{
    TrustdRuntimeClosure, apply_trustd_runtime_closure, inspect_trustd_runtime_closure,
};
use super::*;

fn file(path: &str, target: &str, byte: char) -> FileIdentity {
    FileIdentity {
        path: path.to_owned(),
        target: target.to_owned(),
        device: 1,
        inode: 2,
        mode: 0o755,
        bytes: 1024,
        sha256: byte.to_string().repeat(64),
    }
}

fn example() -> (LinuxRuntimeClosure, String, String) {
    let machine = host_machine().expect("supported test host");
    let interpreter = interpreter_for(machine).expect("known interpreter").to_owned();
    let loader_name = interpreter.rsplit('/').next().expect("loader name").to_owned();
    let directory =
        if machine == 183 { "/usr/lib/aarch64-linux-gnu" } else { "/usr/lib/x86_64-linux-gnu" };
    let loader_target = format!("{directory}/{loader_name}");
    let loader_sha = "c".repeat(64);
    let mut record = LinuxRuntimeClosure {
        machine,
        candidate_sha256: "a".repeat(64),
        interpreter: interpreter.clone(),
        needed: vec!["libc.so.6".into()],
        objects: vec![
            SystemObject {
                name: "libc.so.6".into(),
                file: file(
                    &format!("{directory}/libc.so.6"),
                    &format!("{directory}/libc.so.6"),
                    'b',
                ),
                needed: vec![loader_name.clone()],
            },
            SystemObject {
                name: loader_name,
                file: file(&interpreter, &loader_target, 'c'),
                needed: vec![],
            },
        ],
        loader_cache: None,
        loader_preload: None,
        search_authority: SearchAuthority {
            loader: LoaderSearch {
                glibc_version: "2.39".into(),
                system_directories: vec![directory.into(), "/lib".into()],
                hwcaps_subdirectories: vec![],
            },
            cache_entries: vec![],
            directory_entries: vec![],
            paths: vec![],
        },
    };
    rebind_synthetic_sources(&mut record);
    (record, loader_target, loader_sha)
}

fn rebind_synthetic_sources(record: &mut LinuxRuntimeClosure) {
    let mut names = std::collections::BTreeSet::new();
    names.extend(record.needed.iter().cloned());
    for object in &record.objects {
        names.insert(object.name.clone());
        names.extend(object.needed.iter().cloned());
    }
    let names = names.into_iter().collect::<Vec<_>>();
    let search = &mut record.search_authority;
    let requests = search::requests(
        &search.loader,
        &record.interpreter,
        &search.cache_entries,
        &search.directory_entries,
        &names,
    )
    .expect("synthetic lookup plan");
    let mut nodes = std::collections::BTreeMap::new();
    for directory in search.loader.system_directories.iter().map(String::as_str).chain(["/etc"]) {
        for path in std::path::Path::new(directory).ancestors() {
            let path = path.to_str().expect("synthetic directory");
            nodes.insert(
                path.to_owned(),
                AuthorityNode {
                    path: path.into(),
                    kind: AuthorityKind::Directory,
                    device: 1,
                    inode: 1,
                    uid: 0,
                    gid: 0,
                    mode: 0o755,
                    link: None,
                },
            );
        }
    }
    for file in record
        .objects
        .iter()
        .map(|object| &object.file)
        .chain(record.loader_cache.iter())
        .chain(record.loader_preload.iter())
    {
        for file_path in [&file.path, &file.target] {
            for parent in
                std::path::Path::new(file_path).parent().expect("absolute file parent").ancestors()
            {
                let path = parent.to_str().expect("synthetic parent");
                nodes.insert(
                    path.into(),
                    AuthorityNode {
                        path: path.into(),
                        kind: AuthorityKind::Directory,
                        device: 1,
                        inode: 1,
                        uid: 0,
                        gid: 0,
                        mode: 0o755,
                        link: None,
                    },
                );
            }
        }
        nodes.insert(
            file.target.clone(),
            AuthorityNode {
                path: file.target.clone(),
                kind: AuthorityKind::Object,
                device: file.device,
                inode: file.inode,
                uid: 0,
                gid: 0,
                mode: file.mode,
                link: None,
            },
        );
        if file.path != file.target {
            nodes.insert(
                file.path.clone(),
                AuthorityNode {
                    path: file.path.clone(),
                    kind: AuthorityKind::Symlink,
                    device: 1,
                    inode: 3,
                    uid: 0,
                    gid: 0,
                    mode: 0o777,
                    link: Some(file.target.clone()),
                },
            );
        }
    }
    let mut read =
        |path: &std::path::Path| Ok(nodes.get(path.to_str().expect("test path")).cloned());
    search.paths = requests
        .iter()
        .map(|(path, kind)| {
            authority::resolve(path, *kind, &mut read).expect("synthetic root source")
        })
        .collect();
}

#[test]
fn linux_schema_requires_unselected_cache_targets_and_their_negative_authority() {
    let (mut record, inspector, hash) = example();
    record.loader_cache = Some(file("/etc/ld.so.cache", "/etc/ld.so.cache", 'd'));
    record.search_authority.cache_entries.push(CacheEntry {
        name: "unused.so".into(),
        path: "/lib/not-installed/unused.so".into(),
        flags: 0xffff,
        hwcap: 17,
    });
    rebind_synthetic_sources(&mut record);
    seal(record.clone(), inspector.clone(), hash.clone())
        .expect("complete root-protected negative cache target");
    let index = record
        .search_authority
        .paths
        .iter()
        .position(|path| path.path == "/lib/not-installed/unused.so")
        .expect("unselected cache target");
    record.search_authority.paths.remove(index);
    assert!(seal(record, inspector, hash).is_err(), "rehashing cannot omit an unselected source");
}

#[test]
fn linux_schema_refuses_other_uid_or_writable_negative_parent_even_after_rehash() {
    let (record, inspector, hash) = example();
    for changed in [0, 1] {
        let mut record = record.clone();
        let path = record
            .search_authority
            .paths
            .iter_mut()
            .find(|path| !path.present && path.path.starts_with("/lib/"))
            .expect("negative default source");
        let node = path.nodes.iter_mut().find(|node| node.path == "/lib").expect("nearest parent");
        if changed == 0 {
            node.uid = 1001;
        } else {
            node.mode = 0o775;
        }
        assert!(seal(record, inspector.clone(), hash.clone()).is_err());
    }
}

#[test]
fn linux_digest_binds_the_opened_authority_of_missing_search_targets() {
    let (record, inspector, hash) = example();
    let mut closure = seal(record, inspector, hash).expect("complete source authority");
    let record = closure.linux_elf.as_mut().expect("Linux record");
    let path = record
        .search_authority
        .paths
        .iter_mut()
        .find(|path| !path.present && path.path.starts_with("/lib/"))
        .expect("negative default source");
    path.nodes.iter_mut().find(|node| node.path == "/lib").expect("nearest parent").inode += 1;
    assert!(
        closure.validate().is_err(),
        "unchanged SONAMEs and object hashes do not preserve a changed authority digest"
    );
}

#[test]
fn linux_schema_requires_each_loaded_object_to_have_an_admitted_resolution_source() {
    let (mut record, inspector, hash) = example();
    record.objects[0].file.path = "/usr/lib/unexplained.so".into();
    record.objects[0].file.target = "/usr/lib/unexplained.so".into();
    assert!(
        seal(record, inspector, hash).is_err(),
        "root ownership does not explain how a SONAME resolved"
    );
}
fn seal(
    record: LinuxRuntimeClosure,
    inspector: String,
    hash: String,
) -> Result<TrustdRuntimeClosure, String> {
    TrustdRuntimeClosure::from_linux_observation(inspector, hash, record)
}

#[test]
fn linux_schema_requires_the_original_interpreter_path_even_without_a_default_alias() {
    let (mut record, inspector, hash) = example();
    seal(record.clone(), inspector.clone(), hash.clone()).expect("complete named loader authority");
    let index = record
        .search_authority
        .paths
        .iter()
        .position(|path| path.path == record.interpreter)
        .expect("kernel interpreter is an independent authority source");
    record.search_authority.paths.remove(index);
    assert!(
        seal(record, inspector, hash).is_err(),
        "canonical DSO sources cannot replace the original interpreter path"
    );
}

#[test]
fn linux_schema_couples_named_interpreter_authority_to_the_opened_loader_inode() {
    let (record, inspector, hash) = example();
    for changed in [0, 1, 2] {
        let mut record = record.clone();
        let loader = record
            .objects
            .iter_mut()
            .find(|object| object.file.path == record.interpreter)
            .expect("original loader identity");
        match changed {
            0 => loader.file.device += 1,
            1 => loader.file.inode += 1,
            _ => loader.file.mode = 0o555,
        }
        assert!(
            seal(record, inspector.clone(), hash.clone()).is_err(),
            "same canonical path and hash do not identify a different opened file"
        );
    }
}

#[test]
fn linux_interpreter_resolution_refuses_another_uid_intermediate_symlink_relay() {
    let (record, _, _) = example();
    let file = &record
        .objects
        .iter()
        .find(|object| object.file.path == record.interpreter)
        .expect("original interpreter")
        .file;
    let mut nodes = record
        .search_authority
        .paths
        .iter()
        .flat_map(|path| &path.nodes)
        .map(|node| (node.path.clone(), node.clone()))
        .collect::<std::collections::BTreeMap<_, _>>();
    nodes.get_mut(&record.interpreter).expect("named root-owned symlink").link =
        Some("/interpreter-relay/forward".into());
    nodes.insert(
        "/interpreter-relay".into(),
        AuthorityNode {
            path: "/interpreter-relay".into(),
            kind: AuthorityKind::Directory,
            device: 1,
            inode: 4,
            uid: 1001,
            gid: 1001,
            mode: 0o755,
            link: None,
        },
    );
    nodes.insert(
        "/interpreter-relay/forward".into(),
        AuthorityNode {
            path: "/interpreter-relay/forward".into(),
            kind: AuthorityKind::Symlink,
            device: 1,
            inode: 5,
            uid: 0,
            gid: 0,
            mode: 0o777,
            link: Some(file.target.clone()),
        },
    );
    let resolve = |nodes: &std::collections::BTreeMap<String, AuthorityNode>| {
        authority::resolve(&record.interpreter, AuthorityKind::Object, &mut |path| {
            Ok(nodes.get(path.to_str().expect("test path")).cloned())
        })
    };
    assert!(
        resolve(&nodes).is_err(),
        "root-owned named and canonical endpoints do not protect an other-UID relay"
    );
    nodes.get_mut("/interpreter-relay").expect("relay parent").uid = 0;
    let path = resolve(&nodes).expect("the same full chain is admitted when root-controlled");
    assert_eq!(path.target, file.target);
    validation::validate_interpreter_authority(&[path], file)
        .expect("resolved exact opened loader");
}

#[test]
fn linux_schema_binds_transitive_objects_and_cannot_be_macho_v2() {
    let (record, inspector, hash) = example();
    let mut closure = seal(record, inspector, hash).expect("complete typed Linux observation");
    closure.validate().expect("Linux schema");
    assert_eq!(closure.schema_version, SCHEMA);
    assert_eq!(closure.native_format, FORMAT);
    assert!(closure.search_paths.is_empty() && closure.directory_entries.is_empty());
    closure.schema_version = super::super::TRUSTD_RUNTIME_CLOSURE_SCHEMA.to_owned();
    closure.closure_sha256 = closure.calculated_sha256().expect("rehash malformed variant");
    assert!(closure.validate().is_err(), "Linux data must never become Mach-O evidence");
}

#[test]
fn linux_schema_refuses_unresolved_or_unreachable_loaded_objects() {
    let (mut record, inspector, hash) = example();
    record.objects[0].needed.push("missing.so".into());
    assert!(seal(record, inspector, hash).is_err());
    let (mut record, inspector, hash) = example();
    record.objects.push(SystemObject {
        name: "injected.so".into(),
        file: file("/usr/lib/injected.so", "/usr/lib/injected.so", 'e'),
        needed: vec![],
    });
    assert!(seal(record, inspector, hash).is_err(), "unreachable preload-like object");
}

#[test]
fn linux_schema_rejects_foreign_duplicate_or_writable_objects() {
    let (record, inspector, hash) = example();
    for changed in [0, 1, 2, 3] {
        let mut fresh = record.clone();
        match changed {
            0 => fresh.objects[0].file.target = "/home/owner/lib.so".into(),
            1 => fresh.objects.push(fresh.objects[0].clone()),
            2 => fresh.objects[0].file.mode = 0o775,
            _ => fresh.objects[0].name = "../libc.so.6".into(),
        }
        assert!(seal(fresh, inspector.clone(), hash.clone()).is_err());
    }
}

#[test]
fn linux_schema_requires_the_actual_host_interpreter() {
    let (mut record, inspector, hash) = example();
    record.interpreter = "/usr/local/lib/ld.so".into();
    assert!(seal(record, inspector, hash).is_err());
    let (record, inspector, _) = example();
    assert!(seal(record, inspector, "f".repeat(64)).is_err(), "loader hash must agree");
}

#[test]
fn linux_digest_covers_candidate_config_object_hashes_and_order() {
    let (record, inspector, hash) = example();
    let closure = seal(record, inspector, hash).expect("complete observation");
    for changed in [0, 1, 2, 3] {
        let mut fresh = closure.clone();
        let record = fresh.linux_elf.as_mut().expect("Linux observation");
        match changed {
            0 => record.candidate_sha256 = "d".repeat(64),
            1 => record.objects[0].file.sha256 = "d".repeat(64),
            2 => record.loader_cache = Some(file("/etc/ld.so.cache", "/etc/ld.so.cache", 'd')),
            _ => record.objects.swap(0, 1),
        }
        assert!(fresh.validate().is_err(), "changed runtime data escaped digest/order");
    }
}

#[test]
fn linux_configuration_never_admits_preload_bytes() {
    let (mut record, inspector, hash) = example();
    record.loader_preload = Some(file("/etc/ld.so.preload", "/etc/ld.so.preload", 'd'));
    assert!(seal(record, inspector, hash).is_err());
    let (mut record, inspector, hash) = example();
    let mut empty = file("/etc/ld.so.preload", "/etc/ld.so.preload", 'd');
    empty.bytes = 0;
    record.loader_preload = Some(empty);
    let path = record
        .search_authority
        .paths
        .iter_mut()
        .find(|path| path.path == "/etc/ld.so.preload")
        .expect("preload authority");
    path.present = true;
    path.nodes.push(AuthorityNode {
        path: path.target.clone(),
        kind: AuthorityKind::Object,
        device: 1,
        inode: 2,
        uid: 0,
        gid: 0,
        mode: 0o755,
        link: None,
    });
    assert!(seal(record, inspector, hash).is_ok(), "empty root-bound configuration is data");
}

#[test]
fn loader_records_preserve_names_and_omit_only_one_kernel_vdso() {
    let rows = loader_rows("\tlinux-vdso.so.1 (0xffff0000)\n\tlibc.so.6 => /lib/libc.so.6 (0x1234)\n\t/lib/ld.so (0xabcd)\n", false)
        .expect("closed GNU loader grammar");
    assert_eq!(
        rows,
        [("libc.so.6".into(), "/lib/libc.so.6".into()), ("/lib/ld.so".into(), "/lib/ld.so".into())]
    );
}

#[test]
fn loader_marker_requires_independently_empty_needed_and_cannot_mix_rows() {
    assert!(loader_rows("\tstatically linked\n", true).expect("no-needed marker").is_empty());
    for (output, no_needed) in [
        ("statically linked", false),
        ("statically linked\n/lib/ld.so (0x1)", true),
        ("", true),
        ("linux-vdso.so.1 (0x1)\nlinux-vdso.so.1 (0x2)", true),
    ] {
        assert!(loader_rows(output, no_needed).is_err());
    }
}

#[test]
fn loader_refuses_unknown_missing_relative_and_ambiguous_records() {
    for output in [
        "libx.so => not found",
        "libx.so => relative.so (0x1)",
        "libx.so => /lib/../tmp/lib.so (0x1)",
        "/lib/ld.so (garbage)",
        "libx.so => /lib/lib.so (0x)",
        "unknown record",
        "../lib.so => /lib/lib.so (0x1)",
    ] {
        assert!(loader_rows(output, false).is_err(), "accepted {output}");
    }
}

struct NativeFixture {
    _directory: tempfile::TempDir,
    candidate: PathBuf,
}
impl NativeFixture {
    fn new() -> Self {
        // The candidate's authority requires a real user-owned path beneath an
        // immutable root prefix. A global temporary directory is not that path.
        let directory = tempfile::Builder::new()
            .prefix(".trustd-linux-runtime-test-")
            .tempdir_in(std::env::current_dir().expect("owned test source directory"))
            .expect("private runtime fixture");
        let candidate = directory.path().join("trustd");
        std::fs::copy("/usr/bin/true", &candidate).expect("real native ELF fixture");
        std::fs::set_permissions(&candidate, std::fs::Permissions::from_mode(0o700))
            .expect("fixture authority");
        Self { _directory: directory, candidate }
    }
}

#[test]
fn actual_linux_fixture_reinspects_and_launches_with_cleared_environment() {
    let fixture = NativeFixture::new();
    let closure =
        inspect_trustd_runtime_closure(&fixture.candidate).expect("real GNU loader observation");
    assert_eq!(closure.native_format, FORMAT);
    assert!(!closure.system_dependencies.is_empty());
    let runtime = closure.linux_elf.as_ref().expect("Linux source inventory");
    for entry in &runtime.search_authority.cache_entries {
        assert!(runtime.search_authority.paths.iter().any(|path| path.path == entry.path));
    }
    assert!(!runtime.search_authority.loader.system_directories.is_empty());
    let loader = runtime
        .objects
        .iter()
        .find(|object| object.file.path == runtime.interpreter)
        .expect("original interpreter");
    validation::validate_interpreter_authority(&runtime.search_authority.paths, &loader.file)
        .expect("normal kernel exec reaches the exact hashed loader inode");
    let mut command = std::process::Command::new(&fixture.candidate);
    command.env("LD_PRELOAD", "/untrusted/ignored.so").env("PATH", "/untrusted");
    apply_trustd_runtime_closure(&mut command, &fixture.candidate, &closure)
        .expect("fresh real observation");
    assert_eq!(command.get_envs().count(), 0);
    assert!(command.status().expect("execute original native fixture").success());
}

#[test]
fn actual_linux_fixture_rejects_rehashed_forgery_and_candidate_mutation() {
    let fixture = NativeFixture::new();
    let closure =
        inspect_trustd_runtime_closure(&fixture.candidate).expect("real runtime observation");
    let mut forged = closure.clone();
    forged.linux_elf.as_mut().expect("Linux observation").objects[0].file.sha256 = "e".repeat(64);
    forged.closure_sha256 =
        forged.calculated_sha256().expect("internally consistent forged digest");
    // If the first object is the loader, its common inspector hash must agree
    // too before this is an internally valid data record.
    if forged.linux_elf.as_ref().expect("Linux observation").objects[0].file.target
        == forged.inspector_path
    {
        forged.inspector_sha256 = "e".repeat(64);
        forged.closure_sha256 = forged.calculated_sha256().expect("rebind forged loader digest");
    }
    forged.validate().expect("valid data is not actual candidate evidence");
    assert!(forged.validate_for_candidate(&fixture.candidate).is_err());
    std::fs::OpenOptions::new()
        .append(true)
        .open(&fixture.candidate)
        .expect("owned candidate")
        .write_all(&[0])
        .expect("append ELF-irrelevant byte");
    assert!(
        closure.validate_for_candidate(&fixture.candidate).is_err(),
        "candidate bytes must bind beyond ELF fields"
    );
}

#[test]
fn actual_linux_candidate_authority_refuses_redirect_and_writable_leaf() {
    let fixture = NativeFixture::new();
    let redirected = fixture._directory.path().join("redirect");
    std::os::unix::fs::symlink(&fixture.candidate, &redirected).expect("owned redirected path");
    assert!(inspect_trustd_runtime_closure(&redirected).is_err());
    std::fs::set_permissions(&fixture.candidate, std::fs::Permissions::from_mode(0o770))
        .expect("owned writable leaf");
    assert!(inspect_trustd_runtime_closure(&fixture.candidate).is_err());
}
