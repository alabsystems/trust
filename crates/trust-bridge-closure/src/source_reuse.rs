//! Reuse original bridge artifacts only over independently read, equal inputs.
//!
//! A record selects objects to examine. It supplies no digest authority. The
//! original manifest, producer stamps and artifact bytes remain unchanged.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path};
use std::{fs, io};

use sha2::{Digest, Sha256};
use toml::Value;

use crate::snapshot::Git;

mod effective;
use effective::effective_reader_inputs;

pub const MANIFEST: &str = "crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml";
const SHIP: &str = "crates/trust-clean/fixtures/trustir-oleans";
const CORE: &str = "vendor/lean-core-oleans";
const PRODUCER: &str = "lean/trust_ir-semantics";
const RECORD: &str = "source_reuse";
const SCHEMA: &str = "trust.bridge-source-reuse.v1";

/// The actual source image to judge; a pushed tree never borrows the index.
pub enum Subject<'a> {
    /// Immutable commit selected by a caller such as the push hook.
    Commit(&'a str),
    /// The current index, captured once as an immutable tree object.
    Index,
    /// HEAD plus exact, clean selected checkouts and unchanged artifact files.
    Checkout,
}

/// Selected revisions after all input comparisons succeeded, not a proof token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Selection {
    pub trustir_commit: String,
    pub clean_commit: String,
    pub anchor_commit: String,
    /// Hashes of the complete bytes independently checked by this judgment,
    /// including the reuse record. Consumers must bind their captured parses.
    pub trustir_manifest_sha256: String,
    pub core_manifest_sha256: String,
}

fn invalid(message: impl std::fmt::Display) -> io::Error {
    io::Error::other(message.to_string())
}

fn require(ok: bool, message: &str) -> io::Result<()> {
    if ok { Ok(()) } else { Err(invalid(message)) }
}

fn oid(text: &str) -> io::Result<&str> {
    require(
        text.len() == 40 && text.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()),
        "reuse requires a full lowercase commit ID",
    )?;
    Ok(text)
}

fn string<'a>(doc: &'a Value, key: &str) -> io::Result<&'a str> {
    doc.get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid(format!("missing reuse input {key}")))
}

fn parse(bytes: &[u8]) -> io::Result<Value> {
    std::str::from_utf8(bytes).map_err(invalid)?.parse().map_err(invalid)
}

fn output(git: &Git, args: &[&str]) -> io::Result<String> {
    String::from_utf8(git.output(args)?).map(|s| s.trim().to_owned()).map_err(invalid)
}

fn blob(git: &Git, rev: &str, path: &str) -> io::Result<Vec<u8>> {
    relative(path)?;
    let entry = git.output(&["ls-tree", "-z", rev, "--", path])?;
    let entry = entry.strip_suffix(&[0]).ok_or_else(|| invalid("missing regular source input"))?;
    let row = std::str::from_utf8(entry).map_err(invalid)?;
    let (header, actual) =
        row.split_once('\t').ok_or_else(|| invalid("invalid source tree entry"))?;
    let parts: Vec<_> = header.split_whitespace().collect();
    require(
        actual == path
            && parts.len() == 3
            && matches!(parts[0], "100644" | "100755")
            && parts[1] == "blob",
        "source input must be an exact regular file",
    )?;
    let name = format!("{rev}:{path}");
    require(output(git, &["cat-file", "-t", &name])? == "blob", "reuse input is not a blob")?;
    git.output(&["cat-file", "blob", &name])
}

fn pin(git: &Git, rev: &str, path: &str) -> io::Result<String> {
    let listing = output(git, &["ls-tree", rev, "--", path])?;
    let parts: Vec<_> = listing.split_whitespace().collect();
    require(
        parts.len() == 4 && parts[0] == "160000" && parts[1] == "commit" && parts[3] == path,
        "reuse requires the exact selected submodule gitlink",
    )?;
    Ok(oid(parts[2])?.to_owned())
}

fn relative(path: &str) -> io::Result<()> {
    require(
        !path.is_empty()
            && !path.contains(['\\', '\0', '\n', '\r'])
            && Path::new(path).components().all(|c| matches!(c, Component::Normal(_)))
            && !path.split('/').any(|c| c.eq_ignore_ascii_case(".git")),
        "unsafe reuse input path",
    )
}

fn child_git(parent: &Git, root: &Path, tree: &str, path: &str, checkout: bool) -> io::Result<Git> {
    relative(path)?;
    if checkout {
        require(
            fs::canonicalize(root.join(path))? == root.join(path),
            "source checkout path is not its exact physical root",
        )?;
    }
    if let Ok(child) = Git::new(&root.join(path)) {
        return Ok(child.share_blob_reads(parent));
    }
    require(!checkout, "reuse requires an initialized exact source checkout")?;
    let modules = parse_gitmodules(parent, tree)?;
    let name = modules.get(path).ok_or_else(|| invalid("missing exact submodule declaration"))?;
    let common = parent.directory(&["rev-parse", "--path-format=absolute", "--git-common-dir"])?;
    let stores = common.join("modules");
    let selected = fs::canonicalize(stores.join(name))?;
    require(
        selected.starts_with(fs::canonicalize(&stores)?),
        "submodule object store escaped modules",
    )?;
    Git::store(&selected).map(|child| child.share_blob_reads(parent))
}

fn parse_gitmodules(git: &Git, tree: &str) -> io::Result<BTreeMap<String, String>> {
    let source = format!("{tree}:.gitmodules");
    let bytes = git.output(&[
        "config",
        "--blob",
        &source,
        "--null",
        "--get-regexp",
        "^submodule\\..*\\.path$",
    ])?;
    let mut result = BTreeMap::new();
    for row in bytes.split(|b| *b == 0).filter(|r| !r.is_empty()) {
        let row = std::str::from_utf8(row).map_err(invalid)?;
        let (key, path) =
            row.split_once('\n').ok_or_else(|| invalid("invalid submodule path row"))?;
        let name = key
            .strip_prefix("submodule.")
            .and_then(|k| k.strip_suffix(".path"))
            .ok_or_else(|| invalid("invalid submodule path key"))?;
        relative(name)?;
        relative(path)?;
        require(
            result.insert(path.to_owned(), name.to_owned()).is_none(),
            "duplicate submodule path",
        )?;
    }
    Ok(result)
}

// Full path -> (mode, blob). Trees, gitlinks and symlinks are never data inputs.
fn files(git: &Git, rev: &str, prefix: &str) -> io::Result<BTreeMap<String, (String, String)>> {
    let bytes = git.output(&["ls-tree", "-r", "-z", "--full-tree", rev, "--", prefix])?;
    let mut result = BTreeMap::new();
    for row in bytes.split(|b| *b == 0).filter(|r| !r.is_empty()) {
        let row = std::str::from_utf8(row).map_err(invalid)?;
        let (header, path) =
            row.split_once('\t').ok_or_else(|| invalid("invalid reuse tree row"))?;
        let fields: Vec<_> = header.split_whitespace().collect();
        relative(path)?;
        require(
            path.starts_with(&format!("{prefix}/"))
                && fields.len() == 3
                && matches!(fields[0], "100644" | "100755")
                && fields[1] == "blob",
            "reuse input tree contains an unsupported entry",
        )?;
        require(
            result
                .insert(path.to_owned(), (fields[0].to_owned(), oid(fields[2])?.to_owned()))
                .is_none(),
            "duplicate reuse input path",
        )?;
    }
    require(!result.is_empty() && result.len() <= 100_000, "empty or excessive reuse input tree")?;
    Ok(result)
}

fn equal_tree(git: &Git, before: &str, after: &str, prefix: &str) -> io::Result<()> {
    let old = files(git, before, prefix)?;
    require(old == files(git, after, prefix)?, "producer or reader input tree changed")?;
    // Read the actual objects as well: a missing blob is not equal evidence.
    for (_, hash) in old.values() {
        let _ = git.full_oid_blob(hash)?;
    }
    Ok(())
}

fn working_file(root: &Path, path: &str, bytes: &[u8], mode: &str) -> io::Result<()> {
    relative(path)?;
    let mut file = root.to_path_buf();
    for part in Path::new(path).components() {
        file.push(part);
        require(
            !fs::symlink_metadata(&file)?.file_type().is_symlink(),
            "symlink in working source input",
        )?;
    }
    let metadata = fs::metadata(&file)?;
    require(
        metadata.is_file() && fs::read(&file)? == bytes,
        "raw working source differs from selected object",
    )?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        require(
            (metadata.permissions().mode() & 0o111 != 0) == (mode == "100755"),
            "working source file mode differs from selected object",
        )?;
    }
    Ok(())
}

fn checkout_file(git: &Git, rev: &str, path: &str, root: &Path) -> io::Result<()> {
    let bytes = blob(git, rev, path)?;
    let entry = output(git, &["ls-tree", rev, "--", path])?;
    let mode = entry.split_whitespace().next().ok_or_else(|| invalid("missing source mode"))?;
    working_file(root, path, &bytes, mode)
}

fn checkout_tree(git: &Git, rev: &str, prefix: &str, root: &Path) -> io::Result<()> {
    for (path, (mode, hash)) in files(git, rev, prefix)? {
        working_file(root, &path, &git.full_oid_blob(&hash)?, &mode)?;
    }
    Ok(())
}

fn at<'a>(doc: &'a Value, keys: &[&str]) -> Option<&'a Value> {
    keys.iter().try_fold(doc, |value, key| value.get(*key))
}

fn reader_inputs(
    git: &Git,
    before: &str,
    after: &str,
    checkout: Option<&Path>,
) -> io::Result<BTreeMap<String, BTreeSet<String>>> {
    let old = parse(&blob(git, before, "Cargo.toml")?)?;
    let new = parse(&blob(git, after, "Cargo.toml")?)?;
    for key in ["patch", "profile"] {
        require(old.get(key) == new.get(key), "reader build policy changed")?;
    }
    for path in [".cargo/config.toml", "rust-toolchain.toml", "lean-toolchain"] {
        require(
            blob(git, before, path)? == blob(git, after, path)?,
            "reader toolchain or configuration changed",
        )?;
        if let Some(root) = checkout {
            checkout_file(git, after, path, root)?;
        }
    }
    let mut pending = vec!["crates/clean-olean".to_owned()];
    let mut seen = BTreeSet::new();
    let mut production = BTreeMap::<String, BTreeSet<String>>::new();
    while let Some(dir) = pending.pop() {
        if !seen.insert(dir.clone()) {
            continue;
        }
        require(seen.len() <= 128, "excessive reader path closure")?;
        equal_tree(git, before, after, &dir)?;
        if let Some(root) = checkout {
            checkout_tree(git, after, &dir, root)?;
        }
        let doc = parse(&blob(git, before, &format!("{dir}/Cargo.toml"))?)?;
        let package_name =
            string(doc.get("package").ok_or_else(|| invalid("missing reader package"))?, "name")?
                .to_owned();
        let mut names = BTreeSet::new();
        if let Some(package) = doc.get("package").and_then(Value::as_table) {
            for (key, value) in package {
                if value.get("workspace").and_then(Value::as_bool) == Some(true) {
                    require(
                        at(&old, &["workspace", "package", key])
                            == at(&new, &["workspace", "package", key]),
                        "reader inherited package input changed",
                    )?;
                }
            }
        }
        if at(&doc, &["lints", "workspace"]).and_then(Value::as_bool) == Some(true) {
            require(
                at(&old, &["workspace", "lints"]) == at(&new, &["workspace", "lints"]),
                "reader inherited lints changed",
            )?;
        }
        let mut blocks = vec![&doc];
        if let Some(targets) = doc.get("target").and_then(Value::as_table) {
            blocks.extend(targets.values());
        }
        for block in blocks {
            for section in ["dependencies", "build-dependencies"] {
                if let Some(deps) = block.get(section).and_then(Value::as_table) {
                    for (name, direct) in deps {
                        let inherited =
                            direct.get("workspace").and_then(Value::as_bool) == Some(true);
                        let spec = if inherited {
                            let keys = ["workspace", "dependencies", name];
                            require(
                                at(&old, &keys).is_some() && at(&old, &keys) == at(&new, &keys),
                                "reader inherited dependency changed",
                            )?;
                            at(&old, &keys).ok_or_else(|| invalid("missing reader dependency"))?
                        } else {
                            direct
                        };
                        names.insert(
                            spec.get("package").and_then(Value::as_str).unwrap_or(name).to_owned(),
                        );
                        if let Some(path) = spec.get("path").and_then(Value::as_str) {
                            require(
                                !path.is_empty()
                                    && !Path::new(path).is_absolute()
                                    && !path.contains(['\\', '\0', '\n', '\r']),
                                "invalid reader dependency path",
                            )?;
                            // Workspace paths are repository-relative; direct paths are crate-relative.
                            let base = if inherited { Path::new("") } else { Path::new(&dir) };
                            let mut parts = Vec::new();
                            for part in base.join(path).components() {
                                match part {
                                    Component::Normal(p) => {
                                        parts.push(p.to_string_lossy().into_owned())
                                    }
                                    Component::ParentDir => {
                                        require(
                                            parts.pop().is_some(),
                                            "reader dependency escapes repository",
                                        )?;
                                    }
                                    _ => return Err(invalid("unsupported reader dependency path")),
                                }
                            }
                            pending.push(parts.join("/"));
                        }
                    }
                }
            }
        }
        require(production.insert(package_name, names).is_none(), "duplicate reader path package")?;
    }
    reader_lock(git, before, after, &production)?;
    // These are actual non-crate source inputs of the current reader/kernel.
    // The whole containing crate (including its build script) was compared above.
    require(
        blob(git, before, "data/soundness_tcb.json")?
            == blob(git, after, "data/soundness_tcb.json")?,
        "reader's embedded kernel certificate input changed",
    )?;
    if let Some(root) = checkout {
        checkout_file(git, after, "data/soundness_tcb.json", root)?;
    }
    let worlds = "crates/clean-olean/lean_worlds.tsv";
    let table = blob(git, before, worlds)?;
    require(table == blob(git, after, worlds)?, "reader Lean-world table changed")?;
    for line in std::str::from_utf8(&table).map_err(invalid)?.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<_> = line.split('\t').collect();
        require(fields.len() == 4, "unsupported reader Lean-world row")?;
        for path in fields[3].split_whitespace() {
            relative(path)?;
            require(
                blob(git, before, path)? == blob(git, after, path)?,
                "reader's referenced Lean-world fixture changed",
            )?;
            if let Some(root) = checkout {
                checkout_file(git, after, path, root)?;
            }
        }
    }
    Ok(production)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PackageId {
    name: String,
    version: String,
    source: Option<String>,
}

fn package_id(row: &Value) -> io::Result<PackageId> {
    Ok(PackageId {
        name: string(row, "name")?.to_owned(),
        version: string(row, "version")?.to_owned(),
        source: row
            .get("source")
            .map(|v| v.as_str().map(str::to_owned).ok_or_else(|| invalid("invalid lock source")))
            .transpose()?,
    })
}

fn lock_closure(
    bytes: &[u8],
    production: &BTreeMap<String, BTreeSet<String>>,
) -> io::Result<BTreeMap<PackageId, Value>> {
    lock_closure_with(bytes, production.clone(), |_, _| {
        Err(invalid("unmapped local reader dependency"))
    })
}

fn lock_closure_with(
    bytes: &[u8],
    mut production: BTreeMap<String, BTreeSet<String>>,
    mut discover: impl FnMut(&PackageId, bool) -> io::Result<BTreeSet<String>>,
) -> io::Result<BTreeMap<PackageId, Value>> {
    let doc = parse(bytes)?;
    let rows = doc
        .get("package")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("missing lock packages"))?;
    let mut all = BTreeMap::new();
    for row in rows {
        require(all.insert(package_id(row)?, row.clone()).is_none(), "duplicate lock package")?;
    }
    let resolve = |spelling: &str| -> io::Result<PackageId> {
        let (stem, source) = match spelling.split_once(" (") {
            Some((stem, source)) => (
                stem,
                Some(source.strip_suffix(')').ok_or_else(|| invalid("invalid dependency source"))?),
            ),
            None => (spelling, None),
        };
        let fields: Vec<_> = stem.split_whitespace().collect();
        require(matches!(fields.len(), 1 | 2), "invalid dependency identity")?;
        let matches: Vec<_> = all
            .keys()
            .filter(|id| {
                id.name == fields[0]
                    && (fields.len() == 1 || id.version == fields[1])
                    && source.is_none_or(|s| id.source.as_deref() == Some(s))
            })
            .cloned()
            .collect();
        require(matches.len() == 1, "ambiguous or unresolved lock dependency")?;
        Ok(matches[0].clone())
    };
    let roots: Vec<_> =
        all.keys().filter(|id| id.name == "clean-olean" && id.source.is_none()).cloned().collect();
    require(roots.len() == 1, "missing or ambiguous path reader lock root")?;
    let mut todo = roots;
    let mut found = BTreeMap::new();
    let mut uncertain = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if found.contains_key(&id) {
            continue;
        }
        require(found.len() <= 10_000, "excessive reader dependency closure")?;
        let mut row = all.get(&id).ok_or_else(|| invalid("missing dependency row"))?.clone();
        let dependencies = row
            .get("dependencies")
            .map(|v| v.as_array().ok_or_else(|| invalid("invalid lock dependencies")))
            .transpose()?
            .cloned()
            .unwrap_or_default();
        if id.source.is_none() && !production.contains_key(&id.name) {
            production.insert(id.name.clone(), discover(&id, uncertain.contains(&id))?);
        }
        let mut edges = BTreeSet::new();
        for dep in dependencies {
            let target =
                resolve(dep.as_str().ok_or_else(|| invalid("invalid dependency spelling"))?)?;
            if id.source.is_none() {
                let names = production
                    .get(&id.name)
                    .ok_or_else(|| invalid("unmapped local reader dependency"))?;
                if !names.contains(&target.name) {
                    continue;
                } // Path-package dev edges do not build the reader.
            }
            // Registry feature manifests are not available as Git inputs.
            // An incoming registry edge therefore carries unknown feature
            // requests. Preserve a conservative complete local lock closure,
            // rather than treating those requests as an empty set.
            if target.source.is_none()
                && (id.source.is_some() || uncertain.contains(&id))
                && uncertain.insert(target.clone())
            {
                production.remove(&target.name);
                found.remove(&target);
                todo.push(target.clone());
            }
            edges.insert(target);
        }
        if id.source.is_none() {
            for name in
                production.get(&id.name).ok_or_else(|| invalid("unmapped reader path package"))?
            {
                require(
                    edges.iter().any(|edge| &edge.name == name),
                    "reader production dependency is unresolved",
                )?;
            }
        }
        let strings = edges
            .iter()
            .map(|edge| Value::String(format!("{} {} {:?}", edge.name, edge.version, edge.source)))
            .collect();
        row.as_table_mut()
            .ok_or_else(|| invalid("invalid lock row"))?
            .insert("dependencies".to_owned(), Value::Array(strings));
        todo.extend(edges);
        found.insert(id, row);
    }
    Ok(found)
}

fn reader_lock(
    git: &Git,
    before: &str,
    after: &str,
    production: &BTreeMap<String, BTreeSet<String>>,
) -> io::Result<()> {
    let old = lock_closure(&blob(git, before, "Cargo.lock")?, production)?;
    let new = lock_closure(&blob(git, after, "Cargo.lock")?, production)?;
    require(
        old == new,
        "reader resolved package source, checksum, version or dependency closure changed",
    )
}

fn declared_files(doc: &Value) -> io::Result<BTreeMap<String, String>> {
    let mut result = BTreeMap::new();
    let mut add = |table: &Value, prefix: &str| -> io::Result<()> {
        let table = table.as_table().ok_or_else(|| invalid("invalid artifact file table"))?;
        for (path, value) in table {
            relative(path)?;
            require(path.ends_with(".olean"), "non-olean artifact entry")?;
            let digest = value.as_str().ok_or_else(|| invalid("invalid artifact digest"))?;
            require(
                digest.len() == 64
                    && digest.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()),
                "invalid artifact digest",
            )?;
            require(
                result.insert(format!("{prefix}{path}"), digest.to_owned()).is_none(),
                "duplicate artifact entry",
            )?;
        }
        Ok(())
    };
    add(doc.get("files").ok_or_else(|| invalid("missing artifact files"))?, "")?;
    if let Some(platforms) = doc.get("platforms").and_then(Value::as_table) {
        for (platform, value) in platforms {
            relative(platform)?;
            require(!platform.contains('/'), "invalid artifact platform")?;
            if let Some(table) = value.get("files") {
                add(table, &format!("platform/{platform}/"))?;
            }
        }
    }
    Ok(result)
}

fn artifacts(
    git: &Git,
    anchor: &str,
    tree: &str,
    prefix: &str,
    doc: &Value,
    checkout: Option<&Path>,
) -> io::Result<()> {
    let mut old = files(git, anchor, prefix)?;
    let mut current = files(git, tree, prefix)?;
    let manifest = format!("{prefix}/MANIFEST.toml");
    old.remove(&manifest);
    current.remove(&manifest);
    require(old == current, "original bridge artifact population or bytes changed")?;
    let declared = declared_files(doc)?;
    let actual: BTreeSet<_> = current
        .keys()
        .filter_map(|p| p.strip_prefix(&format!("{prefix}/")))
        .filter(|p| p.ends_with(".olean"))
        .map(str::to_owned)
        .collect();
    require(
        actual == declared.keys().cloned().collect(),
        "artifact inventory differs from manifest",
    )?;
    for (path, digest) in declared {
        let full = format!("{prefix}/{path}");
        let data = blob(git, anchor, &full)?;
        require(
            format!("{:x}", Sha256::digest(&data)) == digest,
            "original artifact digest mismatch",
        )?;
        if let Some(root) = checkout {
            let file = root.join(&full);
            let mut cursor = root.to_path_buf();
            for part in Path::new(&full).components() {
                cursor.push(part);
                require(
                    !fs::symlink_metadata(&cursor)?.file_type().is_symlink(),
                    "symlink in artifact input",
                )?;
            }
            require(fs::read(file)? == data, "working artifact differs from original bytes")?;
        }
    }
    Ok(())
}

/// Verify an optional record against original objects. No record is a no-op;
/// all legacy exact-provenance decisions remain with the existing caller.
pub fn verify(repo: &Path, subject: Subject<'_>) -> io::Result<Option<Selection>> {
    verify_input(repo, subject, None)
}

fn verify_input(
    repo: &Path,
    subject: Subject<'_>,
    proposed: Option<&[u8]>,
) -> io::Result<Option<Selection>> {
    let root = fs::canonicalize(repo)?;
    let git = Git::new(&root)?;
    let subject = capture_subject(&git, subject)?;
    verify_frozen_input(&root, &git, &subject, proposed)
}

struct FrozenSubject {
    tree: String,
    basis: String,
    checkout: bool,
}

fn capture_subject(git: &Git, subject: Subject<'_>) -> io::Result<FrozenSubject> {
    let head = output(git, &["rev-parse", "HEAD"])?;
    oid(&head)?;
    let (tree, basis, checkout) = match subject {
        Subject::Commit(rev) => {
            oid(rev)?;
            let kind = output(git, &["cat-file", "-t", rev])?;
            require(kind == "commit", "invalid reuse subject")?;
            (rev.to_owned(), rev.to_owned(), false)
        }
        Subject::Index => (output(git, &["write-tree"])?, head.clone(), false),
        Subject::Checkout => (head.clone(), head.clone(), true),
    };
    Ok(FrozenSubject { tree, basis, checkout })
}

// All Git reads below use this immutable captured subject, never a second
// index/HEAD capture. Updaters must verify the same tree they intend to write.
fn verify_frozen_input(
    root: &Path,
    git: &Git,
    subject: &FrozenSubject,
    proposed: Option<&[u8]>,
) -> io::Result<Option<Selection>> {
    let tree = &subject.tree;
    let basis = &subject.basis;
    let checkout = subject.checkout.then_some(root);
    let bytes = match proposed {
        Some(bytes) => bytes.to_vec(),
        None => blob(git, tree, MANIFEST)?,
    };
    let mut doc = parse(&bytes)?;
    let Some(record) =
        doc.as_table_mut().ok_or_else(|| invalid("invalid bridge manifest"))?.remove(RECORD)
    else {
        return Ok(None);
    };
    require(string(&record, "schema")? == SCHEMA, "unsupported source reuse schema")?;
    let fields = record.as_table().ok_or_else(|| invalid("invalid source reuse record"))?;
    require(fields.len() == 4, "unexpected source reuse fields")?;
    let anchor = oid(string(&record, "anchor_commit")?)?;
    let ir_pin = oid(string(&record, "selected_trustir_commit")?)?;
    let clean_pin = oid(string(&record, "selected_clean_commit")?)?;
    require(output(git, &["cat-file", "-t", anchor])? == "commit", "reuse anchor is not a commit")?;
    let _ = git.output(&["merge-base", "--is-ancestor", anchor, basis])?;
    let original = parse(&blob(git, anchor, MANIFEST)?)?;
    require(
        string(&doc, "schema")? == "trust.trust-clean.trustir-oleans.manifest.v2",
        "unsupported TrustIr manifest schema",
    )?;
    require(
        original.get(RECORD).is_none() && original == doc,
        "original producer provenance was changed",
    )?;
    require(
        pin(git, tree, "first-party/trust-ir")? == ir_pin
            && pin(git, tree, "first-party/clean")? == clean_pin,
        "reuse selection differs from actual gitlinks",
    )?;
    let origin = doc.get("provenance").ok_or_else(|| invalid("missing original provenance"))?;
    let old_ir = oid(string(origin, "trustir_commit")?)?;
    let old_clean = oid(string(origin, "clean_commit")?)?;
    require(
        pin(git, anchor, "first-party/trust-ir")? == old_ir
            && pin(git, anchor, "first-party/clean")? == old_clean,
        "original provenance differs from anchor gitlinks",
    )?;
    let ir = child_git(git, root, tree, "first-party/trust-ir", checkout.is_some())?;
    let clean = child_git(git, root, tree, "first-party/clean", checkout.is_some())?;
    for (repository, revisions) in [(&ir, [old_ir, ir_pin]), (&clean, [old_clean, clean_pin])] {
        for revision in revisions {
            require(
                output(repository, &["cat-file", "-t", revision])? == "commit",
                "selected input is not a commit object",
            )?;
        }
    }
    equal_tree(&ir, old_ir, ir_pin, PRODUCER)?;
    if checkout.is_some() {
        checkout_tree(&ir, ir_pin, PRODUCER, &root.join("first-party/trust-ir"))?;
    }
    // These are real build inputs, not a source-only selection of .lean files.
    let _ = blob(&ir, ir_pin, &format!("{PRODUCER}/lakefile.lean"))?;
    let toolchain = blob(&ir, ir_pin, &format!("{PRODUCER}/lean-toolchain"))?;
    require(
        std::str::from_utf8(&toolchain).map_err(invalid)?.trim()
            == string(origin, "lean_toolchain")?,
        "producer toolchain differs from original provenance",
    )?;
    let roots = origin
        .get("root_modules")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("missing original roots"))?;
    require(
        roots.iter().map(Value::as_str).eq(crate::BRIDGE_ROOT_MODULES.iter().copied().map(Some)),
        "bridge export roots changed",
    )?;
    let ship_files = declared_files(&doc)?;
    for root_module in crate::BRIDGE_ROOT_MODULES {
        let path = format!("{}.olean", root_module.replace('.', "/"));
        require(
            ship_files.contains_key(&path)
                || ship_files.keys().any(|key| key.ends_with(&format!("/{path}"))),
            "export root is absent from the artifact population",
        )?;
    }
    let production = reader_inputs(
        &clean,
        old_clean,
        clean_pin,
        checkout.map(|root| root.join("first-party/clean")).as_deref(),
    )?;
    effective_reader_inputs(git, root, anchor, tree, &production, checkout.is_some())?;
    let core_path = format!("{CORE}/MANIFEST.toml");
    let core_bytes = blob(git, anchor, &core_path)?;
    require(core_bytes == blob(git, tree, &core_path)?, "original core provenance changed")?;
    let core_doc = parse(&core_bytes)?;
    require(
        string(&core_doc, "schema")? == "trust.vendor.lean-core-oleans.manifest.v2",
        "unsupported core manifest schema",
    )?;
    require(
        at(&core_doc, &["provenance", "lean_toolchain"])
            == at(&doc, &["provenance", "lean_toolchain"]),
        "core and producer toolchains differ",
    )?;
    artifacts(git, anchor, tree, SHIP, &doc, checkout)?;
    artifacts(git, anchor, tree, CORE, &core_doc, checkout)?;
    if checkout.is_some() {
        require(
            fs::read(root.join(MANIFEST))? == bytes
                && fs::read(root.join(&core_path))? == core_bytes,
            "working manifest differs from selected committed manifest",
        )?;
        for (child, expected) in [(&ir, ir_pin), (&clean, clean_pin)] {
            require(
                output(child, &["rev-parse", "HEAD"])? == expected
                    && output(child, &["status", "--porcelain", "--untracked-files=all"])?
                        .is_empty(),
                "cannot establish exact clean selected source checkout",
            )?;
        }
    }
    git.finish_blob_reads()?;
    Ok(Some(Selection {
        trustir_commit: ir_pin.to_owned(),
        clean_commit: clean_pin.to_owned(),
        anchor_commit: anchor.to_owned(),
        trustir_manifest_sha256: format!("{:x}", Sha256::digest(&bytes)),
        core_manifest_sha256: format!("{:x}", Sha256::digest(&core_bytes)),
    }))
}

fn manifest_with_record(original: &[u8], anchor: &str, ir: &str, clean: &str) -> Vec<u8> {
    let mut candidate = original.to_vec();
    candidate.extend_from_slice(format!(
        "\n[source_reuse]\nschema = \"{SCHEMA}\"\nanchor_commit = \"{anchor}\"\nselected_trustir_commit = \"{ir}\"\nselected_clean_commit = \"{clean}\"\n"
    ).as_bytes());
    candidate
}

/// Add only a reuse record to the original manifest, after validating the
/// indexed target and every original input. The caller still stages/commits it.
pub fn prepare(repo: &Path, anchor: &str) -> io::Result<Selection> {
    oid(anchor)?;
    let root = fs::canonicalize(repo)?;
    let git = Git::new(&root)?;
    let subject = capture_subject(&git, Subject::Index)?;
    let tree = subject.tree.clone();
    let ir = pin(&git, &tree, "first-party/trust-ir")?;
    let clean = pin(&git, &tree, "first-party/clean")?;
    let original = blob(&git, anchor, MANIFEST)?;
    require(
        blob(&git, &tree, MANIFEST)? == original && fs::read(root.join(MANIFEST))? == original,
        "prepare requires the unchanged original indexed and working manifest",
    )?;
    let entry = output(&git, &["ls-tree", &tree, "--", MANIFEST])?;
    let mode = entry.split_whitespace().next().ok_or_else(|| invalid("missing manifest mode"))?;
    working_file(&root, MANIFEST, &original, mode)?;
    let candidate = manifest_with_record(&original, anchor, &ir, &clean);
    let selection = verify_frozen_input(&root, &git, &subject, Some(&candidate))?
        .ok_or_else(|| invalid("prepared record did not validate"))?;
    require(fs::read(root.join(MANIFEST))? == original, "manifest changed while preparing reuse")?;
    let path = root.join(MANIFEST);
    working_file(&root, MANIFEST, &original, mode)?;
    let temporary = path.with_extension(format!("reuse-{}", std::process::id()));
    use std::io::Write;
    let mut file = fs::OpenOptions::new().write(true).create_new(true).open(&temporary)?;
    let result = (|| {
        file.set_permissions(fs::metadata(&path)?.permissions())?;
        file.write_all(&candidate)?;
        file.sync_all()?;
        require(
            output(&git, &["rev-parse", "HEAD"])? == subject.basis
                && output(&git, &["write-tree"])? == subject.tree
                && fs::read(&path)? == original,
            "reuse preparation inputs changed before replacement",
        )?;
        working_file(&root, MANIFEST, &original, mode)?;
        fs::rename(&temporary, path)
    })();
    if result.is_err() {
        let _ = fs::remove_file(temporary);
    }
    result?;
    Ok(selection)
}

// This is a local write plan, not mathematical or replay authority. Its only
// constructor authenticates both immutable subjects through the same verifier.
struct RefreshPlan {
    head: String,
    tree: String,
    mode: String,
    current: Vec<u8>,
    candidate: Vec<u8>,
    selection: Selection,
}

fn plan_refresh(root: &Path, git: &Git) -> io::Result<RefreshPlan> {
    let subject = capture_subject(git, Subject::Index)?;
    plan_refresh_captured(root, git, &subject)
}

fn plan_refresh_captured(
    root: &Path,
    git: &Git,
    subject: &FrozenSubject,
) -> io::Result<RefreshPlan> {
    let head = subject.basis.clone();
    let tree = subject.tree.clone();
    let current = blob(git, &head, MANIFEST)?;
    let entry = output(git, &["ls-tree", &head, "--", MANIFEST])?;
    let mode =
        entry.split_whitespace().next().ok_or_else(|| invalid("missing manifest mode"))?.to_owned();
    working_file(root, MANIFEST, &current, &mode)?;
    require(
        blob(git, &tree, MANIFEST)? == current && fs::read(root.join(MANIFEST))? == current,
        "refresh requires the committed manifest unchanged in the index and working tree",
    )?;
    let previous = verify_input(root, Subject::Commit(&head), None)?
        .ok_or_else(|| invalid("refresh requires an authenticated existing reuse record"))?;
    let original = blob(git, &previous.anchor_commit, MANIFEST)?;
    // A machine-prepared appended record has an exact byte representation.
    // Refuse other layouts rather than reserialize original provenance or
    // accidentally rewrite a similarly spelled key in another TOML table.
    require(
        manifest_with_record(
            &original,
            &previous.anchor_commit,
            &previous.trustir_commit,
            &previous.clean_commit,
        ) == current,
        "refresh requires the canonical appended reuse record",
    )?;
    let ir = pin(git, &tree, "first-party/trust-ir")?;
    let clean = pin(git, &tree, "first-party/clean")?;
    let candidate = manifest_with_record(&original, &previous.anchor_commit, &ir, &clean);
    let selection = verify_frozen_input(root, git, subject, Some(&candidate))?
        .ok_or_else(|| invalid("refreshed record did not validate"))?;
    Ok(RefreshPlan { head, tree, mode, current, candidate, selection })
}

fn apply_refresh(root: &Path, git: &Git, plan: RefreshPlan) -> io::Result<Selection> {
    let path = root.join(MANIFEST);
    working_file(root, MANIFEST, &plan.current, &plan.mode)?;
    let temporary = path.with_extension(format!("reuse-{}", std::process::id()));
    use std::io::Write;
    let mut file = fs::OpenOptions::new().write(true).create_new(true).open(&temporary)?;
    let result = (|| {
        file.set_permissions(fs::metadata(&path)?.permissions())?;
        file.write_all(&plan.candidate)?;
        file.sync_all()?;
        require(
            output(git, &["rev-parse", "HEAD"])? == plan.head
                && output(git, &["write-tree"])? == plan.tree
                && fs::read(&path)? == plan.current,
            "reuse refresh inputs changed before replacement",
        )?;
        working_file(root, MANIFEST, &plan.current, &plan.mode)?;
        fs::rename(&temporary, path)
    })();
    if result.is_err() {
        let _ = fs::remove_file(temporary);
    }
    result?;
    Ok(plan.selection)
}

/// Refresh only the selected pins of an existing machine-prepared record.
/// The immutable no-record artifact anchor is derived from the verified HEAD
/// record, never supplied by the caller. Both prior and proposed subjects must
/// pass the complete verifier; the index is left unchanged for caller review.
pub fn refresh(repo: &Path) -> io::Result<Selection> {
    let root = fs::canonicalize(repo)?;
    let git = Git::new(&root)?;
    let plan = plan_refresh(&root, &git)?;
    apply_refresh(&root, &git, plan)
}

#[cfg(test)]
mod tests {
    use std::process::Command;

    use super::*;

    fn run(dir: &Path, args: &[&str]) -> String {
        let out = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .output()
            .expect("run fixture Git");
        assert!(out.status.success(), "{args:?}: {}", String::from_utf8_lossy(&out.stderr));
        String::from_utf8(out.stdout).expect("Git output").trim().to_owned()
    }
    fn write(root: &Path, path: &str, data: impl AsRef<[u8]>) {
        let file = root.join(path);
        fs::create_dir_all(file.parent().unwrap()).unwrap();
        fs::write(file, data).unwrap();
    }
    fn init(root: &Path) {
        fs::create_dir_all(root).unwrap();
        run(root, &["init", "--quiet"]);
        run(root, &["config", "user.name", "fixture"]);
        run(root, &["config", "user.email", "fixture@example.invalid"]);
    }
    fn commit(root: &Path) -> String {
        run(root, &["add", "--all"]);
        run(root, &["commit", "--quiet", "-m", "fixture"]);
        run(root, &["rev-parse", "HEAD"])
    }
    struct Fixture {
        temp: tempfile::TempDir,
        anchor: String,
        old_ir: String,
    }
    impl Fixture {
        fn root(&self) -> &Path {
            self.temp.path()
        }
        fn new() -> Self {
            let temp = tempfile::tempdir().unwrap();
            let root = temp.path();
            init(root);
            let ir = root.join("first-party/trust-ir");
            init(&ir);
            write(&ir, &format!("{PRODUCER}/lean-toolchain"), "leanprover/lean4:v4.8.0\n");
            write(&ir, &format!("{PRODUCER}/lakefile.lean"), "import Lake\n");
            write(&ir, &format!("{PRODUCER}/TrustIr/Basic.lean"), "def original := 1\n");
            let old_ir = commit(&ir);
            let clean = root.join("first-party/clean");
            init(&clean);
            write(&clean, "Cargo.toml", "[workspace]\nmembers=[]\n");
            for p in [".cargo/config.toml", "rust-toolchain.toml", "lean-toolchain"] {
                write(&clean, p, "fixture\n");
            }
            write(
                &clean,
                "crates/clean-olean/Cargo.toml",
                "[package]\nname='clean-olean'\nversion='0.1.0'\n[dependencies]\nclean-kernel={path='../clean-kernel'}\n",
            );
            write(&clean, "crates/clean-olean/src/lib.rs", "pub fn original() {}\n");
            write(
                &clean,
                "crates/clean-kernel/Cargo.toml",
                "[package]\nname='clean-kernel'\nversion='0.1.0'\n[dependencies]\nserde='1'\n",
            );
            write(&clean, "crates/clean-kernel/src/lib.rs", "pub fn original() {}\n");
            write(
                &clean,
                "Cargo.lock",
                "version=3\n[[package]]\nname='clean-olean'\nversion='0.1.0'\ndependencies=['clean-kernel']\n[[package]]\nname='clean-kernel'\nversion='0.1.0'\ndependencies=['serde']\n[[package]]\nname='serde'\nversion='1.0.0'\nsource='registry+https://github.com/rust-lang/crates.io-index'\nchecksum='original'\n",
            );
            write(&clean, "data/soundness_tcb.json", "{}\n");
            write(&clean, "data/world.olean", "world\n");
            write(&clean, "crates/clean-verify/spec/model.lean", "def original := 1\n");
            write(
                &clean,
                "crates/clean-olean/lean_worlds.tsv",
                "fixture\toracle\tfixture\tdata/world.olean\n",
            );
            let old_clean = commit(&clean);
            write(
                root,
                "Cargo.toml",
                "[workspace]\nresolver='2'\n[workspace.dependencies]\nclean-olean={path='first-party/clean/crates/clean-olean'}\nclean-kernel={path='first-party/clean/crates/clean-kernel'}\n[patch.crates-io]\nmemchr={path='crates/memchr'}\n",
            );
            let lock = fs::read_to_string(clean.join("Cargo.lock"))
                .unwrap()
                .replace("name='serde'\n", "name='serde'\ndependencies=['memchr']\n");
            write(
                root,
                "Cargo.lock",
                format!("{lock}\n[[package]]\nname='memchr'\nversion='2.0.0'\n"),
            );
            write(
                root,
                "crates/memchr/Cargo.toml",
                "[package]\nname='memchr'\nversion='2.0.0'\n[features]\ndefault=['std']\nstd=[]\n",
            );
            write(root, "crates/memchr/src/lib.rs", "pub fn original() {}\n");
            write(
                root,
                "crates/trust-clean/Cargo.toml",
                "[package]\nname='trust-clean'\nversion='0.1.0'\n[dependencies]\nclean-olean={workspace=true}\nclean-kernel={workspace=true}\n",
            );
            for path in [".cargo/config.toml", "rust-toolchain.toml"] {
                write(root, path, "fixture\n");
            }
            write(
                root,
                ".gitmodules",
                "[submodule \"ir\"]\npath=first-party/trust-ir\n[submodule \"clean\"]\npath=first-party/clean\n",
            );
            let mut manifest = format!(
                "schema='trust.trust-clean.trustir-oleans.manifest.v2'\n[provenance]\ntrustir_commit='{old_ir}'\nclean_commit='{old_clean}'\nlean_toolchain='leanprover/lean4:v4.8.0'\nroot_modules={:?}\n[files]\n",
                crate::BRIDGE_ROOT_MODULES
            );
            for module in crate::BRIDGE_ROOT_MODULES {
                let name = format!("{}.olean", module.replace('.', "/"));
                let data = module.as_bytes();
                write(root, &format!("{SHIP}/{name}"), data);
                manifest += &format!("'{name}'='{:x}'\n", Sha256::digest(data));
            }
            manifest += &format!("[platforms.'fixture']\nbuilt_from_trustir_commit='{old_ir}'\n");
            write(root, MANIFEST, manifest);
            write(root, &format!("{CORE}/Init/Prelude.olean"), b"core");
            write(
                root,
                &format!("{CORE}/MANIFEST.toml"),
                format!(
                    "schema='trust.vendor.lean-core-oleans.manifest.v2'\n[provenance]\nlean_toolchain='leanprover/lean4:v4.8.0'\n[files]\n'Init/Prelude.olean'='{:x}'\n",
                    Sha256::digest(b"core")
                ),
            );
            let anchor = commit(root);
            write(&ir, "README", "unrelated change\n");
            commit(&ir);
            write(&clean, "README", "unrelated change\n");
            commit(&clean);
            run(root, &["add", "--all"]);
            prepare(root, &anchor).unwrap();
            commit(root);
            Self { temp, anchor, old_ir }
        }
        fn changed_ir(&self, path: &str) {
            let ir = self.root().join("first-party/trust-ir");
            write(&ir, path, "changed input\n");
            let new = commit(&ir);
            let m = fs::read_to_string(self.root().join(MANIFEST)).unwrap();
            let mut doc: Value = m.parse().unwrap();
            doc[RECORD]["selected_trustir_commit"] = Value::String(new);
            write(self.root(), MANIFEST, toml::to_string(&doc).unwrap());
            commit(self.root());
        }
        fn changed_clean(&self, path: &str, value: &str) {
            let clean = self.root().join("first-party/clean");
            write(&clean, path, value);
            let new = commit(&clean);
            let mut doc = parse(&fs::read(self.root().join(MANIFEST)).unwrap()).unwrap();
            doc[RECORD]["selected_clean_commit"] = Value::String(new);
            write(self.root(), MANIFEST, toml::to_string(&doc).unwrap());
            commit(self.root());
        }
    }

    fn stage_refresh_pins(f: &Fixture) -> (String, String) {
        let mut pins = Vec::new();
        for name in ["trust-ir", "clean"] {
            let child = f.root().join(format!("first-party/{name}"));
            let mut readme = fs::read(child.join("README")).unwrap();
            readme.extend_from_slice(b"next unrelated revision\n");
            write(&child, "README", readme);
            pins.push(commit(&child));
        }
        run(f.root(), &["add", "first-party/trust-ir", "first-party/clean"]);
        (pins.remove(0), pins.remove(0))
    }

    fn refresh_refuses_without_write(f: &Fixture) {
        let before = fs::read(f.root().join(MANIFEST)).unwrap();
        assert!(refresh(f.root()).is_err());
        assert_eq!(fs::read(f.root().join(MANIFEST)).unwrap(), before);
        assert!(
            !f.root()
                .join(MANIFEST)
                .with_extension(format!("reuse-{}", std::process::id()))
                .exists()
        );
    }

    #[test]
    fn refresh_selected_pins_preserves_origin_and_supports_next_day() {
        let f = Fixture::new();
        let original = blob(&Git::new(f.root()).unwrap(), &f.anchor, MANIFEST).unwrap();
        let previous = verify(f.root(), Subject::Checkout).unwrap().unwrap();
        let (ir, clean) = stage_refresh_pins(&f);
        assert_ne!(previous.trustir_commit, ir);
        assert_ne!(previous.clean_commit, clean);
        let selected = refresh(f.root()).unwrap();
        assert_eq!(
            (selected.trustir_commit.as_str(), selected.clean_commit.as_str()),
            (ir.as_str(), clean.as_str())
        );
        assert_eq!(selected.anchor_commit, f.anchor);
        assert_eq!(
            fs::read(f.root().join(MANIFEST)).unwrap(),
            manifest_with_record(&original, &f.anchor, &ir, &clean),
        );
        // Refresh never stages its own result. Once reviewed and committed,
        // the same original anchor remains valid for another daily refresh.
        assert!(verify(f.root(), Subject::Index).is_err());
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).unwrap().is_some());
        let first_day = fs::read(f.root().join(MANIFEST)).unwrap();
        assert_eq!(refresh(f.root()).unwrap().anchor_commit, f.anchor);
        assert_eq!(fs::read(f.root().join(MANIFEST)).unwrap(), first_day);
        let (next_ir, next_clean) = stage_refresh_pins(&f);
        let next = refresh(f.root()).unwrap();
        assert_eq!(next.anchor_commit, f.anchor);
        assert_eq!((next.trustir_commit, next.clean_commit), (next_ir, next_clean));
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).unwrap().is_some());
    }

    #[test]
    fn refresh_requires_an_existing_authenticated_record() {
        let f = Fixture::new();
        run(f.root(), &["checkout", "--detach", &f.anchor]);
        refresh_refuses_without_write(&f);
    }

    #[test]
    fn refresh_rejects_forged_prior_selection_or_rolling_anchor() {
        for anchor in [false, true] {
            let f = Fixture::new();
            let prior = fs::read_to_string(f.root().join(MANIFEST)).unwrap();
            let current = verify(f.root(), Subject::Checkout).unwrap().unwrap();
            let bad = if anchor {
                prior.replace(&f.anchor, &run(f.root(), &["rev-parse", "HEAD"]))
            } else {
                prior.replace(&current.trustir_commit, &f.old_ir)
            };
            write(f.root(), MANIFEST, bad);
            commit(f.root());
            refresh_refuses_without_write(&f);
        }
    }

    #[test]
    fn refresh_does_not_authorize_changed_producer_or_reader() {
        for producer in [false, true] {
            let f = Fixture::new();
            let child = if producer { "trust-ir" } else { "clean" };
            let path = if producer {
                format!("{PRODUCER}/TrustIr/Basic.lean")
            } else {
                "crates/clean-kernel/src/lib.rs".to_owned()
            };
            let repo = f.root().join(format!("first-party/{child}"));
            write(&repo, &path, "changed production input\n");
            commit(&repo);
            run(f.root(), &["add", &format!("first-party/{child}")]);
            refresh_refuses_without_write(&f);
        }
    }

    #[test]
    fn refresh_rejects_changed_artifacts_and_uncommitted_manifest() {
        for path in [format!("{CORE}/Init/Prelude.olean"), MANIFEST.to_owned()] {
            let f = Fixture::new();
            let mut bytes = fs::read(f.root().join(&path)).unwrap();
            bytes.extend_from_slice(b"\n# changed\n");
            write(f.root(), &path, bytes);
            run(f.root(), &["add", &path]);
            refresh_refuses_without_write(&f);
        }
    }

    #[test]
    fn refresh_refuses_to_reserialize_a_noncanonical_valid_record() {
        let f = Fixture::new();
        let doc = parse(&fs::read(f.root().join(MANIFEST)).unwrap()).unwrap();
        write(f.root(), MANIFEST, toml::to_string(&doc).unwrap());
        let head = commit(f.root());
        assert!(verify(f.root(), Subject::Commit(&head)).unwrap().is_some());
        refresh_refuses_without_write(&f);
    }

    #[cfg(unix)]
    #[test]
    fn refresh_refuses_a_working_manifest_symlink() {
        let f = Fixture::new();
        let path = f.root().join(MANIFEST);
        let retained = f.root().join("retained-manifest");
        fs::rename(&path, &retained).unwrap();
        std::os::unix::fs::symlink(&retained, &path).unwrap();
        refresh_refuses_without_write(&f);
        assert!(fs::symlink_metadata(path).unwrap().file_type().is_symlink());
    }

    #[test]
    fn refresh_detects_head_index_or_manifest_changes_after_validation() {
        for changed in ["HEAD", "index", "manifest"] {
            let f = Fixture::new();
            let git = Git::new(f.root()).unwrap();
            let plan = plan_refresh(f.root(), &git).unwrap();
            match changed {
                "HEAD" => {
                    run(f.root(), &["commit", "--allow-empty", "-m", "new HEAD"]);
                }
                "index" => {
                    write(f.root(), "later.txt", "new indexed input\n");
                    run(f.root(), &["add", "later.txt"]);
                }
                _ => {
                    let mut bytes = fs::read(f.root().join(MANIFEST)).unwrap();
                    bytes.extend_from_slice(b"\n# concurrent writer\n");
                    write(f.root(), MANIFEST, bytes);
                }
            }
            let before = fs::read(f.root().join(MANIFEST)).unwrap();
            assert!(apply_refresh(f.root(), &git, plan).is_err(), "{changed}");
            assert_eq!(fs::read(f.root().join(MANIFEST)).unwrap(), before);
            assert!(
                !f.root()
                    .join(MANIFEST)
                    .with_extension(format!("reuse-{}", std::process::id()))
                    .exists()
            );
        }
    }

    #[test]
    fn refresh_frozen_subject_refuses_the_invalid_a_valid_b_a_index_pattern() {
        for preparing in [false, true] {
            let f = Fixture::new();
            let git = Git::new(f.root()).unwrap();
            let selected = verify(f.root(), Subject::Checkout).unwrap().unwrap();
            let original = blob(&git, &f.anchor, MANIFEST).unwrap();
            let candidate = manifest_with_record(
                &original,
                &f.anchor,
                &selected.trustir_commit,
                &selected.clean_commit,
            );
            if preparing {
                write(f.root(), MANIFEST, original);
                run(f.root(), &["add", MANIFEST]);
            }
            // A and B have identical selected pins and candidate manifest.
            // Only A's actual consuming reader configuration is invalid.
            write(f.root(), ".cargo/config.toml", "changed reader context\n");
            run(f.root(), &["add", ".cargo/config.toml"]);
            let a = capture_subject(&git, Subject::Index).unwrap();
            run(f.root(), &["reset", "HEAD", "--", ".cargo/config.toml"]);
            let b = capture_subject(&git, Subject::Index).unwrap();
            assert_ne!(a.tree, b.tree);
            assert_eq!(a.basis, b.basis);
            for path in ["first-party/trust-ir", "first-party/clean"] {
                assert_eq!(pin(&git, &a.tree, path).unwrap(), pin(&git, &b.tree, path).unwrap());
            }
            // This is the old updater's independent live-index verification:
            // B passes, then A returns and satisfies an A-only bookend.
            assert!(verify_input(f.root(), Subject::Index, Some(&candidate)).unwrap().is_some());
            run(f.root(), &["read-tree", &a.tree]);
            assert_eq!(output(&git, &["write-tree"]).unwrap(), a.tree);
            // The shared verifier used by BOTH prepare and refresh instead
            // checks the caller's immutable A even while live B is selected.
            run(f.root(), &["read-tree", &b.tree]);
            let error = verify_frozen_input(f.root(), &git, &a, Some(&candidate)).unwrap_err();
            assert!(error.to_string().contains("effective reader configuration changed"));
            if !preparing {
                let error = plan_refresh_captured(f.root(), &git, &a).err().unwrap();
                assert!(error.to_string().contains("effective reader configuration changed"));
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn prepare_regular_manifest_preserves_tracked_executable_mode() {
        use std::os::unix::fs::PermissionsExt;
        let f = Fixture::new();
        let git = Git::new(f.root()).unwrap();
        let original = blob(&git, &f.anchor, MANIFEST).unwrap();
        write(f.root(), MANIFEST, &original);
        fs::set_permissions(f.root().join(MANIFEST), fs::Permissions::from_mode(0o755)).unwrap();
        run(f.root(), &["add", MANIFEST]);
        assert_eq!(prepare(f.root(), &f.anchor).unwrap().anchor_commit, f.anchor);
        assert_ne!(fs::metadata(f.root().join(MANIFEST)).unwrap().permissions().mode() & 0o111, 0);
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).unwrap().is_some());
    }

    #[cfg(unix)]
    #[test]
    fn prepare_regular_manifest_refuses_a_same_byte_working_symlink() {
        let f = Fixture::new();
        let original = blob(&Git::new(f.root()).unwrap(), &f.anchor, MANIFEST).unwrap();
        write(f.root(), MANIFEST, &original);
        run(f.root(), &["add", MANIFEST]);
        let path = f.root().join(MANIFEST);
        let retained = f.root().join("retained-original-manifest");
        fs::rename(&path, &retained).unwrap();
        std::os::unix::fs::symlink(&retained, &path).unwrap();
        assert_eq!(fs::read(&path).unwrap(), original);
        assert!(prepare(f.root(), &f.anchor).is_err());
        assert!(fs::symlink_metadata(&path).unwrap().file_type().is_symlink());
        assert_eq!(fs::read(&retained).unwrap(), original);
        assert!(!path.with_extension(format!("reuse-{}", std::process::id())).exists());
    }

    #[test]
    fn equal_complete_inputs_reuse_without_rewriting_original_provenance() {
        let f = Fixture::new();
        let selected = verify(f.root(), Subject::Checkout).unwrap().unwrap();
        assert_eq!(selected.anchor_commit, f.anchor);
        let doc = parse(&fs::read(f.root().join(MANIFEST)).unwrap()).unwrap();
        assert_eq!(doc["provenance"]["trustir_commit"].as_str(), Some(f.old_ir.as_str()));
        assert_eq!(
            doc["platforms"]["fixture"]["built_from_trustir_commit"].as_str(),
            Some(f.old_ir.as_str())
        );
        assert_ne!(selected.trustir_commit, f.old_ir);
        assert!(
            verify(f.root(), Subject::Commit(&run(f.root(), &["rev-parse", "HEAD"])))
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn source_lake_and_toolchain_changes_each_refuse() {
        for path in ["TrustIr/Basic.lean", "lakefile.lean", "lean-toolchain"] {
            let f = Fixture::new();
            f.changed_ir(&format!("{PRODUCER}/{path}"));
            assert!(verify(f.root(), Subject::Checkout).is_err(), "{path}");
        }
    }

    #[test]
    fn changed_artifact_or_manifest_provenance_refuses() {
        let f = Fixture::new();
        write(f.root(), &format!("{CORE}/Init/Prelude.olean"), b"forged");
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
        let f = Fixture::new();
        let m = fs::read_to_string(f.root().join(MANIFEST))
            .unwrap()
            .replace("built_from_trustir_commit=", "unexpected=");
        write(f.root(), MANIFEST, m);
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn dirty_and_walked_out_source_checkouts_refuse() {
        let f = Fixture::new();
        write(f.root(), "first-party/trust-ir/untracked", "untracked");
        assert!(verify(f.root(), Subject::Checkout).is_err());
        let f = Fixture::new();
        fs::rename(f.root().join("first-party/trust-ir/.git"), f.root().join("ir-metadata"))
            .unwrap();
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn replacement_refs_do_not_hide_changed_source() {
        let f = Fixture::new();
        f.changed_ir(&format!("{PRODUCER}/TrustIr/Basic.lean"));
        let ir = f.root().join("first-party/trust-ir");
        let new = run(&ir, &["rev-parse", "HEAD"]);
        run(&ir, &["replace", &new, &f.old_ir]);
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn changed_resolved_dependency_or_external_reader_input_refuses() {
        let f = Fixture::new();
        let lock = fs::read_to_string(f.root().join("first-party/clean/Cargo.lock")).unwrap();
        f.changed_clean("Cargo.lock", &lock.replace("checksum='original'", "checksum='changed'"));
        assert!(verify(f.root(), Subject::Checkout).is_err());
        for path in ["data/soundness_tcb.json", "data/world.olean"] {
            let f = Fixture::new();
            f.changed_clean(path, "changed\n");
            assert!(verify(f.root(), Subject::Checkout).is_err(), "{path}");
        }
    }

    #[test]
    fn effective_root_lock_and_feature_inputs_refuse_changes_but_unrelated_lock_rows_do_not() {
        let f = Fixture::new();
        let lock = fs::read_to_string(f.root().join("Cargo.lock")).unwrap();
        write(
            f.root(),
            "Cargo.lock",
            lock.replace("checksum='original'", "checksum='root-changed'"),
        );
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
        let f = Fixture::new();
        let mut lock = fs::read_to_string(f.root().join("Cargo.lock")).unwrap();
        lock.push_str("\n[[package]]\nname='unrelated-cg'\nversion='5.0.0'\n");
        write(f.root(), "Cargo.lock", lock);
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).unwrap().is_some());
        let f = Fixture::new();
        let root = fs::read_to_string(f.root().join("Cargo.toml")).unwrap();
        write(f.root(), "Cargo.toml", root.replace("resolver='2'", "resolver='3'"));
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn object_only_submodule_stores_support_immutable_checks_but_not_checkout_reuse() {
        let f = Fixture::new();
        for (path, name) in [("first-party/trust-ir", "ir"), ("first-party/clean", "clean")] {
            fs::create_dir_all(f.root().join(".git/modules")).unwrap();
            fs::rename(f.root().join(path).join(".git"), f.root().join(".git/modules").join(name))
                .unwrap();
            fs::remove_dir_all(f.root().join(path)).unwrap();
            fs::create_dir_all(f.root().join(path)).unwrap();
        }
        let head = run(f.root(), &["rev-parse", "HEAD"]);
        assert!(verify(f.root(), Subject::Commit(&head)).unwrap().is_some());
        assert!(verify(f.root(), Subject::Index).unwrap().is_some());
        assert!(verify(f.root(), Subject::Checkout).is_err());
        fs::rename(f.root().join(".git/modules/ir"), f.root().join("wrong-store")).unwrap();
        assert!(verify(f.root(), Subject::Commit(&head)).is_err());
    }

    #[test]
    fn local_grafts_cannot_counterfeit_anchor_ancestry() {
        let f = Fixture::new();
        let tree = run(f.root(), &["rev-parse", &format!("{}^{{tree}}", f.anchor)]);
        let unrelated = run(f.root(), &["commit-tree", &tree, "-m", "unrelated"]);
        let mut doc = parse(&fs::read(f.root().join(MANIFEST)).unwrap()).unwrap();
        doc[RECORD]["anchor_commit"] = Value::String(unrelated.clone());
        write(f.root(), MANIFEST, toml::to_string(&doc).unwrap());
        let head = commit(f.root());
        write(f.root(), ".git/info/grafts", format!("{head} {unrelated}\n"));
        assert!(verify(f.root(), Subject::Commit(&head)).is_err());
    }

    #[test]
    fn real_absorbed_object_only_stores_ignore_absent_core_worktree() {
        let f = Fixture::new();
        run(f.root(), &["submodule", "absorbgitdirs", "first-party/trust-ir", "first-party/clean"]);
        for path in ["first-party/trust-ir", "first-party/clean"] {
            fs::remove_dir_all(f.root().join(path)).unwrap();
        }
        let head = run(f.root(), &["rev-parse", "HEAD"]);
        assert!(verify(f.root(), Subject::Commit(&head)).unwrap().is_some());
        assert!(verify(f.root(), Subject::Index).unwrap().is_some());
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn effective_root_path_patch_source_and_selector_changes_refuse() {
        let f = Fixture::new();
        write(f.root(), "crates/memchr/src/lib.rs", "pub fn changed() {}\n");
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
        let f = Fixture::new();
        let manifest = fs::read_to_string(f.root().join("Cargo.toml")).unwrap();
        write(
            f.root(),
            "Cargo.toml",
            manifest.replace("path='crates/memchr'", "path='crates/other-memchr'"),
        );
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn clean_filters_cannot_hide_changed_physical_producer_source() {
        let f = Fixture::new();
        let ir = f.root().join("first-party/trust-ir");
        write(
            &ir,
            ".git/info/attributes",
            "lean/trust_ir-semantics/TrustIr/Basic.lean filter=source\n",
        );
        run(&ir, &["config", "filter.source.clean", "sed s/alteredd/original/g"]);
        write(&ir, &format!("{PRODUCER}/TrustIr/Basic.lean"), "def alteredd := 1\n");
        assert_eq!(run(&ir, &["status", "--porcelain"]), "");
        assert!(verify(f.root(), Subject::Checkout).is_err());
        let head = run(f.root(), &["rev-parse", "HEAD"]);
        assert!(verify(f.root(), Subject::Commit(&head)).unwrap().is_some());
    }

    #[cfg(unix)]
    #[test]
    fn same_blob_as_symlink_is_not_an_input_file() {
        use std::os::unix::fs::symlink;
        let f = Fixture::new();
        let clean = f.root().join("first-party/clean");
        fs::remove_file(clean.join("data/soundness_tcb.json")).unwrap();
        symlink("{}\n", clean.join("data/soundness_tcb.json")).unwrap();
        write(&clean, "data/{}\n", "different followed bytes\n");
        let new = commit(&clean);
        let mut doc = parse(&fs::read(f.root().join(MANIFEST)).unwrap()).unwrap();
        doc[RECORD]["selected_clean_commit"] = Value::String(new);
        write(f.root(), MANIFEST, toml::to_string(&doc).unwrap());
        commit(f.root());
        assert!(verify(f.root(), Subject::Checkout).is_err());
    }

    #[test]
    fn registry_feature_forwarding_never_becomes_an_empty_local_feature_set() {
        let lock = "version=3\n[[package]]\nname='clean-olean'\nversion='1'\ndependencies=['registry']\n[[package]]\nname='registry'\nversion='1'\nsource='registry+fixture'\nchecksum='a'\ndependencies=['patched']\n[[package]]\nname='patched'\nversion='1'\ndependencies=['optional']\n[[package]]\nname='optional'\nversion='1'\nsource='registry+fixture'\nchecksum='b'\n";
        let discover = |id: &PackageId, uncertain| match id.name.as_str() {
            "clean-olean" => Ok(BTreeSet::from(["registry".to_owned()])),
            "patched" => {
                assert!(uncertain, "registry feature forwarding must remain unknown");
                Ok(BTreeSet::from(["optional".to_owned()]))
            }
            _ => Err(invalid("unexpected source")),
        };
        let graph = lock_closure_with(lock.as_bytes(), BTreeMap::new(), discover).unwrap();
        assert!(graph.keys().any(|id| id.name == "optional"));
        let missing = lock.replace("dependencies=['optional']", "dependencies=[]");
        assert!(lock_closure_with(missing.as_bytes(), BTreeMap::new(), discover).is_err());
    }
}
