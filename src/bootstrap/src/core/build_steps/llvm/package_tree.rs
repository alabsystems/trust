// Copyright 2026 Andrew Yates
//! Trust: the LLVM build tree as an atpkg package (DC-16c).
//!
//! atpkg's store (aterm's `crates/atpkg/src/keyed_tree.rs`, DC-16b) keeps Trust's LLVM build
//! tree as the keyed tree `llvm-tree`, at `<prefix>/trees.noindex/llvm-tree/<host>/<key>/`
//! beside its ready marker `<key>.ready`, where `<key>` is the SHA-256 of the tree's key
//! inputs ([`key_inputs`]): what the tree was built from. This build writes them into every
//! LLVM tree it completes ([`KEY_FILE`], [`record`]), which is the text a builder packs the
//! tree under (`atpkg-publish pack-tree --key-inputs`), and the reader here forms the same
//! text for the tree this build would make.
//!
//! **The key** names the LLVM sources, the `[llvm]` configuration and the host: the host
//! triple; the host C and C++ compilers that compile LLVM (never stage 0), each by the first
//! line of its `--version`, and what the C++ compiler's driver makes of this build's flags and
//! environment: the target it compiles for, whose OS version is the deployment target the
//! tree's tools need, and the SDK version it compiles against ([`Compilers`]); and the tree's
//! whole completion stamp (`.llvm-stamp`: the target, the digest of the LLVM sources, named
//! relative to their root, the digest of the CMake request the `[llvm]` table makes (every
//! define, flag, tool and environment value the configure step receives, with this
//! checkout's own paths written as tokens), the link mode and the LLVM dependency). atpkg
//! signs a tree only for inputs that name its own `.llvm-stamp`.
//!
//! **What is taken** ([`take`]): where an LLVM miss began `build/<host>/llvm` afresh (there
//! was none, or another tree's clone, or a build of another generation), the store's complete
//! tree of exactly this key is cloned there by `clonefile(2)` (a copy-on-write clone of the
//! whole directory, never a link and never a byte copy; another volume, or one that cannot
//! clone, refuses), made writable by its owner as a tree this build made is, checked (only
//! regular files and directories, the same key inputs and the same `.llvm-stamp` as this
//! build's), and its install manifest is written with this tree's paths. The LLVM step then
//! holds the clone to its own reuse checks, and removes it and builds where they fail. Any
//! mismatch, a missing package, or a clone that cannot be made builds LLVM as before and
//! prints why, naming the key inputs that differ from each tree of another key the store
//! holds ([`differing_inputs`]).

use std::path::{Path, PathBuf};
use std::{fs, io};

use sha2::Digest;

use super::reuse_evidence::parse_source_completion;
use crate::utils::helpers::hex_encode;

/// The key inputs a completed LLVM tree carries at its root.
pub(super) const KEY_FILE: &str = ".trust-llvm-tree-key";
const KEY_SCHEMA: &str = "trust-llvm-tree-key/v1";
/// The line after which the key inputs hold the tree's `.llvm-stamp`, whole.
const STAMP_LINE: &str = "llvm-stamp";
/// atpkg's keyed-tree program for the LLVM build tree.
pub(super) const PROGRAM: &str = "llvm-tree";
/// The suffix atpkg's ready marker takes beside a tree.
const READY_SUFFIX: &str = ".ready";
/// The suffix of atpkg's record of a tree's last use (`aterm pkg gc` keeps a used tree).
const USED_SUFFIX: &str = ".used";

/// The host C and C++ compilers an LLVM tree is built by, as its key names them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Compilers {
    /// The first line of the C compiler's `--version`.
    pub(super) cc: String,
    /// The first line of the C++ compiler's `--version`.
    pub(super) cxx: String,
    /// The target the C++ driver compiles for with this build's flags and environment
    /// (`-triple` of its `-###`; on Apple hosts its OS version is the deployment target), or
    /// `unreported` for a driver that names none.
    pub(super) target: String,
    /// The SDK version the C++ driver compiles against (`-target-sdk-version`), or `none`.
    pub(super) sdk: String,
}

/// The names of the key inputs, in their order: [`differing_inputs`] names these.
const KEY_FIELDS: [&str; 5] = ["host", "cc", "cxx", "cxx-target", "sdk"];

/// The key inputs of an LLVM tree built on `host` by `compilers`, completed with the stamp
/// `stamp`. `None` when the stamp is not a complete LLVM working-source stamp, or a field
/// cannot be one line.
pub(super) fn key_inputs(host: &str, compilers: &Compilers, stamp: &str) -> Option<String> {
    let one_line = |text: &str| !text.is_empty() && !text.contains(['\n', '\r']);
    let completion = parse_source_completion(stamp.as_bytes())?;
    let values = [host, &compilers.cc, &compilers.cxx, &compilers.target, &compilers.sdk];
    if completion.project != "llvm" || !values.iter().all(|value| one_line(value)) {
        return None;
    }
    let mut inputs = format!("{KEY_SCHEMA}\n");
    for (name, value) in KEY_FIELDS.iter().zip(values) {
        inputs.push_str(&format!("{name} {value}\n"));
    }
    inputs.push_str(&format!("{STAMP_LINE}\n{stamp}"));
    Some(inputs)
}

/// The key of `inputs`: their SHA-256, as atpkg names the tree.
pub(super) fn key(inputs: &str) -> String {
    hex_encode(sha2::Sha256::digest(inputs.as_bytes()).as_slice())
}

/// The `.llvm-stamp` text key inputs name.
fn stamp_of(inputs: &str) -> Option<&str> {
    inputs.split_once(&format!("\n{STAMP_LINE}\n")).map(|(_, stamp)| stamp)
}

/// The value of the line `<name> <value>` of key inputs.
fn field<'a>(inputs: &'a str, name: &str) -> Option<&'a str> {
    inputs.lines().find_map(|line| line.strip_prefix(name)?.strip_prefix(' '))
}

/// The key inputs in which `own` and `other` differ, by name: `schema`, `host`, `cc` and
/// `cxx` (the host compilers), `cxx-target` (what the C++ driver compiles for), `sdk`, and of
/// the stamp `target`, `source` (the LLVM sources), `request` (the CMake request the `[llvm]`
/// table makes), `linking` and `dependency`.
pub(super) fn differing_inputs(own: &str, other: &str) -> Vec<String> {
    let fields = |inputs: &str| -> Vec<(String, Option<String>)> {
        let schema = inputs.lines().next().map(str::to_owned);
        let mut fields = vec![("schema".to_owned(), schema)];
        let head = inputs.split_once(&format!("\n{STAMP_LINE}\n")).map_or(inputs, |(h, _)| h);
        for name in KEY_FIELDS {
            fields.push((name.to_owned(), field(head, name).map(str::to_owned)));
        }
        let stamp = stamp_of(inputs).unwrap_or("");
        let project = stamp.lines().next().map(str::to_owned);
        fields.push(("stamp".to_owned(), project));
        for name in ["target", "source", "request", "linking", "dependency"] {
            fields.push((name.to_owned(), field(stamp, name).map(str::to_owned)));
        }
        fields
    };
    let (own, other) = (fields(own), fields(other));
    own.into_iter()
        .zip(other)
        .filter(|((_, a), (_, b))| a != b)
        .map(|((name, _), _)| name)
        .collect()
}

/// atpkg's per-user store prefix under `home` (aterm's `atpkg::platform::default_prefix`).
pub(super) fn atpkg_prefix(home: &Path) -> Result<PathBuf, String> {
    if cfg!(target_os = "macos") {
        Ok(home.join("Library/Application Support/aterm/pkg"))
    } else if cfg!(target_os = "linux") {
        Ok(home.join(".local/share/aterm/pkg"))
    } else {
        Err("atpkg keeps no store on this platform".into())
    }
}

/// Where atpkg keeps the `llvm-tree` trees built on `host`: `trees.noindex/llvm-tree/<host>`.
pub(super) fn store_dir(prefix: &Path, host: &str) -> PathBuf {
    prefix.join("trees.noindex").join(PROGRAM).join(host)
}

/// Whether atpkg's store holds a complete tree at `tree`: a real directory, beside a ready
/// marker that is a regular file whose first line is `ok`. A tree an install left unmarked,
/// or one an eviction has begun to remove (its marker goes first), is not complete.
fn complete(tree: &Path) -> bool {
    let Some(name) = tree.file_name().and_then(|name| name.to_str()) else { return false };
    let marker = tree.with_file_name(format!("{name}{READY_SUFFIX}"));
    fs::symlink_metadata(tree).is_ok_and(|meta| meta.is_dir())
        && fs::symlink_metadata(&marker).is_ok_and(|meta| meta.is_file())
        && fs::read_to_string(&marker).is_ok_and(|text| text.lines().next() == Some("ok"))
}

/// Why the store `store` holds no tree for `inputs`: each complete tree of another key, and
/// the inputs it differs in, or that it holds none.
fn absent(store: &Path, inputs: &str) -> String {
    let mut others = Vec::new();
    for entry in fs::read_dir(store).into_iter().flatten().flatten() {
        let tree = entry.path();
        let Some(name) = entry.file_name().to_str().map(str::to_owned) else { continue };
        if name.len() != 64 || !name.bytes().all(|b| b.is_ascii_hexdigit()) || !complete(&tree) {
            continue;
        }
        let what = match fs::read_to_string(tree.join(KEY_FILE)) {
            Ok(theirs) => match differing_inputs(inputs, &theirs) {
                differ if differ.is_empty() => "names the same inputs under another key".into(),
                differ => format!("differs in {}", differ.join(", ")),
            },
            Err(error) => format!("has no readable {KEY_FILE} ({error})"),
        };
        others.push(format!("{} {what}", &name[..12]));
    }
    others.sort();
    if others.is_empty() {
        format!("atpkg's store holds no {PROGRAM} at {}", store.display())
    } else {
        format!("atpkg's store holds no {PROGRAM} of this key ({})", others.join("; "))
    }
}

/// What [`take`] laid.
#[derive(Debug)]
pub(super) struct Taken {
    /// The key it was taken under.
    pub(super) key: String,
    /// Regular files in the clone.
    pub(super) files: u64,
}

/// The suffix of the clone while it is checked. An interrupted take leaves an entry
/// `llvm<suffix>`, which the next build's stage-1 seed reset removes with its own.
fn partial(dest: &Path) -> Result<PathBuf, String> {
    let name = dest.file_name().and_then(|name| name.to_str()).ok_or("no LLVM directory name")?;
    Ok(dest.with_file_name(format!("{name}{}", crate::utils::trust_stage1_seed::PARTIAL)))
}

/// Clones the tree of `inputs` from atpkg's store `store` to `dest`, which must not exist,
/// and returns its key; or why it did not. Nothing is left at `dest` on a refusal.
pub(super) fn take(store: &Path, inputs: &str, dest: &Path) -> Result<Taken, String> {
    let key = key(inputs);
    let tree = store.join(&key);
    if !complete(&tree) {
        return Err(absent(store, inputs));
    }
    if fs::symlink_metadata(dest).is_ok() {
        return Err(format!("{} already exists", dest.display()));
    }
    let parent = dest.parent().ok_or("the LLVM directory has no parent")?;
    let parent = parent.canonicalize().map_err(|e| format!("{}: {e}", parent.display()))?;
    crate::utils::trust_stage1_seed::same_volume(&tree, &parent)?;
    let staged = partial(dest)?;
    if fs::symlink_metadata(&staged).is_ok() {
        fs::remove_dir_all(&staged).map_err(|e| format!("{}: {e}", staged.display()))?;
    }
    crate::utils::trust_stage1_seed::clonefile(&tree, &staged)
        .map_err(|e| format!("cannot clone {} by clonefile(2): {e}", tree.display()))?;
    let final_dir = parent.join(dest.file_name().ok_or("no LLVM directory name")?);
    let checked = check(&tree, &staged, inputs).and_then(|files| {
        // The clone is this worktree's own tree, which its builds write and remove as they do
        // one they made: owner-writable, whatever modes the store keeps.
        owner_writable(&staged).map_err(|e| format!("cannot make the clone writable: {e}"))?;
        relocate_manifest(&staged, field(inputs, "host").ok_or("no host")?, &final_dir)?;
        fs::rename(&staged, dest).map_err(|e| format!("cannot rename the clone: {e}"))?;
        Ok(files)
    });
    match checked {
        Ok(files) => {
            // atpkg's record of the tree's use (its mtime), which keeps it from `aterm pkg gc`.
            let _ = fs::File::create(tree.with_file_name(format!("{key}{USED_SUFFIX}")))
                .and_then(|used| used.set_modified(std::time::SystemTime::now()));
            Ok(Taken { key, files })
        }
        Err(why) => match remove_tree(&staged) {
            Ok(()) => Err(why),
            Err(error) => Err(format!("{why}; and the clone {} stays: {error}", staged.display())),
        },
    }
}

/// Gives the owner write (and search) permission on every entry of `root`, as atpkg's own
/// removal does before it removes a tree that may hold read-only directories.
fn owner_writable(root: &Path) -> io::Result<()> {
    #[cfg(unix)]
    for entry in walkdir::WalkDir::new(root).follow_links(false) {
        use std::os::unix::fs::PermissionsExt;
        let entry = entry.map_err(io::Error::other)?;
        let meta = entry.metadata().map_err(io::Error::other)?;
        let mode = meta.permissions().mode();
        let wanted = if meta.is_dir() { mode | 0o700 } else { mode | 0o200 };
        if wanted != mode && !meta.file_type().is_symlink() {
            fs::set_permissions(entry.path(), fs::Permissions::from_mode(wanted))?;
        }
    }
    // No store hands a tree out off Unix (`clonefile(2)` is macOS's).
    #[cfg(not(unix))]
    let _ = root;
    Ok(())
}

/// Removes the tree `root` (none is no error), its directories made writable first.
pub(super) fn remove_tree(root: &Path) -> io::Result<()> {
    match fs::symlink_metadata(root) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
        Ok(meta) if meta.is_dir() => owner_writable(root)?,
        Ok(_) => {}
    }
    fs::remove_dir_all(root)
}

/// Holds the clone `staged` of the store's `tree` to `inputs`. Returns how many regular
/// files it holds.
fn check(tree: &Path, staged: &Path, inputs: &str) -> Result<u64, String> {
    // atpkg marks a tree ready before anyone may read it and unmarks it before it removes
    // it: a tree evicted while it was cloned is not taken half.
    if !complete(tree) {
        return Err("the store's tree was removed while it was cloned".into());
    }
    let mut files = 0;
    for entry in walkdir::WalkDir::new(staged).follow_links(false) {
        let entry = entry.map_err(|e| e.to_string())?;
        let kind = entry.file_type();
        if kind.is_file() {
            files += 1;
        } else if !kind.is_dir() {
            return Err(format!(
                "{} is neither a file nor a directory; a package tree holds no other kind",
                entry.path().strip_prefix(staged).unwrap_or(entry.path()).display()
            ));
        }
    }
    let recorded = fs::read_to_string(staged.join(KEY_FILE))
        .map_err(|e| format!("the tree has no readable {KEY_FILE}: {e}"))?;
    if recorded != inputs {
        return Err(format!(
            "the tree's {KEY_FILE} differs in {}",
            differing_inputs(inputs, &recorded).join(", ")
        ));
    }
    let stamp = stamp_of(inputs).ok_or("the key inputs name no stamp")?;
    if fs::read_to_string(staged.join(".llvm-stamp")).ok().as_deref() != Some(stamp) {
        return Err("the tree's .llvm-stamp is not the one its key names".into());
    }
    Ok(files)
}

/// Writes the install manifest of the clone `staged` (`build/install_manifest.txt`, which
/// names every installed file by its absolute path in the tree that built it) with each
/// path under `final_dir` instead: the manifest is how the LLVM step finds what the tree
/// installed. Every line must name a file of the tree, under one `.../<host>/llvm` root.
fn relocate_manifest(staged: &Path, host: &str, final_dir: &Path) -> Result<(), String> {
    let manifest = staged.join("build/install_manifest.txt");
    let text = fs::read_to_string(&manifest)
        .map_err(|e| format!("the tree has no readable build/install_manifest.txt: {e}"))?;
    let marker = format!("/{host}/llvm/");
    let first = text.lines().next().ok_or("the tree's install manifest is empty")?;
    let built_in = first
        .find(&marker)
        .map(|at| &first[..at + marker.len()])
        .ok_or("the tree's install manifest names no LLVM root")?;
    let final_dir = final_dir.to_str().ok_or("this LLVM directory is not UTF-8")?;
    let mut relocated = String::with_capacity(text.len());
    for line in text.lines() {
        let relative = line
            .strip_prefix(built_in)
            .filter(|rest| {
                !rest.is_empty()
                    && Path::new(rest)
                        .components()
                        .all(|c| matches!(c, std::path::Component::Normal(_)))
            })
            .ok_or_else(|| {
                format!("the tree's install manifest names {line:?} outside its root")
            })?;
        if !fs::symlink_metadata(staged.join(relative)).is_ok_and(|meta| meta.is_file()) {
            return Err(format!("the tree's install manifest names {relative}, which it lacks"));
        }
        relocated.push_str(final_dir);
        relocated.push('/');
        relocated.push_str(relative);
        relocated.push('\n');
    }
    fs::write(&manifest, relocated).map_err(|e| format!("{}: {e}", manifest.display()))
}

impl Compilers {
    /// Asks the host compilers `cc` and `cxx` (with the environment and the flags cc-rs
    /// selected for them, which the CMake request passes on) what the key names.
    pub(super) fn query(cc: &cc::Tool, cxx: &cc::Tool) -> Result<Self, String> {
        crate::utils::exec::require_standalone_process("LLVM package compiler query")
            .map_err(|e| e.to_string())?;
        let driver = run(cxx, &["-###", "-x", "c++", "-c", "/dev/null", "-o", "/dev/null"])?;
        let (target, sdk) = driver_target(&String::from_utf8_lossy(&driver.stderr));
        Ok(Self { cc: version_line(cc)?, cxx: version_line(cxx)?, target, sdk })
    }
}

/// Runs the compiler `tool` with its environment, its flags (as the CMake request passes
/// them: without optimization levels) and `args`.
fn run(tool: &cc::Tool, args: &[&str]) -> Result<std::process::Output, String> {
    let flags = tool.args().iter().filter(|flag| {
        !flag.to_str().is_some_and(|flag| flag.starts_with("-O") || flag.starts_with("/O"))
    });
    let output = std::process::Command::new(tool.path())
        .envs(tool.env().iter().map(|(key, value)| (key, value)))
        .args(flags)
        .args(args)
        .output()
        .map_err(|e| format!("{} {}: {e}", tool.path().display(), args.join(" ")))?;
    if output.status.success() {
        Ok(output)
    } else {
        Err(format!("{} {} failed ({})", tool.path().display(), args.join(" "), output.status))
    }
}

/// The first line of the compiler `tool`'s `--version`.
fn version_line(tool: &cc::Tool) -> Result<String, String> {
    let output = run(tool, &["--version"])?;
    let text = String::from_utf8_lossy(&output.stdout);
    match text.lines().next().map(str::trim) {
        Some(line) if !line.is_empty() => Ok(line.to_owned()),
        _ => Err(format!("{} --version names no compiler", tool.path().display())),
    }
}

/// The target and SDK version a clang driver's `-###` names for its compile job: `"-triple"
/// "<target>"` and `-target-sdk-version=<version>`; `unreported` and `none` where it names
/// neither (a driver that is not clang's).
pub(super) fn driver_target(jobs: &str) -> (String, String) {
    let words: Vec<&str> = jobs.split_whitespace().map(|word| word.trim_matches('"')).collect();
    let target = words
        .windows(2)
        .find(|pair| pair[0] == "-triple")
        .map_or("unreported", |pair| pair[1])
        .to_owned();
    let sdk = words
        .iter()
        .find_map(|word| word.strip_prefix("-target-sdk-version="))
        .unwrap_or("none")
        .to_owned();
    (target, sdk)
}

/// Writes `inputs` as the key inputs of the completed LLVM tree `root`; with none, removes
/// a record a previous build left, so a tree never carries inputs other than its own.
pub(super) fn record(root: &Path, inputs: Option<&str>) -> io::Result<()> {
    let path = root.join(KEY_FILE);
    match inputs {
        Some(inputs) => fs::write(path, inputs),
        None => match fs::remove_file(path) {
            Err(error) if error.kind() != io::ErrorKind::NotFound => Err(error),
            _ => Ok(()),
        },
    }
}

#[cfg(all(test, target_os = "macos"))]
#[path = "tests/package_tree_tests.rs"]
mod tests;
