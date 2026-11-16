//! Trust: seed a fresh worktree's stage 1 from another worktree's green one (EW-9).
//!
//! Every new worktree of this repository used to pay a cold stage 1. The first build of a
//! fresh worktree (one with no `build/<host>/stage1-*` yet) now clones, by APFS clone, the
//! stage 1 of another worktree of the same repository when that tree's last successful
//! stage-1 build recorded the same key, and builds cold on any doubt.
//!
//! **The key** ([`Key`]) is what bootstrap knows stage 1 was built from: the source
//! identity of TB1 (`utils::trust_source_identity`: the committed sources, the worktree's
//! departures from them, and the configuration, with each tree's own root written as a
//! token), the host, the stage-0 seed (its extraction stamp and the digests of the
//! stage-0 `rustc` and `cargo`), the environment variables a build reads
//! ([`keyed_env`]) and the command-line flags that may change what it makes
//! ([`key_flags`]), each tree's roots written as tokens ([`key_value`]). A successful
//! invocation that assembled the host stage-1 compiler writes it to
//! `build/<host>/trust-stage1-seed` ([`Seeding::finish`]) when its sysroot is usable and
//! its sources are still the ones it named; every other invocation removes it first
//! ([`begin`]), so a record exists only while the build directory is what a green build
//! left.
//!
//! **What the clone may serve.** A seeded tree must be what the donor's build directory
//! would be if the donor itself were rebuilt in place from the recipient's files: Targo
//! (cargo) and bootstrap then decide freshness exactly as they would in the donor. Three
//! things stand between a plain clone and that:
//! * *Times.* A fresh checkout's files are newer than every cloned output. Each file a
//!   cloned unit read is compared with the donor's ([`carry_time`]). Where the two hold the
//!   same bytes, Targo is to see the donor's time: when the donor's is the older, it goes
//!   into a table that only in-tree Targo reads (`-Ztrust-carried-times`, [`CARRIED_TIMES`])
//!   and that holds only while the file stays as it was compared; a time is never set back
//!   on the file itself, which every other time-based cache in the tree also reads. A file
//!   that differs, or changes while it is compared, is given a time later than every
//!   cloned output, so whatever read it rebuilds. Each path is compared as the file the
//!   system resolves it to ([`carry_times`]), and a donor that was seeded itself is
//!   compared by the times its own table gives its Targo ([`DonorTimes`]). A build script
//!   that names no input is fingerprinted by its package's newest time, which is not
//!   carried: it reruns.
//! * *Paths Targo records.* In-tree Targo records paths and values under the tree's roots
//!   as tokens (`-Ztrust-relocation-roots`, [`relocation_roots`]), so a fingerprint means
//!   the same in either tree and is checked against the recipient's files.
//! * *Paths compiled into artifacts.* An artifact that names the donor's tree outside its
//!   debug information (an `env!("CARGO_MANIFEST_DIR")`, a build script's `OUT_DIR`
//!   output) would make the recipient read or run the donor's files. Every cloned file is
//!   searched for the donor's roots ([`audit`]): debug information may keep them (the
//!   DWARF sections and symbol strings of Mach-O objects and images), a few
//!   bootstrap-owned text files are rewritten, and any other unit whose files name them is
//!   rebuilt, which rebuilds what depends on it.
//!
//! **What is refused** (the tree builds cold, saying why): a key that differs in any
//! input; a donor whose build lock stays held for a minute, or whose record changed; a
//! donor whose lease a seed that is gone left behind (not waited for: only the donor's
//! next build reclaims it); another volume; a clone that cannot be made by
//! `clonefile(2)`; any donor path the
//! audit cannot attribute to a unit; an input of this tree that resolves outside it to a
//! file other than the donor's; a dependency file that cannot be read, or a relative
//! `rerun-if-changed` path whose package cannot be named ([`rerun_inputs`]). A tree whose
//! stage-0 `rustc` or `cargo` is not x.py's extraction is neither a donor nor a recipient
//! ([`stage0_is_extracted`]). One `build/` is never shared: everything is cloned, never
//! linked. `rust.trust-stage1-seed = false` turns seeding off.
//!
//! Decisions and what remains: docs/DECISION_QUEUE.md, "EW-9".

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::io::{self, Read};
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime};

use sha2::Digest;

use crate::core::builder::Kind;
use crate::core::session::Session;
use crate::utils::channel::GitInfo;
use crate::utils::helpers::hex_encode;
use crate::utils::trust_source_identity;

/// The record a green stage-1 build leaves in `build/<host>/`.
pub(crate) const RECORD: &str = "trust-stage1-seed";
const RECORD_SCHEMA: &str = "trust-stage1-seed/v1";
const KEY_SCHEMA: &str = "trust-stage1-seed-key/v1";
/// Written before the cloned entries are renamed into place and removed after: an
/// interrupted seed is undone by the next run instead of being half trusted.
const INCOMPLETE: &str = ".trust-stage1-seed-incomplete";
const PARTIAL: &str = ".trust-seed-partial";
/// The purpose the lease a seed takes on its donor records. The donor's lock script waits
/// for a live holder with it, and a seed judges a gone one by it ([`clone_from_with`]).
const SEED_SOURCE: &str = "stage-1 seed source (another worktree clones this build tree)";
/// The carried-times table a seed leaves in `build/<host>/` for in-tree Targo
/// (`-Ztrust-carried-times`; Targo's `util::carried_times` has the format).
pub(crate) const CARRIED_TIMES: &str = "trust-carried-times";
const CARRIED_TIMES_SCHEMA: &str = "trust-carried-times/v1";
/// How a key writes this tree's roots: the source tree, and a git directory outside it.
const SRC_TOKEN: &[u8] = b"\0src\0";
const GIT_TOKEN: &[u8] = b"\0git\0";

static STAGE1_ASSEMBLED: AtomicBool = AtomicBool::new(false);

/// Called by `compile::Assemble` when this invocation assembled the host stage-1
/// compiler: only such an invocation writes a record.
pub(crate) fn note_stage1_assembled() {
    STAGE1_ASSEMBLED.store(true, Ordering::SeqCst);
}

/// The entries of `build/<host>/` a seed clones. The recipient keeps its own `stage0`
/// (x.py extracted it before bootstrap ran, from the archives `src/stage0` pins), and
/// bootstrap's `Sysroot` step deletes and rebuilds the `stage0-sysroot` and `stage1`
/// sysroots on every build.
fn seeded(name: &str) -> bool {
    !name.ends_with(PARTIAL)
        && (name == "bootstrap-tools" || name == "llvm" || name.starts_with("stage1-"))
}

/// The roots in-tree Targo records paths under (`-Ztrust-relocation-roots`): the
/// canonical source tree, then its git directory (`<root>/.git`, or
/// `<common>/worktrees/<name>` for a linked worktree, under which its submodules'
/// repositories live). `None` when a root cannot be named or holds a `,`, which the flag
/// cannot carry: Targo then records absolute paths, as it always did.
pub(crate) fn relocation_roots(src: &Path) -> Option<String> {
    static CACHED: OnceLock<(PathBuf, Option<String>)> = OnceLock::new();
    if let Some((cached_src, roots)) = CACHED.get()
        && cached_src == src
    {
        return roots.clone();
    }
    let roots = Roots::of(src).map(|roots| roots.flag()).filter(|flag| !flag.contains('\0'));
    let _ = CACHED.set((src.to_owned(), roots.clone()));
    roots
}

/// The carried-times table in-tree Targo is given (`-Ztrust-carried-times`) for the target
/// directory `target_dir`: the one a seed left beside it, when `target_dir` is an entry a
/// seed clones. The units of any other target directory were never cloned, and Targo
/// reads every file's own time for them.
pub(crate) fn carried_times(target_dir: &Path) -> Option<PathBuf> {
    if !seeded(target_dir.file_name()?.to_str()?) {
        return None;
    }
    let table = target_dir.parent()?.join(CARRIED_TIMES);
    table.is_file().then_some(table)
}

/// The `root-relocation` record in-tree Targo leaves beside the output of a build-script
/// run recorded under `roots` (Targo's `RelocationRoots::record`): each root, then its
/// other spelling, which a canonical root ([`Roots::of`]) has none of.
pub(crate) fn relocation_record(roots: &Roots) -> Vec<u8> {
    let mut record = b"trust-relocation-roots-v1\0".to_vec();
    for root in std::iter::once(&roots.src).chain(&roots.git_dir) {
        record.extend_from_slice(root.as_os_str().as_encoded_bytes());
        record.extend_from_slice(b"\0\0");
    }
    record
}

/// A tree's roots, as [`relocation_roots`] names them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Roots {
    pub(crate) src: PathBuf,
    pub(crate) git_dir: Option<PathBuf>,
}

impl Roots {
    fn of(src: &Path) -> Option<Self> {
        crate::utils::exec::require_standalone_process("seed source-root Git query").ok()?;
        let src = src.canonicalize().ok()?;
        let output = std::process::Command::new("git")
            .args(["rev-parse", "--absolute-git-dir"])
            .current_dir(&src)
            .env_remove("GIT_DIR")
            .env_remove("GIT_WORK_TREE")
            .output()
            .ok()?;
        let git_dir = output
            .status
            .success()
            .then(|| String::from_utf8(output.stdout).ok())
            .flatten()
            .map(|dir| PathBuf::from(dir.trim_end_matches('\n')));
        // Build scripts print the git directory as git spells it, and only one spelling
        // of each root can be recognized in what they record.
        if let Some(dir) = &git_dir
            && dir.canonicalize().ok().as_ref() != Some(dir)
        {
            return None;
        }
        let roots = Self { src, git_dir };
        roots.spellable().then_some(roots)
    }

    /// Whether every root is spelled only in bytes that no quoting or escaping changes
    /// (ASCII letters and digits, `/`, `.`, `_`, `-`). A JSON string, a URL or a shell
    /// word spells any other byte differently, and the audit would not find the donor's
    /// roots written that way. It also keeps out `,`, which separates the roots in
    /// `-Ztrust-relocation-roots`.
    fn spellable(&self) -> bool {
        let fine = |path: &Path| {
            path.to_str().is_some_and(|text| {
                text.bytes().all(|byte| byte.is_ascii_alphanumeric() || b"/._-".contains(&byte))
            })
        };
        fine(&self.src) && self.git_dir.as_deref().is_none_or(fine)
    }

    fn flag(&self) -> String {
        match &self.git_dir {
            Some(git_dir) => format!("{},{}", self.src.display(), git_dir.display()),
            None => self.src.display().to_string(),
        }
    }

    /// `path` in `to`'s tree when it lies in this tree (its git directory first, which
    /// may lie inside its source tree), else `None`.
    fn map(&self, path: &Path, to: &Roots) -> Option<PathBuf> {
        if let (Some(from), Some(dest)) = (&self.git_dir, &to.git_dir)
            && let Ok(rest) = path.strip_prefix(from)
        {
            return Some(dest.join(rest));
        }
        path.strip_prefix(&self.src).ok().map(|rest| to.src.join(rest))
    }

    /// Whether `path` lies in this tree: its source tree or its git directory.
    fn holds(&self, path: &Path) -> bool {
        path.starts_with(&self.src)
            || self.git_dir.as_ref().is_some_and(|dir| path.starts_with(dir))
    }

    /// The byte strings that name this tree: each root, as found in a file.
    fn needles(&self) -> Vec<Vec<u8>> {
        let mut needles = vec![self.src.as_os_str().as_encoded_bytes().to_vec()];
        if let Some(git_dir) = &self.git_dir
            && !git_dir.starts_with(&self.src)
        {
            needles.push(git_dir.as_os_str().as_encoded_bytes().to_vec());
        }
        needles
    }
}

/// The key of a stage-1 build directory: the record whose SHA-256 a donor and a
/// recipient compare. One `<field> <value>` line per input, so a refusal can say which
/// input differs ([`differing_fields`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Key {
    pub(crate) record: String,
}

/// What a [`Key`] is made of.
pub(crate) struct KeyInputs<'a> {
    pub(crate) host: &'a str,
    /// The TB1 source identity (40 hex digits).
    pub(crate) identity: &'a str,
    /// `build/<host>/stage0/.rustc-stamp`, the digest of the archives x.py extracted.
    pub(crate) stage0: &'a str,
    /// `(path, sha256)` of the stage-0 `rustc` and `cargo`, the path relative to the tree
    /// when it lies in it.
    pub(crate) tools: Vec<(String, String)>,
    /// The keyed environment ([`keyed_env`]), root-normalized and sorted.
    pub(crate) env: Vec<(String, String)>,
    /// The command-line flags that change what a build makes ([`key_flags`]).
    pub(crate) flags: Vec<(String, String)>,
}

impl Key {
    pub(crate) fn new(inputs: &KeyInputs<'_>) -> Self {
        let mut record = format!(
            "{KEY_SCHEMA}\nhost {}\nidentity {}\nstage0 {:?}\n",
            inputs.host, inputs.identity, inputs.stage0
        );
        for (path, digest) in &inputs.tools {
            record.push_str(&format!("tool {path:?} {digest}\n"));
        }
        for (name, value) in &inputs.env {
            record.push_str(&format!("env {name}={value:?}\n"));
        }
        for (name, value) in &inputs.flags {
            record.push_str(&format!("flag {name}={value:?}\n"));
        }
        Self { record }
    }

    pub(crate) fn digest(&self) -> String {
        hex_encode(sha2::Sha256::digest(self.record.as_bytes()).as_slice())
    }
}

/// The inputs of two keys that differ: `identity`, `env PATH`, `tool "<path>"`, ...
pub(crate) fn differing_fields(own: &Key, other: &Key) -> Vec<String> {
    fn fields(key: &Key) -> BTreeMap<String, String> {
        key.record
            .lines()
            .map(|line| {
                let (name, value) = line.split_once(' ').unwrap_or((line, ""));
                let name = match name {
                    "env" | "flag" => {
                        format!("{name} {}", value.split_once('=').map_or(value, |v| v.0))
                    }
                    "tool" => format!("tool {}", value.rsplit_once(' ').map_or(value, |v| v.0)),
                    _ => name.to_owned(),
                };
                (name, line.to_owned())
            })
            .collect()
    }
    let (own, other) = (fields(own), fields(other));
    let names: BTreeSet<&String> = own.keys().chain(other.keys()).collect();
    names.into_iter().filter(|name| own.get(*name) != other.get(*name)).cloned().collect()
}

/// Whether the environment variable `name` is part of the key: what bootstrap, Targo,
/// rustc, the C toolchain and the build scripts of this tree read, by name or prefix.
/// The build-lock facade's own variables name this invocation, not what it builds,
/// `RUST_BACKTRACE` changes only how a panic is printed, and `CARGO_LOG` only filters what
/// Targo logs to stderr (`setup_logger` in its `main.rs`; no build script of the tree reads
/// it). `CARGO_LOG_PROFILE` stays keyed: it writes a trace file.
pub(crate) fn keyed_env(name: &str) -> bool {
    const EXACT: &[&str] = &[
        "PATH",
        "SDKROOT",
        "DEVELOPER_DIR",
        "MACOSX_DEPLOYMENT_TARGET",
        "SOURCE_DATE_EPOCH",
        "LIBRARY_PATH",
        "CPATH",
        "C_INCLUDE_PATH",
        "CPLUS_INCLUDE_PATH",
        "ARCHFLAGS",
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_COMMON_DIR",
        "GIT_INDEX_FILE",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CEILING_DIRECTORIES",
        "GIT_NAMESPACE",
        "HOME",
        "XDG_CONFIG_HOME",
        "LD",
    ];
    const PREFIXES: &[&str] = &[
        "RUST",
        "CARGO",
        "TARGO",
        "CFG_",
        "CC",
        "CXX",
        "CFLAGS",
        "CXXFLAGS",
        "CPPFLAGS",
        "LDFLAGS",
        "AR_",
        "RANLIB",
        "LLVM",
        "CLANG",
        "LIBCLANG",
        "PKG_CONFIG",
        "DYLD_",
        "LD_",
        "CMAKE",
        "NINJA",
        "PYTHON",
        "TRUST",
        "ALAB_",
        "BOOTSTRAP",
        "TOOLCHAIN_",
        "TVC_",
        "MC_",
        "TIPPY",
        "CLIPPY",
        "MIRI",
        "GIT_CONFIG",
        "HOST_",
        "TARGET_",
        "OPENSSL_",
        "LIBZ_SYS_",
        "LIBGIT2_",
        "LIBSSH2_",
        "LIBCURL_",
        "LIBSQLITE3_",
        "JEMALLOC_",
        "ZSTD_",
        "MACOSX_",
        "IPHONEOS_",
    ];
    const VOLATILE: &[&str] = &["RUST_BACKTRACE", "RUST_LIB_BACKTRACE", "CARGO_LOG"];
    if VOLATILE.contains(&name)
        || name.starts_with("TRUST_BUILD_LOCK_")
        || name.starts_with("TRUST_NATIVE_REPO_PARENT_")
    {
        return false;
    }
    EXACT.contains(&name) || name == "AR" || PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}

/// Each spelling of a root of `roots` with the token a key writes it as: the source tree,
/// and its git directory when that lies outside it.
pub(crate) fn root_tokens(roots: &Roots) -> Vec<(Vec<u8>, &'static [u8])> {
    let mut tokens = vec![(roots.src.as_os_str().as_encoded_bytes().to_vec(), SRC_TOKEN)];
    if let Some(git_dir) = &roots.git_dir
        && !git_dir.starts_with(&roots.src)
    {
        tokens.push((git_dir.as_os_str().as_encoded_bytes().to_vec(), GIT_TOKEN));
    }
    tokens
}

/// `value` as a key writes it: each root at path boundaries
/// ([`trust_source_identity::replace_roots`]) as `{src}` or `{git}`, and every brace of the
/// value itself doubled, so no value spells a token and two roots never share one. A value
/// that is not UTF-8 is written `{bytes:<hex>}`, which no escaped text spells either.
pub(crate) fn key_value(value: &[u8], roots: &[(Vec<u8>, &'static [u8])]) -> String {
    let pairs: Vec<(&[u8], &[u8])> =
        roots.iter().map(|(root, token)| (&root[..], *token)).collect();
    match String::from_utf8(trust_source_identity::replace_roots(value, &pairs)) {
        Ok(text) => text
            .replace('{', "{{")
            .replace('}', "}}")
            .replace("\0src\0", "{src}")
            .replace("\0git\0", "{git}"),
        Err(error) => format!("{{bytes:{}}}", hex_encode(error.as_bytes())),
    }
}

/// The keyed environment of `vars` ([`keyed_env`]), each value as [`key_value`] writes
/// it, sorted by name.
pub(crate) fn key_env(
    vars: impl Iterator<Item = (std::ffi::OsString, std::ffi::OsString)>,
    roots: &[(Vec<u8>, &'static [u8])],
) -> Vec<(String, String)> {
    let mut env: Vec<(String, String)> = vars
        .filter_map(|(name, value)| {
            // A name that is not UTF-8 is keyed by what its readable part names.
            let name = name.as_encoded_bytes();
            keyed_env(&String::from_utf8_lossy(name))
                .then(|| (key_value(name, &[]), key_value(value.as_encoded_bytes(), roots)))
        })
        .collect();
    env.sort();
    env
}

/// The command-line flags of an invocation that may change what its build makes, each as
/// [`key_value`] writes its value: every `--set` (sorted), the configuration, source and
/// build directories, the build, host and target triples, `--incremental`, `--warnings`,
/// the profile-guided and BOLT settings, reproducible artifacts, `--ci`, the stage-0
/// validation, the rustc error format, and the `compile-time-deps` and `skip-std-check`
/// switches. Left out: what is built (the command, its paths and arguments, `--stage`,
/// `--exclude`, `--skip`) and how the run reports or paces itself (verbosity, jobs,
/// colour, JSON output, `--on-fail`); `--keep-stage` and `--bypass-bootstrap-lock` turn
/// seeding off.
pub(crate) fn key_flags(
    flags: &crate::core::config::flags::Flags,
    roots: &[(Vec<u8>, &'static [u8])],
) -> Vec<(String, String)> {
    let mut set = flags.set.clone();
    set.sort();
    let fields = [
        ("set", format!("{set:?}")),
        ("config", format!("{:?}", flags.config)),
        ("src", format!("{:?}", flags.src)),
        ("build-dir", format!("{:?}", flags.build_dir)),
        ("build", format!("{:?}", flags.build)),
        ("host", format!("{:?}", flags.host)),
        ("target", format!("{:?}", flags.target)),
        ("incremental", format!("{:?}", flags.incremental)),
        ("warnings", format!("{:?}", flags.warnings)),
        ("rust-profile-generate", format!("{:?}", flags.rust_profile_generate)),
        ("rust-profile-use", format!("{:?}", flags.rust_profile_use)),
        ("llvm-profile-generate", format!("{:?}", flags.llvm_profile_generate)),
        ("llvm-profile-use", format!("{:?}", flags.llvm_profile_use)),
        ("enable-bolt-settings", format!("{:?}", flags.enable_bolt_settings)),
        ("reproducible-artifact", format!("{:?}", flags.reproducible_artifact)),
        ("ci", format!("{:?}", flags.ci)),
        ("skip-stage0-validation", format!("{:?}", flags.skip_stage0_validation)),
        ("rustc-error-format", format!("{:?}", flags.rustc_error_format)),
        (
            "compile-time-deps",
            format!(
                "{:?} {:?}",
                flags.compile_time_deps, flags.skip_std_check_if_no_download_rustc
            ),
        ),
    ];
    fields
        .into_iter()
        .map(|(name, value)| (name.to_owned(), key_value(value.as_bytes(), roots)))
        .collect()
}

/// The SHA-256 of the file at `path`.
fn file_digest(path: &Path) -> io::Result<String> {
    let mut hasher = sha2::Sha256::new();
    io::copy(&mut fs::File::open(path)?, &mut hasher)?;
    Ok(hex_encode(hasher.finalize().as_slice()))
}

/// A record, as [`Seeding::finish`] writes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Record {
    pub(crate) key: Key,
    pub(crate) roots: Roots,
}

impl Record {
    pub(crate) fn render(&self) -> String {
        let git_dir = self.roots.git_dir.as_ref().map_or("none".to_owned(), |dir| {
            dir.to_str().map_or_else(|| "none".to_owned(), str::to_owned)
        });
        format!(
            "{RECORD_SCHEMA}\nkey {}\nroot {}\ngitdir {git_dir}\n--\n{}",
            self.key.digest(),
            self.roots.src.display(),
            self.key.record
        )
    }

    /// The record `text` holds, or why it is not one. Its `key` line must be the digest
    /// of the key it carries.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let (head, key) = text.split_once("\n--\n").ok_or("no key")?;
        let mut lines = head.lines();
        if lines.next() != Some(RECORD_SCHEMA) {
            return Err(format!("not a {RECORD_SCHEMA} record"));
        }
        let mut field = |name: &str| {
            lines
                .next()
                .and_then(|line| line.strip_prefix(name))
                .and_then(|rest| rest.strip_prefix(' '))
                .map(str::to_owned)
                .ok_or_else(|| format!("no {name} line"))
        };
        let digest = field("key")?;
        let src = PathBuf::from(field("root")?);
        let git_dir = field("gitdir")?;
        let key = Key { record: key.to_owned() };
        if key.digest() != digest || !key.record.starts_with(KEY_SCHEMA) {
            return Err("its key does not match its digest".into());
        }
        if !src.is_absolute() {
            return Err("its root is not absolute".into());
        }
        let git_dir = (git_dir != "none").then(|| PathBuf::from(git_dir));
        Ok(Self { key, roots: Roots { src, git_dir } })
    }

    fn write(&self, host_dir: &Path) -> io::Result<()> {
        let partial = host_dir.join(format!("{RECORD}.{}.partial", std::process::id()));
        fs::write(&partial, self.render())?;
        fs::rename(&partial, host_dir.join(RECORD))
    }
}

/// The worktrees `git worktree list --porcelain` lists, as it prints them.
pub(crate) fn worktrees(porcelain: &str) -> Vec<PathBuf> {
    porcelain.lines().filter_map(|line| line.strip_prefix("worktree ")).map(PathBuf::from).collect()
}

/// What [`begin`] decided, for [`Seeding::finish`].
pub(crate) struct Seeding {
    /// Where this invocation's record goes when it is green: `None` when it writes none.
    record_dir: Option<PathBuf>,
}

/// Removes this build directory's record (any invocation may change what it names),
/// undoes an interrupted seed, and seeds a fresh tree when a donor's key matches.
pub(crate) fn begin(sess: &Session) -> Seeding {
    let config = &sess.config;
    let none = Seeding { record_dir: None };
    // These never write `build/<host>/`.
    if config.dry_run() || matches!(config.cmd.kind(), Kind::Format | Kind::Setup | Kind::Vendor) {
        return none;
    }
    let host_dir = config.out.join(&*config.host_target.triple);
    reset(&host_dir, !config.bypass_bootstrap_lock);
    // Each root has one spelling: the canonical one, which is how bootstrap names this
    // tree's paths and how Targo is told its roots.
    if !trust_source_identity::names_sources(config)
        || Roots::of(&config.src).is_none_or(|roots| roots.src != config.src)
        || !config.keep_stage.is_empty()
        || !config.keep_stage_std.is_empty()
        || config.bypass_bootstrap_lock
        || !matches!(sess.rust_info(), GitInfo::Present(Some(_)))
        || config.out.canonicalize().ok() != config.src.join("build").canonicalize().ok()
        || !stage0_is_extracted(&host_dir, [&sess.initial_rustc, &sess.initial_cargo])
    {
        return none;
    }
    let seeding = Seeding { record_dir: Some(host_dir.clone()) };
    if config.trust_stage1_seed
        && cfg!(target_os = "macos")
        && fs::read_dir(&host_dir).is_ok_and(|entries| {
            !entries.flatten().any(|entry| entry.file_name().to_str().is_some_and(seeded))
        })
        && let Err(reason) = seed(sess, &host_dir)
    {
        println!("Stage-1 seed: {reason}; building stage 1 cold");
    }
    seeding
}

impl Seeding {
    /// Records the key of this build directory when this invocation was green and
    /// assembled the host stage-1 compiler. Called only after the build returned.
    pub(crate) fn finish(&self, sess: &Session) {
        let Some(host_dir) = &self.record_dir else { return };
        if !STAGE1_ASSEMBLED.load(Ordering::SeqCst) {
            return;
        }
        let GitInfo::Present(Some(identity)) = sess.version_info() else { return };
        let Some(roots) = Roots::of(&sess.config.src) else { return };
        // A green build is not yet a usable stage 1: one whose compiler refuses the std
        // beside it (E0514) is never offered.
        if let Some(why) = stage1_sysroot_mismatch(host_dir, &sess.config.host_target.triple) {
            println!("Stage-1 seed: no record written: {why}");
            return;
        }
        // The key names the sources as the build began; an edit since may have been
        // built in part, so the record is written only when they are named alike now.
        if let Some(why) = sources_moved(sess, &identity.sha) {
            println!("Stage-1 seed: no record written: {why}");
            return;
        }
        let key = match own_key(sess, &roots, &identity.sha) {
            Ok(key) => key,
            Err(error) => {
                eprintln!("WARNING: stage-1 seed record not written: {error}");
                return;
            }
        };
        if let Err(error) = (Record { key, roots }).write(host_dir) {
            eprintln!("WARNING: could not write {}: {error}", host_dir.join(RECORD).display());
        }
    }
}

/// Why the sources no longer carry the identity `identity` bootstrap named them by when
/// this invocation began, when they do not.
fn sources_moved(sess: &Session, identity: &str) -> Option<String> {
    let config = &sess.config;
    let GitInfo::Present(Some(head)) = sess.rust_info() else {
        return Some("git names no HEAD".into());
    };
    sources_moved_at(&config.src, config.config.as_deref(), head, identity)
}

/// [`sources_moved`] for the checkout `src` configured by `config`, whose HEAD was `head`.
/// Git is asked afresh: bootstrap's execution context answers a `git` command it has run
/// before from its cache, which would name the sources as they were when it began.
pub(crate) fn sources_moved_at(
    src: &Path,
    config: Option<&Path>,
    head: &crate::utils::channel::Info,
    identity: &str,
) -> Option<String> {
    let fresh = crate::utils::exec::ExecutionContext::new(0, false);
    let digest = trust_source_identity::config_digest(config, src);
    match trust_source_identity::of_sources(&fresh, src, &digest, head) {
        Ok(sources) if sources.info.sha == identity => None,
        Ok(_) => Some("the sources changed while it built".into()),
        Err(why) => Some(why),
    }
}

/// The stamp a crate carries of the compiler that built it, which that compiler compares
/// before it loads the crate (E0514): the first line of the compiler's `-vV` up to its
/// first `)`, as in `rustc 1.101.0-dev (c50c1e566 2026-11-05)`.
pub(crate) fn version_stamp(verbose_version: &str) -> Option<&str> {
    let line = verbose_version.lines().next()?;
    let end = line.find(')')?;
    line.starts_with("rustc ").then(|| &line[..=end])
}

/// Why the stage-1 sysroot in `host_dir` is not a usable stage 1, when it is not: its
/// compiler does not run, it holds no `std` or no `core`, or one beside it does not carry
/// that compiler's [`version_stamp`].
pub(crate) fn stage1_sysroot_mismatch(host_dir: &Path, host: &str) -> Option<String> {
    if let Err(error) =
        crate::utils::exec::require_standalone_process("seed compiler identity query")
    {
        return Some(error.to_string());
    }
    let stage1 = host_dir.join("stage1");
    let ran = std::process::Command::new(stage1.join("bin/rustc")).arg("-vV").output();
    let verbose_version = match ran {
        Ok(output) if output.status.success() => {
            String::from_utf8_lossy(&output.stdout).into_owned()
        }
        _ => return Some("the stage-1 compiler does not run".into()),
    };
    let Some(stamp) = version_stamp(&verbose_version) else {
        return Some("the stage-1 compiler names no version".into());
    };
    let finder = memchr::memmem::Finder::new(stamp.as_bytes());
    let lib = stage1.join("lib/rustlib").join(host).join("lib");
    let mut found = [false; 2];
    for entry in fs::read_dir(&lib).into_iter().flatten().flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let Some(which) = ["libstd-", "libcore-"].iter().position(|lib| name.starts_with(lib))
        else {
            continue;
        };
        if !name.ends_with(".rlib") {
            continue;
        }
        if !fs::read(entry.path()).is_ok_and(|data| finder.find(&data).is_some()) {
            return Some(format!("{name} was not built by the stage-1 compiler ({stamp})"));
        }
        found[which] = true;
    }
    match found {
        [true, true] => None,
        [false, _] => Some(format!("{} holds no std", lib.display())),
        [true, false] => Some(format!("{} holds no core", lib.display())),
    }
}

/// Whether the stage-0 `rustc` and `cargo` (`tools`) are x.py's extraction in
/// `host_dir/stage0`, which the key names by its stamp. One configured elsewhere
/// (`build.rustc`, `build.cargo`) would be named only by its executable, which
/// stays byte-identical while the compiler library it loads changes: such a tree is
/// neither a donor nor a recipient.
pub(crate) fn stage0_is_extracted(host_dir: &Path, tools: [&Path; 2]) -> bool {
    let Ok(stage0) = host_dir.join("stage0").canonicalize() else { return false };
    stage0.join(".rustc-stamp").is_file()
        && tools.iter().all(|tool| tool.canonicalize().is_ok_and(|tool| tool.starts_with(&stage0)))
}

fn own_key(sess: &Session, roots: &Roots, identity: &str) -> Result<Key, String> {
    let config = &sess.config;
    let host = &*config.host_target.triple;
    let stamp = config.out.join(host).join("stage0/.rustc-stamp");
    let stage0 = fs::read_to_string(&stamp).map_err(|e| format!("{}: {e}", stamp.display()))?;
    let tokens = root_tokens(roots);
    let mut tools = Vec::new();
    for tool in [&sess.initial_rustc, &sess.initial_cargo] {
        let digest = file_digest(tool).map_err(|e| format!("{}: {e}", tool.display()))?;
        let canonical = tool.canonicalize().unwrap_or_else(|_| tool.clone());
        tools.push((key_value(canonical.as_os_str().as_encoded_bytes(), &tokens), digest));
    }
    let env = key_env(std::env::vars_os(), &tokens);
    // The arguments bootstrap was started with, parsed as `cli_main` parsed them.
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flags = key_flags(&crate::core::config::flags::Flags::parse(&args), &tokens);
    Ok(Key::new(&KeyInputs { host, identity, stage0: stage0.trim(), tools, env, flags }))
}

/// Deletes what an interrupted seed left: its partial clones and table, and every entry
/// it renamed into place before it stopped. An entry is the one it placed while it keeps
/// the device and inode the marker names ([`marker_lines`]); one that does not was made
/// since by another run (one that bypasses the lock, which never undoes a seed) and is
/// left alone. An entry on a line that names no inode is removed.
fn undo_incomplete(host_dir: &Path) {
    let marker = host_dir.join(INCOMPLETE);
    if let Ok(lines) = fs::read_to_string(&marker) {
        println!("Stage-1 seed: removing the entries of an interrupted seed");
        for line in lines.lines() {
            let mut words = line.split(' ');
            let Some(name) = words.next().filter(|name| seeded(name)) else { continue };
            let id = words
                .next()
                .zip(words.next())
                .and_then(|(dev, ino)| Some((dev.parse::<u64>().ok()?, ino.parse::<u64>().ok()?)));
            let entry = host_dir.join(name);
            if Stat::of(&entry).is_ok_and(|stat| id.is_none_or(|id| id == (stat.dev, stat.ino))) {
                let _ = fs::remove_dir_all(&entry);
            }
        }
        let _ = fs::remove_file(host_dir.join(CARRIED_TIMES));
        let _ = fs::remove_file(&marker);
    }
    if let Ok(entries) = fs::read_dir(host_dir) {
        for entry in entries.flatten() {
            if entry.file_name().to_string_lossy().ends_with(PARTIAL) {
                let _ = fs::remove_dir_all(entry.path());
                let _ = fs::remove_file(entry.path());
                let _ = fs::remove_file(host_dir.join(CARRIED_TIMES));
            }
        }
    }
    // A table no seeded entry is left to use (they were removed) applies to nothing.
    if !has_seeded_entry(host_dir) {
        let _ = fs::remove_file(host_dir.join(CARRIED_TIMES));
    }
}

fn has_seeded_entry(host_dir: &Path) -> bool {
    fs::read_dir(host_dir).is_ok_and(|entries| {
        entries.flatten().any(|entry| entry.file_name().to_str().is_some_and(seeded))
    })
}

/// What every invocation that may write `build/<host>/` does first: removes the record
/// (the invocation may change what it names) and, when it holds the tree's `build/lock`,
/// undoes an interrupted seed ([`undo_incomplete`]). A run that bypasses the lock leaves
/// the rest alone: a seed under the lock may be in progress.
pub(crate) fn reset(host_dir: &Path, holds_lock: bool) {
    let _ = fs::remove_file(host_dir.join(RECORD));
    if holds_lock {
        undo_incomplete(host_dir);
    }
}

/// Seeds the fresh build directory `host_dir` from the first worktree whose record
/// matches, or says why none was used.
fn seed(sess: &Session, host_dir: &Path) -> Result<(), String> {
    crate::utils::exec::require_standalone_process("seed worktree discovery query")
        .map_err(|error| error.to_string())?;
    let started = Instant::now();
    // An entry changed within the last second may still be being written.
    let settled = SystemTime::now() - Duration::from_secs(1);
    let config = &sess.config;
    let host = &*config.host_target.triple;
    let own = Roots::of(&config.src).ok_or("this tree's roots cannot be named")?;
    // Targo re-roots a recorded run only under as many roots as it was recorded under.
    if own.git_dir.is_none() {
        return Err("git names no git directory for this tree".into());
    }
    // The identity this build carries, computed once per invocation, as `finish` records it.
    let GitInfo::Present(Some(identity)) = sess.version_info() else {
        return Err("git names no source identity".into());
    };
    let key = own_key(sess, &own, &identity.sha)?;
    let listing = std::process::Command::new("git")
        .args(["worktree", "list", "--porcelain"])
        .current_dir(&own.src)
        .output()
        .map_err(|e| format!("git worktree list: {e}"))?;
    let mut candidates = Vec::new();
    for tree in worktrees(&String::from_utf8_lossy(&listing.stdout)) {
        let Ok(tree) = tree.canonicalize() else { continue };
        if tree == own.src {
            continue;
        }
        let path = tree.join("build").join(host).join(RECORD);
        let Ok(text) = fs::read_to_string(&path) else { continue };
        let modified = fs::metadata(&path).and_then(|m| m.modified()).ok();
        match Record::parse(&text) {
            Ok(record) if record.roots.src != tree || record.roots.git_dir.is_none() => {
                println!("Stage-1 seed: {} names another tree; not used", path.display())
            }
            Ok(record) if record.key == key => candidates.push((modified, tree, record)),
            Ok(record) => println!(
                "Stage-1 seed: {} differs in {}; not used",
                tree.display(),
                differing_fields(&key, &record.key).join(", ")
            ),
            Err(error) => println!("Stage-1 seed: {}: {error}; not used", path.display()),
        }
    }
    candidates.sort_by_key(|candidate| std::cmp::Reverse(candidate.0));
    if candidates.is_empty() {
        return Err("no other worktree holds a green stage 1 with this key".into());
    }
    let candidates = candidates.into_iter().map(|(_, tree, record)| (tree, record)).collect();
    // A donor another seed clones from holds its lease for seconds: it is tried again for
    // a minute. One that began a build removed its record and is not waited for, nor one
    // whose lease a seed that is gone left behind.
    let patience = (Duration::from_secs(60), Duration::from_secs(5));
    let served = first_served(candidates, patience, |tree, record| {
        let (entries, donor_times) = clone_from(tree, record, host, host_dir)?;
        let placed =
            fix_clone(host_dir, &entries, &donor_times, &record.roots, &own, host, settled)
                .and_then(|report| rename_into_place(host_dir, &entries).map(|()| report));
        placed.map(|report| (tree.to_owned(), entries, report)).map_err(Refused::Failed)
    });
    let (tree, entries, report) = served.inspect_err(|_| undo_incomplete(host_dir))?;
    for why in refresh_indexes(&own.src) {
        println!("Stage-1 seed: {why}; the next build may rerun what watches it");
    }
    println!(
        "Stage-1 seed: cloned build/{host}/{{{}}} from {} (key {}) in {:.1}s; {} inputs read \
         as the donor's ({} by the carried-times table), {} differ and read later; {} unit(s) \
         name the donor's tree and rebuild{}",
        entries.join(","),
        tree.display(),
        &key.digest()[..12],
        started.elapsed().as_secs_f64(),
        report.carried,
        report.table,
        report.differing,
        report.rebuilt.len(),
        if report.rebuilt.is_empty() {
            String::new()
        } else {
            format!(": {}", report.rebuilt.iter().cloned().collect::<Vec<_>>().join(", "))
        }
    );
    Ok(())
}

/// What the first of `candidates` (in order) that `attempt` is served by returned. One
/// whose lease or lock is held ([`Refused::Held`]) is tried again every `pause` until
/// `patience` (the first of the pair) has passed; a failure ends the search.
pub(crate) fn first_served<T>(
    mut candidates: Vec<(PathBuf, Record)>,
    (patience, pause): (Duration, Duration),
    mut attempt: impl FnMut(&Path, &Record) -> Result<T, Refused>,
) -> Result<T, String> {
    let deadline = Instant::now() + patience;
    let mut waited = false;
    loop {
        let mut held = Vec::new();
        let mut busy = Vec::new();
        for (tree, record) in candidates {
            match attempt(&tree, &record) {
                Ok(served) => return Ok(served),
                Err(Refused::Held(why)) => {
                    busy.push(format!("{}: {why}", tree.display()));
                    held.push((tree, record));
                }
                Err(Refused::Busy(why)) => busy.push(format!("{}: {why}", tree.display())),
                Err(Refused::Failed(why)) => return Err(why),
            }
        }
        if held.is_empty() || Instant::now() + pause > deadline {
            return Err(format!("every matching worktree is busy ({})", busy.join("; ")));
        }
        if !waited {
            println!("Stage-1 seed: waiting for a matching worktree ({})", busy.join("; "));
            waited = true;
        }
        candidates = held;
        std::thread::sleep(pause);
    }
}

/// Refreshes the git index of this tree and of every submodule checked out in it, and
/// returns what could not be refreshed. Carrying a time changes a tracked file's stat
/// data, and git rewrites a repository's index the next time it compares that data (any
/// `git status`, among them the identity [`Seeding::finish`] computes after the build). A
/// build script that watches its repository's index (trust-vc-core's dirty check) would
/// then rerun in the build after the seeded one, and rebuild everything above it. Done
/// here, the rewrite comes before the build reads anything. It changes only the cached
/// stat data, never what git reports.
pub(crate) fn refresh_indexes(src: &Path) -> Vec<String> {
    if let Err(error) = crate::utils::exec::require_standalone_process("seed Git index refresh") {
        return vec![error.to_string()];
    }
    let git = |dir: &Path, args: &[&str]| {
        std::process::Command::new("git")
            .args(args)
            .current_dir(dir)
            .env_remove("GIT_DIR")
            .env_remove("GIT_WORK_TREE")
            .env_remove("GIT_INDEX_FILE")
            .stdin(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .output()
    };
    let mut repositories = vec![src.to_owned()];
    match git(src, &["submodule", "status", "--recursive"]) {
        Ok(output) if output.status.success() => {
            for line in String::from_utf8_lossy(&output.stdout).lines() {
                // ` <sha> <path> (<describe>)`; a `-` in place of the space: not checked out.
                let mut words = line.get(1..).unwrap_or_default().split(' ');
                if line.starts_with('-') {
                    continue;
                }
                if let (Some(_), Some(path)) = (words.next(), words.next()) {
                    repositories.push(src.join(path));
                }
            }
        }
        _ => return vec!["git could not list this tree's submodules".into()],
    }
    let mut failed = Vec::new();
    for repository in repositories {
        let refreshed =
            git(&repository, &["update-index", "-q", "--ignore-submodules", "--refresh"]);
        if !refreshed.is_ok_and(|output| output.status.success()) {
            failed.push(format!("git could not refresh the index of {}", repository.display()));
        }
    }
    failed
}

pub(crate) enum Refused {
    /// Its lease or `build/lock` is held while its record stands (read again when the
    /// lock is refused): try the next donor, and this one again shortly.
    Held(String),
    /// Its record changed, its lease's holder is a seed that is gone, or it cannot serve:
    /// try the next donor.
    Busy(String),
    Failed(String),
}

/// Clones the seeded entries of `tree`'s `build/<host>/` into `host_dir` as partial
/// entries, holding the donor's build lock (refused at once if held), and returns the
/// cloned names and the donor's carried times, read under that lock.
fn clone_from(
    tree: &Path,
    record: &Record,
    host: &str,
    host_dir: &Path,
) -> Result<(Vec<String>, DonorTimes), Refused> {
    clone_from_with(tree, record, host, host_dir, || {})
}

/// [`clone_from`], calling `cloned` once the entries are cloned and before the record is
/// read again.
fn clone_from_with(
    tree: &Path,
    record: &Record,
    host: &str,
    host_dir: &Path,
    cloned: impl FnOnce(),
) -> Result<(Vec<String>, DonorTimes), Refused> {
    let donor_dir = tree.join("build").join(host);
    let stands = || {
        fs::read_to_string(donor_dir.join(RECORD)).ok().map(|text| Record::parse(&text))
            == Some(Ok(record.clone()))
    };
    // A held donor is waited for only while its record stands: one whose record is gone
    // has begun a build, which removes it first, and will not serve.
    let held = |why: String| {
        if stands() { Refused::Held(why) } else { Refused::Busy("its record changed".into()) }
    };
    // Trust: this guard is acquired independently for the donor. Any parent
    // handoff in our environment belongs to the recipient, never this tree.
    let lease = build_helper::trust_repo_lock::BuildLease::acquire_independent(
        tree,
        SEED_SOURCE,
        "bootstrap stage-1 seed",
    )
    // Trust: EW-9 (22). A seed killed while it held this lease leaves it behind, and only
    // the donor's next acquire reclaims it (the lock script's stale rule; nothing here
    // takes it over, removes or changes it). A refusal whose record is a seed's and proves
    // that holder gone is not waited for; any doubt waits as before.
    .map_err(|e| {
        match build_helper::trust_repo_lock::gone_independent_holder(tree, SEED_SOURCE) {
            Some(pid) => Refused::Busy(format!(
                "a stage-1 seed that held its lease (pid {pid}) is gone; the donor's next \
                 build reclaims it ({e})"
            )),
            None => held(e),
        }
    })?;
    // Trust: use the same checked output guard as direct bootstrap. Do not
    // create absent donor state or treat a replacement lock as the same owner.
    #[cfg(unix)]
    let bootstrap_lock =
        build_helper::trust_output_lock::OutputLock::try_acquire_existing(&tree.join("build"))
            .map_err(|e| Refused::Busy(format!("build/lock: {e}")))?
            .ok_or_else(|| held("its bootstrap holds build/lock".into()))?;
    // Trust: preserve the existing platform lock without claiming Unix identity
    // validation where the shared checked guard is unsupported.
    #[cfg(not(unix))]
    let bootstrap_lock = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(tree.join("build/lock"))
        .map_err(|e| Refused::Busy(format!("build/lock: {e}")))?;
    #[cfg(not(unix))]
    bootstrap_lock.try_lock().map_err(|_| held("its bootstrap holds build/lock".into()))?;
    if !stands() {
        return Err(Refused::Busy("its record changed".into()));
    }
    lease.check_current().map_err(|error| {
        Refused::Busy(format!("its build-tree ownership changed before cloning: {error}"))
    })?;
    let donor_times = DonorTimes::read(&donor_dir).map_err(Refused::Busy)?;
    same_volume(&donor_dir, host_dir).map_err(Refused::Failed)?;
    let mut names: Vec<String> = fs::read_dir(&donor_dir)
        .map_err(|e| Refused::Failed(format!("{}: {e}", donor_dir.display())))?
        .flatten()
        .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_dir()))
        .filter_map(|entry| entry.file_name().into_string().ok())
        .filter(|name| seeded(name))
        .collect();
    names.sort();
    if !names.iter().any(|name| name == "stage1-rustc") {
        return Err(Refused::Busy("it holds no stage1-rustc".into()));
    }
    for name in &names {
        let from = donor_dir.join(name);
        let to = host_dir.join(format!("{name}{PARTIAL}"));
        clonefile(&from, &to).map_err(|e| {
            Refused::Failed(format!("cannot clone {} by clonefile(2): {e}", from.display()))
        })?;
    }
    cloned();
    // A run that ignores the locks (`--bypass-bootstrap-lock`) removes the record first.
    let record_stands = stands();
    let tree_ownership = lease.check_current();
    #[cfg(unix)]
    let ownership = bootstrap_lock.check_current();
    #[cfg(not(unix))]
    let ownership: Result<(), std::io::Error> = Ok(());
    if !record_stands || tree_ownership.is_err() || ownership.is_err() {
        for name in &names {
            let _ = fs::remove_dir_all(host_dir.join(format!("{name}{PARTIAL}")));
        }
        let why = if !record_stands {
            "its record changed while it was cloned".into()
        } else if let Err(error) = tree_ownership {
            format!("its build-tree ownership changed while it was cloned: {error}")
        } else {
            format!("its output ownership changed while it was cloned: {}", ownership.unwrap_err())
        };
        return Err(Refused::Busy(why));
    }
    Ok((names, donor_times))
}

fn same_volume(a: &Path, b: &Path) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let dev = |path: &Path| fs::metadata(path).map(|m| m.dev()).map_err(|e| e.to_string());
        if dev(a)? != dev(b)? {
            return Err(format!("{} is on another volume", a.display()));
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = (a, b);
        Err("seeding needs clonefile(2)".into())
    }
}

/// `clonefile(2)` without following a symbolic link: a copy-on-write clone of a whole
/// tree, never a link to it and never a byte copy (which `cp -c` silently falls back to).
fn clonefile(from: &Path, to: &Path) -> io::Result<()> {
    #[cfg(target_os = "macos")]
    {
        use std::ffi::CString;
        let from = CString::new(from.as_os_str().as_encoded_bytes())?;
        let to = CString::new(to.as_os_str().as_encoded_bytes())?;
        // SAFETY: both are valid NUL-terminated paths for the duration of the call.
        // `<sys/clonefile.h>`; the libc crate does not name it.
        const CLONE_NOFOLLOW: u32 = 0x0001;
        let status = unsafe { libc::clonefile(from.as_ptr(), to.as_ptr(), CLONE_NOFOLLOW) };
        if status == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
    }
    #[cfg(not(target_os = "macos"))]
    {
        let _ = (from, to);
        Err(io::Error::new(io::ErrorKind::Unsupported, "clonefile(2) is macOS only"))
    }
}

/// Renames each partial clone of `names` into place under the marker [`INCOMPLETE`], by
/// which an interrupted seed is undone ([`undo_incomplete`]). The marker names each entry
/// with the device and inode of its clone, which a rename keeps. When a rename fails, the
/// marker is cut to the entries already placed.
pub(crate) fn rename_into_place(host_dir: &Path, names: &[String]) -> Result<(), String> {
    let marker = host_dir.join(INCOMPLETE);
    let lines = marker_lines(host_dir, names)?;
    fs::write(&marker, lines.join("\n")).map_err(|e| e.to_string())?;
    for (placed, name) in names.iter().enumerate() {
        let from = host_dir.join(format!("{name}{PARTIAL}"));
        if let Err(error) = fs::rename(&from, host_dir.join(name)) {
            let cut = fs::write(&marker, lines[..placed].join("\n"));
            return Err(format!(
                "cannot rename {}: {error}{}",
                from.display(),
                cut.err()
                    .map_or(String::new(), |e| format!(" (and cannot rewrite the marker: {e})"))
            ));
        }
    }
    fs::remove_file(&marker).map_err(|e| e.to_string())
}

/// The marker's line for each partial clone of `names`: `<name> <device> <inode>`.
fn marker_lines(host_dir: &Path, names: &[String]) -> Result<Vec<String>, String> {
    names
        .iter()
        .map(|name| {
            let partial = host_dir.join(format!("{name}{PARTIAL}"));
            let stat = Stat::of(&partial).map_err(|e| format!("{}: {e}", partial.display()))?;
            Ok(format!("{name} {} {}", stat.dev, stat.ino))
        })
        .collect()
}

/// What [`fix_clone`] did.
#[derive(Default, Debug)]
pub(crate) struct Report {
    /// Inputs that read as the donor's: the same, and given the donor's time.
    pub(crate) carried: usize,
    /// Of them, those whose donor time is the older and is in the carried-times table.
    pub(crate) table: usize,
    /// Inputs that differ, and read later than every cloned file.
    pub(crate) differing: usize,
    /// The units rebuilt because their files name the donor's tree, by name.
    pub(crate) rebuilt: BTreeSet<String>,
}

/// Makes the partial clones of `names` in `host_dir` mean in `own` what they meant in
/// `donor`: retargets links, carries source times (writing the carried-times table), and
/// audits every file. An entry of the recipient's tree whose status changed at or after
/// `settled` counts as differing ([`Moments::settled`]).
pub(crate) fn fix_clone(
    host_dir: &Path,
    names: &[String],
    donor_times: &DonorTimes,
    donor: &Roots,
    own: &Roots,
    host: &str,
    settled: SystemTime,
) -> Result<Report, String> {
    let partials: Vec<PathBuf> =
        names.iter().map(|name| host_dir.join(format!("{name}{PARTIAL}"))).collect();
    // LLVM's own build directory names the donor's paths throughout, and LLVM's stamp
    // (content-keyed) decides whether it is needed: a reconfigure starts a new one.
    let _ = fs::remove_dir_all(host_dir.join(format!("llvm{PARTIAL}")).join("build"));

    let mut files = Vec::new();
    let mut inputs = BTreeSet::new();
    let mut scripts: BTreeMap<String, ScriptRoots> = BTreeMap::new();
    let mut rerun: Vec<(String, String)> = Vec::new();
    let mut incremental = Vec::new();
    let mut package_times = BTreeSet::new();
    let mut newest = (i64::MIN, 0);
    for (name, partial) in names.iter().zip(&partials) {
        let mut walk = walkdir::WalkDir::new(partial).follow_links(false).into_iter();
        while let Some(entry) = walk.next() {
            let entry = entry.map_err(|e| e.to_string())?;
            let stat =
                Stat::of(entry.path()).map_err(|e| format!("{}: {e}", entry.path().display()))?;
            newest = newest.max(stat.mtime);
            // rustc's incremental caches name the donor's paths and are only caches.
            if entry.file_type().is_dir() && entry.file_name() == "incremental" {
                incremental.push(entry.path().to_owned());
                walk.skip_current_dir();
                continue;
            }
            let path = entry.path();
            if entry.file_type().is_symlink() {
                retarget(path, donor, own)?;
                continue;
            }
            if !entry.file_type().is_file() {
                continue;
            }
            let file_name = entry.file_name().to_string_lossy();
            if file_name.ends_with(".d") {
                // A dependency file that cannot be read names inputs the seed would not
                // compare: it fails.
                let text =
                    fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
                let tokens = depinfo_paths(&text);
                if file_name.starts_with("build_script_")
                    && let Some(pkg) = unit_dir_name(path)
                {
                    scripts.entry(pkg).or_default().note(&tokens, donor, own);
                }
                inputs.extend(tokens);
            } else if file_name == "output"
                && let Some(pkg) = unit_dir_name(path)
            {
                let output = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
                for value in rerun_if_changed(&output) {
                    rerun.push((pkg.clone(), value));
                }
            } else if file_name.ends_with(".json")
                && let Some(unit) = unit_of(path.strip_prefix(host_dir).unwrap_or(path))
                && unit.fingerprint
                && fs::read_to_string(path).is_ok_and(|json| names_a_package_time(&json))
            {
                package_times.insert((host_dir.join(unit.profile), unit.hash));
            }
            files.push((name.clone(), path.to_owned()));
        }
    }
    for dir in incremental {
        fs::remove_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    }
    inputs.extend(rerun_inputs(rerun, &scripts)?);

    let mut report = Report::default();
    let moments = Moments { newest, settled: stamp(settled), donor_times };
    let pairs = input_pairs(&inputs, donor, own);
    let table = carry_times(pairs, donor, own, host, moments, &mut report)?;
    audit(&files, host_dir, donor, own, host, &mut report)?;
    // A unit whose fingerprint is its package's newest time (a build script that names no
    // input) compares a time the seed does not carry: it rebuilds.
    rebuild_units(package_times, &mut report)?;
    write_table(host_dir, &table)
        .map_err(|e| format!("cannot write {}: {e}", host_dir.join(CARRIED_TIMES).display()))?;
    report.table = table.len();
    Ok(report)
}

/// The paths a make-style dependency file names, as rustc writes it: targets and
/// prerequisites alike, with `\ ` and `\\` unescaped; comments are skipped.
pub(crate) fn depinfo_paths(text: &str) -> Vec<String> {
    let mut paths = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') {
            continue;
        }
        let mut token = String::new();
        let mut chars = line.chars().peekable();
        while let Some(c) = chars.next() {
            match c {
                '\\' if matches!(chars.peek(), Some(' ') | Some('\\') | Some('#')) => {
                    token.push(chars.next().unwrap())
                }
                ' ' | '\t' => {
                    push_token(&mut paths, &mut token);
                }
                _ => token.push(c),
            }
        }
        push_token(&mut paths, &mut token);
    }
    paths
}

fn push_token(paths: &mut Vec<String>, token: &mut String) {
    let path = token.strip_suffix(':').unwrap_or(token);
    if !path.is_empty() && path != "\\" {
        paths.push(path.to_owned());
    }
    token.clear();
}

/// Where the build scripts of one package lie, as their dependency files name their
/// sources: what a relative `rerun-if-changed` path of the package is relative to.
#[derive(Default, Debug)]
pub(crate) struct ScriptRoots {
    /// The package roots, relative to the tree, of its build scripts in the tree.
    roots: BTreeSet<PathBuf>,
    /// A build script of it lies outside both trees (the registry), where a relative
    /// path names one file for both.
    outside: bool,
    /// A build script of it in the tree has no `Cargo.toml` above it.
    unrooted: bool,
}

impl ScriptRoots {
    /// Notes where one of the package's build scripts lies, by the first source its
    /// dependency file (`tokens`) names, its crate root: relative to the tree as rustc
    /// writes it, or absolute in the donor's tree or elsewhere.
    pub(crate) fn note(&mut self, tokens: &[String], donor: &Roots, own: &Roots) {
        let Some(token) = tokens.iter().find(|token| token.ends_with(".rs")) else {
            self.unrooted = true;
            return;
        };
        let path = Path::new(token);
        let in_tree = if path.is_absolute() {
            donor.map(path, own).and_then(|path| {
                path.strip_prefix(&own.src).ok().map(|rest| rest.to_string_lossy().into_owned())
            })
        } else {
            Some(token.clone())
        };
        match in_tree.map(|script| package_root(&own.src, &script)) {
            Some(Some(root)) => {
                self.roots.insert(root);
            }
            Some(None) => self.unrooted = true,
            None if donor.holds(path) || own.holds(path) => self.unrooted = true,
            None => self.outside = true,
        }
    }
}

/// The inputs the `rerun-if-changed` values `rerun` (by package) name: an absolute one
/// as it is, a relative one under each root of its package's build scripts in the tree.
/// A relative one of a package whose build scripts all lie outside both trees names one
/// file for both and is not compared. Any other (a package whose build script's
/// dependency file was not found, or names a source of the tree with no package above
/// it) fails: what it names is not known, so it cannot be compared.
pub(crate) fn rerun_inputs(
    rerun: Vec<(String, String)>,
    scripts: &BTreeMap<String, ScriptRoots>,
) -> Result<Vec<String>, String> {
    let mut inputs = Vec::new();
    for (pkg, value) in rerun {
        if Path::new(&value).is_absolute() {
            inputs.push(value);
            continue;
        }
        match scripts.get(&pkg) {
            Some(script) if !script.unrooted && (!script.roots.is_empty() || script.outside) => {
                for root in &script.roots {
                    inputs.push(root.join(&value).to_string_lossy().into_owned());
                }
            }
            _ => {
                return Err(format!(
                    "a build script of {pkg} watches `{value}`, relative to a package the seed \
                     cannot name"
                ));
            }
        }
    }
    Ok(inputs)
}

/// The package whose build script is `script` (relative to `src`): the nearest directory
/// above it that holds a `Cargo.toml`, when that manifest names it as its build script
/// (`build.rs` beside it, or its `package.build` path). `None` when the script is not a
/// file of this tree (a dependency file written by a build run elsewhere names it relative
/// to that directory) or the manifest does not name it: what its relative
/// `rerun-if-changed` paths are relative to is then unknown.
fn package_root(src: &Path, script: &str) -> Option<PathBuf> {
    let script = Path::new(script);
    if !src.join(script).is_file() {
        return None;
    }
    let mut dir = script.parent();
    while let Some(candidate) = dir {
        let manifest = src.join(candidate).join("Cargo.toml");
        if manifest.is_file() {
            return build_scripts(&manifest)
                .iter()
                .any(|named| candidate.join(named) == script)
                .then(|| candidate.to_owned());
        }
        dir = candidate.parent();
    }
    None
}

/// The build scripts the manifest at `manifest` names, relative to its directory, as
/// Targo reads `package.build`: absent or `true`, `build.rs`; `false`, none; a path or a
/// list of paths, those. A manifest that cannot be read or parsed names none.
fn build_scripts(manifest: &Path) -> Vec<PathBuf> {
    let Some(value) = fs::read_to_string(manifest)
        .ok()
        .and_then(|text| toml::from_str::<toml::Value>(&text).ok())
    else {
        return Vec::new();
    };
    let Some(package) = value.get("package") else { return Vec::new() };
    match package.get("build") {
        None | Some(toml::Value::Boolean(true)) => vec![PathBuf::from("build.rs")],
        Some(toml::Value::String(path)) => vec![PathBuf::from(path)],
        Some(toml::Value::Array(paths)) => {
            paths.iter().filter_map(|path| path.as_str().map(PathBuf::from)).collect()
        }
        Some(_) => Vec::new(),
    }
}

/// The package name of the unit directory (`<package>-<16 hex>`) holding `path`.
fn unit_dir_name(path: &Path) -> Option<String> {
    let dir = path.parent()?.file_name()?.to_str()?;
    let (name, hash) = dir.rsplit_once('-')?;
    is_unit_hash(hash).then(|| name.to_owned())
}

fn is_unit_hash(text: &str) -> bool {
    text.len() == 16 && text.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// Retargets the link at `path` when it names the donor's tree.
fn retarget(path: &Path, donor: &Roots, own: &Roots) -> Result<(), String> {
    let target = fs::read_link(path).map_err(|e| e.to_string())?;
    let Some(mapped) = donor.map(&target, own) else { return Ok(()) };
    let time = fs::symlink_metadata(path).and_then(|m| m.modified()).ok();
    fs::remove_file(path).map_err(|e| e.to_string())?;
    #[cfg(unix)]
    std::os::unix::fs::symlink(&mapped, path).map_err(|e| e.to_string())?;
    if let Some(time) = time {
        set_mtime(path, time, false).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Sets the modification time of `path` (of the link itself when `follow` is false),
/// leaving its access time.
fn set_mtime(path: &Path, time: SystemTime, follow: bool) -> io::Result<()> {
    #[cfg(unix)]
    {
        use std::ffi::CString;
        let since = time.duration_since(SystemTime::UNIX_EPOCH).map_err(io::Error::other)?;
        let times = [
            libc::timespec { tv_sec: 0, tv_nsec: libc::UTIME_OMIT },
            libc::timespec {
                tv_sec: since.as_secs() as libc::time_t,
                tv_nsec: since.subsec_nanos() as libc::c_long,
            },
        ];
        let path = CString::new(path.as_os_str().as_encoded_bytes())?;
        let flag = if follow { 0 } else { libc::AT_SYMLINK_NOFOLLOW };
        // SAFETY: a valid path and a two-element array, as utimensat(2) requires.
        let status =
            unsafe { libc::utimensat(libc::AT_FDCWD, path.as_ptr(), times.as_ptr(), flag) };
        if status == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
    }
    #[cfg(not(unix))]
    {
        let _ = (path, time, follow);
        Err(io::Error::new(io::ErrorKind::Unsupported, "times"))
    }
}

/// The moments [`carry_time`] compares against, each as `(seconds, nanoseconds)` since
/// the epoch.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Moments<'a> {
    /// The latest modification time of any cloned file. A recipient entry that differs
    /// from the donor's must read later than this, or Targo would take an output the
    /// donor built from its own bytes for one built from the recipient's.
    pub(crate) newest: (i64, i64),
    /// An entry whose status changed at or after this may still be being written, as far
    /// as a seed can tell (two writes in one clock tick leave one status-change time), so
    /// it is treated as differing.
    pub(crate) settled: (i64, i64),
    /// The times the donor's Targo reads where they are not its files' own.
    pub(crate) donor_times: &'a DonorTimes,
}

/// The carried-times table of a donor that was itself seeded, by device and inode: the
/// times its Targo reads for those of its inputs whose donor's time was older, as long as
/// each is as it was compared (Targo's `util::carried_times`).
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct DonorTimes(BTreeMap<(u64, u64), TableEntry>);

impl DonorTimes {
    /// The table in the donor's `build/<host>/`, or none. One that is not as a seed
    /// writes it refuses the donor: its Targo refuses it too.
    pub(crate) fn read(donor_dir: &Path) -> Result<DonorTimes, String> {
        let path = donor_dir.join(CARRIED_TIMES);
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Self::default()),
            Err(error) => return Err(format!("{}: {error}", path.display())),
        };
        let mut lines = text.lines();
        if lines.next() != Some(CARRIED_TIMES_SCHEMA) {
            return Err(format!("{} is not a `{CARRIED_TIMES_SCHEMA}` table", path.display()));
        }
        let mut entries = BTreeMap::new();
        for line in lines {
            let entry = TableEntry::parse(line)
                .ok_or_else(|| format!("{}: malformed line `{line}`", path.display()))?;
            if entries.insert((entry.dev, entry.ino), entry).is_some() {
                return Err(format!("{} names one file twice", path.display()));
            }
        }
        Ok(DonorTimes(entries))
    }

    /// The modification time the donor's Targo reads for its entry `stat`.
    fn time(&self, stat: &Stat) -> (i64, i64) {
        match self.0.get(&(stat.dev, stat.ino)) {
            Some(entry)
                if (entry.size, entry.mtime, entry.ctime)
                    == (stat.size, stat.mtime, stat.ctime) =>
            {
                entry.carried
            }
            _ => stat.mtime,
        }
    }
}

/// What [`carry_time`] did with one entry.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Carried {
    /// The same as the donor's, whose time is the older: Targo is to read the donor's time
    /// for it while it stays as it was compared.
    Table(TableEntry),
    /// The same, and it reads as the donor's does: its time was the donor's already, or
    /// was moved forward to it.
    Same,
    /// It differs (other bytes, another link target, other entries, another kind of entry,
    /// a donor entry that changed while it was compared, or none), changed while it was
    /// compared, or has no entry: it reads later than every cloned file, its time moved
    /// forward when it did not.
    Differs,
}

/// One line of a carried-times table: a recipient entry as it was compared, and the
/// donor's time Targo reads for it while it stays so (Targo's `util::carried_times`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TableEntry {
    pub(crate) dev: u64,
    pub(crate) ino: u64,
    pub(crate) size: u64,
    pub(crate) mtime: (i64, i64),
    pub(crate) ctime: (i64, i64),
    pub(crate) carried: (i64, i64),
}

impl TableEntry {
    /// A line as [`TableEntry::line`] writes it, without its newline.
    pub(crate) fn parse(line: &str) -> Option<TableEntry> {
        let fields: Vec<&str> = line.split(' ').collect();
        let [dev, ino, size, m_s, m_ns, c_s, c_ns, t_s, t_ns] = fields[..] else { return None };
        let nanos =
            |field: &str| field.parse::<i64>().ok().filter(|n| (0..1_000_000_000).contains(n));
        Some(TableEntry {
            dev: dev.parse().ok()?,
            ino: ino.parse().ok()?,
            size: size.parse().ok()?,
            mtime: (m_s.parse().ok()?, nanos(m_ns)?),
            ctime: (c_s.parse().ok()?, nanos(c_ns)?),
            carried: (t_s.parse().ok()?, nanos(t_ns)?),
        })
    }

    pub(crate) fn line(&self) -> String {
        let Self { dev, ino, size, mtime, ctime, carried } = self;
        format!(
            "{dev} {ino} {size} {} {} {} {} {} {}\n",
            mtime.0, mtime.1, ctime.0, ctime.1, carried.0, carried.1
        )
    }
}

/// What an entry's metadata says of it, read before and after its contents are compared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Stat {
    dev: u64,
    ino: u64,
    size: u64,
    mtime: (i64, i64),
    ctime: (i64, i64),
    kind: EntryKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EntryKind {
    File,
    Link,
    Dir,
    Other,
}

impl Stat {
    /// The entry itself, never a link's target.
    fn of(path: &Path) -> io::Result<Stat> {
        let meta = fs::symlink_metadata(path)?;
        let kind = meta.file_type();
        let kind = if kind.is_symlink() {
            EntryKind::Link
        } else if kind.is_dir() {
            EntryKind::Dir
        } else if kind.is_file() {
            EntryKind::File
        } else {
            EntryKind::Other
        };
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            Ok(Stat {
                dev: meta.dev(),
                ino: meta.ino(),
                size: meta.len(),
                mtime: (meta.mtime(), meta.mtime_nsec()),
                ctime: (meta.ctime(), meta.ctime_nsec()),
                kind,
            })
        }
        #[cfg(not(unix))]
        {
            let _ = kind;
            Err(io::Error::new(io::ErrorKind::Unsupported, "seeding needs unix metadata"))
        }
    }
}

/// `time` as `(seconds, nanoseconds)` since the epoch, the nanoseconds never negative.
pub(crate) fn stamp(time: SystemTime) -> (i64, i64) {
    match time.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(since) => (since.as_secs() as i64, i64::from(since.subsec_nanos())),
        Err(before) => {
            let before = before.duration();
            let (secs, nanos) = (before.as_secs() as i64, i64::from(before.subsec_nanos()));
            if nanos == 0 { (-secs, 0) } else { (-secs - 1, 1_000_000_000 - nanos) }
        }
    }
}

fn system_time((secs, nanos): (i64, i64)) -> SystemTime {
    let base = if secs >= 0 {
        SystemTime::UNIX_EPOCH + Duration::from_secs(secs as u64)
    } else {
        SystemTime::UNIX_EPOCH - Duration::from_secs(secs.unsigned_abs())
    };
    base + Duration::from_nanos(nanos as u64)
}

/// Makes the recipient's entry `own` read to Targo as the donor's entry `donor` would in
/// the donor rebuilt in place from the recipient's files: with the donor's time when the
/// two are the same (regular files with the same bytes, links with the same target, or
/// directories with the same entries), and later than every cloned file when they are
/// not. A recipient's time only ever moves forward, so every other cache in the tree
/// that compares times (another target directory, an editor) still sees each change: a
/// donor time that is the older is given to Targo alone, as a [`TableEntry`] that holds
/// while the entry stays as it was compared. Both entries are read again after they are
/// compared, and an entry of either tree that changed meanwhile counts as differing. An
/// error is returned only when a differing entry cannot be given its later time.
pub(crate) fn carry_time(donor: &Path, own: &Path, moments: Moments<'_>) -> io::Result<Carried> {
    // No entry, or none Targo can read either: it rebuilds whatever read it.
    let Ok(before) = Stat::of(own) else { return Ok(Carried::Differs) };
    match compare(donor, own, &before, moments) {
        Ok(Some(carried)) => Ok(carried),
        Ok(None) | Err(_) => {
            move_later(own, moments)?;
            Ok(Carried::Differs)
        }
    }
}

/// [`carry_time`]'s comparison: `None` when the entries are not provably the same.
fn compare(
    donor: &Path,
    own: &Path,
    before: &Stat,
    moments: Moments<'_>,
) -> io::Result<Option<Carried>> {
    let theirs = Stat::of(donor)?;
    if theirs.kind != before.kind
        || !same_contents(donor, own, &theirs, before)?
        || Stat::of(donor)? != theirs
    {
        return Ok(None);
    }
    let after = Stat::of(own)?;
    if after != *before || after.ctime >= moments.settled {
        return Ok(None);
    }
    // What the donor's Targo reads: its table's time when it was seeded itself.
    let their_time = moments.donor_times.time(&theirs);
    if their_time == after.mtime {
        return Ok(Some(Carried::Same));
    }
    if their_time > after.mtime {
        set_mtime(own, system_time(their_time), false)?;
        // A write that landed between the comparison and the new time is never hidden.
        let moved = Stat::of(own)?;
        if (moved.ino, moved.size, moved.mtime) != (after.ino, after.size, their_time)
            || !same_contents(donor, own, &theirs, &moved)?
        {
            return Ok(None);
        }
        return Ok(Some(Carried::Same));
    }
    Ok(Some(Carried::Table(TableEntry {
        dev: after.dev,
        ino: after.ino,
        size: after.size,
        mtime: after.mtime,
        ctime: after.ctime,
        carried: their_time,
    })))
}

fn same_contents(donor: &Path, own: &Path, theirs: &Stat, ours: &Stat) -> io::Result<bool> {
    Ok(match ours.kind {
        EntryKind::File => theirs.size == ours.size && same_bytes(donor, own)?,
        EntryKind::Link => fs::read_link(donor)? == fs::read_link(own)?,
        EntryKind::Dir => listing(donor)? == listing(own)?,
        EntryKind::Other => false,
    })
}

/// Gives `own` a modification time later than every cloned file, unless it has one.
fn move_later(own: &Path, moments: Moments<'_>) -> io::Result<()> {
    let stat = match Stat::of(own) {
        Ok(stat) => stat,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    if stat.mtime > moments.newest {
        return Ok(());
    }
    let (secs, nanos) = moments.newest;
    let just_after = if nanos == 999_999_999 { (secs + 1, 0) } else { (secs, nanos + 1) };
    set_mtime(own, system_time(stamp(SystemTime::now()).max(just_after)), false)
}

/// The entries of a directory, by name and kind.
fn listing(dir: &Path) -> io::Result<BTreeSet<(std::ffi::OsString, u8)>> {
    let mut entries = BTreeSet::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let kind = entry.file_type()?;
        let kind = if kind.is_dir() {
            0
        } else if kind.is_symlink() {
            1
        } else if kind.is_file() {
            2
        } else {
            3
        };
        entries.insert((entry.file_name(), kind));
    }
    Ok(entries)
}

fn same_bytes(a: &Path, b: &Path) -> io::Result<bool> {
    let (mut a, mut b) = (fs::File::open(a)?, fs::File::open(b)?);
    let (mut x, mut y) = (vec![0u8; 1 << 16], vec![0u8; 1 << 16]);
    loop {
        let n = read_full(&mut a, &mut x)?;
        let m = read_full(&mut b, &mut y)?;
        if n != m || x[..n] != y[..m] {
            return Ok(false);
        }
        if n == 0 {
            return Ok(true);
        }
    }
}

fn read_full(file: &mut fs::File, buf: &mut [u8]) -> io::Result<usize> {
    let mut filled = 0;
    while filled < buf.len() {
        match file.read(&mut buf[filled..])? {
            0 => break,
            n => filled += n,
        }
    }
    Ok(filled)
}

/// The donor's and the recipient's spelling of each input in `inputs`: relative to the
/// tree (as rustc writes it, under `-Zroot-dir`), or absolute in the donor's tree or git
/// directory. Paths elsewhere (the registry, the system) are the same file in both trees.
/// [`carry_times`] decides which of them to compare.
pub(crate) fn input_pairs(
    inputs: &BTreeSet<String>,
    donor: &Roots,
    own: &Roots,
) -> Vec<(PathBuf, PathBuf)> {
    inputs
        .iter()
        .filter_map(|input| {
            let path = Path::new(input);
            Some(if path.is_absolute() {
                (path.to_owned(), donor.map(path, own)?)
            } else {
                (donor.src.join(path), own.src.join(path))
            })
        })
        .collect()
}

/// Carries the donor's times for the inputs `pairs` names ([`carry_time`]) and returns
/// the table entries. Targo reads more than each named path, and everything it reads is
/// compared: the target of a link as well as the link, and every entry under a watched
/// directory, directories included (Targo takes the newest time under it, following
/// links). Each path is first resolved through the links among its directories, as the
/// system resolves it when Targo reads it, so the spellings of one file (`a/../b/c`,
/// `b/c`, a path through a linked directory) are compared once. A path of this tree that
/// resolves outside it must name the file the donor's resolves to, or the seed fails. A
/// link whose two targets are not the same file of each tree reads later. Inputs inside
/// the cloned entries keep their cloned times, and inputs elsewhere under `build/` are
/// compared when this tree has them (what it does not have yet, its build makes).
fn carry_times(
    pairs: Vec<(PathBuf, PathBuf)>,
    donor: &Roots,
    own: &Roots,
    host: &str,
    moments: Moments<'_>,
    report: &mut Report,
) -> Result<Vec<TableEntry>, String> {
    let build = own.src.join("build");
    let cloned = |path: &Path| {
        path.strip_prefix(build.join(host))
            .is_ok_and(|rest| rest.iter().next().and_then(OsStr::to_str).is_some_and(seeded))
    };
    let mut real_dirs: BTreeMap<PathBuf, Option<PathBuf>> = BTreeMap::new();
    let mut resolve = |path: PathBuf| match (path.parent(), path.file_name()) {
        (Some(parent), Some(name)) => {
            let real =
                real_dirs.entry(parent.to_owned()).or_insert_with(|| fs::canonicalize(parent).ok());
            real.as_ref().map_or(path.clone(), |real| real.join(name))
        }
        _ => path,
    };
    let mut work = pairs;
    let mut seen = BTreeSet::new();
    let mut entries = BTreeSet::new();
    let mut dirs = BTreeSet::new();
    let mut unmatched = BTreeSet::new();
    while let Some((from, to)) = work.pop() {
        let (from, to) = (resolve(from), resolve(to));
        if !own.holds(&to) {
            if from == to {
                // One file outside both trees: it reads alike in both.
                continue;
            }
            return Err(format!(
                "{} resolves outside this tree, and the donor's {} to another file",
                to.display(),
                from.display()
            ));
        }
        if to == own.src
            || cloned(&to)
            || (to.starts_with(&build) && fs::symlink_metadata(&to).is_err())
            || !seen.insert((from.clone(), to.clone()))
        {
            continue;
        }
        match fs::symlink_metadata(&from) {
            Ok(meta) if meta.file_type().is_symlink() => {
                match link_targets(&from, &to, donor, own) {
                    Ok(Some(targets)) => work.push(targets),
                    Ok(None) => {}
                    Err(()) => {
                        unmatched.insert(to.clone());
                    }
                }
                entries.insert((from, to));
            }
            Ok(meta) if meta.is_dir() => {
                // A listing that cannot be read leaves the directory differing ([`listing`]).
                for entry in fs::read_dir(&from).into_iter().flatten().flatten() {
                    work.push((entry.path(), to.join(entry.file_name())));
                }
                dirs.insert((std::cmp::Reverse(to.components().count()), (from, to)));
            }
            _ => {
                entries.insert((from, to));
            }
        }
    }
    let carry = |from: &Path, to: &Path| {
        let id = Stat::of(to).ok().map(|stat| (stat.dev, stat.ino));
        let carried = if unmatched.contains(to) {
            move_later(to, moments).map(|()| Carried::Differs)
        } else {
            carry_time(from, to, moments)
        };
        carried.map(|carried| (id, carried)).map_err(|e| format!("{}: {e}", to.display()))
    };
    let entries: Vec<_> = entries.into_iter().collect();
    let next = AtomicUsize::new(0);
    let results = Mutex::new(Vec::new());
    let failure = Mutex::new(None);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()).min(16);
    crate::utils::exec::scoped_threads(|scope| -> std::io::Result<()> {
        for _ in 0..threads {
            drop(scope.spawn(|| {
                while let Some((from, to)) = entries.get(next.fetch_add(1, Ordering::Relaxed)) {
                    match carry(from, to) {
                        Ok(result) => results.lock().unwrap().push(result),
                        Err(error) => *failure.lock().unwrap() = Some(error),
                    }
                }
            })?);
        }
        Ok(())
    })
    .and_then(|result| result)
    .map_err(|error| error.to_string())?;
    if let Some(error) = failure.into_inner().unwrap() {
        return Err(format!("cannot give a differing input a later time: {error}"));
    }
    let mut results = results.into_inner().unwrap();
    for (_, (from, to)) in dirs {
        let result = carry(&from, &to);
        results.push(result.map_err(|e| format!("cannot give {e} a later time"))?);
    }
    Ok(merge_carried(results, report))
}

/// The table entries of `results` (each the recipient entry's device and inode, when it
/// has one, and what [`carry_time`] did with it). A file reached by more than one input
/// (two directory entries, a hard link) gets one entry, and only when every comparison
/// of it gave one, of its unchanged state: then it carries the latest of the donor
/// times, so no unit reads it as older than its own donor input. Otherwise it reads its
/// own time, which is later than each donor time it was compared with.
pub(crate) fn merge_carried(
    results: Vec<(Option<(u64, u64)>, Carried)>,
    report: &mut Report,
) -> Vec<TableEntry> {
    let mut tabled: BTreeMap<(u64, u64), Vec<TableEntry>> = BTreeMap::new();
    let mut untabled = BTreeSet::new();
    for (id, carried) in results {
        match carried {
            Carried::Table(entry) => tabled.entry((entry.dev, entry.ino)).or_default().push(entry),
            Carried::Same => {
                report.carried += 1;
                untabled.extend(id);
            }
            Carried::Differs => {
                report.differing += 1;
                untabled.extend(id);
            }
        }
    }
    let mut table = Vec::new();
    for (id, entries) in tabled {
        let first = entries[0];
        let state = |entry: &TableEntry| (entry.size, entry.mtime, entry.ctime);
        if untabled.contains(&id) || entries.iter().any(|entry| state(entry) != state(&first)) {
            report.differing += entries.len();
            continue;
        }
        report.carried += entries.len();
        let carried = entries.iter().map(|entry| entry.carried).max().unwrap_or(first.carried);
        table.push(TableEntry { carried, ..first });
    }
    table
}

/// The donor's and the recipient's targets of the link pair `(from, to)`, which Targo
/// reads through the link: `Ok(None)` when neither resolves, or both name one file
/// outside both trees; `Err` when the targets are not the same file of each tree.
fn link_targets(
    from: &Path,
    to: &Path,
    donor: &Roots,
    own: &Roots,
) -> Result<Option<(PathBuf, PathBuf)>, ()> {
    match (fs::canonicalize(from), fs::canonicalize(to)) {
        (Err(_), Err(_)) => Ok(None),
        (Ok(theirs), Ok(ours)) => match donor.map(&theirs, own) {
            Some(mapped) if mapped == ours => Ok(Some((theirs, ours))),
            None if theirs == ours && own.map(&ours, donor).is_none() => Ok(None),
            _ => Err(()),
        },
        _ => Err(()),
    }
}

/// Writes the carried-times table `entries` into `host_dir`, whole or not at all.
fn write_table(host_dir: &Path, entries: &[TableEntry]) -> io::Result<()> {
    let mut text = format!("{CARRIED_TIMES_SCHEMA}\n");
    for entry in entries {
        text.push_str(&entry.line());
    }
    let partial = host_dir.join(format!("{CARRIED_TIMES}{PARTIAL}"));
    fs::write(&partial, text)?;
    fs::rename(&partial, host_dir.join(CARRIED_TIMES))
}

/// What the audit does with a cloned file that names the donor's tree.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Finding {
    /// Debug information only, or a file Targo re-roots itself: kept.
    Kept,
    /// A text file bootstrap or Targo writes for itself: the donor's roots are rewritten
    /// to the recipient's, keeping its time.
    Rewrite,
    /// The unit `<profile>/.fingerprint/*-<hash>` rebuilds.
    Rebuild { profile: PathBuf, hash: String },
    /// A file no unit owns that the build makes again: deleted.
    Delete,
    /// Nothing can say what it means in the recipient: the seed is refused.
    Refuse,
}

/// Searches every cloned file for the donor's roots and acts on each finding ([`classify`]).
fn audit(
    files: &[(String, PathBuf)],
    host_dir: &Path,
    donor: &Roots,
    own: &Roots,
    host: &str,
    report: &mut Report,
) -> Result<(), String> {
    let needles = donor.needles();
    let finders: Vec<memchr::memmem::Finder<'_>> =
        needles.iter().map(memchr::memmem::Finder::new).collect();
    let donor_record = relocation_record(donor);
    let next = AtomicUsize::new(0);
    let findings = Mutex::new(Vec::new());
    let failure = Mutex::new(None);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()).min(16);
    crate::utils::exec::scoped_threads(|scope| -> std::io::Result<()> {
        for _ in 0..threads {
            drop(scope.spawn(|| {
                while let Some((entry, path)) = files.get(next.fetch_add(1, Ordering::Relaxed)) {
                    match scan(path, &finders) {
                        Ok(None) => {}
                        Ok(Some((data, offsets))) => {
                            let relative = path.strip_prefix(host_dir).unwrap_or(path);
                            let relocated = fs::read(path.with_file_name("root-relocation"))
                                .is_ok_and(|record| record == donor_record);
                            let finding =
                                classify(entry, relative, &data, &offsets, donor, host, relocated);
                            findings.lock().unwrap().push((path.clone(), finding));
                        }
                        Err(error) => {
                            *failure.lock().unwrap() =
                                Some(format!("cannot read {}: {error}", path.display()))
                        }
                    }
                }
            })?);
        }
        Ok(())
    })
    .and_then(|result| result)
    .map_err(|error| error.to_string())?;
    if let Some(error) = failure.into_inner().unwrap() {
        return Err(error);
    }
    let mut rebuild = BTreeSet::new();
    for (path, finding) in findings.into_inner().unwrap() {
        match finding {
            Finding::Kept => {}
            Finding::Rewrite => rewrite(&path, donor, own).map_err(|e| e.to_string())?,
            Finding::Rebuild { profile, hash } => {
                rebuild.insert((host_dir.join(profile), hash));
            }
            Finding::Delete => fs::remove_file(&path).map_err(|e| e.to_string())?,
            Finding::Refuse => {
                return Err(format!(
                    "{} names the donor's tree in a way no unit owns",
                    path.strip_prefix(host_dir).unwrap_or(&path).display()
                ));
            }
        }
    }
    rebuild_units(rebuild, report)
}

/// Removes each unit `(profile directory, metadata hash)` of `units`: its fingerprint
/// (`.fingerprint/<name>-<hash>/`), its build-script directory (`build/<name>-<hash>/`)
/// and its outputs (`deps/` and `examples/` entries of that hash). Targo then rebuilds
/// it, and in the same build everything that depends on it, as it would in the donor
/// had the unit been rebuilt there: a dependent compares its dependencies' outputs, and a
/// missing one is stale. Removing the fingerprint alone rebuilt the unit while its
/// dependents compared the cloned outputs, older than their own, and rebuilt only in the
/// build after.
fn rebuild_units(units: BTreeSet<(PathBuf, String)>, report: &mut Report) -> Result<(), String> {
    let mut by_profile: BTreeMap<PathBuf, BTreeSet<String>> = BTreeMap::new();
    for (profile, hash) in units {
        by_profile.entry(profile).or_default().insert(hash);
    }
    for (profile, hashes) in by_profile {
        for dir in [".fingerprint", "build", "deps", "examples"] {
            for entry in fs::read_dir(profile.join(dir)).into_iter().flatten().flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                // `<name>-<hash>`, and in `deps/` and `examples/` `<name>-<hash>.<ext>...`.
                let stem = if matches!(dir, "deps" | "examples") {
                    name.split('.').next().unwrap_or(&name)
                } else {
                    &name
                };
                let Some((unit, hash)) = stem.rsplit_once('-') else { continue };
                if !hashes.contains(hash) {
                    continue;
                }
                let path = entry.path();
                let removed = if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
                    fs::remove_dir_all(&path)
                } else {
                    fs::remove_file(&path)
                };
                removed.map_err(|e| format!("cannot remove {}: {e}", path.display()))?;
                if dir == ".fingerprint" {
                    report.rebuilt.insert(unit.to_owned());
                }
            }
        }
    }
    Ok(())
}

/// The `rerun-if-changed` values of a build script's output, read as Targo reads them
/// (`custom_build.rs`): each line trimmed, in the `cargo::`, `targo::`, `cargo:` or
/// `targo:` spelling, the value trimmed at its end only (`parse_directive`); a line that
/// is not UTF-8 is skipped, as Targo skips it.
pub(crate) fn rerun_if_changed(output: &[u8]) -> Vec<String> {
    let mut values = Vec::new();
    for line in output.split(|&byte| byte == b'\n') {
        let Ok(line) = std::str::from_utf8(line) else { continue };
        let line = line.trim();
        let data = ["cargo::", "targo::", "cargo:", "targo:"]
            .iter()
            .find_map(|prefix| line.strip_prefix(prefix));
        if let Some(value) = data.and_then(|data| data.strip_prefix("rerun-if-changed=")) {
            values.push(value.trim_end().to_owned());
        }
    }
    values
}

/// Whether a Targo fingerprint (JSON) holds a path package's own fingerprint: its newest
/// file's time and path, `"Precalculated":"<seconds>.<nanos>s (<path>)"`, which Targo
/// compares for equality with the package's current newest file.
pub(crate) fn names_a_package_time(json: &str) -> bool {
    json.match_indices("\"Precalculated\":\"").any(|(at, key)| {
        let rest = &json[at + key.len()..];
        let seconds = rest.bytes().take_while(u8::is_ascii_digit).count();
        let rest = &rest[seconds..];
        let nanos =
            rest.strip_prefix('.').map_or(0, |r| r.bytes().take_while(u8::is_ascii_digit).count());
        seconds > 0
            && rest.get(nanos + usize::from(nanos > 0)..).is_some_and(|r| r.starts_with("s ("))
    })
}

/// A file's bytes and each `(offset, needle)` found in them.
type Hits = (Vec<u8>, Vec<(usize, usize)>);

/// The bytes of `path` and where the needles occur in them, or `None` when none does.
fn scan(path: &Path, finders: &[memchr::memmem::Finder<'_>]) -> io::Result<Option<Hits>> {
    let data = fs::read(path)?;
    let mut offsets = Vec::new();
    for (index, finder) in finders.iter().enumerate() {
        offsets.extend(finder.find_iter(&data).map(|offset| (offset, index)));
    }
    if offsets.is_empty() { Ok(None) } else { Ok(Some((data, offsets))) }
}

/// What a cloned file of the entry `entry` at `relative` (to `build/<host>/`) whose
/// bytes `data` name the donor's tree at `offsets` (`(offset, index into
/// [`Roots::needles`])`) means. `relocated` says whether the `root-relocation` record beside
/// it (Targo's record of the roots a build-script run was recorded under) names exactly
/// the donor's roots ([`relocation_record`]).
pub(crate) fn classify(
    entry: &str,
    relative: &Path,
    data: &[u8],
    offsets: &[(usize, usize)],
    donor: &Roots,
    host: &str,
    relocated: bool,
) -> Finding {
    let name = relative.file_name().and_then(OsStr::to_str).unwrap_or("");
    let ranges = debug_ranges(data);
    if offsets.iter().all(|(offset, _)| ranges.iter().any(|range| range.contains(offset))) {
        return Finding::Kept;
    }
    if entry == "llvm" {
        // LLVM's install tree is relocatable: `llvm-config` and LLVM's tools and CMake
        // files name the source and build trees LLVM was built in, which they consult
        // only when run from that build tree (`llvm-config` compares its own location
        // with it). Any other spelling of the donor's tree is refused.
        let src = donor.src.as_os_str().as_encoded_bytes();
        let build = format!("/build/{host}/llvm/build");
        let ends = |rest: &[u8], prefix: &[u8]| {
            rest.starts_with(prefix)
                && !rest
                    .get(prefix.len())
                    .is_some_and(|b| b.is_ascii_alphanumeric() || b"-_.".contains(b))
        };
        let fine = offsets.iter().all(|&(offset, needle)| {
            let rest = &data[offset + src.len().min(data.len() - offset)..];
            needle == 0 && (ends(rest, b"/src/llvm-project") || ends(rest, build.as_bytes()))
        });
        return if fine { Finding::Kept } else { Finding::Refuse };
    }
    if name.ends_with(".d")
        || name.ends_with(".trim-paths.json")
        || (name.starts_with('.') && name.contains("stamp"))
    {
        // Make-style dependency files (rustc's and Targo's uplifted ones), Targo's
        // `trim-paths` unremap records (a debug companion naming the local paths that
        // rustc's remapped ones stand for; nothing in the build reads them), and
        // bootstrap's stamps, which list the artifacts bootstrap copies into the sysroot.
        return Finding::Rewrite;
    }
    if name == ".rustc_info.json" {
        // Targo's cache of `rustc -vV`, keyed by the compiler's path and time.
        return Finding::Delete;
    }
    let Some(unit) = unit_of(relative) else {
        // Bootstrap copies tools and uplifted artifacts again on every build.
        return Finding::Delete;
    };
    match unit.within.as_deref().and_then(Path::to_str) {
        // Targo's cache of a unit's diagnostics, replayed for display only.
        Some(within) if unit.fingerprint && within.starts_with("output-") => Finding::Rewrite,
        // A build-script run's records, which Targo re-roots itself: `root-output` always,
        // and `output` when the run recorded the donor's roots (`root-relocation`, which
        // names only them). `stderr` is only replayed for display.
        Some("root-output" | "root-relocation" | "stderr") if !unit.fingerprint => Finding::Kept,
        Some("output") if !unit.fingerprint && relocated => Finding::Kept,
        _ => Finding::Rebuild { profile: unit.profile, hash: unit.hash },
    }
}

/// The unit owning a file of a Targo target directory, as [`unit_of`] finds it.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Unit {
    /// The profile directory, holding `.fingerprint/`, `build/` and `deps/`.
    pub(crate) profile: PathBuf,
    /// The unit's metadata hash: `.fingerprint/<name>-<hash>` is its fingerprint.
    pub(crate) hash: String,
    /// The file's path within `.fingerprint/<name>-<hash>/` or `build/<name>-<hash>/`.
    pub(crate) within: Option<PathBuf>,
    /// Whether that directory is the unit's fingerprint directory.
    pub(crate) fingerprint: bool,
}

/// The unit that owns the file at `relative` (to `build/<host>/`): the first
/// `.fingerprint/<name>-<hash>/`, `build/<name>-<hash>/`, `deps/<name>-<hash>[.ext]` or
/// `examples/<name>-<hash>[.ext]` on its path.
pub(crate) fn unit_of(relative: &Path) -> Option<Unit> {
    let components: Vec<&str> = relative.iter().map(OsStr::to_str).collect::<Option<_>>()?;
    for (index, pair) in components.windows(2).enumerate() {
        let (dir, child) = (pair[0], pair[1]);
        let rest = &components[index + 2..];
        let profile = components[..index].iter().collect::<PathBuf>();
        let unit_hash = |name: &str| {
            name.rsplit_once('-')
                .map(|(_, hash)| hash)
                .filter(|hash| is_unit_hash(hash))
                .map(str::to_owned)
        };
        let unit = match dir {
            ".fingerprint" | "build" if !rest.is_empty() => unit_hash(child).map(|hash| Unit {
                profile,
                hash,
                within: Some(rest.iter().collect()),
                fingerprint: dir == ".fingerprint",
            }),
            "deps" | "examples" => unit_hash(child.split('.').next().unwrap_or(child))
                .map(|hash| Unit { profile, hash, within: None, fingerprint: false }),
            _ => None,
        };
        if unit.is_some() {
            return unit;
        }
    }
    None
}

/// Rewrites the donor's roots in the text file at `path` to the recipient's
/// ([`trust_source_identity::replace_roots`]), keeping its modification time.
fn rewrite(path: &Path, donor: &Roots, own: &Roots) -> io::Result<()> {
    let time = fs::metadata(path)?.modified()?;
    let data = fs::read(path)?;
    fs::write(path, relocated(&data, donor, own))?;
    set_mtime(path, time, true)
}

/// `data` with the donor's roots written as the recipient's: its git directory as the
/// recipient's git directory and its source tree as the recipient's.
pub(crate) fn relocated(data: &[u8], donor: &Roots, own: &Roots) -> Vec<u8> {
    let bytes = |path: &Path| path.as_os_str().as_encoded_bytes().to_vec();
    let mut pairs = vec![(bytes(&donor.src), bytes(&own.src))];
    if let (Some(from), Some(to)) = (&donor.git_dir, &own.git_dir) {
        pairs.push((bytes(from), bytes(to)));
    }
    let pairs: Vec<(&[u8], &[u8])> = pairs.iter().map(|(a, b)| (&a[..], &b[..])).collect();
    trust_source_identity::replace_roots(data, &pairs)
}

/// The byte ranges of `data` that hold only debug information: the DWARF sections of
/// the `__DWARF` segment and the symbol string table (which holds the debug map's object
/// paths) of a Mach-O object or image, or of a Mach-O member of an `ar` archive (an
/// rlib).
pub(crate) fn debug_ranges(data: &[u8]) -> Vec<Range<usize>> {
    if let Ok(archive) = object::read::archive::ArchiveFile::parse(data) {
        let mut ranges = Vec::new();
        for member in archive.members().flatten() {
            let (offset, size) = member.file_range();
            let (offset, size) = (offset as usize, size as usize);
            if let Some(member_data) = data.get(offset..offset + size) {
                ranges.extend(
                    macho_debug_ranges(member_data)
                        .into_iter()
                        .map(|r| r.start + offset..r.end + offset),
                );
            }
        }
        return ranges;
    }
    macho_debug_ranges(data)
}

fn macho_debug_ranges(data: &[u8]) -> Vec<Range<usize>> {
    use object::read::macho::{LoadCommandVariant, MachHeader, Section, Segment};
    let mut ranges = Vec::new();
    let Ok(header) = object::macho::MachHeader64::<object::Endianness>::parse(data, 0) else {
        return ranges;
    };
    let Ok(endian) = header.endian() else { return ranges };
    let Ok(mut commands) = header.load_commands(endian, data, 0) else { return ranges };
    while let Ok(Some(command)) = commands.next() {
        match command.variant() {
            Ok(LoadCommandVariant::Segment64(segment, section_data)) => {
                let Ok(sections) = segment.sections(endian, section_data) else { continue };
                for section in sections {
                    // DWARF's own sections only: rustc puts an rlib's metadata, which
                    // code is compiled from, in `__DWARF,.rmeta` too, and embedded
                    // bitcode (`__LLVM,__bitcode`) is the module's code as well as its
                    // debug metadata.
                    let name = section.name();
                    if section.segment_name() == b"__DWARF"
                        && (name.starts_with(b"__debug_") || name.starts_with(b"__apple_"))
                    {
                        let offset = section.offset(endian) as usize;
                        let size = section.size(endian) as usize;
                        ranges.push(offset..offset.saturating_add(size));
                    }
                }
            }
            Ok(LoadCommandVariant::Symtab(symtab)) => {
                let offset = symtab.stroff.get(endian) as usize;
                let size = symtab.strsize.get(endian) as usize;
                ranges.push(offset..offset.saturating_add(size));
            }
            _ => {}
        }
    }
    ranges
}

#[cfg(test)]
mod tests;
