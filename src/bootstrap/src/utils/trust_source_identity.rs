//! Trust: the identity a dev stage-1 build's version carries (TB1).
//!
//! The compiler and its tools read their version from the environment bootstrap sets
//! (`CFG_VERSION`, `CFG_VER_HASH`, `CFG_VER_DATE` and `CFG_TRUST_VERSION`, and the tools'
//! `CFG_COMMIT_*`), and cargo rebuilds a crate when one of them changes. Upstream names
//! a build by `git rev-parse HEAD`. So a commit that changed only `docs/`, the decision
//! queue or a script gave every one of them a new value. The crates that read them
//! (`rustc_interface`, `rustc_codegen_llvm`, `rustc_driver_impl`, `trust-router`, and
//! `rustc_session` on a new day) were rebuilt with everything that depends on them,
//! then std and the tools, for bytes that could not differ.
//!
//! A dev stage-1 build ([`names_sources`]) is named instead by what it is built from
//! ([`of_sources`]):
//! * the git object that HEAD's commit records for every top-level entry of the
//!   checkout except the inert ones ([`is_inert_path`]: [`INERT_TREES`] and the top-level
//!   Markdown files), and for each file under an inert tree that a build reads
//!   ([`BUILD_INPUTS_IN_INERT_TREES`]). A gitlink (`first-party/*`) is named by its pin;
//! * the digest of the configuration file bootstrap read and of the files its `include`
//!   keys name, at any depth ([`config_digest`]);
//! * where the worktree departs from HEAD under those paths (an edit, an untracked file,
//!   a submodule checked out at another commit or edited, an untracked repository), each
//!   departing path's content now, through submodules at any depth
//!   ([`worktree_changes`]). An untracked repository is named by its HEAD and its own
//!   departures, never by walking its files.
//!
//! The SHA-256 of that record, cut to 40 hex digits, is the build's `commit-hash`. Its
//! first 9 digits are the short hash. Its `commit-date` is the committer date of the
//! newest commit that changed one of those paths. The same tree and configuration give
//! the same identity, and any difference between them gives a different one. A worktree
//! that departs from HEAD is named by HEAD's tree and its departures, so it never
//! carries a committed tree's name, and committing it names it anew (a rebuild, as the
//! new HEAD gave before). Only the repository's own ignore rules decide what is
//! untracked: a user's global excludes file is not read.
//!
//! When git cannot name the sources (it fails, HEAD moves while they are named, a path
//! cannot be read), the build is refused ([`of_build`]'s error): naming HEAD instead
//! would give an edited tree the name of HEAD's own. `rust.trust-source-identity =
//! false` names HEAD knowingly.
//!
//! The identity is not a commit, and git does not know it. An ancestry question asked of
//! a dev stage-1 `trustc -vV` therefore fails instead of answering for another tree. It
//! has a commit's shape because everything that checks a build's identity checks that
//! shape: targo's commit tuple (`src/tools/targo/build_commit_info.rs`), the verified
//! lane's trustc identity, and the run-make version tests. Those checks also compare the
//! components of one build with each other, and every component gets the same identity.
//!
//! The debuginfo remap prefix (`/rustc/<label>`) is a path label, not an identity. A
//! build named by its sources uses a stable development label. Neither editing nor
//! committing unrelated sources changes every crate's compiler arguments merely to
//! relabel its paths. The version still identifies the complete source state.
//! Private stage-0/1 `build`, `check` and `test` invocations also keep this stable
//! path namespace when `trust-source-identity = false`: that switch chooses the
//! truthful HEAD version required by bootstrap receipts, not a cache-invalidating
//! debug path. Stage 2, distribution, installation and release channels keep
//! commit-labelled paths. Path rules remain ordinary compiler/fingerprint inputs.
//!
//! Every other build keeps its commit ([`names_sources`], [`select`]):
//! * a stage-2 build, which is what `scripts/promote-toolchain.sh` seals, what
//!   `scripts/recreate_bootstrap.py --fresh-seed` builds, and what ancestry readers of
//!   `trustc -vV` read;
//! * `x.py dist` and `x.py install` at any stage;
//! * a `stable` or `beta` channel, or a downloaded rustc;
//! * a `--dry-run`, which builds nothing;
//! * a build that omits git information or comes from a source tarball.
//!
//! What it costs, and what it does not cover (docs/DECISION_QUEUE.md, "Taken 2026-10-16:
//! TB1"):
//! * Every uncommitted edit under the identity gives a new version. The crates that read
//!   the version are rebuilt after each edit, where HEAD's name used to keep them. In
//!   return, a toolchain built from an edited tree never shares `trustc -vV` with another
//!   tree's, which cargo reads to decide whether the compiler changed.
//! * A stage-1 build in a build directory where a stage-2 build ran (or the reverse)
//!   changes the version, and rebuilds as any change of version does.
//! * A tool rebuilds whenever the identity moves. The tools whose build scripts asked git
//!   for HEAD themselves (tippy and targo-miri through `rustc_tools_util`,
//!   trust-analyzer, its proc-macro server, trustfmt) read the identity from their
//!   commit tuple instead ([`tool_commit`]), so they rebuild with the identity and not
//!   on every commit; under `rust.omit-git-hash` bootstrap hands no tuple, and they ask
//!   git as before.
//! * A file under an inert tree that a build reads but [`BUILD_INPUTS_IN_INERT_TREES`]
//!   does not list is still rebuilt by cargo, but it does not change the identity. The
//!   test `every_build_input_under_an_inert_tree_is_listed` holds the list to what the
//!   checkout's code, build scripts and manifests read.
//! * Ignored files (by the repository's `.gitignore` files and `.git/info/exclude`),
//!   `--set` overrides and the environment are not part of the identity, as they were not
//!   part of HEAD's.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::{fs, io};

use sha2::Digest;

use crate::core::builder::Kind;
use crate::core::config::{Config, DryRun};
use crate::utils::channel::{GitInfo, Info};
use crate::utils::exec::{BootstrapCommand, ExecutionContext};
use crate::utils::helpers::{self, hex_encode};

/// The top-level trees of the checkout that no toolchain is built from: documentation
/// (with the decision queue), reports, the repository's scripts and the test suites.
pub(crate) const INERT_TREES: [&str; 4] = ["docs", "reports", "scripts", "tests"];

/// The files under one of [`INERT_TREES`] that a build reads. They stay in the identity.
///
/// * `scripts/frozen-files.txt`: `crates/trust-thir-lower/build.rs` reads it (and asks to
///   be rerun when it changes), and `rustc_mir_build` and `rustc_mir_transform` depend on
///   that crate.
/// * `tests/rustdoc-html/README.md`: tidy's `rustdoc_html_tests.rs` includes it.
/// * `tests/ui/README.md`: tidy's `ui_tests.rs` includes it.
/// * `tests/upstream-rust/targo-witness-layout.json`: cargo-test-support's
///   `paths/witness_layout.rs` includes the layout adapter's build-time ledger.
/// * `tests/ui/attributes/doc_examples`, a directory: `rustc_attr_ir`'s `attribute_docs.rs`
///   (upstream 8144389c895d) includes its examples (and their `.stderr`) as attribute docs,
///   one by a plain `include_str!` and the rest through a macro that names each by a
///   `concat!` the scan in `every_build_input_under_an_inert_tree_is_listed` does not
///   resolve. An entry names a file, or a directory and everything under it.
/// * The signed C ABI fixture's `driver.c` and `observe.S`: the bridge's
///   `abi_extensions/signed_tests.rs` embeds their exact source bytes.
pub(crate) const BUILD_INPUTS_IN_INERT_TREES: [&str; 7] = [
    "scripts/frozen-files.txt",
    "tests/run-make/trust-cg-source-c-signed-abi/driver.c",
    "tests/run-make/trust-cg-source-c-signed-abi/observe.S",
    "tests/rustdoc-html/README.md",
    "tests/ui/README.md",
    "tests/ui/attributes/doc_examples",
    "tests/upstream-rust/targo-witness-layout.json",
];

/// The record's first line. Anything that changes what the record holds changes it.
// Trust: v2 names the configuration by its bytes with the checkout's own root written
// as a fixed token ([`config_digest`]), so two worktrees with the same sources and the
// same configuration relative to their roots carry one identity (EW-9).
const SCHEMA: &str = "trust-dev-source-identity/v2";

/// A source-map namespace, deliberately not a source identity. Development
/// provenance remains in `Naming::version`; release paths still name the commit.
const DEVELOPMENT_REMAP_LABEL: &str = "trust-dev";

/// Whether a build with this channel, top-level command, top stage and `download-rustc`
/// is named by its sources ([`of_sources`]) rather than by its commit.
pub(crate) fn applies(channel: &str, kind: Kind, stage: u32, download_rustc: bool) -> bool {
    stage <= 1
        && !matches!(kind, Kind::Dist | Kind::Install)
        && !matches!(channel, "stable" | "beta")
        && !download_rustc
}

/// Whether the invocation `config` describes is named by its sources: the
/// `rust.trust-source-identity` switch is on, it is no `--dry-run` (which builds
/// nothing), and [`applies`] holds of its channel, command, top stage and
/// `download-rustc`. One invocation names one identity: in a `--stage 2` build the
/// stage-2 compiler loads crates the stage-1 compiler built, and a compiler refuses
/// crates built by a differently named one.
pub(crate) fn names_sources(config: &Config) -> bool {
    config.trust_source_identity
        && !matches!(config.get_dry_run(), DryRun::UserSelected)
        && applies(&config.channel, config.cmd.kind(), config.stage, config.download_rustc())
}

/// Private compiler development paths do not identify the source revision.
/// Keep this independent of `names_sources`: commit-bound bootstrap receipts
/// still require HEAD in the version tuple. The downloaded seed is untouched;
/// this policy labels only the source units compiled by the invocation.
fn private_development_paths(config: &Config) -> bool {
    matches!(config.cmd.kind(), Kind::Build | Kind::Check | Kind::Test)
        && !matches!(config.get_dry_run(), DryRun::UserSelected)
        // Path selection must not dispatch the CI downloader or depend on its
        // process-global cached result. A configured CI compiler is excluded.
        && applies(
            &config.channel,
            config.cmd.kind(),
            config.stage,
            config.download_rustc_commit.is_some(),
        )
}

/// What a build's version and paths carry ([`select`]).
pub(crate) struct Naming {
    /// What `CFG_VER_HASH`, `CFG_VER_DATE`, the hash and date in `CFG_VERSION`,
    /// `CFG_TRUST_VERSION`'s build metadata and the commit tuple of every tool built from
    /// the checkout's own sources ([`tool_commit`]) carry.
    pub(crate) version: GitInfo,
    /// The development debuginfo namespace (`/rustc/<label>`), independent of
    /// `version`. `None` keeps the commit-labelled path policy.
    pub(crate) remap: Option<String>,
}

/// What a build is named. `commit` is what git says of HEAD. When `dev` holds and git
/// names a commit, the build is named by what `sources` makes of it, and an error from
/// `sources` is the result. Otherwise it is named by `commit` itself.
pub(crate) fn select(
    commit: &GitInfo,
    dev: bool,
    sources: impl FnOnce(&Info) -> Result<Sources, String>,
) -> Result<Naming, String> {
    match commit {
        GitInfo::Present(Some(head)) if dev => {
            let Sources { info, .. } = sources(head)?;
            Ok(Naming {
                version: GitInfo::Present(Some(info)),
                remap: Some(DEVELOPMENT_REMAP_LABEL.to_owned()),
            })
        }
        _ => Ok(Naming { version: commit.clone(), remap: None }),
    }
}

/// Select source identity and path presentation separately. Preserve all
/// existing source-identity semantics, including its broader developer kinds.
/// A commit-named private build may share stable paths, but never an absent,
/// omitted or tarball Git identity, and never a release/install/dist build.
pub(crate) fn select_for_build(
    config: &Config,
    commit: &GitInfo,
    sources: impl FnOnce(&Info) -> Result<Sources, String>,
) -> Result<Naming, String> {
    let mut naming = select(commit, names_sources(config), sources)?;
    if private_development_paths(config) && matches!(commit, GitInfo::Present(Some(_))) {
        naming.remap = Some(DEVELOPMENT_REMAP_LABEL.to_owned());
    }
    Ok(naming)
}

/// What the commit tuple of the tool whose directory is `path` (relative to the checkout)
/// names: the `CFG_COMMIT_HASH`, `CFG_SHORT_COMMIT_HASH` and `CFG_COMMIT_DATE` that
/// `prepare_tool_cargo` hands its build. `submodules` are the paths `.gitmodules` lists.
///
/// A tool built from the checkout's own sources, which is every tool outside the
/// submodules (targo, tippy, targo-miri, trust-analyzer and its proc-macro server,
/// trustfmt and the rest of `src/tools/`), is named by `version`, the build's
/// [`Naming::version`]: a dev stage-1 build's source identity, and HEAD's commit
/// otherwise. Their build scripts read the tuple and ask git nothing when it is set, so a
/// tool's version names what `trustc -vV` names, and a commit that keeps the identity (one
/// to `docs/` alone) reruns none of them. A tool inside a submodule is named by its own
/// repository, `own`, as upstream names it; `own` is asked only then.
pub(crate) fn tool_commit(
    path: &Path,
    submodules: &[String],
    version: &GitInfo,
    own: impl FnOnce() -> GitInfo,
) -> GitInfo {
    if submodules.iter().any(|submodule| path.starts_with(submodule)) {
        own()
    } else {
        version.clone()
    }
}

/// Closed ownership of the three independent verifier executable recipes.
/// Mixed compiler and targo-trust graphs keep the enclosing workspace contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IndependentToolComponent {
    Ay,
    Ty,
    Clean,
}

impl IndependentToolComponent {
    pub(crate) fn root(self) -> &'static str {
        match self {
            Self::Ay => "first-party/ay",
            Self::Ty => "first-party/ty",
            Self::Clean => "first-party/clean",
        }
    }

    pub(crate) fn namespace(self) -> &'static str {
        match self {
            Self::Ay => "ay",
            Self::Ty => "ty",
            Self::Clean => "clean",
        }
    }
}

/// Trust: require the exact independent recipe and its declared repository.
/// A package name, path prefix or neighboring checkout establishes no ownership.
pub(crate) fn independent_tool_component(
    path: &Path,
    submodules: &[String],
) -> Option<IndependentToolComponent> {
    let component = if path == Path::new("first-party/ay/crates/ay") {
        IndependentToolComponent::Ay
    } else if path == Path::new("first-party/ty/crates/tla-cli") {
        IndependentToolComponent::Ty
    } else if path == Path::new("first-party/clean/crates/clean") {
        IndependentToolComponent::Clean
    } else {
        return None;
    };
    submodules.iter().any(|path| path == component.root()).then_some(component)
}

/// Trust: a path label for the independent component, not a compiler or proof identity.
/// Keep the existing own-component commit selection. Dirty inputs, including files
/// under `scripts/`, `tests/` and docs, get a distinct content-derived label: those
/// directories are not known to be inert in another repository. A failed read or
/// moving HEAD refuses the build instead of reusing a clean component's namespace.
/// An omitted/unavailable Git identity keeps the existing whole-build remap.
pub(crate) fn component_remap(
    exec_ctx: &ExecutionContext,
    src: &Path,
    commit: &GitInfo,
    component: IndependentToolComponent,
) -> Result<Option<String>, String> {
    let GitInfo::Present(Some(head)) = commit else { return Ok(None) };
    let mut changes = Vec::new();
    worktree_changes(exec_ctx, src, b"", false, &mut changes)?;
    let now = head_commit(exec_ctx, src)?;
    if now != head.sha {
        return Err(format!(
            "component HEAD moved from {} to {now} while bootstrap named its sources",
            head.sha
        ));
    }
    let label = if changes.is_empty() {
        head.sha.clone()
    } else {
        let mut record =
            format!("trust-{}-component-remap/v1\nhead {}\n", component.namespace(), head.sha);
        for change in changes {
            record.push_str(&change);
            record.push('\n');
        }
        digest(record.as_bytes())[..40].to_owned()
    };
    Ok(Some(format!("/rustc/{}/{label}", component.namespace())))
}

/// [`is_inert_path`] of a UTF-8 path, for the tests that hold the carve-outs to the
/// checkout. The build itself only ever asks [`is_inert_path`], of paths as git prints
/// them, so outside the tests this wrapper would be dead code (a `-D warnings` build of
/// bootstrap refuses it).
#[cfg(test)]
pub(crate) fn is_inert(path: &str) -> bool {
    is_inert_path(path.as_bytes())
}

/// Whether `path` is outside the identity. `path` is relative to the checkout root and
/// `/`-separated, as git prints it, and need not be UTF-8. That holds for a top-level
/// Markdown file, a top-level entry named in [`INERT_TREES`], and anything under one
/// except [`BUILD_INPUTS_IN_INERT_TREES`].
fn is_inert_path(mut path: &[u8]) -> bool {
    while let Some(trimmed) = path.strip_suffix(b"/") {
        path = trimmed;
    }
    let inert_tree = |name: &[u8]| INERT_TREES.iter().any(|tree| tree.as_bytes() == name);
    match path.iter().position(|&byte| byte == b'/') {
        Some(slash) => {
            inert_tree(&path[..slash])
                && !BUILD_INPUTS_IN_INERT_TREES.iter().any(|input| {
                    let input = input.as_bytes();
                    path == input
                        || (path.starts_with(input) && path.get(input.len()) == Some(&b'/'))
                })
        }
        None => inert_tree(path) || path.ends_with(b".md"),
    }
}

/// The digest of the configuration bootstrap read: the file at `config` (`None` when it
/// read none) and, depth first, each file an `include` key names, resolved as bootstrap
/// resolves it: beside the file that names it.
///
/// Each file is digested with every occurrence of the checkout's root `src` (as given and
/// canonical) replaced by [`ROOT_TOKEN`] ([`root_normalized`]). A configuration names
/// paths in its own checkout (`recreate_bootstrap.py` writes `<root>/build/...` and
/// `<root>/install`), and the same configuration in another worktree means the same
/// thing there. A path into any other directory, another worktree's included, is kept.
pub(crate) fn config_digest(config: Option<&Path>, src: &Path) -> String {
    let Some(path) = config else {
        return digest(b"config none\n");
    };
    let roots = root_spellings(src);
    let mut record = String::new();
    let mut open = HashSet::from([path.canonicalize().unwrap_or_else(|_| path.to_owned())]);
    config_file_digest(path, 0, &roots, &mut open, &mut record);
    digest(record.as_bytes())
}

/// What a configuration file's bytes become before they are digested: the checkout
/// root is written `\0root\0`. NUL cannot occur in a path, and a configuration that
/// holds one is not TOML, so no configuration's own text reads as the token.
pub(crate) const ROOT_TOKEN: &[u8] = b"\0root\0";

/// The spellings of the checkout root `src` that [`root_normalized`] replaces: as
/// given and canonical, longest first, without a trailing `/`.
fn root_spellings(src: &Path) -> Vec<Vec<u8>> {
    let mut roots = vec![src.as_os_str().as_encoded_bytes().to_vec()];
    if let Ok(canonical) = src.canonicalize() {
        roots.push(canonical.as_os_str().as_encoded_bytes().to_vec());
    }
    for root in &mut roots {
        while root.len() > 1 && root.ends_with(b"/") {
            root.pop();
        }
    }
    roots.retain(|root| root.len() > 1);
    roots.sort_by(|a, b| b.len().cmp(&a.len()).then(a.cmp(b)));
    roots.dedup();
    roots
}

/// `bytes` with each occurrence of a root in `roots` that stands at path boundaries
/// ([`replace_roots`]) written as [`ROOT_TOKEN`]. `/a/root` is not replaced in
/// `/a/rootx` or `/b/a/root`.
pub(crate) fn root_normalized(bytes: &[u8], roots: &[Vec<u8>]) -> Vec<u8> {
    let pairs: Vec<(&[u8], &[u8])> = roots.iter().map(|root| (&root[..], ROOT_TOKEN)).collect();
    replace_roots(bytes, &pairs)
}

/// Whether `byte` can continue a file name. Bytes of a multi-byte UTF-8 character can.
fn continues_name(byte: u8) -> bool {
    byte.is_ascii_alphanumeric()
        || byte >= 0x80
        || matches!(byte, b'-' | b'_' | b'.' | b'~' | b'+' | b'@' | b'%')
}

/// Whether a path starting at `at` in `bytes` starts there rather than continuing a
/// longer path: the bytes before it, back to the first that cannot continue a file name,
/// are no `/<component>` (`/b/a/root` holds no `/a/root`). A flag's letters may precede
/// it (`-L/a/root`), as may `=`, `:`, a quote or whitespace.
fn starts_path(bytes: &[u8], at: usize) -> bool {
    let before = &bytes[..at];
    match before.iter().rposition(|&byte| !continues_name(byte)) {
        Some(stop) => before[stop] != b'/',
        None => true,
    }
}

/// `bytes` with each occurrence of a `from` in `pairs` that is a whole path or a whole
/// path's leading components replaced by its `to`, in one pass, the longest `from` first
/// where two start at the same byte: one root may hold another (a checkout's own `.git`
/// lies inside it), and a replacement is never itself replaced again. An occurrence must
/// start a path ([`starts_path`]), and must end the text, or be followed by `/` or a byte
/// that cannot continue a file name.
pub(crate) fn replace_roots(bytes: &[u8], pairs: &[(&[u8], &[u8])]) -> Vec<u8> {
    let mut pairs: Vec<(&[u8], &[u8])> =
        pairs.iter().copied().filter(|(from, _)| !from.is_empty()).collect();
    pairs.sort_by(|a, b| b.0.len().cmp(&a.0.len()).then(a.0.cmp(b.0)));
    let mut out = Vec::with_capacity(bytes.len());
    let mut at = 0;
    'scan: while at < bytes.len() {
        for (from, to) in &pairs {
            if bytes[at..].starts_with(from) {
                let end = at + from.len();
                if bytes.get(end).is_none_or(|&byte| !continues_name(byte))
                    && starts_path(bytes, at)
                {
                    out.extend_from_slice(to);
                    at = end;
                    continue 'scan;
                }
            }
        }
        out.push(bytes[at]);
        at += 1;
    }
    out
}

/// Appends to `record` the line of the configuration file at `path`, `depth` includes
/// below the file bootstrap read, then those of the files it includes. `open` holds the
/// files whose includes are being read: bootstrap refuses an include of one of them, and
/// the record says `cycle` there.
fn config_file_digest(
    path: &Path,
    depth: usize,
    roots: &[Vec<u8>],
    open: &mut HashSet<PathBuf>,
    record: &mut String,
) {
    let bytes = fs::read(path);
    let line = match &bytes {
        Ok(bytes) => digest(&root_normalized(bytes, roots)),
        Err(error) => format!("unreadable-{:?}", error.kind()),
    };
    record.push_str(&format!("config {depth} {line}\n"));
    let includes = bytes
        .ok()
        .and_then(|bytes| String::from_utf8(bytes).ok())
        .and_then(|text| toml::from_str::<toml::Value>(&text).ok())
        .and_then(|value| value.get("include").and_then(|include| include.as_array()).cloned())
        .unwrap_or_default();
    let base = path.parent().unwrap_or(Path::new(""));
    for include in includes {
        let Some(name) = include.as_str() else {
            record.push_str(&format!("include {} not-a-path\n", depth + 1));
            continue;
        };
        let target = base.join(name);
        let target = target.canonicalize().unwrap_or(target);
        if !open.insert(target.clone()) {
            record.push_str(&format!("include {} cycle\n", depth + 1));
            continue;
        }
        config_file_digest(&target, depth + 1, roots, open, record);
        open.remove(&target);
    }
}

/// What [`select`] asks for in a build: the identity of the sources in the checkout at
/// `src`, configured by the file at `config`, recorded in the build directory `out`
/// ([`RECORD_FILE`]). An error says why git cannot name the sources.
pub(crate) fn of_build(
    exec_ctx: &ExecutionContext,
    src: &Path,
    out: &Path,
    config: Option<&Path>,
    head: &Info,
) -> Result<Sources, String> {
    let sources = of_sources(exec_ctx, src, &config_digest(config, src), head)?;
    if let Err(error) = write_record(out, head, &sources) {
        eprintln!("WARNING: could not write {}: {error}", out.join(RECORD_FILE).display());
    }
    Ok(sources)
}

/// A build's sources, as named by [`of_sources`].
pub(crate) struct Sources {
    /// The identity: what the build's version carries in place of HEAD's.
    pub(crate) info: Info,
    /// The record whose digest the identity is.
    pub(crate) record: String,
}

/// The identity of the sources the dev build in the checkout at `src` compiles, with
/// `config` the digest of its configuration ([`config_digest`]). `head` is what git said
/// of HEAD when bootstrap read its configuration. Every question about HEAD names that
/// commit, and the sources are refused when HEAD has moved since. Its date stands in
/// when no commit dates the sources. An error says why git cannot name them.
pub(crate) fn of_sources(
    exec_ctx: &ExecutionContext,
    src: &Path,
    config: &str,
    head: &Info,
) -> Result<Sources, String> {
    let commit = head.sha.as_str();
    let mut record = format!("{SCHEMA}\n");
    for entry in tree_entries(exec_ctx, src, commit)? {
        record.push_str(&entry);
        record.push('\n');
    }
    for input in BUILD_INPUTS_IN_INERT_TREES {
        let id = object_at(exec_ctx, src, commit, input);
        record.push_str(&format!("input {}\t{input}\n", id.as_deref().unwrap_or("absent")));
    }
    record.push_str(&format!("config {config}\n"));
    let mut changes = Vec::new();
    worktree_changes(exec_ctx, src, b"", true, &mut changes)?;
    let now = head_commit(exec_ctx, src)?;
    if now != commit {
        return Err(format!(
            "HEAD moved from {commit} to {now} while bootstrap named the sources; run it again"
        ));
    }
    for change in changes {
        record.push_str(&change);
        record.push('\n');
    }
    let sha = digest(record.as_bytes())[..40].to_owned();
    let commit_date =
        source_date(exec_ctx, src, commit).unwrap_or_else(|| head.commit_date.clone());
    Ok(Sources { info: Info { short_sha: sha[..9].to_owned(), sha, commit_date }, record })
}

/// Trust: a conservative source-input key for frontend component construction.
/// This is deliberately distinct from TB1 and is never a build/version identity.
/// Only the contents of existing, regular frontend Rust files may differ. Their
/// names and modes, all manifests, shared sources, submodule pins and departures,
/// and the actual configuration remain in the key. A future retained-runtime
/// consumer must additionally bind its recipe, seed, environment and actual
/// images; equality here alone grants neither compatibility nor execution.
pub(crate) fn frontend_runtime_sources(
    exec_ctx: &ExecutionContext,
    src: &Path,
    config: &str,
    head: &Info,
) -> Result<String, String> {
    let mut git = helpers::git(Some(src)).allow_failure();
    git.args(["ls-tree", "-r", "-z", "--full-tree", &head.sha]);
    let listing = captured(git, exec_ctx, "git ls-tree frontend runtime inputs", src)?;
    if listing.len() > 128 * 1024 * 1024 {
        return Err("frontend runtime source inventory exceeds 128 MiB".into());
    }
    let mut record = String::from("trust.frontend-runtime-sources.v1\n");
    let mut editable = std::collections::BTreeMap::new();
    for entry in listing.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
        let tab = entry.iter().position(|&byte| byte == b'\t').ok_or_else(|| {
            "frontend runtime git inventory contains an entry without a name".to_owned()
        })?;
        let (object, name) = (&entry[..tab], &entry[tab + 1..]);
        let explicit_input = BUILD_INPUTS_IN_INERT_TREES.iter().any(|input| {
            name == input.as_bytes()
                || name.strip_prefix(input.as_bytes()).is_some_and(|tail| tail.starts_with(b"/"))
        });
        if is_inert_path(name) && !explicit_input {
            continue;
        }
        let fields: Vec<_> = object.split(|&byte| byte == b' ').collect();
        if fields.len() != 3 || object_id(fields[2]).is_none() {
            return Err("frontend runtime git inventory contains a malformed object".into());
        }
        let label = quoted(name);
        let regular = fields[1] == b"blob" && matches!(fields[0], b"100644" | b"100755");
        if regular && name.starts_with(b"targo-trust/src/") && name.ends_with(b".rs") {
            let executable = fields[0] == b"100755";
            editable.insert(label.clone(), executable);
            record.push_str(&format!("frontend-source {}\t{label}\n", quoted(fields[0])));
        } else {
            record.push_str(&format!("{}\t{label}\n", quoted(object)));
        }
    }
    let mut changes = Vec::new();
    // Preserve the existing full nested-repository departure observation. The
    // output escapes tabs in paths, leaving exactly one separator per row.
    worktree_changes(exec_ctx, src, b"", true, &mut changes)?;
    for change in changes {
        if let Some((value, label)) = change.split_once('\t') {
            let same_regular_mode = match editable.get(label) {
                Some(false) => value.starts_with("path file - "),
                Some(true) => value.starts_with("path file x "),
                None => false,
            };
            if same_regular_mode {
                continue;
            }
        }
        record.push_str(&change);
        record.push('\n');
    }
    record.push_str(&format!("config {config}\n"));
    if head_commit(exec_ctx, src)? != head.sha {
        return Err("HEAD moved while naming frontend runtime source inputs".into());
    }
    Ok(digest(record.as_bytes()))
}

/// Trust (DC-16a): whether the inputs at `inputs` (paths relative to the checkout at
/// `src`, each a tree, a file or a submodule's gitlink) are the same at `source`, the
/// commit a toolchain was built from, as in this checkout: the object HEAD (`head`)
/// records at each, and no worktree departure under any of them. A submodule's input is
/// its pin, and a departure under it is the submodule checked out at another commit or
/// edited, at any depth ([`worktree_changes`]).
///
/// An error says which input differs, or why git cannot say: `source` is no commit this
/// repository holds (it is never fetched), an input is absent on either side, a path
/// cannot be read, or HEAD moved while the inputs were read. Every error means the
/// inputs are not known to be equal.
pub(crate) fn inputs_unchanged_since(
    exec_ctx: &ExecutionContext,
    src: &Path,
    source: &str,
    head: &Info,
    inputs: &[&str],
) -> Result<(), String> {
    if object_id(source.as_bytes()).as_deref() != Some(source) {
        return Err(format!("the source toolchain names no full commit: {source:?}"));
    }
    let mut git = helpers::git(Some(src)).allow_failure();
    git.args(["rev-parse", "--verify", "--quiet"]).arg(format!("{source}^{{commit}}"));
    let held = captured(git, exec_ctx, "git rev-parse --verify", src).ok();
    if held.as_deref().and_then(object_id).as_deref() != Some(source) {
        return Err(format!("this repository holds no commit {source}"));
    }
    for input in inputs {
        let then = object_at(exec_ctx, src, source, input);
        let now = object_at(exec_ctx, src, &head.sha, input);
        if then.is_none() || then != now {
            return Err(format!(
                "{input} is {} at {source} and {} at HEAD {}",
                then.as_deref().unwrap_or("absent"),
                now.as_deref().unwrap_or("absent"),
                head.sha
            ));
        }
    }
    let mut changes = Vec::new();
    worktree_changes_under(exec_ctx, src, b"", false, inputs, &mut changes)?;
    if let Some(change) = changes.first() {
        return Err(format!("the worktree departs from HEAD under the inputs: {change}"));
    }
    let now = head_commit(exec_ctx, src)?;
    if now != head.sha {
        return Err(format!(
            "HEAD moved from {} to {now} while bootstrap read the inputs",
            head.sha
        ));
    }
    Ok(())
}

/// Trust (DC-16a): whether every source Cargo can read for a package of the repository
/// checked out at `root` (a submodule of the checkout at `src`, `root` relative to it)
/// lies inside that repository, so that its pin names them all. Each tracked
/// `Cargo.toml` and `.cargo/config(.toml)` is read, and each `path` (a path dependency,
/// a patch, a target's source), `build` script, `workspace` root and `paths` entry (a
/// path override) in it must resolve, lexically, inside `root`. A file a source names
/// by `include!`-family macros is not a Cargo-listed source and is not read here. Registry and git sources are named by the
/// repository's own lockfile, which its pin holds.
///
/// It reads the checkout's files, so it answers for the pin only when no departure
/// under `root` exists ([`inputs_unchanged_since`]). An error names the first source
/// outside `root`, or why the manifests cannot be read or parsed: a repository that is
/// not checked out is not known to be closed.
pub(crate) fn component_sources_closed(
    exec_ctx: &ExecutionContext,
    src: &Path,
    root: &str,
) -> Result<(), String> {
    let dir = src.join(root);
    if !dir.join(".git").exists() {
        return Err(format!("{root} is not checked out"));
    }
    let mut git = helpers::git(Some(&dir)).allow_failure();
    git.args(["ls-files", "-z", "--"]).args([
        ":(glob)**/Cargo.toml",
        ":(glob)**/.cargo/config.toml",
        ":(glob)**/.cargo/config",
    ]);
    let listing = captured(git, exec_ctx, "git ls-files manifests", &dir)?;
    let mut manifests = 0;
    for name in listing.split(|&byte| byte == 0).filter(|name| !name.is_empty()) {
        let relative = path_of(name)?;
        let text = fs::read_to_string(dir.join(&relative))
            .map_err(|error| format!("cannot read {root}/{}: {error}", relative.display()))?;
        let document = text
            .parse::<toml::Value>()
            .map_err(|error| format!("cannot parse {root}/{}: {error}", relative.display()))?;
        // Cargo resolves a manifest's paths against its directory, and a
        // configuration's against the directory that holds its `.cargo`.
        let mut base = relative.parent().unwrap_or(Path::new("")).to_path_buf();
        if base.file_name().is_some_and(|name| name == ".cargo") {
            base.pop();
        }
        let mut escape = None;
        manifest_source_paths(&document, &mut |value| {
            if escape.is_none() && !stays_inside(&base, value) {
                escape = Some(value.to_owned());
            }
        });
        if let Some(value) = escape {
            return Err(format!(
                "{root}/{} names the source {value:?} outside {root}",
                relative.display()
            ));
        }
        manifests += 1;
    }
    if manifests == 0 {
        return Err(format!("{root} tracks no Cargo manifest"));
    }
    Ok(())
}

/// Calls `found` with every string a `path`, `build` or `workspace` key holds and
/// every entry of a `paths` array, at any depth of `value`.
fn manifest_source_paths(value: &toml::Value, found: &mut impl FnMut(&str)) {
    match value {
        toml::Value::Table(table) => {
            for (key, value) in table {
                match (key.as_str(), value) {
                    // A dependency's, patch's or target's `path`, a package's build
                    // script (`build`) and its workspace root (`workspace`).
                    ("path" | "build" | "workspace", toml::Value::String(path)) => found(path),
                    ("paths", toml::Value::Array(paths)) => {
                        for path in paths {
                            match path.as_str() {
                                Some(path) => found(path),
                                // Not a path Cargo reads: refuse it as one outside.
                                None => found("/"),
                            }
                        }
                    }
                    _ => manifest_source_paths(value, &mut *found),
                }
            }
        }
        toml::Value::Array(values) => {
            for value in values {
                manifest_source_paths(value, &mut *found);
            }
        }
        _ => {}
    }
}

/// Whether `value`, resolved against `base` (both relative to a repository's root),
/// stays inside that root by its components alone. An absolute path never does.
fn stays_inside(base: &Path, value: &str) -> bool {
    use std::path::Component;
    let value = Path::new(value);
    if value.has_root() || value.is_absolute() {
        return false;
    }
    let mut depth = 0usize;
    for component in base.components().chain(value.components()) {
        match component {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir => match depth.checked_sub(1) {
                Some(up) => depth = up,
                None => return false,
            },
            Component::RootDir | Component::Prefix(_) => return false,
        }
    }
    true
}

/// The file in a build directory that says what the version of its last dev stage-1
/// build names: `head <commit>`, `identity <hash>` and `date <date>` lines, then the
/// record whose digest the identity is ([`of_sources`]). It is how a reader of a dev
/// stage-1 `trustc -vV` maps its `commit-hash` back to sources: the record's digest must
/// be that hash, and then `head` is the commit those sources were taken from. The
/// worktree's own changes are the record's `path`, `submodule` and `repo` lines.
pub(crate) const RECORD_FILE: &str = "trust-source-identity";

/// Writes [`RECORD_FILE`] into the build directory `out`, replacing it whole.
pub(crate) fn write_record(out: &Path, head: &Info, sources: &Sources) -> io::Result<()> {
    let Sources { info, record, .. } = sources;
    let text =
        format!("head {}\nidentity {}\ndate {}\n{record}", head.sha, info.sha, info.commit_date);
    fs::create_dir_all(out)?;
    let partial = out.join(format!("{RECORD_FILE}.{}.partial", std::process::id()));
    fs::write(&partial, text)?;
    fs::rename(&partial, out.join(RECORD_FILE))
}

/// The top-level entries that `commit` records in the checkout at `src`, except the
/// inert ones, as `git ls-tree` prints them: mode, type and object id, then the name
/// after a tab ([`quoted`]).
fn tree_entries(
    exec_ctx: &ExecutionContext,
    src: &Path,
    commit: &str,
) -> Result<Vec<String>, String> {
    let mut git = helpers::git(Some(src)).allow_failure();
    git.args(["ls-tree", "-z", "--full-tree", commit]);
    let listing = captured(git, exec_ctx, &format!("git ls-tree {commit}"), src)?;
    let mut entries = Vec::new();
    for entry in listing.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
        let tab = entry.iter().position(|&byte| byte == b'\t').ok_or_else(|| {
            format!("git ls-tree {commit} printed an entry without a name: {}", quoted(entry))
        })?;
        let (object, name) = (&entry[..tab], &entry[tab + 1..]);
        if !is_inert_path(name) {
            entries.push(format!("{}\t{}", quoted(object), quoted(name)));
        }
    }
    Ok(entries)
}

/// The git object id `commit` records at `path` in the checkout at `src`, if it records
/// one.
fn object_at(exec_ctx: &ExecutionContext, src: &Path, commit: &str, path: &str) -> Option<String> {
    let mut git = helpers::git(Some(src)).allow_failure();
    git.args(["rev-parse", "--verify", "--quiet"]).arg(format!("{commit}:{path}"));
    let output = captured(git, exec_ctx, "git rev-parse", src).ok()?;
    object_id(&output)
}

/// The commit the repository at `dir` has checked out.
fn head_commit(exec_ctx: &ExecutionContext, dir: &Path) -> Result<String, String> {
    let mut git = helpers::git(Some(dir)).allow_failure();
    git.args(["rev-parse", "--verify", "HEAD"]);
    let output = captured(git, exec_ctx, "git rev-parse --verify HEAD", dir)?;
    object_id(&output).ok_or_else(|| {
        format!("git rev-parse --verify HEAD in {} printed no commit", dir.display())
    })
}

/// One record of `git status --porcelain=v2 -z` that names paths ([`status_records`]).
#[derive(Debug, PartialEq)]
pub(crate) struct StatusRecord<'a> {
    /// Whether git calls the path a submodule (`S...`).
    pub(crate) submodule: bool,
    /// Whether the path is untracked (`?`).
    pub(crate) untracked: bool,
    /// The path, and for a rename or a copy the path it came from.
    pub(crate) paths: Vec<&'a [u8]>,
}

/// The records of `git status --porcelain=v2 -z` output that name paths, in order:
/// changed (`1`), renamed or copied (`2`), unmerged (`u`) and untracked (`?`). Headers
/// (`#`) and ignored paths (`!`) name nothing in the identity. An error names a record
/// of another shape.
pub(crate) fn status_records(status: &[u8]) -> Result<Vec<StatusRecord<'_>>, String> {
    let mut records = status.split(|&byte| byte == 0).filter(|record| !record.is_empty());
    let mut parsed = Vec::new();
    while let Some(record) = records.next() {
        let malformed =
            || format!("git status printed a record of no known shape: {}", quoted(record));
        // The fields before the path, the type's letter included; the path is the rest.
        let fields = match record.get(..2) {
            // `1 <XY> <sub> <mH> <mI> <mW> <hH> <hI> <path>`
            Some(b"1 ") => 8,
            // `2 <XY> <sub> <mH> <mI> <mW> <hH> <hI> <Xscore> <path>`, then `<origPath>`
            // (`--no-renames` asks for none; a configuration could still produce one).
            Some(b"2 ") => 9,
            // `u <XY> <sub> <m1> <m2> <m3> <mW> <h1> <h2> <h3> <path>`
            Some(b"u ") => 10,
            Some(b"? ") => {
                let path = &record[2..];
                parsed.push(StatusRecord { submodule: false, untracked: true, paths: vec![path] });
                continue;
            }
            Some(b"# " | b"! ") => continue,
            _ => return Err(malformed()),
        };
        let parts: Vec<&[u8]> = record.splitn(fields + 1, |&byte| byte == b' ').collect();
        let (Some(sub), Some(&path)) = (parts.get(2), parts.get(fields)) else {
            return Err(malformed());
        };
        if parts.len() != fields + 1 || path.is_empty() {
            return Err(malformed());
        }
        let mut paths = vec![path];
        if fields == 9 {
            paths.push(records.next().ok_or_else(malformed)?);
        }
        parsed.push(StatusRecord { submodule: sub.starts_with(b"S"), untracked: false, paths });
    }
    Ok(parsed)
}

/// Appends to `out` one line for each path where the worktree of the repository at `dir`
/// departs from its HEAD. For a path, the line holds its content now ([`content`]). For
/// a submodule or an untracked repository, it holds the commit the repository has
/// checked out, and the repository's own lines follow. `prefix` is `dir` relative to
/// the checkout: empty for the checkout itself, whose inert paths are skipped (a
/// submodule has no inert paths). An error says why git cannot say, or which path
/// cannot be read.
fn worktree_changes(
    exec_ctx: &ExecutionContext,
    dir: &Path,
    prefix: &[u8],
    omit_inert: bool,
    out: &mut Vec<String>,
) -> Result<(), String> {
    worktree_changes_under(exec_ctx, dir, prefix, omit_inert, &[], out)
}

/// [`worktree_changes`] of the paths `under` (relative to `dir`; all of it when empty).
/// A repository found there is read whole, as [`worktree_changes`] reads it.
fn worktree_changes_under(
    exec_ctx: &ExecutionContext,
    dir: &Path,
    prefix: &[u8],
    omit_inert: bool,
    under: &[&str],
    out: &mut Vec<String>,
) -> Result<(), String> {
    let mut git = helpers::git(Some(dir)).allow_failure();
    git.args([
        // Only the repository's own ignore rules decide what is untracked: a global
        // excludes file differs between machines, and could hide a compiled file.
        "-c",
        "core.excludesFile=",
        "status",
        "--porcelain=v2",
        "-z",
        "--no-branch",
        "--ignore-submodules=none",
        "--untracked-files=all",
        "--no-renames",
    ]);
    if !under.is_empty() {
        // Literal paths: a name is never read as a glob or a pathspec magic word.
        git.arg("--").args(under.iter().map(|path| format!(":(literal){path}")));
    }
    // A reader: never take the index lock from a git command run beside this build.
    git.env("GIT_OPTIONAL_LOCKS", "0");
    let status = captured(git, exec_ctx, "git status", dir)?;
    for record in status_records(&status)? {
        for path in record.paths {
            if omit_inert && prefix.is_empty() && is_inert_path(path) {
                continue;
            }
            let name = [prefix, path].concat();
            let checkout = dir.join(path_of(path)?);
            let label = quoted(&name);
            // A repository checked out at the path: a submodule, or an untracked
            // repository (which git lists as a directory and never descends into). It is
            // named by the commit it has checked out and its own departures. A submodule
            // that is not checked out is named by what its directory holds, as any path.
            let repository = (record.submodule || (record.untracked && path.ends_with(b"/")))
                && checkout.join(".git").exists();
            if repository {
                let mut inner = name.clone();
                if !inner.ends_with(b"/") {
                    inner.push(b'/');
                }
                if record.submodule {
                    out.push(format!("submodule {}\t{label}", head_commit(exec_ctx, &checkout)?));
                } else {
                    // A repository with no commit yet is named by its departures alone.
                    let head = head_commit(exec_ctx, &checkout).unwrap_or_else(|_| "unborn".into());
                    out.push(format!("repo {head}\t{label}"));
                }
                worktree_changes_under(exec_ctx, &checkout, &inner, omit_inert, &[], out)?;
            } else {
                out.push(format!("path {}\t{label}", content(&checkout)?));
            }
        }
    }
    Ok(())
}

/// What the worktree holds at `path` now: `absent`, or the kind of entry and a digest of
/// it (for a directory, of its entries except `.git`). A FIFO, a socket or a device is
/// `other`: nothing a build compiles. An error names a path that cannot be read.
fn content(path: &Path) -> Result<String, String> {
    let unreadable = |error: io::Error| format!("cannot read {}: {error}", path.display());
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok("absent".to_owned()),
        Err(error) => return Err(unreadable(error)),
    };
    let kind = metadata.file_type();
    if kind.is_symlink() {
        let target = fs::read_link(path).map_err(unreadable)?;
        Ok(format!("link {}", digest(target.as_os_str().as_encoded_bytes())))
    } else if kind.is_file() {
        let mut hasher = sha2::Sha256::new();
        let mut file = fs::File::open(path).map_err(unreadable)?;
        io::copy(&mut file, &mut hasher).map_err(unreadable)?;
        let mode = if is_executable(&metadata) { "x" } else { "-" };
        Ok(format!("file {mode} {}", hex_encode(hasher.finalize().as_slice())))
    } else if kind.is_dir() {
        let mut names = fs::read_dir(path)
            .map_err(unreadable)?
            .map(|entry| entry.map(|entry| entry.file_name()))
            .collect::<io::Result<Vec<_>>>()
            .map_err(unreadable)?;
        names.sort();
        let mut listing = String::new();
        for name in names {
            if name == ".git" {
                continue;
            }
            let entry = content(&path.join(&name))?;
            listing.push_str(&format!("{entry}\t{}\n", quoted(name.as_encoded_bytes())));
        }
        Ok(format!("dir {}", digest(listing.as_bytes())))
    } else {
        Ok("other".to_owned())
    }
}

#[cfg(unix)]
fn is_executable(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt;
    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn is_executable(_: &fs::Metadata) -> bool {
    false
}

/// The path git printed as `bytes`, relative to the repository it ran in.
#[cfg(unix)]
fn path_of(bytes: &[u8]) -> Result<PathBuf, String> {
    use std::os::unix::ffi::OsStrExt;
    Ok(PathBuf::from(std::ffi::OsStr::from_bytes(bytes)))
}

/// The path git printed as `bytes`, relative to the repository it ran in.
#[cfg(not(unix))]
fn path_of(bytes: &[u8]) -> Result<PathBuf, String> {
    std::str::from_utf8(bytes)
        .map(PathBuf::from)
        .map_err(|_| format!("git printed a path that is not UTF-8: {}", quoted(bytes)))
}

/// A name for the record that no other name shares: UTF-8 as it is, except that a
/// backslash, a tab and a newline are escaped, and each byte that is not UTF-8 is
/// `\x<hex>`.
pub(crate) fn quoted(name: &[u8]) -> String {
    let mut text = String::with_capacity(name.len());
    for chunk in name.utf8_chunks() {
        for character in chunk.valid().chars() {
            match character {
                '\\' => text.push_str("\\\\"),
                '\t' => text.push_str("\\t"),
                '\n' => text.push_str("\\n"),
                character => text.push(character),
            }
        }
        for byte in chunk.invalid() {
            text.push_str(&format!("\\x{byte:02x}"));
        }
    }
    text
}

/// The committer date (`--date=short`) of the newest commit, from `commit` back, that
/// changed a path in the identity. `None` when no commit did, or git cannot say: the
/// date names no source, and the identity's hash does.
fn source_date(exec_ctx: &ExecutionContext, src: &Path, commit: &str) -> Option<String> {
    let mut everything = vec![".".to_owned()];
    everything.extend(INERT_TREES.iter().map(|tree| format!(":(exclude){tree}")));
    everything.push(":(exclude,glob)*.md".to_owned());
    let mut pathspecs = vec![everything];
    pathspecs.extend(BUILD_INPUTS_IN_INERT_TREES.iter().map(|input| vec![(*input).to_owned()]));
    pathspecs
        .into_iter()
        .filter_map(|pathspec| {
            let mut git = helpers::git(Some(src)).allow_failure();
            git.args(["log", "-1", "--no-show-signature", "--date=short", "--pretty=format:%cd"]);
            git.args([commit, "--"]).args(pathspec);
            let date = captured(git, exec_ctx, "git log", src).ok()?;
            let date = String::from_utf8(date).ok()?;
            let date = date.trim();
            (!date.is_empty()).then(|| date.to_owned())
        })
        .max()
}

/// What `git` printed, when it succeeded. An error names the command (`what`), the
/// repository it ran in (`dir`) and what git said.
///
/// Every command here is asked in bootstrap's dry-run pass too, so that the pass and the
/// run it precedes name the same sources, and none of them fetches: in a partial clone a
/// missing object is an unnamed source, never a download.
fn captured(
    mut git: BootstrapCommand,
    exec_ctx: &ExecutionContext,
    what: &str,
    dir: &Path,
) -> Result<Vec<u8>, String> {
    git.env("GIT_NO_LAZY_FETCH", "1");
    git.run_in_dry_run();
    let output = git.run_capture(exec_ctx);
    match output.stdout_bytes_if_present() {
        Some(stdout) if output.is_success() => Ok(stdout.to_vec()),
        _ => {
            let said = output.stderr_if_present().unwrap_or_default();
            Err(format!("`{what}` failed in {}: {}", dir.display(), said.trim()))
        }
    }
}

/// A full git object id (sha1 or sha256, lowercase hex), when `output` is one.
fn object_id(output: &[u8]) -> Option<String> {
    let id = std::str::from_utf8(output).ok()?.trim();
    let hex = id.bytes().all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'));
    (matches!(id.len(), 40 | 64) && hex).then(|| id.to_owned())
}

fn digest(bytes: &[u8]) -> String {
    let mut hasher = sha2::Sha256::new();
    hasher.update(bytes);
    hex_encode(hasher.finalize().as_slice())
}

#[cfg(test)]
mod tests;
