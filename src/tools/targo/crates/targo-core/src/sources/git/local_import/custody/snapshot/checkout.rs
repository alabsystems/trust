//! Exact selected checkout DATA under the same original cache/ODB guards.
//! Donor Git configuration, hooks, indexes and completion markers are not input
//! authority. Every admitted working file is joined to the selected Git tree.
use super::super::super::{locked_oid, submodules};
use super::selected::Database;
use super::*;
use crate::workspace::SourceId;

const MAX_DEPTH: usize = 64;

pub(super) fn validate_checkout_name(name: &OsStr, checkout_root: bool) -> CargoResult<()> {
    ensure!(
        Path::new(name).components().count() == 1
            && matches!(
                Path::new(name).components().next(),
                Some(std::path::Component::Normal(_))
            )
            && name != ".git"
            && (name != ".cargo-ok" || !checkout_root),
        "unsupported selected checkout name: {name:?} (Cargo checkout root: {checkout_root})"
    );
    Ok(())
}

pub(in crate::sources::git::local_import::custody) struct Checkout {
    source: ObjectSource,
}
impl Checkout {
    pub(in crate::sources::git::local_import::custody) fn check_current(&self) -> CargoResult<()> {
        self.source.check_current()
    }
}

// Trust: retain original names/HEAD before reading checkout object DATA. The
// recovery profile also requires the actual ready marker and no repository
// indirection; neither marker nor abbreviated directory name grants authority.
pub(in crate::sources::git::local_import::custody) fn capture_original_checkout(
    root: Directory,
    revision: git2::Oid,
    recovery: bool,
) -> CargoResult<Checkout> {
    let mut actual = Checkout {
        source: ObjectSource {
            root,
            directories: BTreeMap::new(),
            files: Vec::new(),
            forbidden: Vec::new(),
            failed: Cell::new(false),
            depth_limit: MAX_DEPTH + 4,
        },
    };
    actual.source.directories.insert(
        actual.source.root.path.clone(),
        actual.source.root.before.clone(),
    );
    check_head(&mut actual, revision)?;
    if recovery {
        let root = Directory::open(&actual.source.root.path)?;
        ensure!(
            original_reference(&mut actual, &root, OsStr::new(".cargo-ok"))?.is_empty(),
            "unsupported original checkout ready marker"
        );
        for relative in [
            ".git/shallow",
            ".git/commondir",
            ".git/config.worktree",
            ".git/info/grafts",
            ".git/refs/replace",
        ] {
            ensure!(
                actual.source.root.missing_relative(Path::new(relative))?,
                "unsupported checkout recovery indirection: {relative}"
            );
            actual.source.forbidden.push(PathBuf::from(relative));
        }
    }
    actual.check_current()?;
    Ok(actual)
}

pub(super) fn copy_selected(
    cache: &Cache,
    sources: &[SourceId],
    databases: &BTreeMap<String, Database>,
    destination: &Path,
    output: &mut Output,
    budget: &mut CopyBudget,
) -> CargoResult<(Vec<Checkout>, Stats)> {
    let mut forecast = Forecast::default();
    for source in sources {
        let database = databases
            .get(&crate::sources::git::source::ident(source))
            .context("checkout forecast lost selected ODB")?;
        let revision = locked_oid(*source)?;
        let short = crate::sources::git::utils::checkout_short_id(&database.input.odb()?, revision)
            .with_context(|| {
                crate::sources::git::source::object_source_context(*source, revision)
            })?;
        let missing = cache.home.missing_relative(
            &PathBuf::from("git/checkouts")
                .join(crate::sources::git::source::ident(source))
                .join(short),
        )?;
        forecast_repository(
            &submodules::Source {
                id: *source,
                parent_url: source.url().to_string(),
            },
            databases,
            &mut forecast,
            missing,
            0,
        )?;
    }
    // This is a measured forecast, not a reservation: later allocations still
    // retain their ordinary errors/bookends. Missing worktrees would otherwise
    // make Cargo expand the full selected tree after publication.
    let metadata = (forecast.entries as u64)
        .checked_mul(4096)
        .context("checkout metadata forecast overflow")?;
    let streamed =
        if output.root.before.dev() == cache.home.before.dev() && cfg!(target_os = "macos") {
            forecast.missing_bytes
        } else {
            forecast.bytes
        };
    let required = streamed
        .checked_add(metadata)
        .and_then(|n| n.checked_add(64 * 1024 * 1024))
        .context("checkout capacity forecast overflow")?;
    let volume = rustix::fs::fstatvfs(&output.root.file)?;
    let available = u128::from(volume.f_bavail)
        .checked_mul(u128::from(volume.f_frsize))
        .context("checkout available capacity overflow")?;
    ensure!(
        available >= u128::from(required),
        "selected checkout output needs {required} forecast bytes but only {available} are available"
    );
    let mut owners = Vec::new();
    // The stored-object counter remains unchanged. Expanded selected checkouts
    // have their own 32GiB domain; both share the original stream-copy budget,
    // namespace/entry bounds and final publication bookends.
    let mut stats = Stats::default();
    for source in sources {
        cache.check_current()?;
        let revision = locked_oid(*source)?;
        let ident = crate::sources::git::source::ident(source);
        let database = databases
            .get(&ident)
            .context("checkout lost selected source ODB")?;
        let short = crate::sources::git::utils::checkout_short_id(&database.input.odb()?, revision)
            .with_context(|| {
                crate::sources::git::source::object_source_context(*source, revision)
            })?;
        let relative = PathBuf::from("git/checkouts").join(&ident).join(&short);
        if cache.home.missing_relative(&relative)? {
            continue; // Ordinary Cargo materialization remains unchanged.
        }
        let root = cache
            .home
            .child(OsStr::new("git"))?
            .child(OsStr::new("checkouts"))?
            .child(OsStr::new(&ident))?
            .child(OsStr::new(&short))?;
        root.current()?;
        let mut actual = capture_original_checkout(root, revision, false)?;
        let root_path = actual.source.root.path.clone();
        output.depth_limit = MAX_DEPTH + 4;
        let id = submodules::Source {
            id: *source,
            parent_url: source.url().to_string(),
        };
        copy_repository(
            &mut actual,
            &root_path,
            &relative,
            &id,
            &Context {
                databases,
                destination,
            },
            &mut Transfer {
                output,
                stats: &mut stats,
                budget,
            },
            0,
        )?;
        actual.check_current()?;
        cache.check_current()?;
        owners.push(actual);
    }
    Ok((owners, stats))
}

fn check_head(actual: &mut Checkout, revision: git2::Oid) -> CargoResult<()> {
    let directory = actual.source.root.child(OsStr::new(".git"))?;
    directory.current()?;
    actual
        .source
        .directories
        .insert(directory.path.clone(), directory.before.clone());
    let bytes = original_reference(actual, &directory, OsStr::new("HEAD"))?;
    let expected = format!("{revision}\n");
    if bytes == expected.as_bytes() {
        return actual.check_current();
    }
    let name = bytes
        .strip_prefix(b"ref: ")
        .and_then(|name| name.strip_suffix(b"\n"))
        .context("unsupported original checkout HEAD form")?;
    let name = std::str::from_utf8(name).context("original checkout reference must be UTF8")?;
    ensure!(
        name.starts_with("refs/heads/") && git2::Reference::is_valid_name(name),
        "unsupported original checkout branch reference"
    );
    let mut parent = directory;
    let parts = Path::new(name).components().collect::<Vec<_>>();
    ensure!(
        parts.len() <= MAX_DEPTH
            && parts
                .iter()
                .all(|part| matches!(part, std::path::Component::Normal(_))),
        "noncanonical original checkout reference"
    );
    let (leaf, parents) = parts
        .split_last()
        .context("empty original checkout reference")?;
    for part in parents {
        parent.current()?;
        parent = parent.child(part.as_os_str())?;
        actual
            .source
            .directories
            .insert(parent.path.clone(), parent.before.clone());
    }
    let branch = original_reference(actual, &parent, leaf.as_os_str())?;
    ensure!(
        branch == expected.as_bytes(),
        "original checkout branch differs from locked revision: {}",
        actual.source.root.path.display()
    );
    actual.check_current()
}

fn original_reference(
    actual: &mut Checkout,
    directory: &Directory,
    name: &OsStr,
) -> CargoResult<Vec<u8>> {
    let mut file = File::from(rustix::fs::openat(
        &directory.file,
        name,
        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )?);
    let before = file.metadata()?;
    ensure!(
        before.is_file() && before.len() <= 128,
        "unsupported original checkout HEAD"
    );
    let mut bytes = Vec::new();
    std::io::Read::by_ref(&mut file)
        .take(129)
        .read_to_end(&mut bytes)?;
    ensure!(
        stamp(&before, &file.metadata()?),
        "original checkout HEAD changed"
    );
    actual
        .source
        .files
        .push((directory.path.join(name), before));
    actual.check_current()?;
    Ok(bytes)
}

fn observe_legacy_marker(actual: &mut Checkout, directory: &Directory) -> CargoResult<()> {
    let name = OsStr::new(".cargo-ok");
    let open = || -> CargoResult<File> {
        Ok(File::from(rustix::fs::openat(
            &directory.file,
            name,
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
            Mode::empty(),
        )?))
    };
    let mut file = open()?;
    let before = file.metadata()?;
    ensure!(
        before.is_file()
            && before.nlink() == 1
            && before.len() == 0
            && before.uid() == actual.source.root.before.uid()
            && matches!(before.mode() & 0o7777, 0o600 | 0o640 | 0o644),
        "unsupported legacy submodule completion marker"
    );
    trust_resource_provenance::require_no_acl_grants(&file)?;
    ensure!(
        file.read(&mut [0])? == 0
            && stamp(&before, &file.metadata()?)
            && stamp(&before, &open()?.metadata()?),
        "legacy submodule completion marker changed"
    );
    actual
        .source
        .files
        .push((directory.path.join(name), before));
    actual.check_current()
}

struct Context<'a> {
    databases: &'a BTreeMap<String, Database>,
    destination: &'a Path,
}
struct Transfer<'a> {
    output: &'a mut Output,
    stats: &'a mut Stats,
    budget: &'a mut CopyBudget,
}
struct Walk<'a> {
    original: &'a Path,
    prefix: &'a Path,
    repository: &'a git2::Repository,
    root: &'a git2::Tree<'a>,
    children: &'a BTreeMap<PathBuf, submodules::Source>,
}
fn copy_repository(
    actual: &mut Checkout,
    original: &Path,
    prefix: &Path,
    source: &submodules::Source,
    context: &Context<'_>,
    transfer: &mut Transfer<'_>,
    depth: usize,
) -> CargoResult<()> {
    let revision = locked_oid(source.id)?;
    copy_repository_inner(actual, original, prefix, source, context, transfer, depth)
        .with_context(|| crate::sources::git::source::object_source_context(source.id, revision))
}

fn copy_repository_inner(
    actual: &mut Checkout,
    original: &Path,
    prefix: &Path,
    source: &submodules::Source,
    context: &Context<'_>,
    transfer: &mut Transfer<'_>,
    depth: usize,
) -> CargoResult<()> {
    ensure!(
        depth < super::super::super::MAX_SOURCES,
        "checkout submodule nesting exceeds bound"
    );
    let ident = crate::sources::git::source::ident(&source.id);
    let database = context
        .databases
        .get(&ident)
        .context("selected checkout lost guarded source ODB")?;
    ensure!(
        database.representative.canonical_url() == source.id.canonical_url(),
        "checkout ODB source collision"
    );
    let revision = locked_oid(source.id)?;
    let tree = database.input.find_commit(revision)?.tree()?;
    let children = submodules::selected_with_paths(&database.input, revision, &source.parent_url)?
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    copy_tree(
        actual,
        &Walk {
            original,
            prefix,
            repository: &database.input,
            root: &tree,
            children: &children,
        },
        &tree,
        Path::new(""),
        context,
        transfer,
        depth,
    )?;
    // Fresh minimal metadata refers only to the SAME newly published cache's
    // guarded object DATA. No donor metadata, hooks or alternate is copied.
    let git = prefix.join(".git");
    // Native Git repository discovery requires refs even for a detached HEAD.
    // It is freshly created and contains no donor branches or tags.
    transfer.output.directory(&git.join("refs"))?;
    transfer.output.generated(
        &git.join("config"),
        b"[core]\nrepositoryformatversion = 0\nbare = false\nautocrlf = false\nfilemode = true\n",
        transfer.stats,
        transfer.budget,
    )?;
    transfer.output.generated(
        &git.join("HEAD"),
        format!("{revision}\n").as_bytes(),
        transfer.stats,
        transfer.budget,
    )?;
    let objects = context
        .destination
        .join("git/db")
        .join(ident)
        .join("objects");
    let objects = objects
        .to_str()
        .context("new checkout object locator must be UTF8")?;
    ensure!(
        !objects.contains(['\n', '\r']),
        "new checkout object locator contains a line separator"
    );
    transfer.output.generated(
        &git.join("objects/info/alternates"),
        format!("{objects}\n").as_bytes(),
        transfer.stats,
        transfer.budget,
    )?;
    let scratch = tempfile::tempdir()?;
    let index_path = scratch.path().join("index");
    let mut index = git2::Index::open(&index_path)?;
    index.read_tree(&tree)?;
    index.write()?;
    let mut index_file = File::open(&index_path)?;
    let len = index_file.metadata()?.len();
    transfer.output.copy(
        &git.join("index"),
        &mut index_file,
        len,
        transfer.stats,
        transfer.budget,
    )?;
    actual.check_current()?;
    // Trust: Cargo's completion marker belongs only to the outer checkout.
    // Generating it in submodules makes their Git worktrees dirty. Git-declared
    // files there remain ordinary source DATA, joined to their selected tree.
    // The marker grants no source, SDK, execution or native readiness authority.
    if depth == 0 {
        transfer.output.generated(
            &prefix.join(".cargo-ok"),
            b"",
            transfer.stats,
            transfer.budget,
        )?;
    }
    Ok(())
}

fn copy_tree(
    actual: &mut Checkout,
    walk: &Walk<'_>,
    tree: &git2::Tree<'_>,
    relative: &Path,
    context: &Context<'_>,
    transfer: &mut Transfer<'_>,
    depth: usize,
) -> CargoResult<()> {
    ensure!(
        relative.components().count() <= MAX_DEPTH,
        "selected checkout tree exceeds depth bound"
    );
    ensure!(
        actual.source.files.len() + actual.source.directories.len() < MAX_CHECKOUT_ENTRIES,
        "selected checkout entry bound exceeded"
    );
    let path = walk.original.join(relative);
    let directory = if path == actual.source.root.path {
        Directory {
            path,
            file: actual.source.root.file.try_clone()?,
            before: actual.source.root.before.clone(),
        }
    } else {
        let mut directory = None;
        actual.source.with_directory(
            path.parent().context("checkout parent unavailable")?,
            |parent| {
                directory =
                    Some(parent.child(path.file_name().context("checkout leaf unavailable")?)?);
                Ok(())
            },
        )?;
        directory.context("original checkout child unavailable")?
    };
    directory.current()?;
    actual
        .source
        .directories
        .insert(directory.path.clone(), directory.before.clone());
    let mut expected = std::collections::BTreeSet::new();
    for entry in tree {
        let name = OsString::from_vec(entry.name_bytes().to_vec());
        validate_checkout_name(&name, depth == 0 && relative.as_os_str().is_empty())
            .with_context(|| format!("selected checkout tree at {}", directory.path.display()))?;
        ensure!(
            expected.insert(name.clone()),
            "duplicate selected tree name"
        );
        let path = relative.join(&name);
        match entry.filemode() {
            0o040000 => {
                let subtree = walk.repository.find_tree(entry.id())?;
                copy_tree(actual, walk, &subtree, &path, context, transfer, depth)?;
            }
            0o100644 | 0o100755 => {
                let mut file = File::from(rustix::fs::openat(
                    &directory.file,
                    &name,
                    OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                    Mode::empty(),
                )?);
                let before = file.metadata()?;
                ensure!(
                    before.is_file()
                        && ((before.mode() & 0o111 != 0) == (entry.filemode() == 0o100755)),
                    "selected checkout file type/mode differs"
                );
                ensure!(
                    before.len() <= super::super::super::MAX_TOTAL_BYTES - transfer.stats.bytes,
                    "selected checkout DATA exceeds32GiB"
                );
                let mut hash = gix::hash::hasher(gix::hash::Kind::Sha1);
                hash.update(&gix::objs::encode::loose_header(
                    gix::objs::Kind::Blob,
                    before.len(),
                ));
                let mut buffer = vec![0; 64 * 1024];
                let mut remaining = before.len();
                while remaining != 0 {
                    let count = (remaining as usize).min(buffer.len());
                    file.read_exact(&mut buffer[..count])?;
                    hash.update(&buffer[..count]);
                    remaining -= count as u64;
                }
                ensure!(
                    file.read(&mut [0])? == 0
                        && hash.try_finalize()?.as_slice() == entry.id().as_bytes(),
                    "selected checkout file bytes differ from locked tree"
                );
                ensure!(
                    stamp(&before, &file.metadata()?),
                    "selected checkout file changed during hash"
                );
                file.rewind()?;
                transfer.output.copy_mode(
                    &walk.prefix.join(&path),
                    &mut file,
                    before.len(),
                    Some(if entry.filemode() == 0o100755 {
                        0o755
                    } else {
                        0o644
                    }),
                    transfer.stats,
                    transfer.budget,
                )?;
                ensure!(
                    stamp(&before, &file.metadata()?),
                    "selected checkout file changed during clone"
                );
                actual
                    .source
                    .files
                    .push((directory.path.join(&name), before));
            }
            0o120000 => {
                let blob = walk.repository.find_blob(entry.id())?;
                let target = blob.content();
                validate_link_target(walk.root, &path, target)?;
                let before = std::fs::symlink_metadata(directory.path.join(&name))?;
                ensure!(
                    before.file_type().is_symlink(),
                    "selected checkout link type differs"
                );
                let mut bytes = [0_u8; 4097];
                let len = rustix::fs::readlinkat_raw(&directory.file, &name, &mut bytes[..])?;
                ensure!(
                    len <= 4096 && &bytes[..len] == target,
                    "selected checkout link bytes differ from locked tree"
                );
                ensure!(
                    stamp(
                        &before,
                        &std::fs::symlink_metadata(directory.path.join(&name))?
                    ),
                    "selected checkout link changed during read"
                );
                directory.current()?;
                transfer.output.link(
                    &walk.prefix.join(&path),
                    target,
                    transfer.stats,
                    transfer.budget,
                )?;
                actual
                    .source
                    .files
                    .push((directory.path.join(&name), before));
            }
            0o160000 => {
                if let Some(child) = walk.children.get(&path) {
                    ensure!(
                        locked_oid(child.id)? == entry.id(),
                        "selected gitlink differs from recipe"
                    );
                    copy_repository(
                        actual,
                        &walk.original.join(&path),
                        &walk.prefix.join(&path),
                        child,
                        context,
                        transfer,
                        depth + 1,
                    )?;
                } else {
                    let child = directory.child(&name)?;
                    ensure!(
                        child.names()?.is_empty(),
                        "unselected submodule has materialized DATA"
                    );
                    actual
                        .source
                        .directories
                        .insert(child.path.clone(), child.before.clone());
                    transfer.output.directory(&walk.prefix.join(&path))?;
                }
            }
            _ => bail!(
                "unsupported selected checkout mode {:o}: {}",
                entry.filemode(),
                path.display()
            ),
        }
    }
    let mut names = directory
        .names()?
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>();
    if relative.as_os_str().is_empty() {
        names.remove(OsStr::new(".git"));
        if depth == 0 {
            names.remove(OsStr::new(".cargo-ok"));
        } else if !expected.contains(OsStr::new(".cargo-ok"))
            && names.contains(OsStr::new(".cargo-ok"))
        {
            // Trust: ordinary Cargo also created empty markers in submodule
            // donors. Observe that narrow metadata form, but never publish it
            // into a child worktree or treat it as selected source authority.
            observe_legacy_marker(actual, &directory)?;
            names.remove(OsStr::new(".cargo-ok"));
        }
    }
    ensure!(
        names == expected,
        "selected checkout has missing or additional working files"
    );
    directory.current()
}

/// The profile copies only exact Git-declared relative links to regular files
/// in this SAME selected repository. No donor target is opened or followed.
/// Parents must precede all normal components: otherwise an intermediate link
/// could change how `..` is resolved by the eventual filesystem consumer.
pub(super) fn validate_link_target(
    tree: &git2::Tree<'_>,
    link: &Path,
    target: &[u8],
) -> CargoResult<()> {
    ensure!(
        !target.is_empty() && target.len() <= 4096 && !target.contains(&0),
        "selected checkout link target exceeds closed bounds"
    );
    let mut path = link
        .parent()
        .context("selected link parent unavailable")?
        .to_owned();
    let mut normal = false;
    for component in target.split(|byte| *byte == b'/') {
        ensure!(
            !component.is_empty() && component != b".",
            "noncanonical selected link target"
        );
        if component == b".." {
            ensure!(
                !normal && path.pop(),
                "selected checkout link escapes its repository"
            );
        } else {
            normal = true;
            path.push(OsStr::from_bytes(component));
        }
    }
    let selected = tree
        .get_path(&path)
        .context("selected link target is not in the locked tree")?;
    ensure!(
        matches!(selected.filemode(), 0o100644 | 0o100755),
        "selected link must resolve directly to an in-repository regular file"
    );
    Ok(())
}

#[derive(Default)]
struct Forecast {
    entries: usize,
    bytes: u64,
    missing_bytes: u64,
}
fn forecast_repository(
    source: &submodules::Source,
    databases: &BTreeMap<String, Database>,
    forecast: &mut Forecast,
    missing: bool,
    depth: usize,
) -> CargoResult<()> {
    let revision = locked_oid(source.id)?;
    forecast_repository_inner(source, databases, forecast, missing, depth)
        .with_context(|| crate::sources::git::source::object_source_context(source.id, revision))
}

fn forecast_repository_inner(
    source: &submodules::Source,
    databases: &BTreeMap<String, Database>,
    forecast: &mut Forecast,
    missing: bool,
    depth: usize,
) -> CargoResult<()> {
    ensure!(
        depth < super::super::super::MAX_SOURCES,
        "checkout forecast submodule nesting exceeds bound"
    );
    let database = databases
        .get(&crate::sources::git::source::ident(&source.id))
        .context("checkout forecast lost actual ODB")?;
    let revision = locked_oid(source.id)?;
    let tree = database.input.find_commit(revision)?.tree()?;
    let odb = database.input.odb()?;
    forecast.entries = forecast
        .entries
        .checked_add(16)
        .context("checkout metadata entry overflow")?;
    let mut failure = None;
    tree.walk(git2::TreeWalkMode::PreOrder, |parent, entry| {
        let result = (|| -> CargoResult<()> {
            if !missing {
                validate_checkout_name(
                    OsStr::from_bytes(entry.name_bytes()),
                    depth == 0 && parent.is_empty(),
                )
                .with_context(|| format!("selected checkout forecast at {parent}"))?;
            }
            ensure!(
                Path::new(parent).components().count() < MAX_DEPTH,
                "checkout forecast namespace exceeds depth bound"
            );
            forecast.entries = forecast
                .entries
                .checked_add(1)
                .context("checkout forecast entry overflow")?;
            ensure!(
                forecast.entries <= MAX_CHECKOUT_ENTRIES,
                "selected checkout forecast exceeds expanded entry bound"
            );
            if matches!(entry.filemode(), 0o100644 | 0o100755 | 0o120000) {
                let (size, kind) = odb.read_header(entry.id())?;
                ensure!(
                    kind == git2::ObjectType::Blob,
                    "selected checkout forecast found non-blob file"
                );
                forecast.bytes = forecast
                    .bytes
                    .checked_add(size as u64)
                    .context("checkout forecast byte overflow")?;
                ensure!(
                    forecast.bytes <= super::super::super::MAX_TOTAL_BYTES,
                    "selected checkout forecast exceeds32GiB"
                );
                if missing {
                    forecast.missing_bytes = forecast
                        .missing_bytes
                        .checked_add(size as u64)
                        .context("missing checkout forecast overflow")?;
                }
            }
            Ok(())
        })();
        match result {
            Ok(()) => git2::TreeWalkResult::Ok,
            Err(error) => {
                failure = Some(error);
                git2::TreeWalkResult::Abort
            }
        }
    })
    .or_else(|error| {
        if failure.is_some() {
            Ok(())
        } else {
            Err(error)
        }
    })?;
    if let Some(error) = failure {
        return Err(error);
    }
    for child in submodules::selected(&database.input, revision, &source.parent_url)? {
        forecast_repository(&child, databases, forecast, missing, depth + 1)?;
    }
    Ok(())
}
