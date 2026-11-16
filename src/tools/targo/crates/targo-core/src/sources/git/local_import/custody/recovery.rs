//! Trust: recover an absent database from original exact checkout object DATA.
//! No checkout/ref/config is changed. This uses the caller's actual download
//! exclusion, original source bookends and the existing guarded copy/hash walk.

use super::super::{Database, Stats, inspect_closure_scope, pack_stream};
use super::*;
use crate::util::GlobalContext;
use crate::util::cache_lock::CacheLockMode;
use crate::util::data_structures::HashMap;
use crate::workspace::{GitReference, SourceId};
use std::ffi::CString;
use std::os::unix::ffi::OsStrExt as _;

pub(in crate::sources::git) fn recover_missing_database(
    gctx: &GlobalContext,
    source: SourceId,
    revision: git2::Oid,
    ident: &str,
    destination: &Path,
) -> CargoResult<()> {
    // A branch/tag's saved precise OID does not authorize skipping its normal
    // refresh. Existing (including damaged) databases keep their normal path.
    let full = revision.to_string();
    if !matches!(source.git_reference(), Some(GitReference::Rev(value)) if value == &full) {
        return Ok(());
    }
    if ident != crate::sources::git::source::ident(&source) {
        return Ok(()); // The separately named shallow profile keeps its normal path.
    }
    match std::fs::symlink_metadata(destination) {
        Ok(_) => return Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    let git = gctx.git_path();
    gctx.assert_package_cache_locked(CacheLockMode::DownloadExclusive, &git);
    ensure!(
        destination == gctx.git_db_path().join(ident).as_path_unlocked(),
        "checkout recovery requires the canonical database destination"
    );
    let path = gctx.git_checkouts_path().join(ident).into_path_unlocked();
    match std::fs::symlink_metadata(&path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error.into()),
        Ok(_) => {}
    }
    recover(gctx, source, revision, &path, destination).context(
        "exact checkout database recovery refused; ordinary source authority was not changed",
    )
}

fn recover(
    gctx: &GlobalContext,
    source: SourceId,
    revision: git2::Oid,
    checkouts: &Path,
    destination: &Path,
) -> CargoResult<()> {
    ensure!(
        checkouts.canonicalize()? == checkouts,
        "noncanonical checkout source namespace"
    );
    let originals = Directory::open(checkouts)?;
    let full = revision.to_string();
    let candidates = originals
        .names()?
        .into_iter()
        .filter(|name| {
            name.to_str()
                .is_some_and(|name| (7..=40).contains(&name.len()) && full.starts_with(name))
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return Ok(()); // No exact candidate: preserve ordinary network/offline behavior.
    }
    ensure!(
        candidates.len() == 1,
        "ambiguous exact checkout recovery candidates"
    );
    let original = originals.child(&candidates[0])?;
    let objects = original.path.join(".git/objects");
    let checkout = snapshot::capture_original_checkout(original, revision, true)?;
    let source_objects = ObjectSource::capture_objects(&objects)?;
    require_local_filesystem(&source_objects.root.file)?;

    let parent_path = destination
        .parent()
        .context("database parent unavailable")?;
    let (ancestors, parent, created_parent) = database_parent(parent_path)?;
    let leaf = destination
        .file_name()
        .context("database name unavailable")?;
    ensure!(
        parent.missing_relative(Path::new(leaf))?,
        "database appeared before recovery staging"
    );
    let name = format!(
        ".targo-checkout-recovery-{:032x}.noindex",
        rand::random::<u128>()
    );
    parent.current()?;
    // Unlike a whole-home import, the normal existing db directory may be0755.
    // It is owner-controlled, ACL-checked and under the actual download lock;
    // only this freshly created0700 namespace permits mutation below it.
    rustix::fs::mkdirat(&parent.file, name.as_str(), Mode::from_bits_truncate(0o700))?;
    let container = parent.child(OsStr::new(&name))?;
    container.private_current()?;
    let mut published = false;
    let result = (|| {
        let repository = container.create_child(OsStr::new("repository"))?;
        let mut view = OwnedView::create(&repository, OsStr::new("objects"))?;
        let mut options = git2::RepositoryInitOptions::new();
        options
            .bare(true)
            .external_template(false)
            .initial_head("master");
        let output = git2::Repository::init_opts(&repository.path, &options)?;
        output.set_config(&git2::Config::new()?)?;
        let mut budget = CopyBudget::new(super::super::MAX_TOTAL_BYTES)?;
        source_objects.materialize_view(
            &objects,
            &mut view,
            super::super::MAX_TOTAL_BYTES,
            &mut budget,
        )?;
        let odb = git2::Odb::new()?;
        odb.add_disk_alternate(
            view.path()
                .to_str()
                .context("private recovery view must be UTF8")?,
        )?;
        let input = git2::Repository::from_odb(odb)?;
        ensure!(
            crate::sources::git::utils::checkout_short_id(&input.odb()?, revision)?.as_str()
                == candidates[0]
                    .to_str()
                    .context("checkout name must be UTF8")?,
            "checkout recovery name does not match the actual original object inventory"
        );
        let mut database = Database {
            representative: source,
            input,
            output: None,
            view,
            original: source_objects,
            copied: HashMap::default(),
        };
        inspect_closure_scope(
            &mut database,
            revision,
            &mut Stats::default(),
            &mut pack_stream::ReadBudget::default(),
            false,
        )?;
        output.reference(
            &format!("refs/commit/{revision}"),
            revision,
            false,
            "exact checkout source DATA recovery",
        )?;
        database.original.check_current()?;
        database.view.check_current()?;
        checkout.check_current()?;
        originals.current()?;
        check_parent(&ancestors, &parent)?;
        repository.file.sync_all()?;
        container.file.sync_all()?;
        let from = CString::new("repository")?;
        let to = CString::new(leaf.as_bytes())?;
        #[cfg(target_os = "macos")]
        // SAFETY: both original directory descriptions and NUL-terminated
        // names remain live; the kernel retains none and refuses replacement.
        let renamed = unsafe {
            libc::renameatx_np(
                container.file.as_raw_fd(),
                from.as_ptr(),
                parent.file.as_raw_fd(),
                to.as_ptr(),
                libc::RENAME_EXCL,
            )
        };
        #[cfg(target_os = "linux")]
        // SAFETY: same held-directory/name lifetime and no-replace contract.
        let renamed = unsafe {
            libc::renameat2(
                container.file.as_raw_fd(),
                from.as_ptr(),
                parent.file.as_raw_fd(),
                to.as_ptr(),
                libc::RENAME_NOREPLACE,
            )
        };
        ensure!(
            renamed == 0,
            "database recovery publication refused: {}",
            std::io::Error::last_os_error()
        );
        published = true;
        // Publication is the commit point; never roll it back or describe a
        // later observation/durability error as an absent database.
        (|| {
            database.original.check_current()?;
            checkout.check_current()?;
            originals.current()?;
            check_parent(&ancestors, &parent)?;
            parent.file.sync_all()?;
            Ok::<_, anyhow::Error>(())
        })().context("database recovery published; post-commit observation/durability failed, no rollback attempted")?;
        gctx.shell().status(
            "Recovered",
            format!("exact Git database {revision} from retained checkout DATA (database directory created: {created_parent})"),
        )?;
        Ok::<_, anyhow::Error>(())
    })();
    // Keep any failed private stage for inspection, never path-only adoption.
    if result.is_ok() {
        (|| {
            container.private_current()?;
            rustix::fs::unlinkat(&parent.file, name.as_str(), AtFlags::REMOVEDIR)?;
            Ok::<_, anyhow::Error>(())
        })()
        .context(
            "database recovery published; empty staging cleanup failed, no rollback attempted",
        )?;
    }
    let result = if published {
        result.context("database recovery published; completion failed, no rollback attempted")
    } else {
        result
    };
    result.with_context(|| {
        format!(
            "original recovery staging namespace: {}",
            container.path.display()
        )
    })
}

fn database_parent(path: &Path) -> CargoResult<(Vec<Directory>, Directory, bool)> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => {
            let (ancestors, parent) = cache_parent(path)?;
            return Ok((ancestors, parent, false));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    // The ordinary source owner already created git/, but cache reclamation
    // may remove db/ in its entirety. Create only that single absent child;
    // never follow/reuse a raced creation or manufacture a directory chain.
    ensure!(
        path.file_name() == Some(OsStr::new("db")),
        "unsupported missing database parent"
    );
    let (mut ancestors, git) = cache_parent(path.parent().context("Git cache root unavailable")?)?;
    git.current()?;
    rustix::fs::mkdirat(&git.file, "db", Mode::from_bits_truncate(0o700))?;
    let parent = git.child(OsStr::new("db"))?;
    parent.private_current()?;
    git.same_identity()?;
    ancestors.push(git);
    check_parent(&ancestors, &parent)?;
    require_local_filesystem(&parent.file)?;
    Ok((ancestors, parent, true))
}

fn cache_parent(path: &Path) -> CargoResult<(Vec<Directory>, Directory)> {
    ensure!(path.canonicalize()? == path, "noncanonical database parent");
    let mut ancestors = Vec::new();
    let mut directory = Directory::open(Path::new("/"))?;
    for part in path.components() {
        match part {
            std::path::Component::RootDir => {}
            std::path::Component::Normal(name) => {
                let child = directory.child(name)?;
                ancestor_security(&directory, Some(&child))?;
                ancestors.push(directory);
                directory = child;
            }
            _ => bail!("noncanonical database parent component"),
        }
    }
    check_parent(&ancestors, &directory)?;
    require_local_filesystem(&directory.file)?;
    Ok((ancestors, directory))
}

fn check_parent(ancestors: &[Directory], parent: &Directory) -> CargoResult<()> {
    for (index, directory) in ancestors.iter().enumerate() {
        ancestor_security(directory, Some(ancestors.get(index + 1).unwrap_or(parent)))?;
    }
    ancestor_security(parent, None)?;
    let metadata = parent.file.metadata()?;
    ensure!(
        metadata.uid() == unsafe { libc::geteuid() } && metadata.mode() & 0o022 == 0,
        "checkout recovery requires an owner-controlled database parent"
    );
    Ok(())
}
