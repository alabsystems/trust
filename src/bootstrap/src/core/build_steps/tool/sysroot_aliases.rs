//! Trust: the compatibility-alias rule for an assembled sysroot `bin/` (docs/trust-naming.md:
//! `cargo` is the `targo` executable under a second name, not a second program).

use super::*;

/// Trust: what is wrong with the compatibility aliases in one sysroot `bin/`.
/// Empty when every tool there that has an alias also has that alias, as the
/// same bytes (docs/trust-naming.md: `cargo` is the `targo` executable under a
/// second name, not a second program). The tools that have one are whatever
/// `upstream_compat_bin_for_tool_source` says, so this reads no second table.
pub(crate) fn sysroot_compat_alias_problems(bindir: &Path, host: TargetSelection) -> Vec<String> {
    // Trust: opening or enumerating the directory is part of validation.
    // An unavailable directory or entry cannot establish alias completeness.
    let entries =
        fs::read_dir(bindir).map(|entries| entries.map(|entry| entry.map(|entry| entry.path())));
    inspect_sysroot_compat_aliases(bindir, host, entries)
}

pub(super) fn inspect_sysroot_compat_aliases(
    bindir: &Path,
    host: TargetSelection,
    entries: io::Result<impl Iterator<Item = io::Result<PathBuf>>>,
) -> Vec<String> {
    let mut problems = Vec::new();
    let mut tools = match entries.and_then(|entries| entries.collect::<io::Result<Vec<_>>>()) {
        Ok(tools) => tools,
        Err(error) => {
            return vec![format!(
                "cannot inspect sysroot bin directory `{}`: {error}",
                bindir.display()
            )];
        }
    };
    tools.sort();
    // The host's executable suffix, which is not the build machine's on a cross build.
    let suffix = exe("", host);
    for tool in tools {
        let Some(name) = tool
            .file_name()
            .and_then(OsStr::to_str)
            .and_then(|file_name| file_name.strip_suffix(suffix.as_str()))
        else {
            continue;
        };
        let Some(compat_name) = upstream_compat_bin_for_tool_source(name) else {
            continue;
        };
        // Trust: inspect a recognized source instead of silently excluding an
        // unreadable, broken or non-file tool from the completeness check.
        match fs::metadata(&tool) {
            Ok(metadata) if metadata.is_file() => {}
            Ok(_) => {
                problems.push(format!("installed tool `{}` is not a regular file", tool.display()));
                continue;
            }
            Err(error) => {
                problems
                    .push(format!("cannot inspect installed tool `{}`: {error}", tool.display()));
                continue;
            }
        }
        let alias = bindir.join(exe(compat_name, host));
        if !alias.is_file() {
            problems.push(format!(
                "`{}` is installed without its compatibility alias `{}`",
                tool.display(),
                alias.display()
            ));
            continue;
        }
        match files_have_same_bytes(&tool, &alias) {
            Ok(true) => {}
            Ok(false) => problems.push(format!(
                "compatibility alias `{}` is not the same bytes as `{}`",
                alias.display(),
                tool.display()
            )),
            Err(error) => problems.push(format!(
                "cannot compare `{}` with its compatibility alias `{}`: {error}",
                tool.display(),
                alias.display()
            )),
        }
    }
    problems
}

// Trust: `copy_link` hard-links where it can, so the usual answer is one inode
// and no read; a copied alias (another filesystem) is compared by content.
fn files_have_same_bytes(left: &Path, right: &Path) -> io::Result<bool> {
    use std::io::Read as _;

    let left_metadata = fs::metadata(left)?;
    let right_metadata = fs::metadata(right)?;
    if left_metadata.len() != right_metadata.len() {
        return Ok(false);
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if left_metadata.dev() == right_metadata.dev()
            && left_metadata.ino() == right_metadata.ino()
        {
            return Ok(true);
        }
    }
    let mut left_file = io::BufReader::new(fs::File::open(left)?);
    let mut right_file = io::BufReader::new(fs::File::open(right)?);
    let mut left_chunk = vec![0u8; 1 << 16];
    let mut right_chunk = vec![0u8; 1 << 16];
    loop {
        let read = left_file.read(&mut left_chunk)?;
        if read == 0 {
            return Ok(true);
        }
        right_file.read_exact(&mut right_chunk[..read])?;
        if left_chunk[..read] != right_chunk[..read] {
            return Ok(false);
        }
    }
}

/// Trust: refuse to finish assembling a sysroot whose frontends lack a
/// compatibility alias, so the next build that installs `targo` without
/// `cargo` stops here, on every host, rather than hours later at admission or
/// promotion (see `sysroot_bin_names_for_tool_source`).
pub(crate) fn validate_sysroot_compat_aliases(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    sysroot: &Path,
) {
    if builder.config.dry_run() {
        return;
    }
    let problems = sysroot_compat_alias_problems(&sysroot.join("bin"), target_compiler.host);
    assert!(
        problems.is_empty(),
        "assembled stage{} sysroot `{}` breaks the compatibility-alias rule: {}",
        target_compiler.stage,
        sysroot.display(),
        problems.join("; ")
    );
}
