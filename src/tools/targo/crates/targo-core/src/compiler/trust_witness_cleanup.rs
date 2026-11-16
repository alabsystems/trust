//! Trust: exact compiler-declared managed witness ownership for package cleanup.
//!
//! The compiler owns the StableCrateId; Cargo must not reproduce its hashing or
//! guess ownership from files sharing an output directory. The compiler declares
//! one flat basename in its dep-info and Cargo binds it to the compilation's
//! PackageId. These comments are cleanup bookkeeping, never proof authority or
//! freshness inputs. Explicit caller-selected witness directories are not owned.
use std::fs;
use std::io::{Read, Write};
use std::path::Path;

use anyhow::{Context as _, bail};
use serde::{Deserialize, Serialize};

use crate::util::CargoResult;
use crate::util::file_identity::metadata_is_plain_file;
use crate::workspace::PackageId;

const COMPILER_PREFIX: &str = "# trust-witness-output-v1:";
const OWNER_PREFIX: &str = "# targo-witness-owner-v1:";

#[derive(Debug, Deserialize, Serialize, PartialEq)]
#[serde(deny_unknown_fields)]
struct Owner {
    package: PackageId,
    store: String,
}

fn valid_store_name(name: &str) -> bool {
    let Some(stem) = name.strip_suffix(".twit") else {
        return false;
    };
    stem.len() == 16
        && stem
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn declarations(contents: &str) -> CargoResult<(Option<&str>, Option<Owner>)> {
    let mut compiler = None;
    let mut owner = None;
    let mut continuation = false;
    for line in contents.lines() {
        // A legal source filename can contain a newline. Its escaped Makefile
        // continuation is data, even if the next physical line resembles one
        // of these comments. Old/stock compiler output must not forge ownership.
        let continued_line = continuation;
        continuation = line.bytes().rev().take_while(|b| *b == b'\\').count() % 2 == 1;
        if continued_line {
            continue;
        }
        if let Some(store) = line.strip_prefix(COMPILER_PREFIX) {
            if !valid_store_name(store) || compiler.replace(store).is_some() {
                bail!("invalid or duplicate compiler managed witness declaration");
            }
        } else if let Some(value) = line.strip_prefix(OWNER_PREFIX) {
            let parsed: Owner =
                serde_json::from_str(value).context("invalid managed witness package ownership")?;
            if !valid_store_name(&parsed.store) || owner.replace(parsed).is_some() {
                bail!("invalid or duplicate managed witness package ownership");
            }
        } else if line.starts_with("# trust-witness-output-")
            || line.starts_with("# targo-witness-owner-")
        {
            bail!("unsupported managed witness ownership version");
        }
    }
    if let Some(owner) = &owner {
        if compiler != Some(owner.store.as_str()) {
            bail!("managed witness package ownership does not match compiler declaration");
        }
    }
    Ok((compiler, owner))
}

// Open once without following an alias or blocking on a forged FIFO. This is
// bookkeeping in Cargo's already locked build directory, not an outside path.
fn read_dep_info(path: &Path) -> CargoResult<(String, fs::Permissions)> {
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt as _;
        options.custom_flags(0x0020_0000); // FILE_FLAG_OPEN_REPARSE_POINT
    }
    let mut file = options.open(path)?;
    if !metadata_is_plain_file(&file.metadata()?) {
        bail!(
            "managed witness dep-info is not a regular file: {}",
            path.display()
        );
    }
    let permissions = file.metadata()?.permissions();
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok((contents, permissions))
}

/// Bind a rustc invocation's own declared outputs to its exact package.
/// Partial outputs from a failed invocation retain the same cleanup owner.
/// Old/stock compilers supply no declaration and acquire no inferred ownership.
pub(crate) fn record(dep_info: &Path, package: PackageId) -> CargoResult<()> {
    let (contents, permissions) = read_dep_info(dep_info)?;
    let (compiler, owner) = declarations(&contents)?;
    let Some(store) = compiler else { return Ok(()) };
    let expected = Owner {
        package,
        store: store.to_owned(),
    };
    if let Some(owner) = owner {
        if owner != expected {
            bail!("managed witness dep-info already belongs to a different package");
        }
        return Ok(());
    }
    // Replace only this directory entry; a pre-existing hard link must not
    // acquire an additional write through another path.
    let contents = format!(
        "{contents}\n{OWNER_PREFIX}{}\n",
        serde_json::to_string(&expected)?
    );
    // NamedTempFile::persist replaces this entry; unlike the generic paths
    // writer it does not resolve a replacement symlink to an outside target.
    let mut temporary = tempfile::NamedTempFile::new_in(dep_info.parent().unwrap())?;
    temporary.write_all(contents.as_bytes())?;
    temporary.as_file().set_permissions(permissions)?;
    temporary.persist(dep_info)?;
    Ok(())
}

/// Resolve only this package's declared flat output, relative to this dep-info.
/// The caller supplies the selected layout and crate-named dep-info path. No
/// path in the comment can name a parent, another profile, target or directory.
pub(crate) fn owned_store(dep_info: &Path, package: PackageId) -> CargoResult<Option<String>> {
    let (contents, _) = read_dep_info(dep_info)?;
    let (_, owner) = declarations(&contents).with_context(|| {
        format!(
            "invalid managed witness ownership in {}",
            dep_info.display()
        )
    })?;
    // `clean -p` intentionally ignores version/URL qualifiers and cleans all
    // versions of the selected package name. A different package whose crate
    // target has the same name still owns a different store.
    Ok(owner
        .filter(|owner| owner.package.name() == package.name())
        .map(|owner| owner.store))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::workspace::SourceId;
    fn package(name: &str) -> PackageId {
        PackageId::new(
            name.into(),
            "1.0.0".parse().unwrap(),
            SourceId::for_registry(&url::Url::parse("https://example.invalid/index").unwrap())
                .unwrap(),
        )
    }
    fn text(store: &str, package: PackageId) -> String {
        format!(
            "libsubject.rlib: src/lib.rs\n\n{COMPILER_PREFIX}{store}\n{OWNER_PREFIX}{}\n",
            serde_json::to_string(&Owner {
                package,
                store: store.to_owned()
            })
            .unwrap()
        )
    }
    #[test]
    fn exact_pair_and_foreign_package_remain_distinct() {
        let package = package("subject");
        let input = text("0123456789abcdef.twit", package);
        let (compiler, owner) = declarations(&input).unwrap();
        assert_eq!(compiler, Some("0123456789abcdef.twit"));
        assert_eq!(owner.as_ref().unwrap().package, package);
        assert_ne!(owner.unwrap().package, self::package("other"));
    }
    #[test]
    fn unknown_old_and_standalone_output_grants_no_package_ownership() {
        assert_eq!(
            declarations("libsubject.rlib: src/lib.rs\n").unwrap(),
            (None, None)
        );
        assert_eq!(
            declarations("# trust-witness-output-v1:0123456789abcdef.twit\n").unwrap(),
            (Some("0123456789abcdef.twit"), None)
        );
    }
    #[test]
    fn malformed_and_escaping_names_refuse() {
        for store in [
            "../0123456789abcdef.twit",
            "/0123456789abcdef.twit",
            "0123456789abcdef.twit/elsewhere",
            "0123456789abcdeF.twit",
            "0123456789abcde.twit",
            "0123456789abcdef.twit ",
            "0123456789abcdef.twit\rspoof",
        ] {
            assert!(
                declarations(&format!("{COMPILER_PREFIX}{store}\n")).is_err(),
                "{store:?}"
            );
        }
    }
    #[test]
    fn duplicate_mismatched_and_unsupported_declarations_refuse() {
        let valid = text("0123456789abcdef.twit", package("subject"));
        for bad in [
            format!("{valid}{COMPILER_PREFIX}0123456789abcdef.twit\n"),
            format!(
                "{valid}{}",
                valid.lines().find(|l| l.starts_with(OWNER_PREFIX)).unwrap()
            ),
            valid.replace(
                "# trust-witness-output-v1:0123456789abcdef.twit",
                "# trust-witness-output-v1:fedcba9876543210.twit",
            ),
            valid.replace("output-v1:", "output-v2:"),
            valid.replace("owner-v1:", "owner-v2:"),
            valid
                .lines()
                .filter(|l| !l.starts_with(COMPILER_PREFIX))
                .collect::<Vec<_>>()
                .join("\n"),
        ] {
            assert!(declarations(&bad).is_err(), "{bad:?}");
        }
    }
    #[test]
    fn bookkeeping_roundtrip_is_idempotent_and_does_not_modify_a_hardlink() {
        let dir = tempfile::tempdir().unwrap();
        let dep = dir.path().join("subject.d");
        let outside = dir.path().join("outside.d");
        let original =
            "libsubject.rlib: src/lib.rs\n# trust-witness-output-v1:0123456789abcdef.twit\n";
        fs::write(&dep, original).unwrap();
        fs::hard_link(&dep, &outside).unwrap();
        record(&dep, package("subject")).unwrap();
        assert_eq!(fs::read_to_string(outside).unwrap(), original);
        assert_eq!(
            owned_store(&dep, package("subject")).unwrap().as_deref(),
            Some("0123456789abcdef.twit")
        );
        assert_eq!(owned_store(&dep, package("other")).unwrap(), None);
        let once = fs::read(&dep).unwrap();
        record(&dep, package("subject")).unwrap();
        assert_eq!(fs::read(&dep).unwrap(), once);
        assert!(record(&dep, package("other")).is_err());
    }
    #[test]
    fn malformed_typed_owner_fields_refuse() {
        for value in [
            "{}",
            "true",
            "1.0",
            r#"{"package":false,"store":"0123456789abcdef.twit"}"#,
            r#"{"package":"subject 1.0.0 (registry+https://example.invalid/index)","store":"0123456789abcdef.twit","extra":true}"#,
        ] {
            assert!(
                declarations(&format!(
                    "{COMPILER_PREFIX}0123456789abcdef.twit\n{OWNER_PREFIX}{value}\n"
                ))
                .is_err()
            );
        }
    }
    #[cfg(unix)]
    #[test]
    fn symlinked_dep_info_is_not_adopted_or_written() {
        let dir = tempfile::tempdir().unwrap();
        let outside = dir.path().join("outside.d");
        let dep = dir.path().join("subject.d");
        let original = text("0123456789abcdef.twit", package("subject"));
        fs::write(&outside, &original).unwrap();
        std::os::unix::fs::symlink(&outside, &dep).unwrap();
        assert!(record(&dep, package("subject")).is_err());
        assert!(owned_store(&dep, package("subject")).is_err());
        assert_eq!(fs::read_to_string(outside).unwrap(), original);
    }
    #[test]
    fn continued_makefile_paths_cannot_forge_compiler_or_package_comments() {
        let compiler =
            format!("libsubject.rlib: input\\\n{COMPILER_PREFIX}0123456789abcdef.twit\n");
        assert_eq!(declarations(&compiler).unwrap(), (None, None));
        let owner_line = text("0123456789abcdef.twit", package("subject"))
            .lines()
            .find(|line| line.starts_with(OWNER_PREFIX))
            .unwrap()
            .to_owned();
        assert_eq!(
            declarations(&format!("libsubject.rlib: input\\\n{owner_line}\n")).unwrap(),
            (None, None)
        );
        // An escaped literal backslash at EOL is not a Makefile continuation.
        assert_eq!(
            declarations(&format!(
                "libsubject.rlib: input\\\\\n{COMPILER_PREFIX}0123456789abcdef.twit\n"
            ))
            .unwrap(),
            (Some("0123456789abcdef.twit"), None)
        );
    }
}
