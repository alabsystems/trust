//! Bounded namespace checks for revision readback, without extracting an archive.
//!
//! Source distributions contain symlinks (licenses and test fixtures). They may
//! be leaves, but no archive member may be written through one, in either tar
//! order or through a case alias. Link targets stay inside the package and cannot
//! traverse another link, alias the revision, or name the package root. Hardlinks
//! remain unsupported. These checks establish identity, not source correctness.
use std::collections::BTreeMap;

// Bound retained names independently of the streamed file-content budget. This
// includes implicit parent directories, avoiding a many-deep-path memory bomb.
const MAX_NAMESPACE_BYTES: usize = 256 * 1024 * 1024;
const MAX_NAMESPACE_NODES: usize = 1_000_000;

#[derive(Default)]
struct Node {
    member: bool,
    descendants: bool,
    link: Option<Vec<u8>>,
}

pub(super) struct Namespace {
    package: Vec<u8>,
    revision: Vec<u8>,
    nodes: BTreeMap<Vec<u8>, Node>,
    bytes: usize,
}

impl Namespace {
    pub(super) fn new(package: &str) -> Self {
        Self {
            package: package.as_bytes().to_vec(),
            revision: format!("{package}/git-commit-hash").into_bytes().to_ascii_lowercase(),
            nodes: BTreeMap::new(),
            bytes: 0,
        }
    }

    fn reserve_bytes(&mut self, bytes: usize) -> Result<(), String> {
        self.bytes = self.bytes.checked_add(bytes).ok_or("source archive namespace overflow")?;
        if self.bytes > MAX_NAMESPACE_BYTES {
            return Err("source archive namespace exceeds its byte bound".into());
        }
        Ok(())
    }

    pub(super) fn register(
        &mut self,
        path: &[u8],
        kind: tar::EntryType,
        target: Option<&[u8]>,
        size: u64,
    ) -> Result<(), String> {
        if !matches!(
            kind,
            tar::EntryType::Regular | tar::EntryType::Directory | tar::EntryType::Symlink
        ) {
            return Err("source archive link or special member type is unsupported".into());
        }
        let path = if kind == tar::EntryType::Directory {
            path.strip_suffix(b"/").unwrap_or(path)
        } else {
            path
        };
        let parts: Vec<_> = path.split(|byte| *byte == b'/').collect();
        if parts.first().copied() != Some(self.package.as_slice())
            || parts.iter().any(|p| p.is_empty() || *p == b"." || *p == b"..")
            || path.contains(&b'\\')
            || path.contains(&0)
        {
            return Err("source archive member has an ambiguous extraction path".into());
        }
        if parts.len() == 1 && kind != tar::EntryType::Directory {
            return Err("source archive package root must be a directory".into());
        }
        if kind != tar::EntryType::Regular && size != 0 {
            return Err("source archive non-file member has data".into());
        }
        let target = if kind == tar::EntryType::Symlink {
            let target = target
                .filter(|t| {
                    !t.is_empty() && t.len() as u64 <= super::MAX_SOURCE_ARCHIVE_LONGNAME_BYTES
                })
                .ok_or("source archive symlink has a missing or oversized target")?;
            self.reserve_bytes(target.len())?;
            Some(target.to_vec())
        } else {
            None
        };
        let mut key = Vec::new();
        for (i, part) in parts.iter().enumerate() {
            if i != 0 {
                key.push(b'/');
            }
            key.extend(part.to_ascii_lowercase());
            if !self.nodes.contains_key(&key) {
                if self.nodes.len() >= MAX_NAMESPACE_NODES {
                    return Err("source archive namespace exceeds its node bound".into());
                }
                self.reserve_bytes(key.len())?;
                self.nodes.insert(key.clone(), Node::default());
            }
            let node = self.nodes.get_mut(&key).expect("registered namespace node");
            if node.link.is_some() {
                return Err("source archive member aliases or traverses a symlink".into());
            }
            if i + 1 == parts.len() {
                if target.is_some() && (node.member || node.descendants) {
                    return Err(
                        "source archive symlink aliases a member or member directory".into()
                    );
                }
                node.member = true;
                node.link = target.clone();
            } else {
                node.descendants = true;
            }
        }
        Ok(())
    }

    pub(super) fn finish(&self) -> Result<(), String> {
        for (path, node) in &self.nodes {
            let Some(target) = &node.link else { continue };
            if target.starts_with(b"/") || target.contains(&b'\\') || target.contains(&0) {
                return Err("source archive symlink target escapes or aliases the package".into());
            }
            let mut parts: Vec<_> = path.split(|b| *b == b'/').map(<[u8]>::to_vec).collect();
            parts.pop();
            for part in target.split(|b| *b == b'/') {
                match part {
                    b"" | b"." => {}
                    b".." => {
                        if parts.len() <= 1 {
                            return Err("source archive symlink target escapes the package".into());
                        }
                        parts.pop();
                    }
                    _ => parts.push(part.to_ascii_lowercase()),
                }
                let resolved = parts.join(&b'/');
                if resolved == self.revision
                    || self.nodes.get(&resolved).is_some_and(|n| n.link.is_some())
                {
                    return Err(
                        "source archive symlink target aliases the revision or another link".into(),
                    );
                }
            }
            if parts.len() <= 1 {
                return Err("source archive symlink target aliases the package root".into());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::super::source_tarball_archive_identity;
    use super::*;

    const PACKAGE: &str = "trust-src-fixture";
    const COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";

    fn archive_identity(
        entries: &[(String, tar::EntryType, &str)],
    ) -> Result<(String, String), String> {
        let temp = tempfile::tempdir().unwrap();
        let archive = temp.path().join(format!("{PACKAGE}.tar.xz"));
        let encoder = xz2::write::XzEncoder::new(fs::File::create(&archive).unwrap(), 6);
        let mut builder = tar::Builder::new(encoder);
        for (name, kind, target) in entries {
            let mut header = tar::Header::new_gnu();
            header.set_entry_type(*kind);
            header.set_mode(0o755);
            let bytes: &[u8] =
                if *kind == tar::EntryType::Regular { COMMIT.as_bytes() } else { &[] };
            header.set_size(bytes.len() as u64);
            if *kind == tar::EntryType::Symlink || *kind == tar::EntryType::Link {
                header.set_link_name(target).unwrap();
            }
            builder.append_data(&mut header, format!("{PACKAGE}/{name}"), bytes).unwrap();
        }
        builder.into_inner().unwrap().finish().unwrap();
        let result = source_tarball_archive_identity(&archive);
        if let Ok((digest, _)) = &result {
            assert_eq!(Some(digest.clone()), super::super::file_sha256(&archive));
        }
        result
    }

    fn revision() -> (String, tar::EntryType, &'static str) {
        ("git-commit-hash".into(), tar::EntryType::Regular, "")
    }

    #[test]
    fn maintained_source_license_and_fixture_symlinks_are_bound() {
        use tar::EntryType::{Directory, Regular, Symlink};
        let long_link = format!("src/{}/LICENSE", "a".repeat(110));
        let entries = [
            revision(),
            ("src/LICENSE".into(), Regular, ""),
            ("src/crate/LICENSE".into(), Symlink, "../LICENSE"),
            ("src/empty_dir".into(), Directory, ""),
            ("src/case/in".into(), Symlink, "../empty_dir/"),
            ("src/test/dangling".into(), Symlink, "missing-input"),
            (long_link, Symlink, "../LICENSE"),
            (format!("src/{}/source.rs", "b".repeat(110)), Regular, ""),
        ];
        for entries in [entries.to_vec(), entries.into_iter().rev().collect()] {
            let (_, commit) = archive_identity(&entries).expect("ordinary source links");
            assert_eq!(commit, COMMIT);
        }
    }

    #[test]
    fn writes_through_symlinks_fail_in_both_orders_and_case_aliases() {
        use tar::EntryType::{Regular, Symlink};
        for (link, member) in [
            ("src/alias".into(), "src/alias/git-commit-hash".into()),
            ("src/alias".into(), "src/ALIAS/child.rs".into()),
            (
                format!("src/{}/alias", "a".repeat(110)),
                format!("src/{}/alias/child.rs", "a".repeat(110)),
            ),
        ] {
            for reverse in [false, true] {
                let mut entries = vec![
                    revision(),
                    (link.clone(), Symlink, "../elsewhere"),
                    (member.clone(), Regular, ""),
                ];
                if reverse {
                    entries.reverse();
                }
                let error =
                    archive_identity(&entries).expect_err("a symlink cannot redirect a member");
                assert!(error.contains("symlink"), "{error}");
            }
        }
    }

    #[test]
    fn symlink_targets_cannot_escape_alias_revision_or_follow_links() {
        use tar::EntryType::Symlink;
        for target in [
            "/tmp/out",
            "../../out",
            "../git-commit-hash",
            "../GIT-COMMIT-HASH",
            "..",
            "other",
            "other/../file",
            "alias",
            "dir\\file",
        ] {
            let error = archive_identity(&[
                revision(),
                ("src/alias".into(), Symlink, target),
                ("src/other".into(), Symlink, "file"),
            ])
            .expect_err(target);
            assert!(error.contains("symlink"), "{target}: {error}");
        }
    }

    #[test]
    fn links_cannot_replace_files_directories_or_each_other() {
        use tar::EntryType::{Directory, Regular, Symlink};
        for kind in [Regular, Directory, Symlink] {
            for reverse in [false, true] {
                let mut entries = vec![
                    revision(),
                    ("src/member".into(), kind, "file"),
                    ("src/MEMBER".into(), Symlink, "file"),
                ];
                if reverse {
                    entries.reverse();
                }
                archive_identity(&entries).expect_err("link overwrite ambiguity");
            }
        }
    }

    #[test]
    fn namespace_metadata_is_bounded_separately_from_file_data() {
        let mut namespace = Namespace::new(PACKAGE);
        namespace.bytes = MAX_NAMESPACE_BYTES;
        assert!(
            namespace
                .register(b"trust-src-fixture/file", tar::EntryType::Regular, None, 0)
                .unwrap_err()
                .contains("byte bound")
        );
        let mut namespace = Namespace::new(PACKAGE);
        namespace.bytes = usize::MAX;
        assert!(
            namespace
                .register(b"trust-src-fixture/link", tar::EntryType::Symlink, Some(b"file"), 0)
                .unwrap_err()
                .contains("overflow")
        );
    }

    #[test]
    fn package_root_and_non_file_payloads_cannot_redirect_identity() {
        let mut namespace = Namespace::new(PACKAGE);
        assert!(
            namespace
                .register(PACKAGE.as_bytes(), tar::EntryType::Symlink, Some(b"other"), 0)
                .is_err()
        );
        assert!(
            namespace
                .register(b"trust-src-fixture/link", tar::EntryType::Symlink, Some(b"other"), 40)
                .is_err()
        );
        assert!(namespace.register(b"other-root/file", tar::EntryType::Regular, None, 0).is_err());
    }
}
