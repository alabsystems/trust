// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

#[test]
fn exact_target_path_parser_preserves_spaces_and_refuses_ambiguous_output() {
    assert_eq!(target_directory(b"/root/library \n").unwrap(), PathBuf::from("/root/library "));
    for output in [
        b"".as_slice(),
        b"/root/lib",
        b"/root/library\r\n",
        b"\n",
        b"relative\n",
        b"/one\n/two\n",
        b"/root/\xff\n",
        b"/root/\xef\xbf\xbd\n",
        b"/root/\tlib\n",
        b"/root/\0lib\n",
        b"/root/\xc2\x85lib\n",
        b"/root/\xe2\x80\xa8lib\n",
    ] {
        assert!(target_directory(output).is_err(), "{output:?}");
    }
    assert!(target_directory(&vec![b'x'; QUERY_LIMIT + 1]).is_err());
}

fn fixture_tree() -> (tempfile::TempDir, PathBuf, PathBuf) {
    let directory = tempfile::tempdir().unwrap();
    let bin = directory.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let executable = bin.join("compiler");
    fs::write(&executable, b"unexecuted compiler fixture").unwrap();
    let library = directory.path().join("target-library");
    fs::create_dir(&library).unwrap();
    fs::write(library.join("libstd.rlib"), b"library").unwrap();
    fs::write(library.join("libstd.rmeta"), b"metadata").unwrap();
    fs::create_dir(library.join("empty")).unwrap();
    fs::create_dir(library.join("rustc-dependencies")).unwrap();
    fs::write(library.join("rustc-dependencies/helper.native"), b"helper").unwrap();
    (directory, executable, library)
}

fn capture(executable: &Path, library: &Path) -> CompilerIdentity {
    let mut query_count = 0;
    let identity = capture_with(executable, |selected, arguments| {
        assert_eq!(selected, fs::canonicalize(executable).unwrap());
        query_count += 1;
        let stdout = if arguments == ["--version", "--verbose"] {
            b"test-only version".to_vec()
        } else {
            let mut expected = EXTRACTION_FLAGS.to_vec();
            expected.extend(["--print", "target-libdir"]);
            assert_eq!(arguments, expected);
            format!("{}\n", library.display()).into_bytes()
        };
        Ok(QueryOutput { stdout, stderr: b"captured diagnostic".to_vec() })
    })
    .unwrap();
    assert_eq!(query_count, 2);
    identity
}

#[test]
fn compiler_observation_includes_recursive_metadata_and_empty_directories() {
    let (_directory, executable, library) = fixture_tree();
    let identity = capture(&executable, &library);
    assert_eq!(identity.target_library.query_stderr, b"captured diagnostic");
    assert_eq!(identity.version_stderr, b"captured diagnostic");
    assert!(identity.target_library.entries.iter().any(|row| matches!(row,
        LibraryEntry::File {path, ..} if path == "libstd.rmeta")));
    assert!(identity.target_library.entries.iter().any(|row| matches!(row,
        LibraryEntry::File {path, ..} if path == "rustc-dependencies/helper.native")));
    assert!(identity.target_library.entries.iter().any(|row| matches!(row,
        LibraryEntry::Directory {path} if path == "empty")));
    fs::write(library.join("libstd.rmeta"), b"mutated!").unwrap();
    assert_ne!(
        identity,
        capture(&executable, &library),
        "same-size metadata mutation must change identity"
    );
    fs::write(library.join("libstd.rmeta"), b"metadata").unwrap();
    assert_eq!(identity, capture(&executable, &library));
    fs::write(library.join("extra.custom"), b"new").unwrap();
    assert_ne!(identity, capture(&executable, &library));
    fs::remove_file(library.join("extra.custom")).unwrap();
    fs::remove_file(library.join("libstd.rmeta")).unwrap();
    assert_ne!(identity, capture(&executable, &library));
}

#[test]
fn compiler_query_failures_and_changed_reported_roots_refuse_or_change_identity() {
    let (_directory, executable, library) = fixture_tree();
    for detail in ["spawn failed", "nonzero compiler status", "query timed out"] {
        let error = capture_with(&executable, |_, _| Err(failure(detail))).unwrap_err();
        assert!(error.to_string().contains(detail));
    }
    for (stdout, stderr) in
        [(vec![b'x'; QUERY_LIMIT + 1], vec![]), (vec![], vec![b'x'; QUERY_LIMIT + 1])]
    {
        assert!(
            capture_with(&executable, |_, _| Ok(QueryOutput {
                stdout: stdout.clone(),
                stderr: stderr.clone()
            }))
            .is_err()
        );
    }
    let first = capture(&executable, &library);
    let other = library.with_file_name("other-library");
    fs::create_dir(&other).unwrap();
    assert_ne!(first, capture(&executable, &other));
    fs::remove_dir(&other).unwrap();
    assert!(
        capture_with(&executable, |_, arguments| Ok(QueryOutput {
            stdout: if arguments == ["--version", "--verbose"] {
                b"version".to_vec()
            } else {
                format!("{}\n", other.display()).into_bytes()
            },
            stderr: vec![],
        }))
        .is_err()
    );
}

#[test]
fn mandatory_inventory_never_defaults_when_legacy_identity_is_read() {
    let identity = fixture();
    let old = serde_json::to_vec(&identity.legacy_keys()).unwrap();
    assert!(serde_json::from_slice::<CompilerIdentity>(&old).is_err());
    let mut missing = serde_json::to_value(&identity).unwrap();
    missing.as_object_mut().unwrap().remove("target_library");
    assert!(serde_json::from_value::<CompilerIdentity>(missing).is_err());
}

#[test]
fn carriage_return_in_reported_root_cannot_select_a_normal_sibling() {
    let (_directory, executable, decoy) = fixture_tree();
    let reported = decoy.with_file_name("target-library\r");
    fs::create_dir(&reported).unwrap();
    fs::write(reported.join("actual.rmeta"), b"actual metadata").unwrap();
    let answer = capture_with(&executable, |_, arguments| {
        Ok(QueryOutput {
            stdout: if arguments == ["--version", "--verbose"] {
                b"test-only version".to_vec()
            } else {
                // This is rustc's actual Path::display + println LF contract.
                format!("{}\n", reported.display()).into_bytes()
            },
            stderr: vec![],
        })
    });
    assert!(answer.is_err(), "a control-bearing root selected its ordinary sibling: {answer:?}");
}
