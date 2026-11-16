use super::*;

#[test]
fn scoped_storage_policy_restores_nested_and_panicking_calls() {
    let initial = ArtifactStorePolicy::current();
    with_artifact_store_policy_for_test(17, false, || {
        assert_eq!(ArtifactStorePolicy::current().copy_cap_bytes, 17);
        let value = with_artifact_store_policy_for_test(23, true, || {
            assert_eq!(ArtifactStorePolicy::current().copy_cap_bytes, 23);
            assert!(ArtifactStorePolicy::current().link_from_private_store);
            42
        });
        assert_eq!(value, 42);
        assert_eq!(ArtifactStorePolicy::current().copy_cap_bytes, 17);
        assert!(!ArtifactStorePolicy::current().link_from_private_store);
        let panic = std::panic::catch_unwind(|| {
            with_artifact_store_policy_for_test(0, true, || panic!("policy unwind control"));
        });
        assert!(panic.is_err());
        assert_eq!(ArtifactStorePolicy::current().copy_cap_bytes, 17);
        assert!(!ArtifactStorePolicy::current().link_from_private_store);
    });
    assert_eq!(ArtifactStorePolicy::current().copy_cap_bytes, initial.copy_cap_bytes);
    assert_eq!(
        ArtifactStorePolicy::current().link_from_private_store,
        initial.link_from_private_store
    );
}

fn stored_artifact(source_root: &Path, label: &str) -> TransportEvidenceArtifact {
    let (materialization, digest) = native_test_materialization(
        "bundle",
        Some("trust-mc"),
        Some("storage-fixture"),
        None,
        serde_json::json!({"storage_fixture": label}),
        "storage-fixture",
        Vec::new(),
    );
    let bytes = materialization.decoded_bytes_at_root(&digest, source_root).unwrap();
    let relative =
        format!("{}/sha256/{}", trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY, digest.value);
    let path = source_root.join(&relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
    native_test_artifact(
        "EngineInput",
        (materialization.with_materialized_path(relative).unwrap(), digest),
        "artifact://storage-fixture".into(),
    )
}

fn occurrence<'a>(
    artifact: &'a TransportEvidenceArtifact,
    row_ordinal: usize,
    outcome: &'static str,
) -> ReportArtifactOccurrence<'a> {
    ReportArtifactOccurrence {
        row_ordinal,
        row: OmittedArtifactRow {
            // Display names need not be unique; the caller's row ordinal is.
            function: "compiler::same_name".into(),
            obligation_index: 0,
            obligation_id: Some(format!("obligation:{row_ordinal}")),
            outcome,
        },
        artifact,
    }
}

#[test]
fn typed_store_matches_report_adapter_and_outlives_private_source() {
    let source = tempfile::tempdir().unwrap();
    let (canonical, _) = sealed_store_backed_canonical_report(source.path());
    let typed = tempfile::tempdir().unwrap();
    let wrapped = tempfile::tempdir().unwrap();
    let _policy = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, false);
    let typed_status = persist_artifact_occurrences(
        path_backed_artifacts_in_persistence_order(&canonical),
        source.path(),
        typed.path(),
    )
    .unwrap();
    let wrapped_status = persist_report_artifact_store(
        &canonical,
        Some(source.path()),
        wrapped.path(),
        ArtifactStorePolicy::current(),
    )
    .unwrap();
    assert_eq!(typed_status, wrapped_status);
    assert!(typed_status.complete);
    assert_eq!(typed_status.persisted_artifacts, 1);
    let artifact = report_evidence_artifacts(&canonical)
        .into_iter()
        .find(|artifact| {
            artifact.materialization.as_ref().is_some_and(|value| value.materialized_path.is_some())
        })
        .unwrap();
    let digest = artifact.digest.as_ref().unwrap();
    let materialization = artifact.materialization.as_ref().unwrap();
    let source_root = source.path().canonicalize().unwrap();
    let typed_root = typed.path().canonicalize().unwrap();
    let wrapped_root = wrapped.path().canonicalize().unwrap();
    let expected = materialization.decoded_bytes_at_root(digest, &source_root).unwrap();
    drop(source);
    assert_eq!(materialization.decoded_bytes_at_root(digest, &typed_root).unwrap(), expected);
    assert_eq!(materialization.decoded_bytes_at_root(digest, &wrapped_root).unwrap(), expected);
}

#[test]
fn typed_store_stably_prioritizes_runtime_and_proved_rows() {
    let source = tempfile::tempdir().unwrap();
    let unknown = stored_artifact(source.path(), "unknown");
    let runtime = stored_artifact(source.path(), "runtime");
    let proved = stored_artifact(source.path(), "proved");
    let cap = runtime.materialization.as_ref().unwrap().byte_len;
    let output = tempfile::tempdir().unwrap();
    let _policy = artifact_store_policy(cap, false);
    let status = persist_artifact_occurrences(
        [
            occurrence(&unknown, 0, "unknown"),
            occurrence(&runtime, 1, "runtime_checked"),
            occurrence(&proved, 2, "proved"),
        ],
        source.path(),
        output.path(),
    )
    .unwrap();
    assert_eq!(status.copied_bytes, cap);
    assert_eq!(status.persisted_artifacts, 1);
    assert!(store_entry(output.path(), &runtime.digest.as_ref().unwrap().value).is_file());
    assert_eq!(status.omitted.len(), 2);
    assert_eq!(status.omitted[0].digest_sha256, proved.digest.as_ref().unwrap().value);
    assert_eq!(status.omitted[1].digest_sha256, unknown.digest.as_ref().unwrap().value);
    assert_eq!(status.omitted_proved_or_runtime_checked_rows, 1);
}

#[test]
fn typed_store_deduplicates_artifacts_and_keeps_distinct_row_owners() {
    let source = tempfile::tempdir().unwrap();
    let first = stored_artifact(source.path(), "first");
    let second = stored_artifact(source.path(), "second");
    let output = tempfile::tempdir().unwrap();
    let status = {
        let _policy = artifact_store_policy(0, false);
        persist_artifact_occurrences(
            [
                occurrence(&first, 0, "proved"),
                occurrence(&first, 0, "proved"),
                occurrence(&second, 0, "proved"),
                occurrence(&first, 1, "proved"),
            ],
            source.path(),
            output.path(),
        )
        .unwrap()
    };
    assert!(!status.complete);
    assert_eq!(status.omitted_artifacts, 2);
    assert_eq!(status.omitted[0].rows.len(), 2);
    assert_eq!(status.omitted[1].rows.len(), 1);
    assert_ne!(status.omitted[0].rows[0].obligation_id, status.omitted[0].rows[1].obligation_id);
    assert_eq!(status.omitted_proved_or_runtime_checked_rows, 2);

    let mut conflicting = first.clone();
    conflicting.materialization.as_mut().unwrap().byte_len += 1;
    let output = tempfile::tempdir().unwrap();
    let _policy = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, false);
    let error = persist_artifact_occurrences(
        [occurrence(&first, 0, "proved"), occurrence(&conflicting, 1, "proved")],
        source.path(),
        output.path(),
    )
    .unwrap_err();
    assert!(error.to_string().contains("earlier occurrence"), "{error}");
}

#[test]
fn typed_store_preserves_materialization_integrity_refusals() {
    let source = tempfile::tempdir().unwrap();
    let original = stored_artifact(source.path(), "integrity");
    type Mutation = (&'static str, fn(&mut TransportEvidenceArtifact));
    let mutations: &[Mutation] = &[
        ("missing digest", |artifact| artifact.digest = None),
        ("wrong digest", |artifact| artifact.digest.as_mut().unwrap().value = "a".repeat(64)),
        ("escaped path", |artifact| {
            artifact.materialization.as_mut().unwrap().materialized_path = Some("../escape".into())
        }),
        ("wrong length", |artifact| artifact.materialization.as_mut().unwrap().byte_len += 1),
    ];
    let _policy = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, false);
    for (name, mutate) in mutations {
        let mut artifact = original.clone();
        mutate(&mut artifact);
        let output = tempfile::tempdir().unwrap();
        assert!(
            persist_artifact_occurrences(
                [occurrence(&artifact, 0, "proved")],
                source.path(),
                output.path()
            )
            .is_err(),
            "{name}"
        );
    }
    let source_path = store_entry(source.path(), &original.digest.as_ref().unwrap().value);
    let mut bytes = fs::read(&source_path).unwrap();
    bytes[0] ^= 1;
    fs::write(source_path, bytes).unwrap();
    let output = tempfile::tempdir().unwrap();
    assert!(
        persist_artifact_occurrences(
            [occurrence(&original, 0, "proved")],
            source.path(),
            output.path()
        )
        .is_err()
    );
}

#[test]
fn typed_store_checks_later_descriptors_before_deduplicating_bytes() {
    let source = tempfile::tempdir().unwrap();
    let first = stored_artifact(source.path(), "shared-descriptor");
    type Mutation = (&'static str, fn(&mut TransportEvidenceArtifact));
    let mutations: &[Mutation] = &[
        ("empty binding", |artifact| {
            artifact.materialization.as_mut().unwrap().proof_binding_id.clear()
        }),
        ("wrong encoding", |artifact| {
            artifact.materialization.as_mut().unwrap().encoding = "bad".into()
        }),
        ("simultaneous inline bytes", |artifact| {
            artifact.materialization.as_mut().unwrap().encoded_bytes = "00".into()
        }),
        ("wrong algorithm", |artifact| artifact.digest.as_mut().unwrap().algorithm = "bad".into()),
        ("different path digest", |artifact| {
            artifact.materialization.as_mut().unwrap().materialized_path = Some(format!(
                "{}/sha256/{}",
                trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY,
                "a".repeat(64)
            ))
        }),
        ("normalized path alias", |artifact| {
            let path =
                artifact.materialization.as_mut().unwrap().materialized_path.as_mut().unwrap();
            *path = path.replace("/sha256/", "/sha256/./");
        }),
        ("repeated separator", |artifact| {
            let path =
                artifact.materialization.as_mut().unwrap().materialized_path.as_mut().unwrap();
            *path = path.replace("/sha256/", "//sha256/");
        }),
    ];
    for (name, mutate) in mutations {
        let mut later = first.clone();
        mutate(&mut later);
        // Copying, linking, cap omission and validation of an existing store
        // must all check a descriptor even when its payload digest was seen.
        for (cap, links, existing_store) in [
            (MAX_REPORT_ARTIFACT_STORE_BYTES, false, false),
            (MAX_REPORT_ARTIFACT_STORE_BYTES, true, false),
            (0, false, false),
            (MAX_REPORT_ARTIFACT_STORE_BYTES, false, true),
        ] {
            let output = tempfile::tempdir().unwrap();
            let destination = if existing_store { source.path() } else { output.path() };
            let _policy = artifact_store_policy(cap, links);
            assert!(
                persist_artifact_occurrences(
                    [occurrence(&first, 0, "unknown"), occurrence(&later, 1, "unknown")],
                    source.path(),
                    destination,
                )
                .is_err(),
                "{name}: cap={cap}, links={links}, existing_store={existing_store}"
            );
        }
    }
}

#[cfg(unix)]
#[test]
fn typed_store_preserves_link_first_and_rejects_symlinked_output_roots() {
    use std::os::unix::fs::MetadataExt as _;
    let source = tempfile::tempdir().unwrap();
    let artifact = stored_artifact(source.path(), "link");
    let output = tempfile::tempdir_in(source.path()).unwrap();
    let _policy = artifact_store_policy(0, true);
    let status = persist_artifact_occurrences(
        [occurrence(&artifact, 0, "proved")],
        source.path(),
        output.path(),
    )
    .unwrap();
    assert!(status.complete);
    assert_eq!((status.linked_artifacts, status.copied_bytes), (1, 0));
    let digest = &artifact.digest.as_ref().unwrap().value;
    assert_eq!(
        fs::metadata(store_entry(source.path(), digest)).unwrap().ino(),
        fs::metadata(store_entry(output.path(), digest)).unwrap().ino()
    );

    let alias = source.path().join("symlinked-output");
    std::os::unix::fs::symlink(output.path(), &alias).unwrap();
    let error =
        persist_artifact_occurrences([occurrence(&artifact, 0, "proved")], source.path(), &alias)
            .unwrap_err();
    assert!(error.to_string().contains("non-symlink directory"), "{error}");
}
