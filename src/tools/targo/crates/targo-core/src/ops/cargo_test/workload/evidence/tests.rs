use super::*;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) mod native {
    use super::*;
    use std::io::{Read as _, Write as _};
    use trust_resource_provenance::program::produced::HeldOutputRoot;

    pub(crate) struct Fixture {
        evidence: Arc<Evidence>,
        _output: HeldOutputRoot,
    }
    impl Fixture {
        pub(crate) fn at(parent: &Path) -> Self {
            let parent = parent.canonicalize().unwrap();
            let sdk_root = parent.join("input-image");
            let bin = sdk_root.join("bin");
            let output = parent.join("output");
            std::fs::create_dir_all(&bin).unwrap();
            std::fs::create_dir(&output).unwrap();
            // Copy an actual system-runtime image; the core test binary
            // may link external Git/TLS libraries outside this custody policy.
            let program = crate::compiler::native_input_fixture::materialize(&sdk_root);
            let mut hash = cargo_util::Sha256::new();
            hash.update_path(&program).unwrap();
            let deadline = Instant::now() + Duration::from_secs(60);
            let sdk =
                Arc::new(HeldProgram::open(&sdk_root, &program, &hash.finish(), deadline).unwrap());
            let (output, writer) =
                HeldOutputRoot::open_with_evidence(&output, &sdk, [1; 16], 16 * 1024, 16, deadline)
                    .unwrap();
            let evidence = Evidence::new(writer, sdk, [1; 16], [2; 32], deadline).unwrap();
            Self {
                evidence,
                _output: output,
            }
        }

        pub(crate) fn action(&self, stdout: u64) -> Arc<ActionEvidence> {
            self.evidence
                .action(
                    Binding {
                        member: [3; 16],
                        kind: Kind::CompilerQuery,
                        description_sha256: [4; 32],
                    },
                    stdout,
                    4096,
                )
                .unwrap()
        }

        pub(crate) fn raw(&self, stream: &str) -> Vec<u8> {
            std::fs::read(self.evidence.path().join(format!(
                "action-0000-{}.{}.bin",
                hex::encode([3; 16]),
                stream,
            )))
            .unwrap()
        }
    }

    #[test]
    fn actual_action_checkpoint_sync_keeps_same_root_writer_for_the_next_graph() {
        let temporary = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(temporary.path());
        let action = fixture.action(4096);
        action.stdout.append(b"original AY prefix\0").unwrap();
        action
            .sync_prefix(Instant::now() + Duration::from_secs(5))
            .unwrap();
        assert!(!fixture.evidence.sealed.load(Ordering::Acquire));
        assert!(!fixture.evidence.failed());
        let next = fixture
            .evidence
            .action(
                Binding {
                    member: [7; 16],
                    kind: Kind::Diagnostic,
                    description_sha256: [8; 32],
                },
                4096,
                4096,
            )
            .unwrap();
        next.stdout.append(b"same root consumer prefix").unwrap();
        action.stdout.append(b"after checkpoint").unwrap();
        next.sync_prefix(Instant::now() + Duration::from_secs(5))
            .unwrap();
        action
            .sync_prefix(Instant::now() + Duration::from_secs(5))
            .unwrap();
        assert_eq!(
            fixture.raw("stdout"),
            b"original AY prefix\0after checkpoint"
        );
        let busy = action.stdout.file.lock().unwrap();
        assert!(
            action
                .sync_prefix(Instant::now() + Duration::from_secs(1))
                .is_err()
        );
        drop(busy);
        assert!(
            fixture.evidence.failed(),
            "later synchronization cannot erase the original incomplete observation"
        );
        action
            .sync_prefix(Instant::now() + Duration::from_secs(5))
            .unwrap();
        assert!(fixture.evidence.failed());
    }

    fn observed_command() -> trust_resource_controller::CommandSpec {
        trust_resource_controller::CommandSpec {
            program: b"/selected/bin/trustc".to_vec(),
            arg0: None,
            cwd: b"/original/source".to_vec(),
            args: vec![
                b"--crate-name".to_vec(),
                b"ay_proof_common".to_vec(),
                b"--cfg=literal spaces and @ with native byte \xff".to_vec(),
                b"-Ztrust-policy=strict".to_vec(),
            ],
            environment: vec![
                (b"LANG".to_vec(), b"C".to_vec()),
                (
                    b"ATERM_RESOURCE_JOB_V3".to_vec(),
                    b"private-root-capability".to_vec(),
                ),
                (
                    b"TRUST_CPU_HANDOFF".to_vec(),
                    b"private-cpu-custody".to_vec(),
                ),
                (b"SEMANTIC".to_vec(), b"exact native value \xfe".to_vec()),
            ],
        }
    }
    fn command_action(
        fixture: &Fixture,
        command: &trust_resource_controller::CommandSpec,
    ) -> Arc<ActionEvidence> {
        fixture
            .evidence
            .action(
                Binding {
                    member: [6; 16],
                    kind: Kind::Compile,
                    description_sha256: command_description(command),
                },
                4096,
                4096,
            )
            .unwrap()
    }
    #[test]
    fn actual_pre_delivery_command_bytes_are_durable_and_private_transports_stay_omitted() {
        let temporary = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(temporary.path());
        let command = observed_command();
        let action = command_action(&fixture, &command);
        fixture
            .evidence
            .publish_action_command(&action, &command)
            .unwrap();
        let path = fixture
            .evidence
            .path()
            .join(format!("member-{}.command.v1.json", hex::encode([6; 16])));
        let bytes = std::fs::read(&path).unwrap();
        let record: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(record["member_attempt"], hex::encode([6; 16]));
        assert_eq!(
            record["args_hex"],
            serde_json::json!(command.args.iter().map(hex::encode).collect::<Vec<_>>())
        );
        assert!(record.get("outcome").is_none());
        assert!(record.get("materialization").is_none());
        let text = String::from_utf8(bytes.clone()).unwrap();
        for private in [
            b"private-root-capability".as_slice(),
            b"private-cpu-custody".as_slice(),
        ] {
            assert!(!text.contains(&hex::encode(private)));
        }
        let before = bytes;
        assert!(
            fixture
                .evidence
                .publish_action_command(&action, &command)
                .is_err(),
            "saved command must never overwrite the original create-only observation"
        );
        assert_eq!(std::fs::read(path).unwrap(), before);
        assert!(fixture.evidence.failed());
    }
    #[test]
    fn command_rebinding_and_wrong_original_action_refuse_before_publication() {
        for foreign in [false, true] {
            let temporary = tempfile::tempdir().unwrap();
            let a = temporary.path().join("a");
            let b = temporary.path().join("b");
            std::fs::create_dir(&a).unwrap();
            std::fs::create_dir(&b).unwrap();
            let fixture = Fixture::at(&a);
            let other = Fixture::at(&b);
            let mut command = observed_command();
            let action = command_action(if foreign { &other } else { &fixture }, &command);
            if !foreign {
                command.args.push(b"--changed-after-binding".to_vec());
            }
            assert!(
                fixture
                    .evidence
                    .publish_action_command(&action, &command)
                    .is_err()
            );
            assert!(
                !fixture
                    .evidence
                    .path()
                    .join(format!("member-{}.command.v1.json", hex::encode([6; 16])))
                    .exists()
            );
        }
    }
    #[test]
    fn command_budget_failure_retains_synced_partial_bytes_and_marks_evidence_incomplete() {
        let temporary = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(temporary.path());
        let mut command = observed_command();
        command.args.push(vec![b'x'; 12_000]);
        let action = command_action(&fixture, &command);
        assert!(
            fixture
                .evidence
                .publish_action_command(&action, &command)
                .is_err()
        );
        let bytes = std::fs::read(
            fixture
                .evidence
                .path()
                .join(format!("member-{}.command.v1.json", hex::encode([6; 16]))),
        )
        .unwrap();
        assert!(!bytes.is_empty() && bytes.len() < 24_000);
        assert!(serde_json::from_slice::<serde_json::Value>(&bytes).is_err());
        assert!(fixture.evidence.failed());
    }

    #[test]
    fn original_service_input_prefix_survives_failed_control_without_inventing_missing_bytes() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let (mut reader, mut writer) = std::io::pipe().unwrap();
        let original = b"\0\0\0\x20original-control\xffpartial";
        writer.write_all(original).unwrap();
        let mut received = vec![0; original.len()];
        reader.read_exact(&mut received).unwrap();
        fixture
            .evidence
            .publish_service_input(Ok((
                received,
                original.len() as u64,
                Some("original frame ended early".into()),
                true,
            )))
            .unwrap();
        let path = fixture.evidence.path().join("service-input.v1.json");
        let saved = std::fs::read(&path).unwrap();
        let record: serde_json::Value = serde_json::from_slice(&saved).unwrap();
        assert_eq!(record["root_attempt"], hex::encode([1; 16]));
        assert_eq!(record["invocation_sha256"], hex::encode([2; 32]));
        assert_eq!(record["observation"]["prefix_hex"], hex::encode(original));
        assert_eq!(record["observation"]["bytes_seen"], original.len() as u64);
        assert_eq!(record["observation"]["stopped"], true);
        assert!(
            fixture
                .evidence
                .publish_service_input(Err("late replacement".into()))
                .is_err()
        );
        assert_eq!(std::fs::read(path).unwrap(), saved);
        assert!(fixture.evidence.failed());
        drop(writer); // Saved input data never establishes actual EOF or retirement.

        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        fixture
            .evidence
            .publish_service_input(Err("observation unavailable".into()))
            .unwrap();
        let record: serde_json::Value = serde_json::from_slice(
            &std::fs::read(fixture.evidence.path().join("service-input.v1.json")).unwrap(),
        )
        .unwrap();
        for field in ["prefix_hex", "bytes_seen", "stopped"] {
            assert!(record["observation"][field].is_null());
        }
    }

    #[test]
    fn original_local_helper_wait_stays_separate_from_target_metrics_and_missing_is_not_zero() {
        use std::process::{Command, Stdio};
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let action = fixture.action(4096);
        action
            .stdout
            .append(b"retained before local helper observation")
            .unwrap();
        // Real local child/wait mechanics only. No managed SDK, registered
        // hosted target, source proof or Root resource admission is constructed.
        let mut child = Command::new("/bin/sh")
            .args(["-c", "read marker; exit 7"])
            .env_clear()
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        let identity = trust_resource_provenance::process::read_identity(child.id()).unwrap();
        child.stdin.take().unwrap().write_all(b"go\n").unwrap();
        let outcome = child.wait().unwrap();
        assert_eq!(outcome.code(), Some(7));
        fixture
            .evidence
            .publish_helper(
                [3; 16],
                Some(trust_resource_controller::client::HelperObservation {
                    identity: trust_resource_controller::Identity {
                        pid: identity.pid,
                        birth: identity.birth,
                        birth_kind: trust_resource_controller::BirthKind::MacosWallMicroseconds,
                    },
                    outcome: Some(trust_resource_controller::Outcome::Exit(7)),
                }),
            )
            .unwrap();
        let saved = std::fs::read(fixture.evidence.path().join(format!(
            "member-{}.local-helper.v1.json",
            hex::encode([3; 16])
        )))
        .unwrap();
        let record: serde_json::Value = serde_json::from_slice(&saved).unwrap();
        assert_eq!(record["helper"]["identity"]["pid"], identity.pid);
        assert_eq!(record["helper"]["outcome"]["exit"], 7);
        assert_eq!(record["target_member_attempt"], hex::encode([3; 16]));
        assert!(record["cpu_times"].is_null());
        assert_eq!(
            fixture.raw("stdout"),
            b"retained before local helper observation"
        );
        assert!(fixture.evidence.publish_helper([4; 16], None).is_err());
        assert!(fixture.evidence.failed());
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        fixture.action(4096);
        fixture.evidence.publish_helper([3; 16], None).unwrap();
        let record: serde_json::Value = serde_json::from_slice(
            &std::fs::read(fixture.evidence.path().join(format!(
                "member-{}.local-helper.v1.json",
                hex::encode([3; 16])
            )))
            .unwrap(),
        )
        .unwrap();
        assert!(record["helper"].is_null() && record["cpu_times"].is_null());
    }

    #[test]
    fn produced_failure_annex_retains_actual_event_prefix_without_relabeling_large_raw_streams() {
        use trust_resource_controller::workload::host::produced::Key;
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let action = fixture.action(4096);
        let (mut reader, mut writer) = std::io::pipe().unwrap();
        let actual = b"\0\0\0\x10produced\xffpartial";
        writer.write_all(actual).unwrap();
        let mut received = vec![0; actual.len()];
        reader.read_exact(&mut received).unwrap();
        action
            .stdout
            .append(b"actual produced stdout\0\xff")
            .unwrap();
        let mut observation = trust_resource_controller::client::ProducedFailureObservation {
            key: Key {
                root_attempt: [1; 16],
                invocation_sha256: [2; 32],
                phase: [5; 16],
                ordinal: 7,
                output: [6; 16],
            },
            member_attempt: [3; 16],
            prepared: None,
            observed_completion: None,
            observed_started: None,
            stdout: b"actual produced stdout\0\xff".to_vec(),
            stderr: Vec::new(),
            stdout_eof: false,
            stderr_eof: false,
            output_limit_exceeded: false,
            event_bytes_seen: received.len() as u64,
            event_prefix: received,
            capture_error: Some("actual incomplete produced frame".into()),
        };
        fixture
            .evidence
            .publish_produced_failure(&observation)
            .unwrap();
        let path = fixture.evidence.path().join(format!(
            "member-{}.produced-failure.v1",
            hex::encode([3; 16])
        ));
        let saved = std::fs::read(&path).unwrap();
        let header = b"trust.workload.produced-failure.v1\0";
        assert!(saved.starts_with(header));
        let mut offset = header.len() + 16 + 32 + 16 + 16 + 8 + 16;
        let number = |offset: &mut usize| {
            let value = u64::from_be_bytes(saved[*offset..*offset + 8].try_into().unwrap());
            *offset += 8;
            value
        };
        assert_eq!(number(&mut offset), observation.stdout.len() as u64);
        assert_eq!(number(&mut offset), 0);
        assert_eq!(&saved[offset..offset + 3], &[0, 0, 0]);
        offset += 3;
        assert_eq!(number(&mut offset), actual.len() as u64);
        assert_eq!(number(&mut offset), actual.len() as u64);
        assert_eq!(&saved[offset..offset + actual.len()], actual);
        assert_eq!(fixture.raw("stdout"), observation.stdout);
        assert!(
            !saved
                .windows(observation.stdout.len())
                .any(|bytes| bytes == observation.stdout),
            "raw bodies retain their original files, not a false metadata capture"
        );
        observation.key.invocation_sha256 = [9; 32];
        assert!(
            fixture
                .evidence
                .publish_produced_failure(&observation)
                .is_err()
        );
        assert_eq!(std::fs::read(path).unwrap(), saved);
        assert!(fixture.evidence.failed());
        drop(writer); // retained prefix did not invent a target or physical EOF.
    }

    #[test]
    fn actual_partial_native_failure_is_synchronized_under_its_original_action_binding() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let action = fixture.action(4096);
        let (mut reader, mut writer) = std::io::pipe().unwrap();
        let actual = b"\0\0\0\x08native\xffpartial";
        writer.write_all(actual).unwrap();
        let mut received = vec![0; actual.len()];
        reader.read_exact(&mut received).unwrap();
        action.stdout.append(b"original stdout\0\xff").unwrap();
        let mut failure = trust_resource_controller::MetadataFailureObservation {
            root_attempt: [1; 16],
            member_attempt: [3; 16],
            stdout: b"original stdout\0\xff".to_vec(),
            stderr: Vec::new(),
            stdout_eof: false,
            stderr_eof: false,
            output_limit_exceeded: false,
            event_bytes_seen: received.len() as u64,
            event_prefix: received,
            capture_error: Some("actual partial frame".into()),
        };
        fixture.evidence.publish_failure(&failure).unwrap();
        let path = fixture
            .evidence
            .path()
            .join(format!("member-{}.failure.v1", hex::encode([3; 16])));
        let saved = std::fs::read(&path).unwrap();
        assert_eq!(
            trust_resource_controller::MetadataFailureObservation::decode(&saved).unwrap(),
            failure
        );
        assert_eq!(fixture.raw("stdout"), b"original stdout\0\xff");
        failure.root_attempt = [9; 16];
        assert!(fixture.evidence.publish_failure(&failure).is_err());
        assert_eq!(
            std::fs::read(path).unwrap(),
            saved,
            "failed binding never overwrites original evidence"
        );
        assert!(fixture.evidence.failed());
        drop(writer); // no physical EOF was invented from saved bytes.
    }

    #[test]
    fn native_failure_publication_quota_keeps_received_prefix_and_stays_incomplete() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let action = fixture.action(4096);
        action
            .stdout
            .append(b"raw stream survives publication exhaustion")
            .unwrap();
        let failure = trust_resource_controller::MetadataFailureObservation {
            root_attempt: [1; 16],
            member_attempt: [3; 16],
            stdout: vec![b'x'; 20 * 1024],
            stderr: Vec::new(),
            stdout_eof: false,
            stderr_eof: false,
            output_limit_exceeded: false,
            event_bytes_seen: 0,
            event_prefix: Vec::new(),
            capture_error: None,
        };
        assert!(fixture.evidence.publish_failure(&failure).is_err());
        let saved = std::fs::read(
            fixture
                .evidence
                .path()
                .join(format!("member-{}.failure.v1", hex::encode([3; 16]))),
        )
        .unwrap();
        assert!(!saved.is_empty() && saved.len() < failure.encode().unwrap().len());
        assert!(trust_resource_controller::MetadataFailureObservation::decode(&saved).is_err());
        assert!(fixture.evidence.failed());
        assert_eq!(
            fixture.raw("stdout"),
            b"raw stream survives publication exhaustion"
        );
    }

    #[test]
    fn actual_binary_reads_are_written_before_completion_with_original_bound_metadata() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let action = fixture.action(4096);
        let (mut reader, mut writer) = std::io::pipe().unwrap();
        let input = b"received\0binary\xffprefix";
        writer.write_all(input).unwrap();
        let mut received = vec![0; input.len()];
        reader.read_exact(&mut received).unwrap();
        action.stdout.append(&received).unwrap();
        action.stderr.append(b"stderr\0\xfe").unwrap();
        assert_eq!(fixture.raw("stdout"), input);
        assert_eq!(fixture.raw("stderr"), b"stderr\0\xfe");
        assert_eq!(action.stdout.received(), input.len() as u64);
        assert_eq!(action.stdout.persisted(), input.len() as u64);
        fixture
            .evidence
            .synchronize(Instant::now() + Duration::from_secs(1))
            .unwrap();
        let unknown = std::fs::read(fixture.evidence.path().join("attempt-unknown.v1")).unwrap();
        assert!(unknown.starts_with(HEADER));
        assert_eq!(unknown.last(), Some(&0));
        assert!(unknown.windows(16).any(|bytes| bytes == [1; 16]));
        assert!(unknown.windows(32).any(|bytes| bytes == [2; 32]));
        assert!(!fixture.evidence.failed());
        // Keep the writer: observed prefixes do not invent stream EOF/exit.
        drop(writer);
    }

    #[test]
    fn byte_bound_keeps_the_actual_short_prefix_and_explicit_incomplete_counts() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let action = fixture.action(7);
        let actual = b"0123456789\0\xff";
        assert!(action.stdout.append(actual).is_err());
        assert_eq!(fixture.raw("stdout"), b"0123456");
        assert_eq!(action.stdout.received(), actual.len() as u64);
        assert_eq!(action.stdout.persisted(), 7);
        assert!(fixture.evidence.failed());
        // Keep collecting actually received peers after the comparison fails.
        action.stderr.append(b"actual later diagnostic").unwrap();
        assert_eq!(fixture.raw("stderr"), b"actual later diagnostic");
        assert!(
            fixture
                .evidence
                .action(
                    Binding {
                        member: [5; 16],
                        kind: Kind::Compile,
                        description_sha256: [6; 32],
                    },
                    7,
                    7
                )
                .is_err(),
            "failure cannot create a fresh replacement sink"
        );
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the isolated actual abort actor selects owned paths/mode before Cargo context exists"
    )]
    fn native_abort_preserves_original_prefixes_and_same_thread_contention_never_deadlocks() {
        const ROOT: &str = "TARGO_RAW_PREFIX_ACTOR_ROOT";
        const MODE: &str = "TARGO_RAW_PREFIX_ACTOR_MODE";
        if let Some(root) = std::env::var_os(ROOT) {
            let root = PathBuf::from(root);
            let fixture = Fixture::at(&root);
            let action = fixture.action(4096);
            let (mut reader, mut writer) = std::io::pipe().unwrap();
            writer.write_all(b"actual read before abort\0\xff").unwrap();
            let mut bytes = [0; 26];
            reader.read_exact(&mut bytes).unwrap();
            action.stdout.append(&bytes).unwrap();
            action.stderr.append(b"actual stderr\0\xfe").unwrap();
            fixture
                .evidence
                .publish_original_command(
                    [1; 16],
                    [2; 32],
                    7,
                    &"a".repeat(64),
                    b"{\"args_hex\":[\"00ff\"],\"materialization\":\"not-observed\"}",
                )
                .unwrap();
            let command = observed_command();
            let command_action = command_action(&fixture, &command);
            fixture
                .evidence
                .publish_action_command(&command_action, &command)
                .unwrap();
            install_abort_evidence(fixture.evidence.clone()).unwrap();
            let locked = std::env::var(MODE).unwrap() == "locked";
            let _held = locked.then(|| action.stdout.file.lock().unwrap());
            std::fs::write(root.join("before-abort"), b"original-provider-installed\n").unwrap();
            crate::resource_v3::workload::abort_fixture();
        }
        let directory = tempfile::tempdir().unwrap();
        let module = module_path!().split_once("::").unwrap().1;
        let exact = format!(
            "{module}::native_abort_preserves_original_prefixes_and_same_thread_contention_never_deadlocks"
        );
        for mode in ["normal", "locked"] {
            let root = directory.path().join(mode);
            std::fs::create_dir(&root).unwrap();
            let mut child = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", &exact])
                .env(ROOT, &root)
                .env(MODE, mode)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .unwrap();
            let until = Instant::now() + Duration::from_secs(30);
            let status = loop {
                if let Some(status) = child.try_wait().unwrap() {
                    break status;
                }
                if Instant::now() >= until {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("actual raw-prefix abort actor failed to terminate: {mode}");
                }
                std::thread::sleep(Duration::from_millis(5));
            };
            assert_eq!(status.code(), Some(75), "{mode}");
            assert_eq!(
                std::fs::read(root.join("before-abort")).unwrap(),
                b"original-provider-installed\n"
            );
            let path = root
                .join("output/.trust-workload-evidence.noindex")
                .join(hex::encode([1; 16]));
            let command: serde_json::Value = serde_json::from_slice(
                &std::fs::read(
                    path.join(format!("member-{}.command.v1.json", hex::encode([6; 16]))),
                )
                .unwrap(),
            )
            .unwrap();
            assert_eq!(
                command["args_hex"],
                serde_json::json!(
                    observed_command()
                        .args
                        .iter()
                        .map(hex::encode)
                        .collect::<Vec<_>>()
                )
            );
            assert!(
                command.get("outcome").is_none(),
                "a synchronized pre-delivery command is not an executed/successful member"
            );
            let name = format!("action-0000-{}", hex::encode([3; 16]));
            assert_eq!(
                std::fs::read(path.join(format!(
                    "unit-7-{}.original-command.v1.json",
                    "a".repeat(64)
                )))
                .unwrap(),
                b"{\"args_hex\":[\"00ff\"],\"materialization\":\"not-observed\"}"
            );
            assert_eq!(
                std::fs::read(path.join(format!("{name}.stdout.bin"))).unwrap(),
                b"actual read before abort\0\xff"
            );
            assert_eq!(
                std::fs::read(path.join(format!("{name}.stderr.bin"))).unwrap(),
                b"actual stderr\0\xfe"
            );
            assert_eq!(
                std::fs::read(path.join("attempt-unknown.v1"))
                    .unwrap()
                    .last(),
                Some(&0)
            );
        }
    }
}
