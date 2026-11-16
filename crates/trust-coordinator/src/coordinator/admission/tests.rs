use std::sync::atomic::{AtomicU64, Ordering};

use super::*;

const TEST_TIMEOUT: Duration = Duration::from_secs(2);

fn work() -> AdmissionWork {
    AdmissionWork {
        run_digest: "1".repeat(64),
        unit_digest: "2".repeat(64),
        semantics_digest: "3".repeat(64),
        work_digest: "4".repeat(64),
        kind: AdmissionWorkKind::NativeVerification,
        attempt: 1,
    }
}

fn test_daemon(bytes: u64) -> Arc<Daemon> {
    let mut daemon = Daemon::with_budget(bytes);
    let identity = AdmissionIdentity::with_entropy(daemon.identity.clone(), |bytes| {
        bytes.fill(42);
        true
    });
    Arc::get_mut(&mut daemon).unwrap().admission_identity = identity;
    daemon
}

fn request(bytes: u64, work: AdmissionWork) -> String {
    serde_json::to_string(&AdmissionRequest {
        version: ADMISSION_REQUEST_VERSION.to_string(),
        bytes,
        pid: std::process::id(),
        work,
    })
    .unwrap()
}

fn grant(daemon: &Daemon, bytes: u64, work: AdmissionWork) -> AdmissionGrant {
    let reply = daemon.reserve_evidence(&request(bytes, work));
    let result: AdmissionGrant =
        serde_json::from_str(reply.line.strip_prefix("ADMITTED ").unwrap()).unwrap();
    assert_eq!(reply.token, Some(result.token));
    assert!(result.is_valid());
    result
}

struct Server {
    root: PathBuf,
    socket: PathBuf,
    thread: Option<std::thread::JoinHandle<()>>,
}

impl Server {
    fn start(handler: impl FnOnce(UnixStream) + Send + 'static) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::fs::canonicalize("/tmp").unwrap().join(format!(
            "trustd-admission-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let socket = root.join("d.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        std::fs::set_permissions(&socket, std::fs::Permissions::from_mode(0o600)).unwrap();
        listener.set_nonblocking(true).unwrap();
        let thread = std::thread::spawn(move || {
            let deadline = Instant::now() + TEST_TIMEOUT;
            let stream = loop {
                match listener.accept() {
                    Ok((stream, _)) => break stream,
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        assert!(Instant::now() < deadline, "test client did not connect");
                        std::thread::sleep(Duration::from_millis(1));
                    }
                    Err(error) => panic!("test accept failed: {error}"),
                }
            };
            // Darwin inherits the listener's nonblocking mode on accept. The
            // fixture's raw EOF checks need the same normalization as serve_conn.
            stream.set_nonblocking(false).unwrap();
            stream.set_read_timeout(Some(TEST_TIMEOUT)).unwrap();
            handler(stream);
        });
        Self { root, socket, thread: Some(thread) }
    }

    fn finish(mut self) {
        self.thread.take().unwrap().join().unwrap();
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        // Every fixture owns only this freshly-created private directory.
        let _ = std::fs::remove_file(&self.socket);
        let _ = std::fs::remove_dir(&self.root);
    }
}

fn exchange(stream: &mut UnixStream, frame: &str) -> String {
    let deadline = Instant::now() + TEST_TIMEOUT;
    write_line_until(stream, frame, deadline).unwrap();
    read_one_line_until(stream, deadline).unwrap()
}

fn reply_to(stream: &mut UnixStream, expected: &str, reply: &str) {
    assert_eq!(read_one_line_until(stream, Instant::now() + TEST_TIMEOUT).unwrap(), expected);
    writeln!(stream, "{reply}").unwrap();
    stream.flush().unwrap();
}

#[test]
fn positive_live_exchange_retains_exact_locked_snapshot_after_preflight_shrink() {
    let daemon = test_daemon(128);
    let earlier = grant(&daemon, 8, AdmissionWork { attempt: 2, ..work() });
    let serving = Arc::clone(&daemon);
    let server = Server::start(move |stream| serving.serve_conn(stream));
    let evidence =
        reserve_at_with(&server.socket, 32, &daemon.identity, work(), TEST_TIMEOUT, || {
            // This callback runs after receiving STATUS and before sending RESERVE.
            // No ambient RAM measurement or process-global configuration is involved.
            daemon.lock().budget_bytes = 64;
            128
        })
        .unwrap();
    let receipt = evidence.receipt().clone();
    assert_eq!(receipt.daemon_budget_at_preflight_bytes(), 128);
    assert_eq!(receipt.client_budget_at_preflight_bytes(), 128);
    assert_eq!(evidence.bytes(), 32);
    assert_eq!(receipt.grant().budget_at_grant_bytes, 64);
    assert_eq!(receipt.grant().reserved_before_bytes, 8);
    assert_eq!(receipt.grant().reserved_after_bytes, 40);
    assert_eq!(receipt.grant().grant_sequence, 2);
    assert_eq!(receipt.grant().authority, *daemon.admission_identity.as_ref().unwrap());
    assert_eq!(receipt.grant().work, work());
    drop(evidence);
    server.finish();
    assert_eq!(daemon.lock().reserved_bytes, 8);
    daemon.release(earlier.token);
    assert_eq!(daemon.lock().released_total, 2);
    // Data survives release but holds no reservation and reports no completion.
    assert!(serde_json::to_string(&receipt).unwrap().contains(ADMISSION_RECEIPT_VERSION));
}

#[test]
fn preflight_shrink_refuses_request_that_no_longer_fits() {
    let daemon = test_daemon(128);
    let serving = Arc::clone(&daemon);
    let server = Server::start(move |stream| serving.serve_conn(stream));
    assert!(
        reserve_at_with(&server.socket, 65, &daemon.identity, work(), TEST_TIMEOUT, || {
            daemon.lock().budget_bytes = 64;
            128
        })
        .is_err()
    );
    server.finish();
    assert_eq!(daemon.lock().granted_total, 0);
}

#[test]
fn evidence_ownership_is_connection_bound_and_live_grants_stay_bounded() {
    let daemon = test_daemon(128);
    let (mut owner, server_side) = UnixStream::pair().unwrap();
    let serving = Arc::clone(&daemon);
    let serving_thread = std::thread::spawn(move || serving.serve_conn(server_side));
    let reply = exchange(&mut owner, &format!("RESERVE_EVIDENCE {}", request(16, work())));
    let granted: AdmissionGrant =
        serde_json::from_str(reply.strip_prefix("ADMITTED ").unwrap()).unwrap();
    assert_eq!(exchange(&mut owner, "RESERVE 1 1 legacy"), "ERR outstanding-grant");
    assert_eq!(
        exchange(&mut owner, &format!("RESERVE_EVIDENCE {}", request(1, work()))),
        "ERR outstanding-grant"
    );

    let (mut other, server_side) = UnixStream::pair().unwrap();
    let serving = Arc::clone(&daemon);
    let other_thread = std::thread::spawn(move || serving.serve_conn(server_side));
    assert_eq!(exchange(&mut other, &format!("RELEASE {}", granted.token)), "ERR unowned-token");
    assert_eq!(
        exchange(&mut other, &format!("RESERVE_EVIDENCE {}", request(1, work()))),
        "ERR duplicate-live-work"
    );
    assert_eq!(daemon.lock().reserved_bytes, 16);
    drop(other);
    other_thread.join().unwrap();
    // EOF, including a client which cannot retain/serialize a receipt, releases once.
    drop(owner);
    serving_thread.join().unwrap();
    assert_eq!(daemon.lock().reserved_bytes, 0);
    assert_eq!(daemon.lock().released_total, 1);
}

#[test]
fn disconnected_reply_releases_the_new_typed_grant() {
    let daemon = test_daemon(128);
    let (mut client, server_side) = UnixStream::pair().unwrap();
    writeln!(client, "RESERVE_EVIDENCE {}", request(8, work())).unwrap();
    let mut peer = Some(client);
    daemon.serve_conn_with_reply_hook(server_side, TEST_TIMEOUT, None, |reply| {
        assert!(reply.token.is_some(), "the disconnect must follow a real grant");
        assert_eq!(daemon.lock().reserved_bytes, 8);
        // Closing before handler setup is not equivalent: Darwin can reject
        // SO_RCVTIMEO on a closed peer before its queued request is read.
        let client = peer.take().expect("exactly one grant reply");
        client.shutdown(std::net::Shutdown::Both).unwrap();
        drop(client);
    });
    assert!(peer.is_none(), "the grant/reply boundary must be reached");
    let state = daemon.lock();
    assert_eq!(state.granted_total, 1);
    assert_eq!(state.released_total, 1);
    assert_eq!(state.reserved_bytes, 0);
}

#[test]
fn malformed_or_zero_requests_never_mutate_the_ledger() {
    let daemon = test_daemon(128);
    let valid: serde_json::Value = serde_json::from_str(&request(1, work())).unwrap();
    for (path, value) in [
        ("version", serde_json::json!("trustd.admission-request.v0")),
        ("bytes", serde_json::json!(0)),
        ("bytes", serde_json::json!("18446744073709551616")),
        ("pid", serde_json::json!(0)),
        ("pid", serde_json::json!(u32::MAX)),
        ("extra", serde_json::json!(true)),
    ] {
        let mut invalid = valid.clone();
        invalid[path] = value;
        assert_eq!(daemon.reserve_evidence(&invalid.to_string()).line, "ERR bad-evidence-request");
    }
    for field in ["run_digest", "unit_digest", "semantics_digest", "work_digest"] {
        let mut invalid = valid.clone();
        invalid["work"][field] = serde_json::json!("A".repeat(64));
        assert_eq!(daemon.reserve_evidence(&invalid.to_string()).line, "ERR bad-evidence-request");
    }
    for body in ["{}".to_string(), format!("{} {{}}", valid), "x".repeat(MAX_REQUEST_BYTES)] {
        assert!(!exact_nonzero_reserve(&format!("RESERVE_EVIDENCE {body}")));
        assert!(daemon.handle_line(&format!("RESERVE_EVIDENCE {body}")).starts_with("ERR "));
    }
    assert_eq!(daemon.lock().granted_total, 0);
    assert_eq!(daemon.handle_line("RESERVE 0 1 legacy"), "GRANTED 0");
}

#[test]
fn entropy_failure_disables_evidence_without_weak_fallback_or_legacy_change() {
    let mut daemon = test_daemon(128);
    let failed = AdmissionIdentity::with_entropy(daemon.identity.clone(), |bytes| {
        bytes.fill(7); // partial writes on error are never used
        false
    });
    assert!(failed.is_none());
    assert!(AdmissionIdentity::with_entropy(daemon.identity.clone(), |_| true).is_none());
    Arc::get_mut(&mut daemon).unwrap().admission_identity = failed;
    assert_eq!(daemon.handle_line("ADMISSION_IDENTITY"), "ERR evidence-unavailable");
    assert_eq!(daemon.reserve_evidence(&request(1, work())).line, "ERR evidence-unavailable");
    assert_eq!(daemon.handle_line("RESERVE 1 1 legacy"), "GRANTED 1");
    daemon.release(1);
}

#[test]
fn token_and_sequence_exhaustion_never_reuses_evidence_identity() {
    let daemon = test_daemon(u64::MAX);
    daemon.lock().next_token = u64::MAX;
    let last = grant(&daemon, 1, work());
    assert_eq!(last.token, u64::MAX);
    daemon.release(last.token);
    assert_eq!(
        daemon.reserve_evidence(&request(1, work())).line,
        "ERR evidence-sequence-exhausted"
    );
    assert_eq!(daemon.handle_line("RESERVE 1 1 legacy"), "GRANTED 1");
    daemon.release(1);
    let daemon = test_daemon(128);
    daemon.lock().granted_total = u64::MAX;
    assert_eq!(
        daemon.reserve_evidence(&request(1, work())).line,
        "ERR evidence-sequence-exhausted"
    );
}

#[test]
fn work_claims_remain_distinct_but_no_terminal_uniqueness_is_claimed() {
    let daemon = test_daemon(128);
    let first = grant(&daemon, 1, work());
    let mut variants = Vec::new();
    for field in 0..6 {
        let mut distinct = work();
        match field {
            0 => distinct.run_digest = "5".repeat(64),
            1 => distinct.unit_digest = "5".repeat(64),
            2 => distinct.semantics_digest = "5".repeat(64),
            3 => distinct.work_digest = "5".repeat(64),
            4 => distinct.attempt = 2,
            _ => distinct.kind = AdmissionWorkKind::ExternalSolver,
        }
        variants.push(grant(&daemon, 1, distinct));
    }
    daemon.release(first.token);
    let repeated = grant(&daemon, 1, work());
    assert_ne!(repeated.token, first.token);
    assert_ne!(repeated.grant_sequence, first.grant_sequence);
    for entry in variants.into_iter().chain([repeated]) {
        daemon.release(entry.token);
    }
    assert!(daemon.lock().active.is_empty());
}

#[test]
fn client_rejects_each_contradictory_grant_and_never_accepts_legacy_success() {
    let daemon = test_daemon(128);
    let preflight_status = daemon.status_line();
    let valid = grant(&daemon, 8, work());
    daemon.release(valid.token);
    let valid_json = serde_json::to_value(&valid).unwrap();
    let mut replies =
        vec!["GRANTED 1".to_string(), "DEGRADED".to_string(), "ADMITTED {}".to_string()];
    for (path, value) in [
        ("version", serde_json::json!("old")),
        ("token", serde_json::json!(0)),
        ("bytes", serde_json::json!(7)),
        ("budget_at_grant_bytes", serde_json::json!(0)),
        ("budget_at_grant_bytes", serde_json::json!(129)),
        ("reserved_before_bytes", serde_json::json!(u64::MAX)),
        ("reserved_after_bytes", serde_json::json!(7)),
        ("grant_sequence", serde_json::json!(0)),
        ("extra", serde_json::json!(true)),
    ] {
        let mut invalid = valid_json.clone();
        invalid[path] = value;
        replies.push(format!("ADMITTED {invalid}"));
    }
    for field in ["incarnation", "version"] {
        let mut invalid = valid_json.clone();
        invalid["authority"][field] = serde_json::json!("5".repeat(64));
        replies.push(format!("ADMITTED {invalid}"));
    }
    for field in ["run_digest", "unit_digest", "semantics_digest", "work_digest"] {
        let mut invalid = valid_json.clone();
        invalid["work"][field] = serde_json::json!("5".repeat(64));
        replies.push(format!("ADMITTED {invalid}"));
    }
    let mut invalid = valid_json.clone();
    invalid["authority"]["daemon"]["commit"] = serde_json::json!("substituted");
    replies.push(format!("ADMITTED {invalid}"));
    replies.push(format!("ADMITTED {valid_json} {{}}"));
    // The same scripted endpoint and pre-grant STATUS accept the intact frame;
    // each following mutation must be causally responsible for its refusal.
    replies.insert(0, format!("ADMITTED {valid_json}"));
    for (index, reply) in replies.into_iter().enumerate() {
        let identity = daemon.admission_identity_line();
        let status = preflight_status.clone();
        let server = Server::start(move |mut stream| {
            reply_to(&mut stream, "ADMISSION_IDENTITY", &identity);
            reply_to(&mut stream, "STATUS", &status);
            let incoming = read_one_line_until(&stream, Instant::now() + TEST_TIMEOUT).unwrap();
            assert!(incoming.starts_with("RESERVE_EVIDENCE "));
            writeln!(stream, "{reply}").unwrap();
        });
        let result =
            reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128);
        if index == 0 {
            assert_eq!(result.unwrap().bytes(), 8);
        } else {
            assert!(result.is_err());
        }
        server.finish();
    }
}

#[test]
fn incompatible_identity_client_domain_zero_budget_and_disconnect_fail_closed() {
    let daemon = test_daemon(128);
    let mut mismatched = daemon.admission_identity.clone().unwrap();
    mismatched.daemon.commit.push_str("-substituted");
    for identity in [
        "ERR unknown-verb".to_string(),
        "{}".to_string(),
        serde_json::to_string(&mismatched).unwrap(),
    ] {
        let server =
            Server::start(move |mut stream| reply_to(&mut stream, "ADMISSION_IDENTITY", &identity));
        assert!(
            reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128)
                .is_err()
        );
        server.finish();
    }
    for (daemon_budget, client_budget_at_preflight_bytes) in [(0, 128), (128, 64), (128, 0)] {
        let mut tested = test_daemon(daemon_budget);
        Arc::get_mut(&mut tested).unwrap().identity = daemon.identity.clone();
        let serving = Arc::clone(&tested);
        let server = Server::start(move |stream| serving.serve_conn(stream));
        assert!(
            reserve_at_with(&server.socket, 8, &tested.identity, work(), TEST_TIMEOUT, || {
                client_budget_at_preflight_bytes
            })
            .is_err()
        );
        server.finish();
        assert_eq!(tested.lock().granted_total, 0);
    }
    let server = Server::start(|_| {});
    assert!(
        reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128).is_err()
    );
    server.finish();
    assert!(
        reserve_at_with(
            Path::new("/nonexistent"),
            0,
            &daemon.identity,
            work(),
            TEST_TIMEOUT,
            || 128
        )
        .is_err()
    );
}

#[test]
fn admission_build_mismatch_names_both_images_before_any_reservation() {
    let daemon = test_daemon(128);
    for field in ["commit", "release", "executable_sha256"] {
        let mut expected = daemon.identity.clone();
        match field {
            "commit" => expected.commit = "new-compiler-source".to_string(),
            "release" => expected.release = "new-compiler-release".to_string(),
            _ => expected.executable_sha256 = "a".repeat(64),
        }
        assert_ne!(expected, daemon.identity, "the fixture changes {field}");
        let identity = daemon.admission_identity_line();
        let server = Server::start(move |mut stream| {
            reply_to(&mut stream, "ADMISSION_IDENTITY", &identity);
            let mut next = [0u8; 1];
            assert_eq!(stream.read(&mut next).unwrap(), 0, "no STATUS or RESERVE after mismatch");
        });
        let error = reserve_at_with(&server.socket, 8, &expected, work(), TEST_TIMEOUT, || 128)
            .expect_err("a different image never grants admission")
            .to_string();
        assert!(error.contains("build identity mismatch"), "{error}");
        for value in [
            &expected.release,
            &expected.commit,
            &expected.executable_sha256,
            &daemon.identity.release,
            &daemon.identity.commit,
            &daemon.identity.executable_sha256,
        ] {
            assert!(error.contains(value), "missing {value}: {error}");
        }
        assert!(error.contains("x.py build --stage 1 targo-trust"), "{error}");
        server.finish();
        assert_eq!(daemon.lock().granted_total, 0);
        assert_eq!(daemon.lock().reserved_bytes, 0);
    }
}

#[test]
fn malformed_admission_identity_does_not_claim_a_valid_build_mismatch() {
    let daemon = test_daemon(128);
    for frame in ["ERR unknown-verb", "{}"] {
        let server = Server::start(move |mut stream| {
            reply_to(&mut stream, "ADMISSION_IDENTITY", frame);
        });
        let error =
            reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128)
                .expect_err("an unsupported or malformed identity stays refused")
                .to_string();
        assert!(error.contains("missing, unsupported or malformed"), "{error}");
        assert!(!error.contains("build identity mismatch"), "{error}");
        server.finish();
        assert_eq!(daemon.lock().granted_total, 0);
    }
}

#[test]
fn identity_and_grant_timeouts_are_bounded_without_fallback() {
    let daemon = test_daemon(128);
    let (resume, wait) = std::sync::mpsc::channel();
    let server = Server::start(move |stream| {
        assert_eq!(
            read_one_line_until(&stream, Instant::now() + TEST_TIMEOUT).unwrap(),
            "ADMISSION_IDENTITY"
        );
        wait.recv_timeout(TEST_TIMEOUT).unwrap();
    });
    assert!(
        reserve_at_with(
            &server.socket,
            8,
            &daemon.identity,
            work(),
            Duration::from_millis(100),
            || 128
        )
        .is_err()
    );
    resume.send(()).unwrap();
    server.finish();

    let (resume, wait) = std::sync::mpsc::channel();
    let identity = daemon.admission_identity_line();
    let status = daemon.status_line();
    let server = Server::start(move |mut stream| {
        reply_to(&mut stream, "ADMISSION_IDENTITY", &identity);
        reply_to(&mut stream, "STATUS", &status);
        assert!(
            read_one_line_until(&stream, Instant::now() + TEST_TIMEOUT)
                .unwrap()
                .starts_with("RESERVE_EVIDENCE ")
        );
        wait.recv_timeout(TEST_TIMEOUT).unwrap();
    });
    assert!(
        reserve_at_with_timeouts(
            &server.socket,
            8,
            &daemon.identity,
            work(),
            (TEST_TIMEOUT, Duration::from_millis(100)),
            || 128
        )
        .is_err()
    );
    resume.send(()).unwrap();
    server.finish();
}

#[test]
fn evidence_refuses_inconsistent_or_overflowing_legacy_ledger() {
    let daemon = test_daemon(u64::MAX);
    // The legacy arithmetic behavior is left alone; an overflow cannot become
    // new evidence. Here the legacy STATUS ledger is deliberately contradictory.
    daemon.lock().reserved_bytes = u64::MAX;
    assert_eq!(daemon.reserve_evidence(&request(1, work())).line, "ERR invalid-evidence-ledger");
    assert_eq!(daemon.lock().granted_total, 0);
}

#[test]
fn legacy_grant_blocks_new_evidence_on_same_connection() {
    let daemon = test_daemon(128);
    let (mut client, stream) = UnixStream::pair().unwrap();
    let serving = Arc::clone(&daemon);
    let thread = std::thread::spawn(move || serving.serve_conn(stream));
    assert_eq!(exchange(&mut client, "RESERVE 8 1 legacy"), "GRANTED 1");
    assert_eq!(
        exchange(&mut client, &format!("RESERVE_EVIDENCE {}", request(8, work()))),
        "ERR outstanding-grant"
    );
    assert_eq!(daemon.lock().granted_total, 1);
    drop(client);
    thread.join().unwrap();
    assert_eq!(daemon.lock().reserved_bytes, 0);
}

#[test]
fn later_budget_shrink_cannot_rewrite_receipt_and_restart_has_new_incarnation() {
    let first = test_daemon(128);
    let serving = Arc::clone(&first);
    let server = Server::start(move |stream| serving.serve_conn(stream));
    let held =
        reserve_at_with(&server.socket, 8, &first.identity, work(), TEST_TIMEOUT, || 128).unwrap();
    let serialized_before = serde_json::to_string(held.receipt()).unwrap();
    first.lock().budget_bytes = 4;
    assert_eq!(held.receipt().grant().budget_at_grant_bytes, 128);
    assert_eq!(serde_json::to_string(held.receipt()).unwrap(), serialized_before);
    let old_grant = held.receipt().grant().clone();
    drop(held);
    server.finish();

    let mut second = test_daemon(128);
    let second_identity = second.identity.clone();
    Arc::get_mut(&mut second).unwrap().admission_identity =
        AdmissionIdentity::with_entropy(second_identity, |bytes| {
            bytes.fill(43);
            true
        });
    let new_grant = grant(&second, 8, work());
    assert_eq!(old_grant.token, new_grant.token);
    assert_eq!(old_grant.authority.daemon, new_grant.authority.daemon);
    assert_ne!(old_grant.authority.incarnation, new_grant.authority.incarnation);
    second.release(new_grant.token);
}

#[test]
fn rejected_reply_after_real_grant_returns_capacity_on_eof() {
    let daemon = test_daemon(128);
    let serving = Arc::clone(&daemon);
    let server = Server::start(move |mut client| {
        let (mut relay, live) = UnixStream::pair().unwrap();
        let live_thread = std::thread::spawn(move || serving.serve_conn(live));
        for index in 0..3 {
            let request = read_one_line_until(&client, Instant::now() + TEST_TIMEOUT).unwrap();
            let reply = exchange(&mut relay, &request);
            if index == 2 {
                assert!(reply.starts_with("ADMITTED "));
                writeln!(client, "{reply} {{}}").unwrap();
            } else {
                writeln!(client, "{reply}").unwrap();
            }
            client.flush().unwrap();
        }
        // Client validation failure closes the connection. Forward that EOF to
        // the actual daemon; the malformed data never mints a local guard.
        let mut byte = [0u8; 1];
        assert_eq!(client.read(&mut byte).expect("client must close, not time out"), 0);
        drop(relay);
        live_thread.join().unwrap();
    });
    assert!(
        reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128).is_err()
    );
    server.finish();
    assert_eq!(daemon.lock().granted_total, 1);
    assert_eq!(daemon.lock().released_total, 1);
    assert_eq!(daemon.lock().reserved_bytes, 0);
}

#[test]
fn evidence_child_lifetime_keeps_capacity_until_child_exit() {
    let daemon = test_daemon(128);
    let serving = Arc::clone(&daemon);
    let server = Server::start(move |stream| serving.serve_conn(stream));
    let held =
        reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128).unwrap();
    let (mut reservation, receipt) = held.into_parts();
    let mut command = std::process::Command::new("/bin/sh");
    command.args(["-c", "read line"]).stdin(std::process::Stdio::piped());
    reservation.configure_child_lifetime_guard(&mut command).unwrap();
    let mut child = command.spawn().unwrap();
    drop(command);
    drop(reservation);
    assert_eq!(daemon.lock().reserved_bytes, 8);
    assert_eq!(receipt.grant().bytes, 8);
    drop(child.stdin.take());
    let _ = child.wait().unwrap();
    server.finish();
    assert_eq!(daemon.lock().reserved_bytes, 0);
    assert_eq!(daemon.lock().released_total, 1);
}

#[test]
fn evidence_identity_and_frames_have_their_own_small_bounds() {
    let daemon = test_daemon(128);
    let preflight_status = daemon.status_line();
    let mut oversized = daemon.identity.clone();
    oversized.release = "x".repeat(MAX_IDENTITY_TEXT_BYTES + 1);
    assert!(
        AdmissionIdentity::with_entropy(oversized, |bytes| {
            bytes.fill(1);
            true
        })
        .is_none()
    );
    let valid = grant(&daemon, 8, work());
    daemon.release(valid.token);
    let valid = serde_json::to_string(&valid).unwrap();
    for (response, accepted) in [
        (format!("ADMITTED {valid}\n"), true),
        (format!("ADMITTED {valid}"), false),
        (format!("ADMITTED {valid}{}\n", " ".repeat(MAX_ADMISSION_REPLY_BYTES)), false),
    ] {
        let identity = daemon.admission_identity_line();
        let status = preflight_status.clone();
        let server = Server::start(move |mut stream| {
            reply_to(&mut stream, "ADMISSION_IDENTITY", &identity);
            reply_to(&mut stream, "STATUS", &status);
            assert!(
                read_one_line_until(&stream, Instant::now() + TEST_TIMEOUT)
                    .unwrap()
                    .starts_with("RESERVE_EVIDENCE ")
            );
            // The intact newline-terminated JSON is the acceptance control.
            // Truncation and a separately oversized, newline-terminated frame
            // are independent refusals; trailing JSON whitespace is otherwise valid.
            let _ = stream.write_all(response.as_bytes());
        });
        let result =
            reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128);
        assert_eq!(result.is_ok(), accepted);
        server.finish();
    }
}

#[test]
fn client_rejects_a_positive_but_previously_issued_grant_sequence() {
    let daemon = test_daemon(128);
    let old = grant(&daemon, 8, work());
    daemon.release(old.token);
    assert!(old.is_valid());
    let identity = daemon.admission_identity_line();
    let status = daemon.status_line();
    let response = format!("ADMITTED {}", serde_json::to_string(&old).unwrap());
    let server = Server::start(move |mut stream| {
        reply_to(&mut stream, "ADMISSION_IDENTITY", &identity);
        reply_to(&mut stream, "STATUS", &status);
        assert!(
            read_one_line_until(&stream, Instant::now() + TEST_TIMEOUT)
                .unwrap()
                .starts_with("RESERVE_EVIDENCE ")
        );
        writeln!(stream, "{response}").unwrap();
    });
    assert!(
        reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || 128).is_err()
    );
    server.finish();
}

#[test]
fn peer_grants_between_preflight_and_admission_can_leave_sequence_gaps() {
    let daemon = test_daemon(128);
    let serving = Arc::clone(&daemon);
    let server = Server::start(move |stream| serving.serve_conn(stream));
    let mut peers = Vec::new();
    // The callback runs after preflight. Two independently issued daemon grants
    // make this client's grant newer, but not adjacent to the observed counter.
    let held = reserve_at_with(&server.socket, 8, &daemon.identity, work(), TEST_TIMEOUT, || {
        for attempt in [2, 3] {
            peers.push(grant(&daemon, 1, AdmissionWork { attempt, ..work() }));
        }
        128
    })
    .unwrap();
    assert_eq!(held.receipt().grant().grant_sequence, 3);
    assert_eq!(held.receipt().grant().reserved_before_bytes, 2);
    drop(held);
    server.finish();
    for peer in peers {
        daemon.release(peer.token);
    }
    assert_eq!(daemon.lock().reserved_bytes, 0);
}
