//! Actual Source Manager/ProtectedWorkScope and ordinary TOML parser controls.
//! These exercise private physical producer/callback guards, not an admitted
//! Host, Graph, accepted materialization, InputWorkClosed, Seed or SDK. The
//! guarded Graph/factory and parser-entry wiring require connected qualification.
use std::fs;
use std::os::unix::fs::symlink;

use trust_resource_controller::bootstrap_graph::Key;
use trust_resource_controller::bootstrap_graph::offline_preparation::IntentSelection;
use trust_resource_controller::{ContextQuery, JobBinding};

use super::*;

struct World {
    inputs: Arc<Inputs>,
    source: Arc<OriginalSourceRoot>,
    scope: ProtectedWorkScope,
    _directory: tempfile::TempDir,
}
fn world() -> World {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    fs::create_dir(root.join("config")).unwrap();
    fs::create_dir_all(root.join("src/ci")).unwrap();
    fs::write(root.join("src/ci/channel"), b"dev\n").unwrap();
    fs::write(root.join("src/version"), b"1.101.0\n").unwrap();
    fs::write(root.join("src/rust-compat-version"), b"1.103.0\n").unwrap();
    fs::write(root.join("bootstrap.toml"), b"profile='compiler'\ninclude=['config/extra.toml']\n")
        .unwrap();
    fs::write(root.join("config/extra.toml"), b"[build]\nlocked-deps=true\n").unwrap();
    fs::write(root.join("invalid.toml"), b"[bad\n").unwrap();
    File::create(root.join("oversize.toml"))
        .unwrap()
        .set_len(configuration::MAX_BYTES + 1)
        .unwrap();
    symlink("config", root.join("redirect")).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual original configuration source control".into(),
            contract: "physical source/file/callback only; no Host or native closure".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected private source contention"),
    };
    let end = Instant::now() + Duration::from_secs(30);
    let scope = ProtectedWorkScope::new(Arc::new(lease.into_withheld().unwrap()), end).unwrap();
    let source = Arc::new(scope.original_source(&root).unwrap());
    let key = Key {
        query: ContextQuery {
            binding: JobBinding {
                session: "t0000000001".into(),
                root_attempt: [1; 16],
                capability: [9; 32],
            },
            call_attempt: [2; 16],
        },
        graph: [3; 16],
    }; // codec equality DATA, never a live native Root
    key.validate().unwrap();
    let selection = IntentSelection {
        source_root: root.as_os_str().as_bytes().to_vec(),
        output_root: b"/unissued-output".to_vec(),
        configured_targo: b"/unissued-seed/bin/cargo".to_vec(),
        configured_compiler: b"/unissued-seed/bin/trustc".to_vec(),
        environment: vec![(b"CARGO_NET_OFFLINE".to_vec(), b"true".to_vec())],
        budget_ns: 30_000_000_000,
    };
    let inputs = Arc::new(Inputs::new(
        Arc::clone(&source),
        scope.dispatcher().downgrade(),
        key,
        selection,
        end,
    ));
    inputs.capture_root().unwrap();
    World { inputs, source, scope, _directory: directory }
}

#[test]
fn original_configuration_bytes_feed_the_existing_parser_and_preserve_ofd() {
    let world = world();
    let file = world.inputs.read(Path::new("bootstrap.toml")).unwrap();
    let end = world.inputs.deadline().unwrap();
    let contents = file.contents(end).unwrap();
    let parsed =
        world.inputs.with_parser(&contents, &mut Config::cache_output_fields).unwrap().unwrap();
    assert_eq!(parsed.2.as_deref(), Some("compiler"));
    assert_eq!(parsed.1, [PathBuf::from("config/extra.toml")]);
    let offer = file.offer(end).unwrap();
    let raw = offer.description(end).unwrap().as_raw_fd();
    let flags = unsafe { libc::fcntl(raw, libc::F_GETFL) };
    assert_eq!(flags & libc::O_ACCMODE, libc::O_RDONLY);
    assert_eq!(unsafe { libc::lseek(raw, 0, libc::SEEK_CUR) }, 0);
    world.inputs.check_current().unwrap();
    assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFL) }, flags);
    assert_eq!(unsafe { libc::lseek(raw, 0, libc::SEEK_CUR) }, 0);
    assert!(world.inputs.all_offered().is_err(), "parser output is not a native offer ACK");
    world.source.check_current().unwrap();
}

#[test]
fn actual_output_lock_and_source_scope_survive_early_physical_custody_and_path_refusal() {
    use std::os::fd::{AsFd, AsRawFd};
    use std::os::unix::net::UnixStream;
    use trust_resource_controller::bootstrap_graph::{offline_preparation, transport};

    // Genuine independent source/output guards. No Graph, native Root or
    // acceptance/retirement owner is fabricated by this physical caller test.
    let world = world();
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    let output = build_helper::trust_output_lock::OutputLock::try_acquire(&root).unwrap().unwrap();
    // SAFETY: fixture receiver and every actual duplicate are close-only.
    // This guard outlives the complete physical exchange and all duplicates.
    let descriptions = unsafe { output.original_descriptions() }.unwrap();
    let request = offline_preparation::PreparationOutputAttachment {
        key: query::OperationKey { graph: world.inputs.key.clone(), sequence: 1, operation: [4; 16] },
        root: fd_identity(descriptions.directory()).unwrap(),
        lock: fd_identity(descriptions.lock()).unwrap(),
    };
    let (left, right) = UnixStream::pair().unwrap();
    let mut sender = trust_resource_controller::Channel::new(left).unwrap();
    let mut receiver = trust_resource_controller::Channel::new(right).unwrap();
    let end = world.inputs.deadline().unwrap();
    let cursor = unsafe { libc::lseek(descriptions.lock().as_raw_fd(), 0, libc::SEEK_CUR) };
    transport::send_preparation_output(&mut sender, &request,
        &[descriptions.directory(), descriptions.lock()], end, || {
            world.inputs.check_current()?;
            output.check_current()
        }).unwrap();
    let delivered = transport::receive_preparation_output_delivery(&mut receiver, end).unwrap();
    let mut retained = Vec::new(); assert!(delivered.into_parts(&mut retained));
    transport::check_output(&request.physical_binding(),
        &[retained[0].as_fd(), retained[1].as_fd()]).unwrap();
    assert_eq!(unsafe { libc::lseek(descriptions.lock().as_raw_fd(), 0, libc::SEEK_CUR) }, cursor);
    assert!(build_helper::trust_output_lock::OutputLock::try_acquire_existing(&root).unwrap().is_none());
    sender.send(b"same source handler", end).unwrap();
    assert_eq!(receiver.receive(end).unwrap(), b"same source handler");
    fs::rename(root.join("lock"), root.join("held-original-lock")).unwrap();
    fs::write(root.join("lock"), b"metadata cannot replace the held lock").unwrap();
    assert!(output.check_current().is_err());
    let competitor = fs::OpenOptions::new().read(true).write(true)
        .open(root.join("held-original-lock")).unwrap();
    assert!(matches!(competitor.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    world.inputs.check_current().unwrap();
    assert!(!Manager::open(world.source.path()).unwrap().status().unwrap().is_free());
    drop((sender, receiver, retained));
    // Physical fixture teardown supplies no native closure/Manager release.
}

#[test]
fn observed_configuration_drift_keeps_the_original_and_quarantines_scope_aliases() {
    let world = world();
    let alias = Arc::clone(&world.source);
    let dispatch = world.scope.dispatcher();
    let file = world.inputs.read(Path::new("bootstrap.toml")).unwrap();
    let original = fs::read(world.source.path().join("bootstrap.toml")).unwrap();
    fs::write(world.source.path().join("bootstrap.toml"), b"profile='dist'\n").unwrap();
    assert!(world.inputs.check_current().is_err());
    fs::write(world.source.path().join("bootstrap.toml"), original).unwrap();
    assert!(world.inputs.read(Path::new("bootstrap.toml")).is_err());
    assert!(alias.directory().is_err());
    assert!(dispatch.register_worker().is_err());
    assert!(file.retained_descriptions() > 0);
    assert!(!Manager::open(alias.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn ordinary_parser_error_and_panic_permanently_quarantine_the_same_source() {
    for panic in [false, true] {
        let world = world();
        let alias = Arc::clone(&world.source);
        let file = world.inputs.read(Path::new("invalid.toml")).unwrap();
        let contents = file.contents(world.inputs.deadline().unwrap()).unwrap();
        if panic {
            let result = catch_unwind(AssertUnwindSafe(|| {
                let _: io::Result<Result<(), ()>> = world
                    .inputs
                    .with_parser(&contents, &mut |_| panic!("actual parser callback panic"));
            }));
            assert!(result.is_err());
        } else {
            let expected =
                Config::parse_toml_contents(&contents).err().expect("invalid TOML").to_string();
            let result =
                world.inputs.with_parser(&contents, &mut Config::parse_toml_contents).unwrap();
            assert_eq!(result.err().expect("same parser refusal").to_string(), expected);
        }
        assert!(alias.check_current().is_err());
        assert!(world.scope.dispatcher().register_launch().is_err());
        assert!(file.retained_descriptions() > 0);
    }
}

#[test]
fn partial_oversize_producer_is_retained_without_allocating_or_reading_contents() {
    let world = world();
    let path = world.source.path().join("oversize.toml");
    assert!(world.inputs.read(&path).is_err());
    let captures = world.inputs.captures.lock().unwrap();
    assert_eq!(captures.files.len(), 1);
    assert_eq!(captures.bytes, 0);
    assert!(captures.files[0].retained_descriptions() > 0);
    assert!(world.source.check_current().is_err());
}

#[test]
fn parser_callback_cannot_restore_changed_source_bytes_to_recover_its_issuer() {
    let world = world();
    let path = world.source.path().join("bootstrap.toml");
    let file = world.inputs.read(&path).unwrap();
    let contents = file.contents(world.inputs.deadline().unwrap()).unwrap();
    let result = world.inputs.with_parser(&contents, &mut |bytes| {
        fs::write(&path, b"profile='dist'\n").unwrap();
        fs::write(&path, bytes).unwrap();
        Config::cache_output_fields(bytes)
    });
    assert!(result.is_err());
    assert!(world.source.close_only_offer().is_err());
    assert!(world.scope.dispatcher().register_worker().is_err());
    assert!(file.retained_descriptions() > 0);
}

#[test]
fn prospective_default_config_discovery_remains_bound_to_the_original_root() {
    let world = world();
    let candidate = world.source.path().join("config.toml");
    assert!(!candidate.exists());
    world.inputs.check_current().unwrap();
    fs::write(&candidate, b"profile='dist'\n").unwrap();
    assert!(world.inputs.check_current().is_err());
    fs::remove_file(&candidate).unwrap();
    assert!(world.inputs.read(Path::new("bootstrap.toml")).is_err());
    assert!(world.source.directory().is_err());
    assert!(world.scope.dispatcher().register_worker().is_err());
}

#[test]
fn nofollow_alias_and_expired_endpoint_never_select_a_replacement_source() {
    for expired in [false, true] {
        let world = world();
        let alias = Arc::clone(&world.source);
        if expired {
            let end = Instant::now();
            assert!(world.inputs.restrict(end).is_err());
        } else {
            assert!(world.inputs.read(Path::new("redirect/extra.toml")).is_err());
        }
        assert!(world.inputs.read(Path::new("bootstrap.toml")).is_err());
        assert!(alias.close_only_offer().is_err());
        assert!(!Manager::open(alias.path()).unwrap().status().unwrap().is_free());
    }
}

#[test]
fn raw_config_text_uses_the_same_retained_producers_without_a_toml_evaluator() {
    let world = world();
    for (path, expected) in [
        ("src/ci/channel", "dev\n"),
        ("src/version", "1.101.0\n"),
        ("src/rust-compat-version", "1.103.0\n"),
    ] {
        let selected = world.inputs.read(Path::new(path)).unwrap();
        assert_eq!(selected.contents(world.inputs.deadline().unwrap()).unwrap(), expected);
        let retained = world.inputs.cached(Path::new(path)).unwrap();
        assert!(Arc::ptr_eq(&selected, &retained));
        let offer = selected.offer(world.inputs.deadline().unwrap()).unwrap();
        offer.check_current(world.inputs.deadline().unwrap()).unwrap();
    }
    world.inputs.check_current().unwrap();
    assert_eq!(world.inputs.captures.lock().unwrap().files.len(), 3);
}

#[test]
fn nested_noncooperating_raw_byte_drift_revokes_all_same_source_aliases() {
    for path in ["src/ci/channel", "src/version", "src/rust-compat-version"] {
        let world = world();
        let alias = Arc::clone(&world.source);
        let selected = world.inputs.read(Path::new(path)).unwrap();
        let original = selected.contents(world.inputs.deadline().unwrap()).unwrap();
        fs::write(world.source.path().join(path), b"changed nested raw input\n").unwrap();
        // The generic root-directory guard alone does not freeze nested bytes.
        world
            .inputs
            .selected_root
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .check_current(world.source.directory().unwrap())
            .unwrap();
        assert!(world.inputs.check_current().is_err());
        fs::write(world.source.path().join(path), original).unwrap();
        assert!(world.inputs.cached(Path::new(path)).is_err());
        assert!(alias.directory().is_err());
        assert!(world.scope.dispatcher().register_launch().is_err());
        assert!(selected.retained_descriptions() > 0);
    }
}

#[test]
fn late_uncaptured_text_cannot_create_a_new_producer_or_restore_source_access() {
    let world = world();
    let original = world.inputs.read(Path::new("src/ci/channel")).unwrap();
    assert!(world.inputs.cached(Path::new("src/version")).is_err());
    assert_eq!(world.inputs.captures.lock().unwrap().files.len(), 1);
    assert!(world.source.close_only_offer().is_err());
    assert!(original.retained_descriptions() > 0);
}

// These controls exercise the real before-Config Manager/Scope/physical stage.
// They deliberately do not fabricate an admitted Graph, native materialization,
// accepted namespace, Config completion, InputWorkClosed, Seed or SDK.
struct SourceWorld {
    original: Arc<SourceStage>,
    _directory: tempfile::TempDir,
}
fn source_world() -> SourceWorld {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().canonicalize().unwrap();
    // An invalid Bootstrap config is unrelated to the closed source/output lane.
    fs::write(root.join("bootstrap.toml"), b"this is not Bootstrap TOML [").unwrap();
    fs::create_dir(root.join(".cargo")).unwrap();
    fs::write(root.join(".cargo/config.toml"), b"[net]\noffline = true\n").unwrap();
    symlink("config.toml", root.join(".cargo/config")).unwrap();
    let output = root.join("output");
    let end = Instant::now() + Duration::from_secs(30);
    let owners = Arc::new(OwnedInputs::acquire(&root, &output, end).unwrap());
    owners.protect(&root).unwrap();
    let selection = IntentSelection {
        source_root: root.as_os_str().as_bytes().to_vec(),
        output_root: output.as_os_str().as_bytes().to_vec(),
        configured_targo: b"/existing-configured-seed/bin/cargo".to_vec(),
        configured_compiler: b"/existing-configured-seed/bin/trustc".to_vec(),
        environment: vec![(b"CARGO_NET_OFFLINE".to_vec(), b"true".to_vec())],
        budget_ns: 30_000_000_000,
    }; // selection DATA only; these spellings are not private program owners.
    let original = Arc::new(SourceStage::new(owners, selection, end));
    original.capture_root().unwrap();
    SourceWorld { original, _directory: directory }
}

#[test]
fn before_config_source_stage_retains_real_managers_and_exact_tool_selection() {
    let world = source_world();
    let original = Arc::clone(&world.original);
    let root = original.source().unwrap().path();
    original.check_current().unwrap();
    let SourceSelection::Complete(selection) = &original.selection else { unreachable!() };
    assert_eq!(selection.source_root, root.as_os_str().as_bytes());
    assert_eq!(selection.configured_targo, b"/existing-configured-seed/bin/cargo");
    assert_eq!(selection.configured_compiler, b"/existing-configured-seed/bin/trustc");
    assert!(!Manager::open(root).unwrap().status().unwrap().is_free());
    assert!(
        build_helper::trust_output_lock::OutputLock::try_acquire(&root.join("output"))
            .unwrap()
            .is_none()
    );
    // The stage retained the real owners, rather than merely their path DATA.
    assert_eq!(Arc::strong_count(&original.owners), 1);
    original.source().unwrap().directory().unwrap();
}

#[test]
fn before_config_observed_root_drift_permanently_revokes_scope_and_source_aliases() {
    let world = source_world();
    let alias = Arc::clone(world.original.owners.source.get().unwrap());
    let dispatch = world.original.owners.scope.lock().unwrap().as_ref().unwrap().dispatcher();
    let path = alias.path().join("new-unowned-namespace");
    fs::create_dir(&path).unwrap();
    assert!(world.original.check_current().is_err());
    fs::remove_dir(path).unwrap();
    assert!(world.original.check_current().is_err());
    assert!(alias.directory().is_err());
    assert!(dispatch.register_launch().is_err());
    assert!(world.original.selected.lock().unwrap().is_some());
    assert!(!Manager::open(alias.path()).unwrap().status().unwrap().is_free());
    assert!(
        build_helper::trust_output_lock::OutputLock::try_acquire(&alias.path().join("output"))
            .unwrap()
            .is_none()
    );
}

#[test]
fn before_config_root_capture_is_one_use_and_refusal_keeps_original_custody() {
    let world = source_world();
    let alias = Arc::clone(world.original.owners.source.get().unwrap());
    assert!(world.original.capture_root().is_err());
    assert!(world.original.check_current().is_err());
    assert!(alias.close_only_offer().is_err());
    assert!(world.original.selected.lock().unwrap().is_some());
    assert!(!Manager::open(alias.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn before_config_endpoint_never_extends_actual_owners_and_expiry_is_sticky() {
    let world = source_world();
    let source = Arc::clone(world.original.owners.source.get().unwrap());
    let later = world.original.owners.deadline + Duration::from_secs(30);
    let mut original = SourceStage::new(
        Arc::clone(&world.original.owners),
        match &world.original.selection {
            SourceSelection::Complete(selection) => selection.clone(),
            SourceSelection::Staged(_) => unreachable!(),
        },
        later,
    );
    assert_eq!(original.end, original.owners.deadline);
    original.capture_root().unwrap();
    original.end = Instant::now(); // restrict the actual accepted endpoint, never renew it.
    assert_eq!(original.check_current().unwrap_err().kind(), io::ErrorKind::TimedOut);
    original.end = later; // even a hostile attempted restoration cannot recover this issuer.
    assert!(original.check_current().is_err());
    assert!(world.original.check_current().is_err());
    assert!(source.directory().is_err());
}

#[test]
fn source_configuration_capture_retains_actual_nested_bytes_and_revokes_aliases_on_drift() {
    let world = source_world();
    let source = Arc::clone(world.original.owners.source.get().unwrap());
    let path = source.path().join(".cargo/config.toml");
    let observed = world.original.capture_configuration_input(&path).unwrap();
    assert!(
        matches!(observed, SourceRead::File { bytes, .. } if bytes == b"[net]\noffline = true\n")
    );
    fs::write(&path, b"[net]\noffline = false\n").unwrap();
    assert!(world.original.check_current().is_err());
    fs::write(&path, b"[net]\noffline = true\n").unwrap();
    assert!(source.directory().is_err());
    assert!(world.original.capture_configuration_input(&path).is_err());
}

#[test]
fn source_configuration_negative_discovery_is_not_reinterpreted_after_restore() {
    let world = source_world();
    let root = world.original.source().unwrap().path();
    let path = root.join(".cargo/missing-parent/optional.toml");
    assert!(world.original.capture_configuration_input(&path).unwrap() == SourceRead::Absent);
    fs::create_dir(root.join(".cargo/missing-parent")).unwrap();
    assert!(world.original.check_current().is_err());
    fs::remove_dir(root.join(".cargo/missing-parent")).unwrap();
    assert!(world.original.capture_configuration_input(&path).is_err());
    assert!(world.original.source().unwrap().check_current().is_err());
}

#[test]
fn source_configuration_never_opens_an_unowned_home_ancestor_or_link_root() {
    for link in [false, true] {
        let world = source_world();
        let source = Arc::clone(world.original.owners.source.get().unwrap());
        let path = if link {
            source.path().join(".cargo/config")
        } else {
            source.path().parent().unwrap().join("unowned-config-not-opened")
        };
        assert!(world.original.capture_configuration_input(&path).is_err());
        assert!(world.original.check_current().is_err());
        assert!(source.close_only_offer().is_err());
        assert!(!Manager::open(source.path()).unwrap().status().unwrap().is_free());
    }
}


fn staged_source_world() -> (SourceWorld, Arc<SourceStage>) {
    let world = source_world();
    let SourceSelection::Complete(prior) = &world.original.selection else { unreachable!() };
    let selection = StagedSelection {
        source_root: prior.source_root.clone(), output_root: prior.output_root.clone(),
        environment: prior.environment.clone(), budget_ns: prior.budget_ns,
    };
    let staged = Arc::new(SourceStage::from_selection(
        Arc::clone(&world.original.owners), SourceSelection::Staged(selection), world.original.end,
    ));
    staged.capture_root().unwrap();
    (world, staged)
}

#[test]
fn staged_source_refuses_config_before_any_payload_capture_and_revokes_real_aliases() {
    let (_world, original) = staged_source_world();
    let source = Arc::clone(original.owners.source.get().unwrap());
    let path = source.path().join(".cargo/config.toml");
    let population = original.selected.lock().unwrap().as_ref().unwrap().selected_population();
    assert!(original.capture_configuration_input(&path).is_err());
    assert_eq!(original.selected.lock().unwrap().as_ref().unwrap().selected_population(), population);
    assert!(original.check_current().is_err());
    assert!(source.directory().is_err());
    assert!(!Manager::open(source.path()).unwrap().status().unwrap().is_free());
    assert!(original.owners.scope.lock().unwrap().as_ref().unwrap().dispatcher().register_launch().is_err());
    // No staged bit, name or DATA reply was promoted to native acceptance.
    assert!(!original.programs_finalized.load(Ordering::Acquire));
}

#[test]
fn finalized_staged_program_data_cannot_replace_native_caller_cache_custody() {
    let (_world, original) = staged_source_world();
    // Private restriction-state fixture only; no Program/137/Root owner minted.
    original.programs_finalized.store(true, Ordering::Release);
    let source=Arc::clone(original.owners.source.get().unwrap());
    let population=original.selected.lock().unwrap().as_ref().unwrap().selected_population();
    assert!(original.capture_configuration_input(&source.path().join(".cargo/config.toml")).is_err());
    assert_eq!(original.selected.lock().unwrap().as_ref().unwrap().selected_population(),population);
    assert!(source.directory().is_err());
    assert!(!original.caller_cache.lock().unwrap().bound);
    assert!(!Manager::open(source.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn staged_root_narrowing_retains_both_actual_descriptions_and_the_shorter_bound() {
    let (_world, original) = staged_source_world();
    let source = Arc::clone(original.owners.source.get().unwrap());
    let end = Instant::now() + Duration::from_secs(5);
    original.narrow_root_before_configuration(end).unwrap();
    assert_eq!(original.selected.lock().unwrap().as_ref().unwrap().original_deadline(), end);
    assert_eq!(original.retained_roots.lock().unwrap().len(), 1);
    original.check_current().unwrap();
    source.directory().unwrap();
    // Narrowing physical custody is not final program ACK or permission to parse.
    assert!(!original.programs_finalized.load(Ordering::Acquire));
    assert!(original.narrow_root_before_configuration(end).is_err());
    assert_eq!(original.retained_roots.lock().unwrap().len(), 1);
    assert!(source.directory().is_err());
}

#[test]
fn pending_source_capture_data_blocks_config_and_preserves_actual_source_guards() {
    let world = source_world();
    let original = &world.original;
    let source = Arc::clone(original.owners.source.get().unwrap());
    let population = original.selected.lock().unwrap().as_ref().unwrap().selected_population();
    // Restriction DATA only. No138/139, native worker, live Graph or cache-lock
    // authority is fabricated by this existing physical Source/Scope fixture.
    *original.source_capture.lock().unwrap() = Some(Arc::new(vec![
        trust_resource_controller::bootstrap_graph::offline_preparation::ArchiveCandidate {
            relative: b"bootstrap/trust-stage0/dist/day/seed.tar.xz".to_vec(), sha256: [7; 32],
        }
    ]));
    assert!(original.capture_configuration_input(&source.path().join(".cargo/config.toml")).is_err());
    assert_eq!(original.selected.lock().unwrap().as_ref().unwrap().selected_population(), population);
    assert!(source.directory().is_err());
    assert!(!Manager::open(source.path()).unwrap().status().unwrap().is_free());
    assert!(original.source_capture.lock().unwrap().is_some());
}

#[test]
fn private_program_spelling_is_closed_explicit_data_under_the_observed_namespace() {
    let world = world();
    let reserved = ReservedPrograms {
        query: trust_resource_controller::bootstrap_graph::offline_preparation::ProgramSelectionQuery {
            key: query::OperationKey { graph: world.inputs.key.clone(), sequence: 1, operation: [91; 16] },
        },
        namespace: b"/output/native-child".to_vec(), remaining_root_ns: 1_000_000_000,
    }; // DATA fixture only: no actual reserved namespace or private program owner.
    for targo in ["targo", "cargo"] {
        for compiler in ["trustc", "rustc"] {
            let selected = program_selection(&reserved, targo.as_ref(), compiler.as_ref()).unwrap();
            assert_eq!(selected.configured_targo, format!("/output/native-child/bin/{targo}").as_bytes());
            assert_eq!(selected.configured_compiler, format!("/output/native-child/bin/{compiler}").as_bytes());
            assert!(selected.key == reserved.query.key);
        }
    }
    for bad in ["/canonical82/bin/cargo", "../cargo", "targo/", "cargo.exe", ""] {
        assert!(program_selection(&reserved, bad.as_ref(), "trustc".as_ref()).is_err());
    }
    assert!(program_selection(&reserved, "cargo".as_ref(), "/canonical82/bin/trustc".as_ref()).is_err());
}
