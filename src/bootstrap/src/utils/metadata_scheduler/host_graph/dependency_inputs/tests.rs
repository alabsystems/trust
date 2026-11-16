use std::fs;

use super::*;

fn until() -> Instant {
    Instant::now() + Duration::from_secs(20)
}
fn full_arguments(source: &Path, config: &Path) -> Vec<OsString> {
    vec![
        "build".into(),
        "--src".into(),
        source.as_os_str().to_owned(),
        "--config".into(),
        config.as_os_str().to_owned(),
    ]
}
#[test]
fn real_source_lease_precedes_layout_reads_and_actual_selected_output_guard() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let config = source.join("bootstrap.toml");
    let output = source.join("selected-output");
    fs::write(&config, format!("[build]\nbuild-dir = '{}'\n", output.display())).unwrap();
    let original = SourceInputs::acquire(&source, until()).unwrap();
    assert!(!Manager::open(&source).unwrap().status().unwrap().is_free());
    assert!(!output.exists(), "source acquisition must not guess or create output");
    let (owned, layout) =
        original.select_xpy_output(&source, &full_arguments(&source, &config)).unwrap();
    assert_eq!(layout.source(), source);
    assert_eq!(layout.output(), output);
    owned.command.check_original_source(&source).unwrap();
    assert!(owned.scope.lock().unwrap().is_none(), "layout cannot withhold a source");
    assert!(owned.source.get().is_none(), "layout cannot mint protected source custody");
    assert!(build_helper::trust_output_lock::OutputLock::try_acquire(&output).unwrap().is_none());
    drop(owned);
    assert!(Manager::open(&source).unwrap().status().unwrap().is_free());
    assert!(build_helper::trust_output_lock::OutputLock::try_acquire(&output).unwrap().is_some());
}
#[test]
fn original_layout_cannot_replace_source_or_claim_a_contended_output() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let foreign = tempfile::tempdir().unwrap();
    let foreign_source = foreign.path().canonicalize().unwrap();
    let config = source.join("bootstrap.toml");
    let output = source.join("selected-output");
    fs::write(&config, format!("[build]\nbuild-dir = '{}'\n", output.display())).unwrap();
    let error = SourceInputs::acquire(&source, until())
        .unwrap()
        .select_xpy_output(
            &source,
            &full_arguments(&foreign_source, &source.join("foreign-config-must-not-be-read")),
        )
        .err()
        .expect("foreign parser source cannot supply the held original source");
    assert!(error.to_string().contains("different source owner"));
    assert!(!output.exists());
    assert!(Manager::open(&source).unwrap().status().unwrap().is_free());
    let held = build_helper::trust_output_lock::OutputLock::try_acquire(&output).unwrap().unwrap();
    let error = SourceInputs::acquire(&source, until())
        .unwrap()
        .select_xpy_output(&source, &full_arguments(&source, &config))
        .err()
        .expect("actual output lock must precede source withholding");
    assert_eq!(error.kind(), io::ErrorKind::WouldBlock);
    assert!(Manager::open(&source).unwrap().status().unwrap().is_free());
    assert!(build_helper::trust_output_lock::OutputLock::try_acquire(&output).unwrap().is_none());
    drop(held);
}
#[test]
fn source_layout_refuses_nonfull_or_expired_work_without_opening_output() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let config = source.join("bootstrap.toml");
    let output = source.join("selected-output");
    fs::write(&config, format!("[build]\nbuild-dir = '{}'\n", output.display())).unwrap();
    for extra in [vec!["--dry-run"], vec!["--stage=1", "compiler/rustc"]] {
        let mut arguments = full_arguments(&source, &config);
        arguments.extend(extra.iter().map(OsString::from));
        assert!(
            SourceInputs::acquire(&source, until())
                .unwrap()
                .select_xpy_output(&source, &arguments)
                .is_err()
        );
        assert!(Manager::open(&source).unwrap().status().unwrap().is_free());
        assert!(!output.exists());
    }
    let mut original = SourceInputs::acquire(&source, until()).unwrap();
    original.deadline = Instant::now();
    let error = original
        .select_xpy_output(&source, &full_arguments(&source, &source.join("never-read")))
        .err()
        .expect("expired original deadline precedes every config read");
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert!(Manager::open(&source).unwrap().status().unwrap().is_free());
    assert!(!output.exists());
}
#[test]
fn no_explicit_src_staging_discovers_actual_foreign_worktree_and_never_compiled_location() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let _repo = gix::init(&source).unwrap();
    fs::create_dir_all(source.join("src/bootstrap")).unwrap();
    fs::write(source.join("src/stage0"), "native source marker\n").unwrap();
    let config = source.join("bootstrap.toml");
    let output = source.join("selected-output");
    fs::write(&config, format!("[build]\nbuild-dir = '{}'\n", output.display())).unwrap();
    // An unborn repository must refuse source identity, not guess the
    // control image's compile-time CARGO_MANIFEST_DIR.
    let arguments = vec!["build".into(), "--config".into(), config.as_os_str().to_owned()];
    let original = SourceInputs::acquire(&source, until()).unwrap();
    assert!(
        original.select_xpy_output_at(&source, &arguments, &source.join("src/bootstrap")).is_err()
    );
    assert!(!output.exists());
    let repo = gix::open_opts(&source, gix::open::Options::isolated()).unwrap();
    let tree = repo.write_object(&gix::objs::Tree { entries: Vec::new() }).unwrap();
    let mut buffer = gix::date::parse::TimeBuf::default();
    let signature = gix::actor::Signature {
        name: "native source".into(),
        email: "source@example.invalid".into(),
        time: gix::date::Time { seconds: 1_600_000_000, offset: 0 },
    };
    let signature = signature.to_ref(&mut buffer);
    repo.commit_as(
        signature,
        signature,
        "HEAD",
        "native fixture",
        tree.detach(),
        std::iter::empty::<gix::ObjectId>(),
    )
    .unwrap();
    let compiled = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
    assert_ne!(source, compiled.canonicalize().unwrap());
    let original = SourceInputs::acquire(&source, until()).unwrap();
    let (owned, layout) =
        original.select_xpy_output_at(&source, &arguments, &source.join("src/bootstrap")).unwrap();
    assert_eq!(layout.source(), source);
    assert_eq!(layout.output(), output);
    owned.command.check_original_source(&source).unwrap();
    assert!(build_helper::trust_output_lock::OutputLock::try_acquire(&output).unwrap().is_none());
}
#[test]
fn actual_input_guards_precede_withholding_and_protected_source_binding() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let out = root.path().join("out");
    let owned = OwnedInputs::acquire(&source, &out, until()).unwrap();
    owned.command.check_original_source(&source).unwrap();
    assert!(!Manager::open(&source).unwrap().status().unwrap().is_free());
    owned.protect(&source).unwrap();
    owned.check().unwrap();
    assert_eq!(owned.source.get().unwrap().path(), source);
    assert!(owned.command.check_original_source(&source).is_err());
    drop(owned);
    // Dropping actual local guards is never a native closure/release.
    assert!(!Manager::open(&source).unwrap().status().unwrap().is_free());
}
#[test]
fn busy_output_refuses_before_source_withholding_and_releases_only_unused_lease() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let out = root.path().join("out");
    let _held = build_helper::trust_output_lock::OutputLock::try_acquire(&out).unwrap().unwrap();
    let error =
        OwnedInputs::acquire(&source, &out, until()).err().expect("actual output contention");
    assert_eq!(error.kind(), io::ErrorKind::WouldBlock);
    assert!(Manager::open(&source).unwrap().status().unwrap().is_free());
}
#[test]
fn actual_output_exclusion_survives_refused_local_join() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let out = source.join("out");
    let owned = OwnedInputs::acquire(&source, &out, until()).unwrap();
    owned.protect(&source).unwrap();
    let OwnedInputs { command, output, scope, source: held_source, .. } = owned;
    let scope = scope.into_inner().unwrap().unwrap();
    let pending = scope.dispatcher().register_worker().unwrap();
    let refused = join_local_inputs(scope, command, output)
        .err()
        .expect("actual unlaunched worker cannot join");
    assert!(
        build_helper::trust_output_lock::OutputLock::try_acquire(&out).unwrap().is_none(),
        "refused join must retain actual output exclusion"
    );
    assert!(!Manager::open(&source).unwrap().status().unwrap().is_free());
    drop(pending);
    drop(refused);
    drop(held_source);
}
#[test]
fn expired_or_noncanonical_input_selection_cannot_acquire_custody() {
    let root = tempfile::tempdir().unwrap();
    let source = root.path().canonicalize().unwrap();
    let out = root.path().join("out");
    assert!(OwnedInputs::acquire(&source, &out, Instant::now()).is_err());
    assert!(!out.exists());
    assert!(OwnedInputs::acquire(Path::new("relative"), &out, until()).is_err());
    assert!(OwnedInputs::acquire(&source, &source.join(".."), Instant::now()).is_err());
}
