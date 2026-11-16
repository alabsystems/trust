// Copyright 2026 Andrew Yates
// These are owned request/artifact file fixtures, not LLVM/provider readiness.
use super::*;
use crate::utils::tests::TestCtx;

fn request(ctx: &TestCtx, name: &str, key: &str) -> BuildStamp {
    BuildStamp::new(&ctx.dir().join(name)).with_prefix("owner").add_stamp(key)
}

fn outputs(stamp: &BuildStamp) -> (PathBuf, PathBuf) {
    let root = stamp.path().parent().unwrap();
    let partial = root.join("build/partial.o");
    let installed = root.join("lib/installed.so");
    fs::create_dir_all(partial.parent().unwrap()).unwrap();
    fs::create_dir_all(installed.parent().unwrap()).unwrap();
    fs::write(&partial, b"same-request incremental work").unwrap();
    fs::write(&installed, b"installed output outside build").unwrap();
    (partial, installed)
}

#[test]
fn matching_generation_keeps_incremental_and_installed_data_but_invalidates_completion() {
    let ctx = TestCtx::new();
    let stamp = request(&ctx, "out", "known-a");
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let (partial, installed) = outputs(&stamp);
    stamp.write().unwrap();
    assert!(cached_enzyme(&stamp, &installed, Some("recorded fixture input")).is_some());
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    assert_eq!(fs::read(&partial).unwrap(), b"same-request incremental work");
    assert_eq!(fs::read(&installed).unwrap(), b"installed output outside build");
    assert!(cmake_generation_matches(&stamp));
    assert!(!stamp.path().exists());
    assert!(cached_enzyme(&stamp, &installed, Some("recorded fixture input")).is_none());
}

#[test]
fn changed_or_unknown_generation_removes_the_whole_output_including_installed_libraries() {
    let ctx = TestCtx::new();
    for unknown in [false, true] {
        let stamp = request(&ctx, if unknown { "unknown" } else { "changed" }, "known-a");
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        let (partial, installed) = outputs(&stamp);
        stamp.write().unwrap();
        let next = if unknown {
            stamp.clone()
        } else {
            BuildStamp::new(stamp.path().parent().unwrap())
                .with_prefix("owner")
                .add_stamp("known-b")
        };
        begin_cmake_miss(
            &next,
            if unknown { CmakeGeneration::Unknown } else { CmakeGeneration::Known },
        )
        .unwrap();
        assert!(!partial.exists());
        assert!(!installed.exists());
        assert!(!next.path().exists());
        assert_eq!(cmake_generation_matches(&next), !unknown);
        if unknown {
            assert!(!cmake_generation_record(&next).unwrap().path().exists());
        }
    }
}

#[test]
fn absent_malformed_and_nonregular_membership_cannot_admit_legacy_completion() {
    let ctx = TestCtx::new();
    for kind in ["missing", "malformed", "oversized", "directory"] {
        let stamp = request(&ctx, kind, "known");
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        let (partial, installed) = outputs(&stamp);
        stamp.write().unwrap();
        let record = cmake_generation_record(&stamp).unwrap();
        fs::remove_file(record.path()).unwrap();
        match kind {
            "missing" => {}
            "malformed" => fs::write(record.path(), b"legacy or malformed").unwrap(),
            "oversized" => fs::write(record.path(), vec![b'x'; record.stamp().len() + 1]).unwrap(),
            "directory" => fs::create_dir(record.path()).unwrap(),
            _ => unreachable!(),
        }
        assert!(stamp.is_up_to_date());
        assert!(cached_enzyme(&stamp, &installed, Some("recorded fixture input")).is_none());
        begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
        assert!(!partial.exists());
        assert!(!installed.exists());
        assert!(!stamp.path().exists());
        assert!(cmake_generation_matches(&stamp));
    }
}

#[test]
fn partial_known_work_can_resume_without_turning_membership_into_completion() {
    let ctx = TestCtx::new();
    let stamp = request(&ctx, "partial", "known");
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let (partial, installed) = outputs(&stamp);
    // The owner has not completed construction. No success/failure result or
    // provider evidence is fabricated: only incomplete on-disk work exists.
    assert!(!stamp.path().exists());
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    assert!(partial.is_file());
    assert!(installed.is_file());
    assert!(cmake_generation_matches(&stamp));
    assert!(cached_enzyme(&stamp, &installed, Some("recorded fixture input")).is_none());
    assert!(cached_enzyme(&stamp, &installed, None).is_none());
}

#[test]
fn invalid_root_and_completion_removal_failure_refuse_before_tree_mutation() {
    let ctx = TestCtx::new();
    let file_stamp = request(&ctx, "file-root", "known");
    let file_root = file_stamp.path().parent().unwrap();
    fs::write(file_root, b"outside the directory contract").unwrap();
    assert!(begin_cmake_miss(&file_stamp, CmakeGeneration::Known).is_err());
    assert!(!cmake_generation_matches(&file_stamp));
    assert_eq!(fs::read(file_root).unwrap(), b"outside the directory contract");

    let stamp = request(&ctx, "remove-error", "known");
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let (partial, installed) = outputs(&stamp);
    fs::create_dir(stamp.path()).unwrap();
    assert!(begin_cmake_miss(&stamp, CmakeGeneration::Unknown).is_err());
    assert!(stamp.path().is_dir());
    assert!(partial.is_file());
    assert!(installed.is_file());
    assert!(cmake_generation_matches(&stamp));
}

#[cfg(unix)]
#[test]
fn final_root_symlink_is_refused_before_outside_completion_or_data_changes() {
    let ctx = TestCtx::new();
    let outside = request(&ctx, "outside", "known");
    begin_cmake_miss(&outside, CmakeGeneration::Known).unwrap();
    let (partial, installed) = outputs(&outside);
    outside.write().unwrap();
    let record = cmake_generation_record(&outside).unwrap();
    let original = fs::read(record.path()).unwrap();
    let link = ctx.dir().join("linked-root");
    std::os::unix::fs::symlink(outside.path().parent().unwrap(), &link).unwrap();
    let linked = BuildStamp::new(&link).with_prefix("owner").add_stamp("known");
    assert!(!cmake_generation_matches(&linked));
    assert!(
        cached_enzyme(&linked, &link.join("lib/installed.so"), Some("recorded fixture input"))
            .is_none()
    );
    assert!(begin_cmake_miss(&linked, CmakeGeneration::Unknown).is_err());
    assert!(outside.is_up_to_date());
    assert!(partial.is_file());
    assert!(installed.is_file());
    assert_eq!(fs::read(record.path()).unwrap(), original);
}

#[test]
fn completion_requires_same_known_source_after_the_actual_action() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let output = temp.path().join("output");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&output).unwrap();
    fs::write(source.join("input"), b"first").unwrap();
    let before = observe_cmake_sources(&source, &output).unwrap().unwrap();
    let stamp = BuildStamp::new(&output).with_prefix("controlled-source").add_stamp(&before);
    complete_with_unchanged_cmake_source(&source, &output, Some(&before), || stamp.write())
        .unwrap();
    assert!(stamp.is_up_to_date());
    stamp.remove().unwrap();
    fs::write(source.join("input"), b"other").unwrap();
    complete_with_unchanged_cmake_source(&source, &output, Some(&before), || stamp.write())
        .unwrap();
    assert!(!stamp.path().exists());
    complete_with_unchanged_cmake_source(&source, &output, None, || stamp.write()).unwrap();
    assert!(!stamp.path().exists());
    assert!(reusable_cmake_inputs(None, Some("provider data"), Some("request data")).is_none());
    assert!(reusable_cmake_inputs(Some(&before), None, Some("request data")).is_none());
    assert!(reusable_cmake_inputs(Some(&before), Some("provider data"), None).is_none());
    let after = observe_cmake_sources(&source, &output).unwrap().unwrap();
    complete_with_unchanged_cmake_source(&source, &output, Some(&after), || stamp.write()).unwrap();
    assert!(stamp.is_up_to_date());
}

#[cfg(unix)]
#[test]
fn unknown_post_source_cannot_publish_completion() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let output = temp.path().join("output");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&output).unwrap();
    fs::write(source.join("input"), b"first").unwrap();
    let before = observe_cmake_sources(&source, &output).unwrap().unwrap();
    let name =
        std::ffi::CString::new(source.join("unsupported").as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: the CString owns a valid terminated pathname through this call.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let stamp = BuildStamp::new(&output).with_prefix("controlled-source").add_stamp(&before);
    complete_with_unchanged_cmake_source(&source, &output, Some(&before), || stamp.write())
        .unwrap();
    assert!(!stamp.path().exists());
}

#[test]
fn actual_source_bytes_change_owner_cache_and_generation_keys() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let output = temp.path().join("output");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("input"), b"first").unwrap();
    let before = observe_cmake_sources(&source, &output).unwrap().unwrap();
    // Provider/request strings are controlled data; only source is observed here.
    let inputs =
        reusable_cmake_inputs(Some(&before), Some("provider data"), Some("request data")).unwrap();
    let stamp = enzyme_stamp(&output, inputs.source, Some(inputs.dependency), inputs.request);
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let dylib = output.join("installed-plugin");
    fs::write(&dylib, b"controlled artifact").unwrap();
    stamp.write().unwrap();
    assert!(cached_enzyme(&stamp, &dylib, Some(inputs.dependency)).is_some());
    let modified = fs::metadata(source.join("input")).unwrap().modified().unwrap();
    fs::write(source.join("input"), b"other").unwrap();
    crate::utils::helpers::set_file_times(
        &source.join("input"),
        fs::FileTimes::new().set_modified(modified),
    )
    .unwrap();
    let after = observe_cmake_sources(&source, &output).unwrap().unwrap();
    assert_ne!(before, after);
    let changed = enzyme_stamp(&output, &after, Some(inputs.dependency), inputs.request);
    assert!(cached_enzyme(&changed, &dylib, Some(inputs.dependency)).is_none());
    assert!(!cmake_generation_matches(&changed));
    begin_cmake_miss(&changed, CmakeGeneration::Known).unwrap();
    assert!(!dylib.exists(), "a changed source cannot retain installed output");
    assert!(cmake_generation_matches(&changed));
    assert!(!changed.path().exists(), "request membership is not completion");
}
