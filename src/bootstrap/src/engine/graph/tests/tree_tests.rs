//! Trust: original finite namespace owners, actual callbacks and refusals.
use super::*;

fn setup() -> (tempfile::TempDir, PathBuf, tempfile::TempDir, PathBuf, Instant, Outcome) {
    let (directory, source) = root();
    let (output_directory, output) = root();
    fs::create_dir_all(source.join("package/src/empty")).unwrap();
    fs::write(source.join("package/Cargo.toml"), b"[package]\nname='original'\n").unwrap();
    fs::write(source.join("package/src/lib.rs"), b"mod leaf;\n").unwrap();
    fs::write(source.join("package/src/leaf.rs"), b"pub fn value()->u32{42}\n").unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(3).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    (directory, source, output_directory, output, deadline, original)
}
fn actor(name: &str) -> bool {
    isolated(name)
}

#[test]
fn complete_tree_drives_real_native_producer_validator_and_test_dependencies() {
    if actor(
        "engine::graph::native::tests::tree_tests::complete_tree_drives_real_native_producer_validator_and_test_dependencies",
    ) {
        return;
    }
    let (_directory, source, _out, output, deadline, original) = setup();
    // No hidden/cache/target exclusions may silently change completeness.
    for path in ["package/.hidden", "package/target", "package/.cache"] {
        fs::create_dir(source.join(path)).unwrap();
        fs::write(source.join(path).join("input"), path.as_bytes()).unwrap();
    }
    let graph = original.open_native_graph().unwrap();
    let inputs = graph.capture_source_tree(Path::new("package"), deadline).unwrap();
    assert_eq!(inputs.observations().len(), 6);
    let produced = graph
        .run_source_task(inputs, &[], deadline, |actual| {
            let mut owned = std::collections::BTreeMap::new();
            for (index, observation) in actual.observations().iter().enumerate() {
                owned.insert(observation.path.clone(), actual.read(index)?);
            }
            Ok::<_, GraphError>(owned)
        })
        .unwrap();
    assert_eq!(produced.value()[Path::new("package/src/leaf.rs")], b"pub fn value()->u32{42}\n");
    let validation = graph
        .run_source_task(
            graph.capture_source_tree(Path::new("package"), deadline).unwrap(),
            &[produced.completion()],
            deadline,
            |actual| {
                assert_eq!(actual.observations().len(), produced.value().len());
                for (index, observed) in actual.observations().iter().enumerate() {
                    assert_eq!(actual.read(index)?, produced.value()[&observed.path]);
                }
                Ok::<_, GraphError>(produced.value().len())
            },
        )
        .unwrap();
    let checked = graph
        .run_source_task(
            graph.capture_source_tree(Path::new("package/src/empty"), deadline).unwrap(),
            &[produced.completion(), validation.completion()],
            deadline,
            |actual| {
                assert!(actual.observations().is_empty());
                Ok::<_, GraphError>(*validation.value())
            },
        )
        .unwrap();
    assert_eq!(*checked.value(), 6);
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}

#[test]
fn additions_deletions_and_empty_directory_changes_are_terminal() {
    if actor(
        "engine::graph::native::tests::tree_tests::additions_deletions_and_empty_directory_changes_are_terminal",
    ) {
        return;
    }
    let (_directory, source, _out, _output, deadline, original) = setup();
    let graph = original.open_native_graph().unwrap();
    for mutation in 0..3 {
        let captured = graph.capture_source_tree(Path::new("package"), deadline).unwrap();
        match mutation {
            0 => fs::write(source.join("package/src/empty/new.rs"), b"new").unwrap(),
            1 => fs::remove_file(source.join("package/src/leaf.rs")).unwrap(),
            2 => fs::rename(source.join("package/src/empty"), source.join("package/src/moved"))
                .unwrap(),
            _ => unreachable!(),
        }
        assert!(graph.revalidate(&captured, deadline).is_err());
        match mutation {
            0 => fs::remove_file(source.join("package/src/empty/new.rs")).unwrap(),
            1 => {
                fs::write(source.join("package/src/leaf.rs"), b"pub fn value()->u32{42}\n").unwrap()
            }
            2 => fs::rename(source.join("package/src/moved"), source.join("package/src/empty"))
                .unwrap(),
            _ => unreachable!(),
        }
        assert!(
            graph.revalidate(&captured, deadline).is_err(),
            "restoration cannot clear a refused owner"
        );
    }
    let empty = graph.capture_source_tree(Path::new("package/src/empty"), deadline).unwrap();
    assert!(empty.observations().is_empty());
    fs::write(source.join("package/src/empty/late"), b"late").unwrap();
    assert!(graph.revalidate(&empty, deadline).is_err());
    assert!(graph.revalidate(&empty, deadline).is_err());
    println!("native-graph-checked");
}

#[test]
fn capture_race_rename_aba_and_late_callback_keep_failure_and_output() {
    if actor(
        "engine::graph::native::tests::tree_tests::capture_race_rename_aba_and_late_callback_keep_failure_and_output",
    ) {
        return;
    }
    let (_directory, source, _out, output, deadline, original) = setup();
    let graph = original.open_native_graph().unwrap();
    let raced = std::thread::scope(|threads| {
        let (ready, observed) = std::sync::mpsc::channel();
        let (done, resume) = std::sync::mpsc::channel();
        let source = &source;
        let writer = threads.spawn(move || {
            observed.recv_timeout(Duration::from_secs(10)).unwrap();
            fs::rename(source.join("package/src/leaf.rs"), source.join("package/src/held.rs"))
                .unwrap();
            fs::rename(source.join("package/src/held.rs"), source.join("package/src/leaf.rs"))
                .unwrap();
            done.send(()).unwrap();
        });
        let result = super::super::tree::capture_with(
            &original,
            Path::new("package"),
            deadline,
            move |path| {
                if path == Path::new("package/src") {
                    ready.send(()).unwrap();
                    resume.recv_timeout(Duration::from_secs(10)).unwrap();
                }
            },
        );
        writer.join().unwrap();
        result
    });
    assert!(raced.is_err(), "restored directory names cannot clear capture-time ABA");
    let captured = graph.capture_source_tree(Path::new("package"), deadline).unwrap();
    let failed = graph
        .run_source_task(captured, &[], deadline, |actual| {
            assert!(!actual.read(0).unwrap().is_empty());
            fs::write(source.join("package/src/empty/new"), b"late input").unwrap();
            Ok::<_, GraphError>(b"actual callback output".to_vec())
        })
        .err()
        .unwrap();
    assert!(matches!(failed.error(), TaskError::Graph(_)));
    assert_eq!(failed.returned_value().unwrap(), b"actual callback output");
    assert_eq!(failed.observations().len(), 3);
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}

#[test]
fn special_symlink_alias_size_depth_and_descriptor_populations_refuse() {
    if actor(
        "engine::graph::native::tests::tree_tests::special_symlink_alias_size_depth_and_descriptor_populations_refuse",
    ) {
        return;
    }
    let (_directory, source, _out, _output, deadline, original) = setup();
    let graph = original.open_native_graph().unwrap();
    let link = source.join("package/link");
    std::os::unix::fs::symlink("src/lib.rs", &link).unwrap();
    assert!(graph.capture_source_tree(Path::new("package"), deadline).is_err());
    fs::remove_file(&link).unwrap();
    let fifo = std::ffi::CString::new(link.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
    assert!(graph.capture_source_tree(Path::new("package"), deadline).is_err());
    fs::remove_file(&link).unwrap();
    fs::hard_link(source.join("package/src/lib.rs"), &link).unwrap();
    assert!(graph.capture_source_tree(Path::new("package"), deadline).is_err());
    fs::remove_file(&link).unwrap();
    fs::File::create(&link).unwrap().set_len(super::super::MAX_BYTES + 1).unwrap();
    assert!(graph.capture_source_tree(Path::new("package"), deadline).is_err());
    fs::remove_file(&link).unwrap();
    let deep = std::iter::repeat_n("d", 33).collect::<PathBuf>();
    fs::create_dir_all(source.join("package").join(&deep)).unwrap();
    assert!(graph.capture_source_tree(Path::new("package"), deadline).is_err());
    fs::remove_dir_all(source.join("package/d")).unwrap();
    for group in ["a", "b"] {
        fs::create_dir(source.join(format!("package/{group}"))).unwrap();
        for index in 0..48 {
            fs::create_dir(source.join(format!("package/{group}/empty{index}"))).unwrap();
        }
    }
    let refused = graph.capture_source_tree(Path::new("package"), deadline).err().unwrap();
    assert!(matches!(refused, GraphError::InvalidReadSet(reason) if reason.contains("descriptor")));
    assert!(graph.capture_source_tree(Path::new("package/../package"), deadline).is_err());
    println!("native-graph-checked");
}

#[test]
fn actual_nofile_256_counts_files_empty_directories_and_intermediate_owners() {
    if actor(
        "engine::graph::native::tests::tree_tests::actual_nofile_256_counts_files_empty_directories_and_intermediate_owners",
    ) {
        return;
    }
    // Change only this isolated actor's actual kernel soft limit; no test
    // status or requested number stands in for available native descriptors.
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) }, 0);
    let mut limit = unsafe { limit.assume_init() };
    assert!(limit.rlim_cur >= 256, "the native fixture requires an actual 256-FD boundary");
    limit.rlim_cur = 256;
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
    let (_directory, source, _out, output, deadline, original) = setup();
    fs::create_dir(source.join("package/nested")).unwrap();
    fs::create_dir(source.join("package/nested/empty")).unwrap();
    for index in 0..5 {
        fs::create_dir(source.join(format!("package/nested/group{index}"))).unwrap();
    }
    for index in 0..86 {
        fs::write(
            source.join(format!("package/nested/group{}/file{index}", index % 5)),
            b"original",
        )
        .unwrap();
    }
    let graph = original.open_native_graph().unwrap();
    let captured = graph.capture_source_tree(Path::new("package/nested"), deadline).unwrap();
    assert_eq!(captured.observations().len(), 86);
    graph.revalidate(&captured, deadline).unwrap();
    drop(captured);
    // One source-root + two intermediate/selected + six empty/group directory
    // owners +87 file owners is exactly the retained descriptor cap of96.
    fs::write(source.join("package/nested/group0/final"), b"original").unwrap();
    let complete = graph
        .run_source_task(
            graph.capture_source_tree(Path::new("package/nested"), deadline).unwrap(),
            &[],
            deadline,
            |actual| {
                assert_eq!(actual.observations().len(), 87);
                actual.read(0)
            },
        )
        .unwrap();
    assert_eq!(complete.value(), b"original");
    drop(complete);
    fs::write(source.join("package/nested/group1/too-many"), b"original").unwrap();
    let refused = graph.capture_source_tree(Path::new("package/nested"), deadline).err().unwrap();
    assert!(matches!(refused, GraphError::InvalidReadSet(reason) if reason.contains("descriptor")));
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}

#[test]
fn original_output_inside_selected_source_tree_refuses_before_task() {
    if actor(
        "engine::graph::native::tests::tree_tests::original_output_inside_selected_source_tree_refuses_before_task",
    ) {
        return;
    }
    let (_directory, source) = root();
    fs::create_dir(source.join("package")).unwrap();
    let output = source.join("package/target");
    let deadline = Instant::now() + Duration::from_secs(30);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(2).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    assert!(matches!(
        graph.capture_source_tree(Path::new("package"), deadline),
        Err(GraphError::OriginalOwner(_))
    ));
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}
