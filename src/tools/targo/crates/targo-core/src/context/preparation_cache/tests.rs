//! Real GlobalContext selection and physical capture only. There is no fake
//! native Root/Graph, accepted137, SourceCacheGuard, Seed or SDK owner here.
use super::*;
use std::os::fd::AsRawFd as _;

fn context_fixture() -> (tempfile::TempDir, GlobalContext, Selection) {
    let root = tempfile::tempdir().unwrap();
    let root_path = root.path().canonicalize().unwrap();
    let source = root_path.join("source");
    let home = root_path.join("home");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&home).unwrap();
    let environment = cargo_util::EnvironmentInputs::from_variables([
        (OsString::from("CARGO_HOME"), home.as_os_str().to_owned()),
        (OsString::from("CARGO_NET_OFFLINE"), OsString::from("true")),
    ])
    .unwrap();
    let mut context = GlobalContext::new(Shell::new(), source.clone(), home.clone());
    context.env = Env::from_selected(&environment);
    let selection = Selection {
        source,
        home,
        environment,
    };
    (root, context, selection)
}

#[test]
fn actual_context_home_issues_one_readonly_original_with_existing_accounted_capture() {
    let (_root, context, selection) = context_fixture();
    let end = Instant::now() + std::time::Duration::from_secs(30);
    let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
    let held = selection.capture(&context, &budget, end).unwrap();
    assert_eq!(held.path(), context.home().as_path_unlocked());
    let fd = held.descriptor(end).unwrap();
    assert_eq!(
        unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) } & libc::O_ACCMODE,
        libc::O_RDONLY
    );
    assert!(held.original_identity(end).unwrap().inode != 0);
    selection.check(&context).unwrap();
    held.validate(end).unwrap();
}

#[test]
fn changed_home_cwd_full_environment_and_preloaded_config_cannot_capture() {
    let (_root, mut context, selection) = context_fixture();
    context.cwd = context.cwd.join("changed");
    assert!(selection.check(&context).is_err());
    let (_root, mut context, selection) = context_fixture();
    context.home_path = Filesystem::new(context.cwd.clone());
    assert!(selection.check(&context).is_err());
    let (_root, mut context, selection) = context_fixture();
    context.env = Env::from_map(Default::default());
    assert!(selection.check(&context).is_err());
    let (_root, mut context, selection) = context_fixture();
    context.set_search_stop_path(context.cwd.clone());
    assert!(selection.check(&context).is_err());
    let (_root, context, selection) = context_fixture();
    context.set_values(Default::default()).unwrap();
    assert!(selection.check(&context).is_err());
}

#[test]
fn actual_maintained_selector_keeps_explicit_empty_compatibility_home_precedence() {
    let (root, mut context, mut selection) = context_fixture();
    let os_home = root.path().canonicalize().unwrap();
    fs::create_dir(os_home.join(".cargo")).unwrap();
    let native = os_home.join("native");
    fs::create_dir(&native).unwrap();
    let environment = cargo_util::EnvironmentInputs::from_variables([
        (OsString::from("CARGO_HOME"), OsString::new()),
        (OsString::from("TARGO_HOME"), native.into_os_string()),
        (OsString::from("HOME"), os_home.as_os_str().to_owned()),
        (OsString::from("CARGO_NET_OFFLINE"), OsString::from("true")),
    ])
    .unwrap();
    context.env = Env::from_selected(&environment);
    context.home_path = Filesystem::new(os_home.join(".cargo"));
    selection.home = context.home_path.as_path_unlocked().into();
    selection.environment = environment;
    selection.check(&context).unwrap();
    let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
    selection
        .capture(
            &context,
            &budget,
            Instant::now() + std::time::Duration::from_secs(30),
        )
        .unwrap();
}

#[test]
fn empty_home_snapshot_uses_the_maintained_os_fallback_without_process_env_mutation() {
    let (_root, mut context, mut selection) = context_fixture();
    let fallback = ::home::home_dir().expect("maintained OS home fallback");
    assert!(fallback.is_absolute());
    let environment = cargo_util::EnvironmentInputs::from_variables([
        (OsString::from("CARGO_HOME"), OsString::new()),
        (
            OsString::from("TARGO_HOME"),
            selection
                .source
                .join("ignored-native-home")
                .into_os_string(),
        ),
        (OsString::from("HOME"), OsString::new()),
        (OsString::from("CARGO_NET_OFFLINE"), OsString::from("true")),
    ])
    .unwrap();
    context.env = Env::from_selected(&environment);
    context.home_path = Filesystem::new(fallback.join(".cargo"));
    selection.home = context.home_path.as_path_unlocked().into();
    selection.environment = environment;
    // HOME="" in this immutable context is absent for OS-home selection. The
    // actual Selection guard must agree with the ordinary maintained fallback;
    // no process-global environment is changed.
    selection.check(&context).unwrap();
}

#[test]
fn absent_or_linked_selected_home_is_refused_without_retargeting_the_context_fixture() {
    let (_root, context, selection) = context_fixture();
    let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
    fs::remove_dir(&selection.home).unwrap();
    assert!(
        selection
            .capture(
                &context,
                &budget,
                Instant::now() + std::time::Duration::from_secs(30)
            )
            .is_err()
    );
    std::os::unix::fs::symlink(&selection.source, &selection.home).unwrap();
    assert!(
        selection
            .capture(
                &context,
                &budget,
                Instant::now() + std::time::Duration::from_secs(30)
            )
            .is_err()
    );
    assert_eq!(context.home().as_path_unlocked(), selection.home);
}
