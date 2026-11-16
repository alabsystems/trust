use super::*;

#[test]
fn actual_parsed_parallel_knobs_cannot_exceed_the_enclosing_limit() {
    let context = crate::utils::tests::TestCtx::new();
    let mut config = context
        .config("build")
        .with_default_toml_config(
            "[build]\njobs = 32\n[llvm]\nlink-jobs = 64\n[rust]\nparallel-frontend-threads = 16\n",
        )
        .create_config();
    let mut callback = |_: Preparation<'_>| Err("test policy never executes work".into());
    let policy = Policy {
        ceiling: NonZeroU32::new(2).unwrap(),
        shims: None,
        before_steps: &mut callback,
        scope: None,
    };
    policy.limit(&mut config);
    assert_eq!(
        (config.jobs, config.llvm_link_jobs, config.rust_parallel_frontend_threads),
        (Some(2), Some(2), Some(2))
    );
    for value in [None, Some(0), Some(1), Some(32)] {
        config.jobs = value;
        config.llvm_link_jobs = value;
        config.rust_parallel_frontend_threads = value;
        policy.limit(&mut config);
        let expected = if value == Some(1) { Some(1) } else { Some(2) };
        assert_eq!(
            (config.jobs, config.llvm_link_jobs, config.rust_parallel_frontend_threads),
            (expected, expected, expected)
        );
    }
}

#[test]
#[cfg(unix)]
fn non_utf8_arguments_refuse_before_scheduler_installation_or_callbacks() {
    use std::os::unix::ffi::OsStringExt;
    let request = Request::new(vec![OsString::from_vec(vec![0xff])], NonZeroU32::new(1).unwrap());
    let result = run(request, jobserver_utils::Jobserver::new(0).unwrap(), |_| {
        panic!("invalid argument reached execution policy")
    });
    assert!(matches!(result, Err(error) if error.contains("UTF-8")));
}
