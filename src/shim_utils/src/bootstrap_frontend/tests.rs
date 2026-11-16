use super::*;

#[test]
fn explicit_config_including_zero_preserves_existing_policy() {
    assert_eq!(bootstrap_seed_frontend_ceiling(None, Some(28)), Some(28));
    for configured in [0, 1, 7, 28] {
        assert_eq!(bootstrap_seed_frontend_ceiling(Some(configured), Some(28)), None);
    }
    assert_eq!(bootstrap_seed_frontend_ceiling(None, None), None);
    assert_eq!(bootstrap_seed_frontend_ceiling(None, Some(0)), None);
}

#[test]
fn requires_both_real_unverified_seed_and_validated_scheduler() {
    for seed in [false, true] {
        for scheduler in [false, true] {
            assert_eq!(
                bootstrap_seed_frontend_threads(&[], seed, scheduler, Some(OsStr::new("28"))),
                Ok((seed && scheduler).then_some(28))
            );
        }
    }
    assert_eq!(bootstrap_seed_frontend_threads(&[], true, true, None), Ok(None));
}

#[test]
fn finalized_explicit_threads_win_in_every_supported_spelling() {
    for words in [
        vec!["-Zthreads=1"],
        vec!["-Z", "threads=7"],
        vec!["-Zthreads", "4"],
        vec!["-Z", "threads", "4"],
    ] {
        let args = words.into_iter().map(OsString::from).collect::<Vec<_>>();
        assert_eq!(
            bootstrap_seed_frontend_threads(&args, true, true, Some(OsStr::new("28"))),
            Ok(None)
        );
    }
}

#[test]
fn potential_never_uses_current_jobs_or_host_load() {
    // The same host potential is selected across distinct GNU supplies;
    // neither current token availability nor generated job count is input.
    for _current_jobs in [1, 7, 21, 28] {
        assert_eq!(
            bootstrap_seed_frontend_threads(&[], true, true, Some(OsStr::new("28"))),
            Ok(Some(28))
        );
    }
    for invalid in ["0", "-1", " 7", "7 ", "4294967296", ""] {
        assert!(
            bootstrap_seed_frontend_threads(&[], true, true, Some(OsStr::new(invalid))).is_err()
        );
    }
}
