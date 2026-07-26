use std::process::Command;

#[test]
fn path_identity_toctou_walkthrough_runs() {
    let stdout = run_bin(env!("CARGO_BIN_EXE_path_identity_toctou"));

    assert_key_values(&stdout, "walkthrough", &["path_identity_toctou"]);
    #[cfg(unix)]
    {
        assert_exact_keys(
            &stdout,
            &[
                "walkthrough",
                "scratch",
                "checked_path",
                "safe_file",
                "swapped_file",
                "pre_link",
                "post_link",
                "pre_file_id",
                "post_file_id",
                "observed",
                "result",
            ],
        );
        assert_no_key(&stdout, "unsupported");
        assert_key_values(&stdout, "pre_link", &["safe.txt"]);
        assert_key_values(&stdout, "post_link", &["swapped.txt"]);
        assert_key_values(&stdout, "observed", &["swapped"]);
        assert_key_values(&stdout, "result", &["toctou-demonstrated"]);
        let pre_id = single_key_value(&stdout, "pre_file_id");
        let post_id = single_key_value(&stdout, "post_file_id");
        assert_unix_file_id(pre_id, &stdout);
        assert_unix_file_id(post_id, &stdout);
        assert_ne!(
            pre_id, post_id,
            "path identity walkthrough should prove the checked path changed file identity\nstdout:\n{stdout}"
        );
    }
    #[cfg(not(unix))]
    {
        assert_exact_keys(&stdout, &["walkthrough", "unsupported"]);
        assert_key_values(&stdout, "unsupported", &["non-unix"]);
        assert_no_key(&stdout, "result");
    }
}

#[test]
fn byte_utf8_walkthrough_runs() {
    let stdout = run_bin(env!("CARGO_BIN_EXE_byte_utf8_walkthrough"));

    assert_key_values(&stdout, "walkthrough", &["byte_utf8"]);
    #[cfg(unix)]
    {
        assert_no_key(&stdout, "unsupported");
        assert_key_values(&stdout, "filename_hex", &["6e6f6e5f757466385fff5f6e616d65"]);
        assert_key_values(&stdout, "payload_hex", &["7061796c6f61643af0288c280a"]);
        assert_key_values(&stdout, "lossy_payload_had_replacement", &["yes"]);
        assert_key_values(&stdout, "strict_filename_utf8", &["error"]);
        assert_key_values(&stdout, "read_to_string_error", &["InvalidData"]);
        assert_key_values(&stdout, "roundtrip_payload_bytes", &["ok"]);
        assert_key_values(&stdout, "result", &["non-utf8-demonstrated"]);
        match key_values(&stdout, "filename_creation").as_slice() {
            ["supported"] => {
                assert_exact_keys(
                    &stdout,
                    &[
                        "walkthrough",
                        "scratch",
                        "filename_hex",
                        "payload_hex",
                        "lossy_payload_had_replacement",
                        "filename_creation",
                        "path_to_str",
                        "lossy_filename_had_replacement",
                        "roundtrip_filename_bytes",
                        "strict_filename_utf8",
                        "read_to_string_error",
                        "roundtrip_payload_bytes",
                        "result",
                    ],
                );
                assert_key_values(&stdout, "path_to_str", &["none"]);
                assert_key_values(&stdout, "lossy_filename_had_replacement", &["yes"]);
                assert_key_values(&stdout, "roundtrip_filename_bytes", &["ok"]);
            }
            ["unsupported"] => {
                assert_exact_keys(
                    &stdout,
                    &[
                        "walkthrough",
                        "scratch",
                        "filename_hex",
                        "payload_hex",
                        "lossy_payload_had_replacement",
                        "filename_creation",
                        "filename_create_error",
                        "filename_create_raw_os_error",
                        "path_to_str",
                        "lossy_filename_had_replacement",
                        "roundtrip_filename_bytes",
                        "strict_filename_utf8",
                        "read_to_string_error",
                        "roundtrip_payload_bytes",
                        "result",
                    ],
                );
                assert_key_values(&stdout, "path_to_str", &["skipped"]);
                assert_key_values(&stdout, "lossy_filename_had_replacement", &["skipped"]);
                assert_key_values(&stdout, "roundtrip_filename_bytes", &["skipped"]);
            }
            actual => panic!(
                "stdout did not contain exactly one supported/unsupported filename_creation value; got {actual:?}\nstdout:\n{stdout}"
            ),
        }
    }
    #[cfg(not(unix))]
    {
        assert_exact_keys(&stdout, &["walkthrough", "unsupported"]);
        assert_key_values(&stdout, "unsupported", &["non-unix"]);
        assert_no_key(&stdout, "result");
    }
}

#[test]
fn additional_hardened_walkthroughs_run() {
    let stdout = run_bin(env!("CARGO_BIN_EXE_additional_walkthroughs"));

    assert_key_values(
        &stdout,
        "walkthrough",
        &[
            "permissions",
            "raw_path_re_resolution",
            "error_discard_integrity",
            "panic_boundary",
            "process_sigpipe",
            "cli_args",
            "trust_domain_order",
            "unsafe_ffi_boundary_inventory",
            "ffi_boundary_inventory",
        ],
    );

    #[cfg(unix)]
    {
        assert_exact_keys(
            &stdout,
            &[
                "walkthrough",
                "scratch",
                "create_parent_file_id",
                "create_parent_identity_verified",
                "create_new_requested_mode",
                "create_new_group_other_bits",
                "chmod_file_id_before",
                "chmod_file_id_after",
                "chmod_identity_stable",
                "chmod_window_start_mode",
                "chmod_window_final_mode",
                "create_dir_requested_mode",
                "create_dir_creation_mode",
                "chmod_change_observed",
                "rootless_scope",
                "result",
                "walkthrough",
                "scratch",
                "checked_path",
                "initial_target",
                "replacement_target",
                "pre_canonical_leaf",
                "post_canonical_leaf",
                "pre_file_id",
                "post_file_id",
                "pre_read",
                "post_read",
                "raw_path_re_resolved",
                "raw_path_scope",
                "result",
                "walkthrough",
                "scratch",
                "expected_len",
                "discarded_remove_error",
                "discarded_canonicalize_error",
                "checked_read_error",
                "discarded_read_error",
                "discarded_fallback_len",
                "fallback_matches_expected",
                "checked_decision",
                "fallback_decision",
                "integrity_check",
                "result",
                "walkthrough",
                "scratch",
                "safe_metadata",
                "safe_utf8",
                "panic_hook",
                "caught_panics",
                "caught_panic_count",
                "panic_payloads_escaped",
                "result",
                "walkthrough",
                "closed_stream_write_error",
                "sigpipe_child_stdout_closed",
                "sigpipe_child_exit",
                "broken_pipe_handled",
                "result",
                "walkthrough",
                "parent_args_os_count",
                "cli_child_mode",
                "cli_child_arg_count",
                "cli_child_space_arg",
                "cli_child_invalid_arg_hex",
                "cli_child_invalid_arg_to_str",
                "cli_child_strict_utf8",
                "result",
                "walkthrough",
                "scratch",
                "rootless_root_metadata",
                "rootless_root_canonicalize",
                "rootless_user_probe",
                "rootless_group_probe",
                "rootless_plugin_metadata",
                "rootless_plugin_canonicalize",
                "rootless_plugin_read",
                "pre_privilege_probe_order",
                "privileged_ops",
                "privileged_ops_executed",
                "privileged_ops_mode",
                "root_transition_effect",
                "uid_gid_transition_effect",
                "nss_inside_chroot",
                "dynamic_loader_inside_chroot",
                "evidence_scope",
                "safe_trace",
                "unsafe_trace",
                "safe_trace_late_lookups",
                "unsafe_trace_late_lookups",
                "result",
                "walkthrough",
                "unsafe_pointer_probe",
                "unsafe_block_count",
                "walkthrough",
                "ffi_declared",
                "ffi_called",
                "ffi_call_count",
                "strlen_result",
                "getenv_path",
                "inventory_count",
                "result",
            ],
        );
        assert_unique_key_value_lines(
            &stdout,
            &[
                "create_parent_identity_verified=yes",
                "create_new_requested_mode=0o600",
                "create_new_group_other_bits=0o000",
                "chmod_identity_stable=yes",
                "chmod_window_start_mode=0o644",
                "chmod_window_final_mode=0o600",
                "create_dir_requested_mode=0o700",
                "create_dir_creation_mode=0o700",
                "chmod_change_observed=yes",
                "rootless_scope=create_new,chmod,metadata",
                "checked_path=raw-candidate",
                "initial_target=raw-trusted.txt",
                "replacement_target=raw-replacement.txt",
                "pre_canonical_leaf=raw-trusted.txt",
                "post_canonical_leaf=raw-replacement.txt",
                "pre_read=trusted",
                "post_read=replacement",
                "raw_path_re_resolved=yes",
                "raw_path_scope=metadata,canonicalize,symlink,rename,read",
                "closed_stream_write_error=BrokenPipe",
                "sigpipe_child_stdout_closed=yes",
                "sigpipe_child_exit=success",
                "broken_pipe_handled=ok",
                "cli_child_mode=args_os",
                "cli_child_space_arg=preserved",
                "cli_child_invalid_arg_hex=6172675fff",
                "cli_child_invalid_arg_to_str=none",
                "cli_child_strict_utf8=error",
                "rootless_user_probe=ok",
                "rootless_group_probe=ok",
                "ffi_declared=getenv,strlen",
                "ffi_called=getenv,strlen",
                "ffi_call_count=2",
                "strlen_result=5",
                "unsafe_pointer_probe=ok",
                "unsafe_block_count=1",
                "inventory_count=3",
            ],
        );
        assert_inventory_count_matches_unsafe_ffi_total(&stdout);
        let create_parent_id = single_key_value(&stdout, "create_parent_file_id");
        let chmod_before_id = single_key_value(&stdout, "chmod_file_id_before");
        let chmod_after_id = single_key_value(&stdout, "chmod_file_id_after");
        let pre_id = single_key_value(&stdout, "pre_file_id");
        let post_id = single_key_value(&stdout, "post_file_id");
        assert_unix_file_id(create_parent_id, &stdout);
        assert_unix_file_id(chmod_before_id, &stdout);
        assert_unix_file_id(chmod_after_id, &stdout);
        assert_unix_file_id(pre_id, &stdout);
        assert_unix_file_id(post_id, &stdout);
        assert_eq!(
            chmod_before_id, chmod_after_id,
            "chmod walkthrough should prove chmod targeted the same file identity\nstdout:\n{stdout}"
        );
        assert_ne!(
            pre_id, post_id,
            "raw path walkthrough should prove the checked path re-resolved to a different file identity\nstdout:\n{stdout}"
        );
    }
    #[cfg(not(unix))]
    {
        assert_exact_keys(
            &stdout,
            &[
                "walkthrough",
                "permissions_unsupported",
                "walkthrough",
                "raw_path_unsupported",
                "walkthrough",
                "scratch",
                "expected_len",
                "discarded_remove_error",
                "discarded_canonicalize_error",
                "checked_read_error",
                "discarded_read_error",
                "discarded_fallback_len",
                "fallback_matches_expected",
                "checked_decision",
                "fallback_decision",
                "integrity_check",
                "result",
                "walkthrough",
                "scratch",
                "safe_metadata",
                "safe_utf8",
                "panic_hook",
                "caught_panics",
                "caught_panic_count",
                "panic_payloads_escaped",
                "result",
                "walkthrough",
                "sigpipe_unsupported",
                "walkthrough",
                "cli_args_unsupported",
                "walkthrough",
                "scratch",
                "rootless_root_metadata",
                "rootless_root_canonicalize",
                "rootless_user_probe",
                "rootless_group_probe",
                "rootless_plugin_metadata",
                "rootless_plugin_canonicalize",
                "rootless_plugin_read",
                "pre_privilege_probe_order",
                "privileged_ops",
                "privileged_ops_executed",
                "privileged_ops_mode",
                "root_transition_effect",
                "uid_gid_transition_effect",
                "nss_inside_chroot",
                "dynamic_loader_inside_chroot",
                "evidence_scope",
                "safe_trace",
                "unsafe_trace",
                "safe_trace_late_lookups",
                "unsafe_trace_late_lookups",
                "result",
                "walkthrough",
                "walkthrough",
                "ffi_unsupported",
            ],
        );
        assert_unique_key_value_lines(
            &stdout,
            &[
                "permissions_unsupported=non-unix",
                "raw_path_unsupported=non-unix",
                "sigpipe_unsupported=non-unix",
                "cli_args_unsupported=non-unix",
                "rootless_user_probe=unsupported",
                "rootless_group_probe=unsupported",
                "ffi_unsupported=non-unix",
            ],
        );
    }

    assert_unique_key_value_lines(
        &stdout,
        &[
            "discarded_remove_error=NotFound",
            "discarded_canonicalize_error=NotFound",
            "checked_read_error=NotFound",
            "discarded_read_error=lost",
            "discarded_fallback_len=0",
            "fallback_matches_expected=no",
            "checked_decision=reject-error",
            "fallback_decision=reject-empty-fallback",
            "integrity_check=discard-changes-decision",
            "safe_metadata=ok",
            "safe_utf8=ok",
            "panic_hook=suppressed",
            "caught_panics=metadata_expect,utf8_unwrap,assert,panic,todo,unreachable",
            "caught_panic_count=6",
            "panic_payloads_escaped=no",
            "rootless_root_metadata=ok",
            "rootless_root_canonicalize=ok",
            "rootless_plugin_metadata=ok",
            "rootless_plugin_canonicalize=ok",
            "rootless_plugin_read=ok",
            "pre_privilege_probe_order=root,user,group,plugin",
            "privileged_ops=simulate_chroot,simulate_setgid,simulate_setuid",
            "privileged_ops_executed=no",
            "privileged_ops_mode=simulated",
            "root_transition_effect=not_exercised",
            "uid_gid_transition_effect=not_exercised",
            "nss_inside_chroot=not_exercised",
            "dynamic_loader_inside_chroot=not_exercised",
            "evidence_scope=rootless_preflight_and_trace_order",
            "safe_trace=resolve_root,resolve_user,getpwnam,resolve_group,getgrnam,resolve_plugin_path,dlopen,simulate_chroot,simulate_setgid,simulate_setuid",
            "unsafe_trace=simulate_chroot,resolve_user,getpwnam,resolve_group,getgrnam,resolve_plugin_path,dlopen,simulate_setgid,simulate_setuid",
            "safe_trace_late_lookups=0",
            "unsafe_trace_late_lookups=6",
        ],
    );
    #[cfg(unix)]
    assert_key_values(
        &stdout,
        "result",
        &[
            "permission-window-create-change-demonstrated",
            "raw-path-re-resolution-demonstrated",
            "error-discard-integrity-demonstrated",
            "panic-boundary-demonstrated",
            "process-sigpipe-demonstrated",
            "cli-arg-compatibility-demonstrated",
            "trust-domain-order-demonstrated-rootlessly",
            "unsafe-ffi-boundary-inventory-demonstrated",
        ],
    );
    #[cfg(not(unix))]
    assert_key_values(
        &stdout,
        "result",
        &[
            "error-discard-integrity-demonstrated",
            "panic-boundary-demonstrated",
            "trust-domain-order-demonstrated-rootlessly",
        ],
    );
}

fn run_bin(path: &str) -> String {
    let output =
        Command::new(path).output().unwrap_or_else(|error| panic!("failed to run {path}: {error}"));
    let stdout = String::from_utf8(output.stdout).expect("walkthrough stdout should be UTF-8");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "walkthrough binary failed\npath: {path}\nstatus: {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        output.status
    );
    assert!(
        stderr.is_empty(),
        "walkthrough binary wrote stderr\npath: {path}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    stdout
}

fn assert_unique_key_value_lines(stdout: &str, expected_lines: &[&str]) {
    for expected in expected_lines {
        assert_unique_key_value_line(stdout, expected);
    }
}

fn assert_exact_keys(stdout: &str, expected_keys: &[&str]) {
    let actual = stdout
        .lines()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| {
                    panic!("stdout line is not key=value: {line:?}\nstdout:\n{stdout}")
                })
                .0
        })
        .collect::<Vec<_>>();

    assert_eq!(
        actual, expected_keys,
        "stdout key inventory changed; update the test and lab validator together\nstdout:\n{stdout}"
    );
}

fn assert_unique_key_value_line(stdout: &str, expected: &str) {
    let (key, _) = expected.split_once('=').expect("expected key=value line");
    let key_lines = stdout
        .lines()
        .filter(|line| line.split_once('=').is_some_and(|(candidate_key, _)| candidate_key == key))
        .collect::<Vec<_>>();

    assert_eq!(
        key_lines,
        vec![expected],
        "stdout did not contain exactly one matching line for key {key:?}\nstdout:\n{stdout}"
    );
}

fn assert_key_values(stdout: &str, key: &str, expected_values: &[&str]) {
    let actual = key_values(stdout, key);

    assert_eq!(
        actual, expected_values,
        "stdout did not contain the exact {key:?} value set\nstdout:\n{stdout}"
    );
}

fn assert_no_key(stdout: &str, key: &str) {
    let actual = key_values(stdout, key);
    assert!(
        actual.is_empty(),
        "stdout contained unexpected {key:?} value(s) {actual:?}\nstdout:\n{stdout}"
    );
}

fn single_key_value<'a>(stdout: &'a str, key: &str) -> &'a str {
    let actual = key_values(stdout, key);
    assert_eq!(
        actual.len(),
        1,
        "stdout did not contain exactly one {key:?} value\nstdout:\n{stdout}"
    );
    actual[0]
}

fn single_usize_key_value(stdout: &str, key: &str) -> usize {
    single_key_value(stdout, key).parse::<usize>().unwrap_or_else(|error| {
        panic!("stdout {key:?} value should be usize: {error}\nstdout:\n{stdout}")
    })
}

#[cfg(unix)]
fn assert_inventory_count_matches_unsafe_ffi_total(stdout: &str) {
    let ffi_call_count = single_usize_key_value(stdout, "ffi_call_count");
    let unsafe_block_count = single_usize_key_value(stdout, "unsafe_block_count");
    let inventory_count = single_usize_key_value(stdout, "inventory_count");

    assert_eq!(
        inventory_count,
        ffi_call_count + unsafe_block_count,
        "unsafe/ffi inventory count should equal ffi_call_count + unsafe_block_count\nstdout:\n{stdout}"
    );
}

#[cfg(unix)]
fn assert_unix_file_id(value: &str, stdout: &str) {
    let (dev, ino) =
        value.split_once(':').unwrap_or_else(|| panic!("file id is not dev:ino: {value:?}"));
    assert!(
        !dev.is_empty()
            && !ino.is_empty()
            && dev.bytes().all(|byte| byte.is_ascii_digit())
            && ino.bytes().all(|byte| byte.is_ascii_digit()),
        "file id should be decimal dev:ino, got {value:?}\nstdout:\n{stdout}"
    );
}

fn key_values<'a>(stdout: &'a str, key: &str) -> Vec<&'a str> {
    stdout
        .lines()
        .filter_map(|line| line.split_once('='))
        .filter_map(|(candidate_key, value)| (candidate_key == key).then_some(value))
        .collect::<Vec<_>>()
}
