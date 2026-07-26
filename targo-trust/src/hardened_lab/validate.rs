use super::claims::WalkthroughEvidenceSpec;

pub(super) fn validate_path_identity_walkthrough(stdout: &str) -> Vec<String> {
    let mut errors = Vec::new();
    expect_key_values(stdout, "walkthrough", &["path_identity_toctou"], &mut errors);
    if cfg!(unix) {
        expect_exact_transcript_keys(
            stdout,
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
            &mut errors,
        );
        expect_no_key(stdout, "unsupported", &mut errors);
        expect_key_values(stdout, "pre_link", &["safe.txt"], &mut errors);
        expect_key_values(stdout, "post_link", &["swapped.txt"], &mut errors);
        let pre_id = single_key_value(stdout, "pre_file_id", &mut errors);
        let post_id = single_key_value(stdout, "post_file_id", &mut errors);
        if let Some(pre_id) = pre_id {
            expect_unix_file_id(pre_id, &mut errors);
        }
        if let Some(post_id) = post_id {
            expect_unix_file_id(post_id, &mut errors);
        }
        if pre_id.zip(post_id).is_some_and(|(pre, post)| pre == post) {
            errors.push("path identity walkthrough kept the same file identity".to_string());
        }
        expect_key_values(stdout, "observed", &["swapped"], &mut errors);
        expect_key_values(stdout, "result", &["toctou-demonstrated"], &mut errors);
    } else {
        expect_exact_transcript_keys(stdout, &["walkthrough", "unsupported"], &mut errors);
        expect_key_values(stdout, "unsupported", &["non-unix"], &mut errors);
        expect_no_key(stdout, "result", &mut errors);
    }
    errors
}

pub(super) fn validate_byte_utf8_walkthrough(stdout: &str) -> Vec<String> {
    let mut errors = Vec::new();
    expect_key_values(stdout, "walkthrough", &["byte_utf8"], &mut errors);
    if cfg!(unix) {
        expect_no_key(stdout, "unsupported", &mut errors);
        expect_key_values(stdout, "filename_hex", &["6e6f6e5f757466385fff5f6e616d65"], &mut errors);
        expect_key_values(stdout, "payload_hex", &["7061796c6f61643af0288c280a"], &mut errors);
        expect_key_values(stdout, "lossy_payload_had_replacement", &["yes"], &mut errors);
        expect_key_values(stdout, "strict_filename_utf8", &["error"], &mut errors);
        expect_key_values(stdout, "read_to_string_error", &["InvalidData"], &mut errors);
        expect_key_values(stdout, "roundtrip_payload_bytes", &["ok"], &mut errors);
        expect_key_values(stdout, "result", &["non-utf8-demonstrated"], &mut errors);
        match key_values(stdout, "filename_creation").as_slice() {
            ["supported"] => {
                expect_exact_transcript_keys(
                    stdout,
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
                    &mut errors,
                );
                expect_key_values(stdout, "path_to_str", &["none"], &mut errors);
                expect_key_values(stdout, "lossy_filename_had_replacement", &["yes"], &mut errors);
                expect_key_values(stdout, "roundtrip_filename_bytes", &["ok"], &mut errors);
            }
            ["unsupported"] => {
                expect_exact_transcript_keys(
                    stdout,
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
                    &mut errors,
                );
                expect_key_values(stdout, "path_to_str", &["skipped"], &mut errors);
                expect_key_values(
                    stdout,
                    "lossy_filename_had_replacement",
                    &["skipped"],
                    &mut errors,
                );
                expect_key_values(stdout, "roundtrip_filename_bytes", &["skipped"], &mut errors);
            }
            actual => errors.push(format!(
                "key `filename_creation` expected exactly one supported/unsupported value, got {actual:?}"
            )),
        }
    } else {
        expect_exact_transcript_keys(stdout, &["walkthrough", "unsupported"], &mut errors);
        expect_key_values(stdout, "unsupported", &["non-unix"], &mut errors);
        expect_no_key(stdout, "result", &mut errors);
    }
    errors
}

pub(super) fn expect_exact_transcript_keys(
    stdout: &str,
    expected_keys: &[&str],
    errors: &mut Vec<String>,
) {
    if stdout.is_empty() {
        errors.push("walkthrough stdout must not be empty".to_string());
        return;
    }

    let mut actual_keys = Vec::new();
    for (line_index, line) in stdout.lines().enumerate() {
        let line_number = line_index + 1;
        if line.is_empty() {
            errors.push(format!("transcript line {line_number} is empty"));
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            errors.push(format!("transcript line {line_number} is not key=value: {line:?}"));
            continue;
        };
        if key.is_empty() || value.is_empty() {
            errors.push(format!(
                "transcript line {line_number} must have a non-empty key and value: {line:?}"
            ));
            continue;
        }
        if !key.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_') {
            errors.push(format!(
                "transcript line {line_number} has invalid key `{key}`; expected [A-Za-z0-9_]+"
            ));
        }
        actual_keys.push(key);
    }

    if actual_keys.as_slice() != expected_keys {
        errors.push(format!(
            "transcript key order/inventory expected {expected_keys:?}, got {actual_keys:?}"
        ));
    }
}

pub(super) fn expect_key_values(
    stdout: &str,
    key: &str,
    expected: &[&str],
    errors: &mut Vec<String>,
) {
    let actual = key_values(stdout, key);
    if actual != expected {
        errors.push(format!("key `{key}` expected {expected:?}, got {actual:?}"));
    }
}

pub(super) fn expect_no_key(stdout: &str, key: &str, errors: &mut Vec<String>) {
    let actual = key_values(stdout, key);
    if !actual.is_empty() {
        errors.push(format!("key `{key}` expected no values, got {actual:?}"));
    }
}

pub(super) fn single_key_value<'a>(
    stdout: &'a str,
    key: &str,
    errors: &mut Vec<String>,
) -> Option<&'a str> {
    let actual = key_values(stdout, key);
    if actual.len() != 1 {
        errors.push(format!("key `{key}` expected exactly one value, got {actual:?}"));
        return None;
    }
    actual.first().copied()
}

pub(super) fn expect_unix_file_id(value: &str, errors: &mut Vec<String>) {
    let Some((dev, ino)) = value.split_once(':') else {
        errors.push(format!("file id is not dev:ino: {value:?}"));
        return;
    };
    if dev.is_empty()
        || ino.is_empty()
        || !dev.bytes().all(|byte| byte.is_ascii_digit())
        || !ino.bytes().all(|byte| byte.is_ascii_digit())
    {
        errors.push(format!("file id should be decimal dev:ino, got {value:?}"));
    }
}

pub(super) fn key_values<'a>(stdout: &'a str, key: &str) -> Vec<&'a str> {
    stdout
        .lines()
        .filter_map(|line| line.split_once('='))
        .filter_map(|(candidate_key, value)| (candidate_key == key).then_some(value))
        .collect()
}

pub(super) fn key_values_in_walkthrough<'a>(
    stdout: &'a str,
    walkthrough_name: Option<&str>,
    key: &str,
) -> Vec<&'a str> {
    let Some(walkthrough_name) = walkthrough_name else {
        return key_values(stdout, key);
    };

    let mut in_named_walkthrough = false;
    stdout
        .lines()
        .filter_map(|line| line.split_once('='))
        .filter_map(|(candidate_key, value)| {
            if candidate_key == "walkthrough" {
                in_named_walkthrough = value == walkthrough_name;
            }
            (in_named_walkthrough && candidate_key == key).then_some(value)
        })
        .collect()
}

pub(super) fn expected_walkthrough_name(spec: &WalkthroughEvidenceSpec) -> Option<&'static str> {
    spec.requirements
        .iter()
        .find_map(|requirement| (requirement.key == "walkthrough").then_some(requirement.value))
}
