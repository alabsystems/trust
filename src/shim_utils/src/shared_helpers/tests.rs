use super::*;

fn context() -> HashMap<String, String> {
    let mut values = TRUST_CARGO_TEST_SHIM_KEYS
        .iter()
        .map(|key| (key.to_string(), "fixture-path".to_owned()))
        .collect::<HashMap<_, _>>();
    for (key, value) in [
        ("TRUST_CARGO_TEST_SHIM_VERSION", TRUST_CARGO_TEST_SHIM_VERSION),
        ("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "1"),
        ("TRUST_VANILLA_ANNOUNCED", "1"),
        ("RUSTC_LINK_STD_INTO_RUSTC_DRIVER", "0"),
        ("RUSTC_STAGE", "1"),
    ] {
        values.insert(key.into(), value.into());
    }
    values
}

fn check(values: &HashMap<String, String>) -> io::Result<HashMap<String, String>> {
    let file = tempfile::NamedTempFile::new().unwrap();
    fs::write(file.path(), serde_json::to_vec(values).unwrap()).unwrap();
    read_cargo_test_shim_config(file.path())
}

#[test]
fn context_requires_all_owner_fields_and_refuses_extra_authority() {
    let valid = context();
    assert_eq!(check(&valid).unwrap(), valid);
    for key in TRUST_CARGO_TEST_SHIM_KEYS {
        let mut missing = valid.clone();
        missing.remove(key);
        assert!(check(&missing).is_err(), "accepted missing {key}");
    }
    let mut extra = valid;
    extra.insert("TRUST_OTHER_POLICY".into(), "1".into());
    assert!(check(&extra).is_err());
}

#[test]
fn context_requires_current_exact_announced_ordinary_policy() {
    for (key, value) in [
        ("TRUST_CARGO_TEST_SHIM_VERSION", "2"),
        ("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "0"),
        ("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "true"),
        ("TRUST_VANILLA_ANNOUNCED", "0"),
        ("TRUST_VANILLA_ANNOUNCED", "true"),
        ("RUSTC_LINK_STD_INTO_RUSTC_DRIVER", "true"),
        ("RUSTC_STAGE", "not-a-stage"),
        ("RUSTC_REAL", ""),
    ] {
        let mut invalid = context();
        invalid.insert(key.into(), value.into());
        assert!(check(&invalid).is_err(), "accepted {key}={value:?}");
    }
}

#[test]
fn compiler_announcement_is_command_bound_and_cannot_authorize_verified_policy() {
    // An inactive overlay avoids process-global environment mutation in
    // these parallel unit tests. Real restore/child behavior is exercised
    // by bootstrap_cargo_fixture_context_test.py.
    for no_verify_applies in [false, true] {
        let mut overlay = IsolatedShimEnvironment { original: Vec::new(), active: false };
        let mut command = Command::new("rustc");
        command.env("TRUST_VANILLA_ANNOUNCED", "authored-value");
        command.env("TRUST_FIXTURE_AUTHORED", "preserved");
        overlay.restore_for_compiler_command(&mut command, no_verify_applies);
        let values = command.get_envs().collect::<HashMap<_, _>>();
        assert_eq!(
            values[OsStr::new("TRUST_VANILLA_ANNOUNCED")],
            no_verify_applies.then_some(OsStr::new("1")),
        );
        assert_eq!(values[OsStr::new("TRUST_FIXTURE_AUTHORED")], Some(OsStr::new("preserved")),);
    }
}
