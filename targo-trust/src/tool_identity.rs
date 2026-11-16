//! The loaded tool's source and its retained oracle compiler are distinct.
//! Only compile-time metadata selects this relation; runtime environment and
//! candidate compiler output cannot replace either side of the binding.

pub(crate) fn oracle_compiler_hash() -> Result<Option<&'static str>, String> {
    select_oracle_compiler(
        option_env!("CFG_VER_HASH"),
        option_env!("CFG_TRUST_ORACLE_COMPILER_HASH"),
        option_env!("CFG_TRUST_ORACLE_HOST"),
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RetainedDaemonBuild<'a> {
    pub(crate) release: &'a str,
    pub(crate) commit: &'a str,
}

/// The retained compiler's build identity, never the frontend's source stamp.
pub(crate) fn retained_daemon_build() -> Result<Option<RetainedDaemonBuild<'static>>, String> {
    select_retained_daemon_build(
        option_env!("CFG_VER_HASH"),
        option_env!("CFG_TRUST_ORACLE_COMPILER_HASH"),
        option_env!("CFG_TRUST_ORACLE_HOST"),
        option_env!("CFG_TRUST_ORACLE_COMPILER_RELEASE"),
    )
}

pub(crate) fn oracle_compiler_release() -> Result<Option<&'static str>, String> {
    match retained_daemon_build()? {
        Some(identity) => Ok(Some(identity.release)),
        None => Ok(option_env!("CFG_RELEASE")),
    }
}

fn select_retained_daemon_build<'a>(
    tool_source: Option<&'a str>,
    retained_compiler: Option<&'a str>,
    bound_host: Option<&str>,
    release: Option<&'a str>,
) -> Result<Option<RetainedDaemonBuild<'a>>, String> {
    let Some(retained) = retained_compiler else {
        return Ok(None);
    };
    select_oracle_compiler(tool_source, Some(retained), bound_host)?;
    let release = release
        .filter(|value| {
            !value.is_empty()
                && value.len() <= 128
                && value.bytes().all(|b| b.is_ascii_alphanumeric() || b".-+_".contains(&b))
        })
        .ok_or("retained daemon requires the observed compiler release")?;
    Ok(Some(RetainedDaemonBuild { release, commit: retained }))
}

fn canonical_hash(value: &str) -> bool {
    value.len() == 40
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn select_oracle_compiler<'a>(
    tool_source: Option<&'a str>,
    retained_compiler: Option<&'a str>,
    bound_host: Option<&str>,
) -> Result<Option<&'a str>, String> {
    let Some(retained) = retained_compiler else {
        // Ordinary same-source builds retain their existing policy, including
        // Clean's existing validation of a missing or malformed host identity.
        return Ok(tool_source);
    };
    if bound_host != Some("1") {
        return Err("retained oracle compiler requires CFG_TRUST_ORACLE_HOST=1".into());
    }
    if !tool_source.is_some_and(canonical_hash) || !canonical_hash(retained) {
        return Err(
            "retained oracle compiler requires exact tool-source and compiler hashes".into()
        );
    }
    Ok(Some(retained))
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOOL: &str = "1111111111111111111111111111111111111111";
    const OTHER: &str = "2222222222222222222222222222222222222222";

    #[test]
    fn ordinary_build_keeps_its_same_source_binding() {
        assert_eq!(select_oracle_compiler(Some(TOOL), None, Some("1")).unwrap(), Some(TOOL));
        assert_eq!(select_oracle_compiler(None, None, None).unwrap(), None);
        assert_eq!(
            select_oracle_compiler(Some(TOOL), Some(OTHER), Some("1")).unwrap(),
            Some(OTHER)
        );
    }

    #[test]
    fn retained_binding_refuses_malformed_or_unbound_metadata() {
        for bound in [None, Some(""), Some("0"), Some("true")] {
            assert!(select_oracle_compiler(Some(TOOL), Some(OTHER), bound).is_err());
        }
        for invalid in [
            "",
            "short",
            "GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG",
            "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
        ] {
            assert!(select_oracle_compiler(Some(invalid), Some(OTHER), Some("1")).is_err());
            assert!(select_oracle_compiler(Some(TOOL), Some(invalid), Some("1")).is_err());
        }
        assert!(select_oracle_compiler(None, Some(OTHER), Some("1")).is_err());
    }

    #[test]
    fn retained_daemon_binding_keeps_observed_release_and_oracle_commit() {
        assert_eq!(select_retained_daemon_build(Some(TOOL), None, None, None).unwrap(), None);
        assert_eq!(
            select_retained_daemon_build(Some(TOOL), Some(OTHER), Some("1"), Some("1.101.0-dev"))
                .unwrap(),
            Some(RetainedDaemonBuild { release: "1.101.0-dev", commit: OTHER })
        );
        assert_ne!(TOOL, OTHER, "the frontend source is deliberately distinct");
    }

    #[test]
    fn retained_daemon_binding_refuses_missing_or_malformed_release() {
        for release in [None, Some(""), Some("1.101.0-dev\n"), Some("../../release")] {
            assert!(
                select_retained_daemon_build(Some(TOOL), Some(OTHER), Some("1"), release).is_err()
            );
        }
        assert!(
            select_retained_daemon_build(Some(TOOL), Some(OTHER), Some("0"), Some("1.101.0-dev"))
                .is_err()
        );
        assert!(
            select_retained_daemon_build(Some(TOOL), Some("short"), Some("1"), Some("1.101.0-dev"))
                .is_err()
        );
    }

    #[test]
    fn native_oracle_admission_keeps_the_exact_selected_compiler() {
        const TEST: &str =
            "tool_identity::tests::native_oracle_admission_keeps_the_exact_selected_compiler";
        const ROLE: &str = "TRUST_ORACLE_BINDING_TEST_ROLE";
        let role = std::env::var(ROLE).ok();
        let Some(role) = role else {
            for role in ["accepted", "wrong-target"] {
                let output = std::process::Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", TEST, "--nocapture"])
                    .env(ROLE, role)
                    .output()
                    .unwrap();
                assert!(output.status.success(), "{role}: {output:?}");
            }
            return;
        };
        // Use the explicitly selected engineering cohort when present, as the
        // real-solver controls do. A source-built frontend need not reside
        // beside its compiler. This observes actual native -vV, not proof.
        let compiler_name = format!("trustc{}", std::env::consts::EXE_SUFFIX);
        let compiler = match std::env::var_os(trust_router::ay_discovery::STAGE2_BIN_ENV) {
            Some(directory) => std::path::PathBuf::from(directory).join(&compiler_name),
            None => std::path::Path::new(env!("CARGO")).with_file_name(&compiler_name),
        };
        assert!(compiler.is_absolute());
        // A targo outside a toolchain `bin/` (x.py's `stageN-tools-bin`) has no
        // trustc beside it: that launch cannot run this test, so say so rather
        // than failing with a bare NotFound.
        let output =
            std::process::Command::new(&compiler).arg("-vV").output().unwrap_or_else(|error| {
                panic!(
                    "NOT RUN: selected Trust compiler is unavailable \
                     (CARGO={}): {}: {error}; select TRUST_STAGE2_BIN explicitly or \
                     run the tests with a Trust toolchain whose targo has trustc beside it",
                    env!("CARGO"),
                    compiler.display()
                )
            });
        assert!(output.status.success());
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.lines().any(|line| line == "binary: trustc"));
        let actual: Vec<_> =
            text.lines().filter_map(|line| line.strip_prefix("commit-hash: ")).collect();
        assert_eq!(actual.len(), 1);
        assert!(canonical_hash(actual[0]));
        let other = if actual[0] == OTHER { TOOL } else { OTHER };
        let expected = match role.as_str() {
            "accepted" => actual[0],
            "wrong-target" => other,
            _ => panic!("unknown isolated binding role"),
        };
        let selected = select_oracle_compiler(Some(TOOL), Some(expected), Some("1")).unwrap();
        clean_elab::oracle_compiler::bind_host_toolchain(selected).unwrap();
        let admitted = clean_elab::oracle_compiler::admit_beside(&compiler);
        if role == "accepted" {
            assert_eq!(admitted.unwrap().path(), compiler.canonicalize().unwrap().as_path());
        } else {
            assert!(
                matches!(admitted, Err(clean_elab::oracle_compiler::OracleCompilerError::CommitMismatch { found, expected: wanted, .. }) if found == actual[0] && wanted == expected)
            );
        }
    }
}
