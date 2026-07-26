use rustc_session::getopts;

fn compiler_options() -> getopts::Options {
    let mut options = getopts::Options::new();
    for option in rustc_session::config::rustc_optgroups() {
        option.apply(&mut options);
    }
    options
}

/// Recover the legacy in-band `--no-deps` frontend marker without stealing a
/// byte sequence that rustc owns as the required value of the preceding
/// option. New v2 payloads never call this: their `no_deps` bit is carried
/// separately and their compiler arguments remain exact.
pub(crate) fn split_legacy_no_deps(args: Vec<String>) -> Result<(bool, Vec<String>), String> {
    let options = compiler_options();
    let mut no_deps = false;
    let mut compiler_args = Vec::with_capacity(args.len());

    for arg in args {
        if arg != "--no-deps" {
            compiler_args.push(arg);
            continue;
        }

        match options.parse(&compiler_args) {
            Err(getopts::Fail::ArgumentMissing(_)) => compiler_args.push(arg),
            Ok(_) => {
                compiler_args.push(arg);
                match options.parse(&compiler_args) {
                    Err(getopts::Fail::UnrecognizedOption(option)) if option == "no-deps" => {
                        let removed = compiler_args.pop();
                        debug_assert_eq!(removed.as_deref(), Some("--no-deps"));
                        no_deps = true;
                    },
                    // An explicit `--`, or a rustc option with an optional
                    // value, can make this spelling valid compiler input even
                    // though the prefix was already complete.
                    Ok(_) => {},
                    Err(error) => {
                        let removed = compiler_args.pop();
                        debug_assert_eq!(removed.as_deref(), Some("--no-deps"));
                        return Err(format!(
                            "cannot identify legacy `--no-deps` marker after valid compiler arguments: {error}"
                        ));
                    },
                }
            },
            Err(error) => {
                return Err(format!(
                    "cannot identify legacy `--no-deps` marker after invalid compiler arguments: {error}"
                ));
            },
        }
    }

    Ok((no_deps, compiler_args))
}

#[cfg(test)]
mod tests {
    use super::split_legacy_no_deps;

    #[test]
    fn standalone_legacy_markers_are_removed_and_coalesced() {
        assert_eq!(
            split_legacy_no_deps(
                ["--no-deps", "-Wclippy::pedantic", "--no-deps"]
                    .map(String::from)
                    .to_vec()
            ),
            Ok((true, vec!["-Wclippy::pedantic".to_string()]))
        );
    }

    #[test]
    fn marker_spelling_is_preserved_when_rustc_owns_it_as_an_option_value() {
        for option in ["--cfg", "--crate-name", "--extern", "-C", "-Z", "-W"] {
            assert_eq!(
                split_legacy_no_deps([option, "--no-deps"].map(String::from).to_vec()),
                Ok((false, vec![option.to_string(), "--no-deps".to_string()])),
                "option={option}"
            );
        }

        assert_eq!(
            split_legacy_no_deps(
                ["--cfg", "--no-deps", "--no-deps", "-Wclippy::all"]
                    .map(String::from)
                    .to_vec()
            ),
            Ok((
                true,
                vec![
                    "--cfg".to_string(),
                    "--no-deps".to_string(),
                    "-Wclippy::all".to_string()
                ]
            ))
        );
    }

    #[test]
    fn malformed_prefix_fails_closed_instead_of_guessing_marker_ownership() {
        let error = split_legacy_no_deps(
            ["--definitely-not-a-rustc-option", "--no-deps"]
                .map(String::from)
                .to_vec(),
        )
        .expect_err("an unknown legacy prefix must fail closed");
        assert!(
            error.contains("invalid compiler arguments") || error.contains("Unrecognized"),
            "{error}"
        );
    }

    #[test]
    fn explicit_rustc_separator_keeps_later_marker_spellings_as_free_arguments() {
        assert_eq!(
            split_legacy_no_deps(["--", "--no-deps"].map(String::from).to_vec()),
            Ok((false, ["--", "--no-deps"].map(String::from).to_vec()))
        );
        assert_eq!(
            split_legacy_no_deps(["--no-deps", "--", "--no-deps"].map(String::from).to_vec()),
            Ok((true, ["--", "--no-deps"].map(String::from).to_vec()))
        );
        assert_eq!(
            split_legacy_no_deps(["--crate-name", "--", "--no-deps"].map(String::from).to_vec()),
            Ok((true, ["--crate-name", "--"].map(String::from).to_vec()))
        );
    }
}
