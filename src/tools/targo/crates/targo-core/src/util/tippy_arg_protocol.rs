// Trust: Trust-authored, no upstream counterpart. Clippy's inherited
// `CLIPPY_ARGS` channel joins arguments with a delimiter string, so any
// argument containing that delimiter is silently re-split — lossy in a place
// where the frontend and the driver must agree exactly. Tippy replaces it with
// a versioned, length-prefixed encoding, and the legacy variable stays
// readable only for inherited Clippy frontends.
//
// Line comments, not `//!`: tippy `include!`s this file into a module body
// (src/tools/tippy/src/arg_protocol.rs), where an inner doc comment is not a
// legal position.

use std::fmt::Write as _;
use std::path::Path;

/// Unambiguous Tippy frontend-to-driver argument channel.
///
/// `CLIPPY_ARGS` remains available for inherited tooling, but new producers
/// and consumers must prefer this versioned, length-prefixed representation.
/// This module lives inside Targo's publishable package so packaged Cargo
/// sources are self-contained; the non-published Tippy package includes this
/// same source file rather than maintaining a second wire-format codec.
pub(crate) const TIPPY_ENCODED_ARGS_ENV: &str = "TIPPY_ENCODED_ARGS";
pub(crate) const CLIPPY_ARGS_ENV: &str = "CLIPPY_ARGS";

/// Whether an environment name belongs to Tippy's protected argument
/// protocol. Environment names are case-insensitive on Windows, so mutation
/// boundaries must reject every ASCII-case variant even when the current host
/// would treat it as a distinct variable.
#[allow(dead_code)]
pub(crate) fn is_protected_tippy_arg_env(name: &str) -> bool {
    name.eq_ignore_ascii_case(TIPPY_ENCODED_ARGS_ENV) || name.eq_ignore_ascii_case(CLIPPY_ARGS_ENV)
}

/// Compare a complete executable name using the target platform's semantics.
/// Windows executable discovery is ASCII-case-insensitive and permits the
/// conventional `.exe` suffix. Unix branding is an exact whole-name match.
/// In particular, `tippy.backup` must never acquire `tippy` authority merely
/// because [`Path::file_stem`] happens to remove its suffix.
#[allow(dead_code)]
pub(crate) fn executable_path_matches(path: &Path, expected: &str) -> bool {
    executable_path_matches_with_windows_semantics(path, expected, cfg!(windows))
}

#[allow(dead_code)]
pub(crate) fn executable_path_matches_with_windows_semantics(
    path: &Path,
    expected: &str,
    windows_semantics: bool,
) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    if windows_semantics {
        name.eq_ignore_ascii_case(expected)
            || name.rsplit_once('.').is_some_and(|(stem, extension)| {
                stem.eq_ignore_ascii_case(expected) && extension.eq_ignore_ascii_case("exe")
            })
    } else {
        name == expected
    }
}

const SCHEMA_V2_PREFIX: &str = "tippy-args-v2;";
const SCHEMA_V1_PREFIX: &str = "tippy-args-v1;";
const NO_DEPS_FALSE_PREFIX: &str = "no-deps=0;";
const NO_DEPS_TRUE_PREFIX: &str = "no-deps=1;";

/// Whether `--no-deps` has an unambiguous out-of-band value or must still be
/// recovered from an older in-band argument list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum NoDepsFlag {
    Explicit(bool),
    LegacyInBand,
}

/// One decoded Tippy frontend payload.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) struct DecodedTippyArgs {
    pub(crate) no_deps: NoDepsFlag,
    pub(crate) compiler_args: Vec<String>,
}

// Each production call site uses one half of the codec. Keep both functions
// available in every includer so one shared test suite exercises the complete
// producer/consumer contract.
#[allow(dead_code)]
pub(crate) fn encode_args<T: AsRef<str>>(no_deps: bool, compiler_args: &[T]) -> String {
    let mut encoded = SCHEMA_V2_PREFIX.to_string();
    encoded.push_str(if no_deps {
        NO_DEPS_TRUE_PREFIX
    } else {
        NO_DEPS_FALSE_PREFIX
    });
    for arg in compiler_args {
        let arg = arg.as_ref();
        // Lengths are bytes, which lets the decoder advance without reserving
        // any delimiter that a valid UTF-8 command-line argument could contain.
        write!(encoded, "{}:", arg.len()).expect("writing to String cannot fail");
        encoded.push_str(arg);
    }
    encoded
}

#[allow(dead_code)]
pub(crate) fn decode_args(encoded: &str) -> Result<DecodedTippyArgs, String> {
    let (no_deps, encoded) = if let Some(encoded) = encoded.strip_prefix(SCHEMA_V2_PREFIX) {
        if let Some(encoded) = encoded.strip_prefix(NO_DEPS_FALSE_PREFIX) {
            (NoDepsFlag::Explicit(false), encoded)
        } else if let Some(encoded) = encoded.strip_prefix(NO_DEPS_TRUE_PREFIX) {
            (NoDepsFlag::Explicit(true), encoded)
        } else {
            return Err("Tippy v2 payload has an invalid or missing `no-deps` field".to_string());
        }
    } else if let Some(encoded) = encoded.strip_prefix(SCHEMA_V1_PREFIX) {
        (NoDepsFlag::LegacyInBand, encoded)
    } else {
        return Err("unsupported or missing Tippy argument schema".to_string());
    };
    let mut args = Vec::new();
    let mut cursor = 0usize;
    while cursor < encoded.len() {
        let length_end = encoded.as_bytes()[cursor..]
            .iter()
            .position(|byte| *byte == b':')
            .map(|offset| cursor + offset)
            .ok_or_else(|| "argument length is missing its `:` terminator".to_string())?;
        let length = encoded[cursor..length_end]
            .parse::<usize>()
            .map_err(|_| "argument length is not a valid usize".to_string())?;
        let start = length_end + 1;
        let end = start
            .checked_add(length)
            .filter(|end| *end <= encoded.len())
            .ok_or_else(|| "argument length exceeds the encoded payload".to_string())?;
        if !encoded.is_char_boundary(end) {
            return Err("argument length ended inside a UTF-8 code point".to_string());
        }
        args.push(encoded[start..end].to_string());
        cursor = end;
    }
    Ok(DecodedTippyArgs {
        no_deps,
        compiler_args: args,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        CLIPPY_ARGS_ENV, DecodedTippyArgs, NO_DEPS_FALSE_PREFIX, NoDepsFlag, SCHEMA_V2_PREFIX,
        TIPPY_ENCODED_ARGS_ENV, decode_args, encode_args,
        executable_path_matches_with_windows_semantics, is_protected_tippy_arg_env,
    };
    use std::path::Path;

    #[test]
    fn protected_channel_names_are_ascii_case_insensitive() {
        for name in [
            TIPPY_ENCODED_ARGS_ENV,
            "tippy_encoded_args",
            "TiPpY_EnCoDeD_ArGs",
            CLIPPY_ARGS_ENV,
            "clippy_args",
            "ClIpPy_ArGs",
        ] {
            assert!(is_protected_tippy_arg_env(name), "did not protect {name:?}");
        }
        assert!(!is_protected_tippy_arg_env("CLIPPY_CONF_DIR"));
        assert!(!is_protected_tippy_arg_env("TIPPY_ENCODED_ARGS_EXTRA"));
    }

    #[test]
    fn executable_names_require_a_complete_platform_valid_match() {
        assert!(executable_path_matches_with_windows_semantics(
            Path::new("TIPPY.EXE"),
            "tippy",
            true
        ));
        assert!(executable_path_matches_with_windows_semantics(
            Path::new("tippy"),
            "tippy",
            true
        ));
        assert!(!executable_path_matches_with_windows_semantics(
            Path::new("TIPPY"),
            "tippy",
            false
        ));
        assert!(!executable_path_matches_with_windows_semantics(
            Path::new("tippy.backup"),
            "tippy",
            false
        ));
        assert!(!executable_path_matches_with_windows_semantics(
            Path::new("tippy.exe"),
            "tippy",
            false
        ));
        for lookalike in ["not-tippy", "tippy-extra", "pre-tippy-post"] {
            assert!(!executable_path_matches_with_windows_semantics(
                Path::new(lookalike),
                "tippy",
                false
            ));
            assert!(!executable_path_matches_with_windows_semantics(
                Path::new(lookalike),
                "tippy",
                true
            ));
        }
        assert!(!executable_path_matches_with_windows_semantics(
            Path::new("tippy.com"),
            "tippy",
            true
        ));
    }

    #[test]
    fn length_prefix_round_trips_delimiter_like_unicode_and_empty_arguments() {
        let args = [
            "-Wclippy::pedantic__CLIPPY_HACKERY__-Aclippy::all",
            "lambda λ-safe",
            "",
            "--cfg=feature=\"a:b\"",
        ]
        .map(String::from);
        assert_eq!(
            decode_args(&encode_args(false, &args)),
            Ok(DecodedTippyArgs {
                no_deps: NoDepsFlag::Explicit(false),
                compiler_args: args.to_vec(),
            })
        );
    }

    #[test]
    fn v2_carries_no_deps_out_of_band_without_reinterpreting_arguments() {
        let compiler_args = ["--cfg", "--no-deps", "--no-deps"].map(String::from);
        assert_eq!(
            decode_args(&encode_args(true, &compiler_args)),
            Ok(DecodedTippyArgs {
                no_deps: NoDepsFlag::Explicit(true),
                compiler_args: compiler_args.to_vec(),
            })
        );
        assert_eq!(
            decode_args(&encode_args(false, &["--no-deps"])),
            Ok(DecodedTippyArgs {
                no_deps: NoDepsFlag::Explicit(false),
                compiler_args: vec!["--no-deps".to_string()],
            })
        );
    }

    #[test]
    fn v1_is_decoded_as_an_explicit_legacy_in_band_payload() {
        assert_eq!(
            decode_args("tippy-args-v1;9:--no-deps2:-W"),
            Ok(DecodedTippyArgs {
                no_deps: NoDepsFlag::LegacyInBand,
                compiler_args: vec!["--no-deps".to_string(), "-W".to_string()],
            })
        );
    }

    #[test]
    fn malformed_or_overflowing_payloads_fail_closed() {
        for encoded in [
            "",
            "1:a",
            "tippy-args-v3;no-deps=0;1:a",
            "tippy-args-v2;1:a",
            "tippy-args-v2;no-deps=false;1:a",
            "tippy-args-v2;no-deps=0;1",
            "tippy-args-v2;no-deps=0;x:a",
            "tippy-args-v2;no-deps=0;9:a",
            "tippy-args-v2;no-deps=0;184467440737095516160:a",
            "tippy-args-v2;no-deps=0;1:λ",
            "tippy-args-v1;1",
            "tippy-args-v1;x:a",
            "tippy-args-v1;9:a",
            "tippy-args-v1;184467440737095516160:a",
            "tippy-args-v1;1:λ",
        ] {
            assert!(
                decode_args(encoded).is_err(),
                "accepted malformed payload {encoded:?}"
            );
        }
    }

    #[test]
    fn distinct_lists_that_collide_in_legacy_encoding_remain_distinct() {
        let embedded_delimiter = ["a__CLIPPY_HACKERY__b".to_string()];
        let separate_arguments = ["a".to_string(), "b".to_string()];
        let legacy = |args: &[String]| {
            args.iter().fold(String::new(), |encoded, arg| {
                encoded + arg + "__CLIPPY_HACKERY__"
            })
        };

        assert_eq!(legacy(&embedded_delimiter), legacy(&separate_arguments));
        assert_ne!(
            encode_args(false, &embedded_delimiter),
            encode_args(false, &separate_arguments)
        );
        assert_eq!(
            decode_args(&encode_args(false, &embedded_delimiter)),
            Ok(DecodedTippyArgs {
                no_deps: NoDepsFlag::Explicit(false),
                compiler_args: embedded_delimiter.to_vec(),
            })
        );
        assert_eq!(
            decode_args(&encode_args(false, &separate_arguments)),
            Ok(DecodedTippyArgs {
                no_deps: NoDepsFlag::Explicit(false),
                compiler_args: separate_arguments.to_vec(),
            })
        );
    }

    #[test]
    fn empty_v2_payload_has_the_expected_canonical_prefix() {
        assert_eq!(
            encode_args::<&str>(false, &[]),
            format!("{SCHEMA_V2_PREFIX}{NO_DEPS_FALSE_PREFIX}")
        );
    }
}
