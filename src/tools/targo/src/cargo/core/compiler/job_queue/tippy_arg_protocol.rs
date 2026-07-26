//! Trust: Trust-authored, no upstream counterpart. The job queue prints a
//! "run this to reproduce" hint containing the driver's arguments; rendering
//! them from the lossy legacy channel would print a command that does not
//! reproduce the run. Kept beside the job queue rather than in
//! `util::tippy_arg_protocol` because shell rendering is a display concern,
//! while the codec there is the wire format.

use std::borrow::Cow;
use std::ffi::OsStr;

use crate::util::tippy_arg_protocol::decode_args;
pub(super) use crate::util::tippy_arg_protocol::{CLIPPY_ARGS_ENV, TIPPY_ENCODED_ARGS_ENV};

const LEGACY_ARGS_DELIMITER: &str = "__CLIPPY_HACKERY__";

/// Decode the argument channel used by Tippy and render it for a suggested
/// shell command without losing argument boundaries.
///
/// The versioned channel is authoritative whenever it is present. In
/// particular, a malformed canonical payload must not fall back to the lossy
/// legacy delimiter channel. The legacy channel remains available only for
/// inherited Clippy frontends that do not set `TIPPY_ENCODED_ARGS`.
pub(super) fn suggested_args_suffix(
    encoded_args: Option<&OsStr>,
    legacy_args: Option<&OsStr>,
) -> Result<String, String> {
    let args = decode_arg_channel(encoded_args, legacy_args)?;
    if args.is_empty() {
        return Ok(String::new());
    }

    let rendered = args
        .into_iter()
        .map(|arg| shell_escape::escape(Cow::Owned(arg)).into_owned())
        .collect::<Vec<_>>()
        .join(" ");
    Ok(format!(" -- {rendered}"))
}

fn decode_arg_channel(
    encoded_args: Option<&OsStr>,
    legacy_args: Option<&OsStr>,
) -> Result<Vec<String>, String> {
    if let Some(encoded_args) = encoded_args {
        let encoded_args = encoded_args
            .to_str()
            .ok_or_else(|| format!("{TIPPY_ENCODED_ARGS_ENV} is not valid UTF-8"))?;
        return decode_args(encoded_args).map(|payload| payload.compiler_args);
    }

    let legacy_args = legacy_args
        .map(|args| {
            args.to_str()
                .ok_or_else(|| format!("{CLIPPY_ARGS_ENV} is not valid UTF-8"))
        })
        .transpose()?
        .unwrap_or_default();
    Ok(legacy_args
        .split(LEGACY_ARGS_DELIMITER)
        .filter(|arg| !arg.is_empty())
        .map(str::to_string)
        .collect())
}

#[cfg(test)]
mod tests {
    use super::suggested_args_suffix;
    use crate::util::tippy_arg_protocol::encode_args;
    use std::borrow::Cow;
    use std::ffi::OsStr;

    fn expected_suffix(args: &[&str]) -> String {
        let rendered = args
            .iter()
            .map(|arg| shell_escape::escape(Cow::Borrowed(*arg)).into_owned())
            .collect::<Vec<_>>()
            .join(" ");
        format!(" -- {rendered}")
    }

    #[test]
    fn canonical_channel_preserves_embedded_legacy_delimiter_and_boundaries() {
        let args = [
            "-Wclippy::pedantic__CLIPPY_HACKERY__-Aclippy::all",
            "--cfg=feature=\"lambda value\"",
            "",
            "λ-safe",
        ];
        let encoded = encode_args(false, &args);

        assert_eq!(
            suggested_args_suffix(
                Some(OsStr::new(&encoded)),
                Some(OsStr::new("attacker__CLIPPY_HACKERY__fallback")),
            ),
            Ok(expected_suffix(&args))
        );
    }

    #[test]
    fn v2_no_deps_field_is_not_rendered_as_a_compiler_argument() {
        let args = ["--cfg", "--no-deps"];
        let encoded = encode_args(true, &args);
        assert_eq!(
            suggested_args_suffix(Some(OsStr::new(&encoded)), None),
            Ok(expected_suffix(&args))
        );
    }

    #[test]
    fn malformed_canonical_payload_never_falls_back_to_legacy_args() {
        let valid_legacy =
            OsStr::new("-Wclippy::pedantic__CLIPPY_HACKERY__-Aclippy::all__CLIPPY_HACKERY__");
        for malformed in [
            "",
            "1:a",
            "tippy-args-v2;1:a",
            "tippy-args-v1;1",
            "tippy-args-v1;x:a",
            "tippy-args-v1;9:a",
            "tippy-args-v1;184467440737095516160:a",
            "tippy-args-v1;1:λ",
        ] {
            assert!(
                suggested_args_suffix(Some(OsStr::new(malformed)), Some(valid_legacy)).is_err(),
                "accepted malformed canonical payload {malformed:?} or fell back to legacy args"
            );
        }
    }

    #[test]
    fn legacy_channel_is_used_only_when_canonical_channel_is_absent() {
        let legacy = "-Wclippy::pedantic__CLIPPY_HACKERY__-Aclippy::all__CLIPPY_HACKERY__";
        assert_eq!(
            suggested_args_suffix(None, Some(OsStr::new(legacy))),
            Ok(expected_suffix(&["-Wclippy::pedantic", "-Aclippy::all"]))
        );
        assert_eq!(suggested_args_suffix(None, None), Ok(String::new()));
    }
}
