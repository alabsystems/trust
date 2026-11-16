use super::FrontendArgs;
use super::tippy_arg_protocol::{CLIPPY_ARGS_ENV, TIPPY_ENCODED_ARGS_ENV, encode_args};

impl FrontendArgs {
    pub fn channels(&self) -> [(&'static str, String); 2] {
        let mut legacy = self.compiler_args.clone();
        if self.no_deps {
            legacy.push("--no-deps".into());
        }
        let mut joined = legacy.join("__CLIPPY_HACKERY__");
        if !legacy.is_empty() {
            joined.push_str("__CLIPPY_HACKERY__");
        }
        // Only the historical spelling after `--` needs compiler option
        // parsing: it may be a value (`--cfg --no-deps`) rather than a flag.
        // The existing v1 length-prefixed driver protocol delegates that exact
        // grammar to the selected driver, without guessing or losing bytes.
        // Normal commands use the explicit v2 no_deps field.
        let encoded = if self.compiler_args.iter().any(|arg| arg == "--no-deps") {
            let mut encoded = String::from("tippy-args-v1;");
            use std::fmt::Write as _;
            let mut deferred = self.compiler_args.clone();
            if self.no_deps {
                deferred.insert(0, "--no-deps".into());
            }
            for arg in &deferred {
                write!(encoded, "{}:{arg}", arg.len()).unwrap();
            }
            encoded
        } else {
            encode_args(self.no_deps, &self.compiler_args)
        };
        [(CLIPPY_ARGS_ENV, joined), (TIPPY_ENCODED_ARGS_ENV, encoded)]
    }
}

#[cfg(test)]
mod tests {
    // Tippy compiles this file too (`#[path]` in src/tools/tippy/src/main.rs),
    // so reach the protocol through the including module, never `crate::`:
    // targo-core's `lint_frontend` and tippy's crate root each bind it.
    use super::super::tippy_arg_protocol::{NoDepsFlag, decode_args};
    use super::*;

    #[test]
    fn ordinary_flags_keep_explicit_modern_transport_and_exact_boundaries() {
        let args = FrontendArgs::parse(
            [
                "--fix",
                "-p",
                "crate",
                "--",
                "-D",
                "warnings",
                "has__CLIPPY_HACKERY__text",
            ]
            .map(String::from),
        );
        assert_eq!(args.verb, "fix");
        assert_eq!(args.args, ["-p", "crate"]);
        let decoded = decode_args(&args.channels()[1].1).unwrap();
        assert_eq!(decoded.no_deps, NoDepsFlag::Explicit(true));
        assert_eq!(
            decoded.compiler_args,
            ["-D", "warnings", "has__CLIPPY_HACKERY__text"]
        );
    }

    #[test]
    fn legacy_spelling_is_kept_exact_for_the_actual_compiler_grammar() {
        let args = FrontendArgs::parse(["--", "--cfg", "--no-deps", "--no-deps"].map(String::from));
        let decoded = decode_args(&args.channels()[1].1).unwrap();
        assert_eq!(decoded.no_deps, NoDepsFlag::LegacyInBand);
        assert_eq!(decoded.compiler_args, args.compiler_args);
    }
}
