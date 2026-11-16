// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Facts from the freeze gate's existing AWK line predicate, not a Rust AST.
//!
//! The caller retains citation ordering/counts and all gate judgments. These
//! names are neither test execution evidence nor a verdict. Unsupported text
//! must use the real legacy reader rather than manufacture a positive fact.

use std::collections::BTreeSet;

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Unsupported {
    InvalidUtf8,
    NulByte,
    LocaleSensitiveWhitespace,
    LocaleSensitiveVisibility,
}

/// Match `test_fn_exists` in `scripts/check_frozen_files.sh` for every ASCII
/// citation name. An attribute arms the next recognized `fn` line, at most six
/// physical lines later. This deliberately does not lex comments or strings.
pub(crate) fn test_functions(source: &[u8]) -> Result<BTreeSet<String>, Unsupported> {
    let source = std::str::from_utf8(source).map_err(|_| Unsupported::InvalidUtf8)?;
    if source.as_bytes().contains(&0) {
        return Err(Unsupported::NulByte);
    }
    let mut names = BTreeSet::new();
    let mut armed = None;
    for (line_number, line) in source.split('\n').enumerate() {
        let line = predicate_start(line)?;
        if line.starts_with(b"#[test]") {
            armed = Some(line_number);
            // The old AWK's `next` also skips a function on this same line.
            continue;
        }
        let Some(tail) = after_function_prefix(line) else {
            continue;
        };
        let recent = armed.take().is_some_and(|at| line_number - at <= 6);
        let length = tail.iter().take_while(|byte| citation_byte(**byte)).count();
        if length == 0 {
            continue;
        }
        let after_name = ascii_space_start(&tail[length..]);
        if leading_non_ascii_space(after_name) {
            return Err(Unsupported::LocaleSensitiveWhitespace);
        }
        if recent && after_name.starts_with(b"(") {
            let name =
                std::str::from_utf8(&tail[..length]).map_err(|_| Unsupported::InvalidUtf8)?;
            names.insert(name.to_owned());
        }
    }
    Ok(names)
}

// POSIX [:space:] includes vertical-tab, unlike Rust's ASCII whitespace set.
fn ascii_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

fn ascii_space_start(bytes: &[u8]) -> &[u8] {
    let count = bytes.iter().take_while(|byte| ascii_space(**byte)).count();
    &bytes[count..]
}

fn citation_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn leading_non_ascii_space(bytes: &[u8]) -> bool {
    // No locale is supplied to this pure parser. Any non-ASCII byte at a
    // [:space:] position may need the caller's actual legacy locale rules.
    bytes.first().is_some_and(|byte| !byte.is_ascii())
}

fn predicate_start(line: &str) -> Result<&[u8], Unsupported> {
    let bytes = ascii_space_start(line.as_bytes());
    let locale_space = leading_non_ascii_space(bytes);
    let possible = if locale_space {
        std::str::from_utf8(bytes)
            .map_err(|_| Unsupported::InvalidUtf8)?
            .trim_start_matches(|character: char| {
                !character.is_ascii()
                    || matches!(character, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r')
            })
            .as_bytes()
    } else {
        bytes
    };
    if possible.strip_prefix(b"pub(").is_some_and(|visibility| {
        visibility
            .iter()
            .position(|byte| *byte == b')')
            .is_some_and(|end| !visibility[..end].is_ascii())
    }) {
        // `[a-z]+` is also locale-sensitive. Do not reinterpret a non-ASCII
        // visibility spelling as a negative match in every possible locale.
        return Err(Unsupported::LocaleSensitiveVisibility);
    }
    // A locale may consume non-ASCII whitespace in [:space:]. Fall back only
    // where doing so could recognize an attribute/function; ordinary Unicode
    // comments and other non-predicate lines remain supported.
    if locale_space
        && (possible.starts_with(b"#[test]") || after_function_prefix(possible).is_some())
    {
        return Err(Unsupported::LocaleSensitiveWhitespace);
    }
    Ok(bytes)
}

fn after_function_prefix(mut line: &[u8]) -> Option<&[u8]> {
    if let Some(rest) = line.strip_prefix(b"pub") {
        line = if let Some(visibility) = rest.strip_prefix(b"(") {
            let end = visibility.iter().position(|byte| *byte == b')')?;
            if end == 0 || !visibility[..end].iter().all(u8::is_ascii_lowercase) {
                return None;
            }
            visibility[end + 1..].strip_prefix(b" ")?
        } else {
            rest.strip_prefix(b" ")?
        };
    }
    line.strip_prefix(b"fn ")
}

#[cfg(test)]
mod tests {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    use super::*;

    fn names(source: &str) -> BTreeSet<String> {
        test_functions(source.as_bytes()).unwrap()
    }

    fn expected(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    }

    #[test]
    fn six_physical_lines_and_attribute_refresh_match_the_gate() {
        let accepted = format!("#[test]\n{}fn boundary() {{}}", "\n".repeat(5));
        let rejected = format!("#[test]\n{}fn boundary() {{}}", "\n".repeat(6));
        assert_eq!(names(&accepted), expected(&["boundary"]));
        assert!(names(&rejected).is_empty());
        assert_eq!(
            names("#[test]\n\n\n\n\n\n#[test]\nfn refreshed() {}"),
            expected(&["refreshed"])
        );
        assert_eq!(
            names("#[test]\r\n#[cfg(unix)]\r\n#[ignore]\r\nfn stacked () {}\r\n"),
            expected(&["stacked"])
        );
    }

    #[test]
    fn only_the_next_recognized_function_consumes_the_attribute() {
        assert_eq!(names("#[test]\nfn first() {}\nfn second() {}\n"), expected(&["first"]));
        assert!(names("#[test]\nfn generic<T>() {}\nfn later() {}\n").is_empty());
        assert!(names("#[test]\nfn  spaced() {}\nfn later() {}\n").is_empty());
        assert_eq!(names("#[test]\nconst fn ignored() {}\nfn later() {}\n"), expected(&["later"]));
        assert_eq!(names("#[test] fn same_line() {}\nfn later() {}\n"), expected(&["later"]));
    }

    #[test]
    fn exact_visibility_and_ascii_citation_names_are_retained() {
        assert_eq!(
            names("#[test]\npub(crate) fn case_42 () {}\n#[test]\npub fn 0data() {}\n"),
            expected(&["0data", "case_42"])
        );
        assert_eq!(
            names("#[test]\npub(in crate) fn ignored() {}\nfn later() {}\n"),
            expected(&["later"])
        );
        assert_eq!(names("#[test]\npub\tfn ignored() {}\nfn later() {}\n"), expected(&["later"]));
        assert!(names("#[test]\nfn λ() {}\nfn later() {}\n").is_empty());
    }

    #[test]
    fn the_line_predicate_does_not_become_a_rust_parser() {
        assert_eq!(
            names(
                "/*\n#[test]\nfn in_comment() {}\n*/\nlet s = r#\"\n#[test]\nfn in_string() {}\n\"#;\n"
            ),
            expected(&["in_comment", "in_string"])
        );
        assert_eq!(
            names("#[test]\nfn repeated() {}\n#[test]\nfn repeated() {}\n"),
            expected(&["repeated"])
        );
    }

    #[test]
    fn posix_ascii_space_includes_vertical_tab_and_form_feed() {
        assert_eq!(
            names("\u{b}#[test]\n\u{c}pub(self) fn whitespace\u{b}\u{c}\r\t () {}\n"),
            expected(&["whitespace"])
        );
    }

    #[test]
    fn unicode_comments_work_but_locale_sensitive_predicates_fall_back() {
        assert_eq!(
            names(
                "// résumé 日本語\n\u{2003}// ordinary comment\n#[test]\n// 再確認\nfn unicode_comment() {}\n"
            ),
            expected(&["unicode_comment"])
        );
        for source in [
            "\u{2003}#[test]\nfn leading() {}\n",
            "#[test]\n\u{a0}pub(crate) fn leading() {}\n",
            "#[test]\nfn after_name\u{2003}() {}\n",
            "#[test]\nfn ascii_prefixλ() {}\n",
        ] {
            assert_eq!(
                test_functions(source.as_bytes()),
                Err(Unsupported::LocaleSensitiveWhitespace)
            );
        }
        assert_eq!(test_functions(&[0xff]), Err(Unsupported::InvalidUtf8));
        assert_eq!(test_functions(b"//\0\n"), Err(Unsupported::NulByte));
        assert_eq!(
            test_functions("#[test]\npub(é) fn localized() {}\n".as_bytes()),
            Err(Unsupported::LocaleSensitiveVisibility)
        );
        assert_eq!(
            test_functions("#[test]\n\u{2003}pub(é) fn localized() {}\n".as_bytes()),
            Err(Unsupported::LocaleSensitiveVisibility)
        );
    }

    fn legacy_program() -> &'static str {
        // Differential qualification executes the unchanged legacy predicate
        // from the actual gate source, rather than a second copied model.
        let gate = include_str!("../../../scripts/check_frozen_files.sh");
        let function = gate
            .split_once("test_fn_exists() {\n")
            .expect("legacy test_fn_exists function")
            .1
            .split_once("\n}\n")
            .expect("legacy function end")
            .0;
        function
            .split_once("awk -v want=\"$2\" '\n")
            .expect("legacy AWK invocation")
            .1
            .rsplit_once("\n  ' \"$1\"")
            .expect("legacy AWK closing quote")
            .0
    }

    fn legacy_matches(source: &[u8], wanted: &str) -> bool {
        let mut child = Command::new("awk")
            .arg("-v")
            .arg(format!("want={wanted}"))
            .arg(legacy_program())
            .env("LC_ALL", "C")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .expect("actual awk for predicate conformance");
        let mut input = child.stdin.take().unwrap();
        let write = input.write_all(source);
        drop(input);
        let output = child.wait_with_output().expect("wait for actual awk");
        write.expect("write owned predicate fixture");
        assert!(
            matches!(output.status.code(), Some(0 | 1)),
            "actual awk refused: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        output.status.success()
    }

    #[test]
    fn supported_facts_match_the_actual_legacy_awk_predicate() {
        let sources = [
            "#[test]\nfn first() {}\nfn later() {}\n",
            "#[test] fn first() {}\nfn later() {}\n",
            "#[test]\nfn first<T>() {}\nfn later() {}\n",
            "#[test]\npub(crate) fn first () {}\n",
            "#[test]\npub(in crate) fn first() {}\nfn later() {}\n",
            "#[test]\nfn  first() {}\nfn later() {}\n",
            "/*\n#[test]\nfn first() {}\n*/\n",
            "// 日本語\n#[test]\n\u{b}fn first\u{c} () {}\n",
            "#[test]\n\n\n\n\n\nfn first() {}",
            "#[test]\n\n\n\n\n\n\nfn first() {}",
            "#[test]\nfn first_extra() {}\n",
        ];
        for source in sources {
            let facts = names(source);
            for wanted in ["first", "later", "first_extra", "absent"] {
                assert_eq!(
                    facts.contains(wanted),
                    legacy_matches(source.as_bytes(), wanted),
                    "wanted={wanted}, source={source:?}"
                );
            }
        }
    }
}
