//! A path as one POSIX shell word, for a refusal that names the command which
//! recovers from it. Its reader pastes that command into a shell, so the shell
//! must read the path in it back as exactly that path, whatever it contains.

use std::path::Path;

/// `path` as one POSIX shell word. A path made only of the characters Python's
/// `shlex.quote` leaves bare (ASCII letters and digits and `_@%+=:,./-`) is
/// itself, as in the `chmod` scripts/build-slot's `unsafe_directory_reason`
/// names; any other is put in single quotes, each single quote in it written
/// `'\''` (shlex writes `'"'"'`, the same word to the shell), and an empty one
/// is `''`. The text is the path as `Path::display` shows it, so a path that is
/// not UTF-8 is shown with U+FFFD for each invalid sequence and its command
/// names another path: a message String cannot carry those bytes.
pub(crate) fn quoted(path: &Path) -> String {
    let text = path.display().to_string();
    let bare = |byte: u8| byte.is_ascii_alphanumeric() || b"_@%+=:,./-".contains(&byte);
    if !text.is_empty() && text.bytes().all(bare) {
        return text;
    }
    format!("'{}'", text.replace('\'', r"'\''"))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::quoted;

    #[test]
    fn a_path_of_only_safe_characters_stays_bare() {
        for path in ["/home/user/.cache/build-slot", "/a_b@c%d+e=f:g,h.i/j-K9", "relative"] {
            assert_eq!(quoted(Path::new(path)), path);
        }
    }

    #[test]
    fn any_other_path_is_one_single_quoted_word() {
        for (path, word) in [
            ("", "''"),
            ("/tmp/a b", "'/tmp/a b'"),
            ("/tmp/it's", r"'/tmp/it'\''s'"),
            ("/tmp/it's a 'repo'", r"'/tmp/it'\''s a '\''repo'\'''"),
            ("'", r"''\'''"),
            ("~/x", "'~/x'"),
            ("/tmp/né", "'/tmp/né'"),
            ("/tmp/a\nb", "'/tmp/a\nb'"),
            (
                r#"/t/$HOME;rm `x` "y" \z*?[]!#&|<>(){}"#,
                r#"'/t/$HOME;rm `x` "y" \z*?[]!#&|<>(){}'"#,
            ),
        ] {
            assert_eq!(quoted(Path::new(path)), word, "{path:?}");
        }
    }
}
