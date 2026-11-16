// The cut that turns a frozen oracle file into its PRODUCTION SECTION.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//
// Shared by two compilations, which is why it is plain `//` text and not a module doc: the
// crate's build script `include!`s it (build.rs, where it prepares the refinement harnesses'
// pinned and current sections), and the library declares it as a `#[cfg(test)]` module so the
// cut itself is under test. One text, so the tested cut IS the one the build script runs.
//
// Everything a refinement harness compares, it compares on this cut's output. A cut that drops
// production code drops it from BOTH halves of the harness — the behavioural comparison and the
// census — so the cut refuses any shape it cannot account for instead of guessing where the
// tests begin. Measured 2026-09-28: the previous end-of-module check only asked whether the
// file's LAST non-blank line was `}`, so a production fn appended after the tests module (its
// own closing brace being that last line) was cut away, and all eleven refinement-harness
// tests passed on a file whose moved code none of them saw. The end is now found by matching
// the module's opening brace, skipping strings, raw strings, char literals and comments.

/// `include!` cannot accept another module's leading `//!` comments: demote only that
/// contiguous prefix to ordinary `//` comments. Every production token after it is left
/// untouched.
fn demote_inner_docs(source: &str) -> String {
    let mut generated = String::with_capacity(source.len());
    let mut in_module_docs = true;
    for line in source.split_inclusive('\n') {
        if in_module_docs && line.starts_with("//!") {
            generated.push_str("//");
            generated.push_str(&line[3..]);
        } else {
            in_module_docs = false;
            generated.push_str(line);
        }
    }
    generated
}

/// The production section of a frozen file: inner docs demoted, and the trailing inline
/// `#[cfg(test)] mod <tests_module> { … }` removed. The module must occur exactly once, no
/// other inline test module may precede it, and nothing but whitespace may follow the brace
/// that closes it — otherwise the cut would drop what follows from every comparison.
fn production_section(source: &str, tests_module: &str) -> Result<String, String> {
    let demoted = demote_inner_docs(source);
    let marker = format!("\n#[cfg(test)]\nmod {tests_module} {{\n");
    let mut hits = demoted.match_indices(&marker).map(|(at, _)| at);
    let Some(at) = hits.next() else {
        return Err(format!("no inline `#[cfg(test)] mod {tests_module} {{` found"));
    };
    if hits.next().is_some() {
        return Err(format!("more than one inline `#[cfg(test)] mod {tests_module} {{`"));
    }
    // The marker ends `{\n`: its `{` is the module's opening brace.
    let open = at + marker.len() - 2;
    let close = closing_brace(&demoted, open)
        .map_err(|e| format!("cannot find the end of `mod {tests_module}`: {e}"))?;
    if let Some(after) = demoted[close..].lines().map(str::trim).find(|l| !l.is_empty()) {
        return Err(format!(
            "text follows the closing brace of `mod {tests_module}`, which the cut would drop \
             from every comparison: `{after}`"
        ));
    }
    if demoted[..at].contains("#[cfg(test)]\nmod ") {
        return Err(format!("an inline test module precedes `mod {tests_module}`"));
    }
    Ok(demoted[..at + 1].to_string())
}

/// The byte offset just past the `}` that closes the `{` at byte `open`. Braces inside line and
/// (nested) block comments, string and byte-string literals (escapes honoured), raw strings
/// (any number of `#`), and char literals (`'{'`, `'\u{7b}'`) are skipped; a lifetime or label
/// (`'a`) is not a literal. Anything unterminated is refused, never guessed.
fn closing_brace(source: &str, open: usize) -> Result<usize, String> {
    let chars: Vec<(usize, char)> =
        source[open..].char_indices().map(|(offset, c)| (open + offset, c)).collect();
    if chars.first().map(|&(_, c)| c) != Some('{') {
        return Err(format!("byte {open} is not an opening brace"));
    }
    let at = |i: usize| chars.get(i).map(|&(_, c)| c);
    let ident = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
    let mut depth = 0usize;
    let mut i = 0;
    while let Some(c) = at(i) {
        match c {
            '/' if at(i + 1) == Some('/') => {
                while at(i).is_some_and(|c| c != '\n') {
                    i += 1;
                }
                continue;
            }
            '/' if at(i + 1) == Some('*') => {
                let mut nest = 1usize;
                i += 2;
                while nest > 0 {
                    match (at(i), at(i + 1)) {
                        (None, _) => return Err("unterminated block comment".to_string()),
                        (Some('/'), Some('*')) => {
                            nest += 1;
                            i += 2;
                        }
                        (Some('*'), Some('/')) => {
                            nest -= 1;
                            i += 2;
                        }
                        _ => i += 1,
                    }
                }
                continue;
            }
            '"' => {
                i += 1;
                loop {
                    match at(i) {
                        None => return Err("unterminated string literal".to_string()),
                        Some('\\') => i += 2,
                        Some('"') => break,
                        Some(_) => i += 1,
                    }
                }
                i += 1;
                continue;
            }
            // `r"…"`, `r#"…"#`, `br"…"`; `r#ident` is a raw identifier and falls through.
            'r' if matches!(at(i + 1), Some('"' | '#'))
                && (i == 0
                    || !ident(at(i - 1))
                    || (at(i - 1) == Some('b') && (i == 1 || !ident(at(i - 2))))) =>
            {
                let hashes = (i + 1..).take_while(|&j| at(j) == Some('#')).count();
                if at(i + 1 + hashes) == Some('"') {
                    i += hashes + 2;
                    loop {
                        match at(i) {
                            None => return Err("unterminated raw string literal".to_string()),
                            Some('"') if (1..=hashes).all(|k| at(i + k) == Some('#')) => break,
                            Some(_) => i += 1,
                        }
                    }
                    i += hashes + 1;
                    continue;
                }
            }
            '\'' if at(i + 1) == Some('\\') => {
                // An escaped char literal: `'\n'`, `'\''`, `'\u{7b}'`.
                let mut j = i + 3;
                while at(j) != Some('\'') {
                    if at(j).is_none_or(|c| c == '\n') {
                        return Err("unterminated char literal".to_string());
                    }
                    j += 1;
                }
                i = j + 1;
                continue;
            }
            '\'' if at(i + 2) == Some('\'') => {
                // A plain char literal, `'{'` included.
                i += 3;
                continue;
            }
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(chars[i].0 + 1);
                }
            }
            _ => {}
        }
        i += 1;
    }
    Err("the opening brace is never closed".to_string())
}

#[cfg(test)]
mod tests {
    use super::{closing_brace, production_section};

    const PRODUCTION: &str = "//! inner doc\nfn oracle() -> bool {\n    true\n}\n";

    fn with_tests_module(body: &str, after: &str) -> String {
        format!("{PRODUCTION}\n#[cfg(test)]\nmod tests {{\n{body}}}\n{after}")
    }

    /// Braces a naive count would miscount — in strings, raw strings, byte strings, char
    /// literals, escaped chars and comments — do not move the end of the module, and the cut
    /// returns exactly the production text (inner docs demoted).
    #[test]
    fn the_cut_skips_braces_that_are_not_code() {
        let body = concat!(
            "    // a } in a line comment\n",
            "    /* a } in a /* nested */ block comment */\n",
            "    const S: &str = \"}\\\"}\";\n",
            "    const R: &str = r#\"} \" }\"#;\n",
            "    const B: &[u8] = br\"}\";\n",
            "    const C: [char; 3] = ['}', '\\u{7d}', '\\''];\n",
            "    fn f<'a>(x: &'a str) -> &'a str { x }\n",
            "    fn r#match() {}\n",
        );
        let source = with_tests_module(body, "\n");
        assert_eq!(
            production_section(&source, "tests").as_deref(),
            Ok("// inner doc\nfn oracle() -> bool {\n    true\n}\n\n"),
        );
    }

    /// THE HOLE THIS CLOSES. Production code appended after the tests module ends the file
    /// with its OWN `}`, which the old last-line check accepted; the cut then dropped it from
    /// every comparison. It is refused, and the refusal names the text.
    #[test]
    fn code_after_the_tests_module_is_refused() {
        let appended = "pub(crate) fn appended_after_the_tests_module() -> bool {\n    true\n}\n";
        let source = with_tests_module("    #[test]\n    fn t() {}\n", appended);
        let old_check = source.trim_end().lines().next_back().map(str::trim) == Some("}");
        assert!(old_check, "the fixture must be the shape the old check accepted");
        let err = production_section(&source, "tests").expect_err("appended code was cut away");
        assert!(err.contains("appended_after_the_tests_module"), "{err}");
        // A trailing comment is refused too: nothing but whitespace may follow.
        assert!(production_section(&with_tests_module("", "// trailing\n"), "tests").is_err());
        // A `}` at column 0 INSIDE a string in the module does not end it early.
        let tricky = with_tests_module("    const S: &str = \"\n}\n\";\n", "");
        assert!(production_section(&tricky, "tests").is_ok());
    }

    /// Unterminated text is refused, never guessed.
    #[test]
    fn unterminated_text_is_refused() {
        for body in ["    const S: &str = \"open;\n", "    /* open\n", "    fn f() {\n"] {
            let source = format!("{PRODUCTION}\n#[cfg(test)]\nmod tests {{\n{body}");
            assert!(production_section(&source, "tests").is_err(), "{body:?} was accepted");
        }
        assert!(closing_brace("x{}", 0).is_err(), "a non-brace start is refused");
        assert_eq!(closing_brace("{ {} }tail", 0), Ok(6));
    }

    /// Both frozen files the refinement harnesses cut, as the working tree has them, are cut
    /// successfully — the same check the build script makes, run where a failure is a red
    /// test with a reason rather than a disarmed harness.
    #[test]
    fn both_frozen_files_cut_cleanly() {
        for (source, module) in [
            (include_str!("mir_differential.rs"), "session_state_tests"),
            (include_str!("flip_registry.rs"), "tests"),
        ] {
            let section = production_section(source, module).expect("the frozen file cuts");
            assert!(section.len() < source.len(), "the cut removed nothing");
        }
    }
}
