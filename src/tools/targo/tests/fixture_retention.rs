// Trust: a native test fixture never outlives a passing test as an untracked
// directory of the source tree (TARGO-TEST-TMP-HYGIENE-1).
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates
//
// `tempfile::TempDir::keep` disowns a directory: nothing removes it afterwards.
// `tests/output_integrity.rs` once created its fixtures with
// `tempdir_in(std::env::current_dir())` (this crate's source directory under
// `x.py test`) and kept them before the outcome was known, so every run left
// `.tmpXXXXXX` packages in `src/tools/targo/`, untracked and not ignored.
//
// This scan holds every test source under `tests/` to one rule. A disowning
// call (`.keep(`, `TempDir::keep(`, `.disable_cleanup(true)`) is allowed only
//   (a) inside a `fn drop`, a failure-path guard that keeps the directory for
//       postmortem only when its test did not pass, or
//   (b) in a function that places its directory under the `.ubd/` retention
//       area (it names `".ubd/`), which `src/tools/targo/.gitignore` ignores.
// Anything else is an unconditional keep and fails here with its file and line.
// The scan lexes Rust well enough to skip comments, strings and character
// literals, so a pattern quoted in text never counts and never hides a brace.

use std::fs;
use std::path::{Path, PathBuf};

/// Rule (a): the call sits in a `fn drop`.
const GUARD: Option<&str> = Some("failure-path Drop guard");
/// Rule (b): the enclosing function names the ignored `.ubd/` area.
const RETAINED: Option<&str> = Some("ignored .ubd/ retention area");

/// Marks each byte of `source` as code (true) or comment/literal (false).
fn code_mask(source: &[u8]) -> Vec<bool> {
    let ident = |byte: u8| byte == b'_' || byte.is_ascii_alphanumeric();
    let mut mask = vec![true; source.len()];
    let mut index = 0;
    let blank = |mask: &mut Vec<bool>, from: usize, to: usize| {
        for flag in &mut mask[from..to.min(source.len())] {
            *flag = false;
        }
    };
    while index < source.len() {
        let rest = &source[index..];
        if rest.starts_with(b"//") {
            let end = rest
                .iter()
                .position(|&byte| byte == b'\n')
                .map_or(source.len(), |offset| index + offset);
            blank(&mut mask, index, end);
            index = end;
        } else if rest.starts_with(b"/*") {
            let mut depth = 0usize;
            let mut end = index;
            while end < source.len() {
                if source[end..].starts_with(b"/*") {
                    depth += 1;
                    end += 2;
                } else if source[end..].starts_with(b"*/") {
                    depth -= 1;
                    end += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    end += 1;
                }
            }
            blank(&mut mask, index, end);
            index = end;
        } else if source[index] == b'r'
            && (index == 0
                || !ident(source[index - 1])
                || (matches!(source[index - 1], b'b' | b'c')
                    && (index < 2 || !ident(source[index - 2]))))
            && {
                let hashes = rest[1..].iter().take_while(|&&byte| byte == b'#').count();
                rest.get(1 + hashes) == Some(&b'"')
            }
        {
            let hashes = rest[1..].iter().take_while(|&&byte| byte == b'#').count();
            let mut close = vec![b'"'];
            close.extend(std::iter::repeat_n(b'#', hashes));
            let body = index + 2 + hashes;
            let end = source[body..]
                .windows(close.len())
                .position(|window| window == close.as_slice())
                .map_or(source.len(), |offset| body + offset + close.len());
            blank(&mut mask, index, end);
            index = end;
        } else if source[index] == b'"' {
            let mut end = index + 1;
            while end < source.len() && source[end] != b'"' {
                end += if source[end] == b'\\' { 2 } else { 1 };
            }
            blank(&mut mask, index, end + 1);
            index = end + 1;
        } else if source[index] == b'\'' {
            // A character literal, or a lifetime or label (which stays code).
            // An escape's closing quote follows the escaped character, as in '\''.
            let end = if rest.get(1) == Some(&b'\\') {
                rest.get(3..).and_then(|tail| {
                    tail.iter()
                        .position(|&byte| byte == b'\'')
                        .map(|offset| index + 3 + offset + 1)
                })
            } else {
                let width = rest.get(1).map_or(1, |&lead| match lead.leading_ones() {
                    2 => 2,
                    3 => 3,
                    4 => 4,
                    _ => 1,
                });
                (rest.get(1 + width) == Some(&b'\'')).then_some(index + 2 + width)
            };
            match end {
                Some(end) => {
                    blank(&mut mask, index, end);
                    index = end;
                }
                None => index += 1,
            }
        } else {
            index += 1;
        }
    }
    mask
}

/// Every `fn` item with a body: (name, body start `{`, body end `}`).
fn functions(source: &[u8], mask: &[bool]) -> Vec<(String, usize, usize)> {
    let ident = |byte: u8| byte == b'_' || byte.is_ascii_alphanumeric();
    let mut found = Vec::new();
    let mut index = 0;
    while index + 3 < source.len() {
        let keyword = mask[index]
            && source[index..].starts_with(b"fn")
            && (index == 0 || !ident(source[index - 1]))
            && source[index + 2].is_ascii_whitespace();
        if !keyword {
            index += 1;
            continue;
        }
        let mut cursor = index + 2;
        while cursor < source.len() && source[cursor].is_ascii_whitespace() {
            cursor += 1;
        }
        let name_start = cursor;
        while cursor < source.len() && ident(source[cursor]) {
            cursor += 1;
        }
        let name = String::from_utf8_lossy(&source[name_start..cursor]).into_owned();
        let mut depth = 0isize;
        let mut body = None;
        while cursor < source.len() {
            if mask[cursor] {
                match source[cursor] {
                    b'(' | b'[' => depth += 1,
                    b')' | b']' => depth -= 1,
                    b'{' if depth == 0 => {
                        body = Some(cursor);
                        break;
                    }
                    b';' if depth == 0 => break,
                    _ => {}
                }
            }
            cursor += 1;
        }
        if let Some(open) = body {
            let mut braces = 0usize;
            let mut close = source.len();
            for (offset, &byte) in source[open..].iter().enumerate() {
                if !mask[open + offset] {
                    continue;
                }
                if byte == b'{' {
                    braces += 1;
                } else if byte == b'}' {
                    braces -= 1;
                    if braces == 0 {
                        close = open + offset;
                        break;
                    }
                }
            }
            found.push((name, open, close));
        }
        index = cursor.max(index + 2);
    }
    found
}

/// Each disowning call in `source`: its 1-based line and the rule that allows
/// it, if any.
fn disowning_sites(source: &str) -> Vec<(usize, Option<&'static str>)> {
    let bytes = source.as_bytes();
    let mask = code_mask(bytes);
    // One ASCII byte per source byte, so match offsets index `source` too.
    let code: String = bytes
        .iter()
        .zip(&mask)
        .map(|(&byte, &code)| match (code, byte) {
            (true, byte) if byte.is_ascii() => byte as char,
            (_, b'\n') => '\n',
            _ => ' ',
        })
        .collect();
    let calls =
        regex::Regex::new(r"(?:\.|::)\s*keep\s*\(|\.\s*disable_cleanup\s*\(\s*true\s*\)").unwrap();
    let functions = functions(bytes, &mask);
    calls
        .find_iter(&code)
        .map(|call| {
            let at = call.start();
            let line = 1 + source[..at].matches('\n').count();
            let enclosing = functions
                .iter()
                .filter(|(_, open, close)| *open < at && at < *close)
                .max_by_key(|(_, open, _)| *open);
            let allowed_by = match enclosing {
                Some((name, _, _)) if name == "drop" => GUARD,
                Some((_, open, close)) if source[*open..*close].contains("\".ubd/") => RETAINED,
                _ => None,
            };
            (line, allowed_by)
        })
        .collect()
}

fn test_sources(root: &Path) -> Vec<PathBuf> {
    let mut sources: Vec<_> = walkdir::WalkDir::new(root)
        .into_iter()
        .map(Result::unwrap)
        .filter(|entry| entry.file_type().is_file())
        .map(walkdir::DirEntry::into_path)
        .filter(|path| path.extension().is_some_and(|extension| extension == "rs"))
        .collect();
    sources.sort();
    sources
}

/// `disowning_sites` over a source given one line per element.
fn sites(lines: &[&str]) -> Vec<(usize, Option<&'static str>)> {
    disowning_sites(&lines.join("\n"))
}

#[test]
fn scanner_classifies_known_shapes() {
    // The shape that leaked `.tmpXXXXXX` packages into the source tree.
    let leak = sites(&[
        "fn leak() {",
        "    let root = tempfile::tempdir_in(std::env::current_dir().unwrap())",
        "        .unwrap()",
        "        .keep();",
        "}",
    ]);
    assert_eq!(leak, [(4, None)]);
    let guard = sites(&[
        "impl Drop for World {",
        "    fn drop(&mut self) {",
        "        if std::thread::panicking() {",
        "            eprintln!(\"kept {}\", self.0.take().unwrap().keep().display());",
        "        }",
        "    }",
        "}",
    ]);
    assert_eq!(guard, [(4, GUARD)]);
    let retained = sites(&[
        "fn world() -> PathBuf {",
        "    let base = std::env::current_dir().unwrap().join(\".ubd/native-x.noindex\");",
        "    tempfile::tempdir_in(base).unwrap().keep()",
        "}",
    ]);
    assert_eq!(retained, [(3, RETAINED)]);
    // Literals and comments neither count as calls nor unbalance a body; a
    // `drop` helper's text does not excuse the next function's keep.
    let quoted = sites(&[
        "fn drop(&mut self) {}",
        "// x.keep();",
        "fn leak() {",
        "    let _ = \"} .keep() {\";",
        "    let _ = r#\"\"}{\"#;",
        "    let _ = ['}', '\\'', '\"'];",
        "    let _: &'static str = \"\";",
        "    /* .keep() } */",
        "    dir.disable_cleanup(true);",
        "    TempDir::keep(dir);",
        "}",
    ]);
    assert_eq!(quoted, [(9, None), (10, None)]);
}

#[test]
fn test_fixtures_are_never_kept_unconditionally() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let ignore = fs::read_to_string(crate_root.join(".gitignore")).unwrap();
    assert!(
        ignore.lines().any(|line| line.trim() == "/.ubd/"),
        "rule (b) relies on src/tools/targo/.gitignore ignoring /.ubd/"
    );
    let sources = test_sources(&crate_root.join("tests"));
    assert!(
        sources.len() > 100,
        "scanned only {} test sources",
        sources.len()
    );
    let mut violations = Vec::new();
    let mut guards = 0;
    let mut retentions = 0;
    for path in &sources {
        let source = String::from_utf8_lossy(&fs::read(path).unwrap()).into_owned();
        if !source.contains("keep") && !source.contains("disable_cleanup") {
            continue;
        }
        for (line, allowed_by) in disowning_sites(&source) {
            if allowed_by == GUARD {
                guards += 1;
            } else if allowed_by == RETAINED {
                retentions += 1;
            } else {
                violations.push(format!(
                    "{}:{line}",
                    path.strip_prefix(crate_root).unwrap().display()
                ));
            }
        }
    }
    // Positive controls: the tree has failure-path guards and `.ubd/`
    // retention today, so a scanner that saw no calls cannot pass vacuously.
    assert!(
        guards > 0 && retentions > 0,
        "guards={guards} retentions={retentions}"
    );
    assert!(
        violations.is_empty(),
        "test fixtures kept unconditionally outside the ignored .ubd/ area; \
         remove them when the test passes and keep them only from a Drop guard \
         on failure (see `Fixture` in tests/output_integrity.rs):\n  {}",
        violations.join("\n  ")
    );
}
