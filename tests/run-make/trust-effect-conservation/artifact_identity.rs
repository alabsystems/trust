// Trust: artifact identity controls for the effect-conservation recipe.
//! Resolve a human fixture path to the exact symbol in its artifact.
//! Display paths select assertions; they never stand in for linker identity.

use std::collections::{BTreeMap, BTreeSet};

use crate::serde_json::Value;

pub fn function_rows(sidecar: &Value) -> BTreeMap<&str, &Value> {
    let mut rows = BTreeMap::new();
    let mut symbols = BTreeSet::new();
    for row in sidecar["functions"].as_array().expect("a function list") {
        let path = row["def_path"].as_str().expect("a definition path");
        let symbol = row["function"].as_str().expect("a linker symbol");
        assert!(!path.is_empty() && !symbol.is_empty(), "missing identity: {row}");
        assert!(rows.insert(path, row).is_none(), "ambiguous definition path: {path}");
        assert!(symbols.insert(symbol), "duplicate linker symbol: {symbol}");
    }
    rows
}

pub fn function_symbol<'a>(sidecar: &'a Value, path: &str) -> &'a str {
    let rows = function_rows(sidecar);
    let row = *rows
        .get(path)
        .unwrap_or_else(|| panic!("no sidecar row for `{path}`"));
    row["function"].as_str().expect("a linker symbol")
}

/// Whether `line` is the top-level header of `fn @{symbol}(`. The printer puts the
/// calling convention (`rustcc`, ...) and other attribute keywords before `fn`, so a
/// header may carry lowercase keyword tokens ahead of it; a comment, an instruction or
/// an indented line never qualifies.
fn is_function_header(line: &str, symbol: &str) -> bool {
    let header = format!("fn @{symbol}(");
    let Some(at) = line.find(&header) else { return false };
    (at == 0 || line[..at].ends_with(' '))
        && line[..at].split_whitespace().all(|token| {
            token.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
        })
        && !line.starts_with(char::is_whitespace)
}

/// Exact body lookup: a missing, repeated or unterminated body must not make a
/// negative mutation check pass merely because no instruction was inspected.
pub fn body_lines(text: &str, symbol: &str) -> Vec<String> {
    let lines: Vec<&str> = text.lines().collect();
    let starts: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| is_function_header(line, symbol).then_some(i))
        .collect();
    assert_eq!(starts.len(), 1, "one exact body for `{symbol}`");
    let body = &lines[starts[0]..];
    let end = body.iter().position(|line| *line == "}").expect("a closed function body");
    body[..end]
        .iter()
        .map(|line| line.split(" ;").next().unwrap_or(line).trim().to_string())
        .filter(|line| !line.is_empty() && !line.starts_with(';'))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::serde_json::json;

    fn rows() -> Value {
        json!({"functions": [
            {"function": "_R_mangled_guard", "def_path": "guard_scope"},
            {"function": "guard_scope", "def_path": "unrelated"}
        ]})
    }

    #[test]
    fn display_path_selects_the_exact_mangled_symbol() {
        let sidecar = rows();
        let text = "fn @guard_scope(functy.0) {\n    ret\n}\n\
                    fn @_R_mangled_guard(functy.0) {\n    drop struct.0, %1\n}\n";
        let body = body_lines(text, function_symbol(&sidecar, "guard_scope"));
        assert!(body.iter().any(|line| line == "drop struct.0, %1"));
        assert!(!body.iter().any(|line| line == "ret"));
    }

    #[test]
    fn duplicate_paths_and_symbols_are_rejected() {
        for key in ["function", "def_path"] {
            let mut sidecar = rows();
            sidecar["functions"][1][key] = sidecar["functions"][0][key].clone();
            assert!(std::panic::catch_unwind(|| function_rows(&sidecar)).is_err());
        }
    }

    #[test]
    fn absent_or_empty_identity_is_rejected() {
        assert!(std::panic::catch_unwind(|| function_symbol(&rows(), "absent").to_owned()).is_err());
        for key in ["function", "def_path"] {
            let mut sidecar = rows();
            sidecar["functions"][0][key] = json!("");
            assert!(std::panic::catch_unwind(|| function_rows(&sidecar)).is_err());
        }
    }

    #[test]
    fn missing_body_is_not_a_successful_negative_mutation() {
        for text in [
            "",
            "; fn @wanted(functy.0) {\n}\n",
            "; rustcc fn @wanted(functy.0) {\n}\n",
            "    rustcc fn @wanted(functy.0) {\n}\n",
            "fn @wanted_suffix(functy.0) {\n}\n",
            "rustcc fn @wanted_suffix(functy.0) {\n}\n",
        ] {
            assert!(std::panic::catch_unwind(|| body_lines(text, "wanted")).is_err());
        }
    }

    #[test]
    fn a_calling_convention_prefix_is_still_the_exact_header() {
        let text = "rustcc fn @wanted(functy.0) {\n    ret\n}\n";
        assert_eq!(body_lines(text, "wanted"), vec!["rustcc fn @wanted(functy.0) {", "ret"]);
        let both = "fn @wanted(functy.0) {\n}\nrustcc fn @wanted(functy.0) {\n}\n";
        assert!(std::panic::catch_unwind(|| body_lines(both, "wanted")).is_err());
    }

    #[test]
    fn duplicate_and_unterminated_bodies_are_rejected() {
        for text in [
            "fn @wanted(functy.0) {\n}\nfn @wanted(functy.0) {\n}\n",
            "fn @wanted(functy.0) {\n    ret\n",
        ] {
            assert!(std::panic::catch_unwind(|| body_lines(text, "wanted")).is_err());
        }
    }
}
