use cargo_metadata::camino::{Utf8Path, Utf8PathBuf};
use cargo_metadata::{Metadata, TargetKind};
use clippy_utils::diagnostics::span_lint_and_then;
use rustc_data_structures::fx::FxHashSet;
use rustc_lint::LateContext;
use rustc_span::DUMMY_SP;

use super::TRUST_HAND_ENCODED_SOLVER_QUERY;
use super::external_dependency_source::local_package;

/// A package tree is walked, not indexed, so the walk is bounded on both axes.
/// `proofs/ay/<bundle>/` is three levels below a crate root; a package that
/// buries a solver query deeper than this is not the shape being reported.
const MAX_DEPTH: usize = 6;
/// Enough to cover every directory of a normal crate and stop dead on a
/// checked-in corpus or a stray build output someone kept in-tree.
const MAX_DIRS: usize = 512;
/// A hand-written obligation is a few kilobytes. The largest file read here is
/// a bit-blasted query, which is still far below this.
const MAX_FILE_BYTES: u64 = 1 << 20;

pub(super) fn check(cx: &LateContext<'_>, metadata: &Metadata) {
    let Some(local) = local_package(cx, metadata) else {
        return;
    };
    let Some(package_dir) = local.manifest_path.parent() else {
        return;
    };

    let mut scan = Scan::default();
    scan.walk(package_dir, 0);
    if scan.bundles.is_empty() {
        return;
    }

    // A tool this build already produces is a tool the build can run: the
    // package is then working on the solver rather than reaching past it. Only
    // a tool nothing here builds puts the discharge outside the build.
    let reached = scan.tools_the_bundles_reach_for(package_dir);
    let provided = executables_this_build_provides(metadata);
    if reached.is_empty() || reached.iter().any(|tool| provided.contains(tool)) {
        return;
    }
    // A set has no order, and the same tree has to yield the same message text
    // on every run for the report to be reviewable.
    let mut outside: Vec<&str> = reached.iter().map(String::as_str).collect();
    outside.sort_unstable();

    // A directory walk carries no documented order, and a per-bundle report is
    // only reviewable if the same tree yields the same list on every run.
    scan.bundles.sort_unstable();

    for bundle in &scan.bundles {
        let dir = relative(package_dir, &bundle.dir);
        let first = relative(package_dir, &bundle.queries[0]);
        let runner = relative(package_dir, &bundle.runner);
        let others = bundle.queries.len() - 1;
        span_lint_and_then(
            cx,
            TRUST_HAND_ENCODED_SOLVER_QUERY,
            DUMMY_SP,
            format!("`{dir}` holds a hand-encoded solver query that nothing in this build reads"),
            |diag| {
                if others == 0 {
                    diag.note(format!(
                        "`{first}` is a self-contained query: an `(assert ...)` and a `(check-sat)`"
                    ));
                } else {
                    diag.note(format!(
                        "`{first}` is a self-contained query: an `(assert ...)` and a `(check-sat)`, and {others} more like it sit here"
                    ));
                }
                diag.note(format!(
                    "`{runner}` discharges them by running `{}`, which nothing in this build produces — so no `cargo build`, no `cargo test` and no `trustc` run reads either the query or its verdict",
                    outside.join("`, `"),
                ));
                diag.help(
                    "state the property on the item instead — a `#[trust::requires]`/`#[trust::ensures]` clause, an invariant, or a `clean { .. }` island — so trust-vc and trust-wp build the query from the MIR that ships and trust-mc discharges it in the build",
                );
                diag.help(
                    "if the stack cannot express the property, that gap is the thing to report against trust-mc, trust-vc or trust-wp; a hand-written query states the property a second time, over a model of the code rather than the code, and the two copies drift apart with nothing watching",
                );
            },
        );
    }
}

/// One directory holding both a hand-written solver query and the script that
/// discharges it.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Bundle {
    dir: Utf8PathBuf,
    queries: Vec<Utf8PathBuf>,
    runner: Utf8PathBuf,
}

/// The executables one shell script reaches for, and where that script lives.
struct ScriptTools {
    dir: Utf8PathBuf,
    tools: Vec<String>,
}

#[derive(Default)]
struct Scan {
    bundles: Vec<Bundle>,
    scripts: Vec<ScriptTools>,
    dirs: usize,
}

impl Scan {
    /// Every executable the scripts belonging to a proof bundle resolve from
    /// the machine.
    ///
    /// A bundle's own runner routinely sources the resolution from a shared
    /// script one directory up, so the directory holding the query need not
    /// name the tool at all; a script on the path from a bundle upwards is
    /// therefore counted too. The package root is excluded unless a bundle sits
    /// directly in it, because that is where a crate's ordinary scripts live —
    /// a release step reaching for `jq` is not part of anyone's proof.
    fn tools_the_bundles_reach_for(&self, package_dir: &Utf8Path) -> FxHashSet<String> {
        let mut tools = FxHashSet::default();
        for script in &self.scripts {
            let belongs = self.bundles.iter().any(|bundle| {
                bundle.dir == script.dir || (script.dir != package_dir && bundle.dir.starts_with(&script.dir))
            });
            if belongs {
                tools.extend(script.tools.iter().cloned());
            }
        }
        tools
    }
}

impl Scan {
    fn walk(&mut self, dir: &Utf8Path, depth: usize) {
        if depth > MAX_DEPTH || self.dirs >= MAX_DIRS {
            return;
        }
        self.dirs += 1;

        let Ok(entries) = dir.read_dir_utf8() else {
            return;
        };
        let mut subdirs = Vec::new();
        let mut queries = Vec::new();
        let mut runners = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path().to_owned();
            let name = entry.file_name();
            // A dot directory is tooling state, `target` is build output, and
            // neither is something an author wrote a proof obligation into.
            if name.starts_with('.') || name == "target" || name == "node_modules" {
                continue;
            }
            let Ok(file_type) = entry.file_type() else {
                continue;
            };
            if file_type.is_dir() {
                subdirs.push(path);
                continue;
            }
            if !file_type.is_file() {
                continue;
            }
            match path.extension() {
                Some("smt2") => {
                    if let Some(text) = read_small(&path)
                        && is_self_contained_query(&text)
                    {
                        queries.push(path);
                    }
                },
                Some("sh") => {
                    if let Some(text) = read_small(&path) {
                        let tools = tools_resolved_from_the_machine(&text);
                        if !tools.is_empty() {
                            self.scripts.push(ScriptTools {
                                dir: dir.to_owned(),
                                tools,
                            });
                        }
                        if discharges_smt_queries(&text) {
                            runners.push(path);
                        }
                    }
                },
                _ => {},
            }
        }

        if !queries.is_empty()
            && let Some(runner) = runners.into_iter().min()
        {
            queries.sort_unstable();
            self.bundles.push(Bundle {
                dir: dir.to_owned(),
                queries,
                runner,
            });
        }

        subdirs.sort_unstable();
        for subdir in subdirs {
            self.walk(&subdir, depth + 1);
        }
    }
}

fn read_small(path: &Utf8Path) -> Option<String> {
    if path.metadata().ok()?.len() > MAX_FILE_BYTES {
        return None;
    }
    std::fs::read_to_string(path).ok()
}

fn relative(package_dir: &Utf8Path, path: &Utf8Path) -> Utf8PathBuf {
    path.strip_prefix(package_dir).unwrap_or(path).to_owned()
}

/// Every executable name this build produces, whether as a package or as a
/// binary target of one.
///
/// The graph is read whole, not just the workspace: a solver reached through a
/// path dependency, a `[patch]`, or a vendored copy is still a solver this
/// build compiles, and a package that compiles the solver is a package whose
/// SMT files are the tool's own material.
fn executables_this_build_provides(metadata: &Metadata) -> FxHashSet<String> {
    let mut provided = FxHashSet::default();
    for package in &metadata.packages {
        provided.insert(package.name.to_string());
        for target in &package.targets {
            if target.kind.iter().any(|kind| *kind == TargetKind::Bin) {
                provided.insert(target.name.clone());
            }
        }
    }
    provided
}

/// Whether an `.smt2` file is a solver query in its own right rather than a
/// fragment.
///
/// A query asserts something and asks for a verdict; a fragment — a shared
/// prelude, a sort declaration, a datatype definition included by others — does
/// one or neither. Only a file that does both stands alone as evidence, and
/// only a file that stands alone can be presented as one.
///
/// Comments are stripped first, so a `.smt2` that merely *discusses* a
/// `(check-sat)` in its header is not mistaken for one that runs it.
fn is_self_contained_query(text: &str) -> bool {
    let code = strip_comments(text);
    code.contains("(check-sat") && code.contains("(assert")
}

/// SMT-LIB comments run from an unquoted `;` to the end of the line.
fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        out.push_str(&line[..code_len(line)]);
        out.push('\n');
    }
    out
}

/// How much of a line is code, i.e. the offset of the `;` that opens a comment,
/// or the whole line when there is none.
fn code_len(line: &str) -> usize {
    let mut in_string = false;
    for (index, ch) in line.char_indices() {
        match ch {
            '"' => in_string = !in_string,
            ';' if !in_string => return index,
            _ => {},
        }
    }
    line.len()
}

/// Whether a shell script is the thing that discharges the queries beside it.
///
/// Naming the file extension is what separates a runner from the other scripts
/// a crate keeps — an installer, a release step, a benchmark driver. It is a
/// deliberately weak test: the conjunction that matters is a runner *and* a
/// query in the same directory, and neither half alone is reported.
fn discharges_smt_queries(script: &str) -> bool {
    script.contains("smt2")
}

/// Executable names a script resolves from the machine it runs on rather than
/// from the build.
///
/// Two spellings cover it, and both appear in the pattern this lint reports: a
/// `PATH` lookup (`command -v ay`, `which z3`) and a hardcoded install
/// directory (`$HOME/.cargo/bin/ay`, `/usr/local/bin/z3`). Anything reached
/// either way is a tool the author expects to already be on the machine —
/// which is exactly why nothing in the build can be made to run it.
fn tools_resolved_from_the_machine(script: &str) -> Vec<String> {
    // Comments go first, and that is also what keeps the interpreter out: a
    // `#!/usr/bin/env bash` line names what runs the script, not a tool the
    // script reaches for, and it carries a `/bin/` that would otherwise be read
    // as one.
    let code = strip_shell_comments(script);
    let mut tools: Vec<String> = Vec::new();

    for lookup in ["command -v", "type -p", "which"] {
        let mut consumed = 0;
        while let Some(at) = code[consumed..].find(lookup) {
            let start = consumed + at;
            consumed = start + lookup.len();
            if !is_word_boundary(&code, start, consumed) {
                continue;
            }
            if let Some(name) = executable_after_separator(&code[consumed..]) {
                tools.push(name.to_owned());
            }
        }
    }

    let mut consumed = 0;
    while let Some(at) = code[consumed..].find("/bin/") {
        consumed += at + "/bin/".len();
        if let Some(name) = leading_executable_name(&code[consumed..]) {
            tools.push(name.to_owned());
        }
    }

    tools.sort_unstable();
    tools.dedup();
    tools
}

/// Whether a match sits on its own rather than inside a longer word, so that
/// `which` is a lookup and `whichever` is not.
fn is_word_boundary(text: &str, start: usize, end: usize) -> bool {
    let before = text[..start].chars().next_back();
    let after = text[end..].chars().next();
    let bare = |ch: Option<char>| ch.is_none_or(|ch| !ch.is_ascii_alphanumeric() && ch != '_');
    bare(before) && bare(after)
}

/// The executable named as the argument of a lookup, skipping whatever quoting
/// and substitution sits between.
fn executable_after_separator(text: &str) -> Option<&str> {
    let rest = text.trim_start_matches([' ', '\t', '$', '(', '"', '\'', '`', '{']);
    // The separator has to be there: `command -verbose` is not a lookup of
    // anything, and reading `erbose` out of it would name a tool nobody wrote.
    if rest.len() == text.len() {
        return None;
    }
    leading_executable_name(rest)
}

/// Shell comments run from an unquoted `#` at the start of a word to the end of
/// the line, which also covers the shebang.
fn strip_shell_comments(script: &str) -> String {
    let mut out = String::with_capacity(script.len());
    for line in script.lines() {
        let mut quote: Option<char> = None;
        let mut cut = line.len();
        let mut previous: Option<char> = None;
        for (index, ch) in line.char_indices() {
            match ch {
                '\'' | '"' if quote == Some(ch) => quote = None,
                '\'' | '"' if quote.is_none() => quote = Some(ch),
                '#' if quote.is_none() && previous.is_none_or(char::is_whitespace) => {
                    cut = index;
                    break;
                },
                _ => {},
            }
            previous = Some(ch);
        }
        out.push_str(&line[..cut]);
        out.push('\n');
    }
    out
}

/// The executable name at the start of `text`, if it is a plain name.
///
/// A name built out of a shell variable is deliberately rejected: this pass
/// cannot say what it expands to, and reporting a guess would name a tool the
/// author never wrote.
fn leading_executable_name(text: &str) -> Option<&str> {
    let end = text
        .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' || ch == '+'))
        .unwrap_or(text.len());
    let name = &text[..end];
    let first = name.chars().next()?;
    (first.is_ascii_alphabetic() || first == '_').then_some(name)
}

#[cfg(test)]
mod tests_for_is_self_contained_query {
    use super::is_self_contained_query;

    /// Verbatim from `orca-renderer-heap/proofs/ay/rh1_band_bound.smt2`, the
    /// shape this lint exists to report.
    const HAND_ENCODED_OBLIGATION: &str = "\
; THEOREM (renderer-heap): the RAM-tier ceiling is always within [FLOOR, CAP].
; Negation asserted; UNSAT == proved for ALL t >= 0.
(set-logic QF_LIA)
(declare-const t Int)
(assert (>= t 0))
(check-sat)
; EXPECT: unsat
";

    #[test]
    fn an_assert_and_a_check_sat_stand_alone() {
        assert!(is_self_contained_query(HAND_ENCODED_OBLIGATION));
    }

    #[test]
    fn a_declaration_only_prelude_does_not() {
        assert!(!is_self_contained_query(
            "(set-logic QF_BV)\n(declare-fun w () (_ BitVec 32))\n"
        ));
    }

    #[test]
    fn an_assertion_with_no_verdict_asked_for_does_not() {
        assert!(!is_self_contained_query("(set-logic QF_LIA)\n(assert (> x 0))\n"));
    }

    #[test]
    fn a_header_that_only_discusses_a_check_sat_does_not() {
        // The comment names both forms; stripping comments is what keeps a
        // README-ish prelude out of the report.
        assert!(!is_self_contained_query(
            "; every bundle here is (assert ...) plus (check-sat)\n(declare-const t Int)\n"
        ));
    }

    #[test]
    fn a_semicolon_inside_a_string_literal_does_not_hide_the_rest_of_the_line() {
        assert!(is_self_contained_query("(assert (= s \"a;b\")) (check-sat)\n"));
    }
}

#[cfg(test)]
mod tests_for_tools_resolved_from_the_machine {
    use super::tools_resolved_from_the_machine;

    /// The tools a script reaches for, as a borrowed list so a failure prints
    /// the names rather than a `String` soup.
    fn tools(script: &str) -> Vec<String> {
        tools_resolved_from_the_machine(script)
    }

    /// Verbatim from `orca-renderer-heap/proofs/ay/verify.sh`, shebang and
    /// header comment included, because both are what the file really contains.
    const LADDER: &str = r#"#!/usr/bin/env bash
# Re-checkable certificate. Discharged by `ay` on hand-encoded SMT-LIB2.
set -u
AY=""
for c in "$HOME/.cargo/bin/ay" \
         "$HOME/trust/build/host/stage2/bin/ay" \
         "$(command -v ay 2>/dev/null || true)"; do
  if [ -n "$c" ] && [ -x "$c" ]; then AY="$c"; break; fi
done
"#;

    #[test]
    fn a_solver_ladder_names_the_solver_once() {
        assert_eq!(tools(LADDER), ["ay"]);
    }

    #[test]
    fn a_shebang_names_the_interpreter_and_is_not_a_tool_lookup() {
        // Without the comment strip this reports `env`, which is neither a
        // solver nor anything the script reaches for.
        assert!(tools("#!/usr/bin/env bash\n").is_empty());
        assert!(tools("#!/bin/sh\n").is_empty());
    }

    #[test]
    fn a_path_lookup_survives_the_quoting_around_it() {
        // Verbatim from `orca-git/proofs/ay/resolve-solver.sh`: the lookup is
        // nested inside a parameter expansion, so nothing here is a bare word.
        assert_eq!(
            tools(r#"SOLVER_BIN="${Z3:-$(command -v z3 2>/dev/null || true)}""#),
            ["z3"]
        );
        assert_eq!(tools("which drat-trim"), ["drat-trim"]);
        assert_eq!(tools("type -p cvc5"), ["cvc5"]);
    }

    #[test]
    fn an_install_directory_is_a_machine_lookup() {
        assert_eq!(tools("exec /usr/local/bin/z3 -T:120 \"$1\""), ["z3"]);
    }

    #[test]
    fn a_lookup_inside_a_longer_word_is_not_a_lookup() {
        assert!(tools("echo whichever ay you like").is_empty());
    }

    #[test]
    fn a_name_that_is_only_a_variable_expansion_is_not_reported() {
        // `"$HOME/bin/$SOLVER"` names no tool this pass can identify, and a
        // guess here would put a tool in the message the author never wrote.
        assert!(tools("\"$HOME/bin/$SOLVER\" \"$f\"").is_empty());
    }

    #[test]
    fn a_script_that_reaches_no_tool_reports_none() {
        assert!(tools("cargo test -p orca-flow-control").is_empty());
    }

    #[test]
    fn every_distinct_tool_is_reported_and_the_order_is_stable() {
        assert_eq!(tools("command -v ay; command -v z3; /opt/bin/ay"), ["ay", "z3"]);
    }
}
