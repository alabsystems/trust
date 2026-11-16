use std::collections::VecDeque;
use std::fmt;
use std::io;
use std::io::Write;

use similar::{Algorithm, ChangeTag};

use crate::config::{Color, Config, Verbosity};

#[derive(Debug, PartialEq)]
pub(crate) enum DiffLine {
    Context(String),
    Expected(String),
    Resulting(String),
}

#[derive(Debug, PartialEq)]
pub(crate) struct Mismatch {
    /// The line number in the formatted version.
    pub(crate) line_number: u32,
    /// The line number in the original version.
    pub(crate) line_number_orig: u32,
    /// The set of lines (context and old/new) in the mismatch.
    pub(crate) lines: Vec<DiffLine>,
}

impl Mismatch {
    fn new(line_number: u32, line_number_orig: u32) -> Mismatch {
        Mismatch {
            line_number,
            line_number_orig,
            lines: Vec::new(),
        }
    }
}

/// A single span of changed lines, with 0 or more removed lines
/// and a vector of 0 or more inserted lines.
#[derive(Debug, PartialEq, Eq)]
pub struct ModifiedChunk {
    /// The first to be removed from the original text
    pub line_number_orig: u32,
    /// The number of lines which have been replaced
    pub lines_removed: u32,
    /// The new lines
    pub lines: Vec<String>,
}

/// Set of changed sections of a file.
#[derive(Debug, PartialEq, Eq)]
pub struct ModifiedLines {
    /// The set of changed chunks.
    pub chunks: Vec<ModifiedChunk>,
}

impl From<Vec<Mismatch>> for ModifiedLines {
    fn from(mismatches: Vec<Mismatch>) -> ModifiedLines {
        let chunks = mismatches.into_iter().map(|mismatch| {
            let lines = mismatch.lines.iter();
            let num_removed = lines
                .filter(|line| matches!(line, DiffLine::Resulting(_)))
                .count();

            let new_lines = mismatch.lines.into_iter().filter_map(|line| match line {
                DiffLine::Context(_) | DiffLine::Resulting(_) => None,
                DiffLine::Expected(str) => Some(str),
            });

            ModifiedChunk {
                line_number_orig: mismatch.line_number_orig,
                lines_removed: num_removed as u32,
                lines: new_lines.collect(),
            }
        });

        ModifiedLines {
            chunks: chunks.collect(),
        }
    }
}

// Converts a `Mismatch` into a serialized form, which just includes
// enough information to modify the original file.
// Each section starts with a line with three integers, space separated:
//     lineno num_removed num_added
// followed by (`num_added`) lines of added text. The line numbers are
// relative to the original file.
impl fmt::Display for ModifiedLines {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in &self.chunks {
            writeln!(
                f,
                "{} {} {}",
                chunk.line_number_orig,
                chunk.lines_removed,
                chunk.lines.len()
            )?;

            for line in &chunk.lines {
                writeln!(f, "{line}")?;
            }
        }

        Ok(())
    }
}

// Allows to convert `Display`ed `ModifiedLines` back to the structural data.
impl std::str::FromStr for ModifiedLines {
    type Err = ();

    fn from_str(s: &str) -> Result<ModifiedLines, ()> {
        let mut chunks = vec![];

        let mut lines = s.lines();
        while let Some(header) = lines.next() {
            let mut header = header.split_whitespace();
            let (orig, rem, new_lines) = match (header.next(), header.next(), header.next()) {
                (Some(orig), Some(removed), Some(added)) => (orig, removed, added),
                _ => return Err(()),
            };
            let (orig, rem, new_lines): (u32, u32, usize) =
                match (orig.parse(), rem.parse(), new_lines.parse()) {
                    (Ok(a), Ok(b), Ok(c)) => (a, b, c),
                    _ => return Err(()),
                };
            let lines = lines.by_ref().take(new_lines);
            let lines: Vec<_> = lines.map(ToOwned::to_owned).collect();
            if lines.len() != new_lines {
                return Err(());
            }

            chunks.push(ModifiedChunk {
                line_number_orig: orig,
                lines_removed: rem,
                lines,
            });
        }

        Ok(ModifiedLines { chunks })
    }
}

// This struct handles writing output to stdout and abstracts away the logic
// of printing in color, if it's possible in the executing environment.
pub(crate) struct OutputWriter {
    terminal: Option<Box<dyn term::Terminal<Output = io::Stdout>>>,
}

impl OutputWriter {
    // Create a new OutputWriter instance based on the caller's preference
    // for colorized output and the capabilities of the terminal.
    pub(crate) fn new(color: Color) -> Self {
        if let Some(t) = term::stdout() {
            if color.use_colored_tty() && t.supports_color() {
                return OutputWriter { terminal: Some(t) };
            }
        }
        OutputWriter { terminal: None }
    }

    // Write output in the optionally specified color. The output is written
    // in the specified color if this OutputWriter instance contains a
    // Terminal in its `terminal` field.
    pub(crate) fn writeln(&mut self, msg: &str, color: Option<term::color::Color>) {
        match &mut self.terminal {
            Some(ref mut t) => {
                if let Some(color) = color {
                    t.fg(color).unwrap();
                }
                writeln!(t, "{msg}").unwrap();
                if color.is_some() {
                    t.reset().unwrap();
                }
            }
            None => println!("{msg}"),
        }
    }
}

/// Largest dense LCS table, in cells, that the legacy `diff::lines` path may
/// build. `diff` 0.1 trims the common prefix and suffix and then allocates a
/// `u32` table of `(n + 1) * (m + 1)` cells over the remaining middle, so two
/// distant edits in a 50k-line file cost gigabytes. 4M cells is 16 MiB.
const LEGACY_DIFF_MAX_CELLS: usize = 1 << 22;

// Produces a diff between the expected output and actual output of rustfmt.
pub(crate) fn make_diff(expected: &str, actual: &str, context_size: usize) -> Vec<Mismatch> {
    make_diff_bounded(expected, actual, context_size, LEGACY_DIFF_MAX_CELLS)
}

/// Uses the legacy dense-LCS diff when its table fits in `max_legacy_cells`, so
/// every hunk rustfmt reported before is reported byte-identically (ambiguous
/// alignments included, which `modified` and `json` output expose). Above the
/// bound it switches to linear-space Myers, which is also minimal but may
/// align an ambiguous edit differently.
fn make_diff_bounded(
    expected: &str,
    actual: &str,
    context_size: usize,
    max_legacy_cells: usize,
) -> Vec<Mismatch> {
    let expected_lines: Vec<_> = expected.lines().collect();
    let actual_lines: Vec<_> = actual.lines().collect();
    if legacy_table_cells(&expected_lines, &actual_lines) <= max_legacy_cells {
        let changes = diff::lines(expected, actual)
            .into_iter()
            .map(|change| match change {
                diff::Result::Left(line) => (ChangeTag::Delete, line),
                diff::Result::Right(line) => (ChangeTag::Insert, line),
                diff::Result::Both(line, _) => (ChangeTag::Equal, line),
            });
        return make_diff_from_changes(changes, context_size);
    }

    // Dense LCS tables require quadratic space even when only two distant lines
    // differ. Myers keeps linear-size frontiers and captures a minimal edit script.
    let ops = similar::capture_diff_slices(Algorithm::Myers, &expected_lines, &actual_lines);
    let changes = ops
        .iter()
        .flat_map(|op| op.iter_changes(&expected_lines, &actual_lines))
        .map(|change| (change.tag(), change.value()));

    // Preserve diff::lines' convention: str::lines normalizes CRLF and omits the
    // final empty item. Append that item after diffing, so it cannot move a hunk.
    let trailing_newline = match (expected.ends_with('\n'), actual.ends_with('\n')) {
        (true, true) => Some((ChangeTag::Equal, "")),
        (true, false) => Some((ChangeTag::Delete, "")),
        (false, true) => Some((ChangeTag::Insert, "")),
        (false, false) => None,
    };
    make_diff_from_changes(changes.chain(trailing_newline), context_size)
}

/// The number of cells `diff` 0.1 would allocate for these lines: it trims the
/// common prefix and suffix exactly like this before building its table.
fn legacy_table_cells(left: &[&str], right: &[&str]) -> usize {
    let leading = left.iter().zip(right).take_while(|(l, r)| l == r).count();
    let trailing = left[leading..]
        .iter()
        .rev()
        .zip(right[leading..].iter().rev())
        .take_while(|(l, r)| l == r)
        .count();
    let rows = left.len() - leading - trailing + 1;
    let cols = right.len() - leading - trailing + 1;
    rows.saturating_mul(cols)
}

fn make_diff_from_changes<'a>(
    changes: impl Iterator<Item = (ChangeTag, &'a str)>,
    context_size: usize,
) -> Vec<Mismatch> {
    let mut line_number = 1;
    let mut line_number_orig = 1;
    let mut context_queue: VecDeque<&str> = VecDeque::with_capacity(context_size);
    let mut lines_since_mismatch = context_size + 1;
    let mut results = Vec::new();
    let mut mismatch = Mismatch::new(0, 0);

    for result in changes {
        match result {
            (ChangeTag::Delete, str) => {
                if lines_since_mismatch >= context_size && lines_since_mismatch > 0 {
                    results.push(mismatch);
                    mismatch = Mismatch::new(
                        line_number - context_queue.len() as u32,
                        line_number_orig - context_queue.len() as u32,
                    );
                }

                while let Some(line) = context_queue.pop_front() {
                    mismatch.lines.push(DiffLine::Context(line.to_owned()));
                }

                mismatch.lines.push(DiffLine::Resulting(str.to_owned()));
                line_number_orig += 1;
                lines_since_mismatch = 0;
            }
            (ChangeTag::Insert, str) => {
                if lines_since_mismatch >= context_size && lines_since_mismatch > 0 {
                    results.push(mismatch);
                    mismatch = Mismatch::new(
                        line_number - context_queue.len() as u32,
                        line_number_orig - context_queue.len() as u32,
                    );
                }

                while let Some(line) = context_queue.pop_front() {
                    mismatch.lines.push(DiffLine::Context(line.to_owned()));
                }

                mismatch.lines.push(DiffLine::Expected(str.to_owned()));
                line_number += 1;
                lines_since_mismatch = 0;
            }
            (ChangeTag::Equal, str) => {
                if context_queue.len() >= context_size {
                    let _ = context_queue.pop_front();
                }

                if lines_since_mismatch < context_size {
                    mismatch.lines.push(DiffLine::Context(str.to_owned()));
                } else if context_size > 0 {
                    context_queue.push_back(str);
                }

                line_number += 1;
                line_number_orig += 1;
                lines_since_mismatch += 1;
            }
        }
    }

    results.push(mismatch);
    results.remove(0);

    results
}

pub(crate) fn print_diff<F>(diff: Vec<Mismatch>, get_section_title: F, config: &Config)
where
    F: Fn(u32) -> String,
{
    let color = config.color();
    let line_terminator = if config.verbose() == Verbosity::Verbose {
        "⏎"
    } else {
        ""
    };

    let mut writer = OutputWriter::new(color);

    for mismatch in diff {
        let title = get_section_title(mismatch.line_number_orig);
        writer.writeln(&title, None);

        for line in mismatch.lines {
            match line {
                DiffLine::Context(ref str) => {
                    writer.writeln(&format!(" {str}{line_terminator}"), None)
                }
                DiffLine::Expected(ref str) => writer.writeln(
                    &format!("+{str}{line_terminator}"),
                    Some(term::color::GREEN),
                ),
                DiffLine::Resulting(ref str) => {
                    writer.writeln(&format!("-{str}{line_terminator}"), Some(term::color::RED))
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::DiffLine::*;
    use super::{
        ChangeTag, LEGACY_DIFF_MAX_CELLS, Mismatch, legacy_table_cells, make_diff,
        make_diff_bounded, make_diff_from_changes,
    };
    use super::{ModifiedChunk, ModifiedLines};

    #[test]
    fn diff_simple() {
        let src = "one\ntwo\nthree\nfour\nfive\n";
        let dest = "one\ntwo\ntrois\nfour\nfive\n";
        let diff = make_diff(src, dest, 1);
        assert_eq!(
            diff,
            vec![Mismatch {
                line_number: 2,
                line_number_orig: 2,
                lines: vec![
                    Context("two".to_owned()),
                    Resulting("three".to_owned()),
                    Expected("trois".to_owned()),
                    Context("four".to_owned()),
                ],
            }]
        );
    }

    #[test]
    fn diff_simple2() {
        let src = "one\ntwo\nthree\nfour\nfive\nsix\nseven\n";
        let dest = "one\ntwo\ntrois\nfour\ncinq\nsix\nseven\n";
        let diff = make_diff(src, dest, 1);
        assert_eq!(
            diff,
            vec![
                Mismatch {
                    line_number: 2,
                    line_number_orig: 2,
                    lines: vec![
                        Context("two".to_owned()),
                        Resulting("three".to_owned()),
                        Expected("trois".to_owned()),
                        Context("four".to_owned()),
                    ],
                },
                Mismatch {
                    line_number: 5,
                    line_number_orig: 5,
                    lines: vec![
                        Resulting("five".to_owned()),
                        Expected("cinq".to_owned()),
                        Context("six".to_owned()),
                    ],
                },
            ]
        );
    }

    #[test]
    fn diff_zerocontext() {
        let src = "one\ntwo\nthree\nfour\nfive\n";
        let dest = "one\ntwo\ntrois\nfour\nfive\n";
        let diff = make_diff(src, dest, 0);
        assert_eq!(
            diff,
            vec![Mismatch {
                line_number: 3,
                line_number_orig: 3,
                lines: vec![Resulting("three".to_owned()), Expected("trois".to_owned())],
            }]
        );
    }

    #[test]
    fn diff_trailing_newline() {
        let src = "one\ntwo\nthree\nfour\nfive";
        let dest = "one\ntwo\nthree\nfour\nfive\n";
        let diff = make_diff(src, dest, 1);
        assert_eq!(
            diff,
            vec![Mismatch {
                line_number: 5,
                line_number_orig: 5,
                lines: vec![Context("five".to_owned()), Expected("".to_owned())],
            }]
        );
    }

    // The Myers fallback, forced regardless of input size (every table has at
    // least one cell). The tests below pin it against the legacy algorithm.
    fn myers_diff(old: &str, new: &str, context: usize) -> Vec<Mismatch> {
        make_diff_bounded(old, new, context, 0)
    }

    // Only tiny cases use the old quadratic implementation. Both algorithms feed
    // the same unchanged hunk builder, so equality checks include its coordinates,
    // context and ordering instead of comparing only a changed/not-changed flag.
    fn legacy_diff(old: &str, new: &str, context: usize) -> Vec<Mismatch> {
        assert!(old.lines().count() <= 32 && new.lines().count() <= 32);
        let changes = diff::lines(old, new)
            .into_iter()
            .map(|change| match change {
                diff::Result::Left(line) => (ChangeTag::Delete, line),
                diff::Result::Right(line) => (ChangeTag::Insert, line),
                diff::Result::Both(line, _) => (ChangeTag::Equal, line),
            });
        make_diff_from_changes(changes, context)
    }

    // Check the public modified-lines representation against the entire input.
    // Keep the old final-newline token convention independently of the matcher.
    fn assert_reconstructs(old: &str, new: &str) {
        let tokens = |text: &str| {
            let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
            if text.ends_with('\n') {
                lines.push(String::new());
            }
            lines
        };
        for diff in [make_diff(old, new, 0), myers_diff(old, new, 0)] {
            let mut reconstructed = tokens(old);
            let modified = ModifiedLines::from(diff);
            for chunk in modified.chunks.iter().rev() {
                let start = (chunk.line_number_orig - 1) as usize;
                let end = start + chunk.lines_removed as usize;
                reconstructed.splice(start..end, chunk.lines.iter().cloned());
            }
            assert_eq!(reconstructed, tokens(new), "old={old:?}, new={new:?}");
        }
    }

    #[test]
    fn diff_matches_legacy_unambiguous_cases() {
        for (old, new) in [
            ("", ""),
            ("", "one"),
            ("one", ""),
            ("", "\n"),
            ("\n", ""),
            ("one", "one\n"),
            ("one\n", "one"),
            ("one\n", "one\n"),
            ("one\ntwo", "zero\none\ntwo"),
            ("one\ntwo", "one\ntwo\nthree"),
            ("zero\none\ntwo", "one\ntwo"),
            ("one\ntwo\nthree", "one\ntwo"),
            ("old\nbody\nend", "new\nbody\nend"),
            ("start\nbody\nold", "start\nbody\nnew"),
            ("one\r\ntwo\r\n", "one\ntwo\n"),
            ("α\nβ\n終\n", "α\nγ\n終\n"),
        ] {
            for context in [0, 1, 3] {
                assert_eq!(
                    myers_diff(old, new, context),
                    legacy_diff(old, new, context)
                );
            }
            assert_reconstructs(old, new);
        }
    }

    #[test]
    fn diff_final_newline_removal_and_crlf() {
        assert_eq!(
            myers_diff("one\n", "one", 0),
            vec![Mismatch {
                line_number: 2,
                line_number_orig: 2,
                lines: vec![Resulting(String::new())],
            }]
        );
        assert!(myers_diff("one\r\ntwo\r\n", "one\ntwo\n", 0).is_empty());
        assert_reconstructs("one\r\ntwo\r\n", "one\ntwo");
    }

    #[test]
    fn diff_repeated_lines_keep_order_and_coordinates() {
        let old = "start\n{\n\n}\n{\n\n}\nend\n";
        let new = "start\n{\nchanged\n}\n{\n\n}\nend\n";
        assert_eq!(
            myers_diff(old, new, 1),
            vec![Mismatch {
                line_number: 2,
                line_number_orig: 2,
                lines: vec![
                    Context("{".to_owned()),
                    Resulting(String::new()),
                    Expected("changed".to_owned()),
                    Context("}".to_owned()),
                ],
            }]
        );
        assert_eq!(
            myers_diff("x\nx\nx\n", "x\nx\n", 0),
            vec![Mismatch {
                line_number: 3,
                line_number_orig: 3,
                lines: vec![Resulting("x".to_owned())],
            }]
        );
        assert_reconstructs(old, new);
    }

    #[test]
    fn diff_small_repeated_inputs_are_minimal_and_reconstruct() {
        let mut inputs = vec![String::new()];
        for len in 1..=3 {
            for mask in 0..(1 << len) {
                inputs.push(
                    (0..len)
                        .map(|i| if mask & (1 << i) == 0 { "a" } else { "b" })
                        .collect::<Vec<_>>()
                        .join("\n"),
                );
            }
        }
        let base_inputs = inputs.clone();
        inputs.extend(base_inputs.into_iter().map(|text| format!("{text}\n")));
        for old in &inputs {
            for new in &inputs {
                let diff = myers_diff(old, new, 0);
                let edit_count = diff
                    .iter()
                    .flat_map(|hunk| &hunk.lines)
                    .filter(|line| !matches!(line, Context(_)))
                    .count();
                let minimum = diff::lines(old, new)
                    .iter()
                    .filter(|line| !matches!(line, diff::Result::Both(_, _)))
                    .count();
                assert_eq!(edit_count, minimum, "old={old:?}, new={new:?}");
                assert_reconstructs(old, new);
                assert_eq!(diff, myers_diff(old, new, 0));
            }
        }
    }

    #[test]
    fn diff_nearby_edits_keep_existing_context_merging() {
        let old = "zero\none\ntwo\nthree\nfour\nfive\n";
        let new = "zero\nONE\ntwo\nTHREE\nfour\nfive\n";
        assert_eq!(myers_diff(old, new, 2), legacy_diff(old, new, 2));
        assert_eq!(myers_diff(old, new, 2).len(), 1);
        assert_reconstructs(old, new);
    }

    #[test]
    fn diff_all_distinct_lines_roundtrip() {
        let old = (0..128).map(|i| format!("old-{i}\n")).collect::<String>();
        let new = (0..128).map(|i| format!("new-{i}\n")).collect::<String>();
        let diff = myers_diff(&old, &new, 0);
        assert_eq!(diff.len(), 1);
        assert_eq!(diff[0].line_number_orig, 1);
        assert_eq!(diff[0].line_number, 1);
        assert_eq!(diff[0].lines.len(), 256);
        assert!(
            diff[0].lines[..128]
                .iter()
                .all(|line| matches!(line, Resulting(_)))
        );
        assert!(
            diff[0].lines[128..]
                .iter()
                .all(|line| matches!(line, Expected(_)))
        );
        assert_reconstructs(&old, &new);
    }

    #[test]
    fn diff_large_separated_edits_use_two_exact_hunks() {
        // Two distant edits defeat prefix/suffix trimming in dense LCS. At
        // 60,000 lines its u32 table would exceed 13 GiB. Never run that oracle
        // here: the large regression exercises only the production algorithm.
        let old_lines: Vec<_> = (0..60_000).map(|i| format!("line-{i:05}")).collect();
        let mut new_lines = old_lines.clone();
        new_lines[1] = "changed-near-start".to_owned();
        new_lines[59_998] = "changed-near-end".to_owned();
        let old = old_lines.join("\n") + "\n";
        let new = new_lines.join("\n") + "\n";
        assert_eq!(
            make_diff(&old, &new, 1),
            vec![
                Mismatch {
                    line_number: 1,
                    line_number_orig: 1,
                    lines: vec![
                        Context("line-00000".to_owned()),
                        Resulting("line-00001".to_owned()),
                        Expected("changed-near-start".to_owned()),
                        Context("line-00002".to_owned()),
                    ],
                },
                Mismatch {
                    line_number: 59_998,
                    line_number_orig: 59_998,
                    lines: vec![
                        Context("line-59997".to_owned()),
                        Resulting("line-59998".to_owned()),
                        Expected("changed-near-end".to_owned()),
                        Context("line-59999".to_owned()),
                    ],
                },
            ]
        );
        assert_reconstructs(&old, &new);
    }

    #[test]
    fn small_inputs_keep_the_legacy_alignment() {
        // An ambiguous edit where the two minimal scripts differ: blank lines
        // can pair with either neighbour. `make_diff` must report the legacy
        // alignment (what `modified`/`json` output has always shown).
        let old = "a\n\nfn\nblah\n()\n{ }\n\n\n#[cfg\n(  a , b\n)]\nfn\nmain() {}\n";
        let new = "a\n\nfn blah() {}\n\n#[cfg(a, b)]\nfn main() {}\n";
        for context in [0, 1, 3] {
            assert_eq!(make_diff(old, new, context), legacy_diff(old, new, context));
        }
        // Guard the guard: the fixture must stay one where Myers aligns differently.
        assert_ne!(myers_diff(old, new, 0), legacy_diff(old, new, 0));
        assert_reconstructs(old, new);
    }

    #[test]
    fn legacy_table_cells_counts_the_trimmed_middle() {
        assert_eq!(legacy_table_cells(&[], &[]), 1);
        assert_eq!(legacy_table_cells(&["a", "b", "c"], &["a", "b", "c"]), 1);
        assert_eq!(
            legacy_table_cells(&["a", "x", "c"], &["a", "y", "z", "c"]),
            2 * 3
        );
        let old: Vec<String> = (0..60_000).map(|i| format!("{i}")).collect();
        let mut new = old.clone();
        new[1] = "start".to_owned();
        new[59_998] = "end".to_owned();
        let old: Vec<&str> = old.iter().map(String::as_str).collect();
        let new: Vec<&str> = new.iter().map(String::as_str).collect();
        assert_eq!(legacy_table_cells(&old, &new), 59_999 * 59_999);
        assert!(legacy_table_cells(&old, &new) > LEGACY_DIFF_MAX_CELLS);
    }

    #[test]
    fn modified_lines_from_str() {
        use std::str::FromStr;

        let src = "1 6 2\nfn some() {}\nfn main() {}\n25 3 1\n  struct Test {}";
        let lines = ModifiedLines::from_str(src).unwrap();
        assert_eq!(
            lines,
            ModifiedLines {
                chunks: vec![
                    ModifiedChunk {
                        line_number_orig: 1,
                        lines_removed: 6,
                        lines: vec!["fn some() {}".to_owned(), "fn main() {}".to_owned(),]
                    },
                    ModifiedChunk {
                        line_number_orig: 25,
                        lines_removed: 3,
                        lines: vec!["  struct Test {}".to_owned()]
                    }
                ]
            }
        );

        let src = "1 5 3";
        assert_eq!(ModifiedLines::from_str(src), Err(()));

        let src = "1 5 3\na\nb";
        assert_eq!(ModifiedLines::from_str(src), Err(()));
    }
}
