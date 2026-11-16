//! Every trust-ir fixture in `tests/ir/` names the trustc that printed it
//! (platform-pass plan L0), so every census assertion is an assertion about
//! a NAMED producer, and a dump nobody can regenerate is refused here rather
//! than trusted.
//!
//! The header is one plain comment after the text-format line:
//!
//! ```text
//! ; TrustIr text format v1
//! ; trustc <40-hex commit hash> <YYYY-MM-DD commit date>
//! ```
//!
//! (`trustc -vV`'s `commit-hash` and `commit-date`). A dump that was edited
//! by hand keeps the header of the dump it edits and is labeled
//! `; HAND EDIT`; a module written by hand is labeled `; SYNTHETIC` and
//! claims no trustc. `scripts/trust_platform/regen_census_fixtures.sh`
//! writes the header, and its `REGEN_NAMES` dumps share one trustc: a
//! re-pin is all of them or none. A dump an older producer printed and a
//! test still needs (its shape is gone from today's output) is held in a
//! subdirectory named by that trustc (`771983b92/`), which its header must
//! match.

use std::collections::BTreeMap;
use std::path::PathBuf;

const TEXT_HEADER: &str = "; TrustIr text format v1";

/// Fixture sources with a dump beside them that the script does NOT
/// regenerate, each with why. Every other `<name>.rs` with a
/// `<name>.trust_ir` must be in the script's `REGEN_NAMES`.
const HELD: &[(&str, &str)] =
    &[("adv7", "adv7m.trust_ir is a labeled hand edit of adv7's dump; the pair stays together")];

#[derive(Clone, Debug, PartialEq, Eq)]
enum Provenance {
    /// Printed by this trustc (then edited by hand when `hand_edit`).
    Trustc { sha: String, date: String, hand_edit: bool },
    /// Written by hand; no trustc printed it.
    Synthetic,
}

/// What the leading `;` comment block of a fixture says about where it came
/// from, or why it says nothing usable.
fn provenance(text: &str) -> Result<Provenance, String> {
    let mut lines = text.lines();
    match lines.next() {
        Some(TEXT_HEADER) => {}
        other => return Err(format!("the first line is {other:?}, not `{TEXT_HEADER}`")),
    }
    let header: Vec<&str> = lines.take_while(|l| l.starts_with(';')).collect();
    let trustc: Vec<&str> = header.iter().copied().filter(|l| l.starts_with("; trustc")).collect();
    let synthetic = header.iter().any(|l| l.starts_with("; SYNTHETIC"));
    let hand_edit = header.iter().any(|l| l.starts_with("; HAND EDIT"));
    if synthetic {
        if hand_edit || !trustc.is_empty() {
            return Err("a `; SYNTHETIC` module claims a trustc or a hand edit".into());
        }
        return Ok(Provenance::Synthetic);
    }
    let [line] = trustc.as_slice() else {
        return Err(format!(
            "{} `; trustc` header lines (exactly one is required; regenerate with \
             scripts/trust_platform/regen_census_fixtures.sh --trustc <stage1>)",
            trustc.len()
        ));
    };
    let words: Vec<&str> = line.strip_prefix("; trustc ").unwrap_or_default().split(' ').collect();
    let [sha, date] = words.as_slice() else {
        return Err(format!("`{line}` is not `; trustc <commit-hash> <commit-date>`"));
    };
    let hex =
        sha.len() == 40 && sha.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b));
    if !hex {
        return Err(format!("`{sha}` is not a full 40-hex commit hash"));
    }
    let d = date.as_bytes();
    let is_date = d.len() == 10
        && d[4] == b'-'
        && d[7] == b'-'
        && d.iter().enumerate().all(|(i, b)| i == 4 || i == 7 || b.is_ascii_digit());
    if !is_date {
        return Err(format!("`{date}` is not a YYYY-MM-DD commit date"));
    }
    Ok(Provenance::Trustc { sha: (*sha).to_string(), date: (*date).to_string(), hand_edit })
}

fn ir_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/ir")
}

/// Every `*.trust_ir` under `tests/ir/` (subdirectories included, such as
/// the held `771983b92/` dumps), by path from `tests/ir/` without the
/// extension (`adv`, `771983b92/adv`).
fn fixtures() -> BTreeMap<String, String> {
    fn walk(dir: &std::path::Path, out: &mut BTreeMap<String, String>) {
        for e in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
            let p = e.expect("dir entry").path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "trust_ir") {
                let rel = p.strip_prefix(ir_dir()).expect("under tests/ir").with_extension("");
                let text =
                    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
                out.insert(rel.to_string_lossy().into_owned(), text);
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&ir_dir(), &mut out);
    assert!(!out.is_empty(), "no fixture dumps in {}", ir_dir().display());
    out
}

/// The regeneration script's `REGEN_NAMES`.
fn regen_names() -> Vec<String> {
    let script = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/trust_platform/regen_census_fixtures.sh");
    let text =
        std::fs::read_to_string(&script).unwrap_or_else(|e| panic!("{}: {e}", script.display()));
    let lines: Vec<&str> = text.lines().filter(|l| l.starts_with("REGEN_NAMES=\"")).collect();
    let [line] = lines.as_slice() else {
        panic!("{}: expected one `REGEN_NAMES=\"…\"` line, found {}", script.display(), lines.len())
    };
    let names: Vec<String> = line["REGEN_NAMES=\"".len()..]
        .trim_end_matches('"')
        .split_whitespace()
        .map(str::to_string)
        .collect();
    assert!(!names.is_empty(), "REGEN_NAMES is empty");
    names
}

#[test]
fn every_fixture_dump_names_its_trustc() {
    let mut bad = Vec::new();
    for (name, text) in fixtures() {
        match provenance(&text) {
            Ok(p) => {
                println!("{name}.trust_ir: {p:?}");
                // The header is a plain comment: the dump still parses.
                if let Err(e) = trust_ir::parser::parse_module(&text) {
                    bad.push(format!("{name}.trust_ir: does not parse with its header: {e:?}"));
                }
                // A held directory (`771983b92/`) is named by the trustc that
                // printed every dump in it.
                if let Some((dir, _)) = name.rsplit_once('/') {
                    let held_by = |sha: &str| sha.starts_with(dir) && dir.len() >= 7;
                    if !matches!(&p, Provenance::Trustc { sha, .. } if held_by(sha)) {
                        bad.push(format!(
                            "{name}.trust_ir: {p:?} is not the trustc `{dir}/` names"
                        ));
                    }
                }
            }
            Err(e) => bad.push(format!("{name}.trust_ir: {e}")),
        }
    }
    assert!(bad.is_empty(), "fixtures without a usable provenance header:\n{}", bad.join("\n"));
}

#[test]
fn the_regenerated_dumps_share_one_trustc() {
    let all = fixtures();
    let mut seen = BTreeMap::new();
    for name in regen_names() {
        assert!(
            ir_dir().join(format!("{name}.rs")).is_file(),
            "REGEN_NAMES `{name}` has no {name}.rs"
        );
        let text = all.get(&name).unwrap_or_else(|| panic!("REGEN_NAMES `{name}` has no dump"));
        match provenance(text) {
            Ok(Provenance::Trustc { sha, date, hand_edit: false }) => {
                seen.entry((sha, date)).or_insert_with(Vec::new).push(name);
            }
            other => panic!(
                "{name}.trust_ir: a regenerated dump must be a plain trustc dump, got {other:?}"
            ),
        }
    }
    assert_eq!(
        seen.len(),
        1,
        "the regenerated dumps name more than one trustc (a partial re-pin): {seen:#?}"
    );
}

#[test]
fn every_source_with_a_dump_is_regenerated_or_held() {
    let regen = regen_names();
    let all = fixtures();
    for (held, why) in HELD {
        assert!(!regen.iter().any(|n| n == held), "`{held}` is both regenerated and held");
        assert!(all.contains_key(*held), "held `{held}` ({why}) has no dump");
    }
    for name in all.keys() {
        if !ir_dir().join(format!("{name}.rs")).is_file() {
            continue;
        }
        assert!(
            regen.iter().any(|n| n == name) || HELD.iter().any(|(h, _)| h == name),
            "{name}.rs has a dump, but the regeneration script neither regenerates nor holds it"
        );
    }
}

#[test]
fn a_dump_without_a_usable_header_is_refused() {
    let sha = "771983b92b0b1266779c958d43234540aad66ccd";
    let body = "module \"m\"\n";
    let ok = format!("{TEXT_HEADER}\n; trustc {sha} 2026-10-01\n{body}");
    assert_eq!(
        provenance(&ok),
        Ok(Provenance::Trustc { sha: sha.into(), date: "2026-10-01".into(), hand_edit: false })
    );
    let hand =
        format!("{TEXT_HEADER}\n; trustc {sha} 2026-10-01\n; HAND EDIT (labeled): x\n{body}");
    assert!(matches!(provenance(&hand), Ok(Provenance::Trustc { hand_edit: true, .. })));
    let synthetic = format!("{TEXT_HEADER}\n; SYNTHETIC, hand-written\n{body}");
    assert_eq!(provenance(&synthetic), Ok(Provenance::Synthetic));
    for refused in [
        // No header at all: the 771983b92 dumps as they were.
        format!("{TEXT_HEADER}\n{body}"),
        // The header after the module line is not a header.
        format!("{TEXT_HEADER}\n{body}; trustc {sha} 2026-10-01\n"),
        // The plan's `#` spelling: not trust-ir text.
        format!("# trustc {sha} 2026-10-01\n{TEXT_HEADER}\n{body}"),
        // Two producers.
        format!("{TEXT_HEADER}\n; trustc {sha} 2026-10-01\n; trustc {sha} 2026-10-02\n{body}"),
        // An abbreviated hash, a missing or malformed date, a trailing word.
        format!("{TEXT_HEADER}\n; trustc 771983b92 2026-10-01\n{body}"),
        format!("{TEXT_HEADER}\n; trustc {sha}\n{body}"),
        format!("{TEXT_HEADER}\n; trustc {sha} 2026-1001\n{body}"),
        format!("{TEXT_HEADER}\n; trustc {sha} 2026-10-01 dirty\n{body}"),
        format!("{TEXT_HEADER}\n; trustc {} 2026-10-01\n{body}", sha.to_uppercase()),
        // A hand-written module claiming a producer.
        format!("{TEXT_HEADER}\n; SYNTHETIC\n; trustc {sha} 2026-10-01\n{body}"),
        // A hand edit that names no dump it edits.
        format!("{TEXT_HEADER}\n; HAND EDIT (labeled): x\n{body}"),
    ] {
        assert!(provenance(&refused).is_err(), "accepted:\n{refused}");
    }
}
