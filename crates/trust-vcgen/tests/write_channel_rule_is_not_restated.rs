// The write-channel rule is stated ONCE (`generate::path_defs::borrow_write_target`
// and its own-storage member `own_storage_write_borrow`; the wide form with no
// read-only exemption, keyed on one local, is `trust_types::Statement::escapes_local`). `trust_types::Statement::escapes_local_storage`,
// which trust-mir-extract's slice-length gate asks, is NOT the slot rule keyed on one
// local: it asks only whether a borrow can RESEAT the local, so it drops every borrow
// whose first projection is `Deref` (`&mut (*p)` included, which the slot rule counts)
// and counts `&raw const` of a place whose `Deref` is not first, which the slot rule
// leaves off — a second slot predicate, sound for its own question. Every
// scan that missed `&raw const` before 2026-09-30 — the havoc list, four stability
// scans, the float lane's three, `f4_whole_local_defs`, a guards recognizer,
// `backing_cert`, and trust-mir-extract's slice-length gate — spelled the channel
// by hand in one of two shapes that name `&mut` and `&raw mut` and silently drop
// `&raw const`:
//
//     Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(true, b)   // an or-pattern
//     Rvalue::AddressOf(true, place) => …                                     // its own arm
//
// This test refuses both in PATTERN position (an or-pattern arm, or
// `AddressOf(true, <binding>)` followed by `=>`, `if` or an if-let `=`) anywhere in
// the verifier's sources, so a new scan either asks the rule or spells the wide
// form (`AddressOf(_, …)`). A construction (`Rvalue::AddressOf(true, Place::…)`) is
// not a pattern and is not flagged. It is a SOURCE SCAN, not a proof: it cannot see
// a scan that lists `&mut` alone, or one that binds the flag and tests it later.
// Measured on origin/main 8ad8af8ec9: it lists exactly the ten sites this change
// rewrote in or-pattern form, plus the two separate-arm ones. Evidence rung: test.
use std::path::{Path, PathBuf};

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read {dir:?}: {e}")) {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
}

/// Every `Rvalue::AddressOf(true, …)` in PATTERN position in `text`, as 1-based
/// lines: an or-pattern arm (`| Rvalue::AddressOf(true, …)`, whitespace and
/// newlines before it ignored), or `Rvalue::AddressOf(true, <binding>)` followed by
/// `=>`, `if`, or an if-let `=`.
fn narrow_channel_arms(text: &str) -> Vec<usize> {
    let needle = "Rvalue::AddressOf(true,";
    let mut hits = Vec::new();
    let mut from = 0;
    while let Some(off) = text[from..].find(needle) {
        let at = from + off;
        let before = text[..at].trim_end();
        let or_arm = before.ends_with('|') && !before.ends_with("||");
        let rest = text[at + needle.len()..].trim_start();
        let binding: String =
            rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
        let after = rest[binding.len()..].trim_start();
        let own_arm = !binding.is_empty()
            && binding.starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
            && after.starts_with(')')
            && {
                let next = after[1..].trim_start();
                next.starts_with("=>")
                    || next.starts_with("if ")
                    || (next.starts_with('=') && !next.starts_with("=="))
            };
        if or_arm || own_arm {
            hits.push(text[..at].matches('\n').count() + 1);
        }
        from = at + needle.len();
    }
    hits
}

#[test]
fn no_scan_restates_the_mut_only_write_channel() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("crates dir");
    let mut files = Vec::new();
    for krate in ["trust-vcgen/src", "trust-mir-extract/src"] {
        rust_files(&crates.join(krate), &mut files);
    }
    files.sort();
    assert!(files.len() > 50, "the scan must actually see the sources: {}", files.len());
    let mut offenders = Vec::new();
    for file in &files {
        let text = std::fs::read_to_string(file).expect("readable source");
        for line in narrow_channel_arms(&text) {
            offenders.push(format!("{}:{line}", file.strip_prefix(crates).unwrap().display()));
        }
    }
    assert!(
        offenders.is_empty(),
        "a scan spells the write channel as `&mut | &raw mut` only, dropping `&raw \
         const`: ask `generate::borrow_write_target` / `own_storage_write_borrow` (or \
         `trust_types::Statement::escapes_local{{,_storage}}`) instead:\n{}",
        offenders.join("\n")
    );
}

#[test]
fn the_scan_sees_the_arms_it_refuses() {
    // The two shapes the pre-2026-09-30 scans used, and what it must not flag.
    let or_arm =
        "if let Rvalue::Ref { mutable: true, place: b }\n    | Rvalue::AddressOf(true, b) = rvalue";
    assert_eq!(narrow_channel_arms(or_arm), vec![2]);
    let own_arm = "match rvalue {\n    Rvalue::AddressOf(true, place) => place,\n}";
    assert_eq!(narrow_channel_arms(own_arm), vec![2]);
    let if_let = "if let Rvalue::AddressOf(true, b) = rvalue {}";
    assert_eq!(narrow_channel_arms(if_let), vec![1]);
    let wide = "Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place) => Some(place)";
    assert!(narrow_channel_arms(wide).is_empty());
    for construction in [
        "rvalue: Rvalue::AddressOf(true, Place::local(1)),",
        "mir::RawPtrKind::Mut => Rvalue::AddressOf(true, converted_place),",
        "(Rvalue::AddressOf(true, owned.clone()), Some(&owned)),",
        "assert!(Rvalue::AddressOf(true, place) == other);",
    ] {
        assert!(narrow_channel_arms(construction).is_empty(), "{construction}");
    }
}

/// The one `fn` of this crate that may ask the SLOT rule's cell-blind classifier
/// (`trust_types::local_defs::statement_escapes_local_slot`): the `LocalWriteIndex`
/// visitor behind the indexed `source_slot_is_stable` twins, whose answers are asserted
/// equal to the shared walks under the differential harness. Trust: 2026-11-07
/// (VCGEN-CENSUS-SITE-REDS-1): PERF-COMPILER-VCGEN-77 (`257cbd36b0`) wrote that visitor
/// with a bare `stmt.escapes_local(local)`.
const SLOT_CLASSIFIER_FNS: &[&str] = &["visit_located_slot_writes"];

/// Every `.escapes_local(` CALL in `text` (comment lines skipped), and every qualified
/// `Statement::escapes_local` (a call or the method as a function value), as 1-based
/// lines, except inside the one wrapper `fn body_stmt_escapes_local`; and every use of
/// the slot rule's named cell-blind classifier `statement_escapes_local_slot` outside
/// [`SLOT_CLASSIFIER_FNS`] (the same question under its trust-types name).
fn bare_escape_calls(text: &str) -> Vec<usize> {
    let mut hits = Vec::new();
    let mut current_fn = String::new();
    for (i, line) in text.lines().enumerate() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") {
            continue;
        }
        if let Some(at) = trimmed.find("fn ") {
            let name: String = trimmed[at + 3..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                current_fn = name;
            }
        }
        let qualified = line
            .match_indices("Statement::escapes_local")
            .any(|(at, m)| !line[at + m.len()..].starts_with('_'));
        let slot_classifier = line.contains("statement_escapes_local_slot")
            && !SLOT_CLASSIFIER_FNS.contains(&current_fn.as_str());
        if ((line.contains(".escapes_local(") || qualified)
            && current_fn != "body_stmt_escapes_local")
            || slot_classifier
        {
            hits.push(i + 1);
        }
    }
    hits
}

/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1). `trust_types::Statement::escapes_local`
/// leaves a SHARED borrow off, which is right for `Freeze` bytes and wrong for
/// `UnsafeCell` bytes: `poke(&c)` rewrites an owned `c: Cell<usize>`. Every scan in the
/// verifier asks `crate::stmt_escapes_local` (or `crate::body_stmt_escapes_local`), which
/// adds the shared borrow of a cell; a bare `.escapes_local(` call anywhere else in
/// `trust-vcgen/src` is refused, `*_tests.rs` unit modules aside (they pin the
/// difference). A source scan, not a proof: it cannot see the method passed as a
/// function value under another name.
#[test]
fn no_scan_asks_the_cell_blind_escape_question() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    rust_files(&src, &mut files);
    files.sort();
    assert!(files.len() > 50, "the scan must actually see the sources: {}", files.len());
    let mut offenders = Vec::new();
    let mut wrapper_seen = false;
    for file in &files {
        let text = std::fs::read_to_string(file).expect("readable source");
        wrapper_seen |= text.contains("fn body_stmt_escapes_local(");
        // A `#[cfg(test)]` unit module (`*_tests.rs`) is no scan: it may ask the
        // cell-blind question to pin how it differs from the wrapper.
        if file.file_name().is_some_and(|n| n.to_string_lossy().ends_with("_tests.rs")) {
            continue;
        }
        for line in bare_escape_calls(&text) {
            offenders.push(format!("{}:{line}", file.strip_prefix(&src).unwrap().display()));
        }
    }
    assert!(wrapper_seen, "the wrapper `body_stmt_escapes_local` must exist");
    assert!(
        offenders.is_empty(),
        "a scan asks `Statement::escapes_local` directly, which misses a shared borrow of \
         `UnsafeCell` bytes: ask `crate::stmt_escapes_local` instead:\n{}",
        offenders.join("\n")
    );
}

#[test]
fn the_escape_scan_sees_the_calls_it_refuses() {
    let bare = "fn f() {\n    if stmt.escapes_local(local) {}\n}";
    assert_eq!(bare_escape_calls(bare), vec![2]);
    let wrapper = "pub(crate) fn body_stmt_escapes_local(\n    body: &B,\n) -> bool {\n    stmt.escapes_local(local)\n}";
    assert!(bare_escape_calls(wrapper).is_empty());
    let doc = "/// `stmt.escapes_local(local)` is the wide form.";
    assert!(bare_escape_calls(doc).is_empty());
    let routed = "fn g() {\n    crate::stmt_escapes_local(func, stmt, local)\n}";
    assert!(bare_escape_calls(routed).is_empty());
    let value = "fn h() {\n    walk(body, local, trust_types::Statement::escapes_local, f)\n}";
    assert_eq!(bare_escape_calls(value), vec![2], "the method as a function value");
    let narrow =
        "fn k() {\n    walk(body, local, trust_types::Statement::escapes_local_storage, f)\n}";
    assert!(bare_escape_calls(narrow).is_empty(), "the narrow storage classifier is another rule");
    let slot_index = "fn visit_located_slot_writes() {\n    \
                      if trust_types::local_defs::statement_escapes_local_slot(stmt, local) {}\n}";
    assert!(bare_escape_calls(slot_index).is_empty(), "the indexed slot rule's own visitor");
    let slot_elsewhere = "fn scan() {\n    \
                          if trust_types::local_defs::statement_escapes_local_slot(stmt, local) {}\n}";
    assert_eq!(bare_escape_calls(slot_elsewhere), vec![2], "the cell-blind question by its name");
}
