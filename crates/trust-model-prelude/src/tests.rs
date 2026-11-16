// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Unit tests. `tests::digest::` is the push-lane instrument of B1A-D35
//! (`scripts/check_crates_tests_scoped.py`, `CROSS_CRATE_INSTRUMENTS`): it must stay
//! a debug-cheap module of this file holding `source_digest_matches`.

use super::{EP_VERSION, MODULE_ORDER, MODULES};

mod digest {
    use trust_sha2::{Digest, Sha256};

    use super::super::{MODULES, PRELUDE_DIGEST, PRELUDE_TERM_DIGEST};

    /// SHA-256 over `(name NUL source NUL)*` in `MODULES` order (B1A-D35), lower-case hex.
    fn source_digest() -> String {
        let mut hasher = Sha256::new();
        for (name, _, source) in MODULES {
            hasher.update(name.as_bytes());
            hasher.update([0u8]);
            hasher.update(source.as_bytes());
            hasher.update([0u8]);
        }
        hex(hasher.finalize().as_ref())
    }

    fn hex(bytes: &[u8]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut out = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            out.push(char::from(DIGITS[usize::from(byte >> 4)]));
            out.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
        }
        out
    }

    fn is_sha256_hex(text: &str) -> bool {
        text.len() == 64 && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    }

    #[test]
    fn source_digest_matches() {
        let fresh = source_digest();
        assert_eq!(
            fresh, PRELUDE_DIGEST,
            "a served Trust/*.lean module changed: re-bless PRELUDE_DIGEST with \
             `--ignored --exact tests::digest::print_source_digest` (B1A-D35)"
        );
    }

    #[test]
    fn the_digest_frames_names_and_sources() {
        // The NUL framing is what the digest is defined over: moving bytes from a
        // source into the next name changes the digest even though the
        // concatenation of all bytes stays the same.
        assert_eq!(hex(&[0x00, 0x7f, 0xa5, 0xff]), "007fa5ff");
        let framed = |parts: &[(&str, &str)]| {
            let mut hasher = Sha256::new();
            for (name, source) in parts {
                hasher.update(name.as_bytes());
                hasher.update([0u8]);
                hasher.update(source.as_bytes());
                hasher.update([0u8]);
            }
            hex(hasher.finalize().as_ref())
        };
        assert_ne!(framed(&[("A", "xy"), ("B", "z")]), framed(&[("A", "x"), ("yB", "z")]));
        // FIPS 180-4 test vector, so the hasher really is SHA-256.
        assert_eq!(
            hex(Sha256::digest(b"abc").as_ref()),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn digest_literals_are_sha256_hex() {
        assert!(is_sha256_hex(PRELUDE_DIGEST), "{PRELUDE_DIGEST}");
        assert!(is_sha256_hex(PRELUDE_TERM_DIGEST), "{PRELUDE_TERM_DIGEST}");
    }

    #[test]
    #[ignore = "prints a fresh PRELUDE_DIGEST for re-blessing (TASK-STATE 4.5)"]
    fn print_source_digest() {
        let fresh = source_digest();
        println!("PRELUDE_DIGEST = \"{fresh}\"");
        assert!(is_sha256_hex(&fresh));
    }
}

#[test]
fn modules_follow_the_d50_order() {
    let names: Vec<&str> = MODULES.iter().map(|(name, _, _)| *name).collect();
    let mut order = MODULE_ORDER.iter();
    for name in &names {
        assert!(
            order.any(|m| m == name),
            "{name} is not in B1A-D50 order (or is served twice): {names:?}"
        );
    }
    assert_eq!(&names[..2], ["Trust.Temporal", "Trust.FiniteModel"]);
    for (index, (module, deps, source)) in MODULES.iter().enumerate() {
        assert!(!source.trim().is_empty(), "{module} is empty");
        for dep in *deps {
            let at = names.iter().position(|m| m == dep);
            assert!(
                at.is_some_and(|at| at < index),
                "{module} is served before its dependency {dep}"
            );
        }
    }
}

#[test]
fn the_served_modules_are_the_lane_files() {
    // MODULES names each file by the namespace it opens; a swapped include fails here.
    assert!(super::TEMPORAL.contains("namespace Trust\nnamespace Temporal\n"));
    assert!(super::TEMPORAL.contains("def Always"));
    assert!(super::FINITE_MODEL.contains("namespace Temporal\nnamespace FiniteModel\n"));
    assert!(super::FINITE_MODEL.contains("inductive Member"));
    assert!(super::LIST.contains("namespace Trust\nnamespace Temporal\n"));
    assert!(super::LIST.contains("@[reducible] def Member"));
    assert!(super::GRAPH.contains("namespace Trust\nnamespace Temporal\n"));
    assert!(super::GRAPH.contains("inductive Reach"));
    assert!(super::MODEL_VALUE.contains("namespace Trust\nnamespace Model\n"));
    assert!(super::MODEL_SYNTAX.contains("namespace Trust\nnamespace Model\n"));
    assert!(super::MODEL_SYNTAX.contains("inductive PrimOp where"));
    assert!(super::MODEL_SPEC.contains("namespace Trust\nnamespace Model\n"));
    assert!(super::MODEL_SPEC.contains("structure Spec where"));
    assert!(super::MODEL_TLC.contains("namespace Trust\nnamespace Model\n"));
    assert!(super::MODEL_TLC.contains("inductive XVal where"));
    assert!(super::MODEL_TLC.contains("def Tlc.run (sp : Spec)"));
}

#[test]
fn ep_version_mirrors_the_lean_definition() {
    assert_eq!(EP_VERSION, 1);
    let line = format!("def epVersion : Nat := {EP_VERSION}");
    assert_eq!(
        super::MODEL_VALUE.lines().filter(|l| l.trim() == line).count(),
        1,
        "Trust.Model.Value must define `{line}` exactly once"
    );
}

#[test]
fn check_ep_version_refuses_until_complete() {
    // EP_COMPLETE flips only when the lane lands (B1A-54); until then the current
    // version is refused too.
    assert_eq!(super::check_ep_version(EP_VERSION).is_ok(), super::EP_COMPLETE);
    let refused = super::check_ep_version_with(EP_VERSION, false).unwrap_err();
    assert_eq!(refused.code(), "model.ep-version");
    assert!(!refused.complete);
    assert!(refused.to_string().starts_with("model.ep-version: "), "{refused}");
    assert_eq!(super::check_ep_version(2).unwrap_err().requested, 2);
    // Complete: only EP_VERSION is accepted.
    assert_eq!(super::check_ep_version_with(EP_VERSION, true), Ok(()));
    assert!(super::check_ep_version_with(EP_VERSION + 1, true).is_err());
    assert!(super::check_ep_version_with(0, true).is_err());
}

/// The design's fixed codes (ty design 10:109) and `cmp.unpinned` (B1A-D14, added by
/// B1A-11a for `tlcCmp`, B1A-D86): every one is in the table. The `lazy.<op>` family
/// gets codes as forcing rows need them (B1A-D22).
const DESIGN_CODES: &[&str] = &[
    "int.div-wrap",
    "cmp.unpinned",
    "lazy.arg",
    "lazy.except",
    "lazy.refused-force",
    "lazy.mem-kind",
    "lazy.soa-elem",
    "lazy.enabled-assign",
];

/// Parse every `def Code.` line of every served module. Each must have exactly the form
/// `def Code.<name> : Nat := <n>  -- <code> <refusal>` (Trust/Model/Value.lean's table
/// header); any other `def Code.` line is an error, so a code cannot be added to the
/// Lean table without this parser seeing it.
fn parse_code_table(modules: &[(&str, &str)]) -> Result<Vec<super::UnmodeledCode>, String> {
    let mut table = Vec::new();
    for (module, source) in modules {
        for (index, line) in source.lines().enumerate() {
            let trimmed = line.trim_start();
            // A comment line is not a definition (the table header quotes the form).
            if trimmed.starts_with("--") || !trimmed.contains("def Code.") {
                continue;
            }
            let at = format!("{module}:{}", index + 1);
            if *module != "Trust.Model.Value" {
                return Err(format!("{at}: a code outside Trust.Model.Value: {line}"));
            }
            let rest = trimmed
                .strip_prefix("def Code.")
                .ok_or_else(|| format!("{at}: not a table line: {line}"))?;
            let (name, rest) =
                rest.split_once(" : Nat := ").ok_or_else(|| format!("{at}: no ` : Nat := `"))?;
            let (number, comment) =
                rest.split_once("  -- ").ok_or_else(|| format!("{at}: no `  -- ` comment"))?;
            let number: u32 =
                number.parse().map_err(|_| format!("{at}: number `{number}` is not a Nat"))?;
            let fields: Vec<&str> = comment.split(' ').collect();
            let [code, refusal] = fields[..] else {
                return Err(format!("{at}: comment `{comment}` is not `<code> <refusal>`"));
            };
            if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric()) {
                return Err(format!("{at}: name `{name}`"));
            }
            table.push(super::UnmodeledCode {
                number,
                code: leak(code),
                lean: leak(&format!("Trust.Model.Code.{name}")),
                refusal: leak(refusal),
            });
        }
    }
    Ok(table)
}

fn lean_code_table() -> Result<Vec<super::UnmodeledCode>, String> {
    let modules: Vec<(&str, &str)> =
        MODULES.iter().map(|(name, _, source)| (*name, *source)).collect();
    parse_code_table(&modules)
}

fn leak(text: &str) -> &'static str {
    Box::leak(text.to_owned().into_boxed_str())
}

#[test]
fn unmodeled_codes_mirror_the_lean_table() {
    let lean = lean_code_table().expect("the Lean code table parses");
    assert_eq!(lean.as_slice(), super::UNMODELED_CODES, "UNMODELED_CODES and Value.lean differ");
    let mut numbers: Vec<u32> = lean.iter().map(|c| c.number).collect();
    numbers.sort_unstable();
    numbers.dedup();
    assert_eq!(numbers.len(), lean.len(), "two codes share a number");
    let mut codes: Vec<&str> = lean.iter().map(|c| c.code).collect();
    codes.sort_unstable();
    codes.dedup();
    assert_eq!(codes.len(), lean.len(), "a code is listed twice");
    for design in DESIGN_CODES {
        assert!(lean.iter().any(|c| c.code == *design), "design code {design} missing");
    }
    // The registry mapping of design 10:109 / 50: int.* as model.int-div-wrap, every
    // lazy.* as model.lazy-unpinned; only the placeholder has none.
    for entry in &lean {
        let expected = if entry.code == "todo" {
            "-"
        } else if entry.code.starts_with("int.") && entry.code.ends_with("-wrap") {
            "model.int-div-wrap"
        } else if entry.code.starts_with("lazy.") {
            "model.lazy-unpinned"
        } else if entry.code == "cmp.unpinned" {
            "model.cmp-unpinned"
        } else {
            panic!("code {} is from no design source (B1A-D13)", entry.code);
        };
        assert_eq!(entry.refusal, expected, "{entry:?}");
    }
}

#[test]
fn the_code_table_parser_rejects_malformed_lines() {
    // Negative controls of the parser the mirror test uses: each malformed table line is
    // an error, so the mirror cannot pass by skipping a line it fails to read.
    let one = |line: &str| parse_code_table(&[("Trust.Model.Value", line)]);
    let good = one("def Code.a : Nat := 3  -- lazy.x model.lazy-unpinned").expect("well formed");
    assert_eq!(good.len(), 1);
    assert_eq!(good[0].lean, "Trust.Model.Code.a");
    assert_eq!(good[0].number, 3);
    for bad in [
        "def Code.a : Nat := 3",
        "def Code.a : Nat := three  -- lazy.x model.lazy-unpinned",
        "def Code.a : Nat := 3  -- lazy.x",
        "def Code.a : Nat := 3  -- lazy.x model.lazy-unpinned extra",
        "def Code.a := 3  -- lazy.x model.lazy-unpinned",
        "def Code.a.b : Nat := 3  -- lazy.x model.lazy-unpinned",
        "@[reducible] def Code.a : Nat := 3  -- lazy.x model.lazy-unpinned",
    ] {
        assert!(one(bad).is_err(), "accepted: {bad}");
    }
    assert!(
        parse_code_table(&[(
            "Trust.Model.Syntax",
            "def Code.a : Nat := 3  -- lazy.x model.lazy-unpinned"
        )])
        .is_err(),
        "a code outside Value.lean was accepted"
    );
    // Lines that are not table lines are ignored: a non-code `def`, and a comment.
    assert_eq!(one("def notACode : Nat := 3").expect("ignored"), Vec::new());
    assert_eq!(one("-- def Code.a : Nat := 3").expect("ignored"), Vec::new());
}

/// Check every use of `unmodeled` in the code of the served modules (`--` comments
/// stripped): it is the constructor's own declaration `| unmodeled (code : Nat)` in
/// `Trust.Model.Value` (exactly once), or `Fail.unmodeled` (optionally
/// `Trust.Model.Fail.unmodeled`) applied, on the same line, to a constant
/// `Code.<name>` / `Trust.Model.Code.<name>` of the parsed table. A raw numeral
/// (`Fail.unmodeled 7`), a computed or bound argument, the anonymous `.unmodeled` form
/// or an argument on the next line would bypass the table and its registry mapping, so
/// each is an error (B1A-10 verifier finding 5). Returns the Lean names of the codes
/// applied, in source order.
fn unmodeled_uses(
    modules: &[(&str, &str)],
    table: &[super::UnmodeledCode],
) -> Result<Vec<String>, String> {
    const DECLARATION: &str = "| unmodeled (code : Nat)";
    const WORD: &str = "unmodeled";
    let mut applications: Vec<String> = Vec::new();
    let mut declarations = 0usize;
    for (module, source) in modules {
        for (index, line) in source.lines().enumerate() {
            let at = format!("{module}:{}", index + 1);
            let code = line.split_once("--").map_or(line, |(code, _)| code);
            let mut from = 0usize;
            while let Some(offset) = code[from..].find(WORD) {
                let start = from + offset;
                let end = start + WORD.len();
                from = end;
                let before = &code[..start];
                let after = &code[end..];
                if code.trim_start() == DECLARATION && *module == "Trust.Model.Value" {
                    declarations += 1;
                    continue;
                }
                let Some(head) = before.strip_suffix("Fail.") else {
                    return Err(format!("{at}: `unmodeled` not as `Fail.unmodeled`: {line}"));
                };
                let head = head.strip_suffix("Trust.Model.").unwrap_or(head);
                if head.ends_with(|c: char| c.is_ascii_alphanumeric() || c == '.' || c == '_') {
                    return Err(format!("{at}: `Fail.unmodeled` behind a qualifier: {line}"));
                }
                let Some(rest) = after
                    .strip_prefix(" Code.")
                    .or_else(|| after.strip_prefix(" Trust.Model.Code."))
                else {
                    return Err(format!("{at}: `Fail.unmodeled` not applied to a code: {line}"));
                };
                let name: String = rest.chars().take_while(char::is_ascii_alphanumeric).collect();
                let tail = &rest[name.len()..];
                if tail.starts_with(['.', '_', '\'']) {
                    return Err(format!("{at}: `Code.{name}` continues: {line}"));
                }
                let lean = format!("Trust.Model.Code.{name}");
                if !table.iter().any(|entry| entry.lean == lean) {
                    return Err(format!("{at}: `{lean}` is not in the code table: {line}"));
                }
                applications.push(lean);
            }
        }
    }
    if declarations != 1 {
        return Err(format!("{declarations} declarations of `unmodeled` in Trust.Model.Value"));
    }
    Ok(applications)
}

#[test]
fn unmodeled_is_applied_only_to_table_codes() {
    let modules: Vec<(&str, &str)> =
        MODULES.iter().map(|(name, _, source)| (*name, *source)).collect();
    let table = lean_code_table().expect("the Lean code table parses");
    let applications = unmodeled_uses(&modules, &table).expect("every `unmodeled` is a table code");
    // Not vacuous: the two codes that stay for good are applied (`intDiv`'s wrap refusal,
    // B1A-10; `tlcCmp`'s unpinned orders, B1A-11a). `todo`'s use goes with B1A-15/25.
    for code in ["Trust.Model.Code.intDivWrap", "Trust.Model.Code.cmpUnpinned"] {
        assert!(applications.iter().any(|name| name == code), "{code} is never applied");
    }
}

#[test]
fn the_unmodeled_use_check_rejects_bypasses() {
    // Negative controls of `unmodeled_uses`: each line bypasses the table, so each is an
    // error; the well-formed forms pass.
    let table = [super::UnmodeledCode {
        number: 7,
        code: "cmp.unpinned",
        lean: "Trust.Model.Code.cmpUnpinned",
        refusal: "model.cmp-unpinned",
    }];
    let declaration = "inductive Fail where\n  | unmodeled (code : Nat)\n";
    // `body` in Trust.Model.Value after the declaration, or in `module` beside it.
    let check = |module: &str, body: &str| {
        if module == "Trust.Model.Value" {
            unmodeled_uses(&[(module, leak(&format!("{declaration}{body}")))], &table)
        } else {
            unmodeled_uses(&[("Trust.Model.Value", declaration), (module, body)], &table)
        }
    };
    for good in [
        "def a : Res Nat := Res.error (Fail.unmodeled Code.cmpUnpinned)",
        "def a : Res Nat := Res.error (Trust.Model.Fail.unmodeled Trust.Model.Code.cmpUnpinned)",
        "def a : Nat := 3  -- a comment may say Fail.unmodeled 7",
    ] {
        assert!(check("Trust.Model.Value", good).is_ok(), "refused: {good}");
        assert!(check("Trust.Model.Tlc", good).is_ok(), "refused in another module: {good}");
    }
    for bad in [
        "def a : Res Nat := Res.error (Fail.unmodeled 7)",
        "def a : Res Nat := Res.error (.unmodeled 7)",
        "def a : Res Nat := Res.error (Fail.unmodeled (Code.cmpUnpinned + 1))",
        "def a (c : Nat) : Res Nat := Res.error (Fail.unmodeled c)",
        "def a : Res Nat := Res.error (Fail.unmodeled Code.lazyArg)",
        "def a : Res Nat := Res.error (Fail.unmodeled Code.cmpUnpinned.x)",
        "def a : Res Nat := Res.error (Fail.unmodeled\n  Code.cmpUnpinned)",
        "def a : Res Nat := Res.error (My.Fail.unmodeled Code.cmpUnpinned)",
        "def unmodeledHelper : Nat := 7",
    ] {
        assert!(check("Trust.Model.Value", bad).is_err(), "accepted: {bad}");
        assert!(check("Trust.Model.Tlc", bad).is_err(), "accepted in another module: {bad}");
    }
    // The declaration must be in Trust.Model.Value, exactly once.
    assert!(unmodeled_uses(&[("Trust.Model.Value", "")], &table).is_err());
    assert!(unmodeled_uses(&[("Trust.Model.Tlc", declaration)], &table).is_err());
    let twice = leak(&format!("{declaration}{declaration}"));
    assert!(unmodeled_uses(&[("Trust.Model.Value", twice)], &table).is_err());
}

/// Contract K2 at the version B1A-12 started from: version 2, amendment 4
/// (`CONTRACT_VERSION = 2`, `CONTRACT_AMENDMENT = 4`), every row of ty
/// `crates/tla-model-ir/src/ops.rs` `OPS` (:476-603) at ty `874e62f03b`, in order, as
/// (mnemonic, is a row of class `Value`). A K2 change is a new contract version; moving
/// this list is a deliberate re-reading of the catalog (B1A-D10).
const K2_ROWS: &[(&str, bool)] = &[
    ("rep.load", false),
    ("rep.store", false),
    ("int.add", true),
    ("int.sub", true),
    ("int.mul", true),
    ("int.div", true),
    ("int.mod", true),
    ("int.neg", true),
    ("int.lt", true),
    ("int.le", true),
    ("int.eq", true),
    ("enum.eq", true),
    ("enum.lt", true),
    ("rec.get", true),
    ("rec.with", true),
    ("func.apply", true),
    ("func.except", true),
    ("func.domain", true),
    ("set.in", true),
    ("set.insert", true),
    ("set.union", true),
    ("set.diff", true),
    ("set.card", true),
    ("set.subseteq", true),
    ("set.iter", true),
    ("seq.len", true),
    ("seq.index", true),
    ("seq.append", true),
    ("seq.head", true),
    ("seq.tail", true),
    ("seq.subseq", true),
    ("box", false),
    ("unbox", false),
    ("top.call", false),
    ("gen.branch", false),
    ("gen.loop", false),
    ("gen.assign", false),
    ("gen.guard", false),
    ("gen.emit", false),
    ("gen.enabled_exit", false),
    ("value.eq", true),
    ("value.ne", true),
    ("value.eq_func_except", true),
    ("value.eq_record_new", true),
    ("set.enum", true),
    ("set.range", true),
    ("set.intersect", true),
    ("set.big_union", true),
    ("set.powerset", true),
    ("set.product", true),
    ("set.is_finite", true),
    ("func.set", true),
    ("rec.new", true),
    ("rec.set_of", true),
    ("tuple.new", true),
    ("tuple.get", true),
    ("seq.new", true),
    ("seq.concat", true),
    ("seq.set", true),
    ("seq.remove_at", true),
    ("gen.keep", false),
    ("gen.if", false),
    ("gen.unit", false),
    ("raise", false),
    ("loop.begin", false),
    ("loop.next", false),
    ("loop.binder", false),
    ("loop.yield", false),
    ("loop.end", false),
    ("pool.load", false),
    ("gen.next", false),
    ("gen.back", false),
    ("gen.forall_init", false),
    ("gen.forall_step", false),
    ("gen.forall_check", false),
    ("gen.assign_in", false),
    ("gen.pred", false),
    ("value.as_bool", true),
    ("gen.view", false),
    ("func.tabulate", true),
];

/// The value rows B1A-D10 excludes as L4-only representation, iterator or fused rows.
const K2_EXCLUDED: &[&str] = &[
    "int.eq",
    "enum.eq",
    "enum.lt",
    "set.iter",
    "value.eq_func_except",
    "value.eq_record_new",
    "seq.new",
    "func.tabulate",
];

/// The constructors B1A-D10 adds for TLC operators K2 lacks, in declaration order.
const B1A_ADDITIONS: &[&str] = &["intPow", "intGt", "intGe", "natSuccU", "natSatU", "assert"];

/// A K2 mnemonic in camelCase: `set.big_union` is `setBigUnion`.
fn camel(mnemonic: &str) -> String {
    let mut out = String::new();
    let mut upper = false;
    for c in mnemonic.chars() {
        if c == '.' || c == '_' {
            upper = true;
        } else if upper {
            out.push(c.to_ascii_uppercase());
            upper = false;
        } else {
            out.push(c);
        }
    }
    out
}

/// The constructors of `inductive PrimOp`, in order: the `| name ...` alternatives of the
/// lines after `inductive PrimOp where`, up to the first line that is not one.
fn primop_constructors(source: &str) -> Result<Vec<String>, String> {
    let mut lines = source.lines().skip_while(|l| l.trim() != "inductive PrimOp where");
    lines.next().ok_or("no `inductive PrimOp where`")?;
    let mut names = Vec::new();
    for line in lines {
        let Some(alternatives) = line.trim().strip_prefix('|') else { break };
        for alternative in alternatives.split(" | ") {
            let name = alternative.split_whitespace().next().unwrap_or("");
            if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric()) {
                return Err(format!("PrimOp alternative `{alternative}`"));
            }
            names.push(name.to_owned());
        }
    }
    Ok(names)
}

/// Check Syntax.lean's PrimOp doc-comment table (`-- | <constructor> | <row> |`) against
/// its `inductive PrimOp` and against [`K2_ROWS`] (B1A-D10): the table's constructors are
/// exactly the declared ones, in order; each maps to the K2 value row whose camelCase
/// name it is, or is one of [`B1A_ADDITIONS`] marked `B1a addition (K2 request)`; every
/// K2 value row is either a constructor (in `OPS` order) or one of [`K2_EXCLUDED`]
/// marked `excluded L4-only`; no row of another class is in the table.
fn check_primop_table(source: &str) -> Result<(), String> {
    let declared = primop_constructors(source)?;
    let value_rows: Vec<&str> =
        K2_ROWS.iter().filter(|(_, value)| *value).map(|(mnemonic, _)| *mnemonic).collect();
    let mut table_ctors: Vec<String> = Vec::new();
    let mut kept_rows: Vec<&str> = Vec::new();
    let mut excluded: Vec<&str> = Vec::new();
    let mut additions: Vec<String> = Vec::new();
    for line in source.lines() {
        let Some(row) = line.strip_prefix("-- | ") else { continue };
        let cells: Vec<&str> = row.split(" | ").collect();
        let [ctor, target] = cells[..] else {
            return Err(format!("table line `{line}` is not `-- | <constructor> | <row> |`"));
        };
        let target = target
            .strip_suffix(" |")
            .ok_or_else(|| format!("table line `{line}` does not end with ` |`"))?;
        if ctor == "-" {
            let (mnemonic, reason) = target
                .split_once(": excluded L4-only (")
                .ok_or_else(|| format!("excluded line `{line}`"))?;
            if !reason.ends_with(')') || reason.len() < 2 {
                return Err(format!("excluded line `{line}` has no reason"));
            }
            let row = value_rows
                .iter()
                .find(|r| **r == mnemonic)
                .ok_or_else(|| format!("`{mnemonic}` is not a K2 value row"))?;
            excluded.push(row);
            continue;
        }
        table_ctors.push(ctor.to_owned());
        if target == "B1a addition (K2 request)" {
            additions.push(ctor.to_owned());
            continue;
        }
        let row = value_rows
            .iter()
            .find(|r| **r == target)
            .ok_or_else(|| format!("`{ctor}` maps to `{target}`, not a K2 value row"))?;
        if camel(row) != ctor {
            return Err(format!("`{ctor}` is not the camelCase of `{row}`"));
        }
        kept_rows.push(row);
    }
    if table_ctors != declared {
        return Err(format!("table constructors {table_ctors:?} != declared {declared:?}"));
    }
    if additions != B1A_ADDITIONS {
        return Err(format!("additions {additions:?} != {B1A_ADDITIONS:?}"));
    }
    if excluded != K2_EXCLUDED {
        return Err(format!("excluded rows {excluded:?} != {K2_EXCLUDED:?}"));
    }
    let expected_kept: Vec<&str> =
        value_rows.iter().copied().filter(|r| !K2_EXCLUDED.contains(r)).collect();
    if kept_rows != expected_kept {
        return Err(format!(
            "kept rows {kept_rows:?} != the K2 value rows in order {expected_kept:?}"
        ));
    }
    if declared.len() != kept_rows.len() + additions.len() {
        return Err(format!("{} constructors, {} rows mapped", declared.len(), kept_rows.len()));
    }
    Ok(())
}

#[test]
fn primop_table_mirrors_k2() {
    assert_eq!(K2_ROWS.len(), 80, "ty ops.rs OPS has 80 rows at 874e62f03b");
    assert_eq!(K2_ROWS.iter().filter(|(_, value)| *value).count(), 51);
    for row in K2_EXCLUDED {
        assert!(K2_ROWS.contains(&(row, true)), "{row} is not a K2 value row");
    }
    let declared = primop_constructors(super::MODEL_SYNTAX).expect("PrimOp parses");
    assert_eq!(declared.len(), 51 - K2_EXCLUDED.len() + B1A_ADDITIONS.len());
    check_primop_table(super::MODEL_SYNTAX).expect("Syntax.lean's PrimOp table mirrors K2");
}

#[test]
fn the_primop_table_check_rejects_drift() {
    let source = super::MODEL_SYNTAX;
    let one = |find: &str, replace: &str| {
        assert_eq!(source.matches(find).count(), 1, "{find}");
        check_primop_table(&source.replacen(find, replace, 1))
    };
    // A constructor dropped from the inductive, but still in the table.
    assert!(one("  | valueEq | valueNe\n", "  | valueEq\n").is_err());
    // A K2 value row dropped from the table.
    assert!(one("-- | setCard | set.card |\n", "").is_err());
    // A K2 value row excluded beyond D10's list.
    assert!(
        one("-- | setCard | set.card |\n", "-- | - | set.card: excluded L4-only (x) |\n").is_err()
    );
    // A constructor mapped to a row it is not named after.
    assert!(one("-- | intLt | int.lt |", "-- | intLt | int.le |").is_err());
    // An addition that is not one of D10's.
    assert!(one("-- | assert | B1a addition (K2 request) |", "-- | assert | int.eq |").is_err());
    // Two kept rows out of K2 order (both the table and the inductive swapped).
    let swapped = source
        .replacen(
            "-- | intAdd | int.add |\n-- | intSub | int.sub |",
            "-- | intSub | int.sub |\n-- | intAdd | int.add |",
            1,
        )
        .replacen("  | intAdd | intSub |", "  | intSub | intAdd |", 1);
    assert!(check_primop_table(&swapped).is_err());
    // A non-value row in the table.
    assert!(one("-- | intAdd | int.add |", "-- | intAdd | rep.load |").is_err());
}
