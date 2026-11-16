// mir_shim_enum_encoding_gates — source-level pins of the trust-ir -> MIR shim's enum
// tag-encoding gates in `crates/trust-thir-lower/src/to_mir.rs`.
//
// WHY THIS LIVES HERE. `to_mir.rs` needs `rustc_private` and is blob-frozen
// (`scripts/frozen-files.txt`). Its two encoding gates are private fns that only a test inside
// `to_mir.rs` can call, and both an inline test there and a new `mod` line in the (also frozen)
// `trust-thir-lower/src/lib.rs` would move a frozen blob. `trust-types` is the cheap workspace
// member an ordinary `targo test` reaches — the reason `span_normalization_parity.rs` lives here
// too — so this is a SOURCE pin: it reads the shim and asserts the shape of its gates.
//
// WHAT IT DEFENDS. ORACLE-FREEZE-MAIN-1 (docs/DECISION_QUEUE.md, 2026-11-09). trust-ir IR65
// added `EnumTagEncoding::SingleInhabited`, and `to_mir.rs` moved by exactly one match arm
// for it (ada3447e0b, +4/-0 from the pin 0676e4e8a2) in the reason-collecting match of the
// enum-return REFUSAL arm. The waiver row claims the move refuses more and admits nothing new.
// That claim holds iff, in the shim:
//
//   * the by-value byte gate `enum_flip_direct_only` admits a recorded descriptor only when it
//     is `Direct` (a positive allow-list, so a new encoding refuses);
//   * the by-ref logical-read gate `enum_flip_logical_read_ok` admits only `Direct | Niche`;
//   * the only `SingleInhabited` token is inside the enum-return refusal arm, which has no exit
//     but `return unsup(..)`, and whose reason match stays exhaustive (no wildcard, so the next
//     trust-ir encoding again fails to compile and needs its own adjudication);
//   * the enum-return ADMIT arm above it is unchanged and still conjoins the byte gate;
//   * no other place in the shim reads an enum layout descriptor or its encoding.
//
// Each test fails if its part of that claim stops being true of the source, and
// `every_pin_fails_on_its_own_mutant` shows each check firing on a hand-made widening (and
// not firing on a comment or string that merely names the encoding).
//
// WHAT IT IS NOT. A source pin, not an execution: nothing here runs `lower_ir_to_mir` (it needs
// a `TyCtxt`), and it cannot see a widening hidden behind a trust-ir method the shim calls.
// The waiver row declares that half in its PROSE-RESIDUAL clause.

use std::path::{Path, PathBuf};

const SHIM: &str = "crates/trust-thir-lower/src/to_mir.rs";

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is <repo>/crates/trust-types.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").canonicalize().expect("repo root")
}

fn shim_source() -> String {
    std::fs::read_to_string(repo_root().join(SHIM)).expect("read the trust-ir -> MIR shim")
}

/// Two byte-for-byte views of a Rust source: `code` with every comment blanked, and `skeleton`
/// with string and char literal contents blanked as well. Newlines survive, and only whole
/// ASCII-delimited spans are blanked, so a byte offset means the same place in all three.
struct Views {
    code: String,
    skeleton: String,
}

fn views(src: &str) -> Views {
    fn blank(bytes: &mut [u8]) {
        for byte in bytes {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    }
    let b = src.as_bytes();
    let mut code = b.to_vec();
    let mut skeleton = b.to_vec();
    let is_ident = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'/' if b.get(i + 1) == Some(&b'/') => {
                let end = b[i..].iter().position(|&c| c == b'\n').map_or(b.len(), |p| i + p);
                blank(&mut code[i..end]);
                blank(&mut skeleton[i..end]);
                i = end;
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                let (mut depth, mut j) = (1usize, i + 2);
                while j < b.len() && depth > 0 {
                    if b[j] == b'/' && b.get(j + 1) == Some(&b'*') {
                        depth += 1;
                        j += 2;
                    } else if b[j] == b'*' && b.get(j + 1) == Some(&b'/') {
                        depth -= 1;
                        j += 2;
                    } else {
                        j += 1;
                    }
                }
                blank(&mut code[i..j]);
                blank(&mut skeleton[i..j]);
                i = j;
            }
            // `r"…"`, `r#"…"#`, and the byte forms `br…` (the `b` glued in front).
            b'r' if (i == 0
                || !is_ident(b[i - 1])
                || (b[i - 1] == b'b' && (i < 2 || !is_ident(b[i - 2]))))
                && matches!(b.get(i + 1), Some(b'"') | Some(b'#')) =>
            {
                let hashes = b[i + 1..].iter().take_while(|&&c| c == b'#').count();
                let open = i + 1 + hashes;
                if b.get(open) != Some(&b'"') {
                    i += 1;
                    continue;
                }
                let mut close = b"\"".to_vec();
                close.extend(std::iter::repeat_n(b'#', hashes));
                let end = b[open + 1..]
                    .windows(close.len())
                    .position(|w| w == close.as_slice())
                    .map_or(b.len(), |p| open + 1 + p);
                blank(&mut skeleton[open + 1..end]);
                i = (end + close.len()).min(b.len());
            }
            b'"' => {
                let mut j = i + 1;
                while j < b.len() && b[j] != b'"' {
                    j += if b[j] == b'\\' { 2 } else { 1 };
                }
                let end = j.min(b.len());
                blank(&mut skeleton[i + 1..end]);
                i = end + 1;
            }
            b'\'' => {
                if b.get(i + 1) == Some(&b'\\') {
                    let end =
                        b[i + 3..].iter().position(|&c| c == b'\'').map_or(b.len(), |p| i + 3 + p);
                    blank(&mut skeleton[i + 1..end]);
                    i = end + 1;
                } else {
                    let len = src[i + 1..].chars().next().map_or(1, char::len_utf8);
                    if b.get(i + 1 + len) == Some(&b'\'') {
                        blank(&mut skeleton[i + 1..i + 1 + len]);
                        i += 2 + len;
                    } else {
                        i += 1; // a lifetime or label
                    }
                }
            }
            _ => i += 1,
        }
    }
    Views {
        code: String::from_utf8(code).expect("blanking whole ASCII-delimited spans keeps UTF-8"),
        skeleton: String::from_utf8(skeleton).expect("blanking keeps UTF-8"),
    }
}

/// Whitespace runs collapsed to one space; `map[k]` is the source offset of output byte `k`.
fn normalized(text: &str) -> (String, Vec<usize>) {
    let (mut out, mut map, mut space) = (String::new(), Vec::new(), false);
    for (i, ch) in text.char_indices() {
        if ch.is_whitespace() {
            space = !out.is_empty();
            continue;
        }
        if space {
            out.push(' ');
            map.push(i);
            space = false;
        }
        out.push(ch);
        map.extend(std::iter::repeat_n(i, ch.len_utf8()));
    }
    (out, map)
}

fn norm(text: &str) -> String {
    normalized(text).0
}

/// The source offset of the ONE whitespace-insensitive occurrence of `pattern` in `text`.
fn unique(text: &str, pattern: &str, what: &str) -> Result<usize, String> {
    let (flat, map) = normalized(text);
    let pattern = norm(pattern);
    let hits: Vec<usize> = flat.match_indices(&pattern).map(|(at, _)| map[at]).collect();
    match hits.as_slice() {
        [one] => Ok(*one),
        _ => Err(format!("{what}: expected exactly one `{pattern}`, found {}", hits.len())),
    }
}

/// The offset just past the `}` that closes the first `{` at or after `from` (skeleton offsets).
fn block_end(skeleton: &str, from: usize) -> Result<usize, String> {
    let open = from + skeleton[from..].find('{').ok_or("no `{` after the anchor")?;
    let mut depth = 0usize;
    for (k, byte) in skeleton.as_bytes()[open..].iter().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(open + k + 1);
                }
            }
            _ => {}
        }
    }
    Err("unbalanced braces after the anchor".to_string())
}

const BYTE_GATE: &str = "fn enum_flip_direct_only(module: &trust_ir::Module, eid: trust_ir::EnumId) -> bool { match module.enum_def(eid) { None => false, Some(def) => match &def.layout { None => true, Some(desc) => { matches!(desc.encoding, trust_ir::ty::EnumTagEncoding::Direct { .. }) } }, } }";

const LOGICAL_GATE: &str = "fn enum_flip_logical_read_ok(module: &trust_ir::Module, eid: trust_ir::EnumId) -> bool { match module.enum_def(eid) { None => false, Some(def) => match &def.layout { None => true, Some(desc) => matches!( desc.encoding, trust_ir::ty::EnumTagEncoding::Direct { .. } | trust_ir::ty::EnumTagEncoding::Niche { .. } ), }, } }";

const ADMIT_ARM: &str = "Ty::Enum(eid) if matches!(built_ret_ty.kind(), ty::Adt(adt, _) if adt.is_enum() && !adt.variants().is_empty() && adt.variants().iter().all(|v| v.fields.len() <= 1)) && !built_ret_ty.has_non_region_param() && !built_ret_ty.has_non_region_infer() && !crate::needs_drop_unrevealed( tcx, built_ret_ty, ty::TypingEnv::fully_monomorphized(), ) && enum_flip_direct_only(module, *eid) => { built_ret_ty }";

const REFUSAL_ARM_OPENER: &str =
    "Ty::Enum(eid) => { let te = ty::TypingEnv::fully_monomorphized();";

const REFUSAL_ARM_EXIT: &str = r#"return unsup(format!("enum return type {}", why.join("; "))); }"#;

const REASON_MATCH: &str = r#"let enc = match desc.encoding { trust_ir::ty::EnumTagEncoding::Direct { .. } => None, trust_ir::ty::EnumTagEncoding::Niche { .. } => { Some("Niche") } trust_ir::ty::EnumTagEncoding::Untagged => { Some("Untagged") } trust_ir::ty::EnumTagEncoding::SingleInhabited { .. } => { Some("SingleInhabited") } };"#;

/// The source span `[start, end)` of `fn <name>` — exactly one definition — through its body.
fn fn_span(v: &Views, name: &str, what: &str) -> Result<(usize, usize), String> {
    let start = unique(&v.skeleton, &format!("fn {name}("), what)?;
    Ok((start, block_end(&v.skeleton, start)?))
}

fn byte_gate(src: &str) -> Result<(), String> {
    let v = views(src);
    let (start, end) = fn_span(&v, "enum_flip_direct_only", "byte gate")?;
    let got = norm(&v.code[start..end]);
    if got != BYTE_GATE {
        return Err(format!("byte gate is no longer the Direct-only allow-list:\n  {got}"));
    }
    Ok(())
}

fn logical_gate(src: &str) -> Result<(), String> {
    let v = views(src);
    let (start, end) = fn_span(&v, "enum_flip_logical_read_ok", "logical-read gate")?;
    let got = norm(&v.code[start..end]);
    if got != LOGICAL_GATE {
        return Err(format!(
            "logical-read gate is no longer the Direct|Niche allow-list:\n  {got}"
        ));
    }
    Ok(())
}

/// The enum-return arms: `[admit_start, refusal_start)` is the admit arm, and
/// `[refusal_start, refusal_end)` the refusal arm.
fn return_arms(v: &Views) -> Result<(usize, usize, usize), String> {
    let admit = unique(&v.code, "Ty::Enum(eid) if matches!(built_ret_ty.kind(),", "admit arm")?;
    let refusal = unique(&v.code, REFUSAL_ARM_OPENER, "refusal arm")?;
    if refusal < admit {
        return Err("the refusal arm no longer follows the admit arm".to_string());
    }
    Ok((admit, refusal, block_end(&v.skeleton, refusal)?))
}

fn refusal_arm(src: &str) -> Result<(), String> {
    let v = views(src);
    let (admit, refusal, end) = return_arms(&v)?;
    let got = norm(&v.code[admit..refusal]);
    if got != ADMIT_ARM {
        return Err(format!("the enum-return admit arm changed:\n  {got}"));
    }
    let arm = norm(&v.code[refusal..end]);
    if !arm.ends_with(REFUSAL_ARM_EXIT) {
        return Err(format!("the refusal arm no longer ends in its unsup return:\n  {arm}"));
    }
    // Counted in the skeleton, so the `return` inside the message string is not a `return`.
    let skeleton = norm(&v.skeleton[refusal..end]);
    let returns = skeleton
        .match_indices("return")
        .filter(|(at, _)| {
            let before = skeleton[..*at].bytes().last();
            let after = skeleton.as_bytes().get(at + "return".len()).copied();
            !before.is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_')
                && !after.is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_')
        })
        .count();
    if returns != 1 {
        return Err(format!("the refusal arm has {returns} `return`s; its only exit is unsup"));
    }
    let reason = unique(&v.code, "let enc = match desc.encoding {", "reason match")?;
    if !(refusal..end).contains(&reason) {
        return Err("the reason match left the refusal arm".to_string());
    }
    let reason_end = block_end(&v.skeleton, reason)?;
    let got = norm(&v.code[reason..=reason_end]);
    if got != REASON_MATCH {
        return Err(format!(
            "the reason match is no longer the exhaustive four-arm match:\n  {got}"
        ));
    }
    Ok(())
}

/// Every read of an enum layout descriptor or its encoding, and every mention of
/// `SingleInhabited`, in the shim's code (comments and string contents excluded).
fn descriptor_census(src: &str) -> Result<(), String> {
    let v = views(src);
    let regions = [
        fn_span(&v, "enum_flip_direct_only", "byte gate")?,
        fn_span(&v, "enum_flip_logical_read_ok", "logical-read gate")?,
        {
            let (_, refusal, end) = return_arms(&v)?;
            (refusal, end)
        },
    ];
    // A whole token: no identifier byte glued to an identifier-edged end of the needle.
    let ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let field_reads = |needle: &str| -> Vec<usize> {
        let (first, last) = (needle.as_bytes()[0], needle.as_bytes()[needle.len() - 1]);
        let bytes = v.skeleton.as_bytes();
        v.skeleton
            .match_indices(needle)
            .filter(|(at, _)| {
                !(ident(first) && *at > 0 && ident(bytes[at - 1]))
                    && !(ident(last) && bytes.get(at + needle.len()).is_some_and(|&c| ident(c)))
            })
            .map(|(at, _)| at)
            .collect()
    };
    for (needle, expected, per_region) in [
        (".layout", 3, [1, 1, 1]),
        (".encoding", 3, [1, 1, 1]),
        ("enum_def(", 3, [1, 1, 1]),
        ("EnumTagEncoding", 7, [1, 2, 4]),
        ("SingleInhabited", 1, [0, 0, 1]),
    ] {
        let hits = field_reads(needle);
        if hits.len() != expected {
            return Err(format!(
                "`{needle}` occurs {} times in the shim's code, not {expected}",
                hits.len()
            ));
        }
        for (k, &(start, end)) in regions.iter().enumerate() {
            let inside = hits.iter().filter(|at| (start..end).contains(at)).count();
            if inside != per_region[k] {
                return Err(format!(
                    "`{needle}`: {inside} occurrence(s) in gate region {k}, expected {}",
                    per_region[k]
                ));
            }
        }
    }
    for banned in ["EnumLayoutDescriptor", "EnumByteView"] {
        if v.skeleton.contains(banned) {
            return Err(format!(
                "the shim now names `{banned}`: a descriptor read outside the gates"
            ));
        }
    }
    Ok(())
}

#[test]
fn the_byte_gate_admits_only_direct_tagged_descriptors() {
    byte_gate(&shim_source()).unwrap();
}

#[test]
fn the_logical_read_gate_admits_only_direct_and_niche_descriptors() {
    logical_gate(&shim_source()).unwrap();
}

#[test]
fn single_inhabited_reaches_only_the_exhaustive_reasons_of_the_enum_return_refusal() {
    refusal_arm(&shim_source()).unwrap();
}

#[test]
fn the_shim_reads_enum_layout_descriptors_only_in_its_three_gates() {
    descriptor_census(&shim_source()).unwrap();
}

/// The mutation proof: every check above must fail on a widening of its own part of the
/// claim, and none may fail on a comment or a string that merely names the encoding.
#[test]
fn every_pin_fails_on_its_own_mutant() {
    let src = shim_source();
    let mutate = |from: &str, to: &str| -> String {
        assert_eq!(src.matches(from).count(), 1, "mutant anchor must be unique: {from}");
        src.replacen(from, to, 1)
    };
    type Check = fn(&str) -> Result<(), String>;
    let all: [(&str, Check); 4] = [
        ("byte gate", byte_gate),
        ("logical-read gate", logical_gate),
        ("refusal arm", refusal_arm),
        ("descriptor census", descriptor_census),
    ];

    let byte_widened = mutate(
        "matches!(desc.encoding, trust_ir::ty::EnumTagEncoding::Direct { .. })",
        "matches!(desc.encoding, trust_ir::ty::EnumTagEncoding::Direct { .. } \
         | trust_ir::ty::EnumTagEncoding::SingleInhabited { .. })",
    );
    let logical_widened = mutate(
        "| trust_ir::ty::EnumTagEncoding::Niche { .. }\n",
        "| trust_ir::ty::EnumTagEncoding::Niche { .. }\n\
         | trust_ir::ty::EnumTagEncoding::SingleInhabited { .. }\n",
    );
    let early_admit = mutate(
        "                Ty::Enum(eid) => {\n                    let te = ty::TypingEnv::fully_monomorphized();",
        "                Ty::Enum(eid) => {\n                    let te = ty::TypingEnv::fully_monomorphized();\n                    if why_not_single(module, *eid) { return Ok(()); }",
    );
    let wildcard = mutate(
        "Some(\"SingleInhabited\")\n                                            }\n",
        "Some(\"SingleInhabited\")\n                                            }\n                                            _ => None,\n",
    );
    let stray_read = format!(
        "{src}\nfn stray(m: &trust_ir::Module, e: trust_ir::EnumId) -> bool {{ \
         m.enum_def(e).is_some_and(|d| d.layout.is_some()) }}\n"
    );
    for (name, mutant, must_fail) in [
        ("byte gate widened", &byte_widened, &["byte gate", "descriptor census"][..]),
        ("logical gate widened", &logical_widened, &["logical-read gate", "descriptor census"][..]),
        ("early return in the refusal arm", &early_admit, &["refusal arm"][..]),
        ("wildcard reason arm", &wildcard, &["refusal arm"][..]),
        ("descriptor read outside the gates", &stray_read, &["descriptor census"][..]),
    ] {
        for (check, run) in all {
            let failed = run(mutant).is_err();
            assert_eq!(
                failed,
                must_fail.contains(&check),
                "mutant `{name}`: the {check} check {}",
                if failed { "failed but should not have" } else { "did not catch it" }
            );
        }
    }

    // Controls: naming the encoding in a comment or a string is not a read and not a widening.
    let named = format!(
        "{src}\n// SingleInhabited, def.layout and desc.encoding, in a comment\n\
         const NAMED: &str = \"SingleInhabited def.layout desc.encoding enum_def(\";\n"
    );
    for (check, run) in all {
        assert!(run(&named).is_ok(), "control: the {check} check fired on a comment or a string");
    }
}
