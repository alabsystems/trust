// trust-js-certify-bridge: TrustJS M3 D2 — the first kernel-certified JS builtins.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

//! Bridge pure, finite-table-shaped JavaScript builtins from the tier-0
//! interpreter, through the [`trust_certify::finite_dfa`] finite-table lane, to
//! Clean-kernel [`trust_ir::ProofEvidence::CleanCic`] receipts. This is the
//! first place *JS builtins* produce *Clean kernel proofs*.
//!
//! Certified builtins (each over the ASCII domain, code points `0..=127`):
//!
//! * `String.prototype.toLowerCase` — [`certify_tolowercase_ascii`]
//! * `String.prototype.toUpperCase` — [`certify_touppercase_ascii`]
//! * `String.prototype.trim`'s ASCII whitespace/line-terminator predicate —
//!   [`certify_whitespace_ascii`] (a `Byte → Bool` class test, encoded `0/1`)
//! * the ECMA-262 §19.2.6 URI-Decode ASCII hex-digit value —
//!   [`certify_hexval_ascii`] (a `Byte → Nat` table, `hex_val`, with non-digits
//!   encoded as the out-of-band sentinel `16`)
//! * the ECMA-262 §19.2.6.4 `encodeURIComponent` unreserved-character predicate —
//!   [`certify_encuri_unreserved_ascii`] (a `Byte → Bool` set-membership test —
//!   pass through verbatim vs `%`-escape — encoded `0/1`)
//!
//! # The honesty boundary (spec surface §9 item 5 — NEVER crossed)
//!
//! The claim minted for each builtin is EXACTLY:
//!
//! > **the interpreter's builtin refines OUR TRANSCRIPTION of the ECMA-262
//! > table, kernel-checked.**
//!
//! It is NOT "refines ECMA-262". A pinned, checksummed transcription is our
//! *fallible reading* of the standard; the kernel checks the interpreter's
//! *extracted* behaviour against THAT table, cell by cell. An
//! independently-governed spec extractor does not exist (that is RESEARCH, out
//! of scope), so this bridge never asserts refinement to the standard itself.
//! [`ASSURANCE_TIER`] states the tier verbatim and is embedded in every emitted
//! certificate.
//!
//! # What is proved, mechanically (per builtin)
//!
//! Over the finite domain `Ascii128` (the 128 code points `0..=127`):
//!
//! * `interp_fn : Ascii128 → Nat` — the interpreter's builtin behaviour,
//!   EXTRACTED by running a tiny JS snippet through the real tier-0 interpreter
//!   for each code point (so extraction exercises the deployed dispatch path);
//! * `spec_fn : Ascii128 → Nat` — the pinned transcription table (a `Byte→Byte`
//!   code-point map, or a `Byte→Bool` class predicate encoded as `0/1`);
//! * the kernel checks `∀ (c : Ascii128), Eq Nat (interp_fn c) (spec_fn c)` via
//!   an explicit `Ascii128.casesOn` case analysis (one `Eq.refl` per code
//!   point). If interpreter and transcription disagree at ANY cell, the kernel
//!   re-check fails closed — no certificate is minted. A disagreement is a
//!   genuine interpreter bug OR a transcription error; the honest response is to
//!   fix the correct side, never to doctor the table.

#![forbid(unsafe_code)]

use std::path::PathBuf;

use clean_auto::bridge::ay_contract::serialize_term;
use clean_kernel::name::Name;
use clean_kernel::{Constructor, Expr, InductiveDecl, InductiveType};
use sha2::{Digest, Sha256};
use trust_certify::finite_dfa::{
    certify_finite_sim, enum_cases_refl_proof, enum_transition_body, recheck_finite_sim,
    FiniteSimSpec, SimFlavor,
};
use trust_ir::ProofEvidence;

/// Size of the certified finite domain: the 128 ASCII code points `0..=127`.
pub const ASCII_DOMAIN: usize = 128;

/// The assurance tier — stated **verbatim** (spec surface §9 item 5). Embedded
/// in every emitted certificate; MUST NOT be softened into a claim of
/// refinement to ECMA-262 itself.
pub const ASSURANCE_TIER: &str = "the interpreter's builtin refines OUR TRANSCRIPTION of the ECMA-262 table, kernel-checked (not refinement to an independent extractor)";

// ════════════════════════════════════════════════════════════════════════════
// Generic kernel-certification core (shared by every builtin)
// ════════════════════════════════════════════════════════════════════════════

/// Per-builtin identity/metadata folded into the emitted certificate.
#[derive(Debug, Clone)]
pub struct BuiltinMeta {
    /// Human-readable builtin name + domain.
    pub builtin: &'static str,
    /// Stable obligation label (folded into the Clean-kernel lineage digest).
    pub label: &'static str,
    /// Human-readable statement of the kernel goal.
    pub goal: &'static str,
    /// The codomain interpretation ("code point (Nat)" or "Bool encoded 0/1").
    pub codomain: &'static str,
    /// The pinned SHA-256 (lower-hex) of the transcription table.
    pub transcription_sha256: &'static str,
    /// The §9-item-5 honesty note recorded with the transcription.
    pub honesty_note: &'static str,
    /// Committed artifact filename under `certificates/`.
    pub cert_filename: &'static str,
}

/// The finite domain inductive `Ascii128` with 128 nullary constructors
/// `Ascii128.cp000 .. Ascii128.cp127` (one per ASCII code point). This is the
/// nullary-enum shape the [`SimFlavor::EnumCases`] lane requires.
#[must_use]
pub fn ascii_domain() -> InductiveDecl {
    let dom = Name::from_string("Ascii128");
    let dom_ref = Expr::const_(dom.clone(), vec![]);
    let constructors = (0..ASCII_DOMAIN)
        .map(|i| Constructor {
            name: Name::from_string(&format!("Ascii128.cp{i:03}")),
            type_: dom_ref.clone(),
        })
        .collect();
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: dom,
            type_: Expr::type_(),
            constructors,
        }],
    }
}

/// Lower a `Byte → Nat` table to per-constructor `Nat` cell literals.
fn table_cells(table: &[u8; ASCII_DOMAIN]) -> Vec<Expr> {
    table.iter().map(|&b| Expr::nat_lit(u64::from(b))).collect()
}

/// Lower-hex SHA-256 of a raw 128-cell table.
#[must_use]
pub fn table_checksum(table: &[u8; ASCII_DOMAIN]) -> String {
    to_hex(&Sha256::digest(table))
}

/// A certified builtin: the kernel receipt plus everything needed to re-check it
/// and to emit its honest certificate.
pub struct CertifiedBuiltin {
    /// Builtin identity/metadata.
    pub meta: BuiltinMeta,
    /// The kernel-checked `ProofEvidence::CleanCic` receipt.
    pub evidence: ProofEvidence,
    /// The finite-simulation spec the receipt is evidence for.
    pub spec: FiniteSimSpec,
    /// The interpreter's extracted output table (128 cells).
    pub extracted: [u8; ASCII_DOMAIN],
    /// The pinned transcription table the interpreter was checked against.
    pub transcription: [u8; ASCII_DOMAIN],
}

impl CertifiedBuiltin {
    /// Independently re-check the minted receipt against the same spec through
    /// the clean kernel (the check an external consumer runs).
    #[must_use]
    pub fn recheck(&self) -> bool {
        let ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            ..
        } = &self.evidence
        else {
            return false;
        };
        recheck_finite_sim(&self.spec, term, context, lineage)
    }

    /// Serialize into a committed [`BuiltinCertificate`].
    #[must_use]
    pub fn to_certificate(&self) -> BuiltinCertificate {
        let ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            ..
        } = &self.evidence
        else {
            unreachable!("CertifiedBuiltin always carries a CleanCic receipt");
        };
        let lineage_hex = to_hex(&lineage.bytes);
        let algorithm = format!("{:?}", lineage.algorithm);
        BuiltinCertificate {
            schema: "trust-js-certify-bridge.cert.v1".to_string(),
            builtin: self.meta.builtin.to_string(),
            assurance_tier: ASSURANCE_TIER.to_string(),
            honesty_note: self.meta.honesty_note.to_string(),
            domain: "ASCII code points 0..=127 (Ascii128, 128 nullary constructors)".to_string(),
            codomain: self.meta.codomain.to_string(),
            transcription_sha256: table_checksum(&self.transcription),
            obligation: CertObligation {
                label: self.meta.label.to_string(),
                goal: self.meta.goal.to_string(),
                lineage_sha256: lineage_hex.clone(),
            },
            kernel_check: CertKernelCheck {
                passed: self.recheck(),
                kernel: "clean-kernel TypeChecker::check_type (infer_only=false)".to_string(),
                tier: "Certified (de Bruijn / CleanCic)".to_string(),
            },
            clean_cic: CertCleanCic {
                term_sha256: to_hex(&Sha256::digest(term)),
                term_len: term.len(),
                context_sha256: to_hex(&Sha256::digest(context)),
                lineage_algorithm: algorithm,
                lineage_sha256: lineage_hex,
                term_hex: to_hex(term),
                context_hex: to_hex(context),
            },
            extracted_table: self.extracted.to_vec(),
            transcription_table: self.transcription.to_vec(),
        }
    }

    /// Serialize the certificate to pretty JSON.
    pub fn to_certificate_json(&self) -> Result<String, String> {
        serde_json::to_string_pretty(&self.to_certificate())
            .map_err(|e| format!("serialize certificate: {e}"))
    }

    /// Write the certificate to `<crate>/certificates/<meta.cert_filename>` and
    /// return the path.
    pub fn emit_certificate(&self) -> Result<PathBuf, String> {
        let json = self.to_certificate_json()?;
        let path: PathBuf = [env!("CARGO_MANIFEST_DIR"), "certificates", self.meta.cert_filename]
            .iter()
            .collect();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|e| format!("mkdir certificates: {e}"))?;
        }
        std::fs::write(&path, json.as_bytes()).map_err(|e| format!("write certificate: {e}"))?;
        Ok(path)
    }
}

/// Kernel-check that an EXTRACTED interpreter table equals a pinned
/// TRANSCRIPTION cell-by-cell, minting a `CleanCic` receipt.
///
/// Returns `Ok(None)` (fail-closed, honest) when the kernel re-check does not
/// pass — including the important case where interpreter and transcription
/// genuinely disagree at some cell (a real bug, not a receipt). Never fabricates.
fn certify_ascii_table(
    meta: BuiltinMeta,
    extracted: [u8; ASCII_DOMAIN],
    transcription: [u8; ASCII_DOMAIN],
) -> Result<Option<CertifiedBuiltin>, String> {
    let domain = ascii_domain();

    // impl_def from the EXTRACTED interpreter behaviour; spec_def from the
    // pinned TRANSCRIPTION — two independent inputs. The kernel is the sole
    // arbiter of whether they agree at every cell.
    let impl_def = enum_transition_body(&domain, &table_cells(&extracted))
        .ok_or("failed to build interp transition body")?;
    let spec_def = enum_transition_body(&domain, &table_cells(&transcription))
        .ok_or("failed to build transcription transition body")?;

    // The casesOn refinement proof claims the transcription value as the common
    // cell value; it only type-checks if the interpreter reduces to that same
    // value at that constructor.
    let proof = enum_cases_refl_proof(&domain, &table_cells(&transcription))
        .ok_or("failed to build casesOn refinement proof")?;
    let term_bytes = serialize_term(&proof).map_err(|e| format!("serialize proof term: {e:?}"))?;

    let spec = FiniteSimSpec {
        label: meta.label.to_string(),
        flavor: SimFlavor::EnumCases {
            domain,
            impl_def,
            spec_def,
        },
    };

    match certify_finite_sim(&spec, &term_bytes) {
        Some(evidence) => Ok(Some(CertifiedBuiltin {
            meta,
            evidence,
            spec,
            extracted,
            transcription,
        })),
        None => Ok(None),
    }
}

/// Generic interpreter extractor: evaluate `body_for(i)` for each code point `i`
/// in `0..128` with the completion witness ON, read the numeric completion
/// value, and `map` it to the cell byte. Fail-closed on any refusal, non-normal
/// completion, or non-Number projection.
fn extract_num_table<F, M>(body_for: F, map: M) -> Result<[u8; ASCII_DOMAIN], String>
where
    F: Fn(usize) -> String,
    M: Fn(usize, u32) -> Result<u8, String>,
{
    use trust_js_interp::{evaluate_case_opts, InterpOutcome};
    use trust_js_trace::{Completion, ProjectedValue};

    let mut table = [0u8; ASCII_DOMAIN];
    for (i, slot) in table.iter_mut().enumerate() {
        let body = body_for(i);
        let outcome = evaluate_case_opts(&[], &body, false, true);
        let trace = match outcome {
            InterpOutcome::Trace(t) => t,
            InterpOutcome::NoCoverage { reason } => {
                return Err(format!("interp refused at code point {i}: {reason}"));
            }
        };
        let value = match trace.completion {
            Completion::Normal { v: Some(v) } => v,
            other => {
                return Err(format!("code point {i}: non-normal/absent completion: {other:?}"));
            }
        };
        let ProjectedValue::Num { v } = value else {
            return Err(format!("code point {i}: completion is not a Number: {value:?}"));
        };
        let raw: u32 = v
            .parse()
            .map_err(|e| format!("code point {i}: unparsable Number {v:?}: {e}"))?;
        *slot = map(i, raw)?;
    }
    Ok(table)
}

/// Map a `charCodeAt`-style numeric completion to an ASCII output code point.
fn map_codepoint(i: usize, out: u32) -> Result<u8, String> {
    if out < ASCII_DOMAIN as u32 {
        Ok(out as u8)
    } else {
        Err(format!("code point {i}: interp produced out-of-ASCII output {out} (case data leaked)"))
    }
}

/// Map a `String.prototype.trim().length` completion to a `0/1` whitespace
/// predicate: a single-char string trims to length 0 iff the char is trimmable
/// whitespace.
fn map_trim_predicate(_i: usize, trimmed_len: u32) -> Result<u8, String> {
    Ok(u8::from(trimmed_len == 0))
}

/// Map a `0/1` boolean-predicate completion to its cell byte. The JS probe
/// already reduces the pass-through/escape decision to `1`/`0`; anything else is
/// a leak and fails closed.
fn map_bool_predicate(i: usize, v: u32) -> Result<u8, String> {
    match v {
        0 | 1 => Ok(v as u8),
        _ => Err(format!("code point {i}: predicate produced non-boolean value {v}")),
    }
}

/// Map a `decodeURIComponent('%0'+c).charCodeAt(0)` completion to a hex-digit
/// value cell. A valid HexDigit yields its value `0..=15`; a non-HexDigit throws
/// URIError in the interpreter, caught in JS to the out-of-band sentinel
/// [`HEXVAL_NOT_A_DIGIT`] (`16`), which is disjoint from every real value so it
/// can never mask a wrong cell.
fn map_hexval(i: usize, out: u32) -> Result<u8, String> {
    if out <= u32::from(HEXVAL_NOT_A_DIGIT) {
        Ok(out as u8)
    } else {
        Err(format!("code point {i}: interp produced out-of-range hex value {out}"))
    }
}

/// Run the SAME sweep through the Node reference engine and return its 128-cell
/// table. `cell_expr` is a JS expression over the loop variable `i`. Fail-closed
/// on any failure to launch Node or parse its output.
fn node_table(cell_expr: &str) -> Result<[u8; ASCII_DOMAIN], String> {
    let script = format!(
        "console.log(Array.from({{length:128}},function(_,i){{return ({cell_expr});}}).join(','))"
    );
    let mut last_err = String::new();
    for bin in node_candidates() {
        match std::process::Command::new(&bin).arg("-e").arg(&script).output() {
            Ok(out) if out.status.success() => {
                let text = String::from_utf8_lossy(&out.stdout);
                return parse_csv_table(text.trim(), "node", &bin);
            }
            Ok(out) => {
                last_err = format!(
                    "{bin} exited {:?}: {}",
                    out.status.code(),
                    String::from_utf8_lossy(&out.stderr).trim()
                );
            }
            Err(e) => last_err = format!("spawn {bin}: {e}"),
        }
    }
    Err(format!("no working node binary ({last_err})"))
}

fn node_candidates() -> Vec<String> {
    let mut c = Vec::new();
    if let Ok(home) = std::env::var("HOME") {
        c.push(format!("{home}/.local/opt/node-v24.5.0/bin/node"));
    }
    c.push("node".to_string());
    c
}

fn parse_csv_table(text: &str, engine: &str, bin: &str) -> Result<[u8; ASCII_DOMAIN], String> {
    let parts: Vec<&str> = text.split(',').collect();
    if parts.len() != ASCII_DOMAIN {
        return Err(format!("{engine} ({bin}) produced {} cells, want {ASCII_DOMAIN}", parts.len()));
    }
    let mut table = [0u8; ASCII_DOMAIN];
    for (i, (p, slot)) in parts.iter().zip(table.iter_mut()).enumerate() {
        let v: u32 = p
            .trim()
            .parse()
            .map_err(|e| format!("{engine} cell {i}: unparsable {p:?}: {e}"))?;
        if v >= ASCII_DOMAIN as u32 {
            return Err(format!("{engine} cell {i}: out-of-ASCII output {v}"));
        }
        *slot = v as u8;
    }
    Ok(table)
}

// ════════════════════════════════════════════════════════════════════════════
// Builtin 1 — String.prototype.toLowerCase (ASCII)
// ════════════════════════════════════════════════════════════════════════════

/// The builtin certified first (kept for API stability).
pub const BUILTIN: &str = "String.prototype.toLowerCase (ASCII domain, code points 0..=127)";

/// A stable label for the toLowerCase obligation.
pub const OBLIGATION_LABEL: &str = "trust-js.String.prototype.toLowerCase.ascii-0-127";

/// The §9-item-5 honesty note for toLowerCase.
pub const HONESTY_NOTE: &str = "This table is OUR TRANSCRIPTION of the ECMA-262 String.prototype.toLowerCase ASCII mapping, not the output of an independently-governed spec extractor. The kernel checks the interpreter's extracted behaviour against THIS table; it does not check the table against the standard.";

/// The pinned SHA-256 checksum of [`TOLOWER_ASCII_TRANSCRIPTION`] (lower-hex).
pub const TRANSCRIPTION_SHA256: &str =
    "fc5b9b2c32b0ecc0354c66f03e60790599a8fbae3511b2b60b2c0f7f27b6ceae";

/// OUR TRANSCRIPTION of ECMA-262 `String.prototype.toLowerCase` over the ASCII
/// range: `A`–`Z` (`0x41`–`0x5A`) map to `a`–`z` (`+0x20`); every other ASCII
/// code point maps to itself. Written as the explicit range rule (not via Rust's
/// `to_ascii_lowercase`), so it is an *independent* re-expression of the spec.
pub const TOLOWER_ASCII_TRANSCRIPTION: [u8; ASCII_DOMAIN] = {
    let mut t = [0u8; ASCII_DOMAIN];
    let mut i = 0usize;
    while i < ASCII_DOMAIN {
        let c = i as u8;
        t[i] = if c >= 0x41 && c <= 0x5A { c + 0x20 } else { c };
        i += 1;
    }
    t
};

fn tolower_meta() -> BuiltinMeta {
    BuiltinMeta {
        builtin: BUILTIN,
        label: OBLIGATION_LABEL,
        goal: "forall (c : Ascii128), Eq Nat (interp_lower c) (spec_lower c)",
        codomain: "output code point (Nat, 0..=127)",
        transcription_sha256: TRANSCRIPTION_SHA256,
        honesty_note: HONESTY_NOTE,
        cert_filename: "toLowerCase-ascii.cert.json",
    }
}

/// Extract the interpreter's `toLowerCase` output code point for each ASCII input.
pub fn extract_interp_lowercase_table() -> Result<[u8; ASCII_DOMAIN], String> {
    extract_num_table(
        |i| format!("String.fromCharCode({i}).toLowerCase().charCodeAt(0)"),
        map_codepoint,
    )
}

/// Node's `toLowerCase` table over the ASCII domain.
pub fn node_lowercase_table() -> Result<[u8; ASCII_DOMAIN], String> {
    node_table("String.fromCharCode(i).toLowerCase().charCodeAt(0)")
}

/// Extract + KERNEL-CHECK `String.prototype.toLowerCase` over ASCII.
pub fn certify_tolowercase_ascii() -> Result<Option<CertifiedBuiltin>, String> {
    let extracted = extract_interp_lowercase_table()?;
    certify_ascii_table(tolower_meta(), extracted, TOLOWER_ASCII_TRANSCRIPTION)
}

/// Lower-hex SHA-256 of the toLowerCase transcription (kept for API stability).
#[must_use]
pub fn transcription_checksum() -> String {
    table_checksum(&TOLOWER_ASCII_TRANSCRIPTION)
}

/// Does the toLowerCase transcription still hash to its pinned checksum?
#[must_use]
pub fn transcription_checksum_matches() -> bool {
    transcription_checksum() == TRANSCRIPTION_SHA256
}

// ════════════════════════════════════════════════════════════════════════════
// Builtin 2 — String.prototype.toUpperCase (ASCII)
// ════════════════════════════════════════════════════════════════════════════

/// A stable label for the toUpperCase obligation.
pub const TOUPPER_OBLIGATION_LABEL: &str = "trust-js.String.prototype.toUpperCase.ascii-0-127";

/// The §9-item-5 honesty note for toUpperCase.
pub const TOUPPER_HONESTY_NOTE: &str = "This table is OUR TRANSCRIPTION of the ECMA-262 String.prototype.toUpperCase ASCII mapping, not the output of an independently-governed spec extractor. The kernel checks the interpreter's extracted behaviour against THIS table; it does not check the table against the standard.";

/// The pinned SHA-256 checksum of [`TOUPPER_ASCII_TRANSCRIPTION`] (lower-hex).
pub const TOUPPER_TRANSCRIPTION_SHA256: &str =
    "cf4e4b49cfa6c92fdff0c21576b5983addce5ad87fa525e9609f679102e8107e";

/// OUR TRANSCRIPTION of ECMA-262 `String.prototype.toUpperCase` over the ASCII
/// range: `a`–`z` (`0x61`–`0x7A`) map to `A`–`Z` (`-0x20`); every other ASCII
/// code point maps to itself. Written as the explicit range rule.
pub const TOUPPER_ASCII_TRANSCRIPTION: [u8; ASCII_DOMAIN] = {
    let mut t = [0u8; ASCII_DOMAIN];
    let mut i = 0usize;
    while i < ASCII_DOMAIN {
        let c = i as u8;
        t[i] = if c >= 0x61 && c <= 0x7A { c - 0x20 } else { c };
        i += 1;
    }
    t
};

fn toupper_meta() -> BuiltinMeta {
    BuiltinMeta {
        builtin: "String.prototype.toUpperCase (ASCII domain, code points 0..=127)",
        label: TOUPPER_OBLIGATION_LABEL,
        goal: "forall (c : Ascii128), Eq Nat (interp_upper c) (spec_upper c)",
        codomain: "output code point (Nat, 0..=127)",
        transcription_sha256: TOUPPER_TRANSCRIPTION_SHA256,
        honesty_note: TOUPPER_HONESTY_NOTE,
        cert_filename: "toUpperCase-ascii.cert.json",
    }
}

/// Extract the interpreter's `toUpperCase` output code point for each ASCII input.
pub fn extract_interp_uppercase_table() -> Result<[u8; ASCII_DOMAIN], String> {
    extract_num_table(
        |i| format!("String.fromCharCode({i}).toUpperCase().charCodeAt(0)"),
        map_codepoint,
    )
}

/// Node's `toUpperCase` table over the ASCII domain.
pub fn node_uppercase_table() -> Result<[u8; ASCII_DOMAIN], String> {
    node_table("String.fromCharCode(i).toUpperCase().charCodeAt(0)")
}

/// Extract + KERNEL-CHECK `String.prototype.toUpperCase` over ASCII.
pub fn certify_touppercase_ascii() -> Result<Option<CertifiedBuiltin>, String> {
    let extracted = extract_interp_uppercase_table()?;
    certify_ascii_table(toupper_meta(), extracted, TOUPPER_ASCII_TRANSCRIPTION)
}

// ════════════════════════════════════════════════════════════════════════════
// Builtin 3 — String.prototype.trim's ASCII whitespace predicate (Byte -> Bool)
// ════════════════════════════════════════════════════════════════════════════
//
// A total `Byte -> Bool` class test, encoded as `Byte -> Nat` (0/1) so the SAME
// EnumCases `Eq Nat` obligation applies. The predicate is "does
// String.prototype.trim remove this single ASCII character?" — i.e. ECMA-262
// (WhiteSpace ∪ LineTerminator) ∩ ASCII = {0x09 TAB, 0x0A LF, 0x0B VT, 0x0C FF,
// 0x0D CR, 0x20 SP}. (0xA0 NBSP and the other Unicode WhiteSpace code points are
// > 127 and outside this domain.) Extraction reads `.trim().length` (0 => the
// char is whitespace); this is the predicate the interpreter genuinely computes
// in its trim path, and it cross-checks against Node's String.prototype.trim.

/// A stable label for the whitespace-predicate obligation.
pub const WHITESPACE_OBLIGATION_LABEL: &str =
    "trust-js.String.prototype.trim.ascii-whitespace-predicate.0-127";

/// The §9-item-5 honesty note for the whitespace predicate.
pub const WHITESPACE_HONESTY_NOTE: &str = "This table is OUR TRANSCRIPTION of the ECMA-262 (WhiteSpace + LineTerminator) set intersected with ASCII — the code points String.prototype.trim removes — encoded as a 0/1 predicate. It is not the output of an independently-governed spec extractor. The kernel checks the interpreter's extracted trim predicate against THIS table; it does not check the table against the standard.";

/// The pinned SHA-256 checksum of [`WHITESPACE_ASCII_TRANSCRIPTION`] (lower-hex).
pub const WHITESPACE_TRANSCRIPTION_SHA256: &str =
    "952076615aa14abfbdfc8cccee2dc160d467d893199291fac0e16cd2c96ed109";

/// OUR TRANSCRIPTION of the ASCII whitespace/line-terminator predicate removed
/// by `String.prototype.trim`: `1` for `{0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20}`,
/// `0` otherwise. Written as the explicit set-membership rule.
pub const WHITESPACE_ASCII_TRANSCRIPTION: [u8; ASCII_DOMAIN] = {
    let mut t = [0u8; ASCII_DOMAIN];
    let mut i = 0usize;
    while i < ASCII_DOMAIN {
        let c = i as u8;
        t[i] = if matches!(c, 0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20) { 1 } else { 0 };
        i += 1;
    }
    t
};

fn whitespace_meta() -> BuiltinMeta {
    BuiltinMeta {
        builtin:
            "String.prototype.trim ASCII whitespace predicate (Byte -> Bool, code points 0..=127)",
        label: WHITESPACE_OBLIGATION_LABEL,
        goal: "forall (c : Ascii128), Eq Nat (interp_is_ws c) (spec_is_ws c)  -- Bool encoded 0/1",
        codomain: "class predicate (Bool encoded as Nat 0/1)",
        transcription_sha256: WHITESPACE_TRANSCRIPTION_SHA256,
        honesty_note: WHITESPACE_HONESTY_NOTE,
        cert_filename: "trim-whitespace-ascii.cert.json",
    }
}

/// Extract the interpreter's trim-whitespace predicate (0/1) for each ASCII input.
pub fn extract_interp_whitespace_table() -> Result<[u8; ASCII_DOMAIN], String> {
    extract_num_table(
        |i| format!("String.fromCharCode({i}).trim().length"),
        map_trim_predicate,
    )
}

/// Node's trim-whitespace predicate table (0/1) over the ASCII domain.
pub fn node_whitespace_table() -> Result<[u8; ASCII_DOMAIN], String> {
    node_table("String.fromCharCode(i).trim().length===0?1:0")
}

/// Extract + KERNEL-CHECK the `String.prototype.trim` ASCII whitespace predicate.
pub fn certify_whitespace_ascii() -> Result<Option<CertifiedBuiltin>, String> {
    let extracted = extract_interp_whitespace_table()?;
    certify_ascii_table(whitespace_meta(), extracted, WHITESPACE_ASCII_TRANSCRIPTION)
}

// ════════════════════════════════════════════════════════════════════════════
// Builtin 4 — URI-decode ASCII hex-digit value (Byte -> Nat, sentinel encoded)
// ════════════════════════════════════════════════════════════════════════════
//
// The ECMA-262 URI Decode algorithm (§19.2.6, the `Decode` abstract operation)
// reads each `%XY` escape by taking the numeric *value* of two HexDigits. In the
// interpreter that value is `builtins_uri::hex_val` — a genuine pure
// `Byte -> Option<value>` table (`'0'..'9' -> 0..9`, `'A'..'F' -> 10..15`,
// `'a'..'f' -> 10..15`, else `None`), which we certify here.
//
// Extraction exercises the DEPLOYED `decodeURIComponent` path that calls
// `hex_val` directly: `decodeURIComponent('%0' + c)` decodes the two units
// `'0'` and `c`, i.e. the byte `(hex_val('0') << 4) | hex_val(c) = hex_val(c)`
// (0..=15, a single code unit), whose `.charCodeAt(0)` is exactly `hex_val(c)`.
// A non-HexDigit `c` makes `hex_val(c) = None`, so `decodeURIComponent` throws a
// URIError; JS `try/catch` maps that to the out-of-band sentinel
// [`HEXVAL_NOT_A_DIGIT`]. This is a total `Byte -> Nat` function encoding the
// partial `hex_val`: the interpreter never observably yields the sentinel for a
// real digit, so the sentinel cannot hide a wrong cell. Cross-checked against
// Node's `decodeURIComponent`.

/// Out-of-band "not a HexDigit" sentinel for the hex-value encoding. Chosen as
/// `16`, one past the largest real hex value `15`, so it is disjoint from every
/// genuine cell and stays inside the ASCII codomain (`< 128`).
pub const HEXVAL_NOT_A_DIGIT: u8 = 16;

/// A stable label for the hex-digit-value obligation.
pub const HEXVAL_OBLIGATION_LABEL: &str = "trust-js.URI.decode.ascii-hex-digit-value.0-127";

/// The §9-item-5 honesty note for the hex-digit-value table.
pub const HEXVAL_HONESTY_NOTE: &str = "This table is OUR TRANSCRIPTION of the ECMA-262 (§19.2.6 Decode) HexDigit value — the per-code-point value URI decoding assigns to a hex digit — with non-HexDigits encoded as the out-of-band sentinel 16. It is not the output of an independently-governed spec extractor. The kernel checks the interpreter's extracted decodeURIComponent hex-value behaviour against THIS table; it does not check the table against the standard.";

/// The pinned SHA-256 checksum of [`HEXVAL_ASCII_TRANSCRIPTION`] (lower-hex).
pub const HEXVAL_TRANSCRIPTION_SHA256: &str =
    "555c9860c906e932e3e10c2626eb8438af9754dfcbdaee82c30ce9ece80cb02c";

/// OUR TRANSCRIPTION of the ECMA-262 §19.2.6 URI-Decode HexDigit value over the
/// ASCII range: `'0'`–`'9'` (`0x30`–`0x39`) → `0`–`9`; `'A'`–`'F'`
/// (`0x41`–`0x46`) and `'a'`–`'f'` (`0x61`–`0x66`) → `10`–`15`; every other ASCII
/// code point is not a HexDigit and maps to the sentinel
/// [`HEXVAL_NOT_A_DIGIT`]. Written as the explicit range rule (not via Rust's
/// `to_digit`), so it is an *independent* re-expression of the spec.
pub const HEXVAL_ASCII_TRANSCRIPTION: [u8; ASCII_DOMAIN] = {
    let mut t = [HEXVAL_NOT_A_DIGIT; ASCII_DOMAIN];
    let mut i = 0usize;
    while i < ASCII_DOMAIN {
        let c = i as u8;
        if c >= 0x30 && c <= 0x39 {
            t[i] = c - 0x30;
        } else if c >= 0x41 && c <= 0x46 {
            t[i] = c - 0x41 + 10;
        } else if c >= 0x61 && c <= 0x66 {
            t[i] = c - 0x61 + 10;
        }
        i += 1;
    }
    t
};

fn hexval_meta() -> BuiltinMeta {
    BuiltinMeta {
        builtin: "URI-decode ASCII hex-digit value (Byte -> Nat, code points 0..=127)",
        label: HEXVAL_OBLIGATION_LABEL,
        goal: "forall (c : Ascii128), Eq Nat (interp_hexval c) (spec_hexval c)  -- non-digit = 16",
        codomain: "hex-digit value (Nat 0..=15; 16 = not a HexDigit)",
        transcription_sha256: HEXVAL_TRANSCRIPTION_SHA256,
        honesty_note: HEXVAL_HONESTY_NOTE,
        cert_filename: "uri-decode-hexval-ascii.cert.json",
    }
}

/// The single-percent-escape JS probe that isolates `hex_val(c)` through the
/// deployed `decodeURIComponent` path (used identically by interp and Node).
fn hexval_cell_expr(index_var: &str) -> String {
    format!(
        "(function(){{try{{return decodeURIComponent('%0'+String.fromCharCode({index_var})).charCodeAt(0);}}catch(e){{return {HEXVAL_NOT_A_DIGIT};}}}})()"
    )
}

/// Extract the interpreter's URI-decode hex-digit value for each ASCII input.
pub fn extract_interp_hexval_table() -> Result<[u8; ASCII_DOMAIN], String> {
    extract_num_table(|i| hexval_cell_expr(&i.to_string()), map_hexval)
}

/// Node's URI-decode hex-digit value table over the ASCII domain.
pub fn node_hexval_table() -> Result<[u8; ASCII_DOMAIN], String> {
    node_table(&hexval_cell_expr("i"))
}

/// Extract + KERNEL-CHECK the URI-decode ASCII hex-digit value function.
pub fn certify_hexval_ascii() -> Result<Option<CertifiedBuiltin>, String> {
    let extracted = extract_interp_hexval_table()?;
    certify_ascii_table(hexval_meta(), extracted, HEXVAL_ASCII_TRANSCRIPTION)
}

// ════════════════════════════════════════════════════════════════════════════
// Builtin 5 — encodeURIComponent unreserved-character predicate (Byte -> Bool)
// ════════════════════════════════════════════════════════════════════════════
//
// The ECMA-262 §19.2.6.4 `encodeURIComponent` Encode algorithm decides, per code
// point, whether the character passes through VERBATIM or is `%`-escaped. The
// pass-through set is `uriUnescaped = uriAlpha ∪ DecimalDigit ∪ uriMark`, i.e.
// exactly `A`–`Z`, `a`–`z`, `0`–`9`, and the marks `- _ . ! ~ * ' ( )`; every
// other code point is escaped.
//
// In the interpreter this decision is `builtins_uri::is_unescaped` — a genuine
// pure `u16 -> bool` set-membership test (a `matches!` over the code point,
// with NO surrogate/multi-byte state). For an ASCII input the deployed
// `encodeURIComponent` path (`realm.rs` global -> `dispatch_uri(true, true, ..)`
// -> `encode(&s, false)`) either pushes the unit verbatim (`is_unescaped` true,
// a 1-code-unit result) or emits `%XX` (a 3-code-unit result); the single ASCII
// byte never triggers the surrogate-pair or continuation-byte branches. So the
// per-code-point pass-through decision IS the pure predicate, reachable through
// the real interpreter.
//
// Extraction exercises that deployed path and reduces it to a boolean:
// `encodeURIComponent(String.fromCharCode(c)) === String.fromCharCode(c)` is
// `true` iff the interpreter passed the character through verbatim (unreserved),
// `false` iff it produced a `%XX` escape — mapped to `1`/`0`. Cross-checked
// against Node's `encodeURIComponent`.

/// A stable label for the encodeURIComponent unreserved-predicate obligation.
pub const ENCURI_UNRESERVED_OBLIGATION_LABEL: &str =
    "trust-js.encodeURIComponent.ascii-unreserved-predicate.0-127";

/// The §9-item-5 honesty note for the encodeURIComponent unreserved predicate.
pub const ENCURI_UNRESERVED_HONESTY_NOTE: &str = "This table is OUR TRANSCRIPTION of the ECMA-262 (§19.2.6.4 Encode) uriUnescaped set (uriAlpha + DecimalDigit + uriMark) intersected with ASCII — the code points encodeURIComponent passes through verbatim rather than %-escaping — encoded as a 0/1 predicate. It is not the output of an independently-governed spec extractor. The kernel checks the interpreter's extracted encodeURIComponent pass-through predicate against THIS table; it does not check the table against the standard.";

/// The pinned SHA-256 checksum of [`ENCURI_UNRESERVED_ASCII_TRANSCRIPTION`]
/// (lower-hex).
pub const ENCURI_UNRESERVED_TRANSCRIPTION_SHA256: &str =
    "2797c897f18fec2c1178c699331110eba920f0e7ee29d5c4b70ec5d09ccdacfb";

/// OUR TRANSCRIPTION of the ECMA-262 §19.2.6.4 `encodeURIComponent`
/// unreserved-character predicate over the ASCII range: `1` for the
/// `uriUnescaped` set — `A`–`Z` (`0x41`–`0x5A`), `a`–`z` (`0x61`–`0x7A`),
/// `0`–`9` (`0x30`–`0x39`), and the marks `- _ . ! ~ * ' ( )`
/// (`0x2D 0x5F 0x2E 0x21 0x7E 0x2A 0x27 0x28 0x29`) — and `0` for every other
/// ASCII code point (which `encodeURIComponent` `%`-escapes). Written as the
/// explicit set-membership rule (an *independent* re-expression of the spec, not
/// a call to the interpreter's own `is_unescaped`).
pub const ENCURI_UNRESERVED_ASCII_TRANSCRIPTION: [u8; ASCII_DOMAIN] = {
    let mut t = [0u8; ASCII_DOMAIN];
    let mut i = 0usize;
    while i < ASCII_DOMAIN {
        let c = i as u8;
        let unreserved = (c >= 0x41 && c <= 0x5A) // A-Z (uriAlpha upper)
            || (c >= 0x61 && c <= 0x7A) // a-z (uriAlpha lower)
            || (c >= 0x30 && c <= 0x39) // 0-9 (DecimalDigit)
            || matches!(c, 0x2D | 0x5F | 0x2E | 0x21 | 0x7E | 0x2A | 0x27 | 0x28 | 0x29); // uriMark: - _ . ! ~ * ' ( )
        t[i] = if unreserved { 1 } else { 0 };
        i += 1;
    }
    t
};

fn encuri_unreserved_meta() -> BuiltinMeta {
    BuiltinMeta {
        builtin:
            "encodeURIComponent unreserved-character predicate (Byte -> Bool, code points 0..=127)",
        label: ENCURI_UNRESERVED_OBLIGATION_LABEL,
        goal:
            "forall (c : Ascii128), Eq Nat (interp_is_unreserved c) (spec_is_unreserved c)  -- Bool encoded 0/1",
        codomain: "class predicate (Bool encoded as Nat 0/1)",
        transcription_sha256: ENCURI_UNRESERVED_TRANSCRIPTION_SHA256,
        honesty_note: ENCURI_UNRESERVED_HONESTY_NOTE,
        cert_filename: "encodeuricomponent-unreserved-ascii.cert.json",
    }
}

/// The JS probe isolating the pass-through/escape decision through the deployed
/// `encodeURIComponent` path (used identically by interp and Node): the encoded
/// single-char string equals the input char iff the code point is unreserved.
fn encuri_unreserved_cell_expr(index_var: &str) -> String {
    format!(
        "(function(){{var ch=String.fromCharCode({index_var});return encodeURIComponent(ch)===ch?1:0;}})()"
    )
}

/// Extract the interpreter's `encodeURIComponent` unreserved predicate (0/1) for
/// each ASCII input.
pub fn extract_interp_encuri_unreserved_table() -> Result<[u8; ASCII_DOMAIN], String> {
    extract_num_table(|i| encuri_unreserved_cell_expr(&i.to_string()), map_bool_predicate)
}

/// Node's `encodeURIComponent` unreserved predicate table (0/1) over the ASCII
/// domain.
pub fn node_encuri_unreserved_table() -> Result<[u8; ASCII_DOMAIN], String> {
    node_table(&encuri_unreserved_cell_expr("i"))
}

/// Extract + KERNEL-CHECK the `encodeURIComponent` ASCII unreserved-character
/// predicate.
pub fn certify_encuri_unreserved_ascii() -> Result<Option<CertifiedBuiltin>, String> {
    let extracted = extract_interp_encuri_unreserved_table()?;
    certify_ascii_table(encuri_unreserved_meta(), extracted, ENCURI_UNRESERVED_ASCII_TRANSCRIPTION)
}

// ════════════════════════════════════════════════════════════════════════════
// Certificate artifact schema
// ════════════════════════════════════════════════════════════════════════════

/// The committed certificate: the CleanCic receipt (term + context + lineage),
/// the obligation identity, the assurance-tier string, and the transcription
/// checksum — everything a consumer needs to re-check and read the trust boundary.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct BuiltinCertificate {
    pub schema: String,
    pub builtin: String,
    /// The §9-item-5 assurance tier, stated verbatim.
    pub assurance_tier: String,
    pub honesty_note: String,
    pub domain: String,
    pub codomain: String,
    pub transcription_sha256: String,
    pub obligation: CertObligation,
    pub kernel_check: CertKernelCheck,
    pub clean_cic: CertCleanCic,
    /// The interpreter's extracted outputs (128 cells).
    pub extracted_table: Vec<u8>,
    /// The pinned transcription outputs (128 cells).
    pub transcription_table: Vec<u8>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CertObligation {
    pub label: String,
    pub goal: String,
    /// Lower-hex of the Clean-kernel lineage digest binding this receipt to this
    /// obligation (spec + term). Equal to `clean_cic.lineage_sha256`.
    pub lineage_sha256: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CertKernelCheck {
    /// True iff the clean kernel accepted the proof term for the goal AND the
    /// serialized payload independently re-checks.
    pub passed: bool,
    pub kernel: String,
    pub tier: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CertCleanCic {
    pub term_sha256: String,
    pub term_len: usize,
    pub context_sha256: String,
    pub lineage_algorithm: String,
    pub lineage_sha256: String,
    /// The full serialized proof term (lower-hex), so the certificate is
    /// self-contained for an external kernel re-check.
    pub term_hex: String,
    /// The serialized (empty, closed) local context (lower-hex).
    pub context_hex: String,
}

// ── helpers ──────────────────────────────────────────────────────────────────

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
