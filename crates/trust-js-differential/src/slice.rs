// S0 slice selection over the pinned Test262 corpus — the byte-for-byte
// selection contract (M0). A test file is IN the S0 slice iff ALL of:
//   1. rel path (forward slashes) starts with test/language/ or test/built-ins/
//   2. and does NOT start with test/intl402/, test/staging/, test/annexB/,
//      or test/built-ins/Temporal/
//   3. filename ends .js and does NOT end _FIXTURE.js
//   4. frontmatter flags contain NONE of: async, module, CanBlockIsTrue,
//      CanBlockIsFalse
//   5. raw content does NOT contain the substring "$262."
//   6. frontmatter features contain NONE of: Atomics, SharedArrayBuffer,
//      Temporal, tail-call-optimization, IsHTMLDDA, cross-realm,
//      host-gc-required — and NO feature containing the substring "Intl"
//   7. frontmatter features contain NO proposal-stage feature, where the
//      proposal set is the corpus's own features.txt "## Proposed language
//      features" section (pin-derived, so the rule can never be tuned to
//      observed engine agreement)
//   8. frontmatter includes name NO harness file whose content contains
//      "$262." (e.g. detachArrayBuffer.js, atomicsHelper.js — running those
//      would test the harness stub, not the engines)
// The S0 list = all selected relative paths sorted bytewise ascending;
// list_sha256 = sha256 over UTF-8 concat of (path + "\n") in that order.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::Path;

use sha2::{Digest, Sha256};

use crate::frontmatter::parse_frontmatter;
use crate::model::{ExternalSliceManifest, SliceManifest, SLICE_SCHEMA};
use crate::util::{contains_subslice, today_utc, Finding};

pub const INCLUDE_PREFIXES: [&str; 2] = ["test/language/", "test/built-ins/"];
pub const EXCLUDE_PREFIXES: [&str; 4] =
    ["test/intl402/", "test/staging/", "test/annexB/", "test/built-ins/Temporal/"];
pub const EXCLUDE_FLAGS: [&str; 4] = ["async", "module", "CanBlockIsTrue", "CanBlockIsFalse"];
pub const EXCLUDE_FEATURES: [&str; 7] = [
    "Atomics",
    "SharedArrayBuffer",
    "Temporal",
    "tail-call-optimization",
    "IsHTMLDDA",
    "cross-realm",
    "host-gc-required",
];

/// Canonical S0 selection-rules text; its sha256 is the slice's rules digest.
pub const S0_RULES_TEXT: &str = "trust.js262.slice-rules.S0.v2\n\
include-prefix: test/language/ test/built-ins/\n\
exclude-prefix: test/intl402/ test/staging/ test/annexB/ test/built-ins/Temporal/\n\
suffix: .js not _FIXTURE.js\n\
exclude-flags: async module CanBlockIsTrue CanBlockIsFalse\n\
exclude-substring: $262.\n\
exclude-features: Atomics SharedArrayBuffer Temporal tail-call-optimization IsHTMLDDA cross-realm host-gc-required *Intl*\n\
exclude-proposal-features: features.txt '## Proposed language features' section\n\
exclude-includes-containing: $262.\n";

/// Where rule 7's proposal-feature set comes from (recorded in S0.toml).
pub const PROPOSAL_FEATURES_SOURCE: &str = "features.txt#Proposed language features";

pub fn s0_rules_sha256() -> String {
    trust_js_trace::sha256_hex(S0_RULES_TEXT.as_bytes())
}

/// Canonical S-async selection-rules text; its sha256 is the slice's rules
/// digest. S-async is S0's contract with the async flag SELECTED (required)
/// instead of excluded: rules 1–3 and 5–8 are byte-identical to S0, and rule 4
/// flips from "flags contain NONE of {async, module, CanBlockIsTrue,
/// CanBlockIsFalse}" to "flags contain async AND NONE of {module,
/// CanBlockIsTrue, CanBlockIsFalse}". `module` stays excluded (module/top-level
/// -await tests are the S-module slice's territory, evaluated by a different
/// goal); CanBlock* stay excluded (they gate SharedArrayBuffer blocking).
pub const S_ASYNC_RULES_TEXT: &str = "trust.js262.slice-rules.S-async.v1\n\
include-prefix: test/language/ test/built-ins/\n\
exclude-prefix: test/intl402/ test/staging/ test/annexB/ test/built-ins/Temporal/\n\
suffix: .js not _FIXTURE.js\n\
require-flags: async\n\
exclude-flags: module CanBlockIsTrue CanBlockIsFalse\n\
exclude-substring: $262.\n\
exclude-features: Atomics SharedArrayBuffer Temporal tail-call-optimization IsHTMLDDA cross-realm host-gc-required *Intl*\n\
exclude-proposal-features: features.txt '## Proposed language features' section\n\
exclude-includes-containing: $262.\n";

/// Canonical S-module selection-rules text. S-module is S0's contract with rule
/// 4 set to REQUIRE the `module` flag (module-goal tests), keeping only the
/// CanBlock* exclusions — `async` is NOT excluded, so module + top-level-await
/// (TLA) tests are included (a TLA test is `flags: [module, async]`). Every
/// other rule (prefixes, $262., features, proposal features, poisoned includes)
/// is byte-identical to S0. These tests need the module-goal driver (an ES
/// module evaluated with the correct base URL + a settled module graph), which
/// is the M2 D2/D5 build; the slice contract is frozen here ahead of it.
pub const S_MODULE_RULES_TEXT: &str = "trust.js262.slice-rules.S-module.v1\n\
include-prefix: test/language/ test/built-ins/\n\
exclude-prefix: test/intl402/ test/staging/ test/annexB/ test/built-ins/Temporal/\n\
suffix: .js not _FIXTURE.js\n\
require-flags: module\n\
exclude-flags: CanBlockIsTrue CanBlockIsFalse\n\
exclude-substring: $262.\n\
exclude-features: Atomics SharedArrayBuffer Temporal tail-call-optimization IsHTMLDDA cross-realm host-gc-required *Intl*\n\
exclude-proposal-features: features.txt '## Proposed language features' section\n\
exclude-includes-containing: $262.\n";

/// The frozen slice kinds this harness derives. All share the S0 path/content
/// contract; they differ only in the flag rule (rule 4): S0 EXCLUDES async and
/// module, S-async REQUIRES async, S-module REQUIRES module. Every other rule
/// (prefixes, $262., features, proposal features, poisoned includes) is
/// identical, so the slices partition the corpus's language/built-ins tests
/// along the async / module-goal boundaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SliceKind {
    /// The modern sync core (async + module EXCLUDED) — the M0 calibration slice.
    S0,
    /// The async core (async REQUIRED, module excluded) — the M2 D5 slice.
    SAsync,
    /// The module-goal core (module REQUIRED; includes module+TLA) — the M2
    /// D2/D5 module slice, calibrated by the module-goal driver.
    SModule,
}

impl SliceKind {
    /// The slice identifier written to the manifest `slice` field.
    pub fn id(self) -> &'static str {
        match self {
            SliceKind::S0 => "S0",
            SliceKind::SAsync => "S-async",
            SliceKind::SModule => "S-module",
        }
    }

    /// Flags a case MUST carry to be selected: [] for S0, ["async"] for
    /// S-async, ["module"] for S-module.
    pub fn require_flags(self) -> &'static [&'static str] {
        match self {
            SliceKind::S0 => &[],
            SliceKind::SAsync => &["async"],
            SliceKind::SModule => &["module"],
        }
    }

    /// Flags whose presence EXCLUDES a case. S0 excludes async + module;
    /// S-async requires async (drops async from the exclusion set, keeps
    /// module/CanBlock); S-module requires module (drops module AND async from
    /// the exclusion set — module+TLA is in scope — keeping only CanBlock*).
    pub fn exclude_flags(self) -> &'static [&'static str] {
        match self {
            SliceKind::S0 => &EXCLUDE_FLAGS,
            SliceKind::SAsync => &["module", "CanBlockIsTrue", "CanBlockIsFalse"],
            SliceKind::SModule => &["CanBlockIsTrue", "CanBlockIsFalse"],
        }
    }

    /// The canonical selection-rules text whose sha256 is the rules digest.
    pub fn rules_text(self) -> &'static str {
        match self {
            SliceKind::S0 => S0_RULES_TEXT,
            SliceKind::SAsync => S_ASYNC_RULES_TEXT,
            SliceKind::SModule => S_MODULE_RULES_TEXT,
        }
    }

    pub fn rules_sha256(self) -> String {
        trust_js_trace::sha256_hex(self.rules_text().as_bytes())
    }

    /// Kind from a manifest `slice` field (embedded format).
    pub fn from_id(id: &str) -> Option<SliceKind> {
        match id {
            "S0" => Some(SliceKind::S0),
            "S-async" => Some(SliceKind::SAsync),
            "S-module" => Some(SliceKind::SModule),
            _ => None,
        }
    }

    /// Parse the `--slice-kind` CLI value (`s0` | `async` | `module`).
    pub fn parse_cli(s: &str) -> Option<SliceKind> {
        match s {
            "s0" | "S0" => Some(SliceKind::S0),
            "async" | "s-async" | "S-async" => Some(SliceKind::SAsync),
            "module" | "s-module" | "S-module" => Some(SliceKind::SModule),
            _ => None,
        }
    }
}

/// Corpus-derived exclusion context (rules 7–8). Fail-closed: a corpus
/// without features.txt or harness/ cannot be sliced.
#[derive(Debug, Clone)]
pub struct SliceContext {
    pub proposal_features: std::collections::BTreeSet<String>,
    pub poisoned_includes: std::collections::BTreeSet<String>,
}

pub fn load_slice_context(corpus: &Path) -> anyhow::Result<SliceContext> {
    let features_path = corpus.join("features.txt");
    let text = std::fs::read_to_string(&features_path).map_err(|e| {
        anyhow::anyhow!("S0 rule 7 needs {}: {e}", features_path.display())
    })?;
    let mut proposal_features = std::collections::BTreeSet::new();
    let mut in_proposed = false;
    for line in text.lines() {
        let t = line.trim();
        if let Some(h) = t.strip_prefix("## ") {
            // test262's features.txt delimits sections with `## <Title>`, but a
            // few rows erroneously use `## ` for URL / sub-comment lines INSIDE a
            // section (e.g. `## https://github.com/tc39/proposal-source-phase-imports`
            // and `## test262 special specifier`, both under "Proposed language
            // features"). A naive "any `## ` ends the section" reader flips out of
            // the proposal section at the first such typo and silently drops every
            // proposal listed after it (source-phase-imports, import-defer,
            // import-text, immutable-arraybuffer, import-bytes, ... — 10 of the 16
            // proposals here), wrongly admitting their tests into S0/S-async. Real
            // section headers name a feature GROUP and always contain "features"
            // ("Proposed language features", "Standard language features",
            // "Test-Harness Features"); the typo rows never do. So only a header
            // that contains "features" changes the active section — typo'd `##`
            // rows are treated as comments, keeping the proposal section intact.
            if h.to_ascii_lowercase().contains("features") {
                in_proposed = h == "Proposed language features";
            }
            continue;
        }
        if t.is_empty() || t.starts_with('#') {
            continue;
        }
        if in_proposed {
            // A feature row is a bare token, optionally trailed by an inline
            // `# comment`; take the leading whitespace/`#`-delimited token.
            let tok = t.split_whitespace().next().unwrap_or(t);
            proposal_features.insert(tok.to_string());
        }
    }
    let harness = corpus.join("harness");
    let mut poisoned_includes = std::collections::BTreeSet::new();
    let entries = std::fs::read_dir(&harness)
        .map_err(|e| anyhow::anyhow!("S0 rule 8 needs {}: {e}", harness.display()))?;
    for entry in entries {
        let entry = entry?;
        let Some(name) = entry.file_name().to_str().map(str::to_string) else {
            continue;
        };
        if !name.ends_with(".js") || !entry.file_type()?.is_file() {
            continue;
        }
        if contains_subslice(&std::fs::read(entry.path())?, b"$262.") {
            poisoned_includes.insert(name);
        }
    }
    Ok(SliceContext { proposal_features, poisoned_includes })
}

#[derive(Debug, Clone)]
pub struct DerivedSlice {
    /// Selected corpus-relative paths, sorted bytewise ascending.
    pub paths: Vec<String>,
    pub list_sha256: String,
}

/// list_sha256 over an already-ordered path list.
pub fn list_sha256(paths: &[String]) -> String {
    let mut hasher = Sha256::new();
    for p in paths {
        hasher.update(p.as_bytes());
        hasher.update(b"\n");
    }
    let digest = hasher.finalize();
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

/// Path-only selection rules (1..3). Applied before reading file content.
fn path_selected(rel: &str) -> bool {
    if !INCLUDE_PREFIXES.iter().any(|p| rel.starts_with(p)) {
        return false;
    }
    if EXCLUDE_PREFIXES.iter().any(|p| rel.starts_with(p)) {
        return false;
    }
    rel.ends_with(".js") && !rel.ends_with("_FIXTURE.js")
}

/// Content rules (4..8). `Err` = unparseable frontmatter (fail-closed).
/// The flag rule (4) is `kind`-parametric: every `kind.require_flags()` must be
/// present and no `kind.exclude_flags()` may be — the only place S0 and S-async
/// diverge.
fn content_selected(
    rel: &str,
    content: &[u8],
    ctx: &SliceContext,
    kind: SliceKind,
) -> Result<bool, String> {
    if contains_subslice(content, b"$262.") {
        return Ok(false);
    }
    let text = String::from_utf8_lossy(content);
    let fm = parse_frontmatter(&text).map_err(|e| format!("{rel}: {e}"))?;
    if !kind.require_flags().iter().all(|rf| fm.flags.iter().any(|f| f == rf)) {
        return Ok(false);
    }
    if fm.flags.iter().any(|f| kind.exclude_flags().contains(&f.as_str())) {
        return Ok(false);
    }
    if fm
        .features
        .iter()
        .any(|f| EXCLUDE_FEATURES.contains(&f.as_str()) || f.contains("Intl"))
    {
        return Ok(false);
    }
    if fm.features.iter().any(|f| ctx.proposal_features.contains(f)) {
        return Ok(false);
    }
    if fm.includes.iter().any(|i| ctx.poisoned_includes.contains(i.as_str())) {
        return Ok(false);
    }
    Ok(true)
}

/// May a directory (rel path, no trailing slash) contain selected files?
fn dir_may_contain(rel: &str) -> bool {
    let with_slash = format!("{rel}/");
    if EXCLUDE_PREFIXES.iter().any(|p| with_slash.starts_with(p)) {
        return false;
    }
    INCLUDE_PREFIXES.iter().any(|p| with_slash.starts_with(p) || p.starts_with(&with_slash))
}

fn walk(
    corpus: &Path,
    rel_dir: &str,
    ctx: &SliceContext,
    kind: SliceKind,
    out: &mut Vec<String>,
    errors: &mut Vec<String>,
) -> std::io::Result<()> {
    let abs = corpus.join(rel_dir);
    for entry in std::fs::read_dir(&abs)? {
        let entry = entry?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            errors.push(format!("{rel_dir}: non-UTF-8 file name"));
            continue;
        };
        let rel = format!("{rel_dir}/{name}");
        let ft = entry.file_type()?;
        if ft.is_dir() {
            if dir_may_contain(&rel) {
                walk(corpus, &rel, ctx, kind, out, errors)?;
            }
        } else if ft.is_file() && path_selected(&rel) {
            let content = std::fs::read(entry.path())?;
            match content_selected(&rel, &content, ctx, kind) {
                Ok(true) => out.push(rel),
                Ok(false) => {}
                Err(e) => errors.push(e),
            }
        }
    }
    Ok(())
}

/// Derive a slice of the given `kind` from a corpus checkout. Fail-closed: any
/// unparseable candidate frontmatter aborts the derivation.
pub fn derive(corpus: &Path, kind: SliceKind) -> anyhow::Result<DerivedSlice> {
    if !corpus.join("test").is_dir() {
        anyhow::bail!("corpus {} has no test/ directory", corpus.display());
    }
    let ctx = load_slice_context(corpus)?;
    let mut paths = Vec::new();
    let mut errors = Vec::new();
    walk(corpus, "test", &ctx, kind, &mut paths, &mut errors)?;
    if !errors.is_empty() {
        let shown = errors.iter().take(10).cloned().collect::<Vec<_>>().join("\n  ");
        anyhow::bail!(
            "{} derivation is fail-closed and {} candidate file(s) had unparseable frontmatter:\n  {shown}",
            kind.id(),
            errors.len()
        );
    }
    paths.sort(); // bytewise ascending
    let hash = list_sha256(&paths);
    Ok(DerivedSlice { paths, list_sha256: hash })
}

/// Derive the S0 slice (back-compat convenience over [`derive`]).
pub fn derive_s0(corpus: &Path) -> anyhow::Result<DerivedSlice> {
    derive(corpus, SliceKind::S0)
}

/// Build the committed embedded S0.toml manifest for a derivation (tests
/// inline). The payload-external committed slices use [`build_external_manifest`].
pub fn build_manifest(corpus_revision: &str, derived: &DerivedSlice) -> SliceManifest {
    SliceManifest {
        schema: SLICE_SCHEMA.to_string(),
        slice: "S0".to_string(),
        corpus_revision: corpus_revision.to_string(),
        derived_on: today_utc(),
        count: derived.paths.len() as u64,
        list_sha256: derived.list_sha256.clone(),
        rules_sha256: s0_rules_sha256(),
        tests: derived.paths.clone(),
    }
}

/// Render the committed payload-external slice manifest (schema_version +
/// [corpus] + [rules] + [derived], no embedded test list) — the S0.toml shape,
/// generalized to `kind`. The [rules] table always mirrors the canonical
/// selection constants for `kind`, so a re-derivation checks against it. Used
/// to (re)generate S-async.toml and by `slice-derive --slice-kind async --out`.
pub fn build_external_manifest(kind: SliceKind, corpus_revision: &str, derived: &DerivedSlice) -> String {
    fn arr(items: &[&str]) -> String {
        let inner = items.iter().map(|s| format!("\"{s}\"")).collect::<Vec<_>>().join(", ");
        format!("[{inner}]")
    }
    let id_slug = kind.id().to_ascii_lowercase();
    format!(
        "# {id} — a frozen Test262 slice for TrustJS calibration, re-derived from the\n\
# pinned corpus by applying [rules] exactly (see slice.rs / the M0 & M2 D5\n\
# scope docs) then checked against [derived]: the sorted selected-path list must\n\
# have exactly `count` entries and hash to `list_sha256` (sha256 over the UTF-8\n\
# concatenation of each relative path + \"\\n\", paths sorted bytewise ascending).\n\
# Any mismatch is drift — fail closed. This slice differs from S0 in rule 4 only:\n\
# `require_flags` are REQUIRED and `exclude_flags` are excluded.\n\
#\n\
# Author: Andrew Yates\n\
# Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0\n\
\n\
schema_version = \"0.1.0\"\n\
id = \"js262.{id_slug}.{date}-v1\"\n\
\n\
[corpus]\n\
revision = \"{revision}\"\n\
\n\
[rules]\n\
include_prefixes = {include_prefixes}\n\
exclude_prefixes = {exclude_prefixes}\n\
exclude_suffixes = [\"_FIXTURE.js\"]\n\
require_flags = {require_flags}\n\
exclude_flags = {exclude_flags}\n\
exclude_content_substrings = [\"$262.\"]\n\
exclude_features = {exclude_features}\n\
exclude_feature_substrings = [\"Intl\"]\n\
exclude_proposal_features_from = \"{proposal_source}\"\n\
exclude_include_content_substrings = [\"$262.\"]\n\
\n\
[derived]\n\
count = {count}\n\
list_sha256 = \"{list_sha256}\"\n",
        id = kind.id(),
        id_slug = id_slug,
        date = today_utc(),
        revision = corpus_revision,
        include_prefixes = arr(&INCLUDE_PREFIXES),
        exclude_prefixes = arr(&EXCLUDE_PREFIXES),
        require_flags = arr(kind.require_flags()),
        exclude_flags = arr(kind.exclude_flags()),
        exclude_features = arr(&EXCLUDE_FEATURES),
        proposal_source = PROPOSAL_FEATURES_SOURCE,
        count = derived.paths.len(),
        list_sha256 = derived.list_sha256,
    )
}

/// A committed slice manifest reduced to what verification and calibration
/// consume, format-independent.
#[derive(Debug, Clone)]
pub struct LoadedSlice {
    /// The slice kind the manifest self-declares (S0 vs S-async). The
    /// re-derivation path uses it so a payload-external manifest is checked
    /// against the matching selection contract.
    pub kind: SliceKind,
    pub count: u64,
    pub list_sha256: String,
    /// Present only for the embedded format; the payload-external format
    /// requires re-derivation from the pinned corpus.
    pub tests: Option<Vec<String>>,
    /// Internal-consistency + rules-digest findings (fail-closed).
    pub findings: Vec<Finding>,
}

/// Load a committed slice manifest — either the embedded format
/// (schema = trust.js262.slice.v1, tests inline) or the payload-external
/// format (schema_version + [corpus]/[rules]/[derived]) — and check internal
/// consistency and the rules digest against the canonical constants.
pub fn load_slice(path: &Path) -> anyhow::Result<LoadedSlice> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("cannot read slice manifest {}: {e}", path.display()))?;
    let value: toml::Value = toml::from_str(&text)
        .map_err(|e| anyhow::anyhow!("cannot parse slice manifest {}: {e}", path.display()))?;
    if value.get("schema").is_some() {
        let manifest: SliceManifest = toml::from_str(&text).map_err(|e| {
            anyhow::anyhow!("cannot parse embedded slice manifest {}: {e}", path.display())
        })?;
        let mut findings = Vec::new();
        if manifest.schema != SLICE_SCHEMA {
            findings.push(Finding::new(
                "slice-schema-mismatch",
                format!("schema is {:?}, want {SLICE_SCHEMA:?}", manifest.schema),
            ));
        }
        let kind = match SliceKind::from_id(&manifest.slice) {
            Some(k) => k,
            None => {
                findings.push(Finding::new(
                    "slice-unknown-kind",
                    format!("unknown slice id {:?} (want \"S0\" or \"S-async\")", manifest.slice),
                ));
                SliceKind::S0
            }
        };
        if manifest.count != manifest.tests.len() as u64 {
            findings.push(Finding::new(
                "slice-count-mismatch",
                format!("count field {} != tests.len() {}", manifest.count, manifest.tests.len()),
            ));
        }
        let recomputed = list_sha256(&manifest.tests);
        if recomputed != manifest.list_sha256 {
            findings.push(Finding::new(
                "slice-list-hash-mismatch",
                format!("recomputed {recomputed} != recorded {}", manifest.list_sha256),
            ));
        }
        let rules = kind.rules_sha256();
        if manifest.rules_sha256 != rules {
            findings.push(Finding::new(
                "slice-rules-digest-mismatch",
                format!("committed rules_sha256 {} != canonical {rules}", manifest.rules_sha256),
            ));
        }
        Ok(LoadedSlice {
            kind,
            count: manifest.count,
            list_sha256: manifest.list_sha256,
            tests: Some(manifest.tests),
            findings,
        })
    } else {
        let manifest: ExternalSliceManifest = toml::from_str(&text).map_err(|e| {
            anyhow::anyhow!("cannot parse payload-external slice manifest {}: {e}", path.display())
        })?;
        let mut findings = Vec::new();
        let r = &manifest.rules;
        // Self-declared kind from require_flags: exact ["async"] selects
        // S-async, exact ["module"] selects S-module; anything else (including
        // the absent/empty S0 default) is S0. The require_flags check below then
        // validates that choice against the canonical constants, so a corrupt
        // require_flags fails closed.
        let kind = match r.require_flags.as_slice() {
            [only] if only == "async" => SliceKind::SAsync,
            [only] if only == "module" => SliceKind::SModule,
            _ => SliceKind::S0,
        };
        let checks: [(&str, &[String], &[&str]); 9] = [
            ("include_prefixes", &r.include_prefixes, &INCLUDE_PREFIXES),
            ("exclude_prefixes", &r.exclude_prefixes, &EXCLUDE_PREFIXES),
            ("exclude_suffixes", &r.exclude_suffixes, &["_FIXTURE.js"]),
            ("require_flags", &r.require_flags, kind.require_flags()),
            ("exclude_flags", &r.exclude_flags, kind.exclude_flags()),
            ("exclude_content_substrings", &r.exclude_content_substrings, &["$262."]),
            ("exclude_features", &r.exclude_features, &EXCLUDE_FEATURES),
            ("exclude_feature_substrings", &r.exclude_feature_substrings, &["Intl"]),
            (
                "exclude_include_content_substrings",
                &r.exclude_include_content_substrings,
                &["$262."],
            ),
        ];
        for (name, got, want) in checks {
            if got.iter().map(String::as_str).ne(want.iter().copied()) {
                findings.push(Finding::new(
                    "slice-rules-digest-mismatch",
                    format!("[rules].{name} is {got:?}, canonical for {} is {want:?}", kind.id()),
                ));
            }
        }
        if r.exclude_proposal_features_from != PROPOSAL_FEATURES_SOURCE {
            findings.push(Finding::new(
                "slice-rules-digest-mismatch",
                format!(
                    "[rules].exclude_proposal_features_from is {:?}, canonical is {PROPOSAL_FEATURES_SOURCE:?}",
                    r.exclude_proposal_features_from
                ),
            ));
        }
        Ok(LoadedSlice {
            kind,
            count: manifest.derived.count,
            list_sha256: manifest.derived.list_sha256,
            tests: None,
            findings,
        })
    }
}

/// Compare a fresh derivation against the committed manifest (slice-verify
/// and the calibrate preflight).
pub fn verify_derived(loaded: &LoadedSlice, derived: &DerivedSlice) -> Vec<Finding> {
    let mut findings = Vec::new();
    if loaded.count != derived.paths.len() as u64 {
        findings.push(Finding::new(
            "slice-derived-count-mismatch",
            format!("committed count {} != derived count {}", loaded.count, derived.paths.len()),
        ));
    }
    if loaded.list_sha256 != derived.list_sha256 {
        findings.push(Finding::new(
            "slice-derived-list-mismatch",
            format!(
                "committed list_sha256 {} != derived {}",
                loaded.list_sha256, derived.list_sha256
            ),
        ));
    }
    findings
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write(root: &Path, rel: &str, content: &str) {
        let p = root.join(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, content).unwrap();
    }

    #[test]
    fn slice_kinds_partition_on_async_and_module_flags() {
        // The three slice kinds differ only in rule 4. S0 excludes both async
        // and module; S-async requires async (module still excluded); S-module
        // requires module (async NOT excluded — module+TLA is in scope).
        assert_eq!(SliceKind::S0.require_flags(), &[] as &[&str]);
        assert_eq!(SliceKind::SAsync.require_flags(), &["async"]);
        assert_eq!(SliceKind::SModule.require_flags(), &["module"]);
        assert!(SliceKind::SAsync.exclude_flags().contains(&"module"));
        assert!(!SliceKind::SModule.exclude_flags().contains(&"module"));
        assert!(!SliceKind::SModule.exclude_flags().contains(&"async"));
        // CanBlock* stay excluded everywhere.
        for k in [SliceKind::SAsync, SliceKind::SModule] {
            assert!(k.exclude_flags().contains(&"CanBlockIsTrue"));
        }
        // Round-trips and distinct rules digests.
        assert_eq!(SliceKind::from_id("S-module"), Some(SliceKind::SModule));
        assert_eq!(SliceKind::parse_cli("module"), Some(SliceKind::SModule));
        let digests = [
            SliceKind::S0.rules_sha256(),
            SliceKind::SAsync.rules_sha256(),
            SliceKind::SModule.rules_sha256(),
        ];
        assert_eq!(
            digests.iter().collect::<std::collections::BTreeSet<_>>().len(),
            3,
            "each slice kind has a distinct rules digest"
        );
    }

    #[test]
    fn proposal_section_survives_typo_double_hash_rows() {
        // Regression: the real test262 features.txt lists some proposals AFTER
        // rows that erroneously start with `## ` (a URL and a sub-comment) inside
        // the "Proposed language features" section. A reader that treats every
        // `## ` as a section boundary drops those proposals, wrongly admitting
        // their tests into the slice. Mirror that structure and assert every
        // proposal — including the ones after the typo rows — is captured, and
        // that the following real "## Standard language features" header still
        // ends the section.
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(
            root,
            "features.txt",
            "## Proposed language features\n#\n# Decorators\ndecorators\n\
             # Source Phase Imports\n## https://github.com/tc39/proposal-source-phase-imports\n\
             source-phase-imports\n## test262 special specifier\nsource-phase-imports-module-source\n\
             # Deferred import evaluation\nimport-defer\n\
             align-web-reality  # https://github.com/tc39/ecma262/pull/2164\n\n\
             ## Standard language features\nSymbol.iterator\nArray.prototype.includes\n\n\
             ## Test-Harness Features\nIsHTMLDDA\n",
        );
        write(root, "harness/assert.js", "// clean\n");
        let ctx = load_slice_context(root).unwrap();
        for want in [
            "decorators",
            "source-phase-imports",
            "source-phase-imports-module-source",
            "import-defer",
            "align-web-reality",
        ] {
            assert!(ctx.proposal_features.contains(want), "missing proposal {want}");
        }
        // Standard/harness features are NOT proposals.
        assert!(!ctx.proposal_features.contains("Symbol.iterator"));
        assert!(!ctx.proposal_features.contains("Array.prototype.includes"));
        assert!(!ctx.proposal_features.contains("IsHTMLDDA"));
        // The inline `# comment` after a proposal token is not swept in.
        assert!(!ctx.proposal_features.iter().any(|f| f.contains('#') || f.contains("github")));
    }

    #[test]
    fn synthetic_corpus_derivation() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        // Rules 7-8 context: every corpus carries features.txt + harness/.
        write(
            root,
            "features.txt",
            "## Proposed language features\n#\n# comment\nTestProposalFeat\n\n## Standard language features\nSymbol.iterator\n",
        );
        write(root, "harness/assert.js", "// clean include\n");
        write(root, "harness/poison.js", "$262.detachArrayBuffer(buf);\n");
        // IN: plain language test.
        write(root, "test/language/expressions/add.js", "/*---\ndescription: ok\n---*/\n1+1;");
        // IN: built-ins with benign frontmatter.
        write(
            root,
            "test/built-ins/Array/from.js",
            "/*---\nflags: [onlyStrict]\nfeatures: [Symbol.iterator]\n---*/\nx;",
        );
        // OUT rule 4: async flag.
        write(root, "test/language/async.js", "/*---\nflags: [async]\n---*/\nx;");
        // OUT rule 4: module flag (block-ish flow).
        write(root, "test/language/mod.js", "/*---\nflags: [module, generated]\n---*/\nx;");
        // OUT rule 3: fixture.
        write(root, "test/language/thing_FIXTURE.js", "x;");
        // OUT rule 3: not .js.
        write(root, "test/language/notes.md", "hi");
        // OUT rule 5: $262. usage.
        write(root, "test/built-ins/Realm/x.js", "/*---\n---*/\n$262.createRealm();");
        // OUT rule 6: Intl-containing feature.
        write(
            root,
            "test/built-ins/Intlish.js",
            "/*---\nfeatures: [Intl.DurationFormat]\n---*/\nx;",
        );
        // OUT rule 6: listed feature.
        write(root, "test/built-ins/sab.js", "/*---\nfeatures: [SharedArrayBuffer]\n---*/\nx;");
        // OUT rule 2: excluded prefixes.
        write(root, "test/annexB/b.js", "x;");
        write(root, "test/intl402/i.js", "x;");
        write(root, "test/staging/s.js", "x;");
        write(root, "test/built-ins/Temporal/t.js", "x;");
        // OUT rule 1: outside included roots.
        write(root, "test/harness/h.js", "x;");
        // IN: raw-flag test stays in.
        write(root, "test/language/raw.js", "/*---\nflags: [raw]\n---*/\nx;");
        // OUT rule 7: proposal-stage feature (from the fixture features.txt).
        write(
            root,
            "test/built-ins/proposal.js",
            "/*---\nfeatures: [TestProposalFeat]\n---*/\nx;",
        );
        // OUT rule 8: pulls a $262.-dependent harness include.
        write(
            root,
            "test/built-ins/poisoned-include.js",
            "/*---\nincludes: [poison.js]\n---*/\nx;",
        );
        // IN: a clean include is fine.
        write(
            root,
            "test/built-ins/clean-include.js",
            "/*---\nincludes: [assert.js]\n---*/\nx;",
        );

        let derived = derive_s0(root).unwrap();
        assert_eq!(
            derived.paths,
            [
                "test/built-ins/Array/from.js",
                "test/built-ins/clean-include.js",
                "test/language/expressions/add.js",
                "test/language/raw.js",
            ]
        );
        // Hash is the concat-of-(path + \n) digest, stable by construction.
        let expected = list_sha256(&derived.paths);
        assert_eq!(derived.list_sha256, expected);
        // Round-trip through the embedded manifest format.
        let manifest = build_manifest("cafe", &derived);
        let toml_text = toml::to_string_pretty(&manifest).unwrap();
        let manifest_path = root.join("S0.toml");
        fs::write(&manifest_path, &toml_text).unwrap();
        let loaded = load_slice(&manifest_path).unwrap();
        assert!(loaded.findings.is_empty(), "{:?}", loaded.findings);
        assert_eq!(loaded.tests.as_deref(), Some(&derived.paths[..]));
        assert!(verify_derived(&loaded, &derived).is_empty());
        let reparsed: SliceManifest = toml::from_str(&toml_text).unwrap();
        assert_eq!(reparsed, manifest);
    }

    #[test]
    fn payload_external_manifest_loads() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(root, "features.txt", "## Proposed language features\n");
        write(root, "harness/assert.js", "// clean\n");
        write(root, "test/language/a.js", "/*---\n---*/\nx;");
        let derived = derive_s0(root).unwrap();
        let text = format!(
            r#"
schema_version = "0.1.0"
id = "js262.s0.2026-07-21"
[corpus]
revision = "tc39/test262:cafe"
[rules]
include_prefixes = ["test/language/", "test/built-ins/"]
exclude_prefixes = ["test/intl402/", "test/staging/", "test/annexB/", "test/built-ins/Temporal/"]
exclude_suffixes = ["_FIXTURE.js"]
exclude_flags = ["async", "module", "CanBlockIsTrue", "CanBlockIsFalse"]
exclude_content_substrings = ["$262."]
exclude_features = ["Atomics", "SharedArrayBuffer", "Temporal", "tail-call-optimization", "IsHTMLDDA", "cross-realm", "host-gc-required"]
exclude_feature_substrings = ["Intl"]
exclude_proposal_features_from = "features.txt#Proposed language features"
exclude_include_content_substrings = ["$262."]
[derived]
count = {}
list_sha256 = "{}"
"#,
            derived.paths.len(),
            derived.list_sha256
        );
        let path = root.join("S0-external.toml");
        fs::write(&path, text).unwrap();
        let loaded = load_slice(&path).unwrap();
        assert!(loaded.findings.is_empty(), "{:?}", loaded.findings);
        assert!(loaded.tests.is_none());
        assert!(verify_derived(&loaded, &derived).is_empty());

        // A rules drift is a named finding.
        let drifted = fs::read_to_string(&path).unwrap().replace("\"async\", ", "");
        fs::write(&path, drifted).unwrap();
        let loaded = load_slice(&path).unwrap();
        assert!(loaded.findings.iter().any(|f| f.code == "slice-rules-digest-mismatch"));
    }

    #[test]
    fn derivation_is_fail_closed_on_bad_frontmatter() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(root, "features.txt", "## Proposed language features\n");
        write(root, "harness/assert.js", "// clean\n");
        write(root, "test/language/ok.js", "/*---\n---*/\nx;");
        write(root, "test/language/bad.js", "/*---\nflags: [async\n---*/\nx;");
        assert!(derive_s0(root).is_err());
    }

    #[test]
    fn verify_flags_drift() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(root, "features.txt", "## Proposed language features\n");
        write(root, "harness/assert.js", "// clean\n");
        write(root, "test/language/a.js", "/*---\n---*/\nx;");
        let derived = derive_s0(root).unwrap();
        let mut manifest = build_manifest("cafe", &derived);
        manifest.tests.push("test/language/phantom.js".to_string());
        manifest.count += 1;
        manifest.list_sha256 = list_sha256(&manifest.tests);
        let loaded = LoadedSlice {
            kind: SliceKind::S0,
            count: manifest.count,
            list_sha256: manifest.list_sha256.clone(),
            tests: Some(manifest.tests.clone()),
            findings: vec![],
        };
        let findings = verify_derived(&loaded, &derived);
        assert!(findings.iter().any(|f| f.code == "slice-derived-count-mismatch"));
        assert!(findings.iter().any(|f| f.code == "slice-derived-list-mismatch"));
    }

    /// S-async selects EXACTLY the async-flag cases that S0 excludes, over the
    /// same synthetic corpus — the two slices partition the async boundary.
    #[test]
    fn synthetic_corpus_async_derivation() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(
            root,
            "features.txt",
            "## Proposed language features\nTestProposalFeat\n\n## Standard language features\nSymbol.iterator\n",
        );
        write(root, "harness/assert.js", "// clean include\n");
        write(root, "harness/poison.js", "$262.detachArrayBuffer(buf);\n");
        // IN (async): a plain async test, no includes (auto doneprintHandle).
        write(root, "test/built-ins/Promise/p.js", "/*---\nflags: [async]\n---*/\n$DONE();");
        // IN (async): async + a benign extra flag + a clean include.
        write(
            root,
            "test/language/await/a.js",
            "/*---\nflags: [async, noStrict]\nincludes: [asyncHelpers.js]\n---*/\nasyncTest(f);",
        );
        // OUT: sync test (no async flag) — this is S0's, not S-async's.
        write(root, "test/language/sync.js", "/*---\n---*/\n1+1;");
        // OUT: async BUT module (module tests are the S-module slice).
        write(root, "test/language/am.js", "/*---\nflags: [async, module]\n---*/\nx;");
        // OUT: async BUT CanBlockIsFalse.
        write(root, "test/language/ab.js", "/*---\nflags: [async, CanBlockIsFalse]\n---*/\nx;");
        // OUT rule 5: async but uses $262.
        write(root, "test/built-ins/realm.js", "/*---\nflags: [async]\n---*/\n$262.evalScript();");
        // OUT rule 6: async but Intl / listed feature.
        write(root, "test/built-ins/sab.js", "/*---\nflags: [async]\nfeatures: [SharedArrayBuffer]\n---*/\nx;");
        // OUT rule 7: async but proposal-stage feature.
        write(root, "test/built-ins/prop.js", "/*---\nflags: [async]\nfeatures: [TestProposalFeat]\n---*/\nx;");
        // OUT rule 8: async but pulls a $262.-poisoned include.
        write(root, "test/built-ins/pi.js", "/*---\nflags: [async]\nincludes: [poison.js]\n---*/\nx;");
        // OUT rule 2/3: excluded prefix + fixture.
        write(root, "test/intl402/i.js", "/*---\nflags: [async]\n---*/\nx;");
        write(root, "test/language/thing_FIXTURE.js", "/*---\nflags: [async]\n---*/\nx;");

        let derived = derive(root, SliceKind::SAsync).unwrap();
        assert_eq!(
            derived.paths,
            ["test/built-ins/Promise/p.js", "test/language/await/a.js"]
        );
        assert_eq!(derived.list_sha256, list_sha256(&derived.paths));

        // The same corpus under S0 selects the complement: the sync test only.
        let s0 = derive(root, SliceKind::S0).unwrap();
        assert_eq!(s0.paths, ["test/language/sync.js"]);

        // Round-trip through the payload-external manifest S-async.toml uses.
        let text = build_external_manifest(SliceKind::SAsync, "cafe", &derived);
        let path = root.join("S-async.toml");
        fs::write(&path, &text).unwrap();
        let loaded = load_slice(&path).unwrap();
        assert!(loaded.findings.is_empty(), "{:?}", loaded.findings);
        assert_eq!(loaded.kind, SliceKind::SAsync);
        assert!(loaded.tests.is_none());
        assert_eq!(loaded.count, 2);
        assert!(verify_derived(&loaded, &derived).is_empty());

        // A require_flags drift (async dropped) is a named finding, and the
        // kind falls back to S0 whose exclude_flags then also mismatch.
        let drifted = text.replace("require_flags = [\"async\"]", "require_flags = []");
        fs::write(&path, drifted).unwrap();
        let loaded = load_slice(&path).unwrap();
        assert!(loaded.findings.iter().any(|f| f.code == "slice-rules-digest-mismatch"));
    }

    /// The two rules digests are distinct and stable, and CLI/id parsing is
    /// exact.
    #[test]
    fn slice_kind_identities() {
        assert_ne!(SliceKind::S0.rules_sha256(), SliceKind::SAsync.rules_sha256());
        assert_eq!(SliceKind::S0.rules_sha256(), s0_rules_sha256());
        assert_eq!(SliceKind::from_id("S-async"), Some(SliceKind::SAsync));
        assert_eq!(SliceKind::from_id("nope"), None);
        assert_eq!(SliceKind::parse_cli("async"), Some(SliceKind::SAsync));
        assert_eq!(SliceKind::parse_cli("s0"), Some(SliceKind::S0));
        assert_eq!(SliceKind::parse_cli("weird"), None);
        // S-async keeps module/CanBlock excluded but drops async.
        assert!(!SliceKind::SAsync.exclude_flags().contains(&"async"));
        assert!(SliceKind::SAsync.exclude_flags().contains(&"module"));
        assert_eq!(SliceKind::SAsync.require_flags(), &["async"]);
    }
}
