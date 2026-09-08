// targo trust spec: the compiler-authoritative spec surface (v6/D1, W3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

//! `targo trust spec --emit clean [-p <pkg>]`
//!
//! Standing ruling v6/D1: this subcommand prints the Clean proposition the
//! compiler actually elaborated. Kernel-graded cited goals remain distinct
//! from W3's explicitly ungraded, zero-authority uncited-clause denotations. An offline
//! re-elaboration in targo-trust was considered and REJECTED — it can print a
//! different proposition than the kernel saw, precisely when someone is
//! debugging a failure. So this module never elaborates anything. It:
//!
//! 1. provisions a fresh, empty session directory (so no stale artifact from
//!    an earlier run can ever satisfy the read);
//! 2. drives a `targo trust check`-equivalent verified compilation with the
//!    emission knob (`--spec-emit-dir <dir>`, which the pipeline transports to
//!    the compiler — `TRUST_SPEC_EMIT_DIR` in Cargo crate mode, the typed
//!    `-Ztrust-dump=spec-clean:` sink for a direct trustc invocation);
//! 3. reads back the artifact the compiler session sealed, validates its
//!    format version and its independent row counts, and prints the rows.
//!
//! FAIL-CLOSED: no artifact, an unknown format version, or a torn artifact
//! (missing seal / seal count mismatch) is a REFUSAL carrying the fix options
//! (v7/D3), never an excuse to re-derive a proposition locally. Rows print even
//! when the verified build itself failed — that is the debugging case the
//! ruling exists for — but the failing exit status is preserved.

use std::collections::BTreeSet;
use std::fmt;
use std::path::Path;
use std::process::ExitCode;

use serde::de::{Error as _, MapAccess, Visitor};

use crate::types::Subcommand;

/// Artifact format tag; every line of the compiler-written JSONL carries it.
/// Mirror of `rustc_mir_transform::trust_spec_emit::SPEC_CLEAN_FORMAT`.
const SPEC_CLEAN_FORMAT: &str = "trust-spec-clean";

/// The one artifact version this reader understands. An unknown version is a
/// refusal, not a best-effort parse.
const SPEC_CLEAN_SUPPORTED_VERSION: u64 = 2;

/// Closed schema-v2 spellings emitted by `trust_spec_emit`. A producer adding
/// a new tag must update this reader rather than having the tag silently acquire
/// meaning here.
const SPEC_CLEAN_GOAL_ORIGINS: &[&str] = &["ensures-citation", "ensures-citation-deferred"];
const SPEC_CLEAN_GOAL_VERDICTS: &[&str] = &[
    "certified",
    "trusted",
    "session-tainted",
    "theorem-not-found",
    "declaration-not-theorem",
    "unsafe-theorem",
    "partial-theorem",
    "no-proof-term",
    "clause-outside-fragment",
    "statement-or-certification-rejected",
];

/// Schema-v2 rows are closed objects. Unknown members cannot be ignored: doing
/// so would let a newer producer attach semantics that this reader silently
/// drops while still presenting the row as understood.
const SPEC_CLEAN_GOAL_KEYS: &[&str] = &[
    "format",
    "v",
    "row",
    "crate",
    "session",
    "def_path",
    "contract_index",
    "origin",
    "clause",
    "theorem",
    "goal_clean",
    "elab_error",
    "verdict",
    "detail",
];
const SPEC_CLEAN_DENOTATION_KEYS: &[&str] = &[
    "format",
    "v",
    "row",
    "crate",
    "session",
    "def_path",
    "contract_index",
    "kind",
    "source",
    "clause",
    "goal_clean",
    "elab_error",
    "authority",
    "verdict",
];
const SPEC_CLEAN_SESSION_KEYS: &[&str] =
    &["format", "v", "row", "crate", "session", "goals", "denotations"];

/// Per-unit artifact filename suffix.
const SPEC_CLEAN_FILE_SUFFIX: &str = ".spec-clean.jsonl";

/// Parsed `targo trust spec` arguments.
#[derive(Debug)]
struct SpecArgs {
    /// Raw machine-readable row output instead of the human rendering.
    json: bool,
    /// Everything forwarded to the underlying verified check.
    forwarded: Vec<String>,
}

/// Parse the spec surface. `--emit clean` is MANDATORY and `clean` is the only
/// supported value: the subcommand exists to print compiler-elaborated Clean
/// propositions, with graded goals and zero-authority denotations distinct,
/// and refusing anything else with the options listed is the v7/D3 contract.
fn parse_spec_args(args: &[String]) -> Result<SpecArgs, String> {
    let mut emit: Option<String> = None;
    let mut json = false;
    let mut forwarded = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--emit" => {
                i += 1;
                let value = args.get(i).ok_or_else(|| {
                    "targo trust spec: `--emit` requires a value; the supported surface is \
                     `--emit clean`"
                        .to_string()
                })?;
                emit = Some(value.clone());
            }
            s if s.starts_with("--emit=") => {
                emit = Some(s["--emit=".len()..].to_string());
            }
            "--json" => {
                json = true;
            }
            s if s == "--spec-emit-dir" || s.starts_with("--spec-emit-dir=") => {
                return Err(
                    "targo trust spec: `--spec-emit-dir` is provisioned by the subcommand itself \
                     (a fresh directory per run, so a stale artifact can never satisfy the read). \
                     To keep the raw artifact, run `targo trust check --spec-emit-dir <abs dir>` \
                     and read the *.spec-clean.jsonl files directly."
                        .to_string(),
                );
            }
            _ => forwarded.push(args[i].clone()),
        }
        i += 1;
    }
    match emit.as_deref() {
        Some("clean") => Ok(SpecArgs { json, forwarded }),
        Some(other) => Err(format!(
            "targo trust spec: `--emit {other}` is not a supported spec surface. Options:\n  \
             - `--emit clean` prints compiler-elaborated Clean propositions: explicitly \
             ungraded denotations plus the goals the kernel actually graded\n  \
             - for the TrustIr lowering artifact use `--emit=trust-ir` on a direct trustc \
             invocation, or `-Ztrust-dump=ir:<dir>`"
        )),
        None => {
            Err("targo trust spec: `--emit clean` is required — this surface prints the Clean \
             propositions the compiler actually elaborated, distinguishing zero-authority \
             denotations from kernel-graded goals (v6/D1, W3). Run: `targo trust spec --emit \
             clean [-p <pkg>]`"
                .to_string())
        }
    }
}

/// One kernel-graded goal row read back from the artifact.
#[derive(Debug, Clone, PartialEq)]
struct GoalRow {
    krate: String,
    session: String,
    def_path: String,
    contract_index: u64,
    origin: String,
    clause: Option<String>,
    theorem: String,
    goal_clean: Option<String>,
    elab_error: Option<String>,
    verdict: String,
    detail: Option<String>,
    /// The raw line, for `--json` passthrough (byte-preserving output).
    raw: String,
}

/// One explicitly ungraded, zero-authority canonical clause denotation.
#[derive(Debug, Clone, PartialEq)]
struct DenotationRow {
    krate: String,
    session: String,
    def_path: String,
    contract_index: u64,
    kind: String,
    source: String,
    clause: Option<String>,
    goal_clean: Option<String>,
    elab_error: Option<String>,
    authority: String,
    verdict: String,
    /// The raw line, for `--json` passthrough (byte-preserving output).
    raw: String,
}

/// One sealed per-unit artifact file.
#[derive(Debug)]
struct UnitArtifact {
    krate: String,
    session: String,
    goals: Vec<GoalRow>,
    denotations: Vec<DenotationRow>,
}

/// Why the artifact read REFUSED. Every variant carries its fix (v7/D3).
#[derive(Debug, PartialEq)]
enum SpecRefusal {
    NoArtifact,
    Malformed {
        file: String,
        detail: String,
    },
    UnsupportedVersion {
        file: String,
        version: String,
    },
    Unsealed {
        file: String,
    },
    Torn {
        file: String,
        sealed_goals: u64,
        counted_goals: u64,
        sealed_denotations: u64,
        counted_denotations: u64,
    },
}

impl SpecRefusal {
    fn render(&self) -> String {
        match self {
            SpecRefusal::NoArtifact => "targo trust spec: REFUSED — no compiler spec artifact \
                 was produced by this run.\n\
                 `--emit clean` is compiler-authoritative (v6/D1): it prints only Clean \
                 propositions a live compiler session elaborated; it never re-elaborates \
                 offline, so with no \
                 session artifact there is nothing it may claim. Causes and fixes:\n  \
                 - the compilation failed before verification ran: fix the build errors reported \
                 above and re-run\n  \
                 - the installed trustc predates the spec-clean emitter: rebuild the toolchain \
                 (`./x.py build`) so trustc understands `-Ztrust-dump=spec-clean:<dir>`\n  \
                 - verification did not run for this invocation (an unverified or compat lane): \
                 run from the verified workspace lane — only an enabled verification walk writes \
                 and seals the artifact"
                .to_string(),
            SpecRefusal::Malformed { file, detail } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` is not well-formed \
                 ({detail}).\n\
                 The artifact is written only by trustc; a malformed file means a torn write or \
                 an incompatible producer. Fix: re-run `targo trust spec`; if it persists, \
                 rebuild the toolchain so trustc and targo-trust agree on the artifact format"
            ),
            SpecRefusal::UnsupportedVersion { file, version } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` carries format version \
                 {version}, and this targo-trust understands only version \
                 {SPEC_CLEAN_SUPPORTED_VERSION}.\n\
                 Fix: rebuild targo-trust and trustc from the same tree so the producer and the \
                 reader agree, then re-run"
            ),
            SpecRefusal::Unsealed { file } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` has no session seal.\n\
                 The seal is written when the verification walk COMPLETES; its absence means the \
                 compiler session died mid-walk (or an incompatible producer wrote the file). \
                 Fix: address the compiler failure reported above and re-run"
            ),
            SpecRefusal::Torn {
                file,
                sealed_goals,
                counted_goals,
                sealed_denotations,
                counted_denotations,
            } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` is torn: the session seal \
                 records {sealed_goals} goal row(s) and {sealed_denotations} denotation row(s), \
                 but the file holds {counted_goals} and {counted_denotations}, respectively.\n\
                 Fix: re-run `targo trust spec` (the session directory is provisioned fresh per \
                 run); if it persists, report it — two writers on one session directory is a bug"
            ),
        }
    }
}

/// A top-level JSON object that refuses duplicate member names while it is
/// being decoded. `serde_json::Value` alone cannot provide this property: its
/// map representation has already overwritten an earlier member by the time a
/// caller can inspect it.
struct UniqueJsonObject(serde_json::Map<String, serde_json::Value>);

impl<'de> serde::Deserialize<'de> for UniqueJsonObject {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct UniqueJsonObjectVisitor;

        impl<'de> Visitor<'de> for UniqueJsonObjectVisitor {
            type Value = UniqueJsonObject;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a JSON object with unique member names")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut object = serde_json::Map::new();
                while let Some(key) = map.next_key::<String>()? {
                    if object.contains_key(&key) {
                        return Err(A::Error::custom(format!("duplicate object member `{key}`")));
                    }
                    object.insert(key, map.next_value()?);
                }
                Ok(UniqueJsonObject(object))
            }
        }

        deserializer.deserialize_map(UniqueJsonObjectVisitor)
    }
}

fn parse_unique_json_object(line: &str, file: &str) -> Result<serde_json::Value, SpecRefusal> {
    serde_json::from_str::<UniqueJsonObject>(line)
        .map(|UniqueJsonObject(object)| serde_json::Value::Object(object))
        .map_err(|error| SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("invalid JSON line: {error}"),
        })
}

fn reject_unknown_row_keys(
    value: &serde_json::Value,
    allowed: &[&str],
    row_kind: &str,
    file: &str,
) -> Result<(), SpecRefusal> {
    let object = value.as_object().ok_or_else(|| SpecRefusal::Malformed {
        file: file.to_string(),
        detail: "JSON line is not an object".to_string(),
    })?;
    if let Some(key) = object.keys().find(|key| !allowed.contains(&key.as_str())) {
        return Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("{row_kind} row has unknown field `{key}`"),
        });
    }
    Ok(())
}

fn parse_required_string(
    value: &serde_json::Value,
    key: &str,
    file: &str,
) -> Result<String, SpecRefusal> {
    match value.get(key) {
        Some(serde_json::Value::String(value)) => Ok(value.clone()),
        Some(_) => Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row field `{key}` is not a string"),
        }),
        None => Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row missing `{key}`"),
        }),
    }
}

fn parse_required_nonempty_string(
    value: &serde_json::Value,
    key: &str,
    file: &str,
) -> Result<String, SpecRefusal> {
    let parsed = parse_required_string(value, key, file)?;
    if parsed.trim().is_empty() {
        return Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row field `{key}` is empty"),
        });
    }
    Ok(parsed)
}

fn parse_required_u64(
    value: &serde_json::Value,
    key: &str,
    file: &str,
) -> Result<u64, SpecRefusal> {
    match value.get(key) {
        Some(value) => value.as_u64().ok_or_else(|| SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row field `{key}` is not an unsigned integer"),
        }),
        None => Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row missing integer `{key}`"),
        }),
    }
}

fn parse_nullable_string(
    value: &serde_json::Value,
    key: &str,
    file: &str,
) -> Result<Option<String>, SpecRefusal> {
    match value.get(key) {
        Some(serde_json::Value::Null) => Ok(None),
        Some(serde_json::Value::String(value)) => Ok(Some(value.clone())),
        Some(_) => Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row field `{key}` is neither a string nor null"),
        }),
        None => Err(SpecRefusal::Malformed {
            file: file.to_string(),
            detail: format!("row missing `{key}`"),
        }),
    }
}

/// Parse and validate ONE per-unit artifact file: every line self-describes
/// the format and version, exactly one session seal is present, and the seal's
/// independent goal/denotation counts match the rows read. Goal and denotation
/// identities are exact within their respective populations: a duplicate
/// `(def_path, contract_index)` is malformed even when the two JSON objects are
/// byte-identical.
fn parse_unit_artifact(file_name: &str, contents: &str) -> Result<UnitArtifact, SpecRefusal> {
    let mut goals: Vec<GoalRow> = Vec::new();
    let mut goal_keys: BTreeSet<(String, u64)> = BTreeSet::new();
    let mut denotations: Vec<DenotationRow> = Vec::new();
    let mut denotation_keys: BTreeSet<(String, u64)> = BTreeSet::new();
    let mut seal: Option<(String, String, u64, u64)> = None;
    for (line_index, line) in contents.lines().enumerate() {
        if line.trim().is_empty() {
            return Err(SpecRefusal::Malformed {
                file: file_name.to_string(),
                detail: format!("blank JSONL row at line {}", line_index + 1),
            });
        }
        if seal.is_some() {
            return Err(SpecRefusal::Malformed {
                file: file_name.to_string(),
                detail: "nonblank row follows the terminal session seal".to_string(),
            });
        }
        let value = parse_unique_json_object(line, file_name)?;
        let format = value.get("format").and_then(|v| v.as_str()).unwrap_or_default();
        if format != SPEC_CLEAN_FORMAT {
            return Err(SpecRefusal::Malformed {
                file: file_name.to_string(),
                detail: format!("unexpected format tag `{format}`"),
            });
        }
        // Version gate BEFORE any row interpretation: unknown versions refuse.
        match value.get("v").and_then(|v| v.as_u64()) {
            Some(SPEC_CLEAN_SUPPORTED_VERSION) => {}
            other => {
                return Err(SpecRefusal::UnsupportedVersion {
                    file: file_name.to_string(),
                    version: other
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| "<non-integer>".to_string()),
                });
            }
        }
        match value.get("row").and_then(|v| v.as_str()) {
            Some("goal") => {
                reject_unknown_row_keys(&value, SPEC_CLEAN_GOAL_KEYS, "goal", file_name)?;
                let krate = parse_required_nonempty_string(&value, "crate", file_name)?;
                // A direct `trustc -Ztrust-dump=spec-clean:...` invocation may
                // omit `-Ztrust-verify-session`; the compiler then emits the
                // empty string consistently on every row. Presence and type,
                // plus equality with the seal below, are the identity contract.
                let session = parse_required_string(&value, "session", file_name)?;
                let def_path = parse_required_nonempty_string(&value, "def_path", file_name)?;
                let contract_index = parse_required_u64(&value, "contract_index", file_name)?;
                let origin = parse_required_nonempty_string(&value, "origin", file_name)?;
                if !SPEC_CLEAN_GOAL_ORIGINS.contains(&origin.as_str()) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!("unknown goal origin `{origin}`"),
                    });
                }
                let clause = parse_nullable_string(&value, "clause", file_name)?;
                if clause.as_deref().is_some_and(|clause| clause.trim().is_empty()) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "goal row has an empty `clause` spelling".to_string(),
                    });
                }
                let theorem = parse_required_nonempty_string(&value, "theorem", file_name)?;
                let goal_clean = parse_nullable_string(&value, "goal_clean", file_name)?;
                let elab_error = parse_nullable_string(&value, "elab_error", file_name)?;
                let verdict = parse_required_nonempty_string(&value, "verdict", file_name)?;
                if !SPEC_CLEAN_GOAL_VERDICTS.contains(&verdict.as_str()) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!("unknown goal verdict `{verdict}`"),
                    });
                }
                let detail = parse_nullable_string(&value, "detail", file_name)?;
                if clause.is_some() {
                    match (&goal_clean, &elab_error) {
                        (Some(goal), None) if !goal.trim().is_empty() => {}
                        (None, Some(error)) if !error.trim().is_empty() => {}
                        (Some(goal), None) if goal.trim().is_empty() => {
                            return Err(SpecRefusal::Malformed {
                                file: file_name.to_string(),
                                detail: "goal row has an empty `goal_clean` proposition"
                                    .to_string(),
                            });
                        }
                        (None, Some(error)) if error.trim().is_empty() => {
                            return Err(SpecRefusal::Malformed {
                                file: file_name.to_string(),
                                detail: "goal row has an empty `elab_error` reason".to_string(),
                            });
                        }
                        _ => {
                            return Err(SpecRefusal::Malformed {
                                file: file_name.to_string(),
                                detail: "goal row must carry exactly one nonempty `goal_clean` or \
                                         `elab_error`"
                                    .to_string(),
                            });
                        }
                    }
                } else {
                    let Some(reason) =
                        elab_error.as_deref().filter(|reason| !reason.trim().is_empty())
                    else {
                        return Err(SpecRefusal::Malformed {
                            file: file_name.to_string(),
                            detail: "goal row with null `clause` must carry a nonempty \
                                     `elab_error` preparation-refusal reason"
                                .to_string(),
                        });
                    };
                    if goal_clean.is_some() {
                        return Err(SpecRefusal::Malformed {
                            file: file_name.to_string(),
                            detail: "goal row with null `clause` cannot carry `goal_clean`"
                                .to_string(),
                        });
                    }
                    if verdict != "clause-outside-fragment" {
                        return Err(SpecRefusal::Malformed {
                            file: file_name.to_string(),
                            detail: "goal row with null `clause` must have verdict \
                                     `clause-outside-fragment`"
                                .to_string(),
                        });
                    }
                    if detail.as_deref() != Some(reason) {
                        return Err(SpecRefusal::Malformed {
                            file: file_name.to_string(),
                            detail: "goal row with null `clause` must repeat its nonempty \
                                     `elab_error` preparation-refusal reason exactly in `detail`"
                                .to_string(),
                        });
                    }
                }
                if !goal_keys.insert((def_path.clone(), contract_index)) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!("duplicate goal identity ({def_path:?}, {contract_index})"),
                    });
                }
                goals.push(GoalRow {
                    krate,
                    session,
                    def_path,
                    contract_index,
                    origin,
                    clause,
                    theorem,
                    goal_clean,
                    elab_error,
                    verdict,
                    detail,
                    raw: line.to_string(),
                });
            }
            Some("denotation") => {
                reject_unknown_row_keys(
                    &value,
                    SPEC_CLEAN_DENOTATION_KEYS,
                    "denotation",
                    file_name,
                )?;
                let krate = parse_required_nonempty_string(&value, "crate", file_name)?;
                let session = parse_required_string(&value, "session", file_name)?;
                let def_path = parse_required_nonempty_string(&value, "def_path", file_name)?;
                let contract_index = parse_required_u64(&value, "contract_index", file_name)?;
                let kind = parse_required_string(&value, "kind", file_name)?;
                if !matches!(kind.as_str(), "requires" | "ensures") {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!("unknown denotation kind `{kind}`"),
                    });
                }
                let source = parse_required_string(&value, "source", file_name)?;
                if !matches!(
                    source.as_str(),
                    "attribute" | "native" | "builtin" | "inferred" | "synthesized"
                ) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!("unknown denotation source `{source}`"),
                    });
                }
                let clause = parse_nullable_string(&value, "clause", file_name)?;
                if clause.as_deref().is_some_and(|clause| clause.trim().is_empty()) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "denotation row has an empty `clause` spelling".to_string(),
                    });
                }
                let goal_clean = parse_nullable_string(&value, "goal_clean", file_name)?;
                let elab_error = parse_nullable_string(&value, "elab_error", file_name)?;
                if goal_clean.is_some() == elab_error.is_some() {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "denotation must carry exactly one of `goal_clean` or `elab_error`"
                            .to_string(),
                    });
                }
                if goal_clean.is_some()
                    && clause.as_deref().is_none_or(|clause| clause.trim().is_empty())
                {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "successful denotation has no nonempty canonical clause spelling"
                            .to_string(),
                    });
                }
                if goal_clean.as_deref().is_some_and(|goal| goal.trim().is_empty()) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "successful denotation has an empty `goal_clean` proposition"
                            .to_string(),
                    });
                }
                if elab_error.as_deref().is_some_and(|reason| reason.trim().is_empty()) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "refused denotation has an empty `elab_error` reason".to_string(),
                    });
                }
                let authority = parse_required_string(&value, "authority", file_name)?;
                let verdict = parse_required_string(&value, "verdict", file_name)?;
                if authority != "none" || verdict != "ungraded" {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!(
                            "denotation is not zero-authority (`authority`={authority:?}, \
                             `verdict`={verdict:?})"
                        ),
                    });
                }
                if !denotation_keys.insert((def_path.clone(), contract_index)) {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: format!(
                            "duplicate denotation identity ({def_path:?}, {contract_index})"
                        ),
                    });
                }
                denotations.push(DenotationRow {
                    krate,
                    session,
                    def_path,
                    contract_index,
                    kind,
                    source,
                    clause,
                    goal_clean,
                    elab_error,
                    authority,
                    verdict,
                    raw: line.to_string(),
                });
            }
            Some("session") => {
                reject_unknown_row_keys(&value, SPEC_CLEAN_SESSION_KEYS, "session", file_name)?;
                if seal.is_some() {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "more than one session seal".to_string(),
                    });
                }
                let goals_sealed = parse_required_u64(&value, "goals", file_name)?;
                let denotations_sealed = parse_required_u64(&value, "denotations", file_name)?;
                seal = Some((
                    parse_required_nonempty_string(&value, "crate", file_name)?,
                    parse_required_string(&value, "session", file_name)?,
                    goals_sealed,
                    denotations_sealed,
                ));
            }
            other => {
                return Err(SpecRefusal::Malformed {
                    file: file_name.to_string(),
                    detail: format!("unknown row kind {other:?}"),
                });
            }
        }
    }
    let Some((krate, session, sealed_goals, sealed_denotations)) = seal else {
        return Err(SpecRefusal::Unsealed { file: file_name.to_string() });
    };
    if goals.iter().any(|row| row.krate != krate || row.session != session)
        || denotations.iter().any(|row| row.krate != krate || row.session != session)
    {
        return Err(SpecRefusal::Malformed {
            file: file_name.to_string(),
            detail: "row crate/session identity disagrees with the session seal".to_string(),
        });
    }
    let counted_goals = u64::try_from(goals.len()).expect("artifact row count fits u64");
    let counted_denotations =
        u64::try_from(denotations.len()).expect("artifact row count fits u64");
    if sealed_goals != counted_goals || sealed_denotations != counted_denotations {
        return Err(SpecRefusal::Torn {
            file: file_name.to_string(),
            sealed_goals,
            counted_goals,
            sealed_denotations,
            counted_denotations,
        });
    }
    Ok(UnitArtifact { krate, session, goals, denotations })
}

/// Read every sealed per-unit artifact from the session directory. Zero files
/// is the fail-closed `NoArtifact` refusal — this is the property that makes
/// the subcommand a live-session instrument rather than an offline derivation.
fn read_spec_artifacts(dir: &Path) -> Result<Vec<UnitArtifact>, SpecRefusal> {
    let mut units = Vec::new();
    let mut names: Vec<std::path::PathBuf> = match std::fs::read_dir(dir) {
        Ok(entries) => entries
            .filter_map(|entry| entry.ok().map(|e| e.path()))
            .filter(|path| {
                path.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with(SPEC_CLEAN_FILE_SUFFIX))
            })
            .collect(),
        Err(_) => return Err(SpecRefusal::NoArtifact),
    };
    names.sort();
    for path in names {
        let file_name =
            path.file_name().and_then(|n| n.to_str()).unwrap_or("<non-utf8>").to_string();
        let contents = std::fs::read_to_string(&path).map_err(|error| SpecRefusal::Malformed {
            file: file_name.clone(),
            detail: format!("unreadable: {error}"),
        })?;
        units.push(parse_unit_artifact(&file_name, &contents)?);
    }
    if units.is_empty() {
        return Err(SpecRefusal::NoArtifact);
    }
    Ok(units)
}

fn render_goal_row(row: &GoalRow) -> String {
    let mut out = String::new();
    out.push_str(&format!("  fn {}\n", row.def_path));
    out.push_str(&format!("    origin   {}\n", row.origin));
    match &row.clause {
        Some(clause) => {
            out.push_str(&format!("    clause   #{} `{clause}`\n", row.contract_index));
        }
        None => out.push_str(&format!(
            "    clause   #{} (spelling unavailable from compiler preparation)\n",
            row.contract_index
        )),
    }
    out.push_str(&format!("    theorem  `{}`\n", row.theorem));
    match &row.detail {
        Some(detail) => out.push_str(&format!("    verdict  {} ({detail})\n", row.verdict)),
        None => out.push_str(&format!("    verdict  {}\n", row.verdict)),
    }
    match (&row.goal_clean, &row.elab_error) {
        (Some(goal), _) => out.push_str(&format!("    goal     {goal}\n")),
        (None, Some(reason)) => {
            out.push_str(&format!("    goal     (elaboration refused: {reason})\n"))
        }
        (None, None) => out.push_str("    goal     (absent)\n"),
    }
    out
}

fn render_denotation_row(row: &DenotationRow) -> String {
    let mut out = String::new();
    out.push_str(&format!("  fn {}\n", row.def_path));
    out.push_str(&format!("    clause   #{} {} ({})\n", row.contract_index, row.kind, row.source));
    match &row.clause {
        Some(clause) => out.push_str(&format!("    spelling `{clause}`\n")),
        None => out.push_str("    spelling (unavailable from typed query)\n"),
    }
    out.push_str(&format!("    authority {} / {}\n", row.authority, row.verdict));
    match (&row.goal_clean, &row.elab_error) {
        (Some(goal), None) => out.push_str(&format!("    denotes   {goal}\n")),
        (None, Some(reason)) => {
            out.push_str(&format!("    denotes   (elaboration refused: {reason})\n"));
        }
        _ => unreachable!("the parser enforces exactly one denotation outcome"),
    }
    out
}

fn render_units_human(units: &[UnitArtifact]) -> String {
    let mut out = String::new();
    out.push_str("targo trust spec --emit clean (compiler-authoritative, v6/D1)\n");
    for unit in units {
        let session_short: String = unit.session.chars().take(12).collect();
        out.push_str(&format!(
            "\ncrate {} (session {}…): {} zero-authority denotation(s), {} \
             kernel-graded goal(s)\n",
            unit.krate,
            session_short,
            unit.denotations.len(),
            unit.goals.len()
        ));
        for row in &unit.denotations {
            out.push('\n');
            out.push_str(&render_denotation_row(row));
        }
        for row in &unit.goals {
            out.push('\n');
            out.push_str(&render_goal_row(row));
        }
        if unit.goals.is_empty() && unit.denotations.is_empty() {
            out.push_str(
                "\n  (the verification session completed and sealed the artifact, but this crate \
                 contains no uncited function requires/ensures denotations and no graded \
                 cited-ensures goals.)\n",
            );
        }
    }
    out
}

/// Trim the hidden Cargo proof-unit identity subject (`cargo-target(...)`)
/// off a report crate/function name for HUMAN display. The full subject is
/// authoritative identity and stays in `--json`/report artifacts; here it
/// buries the one thing the reader needs (which function failed) under a
/// 500-character envelope. Purely lexical: no identity is re-derived, and a
/// name without the envelope prefix passes through unchanged.
fn strip_cargo_subject_prefix(name: &str) -> &str {
    if let Some(rest) = name.strip_prefix("cargo-target(") {
        if let Some(index) = rest.find(")::") {
            return &rest[index + ")::".len()..];
        }
    }
    name
}

/// The `package="..."` component of a hidden Cargo identity subject, for the
/// human crate label; the whole subject when the shape is not recognized.
fn human_crate_label(crate_name: &str) -> &str {
    if !crate_name.starts_with("cargo-target(") {
        return crate_name;
    }
    let Some(start) = crate_name.find("package=\"") else {
        return crate_name;
    };
    let rest = &crate_name[start + "package=\"".len()..];
    match rest.find('"') {
        Some(end) => &rest[..end],
        None => crate_name,
    }
}

/// One human line per obligation that kept the verified run from passing:
/// Failed / Unknown / Timeout rows, exactly as the sealed canonical report
/// records them. Proved, runtime-checked, and design-requirement rows are not
/// failures and are deliberately absent — this is a failure account, not a
/// report rendering (the spec surface suppresses those).
fn unfavorable_obligation_lines(report: &trust_types::JsonProofReport) -> Vec<String> {
    let mut lines = Vec::new();
    for function in &report.functions {
        for obligation in &function.obligations {
            let verdict = match &obligation.outcome {
                trust_types::ObligationOutcome::Failed { .. } => "FAILED".to_string(),
                trust_types::ObligationOutcome::Unknown { reason } => {
                    format!("UNKNOWN ({reason})")
                }
                trust_types::ObligationOutcome::Timeout { timeout_ms } => {
                    format!("TIMEOUT ({timeout_ms}ms)")
                }
                trust_types::ObligationOutcome::Proved { .. }
                | trust_types::ObligationOutcome::RuntimeChecked { .. }
                | trust_types::ObligationOutcome::DesignRequirement { .. } => continue,
                // `#[non_exhaustive]`: an outcome this build does not know is
                // DISCLOSED, never silently skipped — skipping would hide the
                // very row that failed the gate.
                other => format!("UNRECOGNIZED OUTCOME ({other:?})"),
            };
            let location = obligation
                .location
                .as_ref()
                .map(|span| format!(" @ {}:{}", span.file, span.line_start))
                .unwrap_or_default();
            lines.push(format!(
                "  {}: [{}] {} -> {verdict}{location}",
                strip_cargo_subject_prefix(&function.function),
                obligation.kind,
                obligation.description
            ));
        }
    }
    lines
}

/// Render the failing-run account from the sealed canonical report (when one
/// was sealed). A non-zero exit must never be silent: the spec surface
/// suppresses ordinary report rendering, so without this the strict gate's
/// verdict — which lives only in that report — would be invisible.
fn render_failed_run_account(sealed: Option<&trust_types::JsonProofReport>) -> String {
    let Some(report) = sealed else {
        return "targo trust spec: note: the verification run itself did not pass, and no \
                canonical report was sealed for this run — the failure happened before or \
                outside the verification walk (see the compiler/Cargo diagnostics above)"
            .to_string();
    };
    let mut out = String::new();
    let summary = &report.summary;
    out.push_str(&format!(
        "targo trust spec: note: the verification run itself did not pass; the rows above are \
         the compiler's canonical denotations and the goals the kernel graded before the \
         failure.\n\
         targo trust spec: strict-gate summary for crate {}: {} proved, {} failed, {} \
         runtime-checked, {} unknown, {} timed out of {} obligation(s)",
        human_crate_label(&report.crate_name),
        summary.total_proved,
        summary.total_failed,
        summary.total_runtime_checked,
        summary.total_unknown,
        summary.total_timed_out,
        summary.total_obligations,
    ));
    let lines = unfavorable_obligation_lines(report);
    if lines.is_empty() {
        out.push_str(
            "\ntargo trust spec: no obligation in the sealed report is unproved — the failure \
             is outside the obligation rows (coverage, proof-frontier exclusion, or compiler \
             exit; see the diagnostics above)",
        );
    } else {
        out.push_str(&format!(
            "\ntargo trust spec: {} obligation(s) did not reach a favorable outcome:",
            lines.len()
        ));
        for line in &lines {
            out.push('\n');
            out.push_str(line);
        }
    }
    out
}

fn spec_usage() -> &'static str {
    "targo trust spec --emit clean [-p <pkg>] [check options]\n\
     \n\
     Prints canonical Clean propositions from a live verified compilation:\n\
     zero-authority/ungraded denotations for uncited function clauses, and the\n\
     distinct goals the kernel actually graded for cited `ensures` clauses.\n\
     The command never re-elaborates offline and REFUSES when no sealed session\n\
     artifact exists.\n\
     \n\
     Options:\n\
     \x20 --emit clean   required; the only supported canonical spec surface today\n\
     \x20 --json         print the raw artifact rows (JSONL) instead of the human view\n\
     \x20 <everything else> is forwarded to the underlying `targo trust check`\n"
}

/// Entry point for `targo trust spec`.
pub(crate) fn run_spec_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", spec_usage());
        return ExitCode::SUCCESS;
    }
    let parsed = match parse_spec_args(args) {
        Ok(parsed) => parsed,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(2);
        }
    };
    // A FRESH directory per run: the read below can only be satisfied by an
    // artifact THIS compiler session wrote and sealed.
    let session_dir = match tempfile::Builder::new().prefix("targo-trust-spec-").tempdir() {
        Ok(dir) => dir,
        Err(error) => {
            eprintln!("targo trust spec: could not provision a session directory: {error}");
            return ExitCode::from(2);
        }
    };
    let session_path = match session_dir.path().canonicalize() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("targo trust spec: could not canonicalize the session directory: {error}");
            return ExitCode::from(2);
        }
    };
    let Some(session_path_str) = session_path.to_str() else {
        eprintln!("targo trust spec: session directory path is not valid Unicode");
        return ExitCode::from(2);
    };

    // Drive the check-equivalent verified compilation with the emission knob.
    // Ordinary report rendering is suppressed (no report artifacts were
    // requested); compiler and verifier diagnostics still stream, which is
    // what the failing-build debugging case needs.
    let mut check_args = parsed.forwarded.clone();
    check_args.push("--spec-emit-dir".to_string());
    check_args.push(session_path_str.to_string());
    // Capture the sealed canonical report so a FAILING run can say why it
    // failed: ordinary report rendering is suppressed on this surface, and the
    // strict gate's verdict lives only in that report — without this capture a
    // gate failure exits non-zero with no visible cause (the fail-silent
    // class). Capturing is observational; verdicts and exit codes are the
    // check pipeline's alone.
    let mut sealed_report: Option<trust_types::JsonProofReport> = None;
    let mut capture_sealed_report =
        |live: &crate::report::LiveCanonicalReport| -> Result<(), String> {
            sealed_report = Some(live.for_spec_gate_disclosure().clone());
            Ok(())
        };
    let check_exit = crate::run_subcommand_with_live_report(
        Subcommand::Check,
        &check_args,
        Some(&mut capture_sealed_report),
        false,
    );

    // Fail-closed read-back: refusal wins over every other outcome.
    let units = match read_spec_artifacts(&session_path) {
        Ok(units) => units,
        Err(refusal) => {
            eprintln!("{}", refusal.render());
            return ExitCode::from(2);
        }
    };

    if parsed.json {
        for unit in &units {
            for row in &unit.goals {
                println!("{}", row.raw);
            }
            for row in &unit.denotations {
                println!("{}", row.raw);
            }
        }
    } else {
        print!("{}", render_units_human(&units));
    }

    // The proposition rows print even when the verified build failed — that is the
    // debugging case v6/D1 exists for — but the failure still fails, and it
    // says why (from the sealed canonical report, never a local re-derivation).
    if check_exit != ExitCode::SUCCESS {
        eprintln!("{}", render_failed_run_account(sealed_report.as_ref()));
        return check_exit;
    }
    check_exit
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn emit_clean_is_required_and_the_refusal_carries_the_fix() {
        let error = parse_spec_args(&args(&["-p", "demo"])).expect_err("missing --emit");
        assert!(error.contains("--emit clean"), "{error}");

        let error =
            parse_spec_args(&args(&["--emit", "trust-ir"])).expect_err("wrong emit surface");
        assert!(error.contains("not a supported spec surface"), "{error}");
        assert!(error.contains("--emit clean"), "options must be listed: {error}");
        assert!(error.contains("trust-dump=ir"), "options must be listed: {error}");
    }

    #[test]
    fn spec_owns_its_session_directory() {
        let error = parse_spec_args(&args(&["--emit", "clean", "--spec-emit-dir", "/tmp/x"]))
            .expect_err("--spec-emit-dir is subcommand-provisioned");
        assert!(error.contains("provisioned by the subcommand"), "{error}");
        assert!(error.contains("targo trust check --spec-emit-dir"), "fix option: {error}");
    }

    #[test]
    fn package_selection_and_json_parse_and_forward() {
        let parsed = parse_spec_args(&args(&["--emit=clean", "--json", "-p", "demo"]))
            .expect("valid spec args");
        assert!(parsed.json);
        assert_eq!(parsed.forwarded, args(&["-p", "demo"]));
    }

    const GOAL_LINE: &str = r#"{"format":"trust-spec-clean","v":2,"row":"goal","crate":"demo","session":"abc123","def_path":"demo::caller","contract_index":1,"origin":"ensures-citation","clause":"ident(x) >= ident(x)","theorem":"u64_ge_refl","goal_clean":"∀ (x : UInt64), Nat.le (UInt64.toNat (demo_ident x)) (UInt64.toNat (demo_ident x))","elab_error":null,"verdict":"certified","detail":null}"#;
    const DENOTATION_LINE: &str = r#"{"format":"trust-spec-clean","v":2,"row":"denotation","crate":"demo","session":"abc123","def_path":"demo::plain","contract_index":0,"kind":"requires","source":"native","clause":"x <= x","goal_clean":"(x : UInt64) -> Nat.le (UInt64.toNat x) (UInt64.toNat x)","elab_error":null,"authority":"none","verdict":"ungraded"}"#;

    fn seal_line(goals: u64, denotations: u64) -> String {
        format!(
            r#"{{"format":"trust-spec-clean","v":2,"row":"session","crate":"demo","session":"abc123","goals":{goals},"denotations":{denotations}}}"#
        )
    }

    fn goal_value() -> serde_json::Value {
        serde_json::from_str(GOAL_LINE).expect("test goal JSON")
    }

    fn parse_goal_value(value: serde_json::Value) -> Result<UnitArtifact, SpecRefusal> {
        let line = serde_json::to_string(&value).expect("serialize test goal");
        parse_unit_artifact("demo.spec-clean.jsonl", &format!("{line}\n{}\n", seal_line(1, 0)))
    }

    fn malformed_goal_detail(value: serde_json::Value) -> String {
        match parse_goal_value(value).expect_err("mutated goal must refuse") {
            SpecRefusal::Malformed { detail, .. } => detail,
            other => panic!("expected malformed goal refusal, got {other:?}"),
        }
    }

    fn malformed_artifact_detail(contents: &str) -> String {
        match parse_unit_artifact("demo.spec-clean.jsonl", contents)
            .expect_err("mutated artifact must refuse")
        {
            SpecRefusal::Malformed { detail, .. } => detail,
            other => panic!("expected malformed artifact refusal, got {other:?}"),
        }
    }

    #[test]
    fn a_sealed_artifact_round_trips_byte_preserving() {
        let contents = format!("{GOAL_LINE}\n{DENOTATION_LINE}\n{}\n", seal_line(1, 1));
        let unit = parse_unit_artifact("demo.spec-clean.jsonl", &contents).expect("sealed unit");
        assert_eq!(unit.krate, "demo");
        assert_eq!(unit.goals.len(), 1);
        assert_eq!(unit.denotations.len(), 1);
        let row = &unit.goals[0];
        assert_eq!(row.contract_index, 1);
        assert_eq!(row.verdict, "certified");
        assert_eq!(row.theorem, "u64_ge_refl");
        // --json passthrough must reproduce the compiler's bytes, not a
        // re-serialization: the goal text is the authoritative payload.
        assert_eq!(row.raw, GOAL_LINE);
        assert!(row.goal_clean.as_deref().unwrap_or_default().contains("UInt64.toNat"));
        let denotation = &unit.denotations[0];
        assert_eq!(denotation.authority, "none");
        assert_eq!(denotation.verdict, "ungraded");
        assert_eq!(denotation.raw, DENOTATION_LINE);
    }

    #[test]
    fn goal_required_strings_reject_missing_wrong_null_and_empty_values() {
        for field in ["crate", "def_path", "origin", "theorem", "verdict"] {
            let mut missing = goal_value();
            missing.as_object_mut().expect("goal object").remove(field);
            assert_eq!(
                malformed_goal_detail(missing),
                format!("row missing `{field}`"),
                "missing {field} must refuse"
            );

            for wrong in [serde_json::Value::Null, serde_json::json!(17)] {
                let mut value = goal_value();
                value[field] = wrong;
                assert_eq!(
                    malformed_goal_detail(value),
                    format!("row field `{field}` is not a string"),
                    "non-string {field} must refuse"
                );
            }

            for empty in ["", " \t "] {
                let mut value = goal_value();
                value[field] = serde_json::json!(empty);
                assert_eq!(
                    malformed_goal_detail(value),
                    format!("row field `{field}` is empty"),
                    "empty {field} must refuse"
                );
            }
        }
    }

    #[test]
    fn goal_contract_index_is_required_and_must_be_a_u64() {
        let mut missing = goal_value();
        missing.as_object_mut().expect("goal object").remove("contract_index");
        assert_eq!(malformed_goal_detail(missing), "row missing integer `contract_index`");

        for wrong in [
            serde_json::Value::Null,
            serde_json::json!("1"),
            serde_json::json!(-1),
            serde_json::json!(1.5),
        ] {
            let mut value = goal_value();
            value["contract_index"] = wrong;
            assert_eq!(
                malformed_goal_detail(value),
                "row field `contract_index` is not an unsigned integer"
            );
        }
    }

    #[test]
    fn a_null_goal_clause_is_only_an_exact_preparation_refusal() {
        let reason = "compiler could not recover the canonical clause spelling";
        let mut refused = goal_value();
        refused["clause"] = serde_json::Value::Null;
        refused["goal_clean"] = serde_json::Value::Null;
        refused["elab_error"] = serde_json::json!(reason);
        refused["verdict"] = serde_json::json!("clause-outside-fragment");
        refused["detail"] = serde_json::json!(reason);
        let unit = parse_goal_value(refused.clone()).expect("explicit preparation refusal");
        assert!(unit.goals[0].clause.is_none());
        let rendered = render_goal_row(&unit.goals[0]);
        assert!(rendered.contains("#1 (spelling unavailable"), "{rendered}");

        let mut missing_clause = goal_value();
        missing_clause.as_object_mut().expect("goal object").remove("clause");
        assert_eq!(malformed_goal_detail(missing_clause), "row missing `clause`");

        for wrong in [serde_json::json!(17), serde_json::json!({"text": "clause"})] {
            let mut value = goal_value();
            value["clause"] = wrong;
            assert_eq!(
                malformed_goal_detail(value),
                "row field `clause` is neither a string nor null"
            );
        }

        let mut empty_clause = goal_value();
        empty_clause["clause"] = serde_json::json!(" \t ");
        assert_eq!(malformed_goal_detail(empty_clause), "goal row has an empty `clause` spelling");

        for (label, mutate, expected) in [
            (
                "goal present",
                (Some(serde_json::json!("unexpected goal")), None, None),
                "cannot carry `goal_clean`",
            ),
            ("error absent", (None, Some(serde_json::Value::Null), None), "nonempty `elab_error`"),
            (
                "wrong verdict",
                (None, None, Some(serde_json::json!("certified"))),
                "must have verdict `clause-outside-fragment`",
            ),
        ] {
            let mut value = refused.clone();
            if let Some(goal_clean) = mutate.0 {
                value["goal_clean"] = goal_clean;
            }
            if let Some(elab_error) = mutate.1 {
                value["elab_error"] = elab_error;
            }
            if let Some(verdict) = mutate.2 {
                value["verdict"] = verdict;
            }
            let detail = malformed_goal_detail(value);
            assert!(detail.contains(expected), "{label}: {detail}");
        }

        for bad_detail in [
            serde_json::Value::Null,
            serde_json::json!(""),
            serde_json::json!("a different refusal reason"),
        ] {
            let mut value = refused.clone();
            value["detail"] = bad_detail;
            assert!(
                malformed_goal_detail(value).contains("repeat its nonempty `elab_error`"),
                "null-clause detail must repeat the refusal reason"
            );
        }
    }

    #[test]
    fn goal_session_is_required_and_typed_but_direct_compiler_empty_is_valid() {
        let mut missing = goal_value();
        missing.as_object_mut().expect("goal object").remove("session");
        assert_eq!(malformed_goal_detail(missing), "row missing `session`");

        for wrong in [serde_json::Value::Null, serde_json::json!(17)] {
            let mut value = goal_value();
            value["session"] = wrong;
            assert_eq!(malformed_goal_detail(value), "row field `session` is not a string");
        }

        let goal = GOAL_LINE.replace(r#""session":"abc123""#, r#""session":"""#);
        let seal = seal_line(1, 0).replace(r#""session":"abc123""#, r#""session":"""#);
        let unit = parse_unit_artifact("demo.spec-clean.jsonl", &format!("{goal}\n{seal}\n"))
            .expect("an absent optional compiler session id is represented by a consistent empty string");
        assert!(unit.session.is_empty());
    }

    #[test]
    fn goal_nullable_fields_must_be_present_and_well_typed() {
        for field in ["goal_clean", "elab_error", "detail"] {
            let mut missing = goal_value();
            missing.as_object_mut().expect("goal object").remove(field);
            assert_eq!(
                malformed_goal_detail(missing),
                format!("row missing `{field}`"),
                "missing nullable field {field} must refuse"
            );

            let mut wrong = goal_value();
            wrong[field] = serde_json::json!({ "not": "a nullable string" });
            assert_eq!(
                malformed_goal_detail(wrong),
                format!("row field `{field}` is neither a string nor null"),
                "wrongly typed nullable field {field} must refuse"
            );
        }

        let mut refused = goal_value();
        refused["goal_clean"] = serde_json::Value::Null;
        refused["elab_error"] = serde_json::json!("clause is outside the elaborator fragment");
        refused["detail"] = serde_json::json!("compiler refusal detail");
        let unit = parse_goal_value(refused).expect("the opposite nullable arms are valid");
        assert!(unit.goals[0].goal_clean.is_none());
        assert!(unit.goals[0].elab_error.is_some());
        assert_eq!(unit.goals[0].detail.as_deref(), Some("compiler refusal detail"));
    }

    #[test]
    fn goal_result_requires_exactly_one_nonempty_payload() {
        for (label, goal_clean, elab_error, expected) in [
            ("both null", serde_json::Value::Null, serde_json::Value::Null, "exactly one nonempty"),
            (
                "both populated",
                serde_json::json!("goal"),
                serde_json::json!("error"),
                "exactly one nonempty",
            ),
            (
                "empty goal",
                serde_json::json!(" \t "),
                serde_json::Value::Null,
                "empty `goal_clean`",
            ),
            ("empty error", serde_json::Value::Null, serde_json::json!(""), "empty `elab_error`"),
        ] {
            let mut value = goal_value();
            value["goal_clean"] = goal_clean;
            value["elab_error"] = elab_error;
            let detail = malformed_goal_detail(value);
            assert!(detail.contains(expected), "{label}: {detail}");
        }
    }

    #[test]
    fn goal_tags_are_closed_to_compiler_schema_v2_spellings() {
        for origin in ["ensures-citation", "ensures-citation-deferred"] {
            let mut value = goal_value();
            value["origin"] = serde_json::json!(origin);
            parse_goal_value(value).unwrap_or_else(|error| {
                panic!("compiler-emitted origin {origin:?} must parse: {error:?}")
            });
        }
        for verdict in [
            "certified",
            "trusted",
            "session-tainted",
            "theorem-not-found",
            "declaration-not-theorem",
            "unsafe-theorem",
            "partial-theorem",
            "no-proof-term",
            "clause-outside-fragment",
            "statement-or-certification-rejected",
        ] {
            let mut value = goal_value();
            value["verdict"] = serde_json::json!(verdict);
            parse_goal_value(value).unwrap_or_else(|error| {
                panic!("compiler-emitted verdict {verdict:?} must parse: {error:?}")
            });
        }

        let mut unknown_origin = goal_value();
        unknown_origin["origin"] = serde_json::json!("future-citation-lane");
        assert_eq!(
            malformed_goal_detail(unknown_origin),
            "unknown goal origin `future-citation-lane`"
        );

        let mut unknown_verdict = goal_value();
        unknown_verdict["verdict"] = serde_json::json!("future-positive-verdict");
        assert_eq!(
            malformed_goal_detail(unknown_verdict),
            "unknown goal verdict `future-positive-verdict`"
        );
    }

    #[test]
    fn an_unknown_version_refuses_with_the_supported_one_named() {
        let line = GOAL_LINE.replace(r#""v":2"#, r#""v":3"#);
        let contents = format!("{line}\n{}\n", seal_line(1, 0));
        let refusal =
            parse_unit_artifact("demo.spec-clean.jsonl", &contents).expect_err("v=3 must refuse");
        match &refusal {
            SpecRefusal::UnsupportedVersion { version, .. } => assert_eq!(version, "3"),
            other => panic!("expected UnsupportedVersion, got {other:?}"),
        }
        assert!(refusal.render().contains("understands only version 2"), "{}", refusal.render());
    }

    #[test]
    fn a_missing_seal_refuses_as_an_incomplete_session() {
        let contents = format!("{GOAL_LINE}\n");
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("unsealed must refuse");
        assert!(matches!(refusal, SpecRefusal::Unsealed { .. }), "{refusal:?}");
        assert!(refusal.render().contains("COMPLETES"), "{}", refusal.render());
    }

    #[test]
    fn a_seal_count_mismatch_refuses_as_torn() {
        let contents = format!("{GOAL_LINE}\n{}\n", seal_line(2, 0));
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("count mismatch must refuse");
        assert!(
            matches!(refusal, SpecRefusal::Torn { sealed_goals: 2, counted_goals: 1, .. }),
            "{refusal:?}"
        );
    }

    #[test]
    fn schema_v2_rejects_unknown_members_on_every_row_kind() {
        let mut goal = goal_value();
        goal["future_goal_semantics"] = serde_json::json!(true);
        let goal = serde_json::to_string(&goal).expect("serialize goal mutation");
        assert_eq!(
            malformed_artifact_detail(&format!("{goal}\n{}\n", seal_line(1, 0))),
            "goal row has unknown field `future_goal_semantics`"
        );

        let mut denotation: serde_json::Value =
            serde_json::from_str(DENOTATION_LINE).expect("test denotation JSON");
        denotation["future_denotation_semantics"] = serde_json::json!(true);
        let denotation = serde_json::to_string(&denotation).expect("serialize denotation mutation");
        assert_eq!(
            malformed_artifact_detail(&format!("{denotation}\n{}\n", seal_line(0, 1))),
            "denotation row has unknown field `future_denotation_semantics`"
        );

        let mut seal: serde_json::Value =
            serde_json::from_str(&seal_line(0, 0)).expect("test seal JSON");
        seal["future_session_semantics"] = serde_json::json!(true);
        let seal = serde_json::to_string(&seal).expect("serialize seal mutation");
        assert_eq!(
            malformed_artifact_detail(&format!("{seal}\n")),
            "session row has unknown field `future_session_semantics`"
        );
    }

    #[test]
    fn duplicate_json_object_members_refuse_before_interpretation() {
        let duplicate_v = GOAL_LINE.replacen(r#""v":2"#, r#""v":2,"v":3"#, 1);
        let detail = malformed_artifact_detail(&format!("{duplicate_v}\n{}\n", seal_line(1, 0)));
        assert!(detail.contains("duplicate object member `v`"), "{detail}");

        let duplicate_authority = DENOTATION_LINE.replacen(
            r#""authority":"none""#,
            r#""authority":"none","authority":"kernel""#,
            1,
        );
        let detail =
            malformed_artifact_detail(&format!("{duplicate_authority}\n{}\n", seal_line(0, 1)));
        assert!(detail.contains("duplicate object member `authority`"), "{detail}");
    }

    #[test]
    fn blank_jsonl_rows_refuse_but_one_terminal_newline_is_not_a_row() {
        parse_unit_artifact(
            "demo.spec-clean.jsonl",
            &format!("{GOAL_LINE}\n{}\n", seal_line(1, 0)),
        )
        .expect("one ordinary terminal newline is valid");

        for (label, contents, line) in [
            ("middle", format!("{GOAL_LINE}\n\n{}\n", seal_line(1, 0)), 2),
            ("whitespace middle", format!("{GOAL_LINE}\n \t \n{}\n", seal_line(1, 0)), 2),
            ("trailing", format!("{GOAL_LINE}\n{}\n\n", seal_line(1, 0)), 3),
        ] {
            assert_eq!(
                malformed_artifact_detail(&contents),
                format!("blank JSONL row at line {line}"),
                "{label} blank row must refuse"
            );
        }
    }

    #[test]
    fn duplicate_goal_identity_refuses_even_when_rows_match() {
        let contents = format!("{GOAL_LINE}\n{GOAL_LINE}\n{}\n", seal_line(2, 0));
        let detail = malformed_artifact_detail(&contents);
        assert!(detail.contains("duplicate goal identity"), "{detail}");

        let second = GOAL_LINE.replace(r#""contract_index":1"#, r#""contract_index":2"#);
        let contents = format!("{GOAL_LINE}\n{second}\n{}\n", seal_line(2, 0));
        let unit = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect("contract index distinguishes two clauses on one function");
        assert_eq!(unit.goals.len(), 2);
    }

    #[test]
    fn a_denotation_cannot_claim_authority_or_a_positive_verdict() {
        for mutated in [
            DENOTATION_LINE.replace(r#""authority":"none""#, r#""authority":"kernel""#),
            DENOTATION_LINE.replace(r#""verdict":"ungraded""#, r#""verdict":"certified""#),
        ] {
            let contents = format!("{mutated}\n{}\n", seal_line(0, 1));
            let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
                .expect_err("a denotation promotion must refuse");
            assert!(matches!(refusal, SpecRefusal::Malformed { .. }), "{refusal:?}");
            assert!(refusal.render().contains("zero-authority"), "{}", refusal.render());
        }
    }

    #[test]
    fn denotation_and_seal_identities_cannot_be_empty() {
        for field in ["crate", "def_path"] {
            let mut denotation: serde_json::Value =
                serde_json::from_str(DENOTATION_LINE).expect("test denotation JSON");
            denotation[field] = serde_json::json!(" \t ");
            let denotation =
                serde_json::to_string(&denotation).expect("serialize denotation mutation");
            assert_eq!(
                malformed_artifact_detail(&format!("{denotation}\n{}\n", seal_line(0, 1))),
                format!("row field `{field}` is empty")
            );
        }

        let seal = seal_line(0, 0).replace(r#""crate":"demo""#, r#""crate":"""#);
        assert_eq!(malformed_artifact_detail(&format!("{seal}\n")), "row field `crate` is empty");
    }

    #[test]
    fn duplicate_denotation_identity_refuses_even_when_rows_match() {
        let contents = format!("{DENOTATION_LINE}\n{DENOTATION_LINE}\n{}\n", seal_line(0, 2));
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("duplicate identity must refuse before the seal can bless the count");
        assert!(matches!(refusal, SpecRefusal::Malformed { .. }), "{refusal:?}");
        assert!(refusal.render().contains("duplicate denotation identity"));
    }

    #[test]
    fn the_session_seal_is_terminal() {
        let contents = format!("{}\n{DENOTATION_LINE}\n", seal_line(0, 1));
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("data after the completion seal must refuse");
        assert!(matches!(refusal, SpecRefusal::Malformed { .. }), "{refusal:?}");
        assert!(refusal.render().contains("terminal session seal"));
    }

    #[test]
    fn an_unknown_row_kind_refuses_instead_of_being_dropped() {
        let unknown = DENOTATION_LINE.replace(r#""row":"denotation""#, r#""row":"future""#);
        let contents = format!("{unknown}\n{}\n", seal_line(0, 0));
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("an unknown row kind must not disappear from the sealed inventory");
        assert!(matches!(refusal, SpecRefusal::Malformed { .. }), "{refusal:?}");
        assert!(refusal.render().contains("unknown row kind"));
    }

    #[test]
    fn a_row_identity_must_match_its_session_seal() {
        let foreign = DENOTATION_LINE.replace(r#""session":"abc123""#, r#""session":"other""#);
        let contents = format!("{foreign}\n{}\n", seal_line(0, 1));
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("a foreign row cannot borrow this unit's completion seal");
        assert!(matches!(refusal, SpecRefusal::Malformed { .. }), "{refusal:?}");
        assert!(refusal.render().contains("disagrees with the session seal"));
    }

    #[test]
    fn a_denotation_refusal_is_counted_and_requires_a_reason() {
        let refused = DENOTATION_LINE
            .replace(r#""clause":"x <= x""#, r#""clause":null"#)
            .replace(
                r#""goal_clean":"(x : UInt64) -> Nat.le (UInt64.toNat x) (UInt64.toNat x)""#,
                r#""goal_clean":null"#,
            )
            .replace(
                r#""elab_error":null"#,
                r#""elab_error":"compiler contract predicate has no query-owned typed proposition""#,
            );
        let contents = format!("{refused}\n{}\n", seal_line(0, 1));
        let unit = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect("an explicit refusal is a complete inventory row");
        assert!(unit.denotations[0].goal_clean.is_none());
        assert!(unit.denotations[0].elab_error.is_some());

        let empty_clause = refused.replace(r#""clause":null"#, r#""clause":" \t ""#);
        let contents = format!("{empty_clause}\n{}\n", seal_line(0, 1));
        assert_eq!(
            malformed_artifact_detail(&contents),
            "denotation row has an empty `clause` spelling"
        );

        let reason_dropped = refused.replace(
            r#""elab_error":"compiler contract predicate has no query-owned typed proposition""#,
            r#""elab_error":null"#,
        );
        let contents = format!("{reason_dropped}\n{}\n", seal_line(0, 1));
        assert!(matches!(
            parse_unit_artifact("demo.spec-clean.jsonl", &contents),
            Err(SpecRefusal::Malformed { .. })
        ));

        let empty_reason = refused.replace(
            r#""elab_error":"compiler contract predicate has no query-owned typed proposition""#,
            r#""elab_error":"   ""#,
        );
        let contents = format!("{empty_reason}\n{}\n", seal_line(0, 1));
        assert!(matches!(
            parse_unit_artifact("demo.spec-clean.jsonl", &contents),
            Err(SpecRefusal::Malformed { .. })
        ));

        let empty_goal = DENOTATION_LINE.replace(
            r#""goal_clean":"(x : UInt64) -> Nat.le (UInt64.toNat x) (UInt64.toNat x)""#,
            r#""goal_clean":"   ""#,
        );
        let contents = format!("{empty_goal}\n{}\n", seal_line(0, 1));
        assert!(matches!(
            parse_unit_artifact("demo.spec-clean.jsonl", &contents),
            Err(SpecRefusal::Malformed { .. })
        ));
    }

    #[test]
    fn an_empty_session_directory_is_the_no_artifact_refusal() {
        let dir = tempfile::tempdir().expect("tempdir");
        let refusal = read_spec_artifacts(dir.path()).expect_err("no files must refuse");
        assert_eq!(refusal, SpecRefusal::NoArtifact);
        let rendered = refusal.render();
        // v7/D3: the refusal must carry the fix, with options.
        assert!(rendered.contains("compiler-authoritative"), "{rendered}");
        assert!(rendered.contains("./x.py build"), "{rendered}");
        assert!(rendered.contains("fix the build errors"), "{rendered}");
        assert!(rendered.contains("-Ztrust-dump=spec-clean:"), "{rendered}");
    }

    fn obligation_row(
        kind: &str,
        description: &str,
        outcome: trust_types::ObligationOutcome,
    ) -> trust_types::ObligationReport {
        trust_types::ObligationReport {
            obligation_id: None,
            description: description.to_string(),
            kind: kind.to_string(),
            proof_level: trust_types::ProofLevel::L1Functional,
            location: Some(trust_types::SourceSpan {
                file: "src/main.rs".to_string(),
                line_start: 9,
                col_start: 1,
                line_end: 9,
                col_end: 2,
            }),
            outcome,
            solver: "clean-kernel-citation".to_string(),
            time_ms: 0,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    #[test]
    fn a_failing_run_account_names_each_unfavorable_obligation() {
        let function = trust_types::FunctionProofReport {
            function: "demo::caller".to_string(),
            summary: trust_types::FunctionSummary {
                total_obligations: 3,
                proved: 1,
                runtime_checked: 0,
                failed: 1,
                unknown: 1,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 0,
                max_proof_level: Some(trust_types::ProofLevel::L1Functional),
                verdict: trust_types::FunctionVerdict::Inconclusive,
            },
            obligations: vec![
                obligation_row(
                    "postcondition",
                    "postcondition",
                    trust_types::ObligationOutcome::Proved {
                        strength: trust_types::ProofStrength::smt_unsat_certified(),
                    },
                ),
                obligation_row(
                    "unsupported_mir",
                    "unsupported MIR `SpecEnsuresUnparseable`",
                    trust_types::ObligationOutcome::Unknown {
                        reason: "unsupported MIR obligations cannot carry proved outcomes"
                            .to_string(),
                    },
                ),
                obligation_row(
                    "assertion",
                    "assertion may fail",
                    trust_types::ObligationOutcome::Failed { counterexample: None },
                ),
            ],
        };
        let report = trust_types::JsonProofReport {
            metadata: trust_types::ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "test".to_string(),
                timestamp: String::new(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "demo".to_string(),
            summary: trust_types::CrateSummary {
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 1,
                functions_inconclusive: 0,
                total_obligations: 3,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 1,
                total_unknown: 1,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: Vec::new(),
                verdict: trust_types::CrateVerdict::HasViolations,
            },
            functions: vec![function],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        };
        let lines = unfavorable_obligation_lines(&report);
        assert_eq!(lines.len(), 2, "{lines:?}");
        assert!(lines[0].contains("UNKNOWN (unsupported MIR obligations"), "{}", lines[0]);
        assert!(lines[0].contains("demo::caller"), "{}", lines[0]);
        assert!(lines[0].contains("src/main.rs:9"), "{}", lines[0]);
        assert!(lines[1].contains("FAILED"), "{}", lines[1]);
        // The account renders the summary AND the rows; a proved row never
        // appears as a failure.
        let account = render_failed_run_account(Some(&report));
        assert!(account.contains("did not pass"), "{account}");
        assert!(account.contains("2 obligation(s) did not reach a favorable outcome"), "{account}");
        assert!(!account.contains("postcondition -> "), "{account}");
    }

    #[test]
    fn cargo_identity_subjects_trim_for_display_only() {
        let subject = r#"cargo-target(package_id="path+file:///w/demo#0.1.0",package="demo",kind=["bin"],target="demo")"#;
        assert_eq!(strip_cargo_subject_prefix(&format!("{subject}::demo::caller")), "demo::caller");
        assert_eq!(human_crate_label(subject), "demo");
        // Unrecognized shapes pass through UNCHANGED — trimming must never
        // invent a name.
        assert_eq!(strip_cargo_subject_prefix("demo::caller"), "demo::caller");
        assert_eq!(human_crate_label("demo"), "demo");
        assert_eq!(
            human_crate_label("cargo-target(no package key)"),
            "cargo-target(no package key)"
        );
    }

    #[test]
    fn a_failing_run_without_a_sealed_report_says_so() {
        let account = render_failed_run_account(None);
        assert!(account.contains("did not pass"), "{account}");
        assert!(account.contains("no canonical report was sealed"), "{account}");
    }

    #[test]
    fn sealed_files_in_a_directory_are_read_and_sorted() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("b_unit-0000000000000002.spec-clean.jsonl"),
            format!("{}\n", seal_line(0, 0)),
        )
        .expect("write b");
        std::fs::write(
            dir.path().join("a_unit-0000000000000001.spec-clean.jsonl"),
            format!("{GOAL_LINE}\n{DENOTATION_LINE}\n{}\n", seal_line(1, 1)),
        )
        .expect("write a");
        // A non-artifact file is ignored rather than parsed.
        std::fs::write(dir.path().join("notes.txt"), "not an artifact").expect("write noise");
        let units = read_spec_artifacts(dir.path()).expect("both units sealed");
        assert_eq!(units.len(), 2);
        assert_eq!(units[0].goals.len(), 1, "lexicographic file order");
        assert_eq!(units[0].denotations.len(), 1);
        assert_eq!(units[1].goals.len(), 0);
        let human = render_units_human(&units);
        assert!(human.contains("1 kernel-graded goal(s)"), "{human}");
        assert!(
            human.contains("contains no uncited function"),
            "empty unit is reported honestly: {human}"
        );
    }
}
