// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The NON-EXPORTABLE NOTICE — what a library crate writes for a Clean-origin
//! def whose verdict cannot leave the crate.**
//!
//! # The defect this closes
//!
//! The rmeta encoder demands one `trust_clean_verdict_digest` row for EVERY
//! local Clean-origin def, regardless of visibility (row-absence is how an
//! importer recognises ordinary Rust, so skipping a row would fail OPEN — I7
//! risk R1). Two classes of def are admitted by the LOCAL gate and still have
//! no certificate the wire can carry:
//!
//! * a def whose [`Faithful`](crate::gate::Faithful) was earned by
//!   [`FaithfulnessMethod::PerEquationDefeq`] or
//!   [`FaithfulnessMethod::WellFoundedFunctionalDefeq`] — deliberately no wire
//!   tag ([`crate::admission::mint_encoded_digest_for_export`]'s R1/R2
//!   accounting);
//! * a def that calls a Rust `fn` of its own crate
//!   ([`CleanOriginShape::RustCallChain`]) — the importer's Clean environment
//!   has no table of the exporter's Rust callees to re-plan against.
//!
//! Until this module, the export provider answered both with a FATAL, so the
//! documented scope ("a cross-crate call refuses") was measured wider than
//! documented: the crate that merely DEFINED such a def — in a private module,
//! used only internally, or only in proof position — could not be built as a
//! library at all (wf1 probes 36b/36d/18b/18c/18d, 2026-09-15). Recursion and
//! the whole Lean→Rust edge were bin-crate-only.
//!
//! # What a notice is, and what it is NOT
//!
//! A notice is the row the exporter writes INSTEAD of a certificate. It says
//! one thing: *this def exists, and no certificate for it crosses this
//! boundary*. It is **not evidence**:
//!
//! * it has its own magic ([`NON_EXPORTABLE_NOTICE_MAGIC`]), so
//!   [`VerdictDigest::decode`](crate::admission::VerdictDigest::decode)
//!   refuses it as `NotAVerdictDigest` — an importer that does not know about
//!   notices fails closed, never open;
//! * there is NO conversion from a notice to a
//!   [`VerdictDigest`](crate::admission::VerdictDigest), a
//!   [`Readmitted`](crate::admission::Readmitted) or any other permission, and
//!   the only thing an importer can do with a recognised notice is REFUSE with
//!   [`NonExportableNotice::import_note`];
//! * it invents no wire tag for the unspellable evidence. The evidence form
//!   travels as DIAGNOSTIC TEXT only (the `Debug` name of the method), is never
//!   parsed back into a [`FaithfulnessMethod`], and nothing branches on it.
//!   Spelling `WellFoundedFunctionalDefeq` as a certificate remains the
//!   reviewed format change the admission docs describe, landing WITH the
//!   fields that judgment rests on.
//!
//! The row is still PRESENT for every registry def, so I7 risk R1 is
//! unchanged: a listed def with no row is still a refusal, and a def can never
//! be demoted to "ordinary Rust" by omission.
//!
//! # Tamper accounting
//!
//! A notice is a claim anyone with write access to the rmeta could have
//! written, like every other wire byte. Deleting it leaves a listed def with
//! no row (refused). Corrupting it refuses ([`NoticeDecodeRefusal`]).
//! REPLACING it with a forged certificate buys nothing a forged certificate
//! did not already buy: the importer still re-plans, re-gates the decoded body
//! under its own kernel and compares the locally OBSERVED method with the wire
//! tag — and no wire tag names either unspellable method, so that comparison
//! cannot succeed for such a body. Forging a notice over an honest certificate
//! only turns a working import into a refusal.

use crate::emit::{CleanOriginPlan, CleanOriginShape};
use crate::gate::FaithfulnessMethod;

/// Magic prefix of a non-exportable notice. Deliberately NOT the verdict
/// digest's `TVDG`: the two records must be unconfusable from their first four
/// bytes, in both directions.
pub const NON_EXPORTABLE_NOTICE_MAGIC: [u8; 4] = *b"TVNX";

/// The one notice format. CHECKED, not advisory — an unknown version refuses.
pub const NON_EXPORTABLE_NOTICE_FORMAT_V1: u8 = 1;

const REASON_UNSPELLABLE_FAITHFULNESS: u8 = 1;
const REASON_RUST_CALLEES: u8 = 2;

/// Why a Clean-origin def has no exportable certificate.
///
/// A REFUSAL reason, never evidence: nothing downstream of a recognised notice
/// does anything but refuse, so a forged reason can change only which
/// paragraph of explanation the user reads.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum NonExportableReason {
    /// The local gate admitted the def by an evidence form the certificate
    /// wire format deliberately has no tag for.
    UnspellableFaithfulness {
        /// The `Debug` rendering of the [`FaithfulnessMethod`], as DIAGNOSTIC
        /// TEXT. Never parsed back; see the module docs.
        evidence_form: String,
    },
    /// The def calls a Rust `fn` of its defining crate, and the importer has
    /// no table of those callees to re-plan the def against.
    RustCallees,
}

/// The row a library crate exports for a Clean-origin def that may be DEFINED
/// and used there but never called from another crate.
///
/// # Constructors — sealed evidence in, or wire bytes in
///
/// * [`crate::admission::ExportDigestRefusal::non_exportable_notice`] — from
///   the export seam's own refusal, and ONLY for
///   `DigestMintRefusal::UnencodableFaithfulness`, i.e. only after the seam
///   re-earned a fresh `Faithful` against the body being serialized and found
///   its method unspellable. Every other export refusal stays a refusal.
/// * [`Self::for_rust_call_chain`] — from a sealed [`CleanOriginPlan`] whose
///   shape really is a Rust call chain.
/// * [`Self::recognize`] — wire bytes in, CLAIM out.
///
/// There is no constructor from a bare name, so the compiler cannot mark an
/// arbitrary def non-exportable to get a library past the export seam.
///
/// ```compile_fail,E0451
/// let forged = trust_clean_origin::NonExportableNotice {
///     decl: String::new(),
///     reason: trust_clean_origin::NonExportableReason::RustCallees,
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonExportableNotice {
    decl: String,
    reason: NonExportableReason,
}

impl NonExportableNotice {
    /// Crate-private: the export seam's route (see the type docs).
    pub(crate) fn unspellable_faithfulness(decl: &str, method: FaithfulnessMethod) -> Self {
        Self {
            decl: decl.to_owned(),
            reason: NonExportableReason::UnspellableFaithfulness {
                evidence_form: format!("{method:?}"),
            },
        }
    }

    /// The notice for a def planned as a [`CleanOriginShape::RustCallChain`],
    /// or `None` for every other shape — those either export a real
    /// certificate or refuse at the export seam, exactly as before.
    ///
    /// Takes the sealed plan, not a name: holding a `CleanOriginPlan` is
    /// evidence the declaration is kernel-checked with a total carrier, and
    /// the shape is read from it rather than asserted by the caller.
    #[must_use]
    pub fn for_rust_call_chain(plan: &CleanOriginPlan) -> Option<Self> {
        match plan.shape() {
            CleanOriginShape::RustCallChain { .. } => Some(Self {
                decl: plan.name().to_owned(),
                reason: NonExportableReason::RustCallees,
            }),
            _ => None,
        }
    }

    /// The declaration the notice is about (diagnostic rendering).
    #[must_use]
    pub fn decl(&self) -> &str {
        &self.decl
    }

    /// Why no certificate was exported.
    #[must_use]
    pub fn reason(&self) -> &NonExportableReason {
        &self.reason
    }

    /// Encode to the versioned wire format.
    ///
    /// Layout (all integers little-endian, strings `u32` byte-length + UTF-8):
    ///
    /// ```text
    /// magic "TVNX" · format u8 · decl · reason u8
    /// · [reason 1 only: evidence-form text]
    /// ```
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(16 + self.decl.len());
        out.extend_from_slice(&NON_EXPORTABLE_NOTICE_MAGIC);
        out.push(NON_EXPORTABLE_NOTICE_FORMAT_V1);
        put_str(&mut out, &self.decl);
        match &self.reason {
            NonExportableReason::UnspellableFaithfulness { evidence_form } => {
                out.push(REASON_UNSPELLABLE_FAITHFULNESS);
                put_str(&mut out, evidence_form);
            }
            NonExportableReason::RustCallees => out.push(REASON_RUST_CALLEES),
        }
        out
    }

    /// Is this digest-table row a non-exportable notice?
    ///
    /// * `None` — the bytes do not begin with the notice magic. The caller
    ///   proceeds to [`VerdictDigest::decode`](crate::admission::VerdictDigest::decode),
    ///   which fail-closes on everything that is not a whole digest.
    /// * `Some(Ok(notice))` — a whole, well-formed notice. The ONLY correct
    ///   consumer action is to refuse the import with [`Self::import_note`].
    /// * `Some(Err(_))` — the magic matched and the rest did not parse whole.
    ///   Also a refusal: a damaged notice is never reinterpreted as a digest.
    ///
    /// No outcome of this function admits anything.
    #[must_use]
    pub fn recognize(bytes: &[u8]) -> Option<Result<Self, NoticeDecodeRefusal>> {
        let magic = bytes.get(..NON_EXPORTABLE_NOTICE_MAGIC.len())?;
        if magic != NON_EXPORTABLE_NOTICE_MAGIC {
            return None;
        }
        Some(Self::decode_after_magic(bytes))
    }

    fn decode_after_magic(bytes: &[u8]) -> Result<Self, NoticeDecodeRefusal> {
        let mut reader = Reader { bytes, at: NON_EXPORTABLE_NOTICE_MAGIC.len() };
        let format = reader.u8("format version")?;
        if format != NON_EXPORTABLE_NOTICE_FORMAT_V1 {
            return Err(NoticeDecodeRefusal::UnknownFormatVersion {
                found: format,
                supported: NON_EXPORTABLE_NOTICE_FORMAT_V1,
            });
        }
        let decl = reader.non_empty_str("decl")?;
        let reason = match reader.u8("reason")? {
            REASON_UNSPELLABLE_FAITHFULNESS => NonExportableReason::UnspellableFaithfulness {
                evidence_form: reader.non_empty_str("evidence form")?,
            },
            REASON_RUST_CALLEES => NonExportableReason::RustCallees,
            other => {
                return Err(NoticeDecodeRefusal::Malformed {
                    field: "reason",
                    detail: format!(
                        "unknown reason tag {other}; this reader knows \
                         {REASON_UNSPELLABLE_FAITHFULNESS} (faithfulness evidence without a \
                         wire spelling) and {REASON_RUST_CALLEES} (Rust callees)"
                    ),
                });
            }
        };
        if reader.at != reader.bytes.len() {
            return Err(NoticeDecodeRefusal::TrailingBytes {
                count: reader.bytes.len() - reader.at,
            });
        }
        Ok(Self { decl, reason })
    }

    /// The v7/D3 note an IMPORTER shows when a crate tries to call this def:
    /// what was refused, why, and the options.
    #[must_use]
    pub fn import_note(&self) -> String {
        let decl = &self.decl;
        match &self.reason {
            NonExportableReason::UnspellableFaithfulness { evidence_form } => format!(
                "`{decl}` is callable inside the crate that defines it — the faithfulness gate \
                 admitted its emitted body there, by {evidence_form} — but that evidence form \
                 has no wire tag in the Clean-origin certificate format yet. It rests on facts \
                 taken in the defining crate's own Clean environment (a per-equation or \
                 functional-layer judgment, the declaration's own decrease proofs, an \
                 axiom-closure audit) that the certificate has no field for, and spelling it \
                 as whole-term definitional equality or induction would tell this crate a \
                 judgment happened that never did. The defining crate therefore exported a \
                 non-exportable notice instead of a certificate, and without a certificate \
                 this compiler serves no body for `{decl}`: it cannot be called, \
                 const-evaluated or linked from here. This is a measured boundary of the \
                 compiler, not a rule about what you may write (ruling v7/D2).\n\
                 options:\n\
                 - call `{decl}` from an ordinary `pub fn` in its defining crate and call \
                   that wrapper from here — the wrapper is compiled where the local gate \
                   already admitted `{decl}` (keep the wrapper non-generic and without \
                   `#[inline]`, or its body is instantiated in this crate and lands here \
                   again);\n\
                 - restate `{decl}` in a shape whose evidence has a wire tag: a \
                   non-recursive body, or a structural recursion the induction lane proves \
                   — both export today;\n\
                 - keep `{decl}` proof-only and cite it from theorems and contracts in its \
                   defining crate, which needs no certificate."
            ),
            NonExportableReason::RustCallees => format!(
                "`{decl}` is callable inside the crate that defines it, but it calls a Rust \
                 `fn` of that crate, and a certificate for it cannot be re-admitted here: \
                 this crate's Clean environment has no table of the defining crate's Rust \
                 callees to re-elaborate `{decl}` against (that wire is a later increment of \
                 the Lean-calls-Rust lane). The defining crate therefore exported a \
                 non-exportable notice instead of a certificate, and without a certificate \
                 this compiler serves no body for `{decl}`: it cannot be called, \
                 const-evaluated or linked from here. This is a measured boundary of the \
                 compiler, not a rule about what you may write (ruling v7/D2).\n\
                 options:\n\
                 - call `{decl}` from an ordinary `pub fn` in its defining crate and call \
                   that wrapper from here (keep the wrapper non-generic and without \
                   `#[inline]`, or its body is instantiated in this crate and lands here \
                   again);\n\
                 - restate `{decl}` without the Rust callee (a wrapping op, a select, a \
                   projection …), which IS exportable;\n\
                 - keep `{decl}` proof-only and cite it from a contract in its defining \
                   crate instead of calling it across crates."
            ),
        }
    }

    /// The v7/D3 note an IMPORTER shows when it cannot re-admit a DIFFERENT,
    /// otherwise exportable def (`sibling`) of the same defining crate BECAUSE
    /// of this one. `Some` only for [`NonExportableReason::RustCallees`].
    ///
    /// Readmission re-elaborates ALL of the defining crate's island sources in
    /// a fresh session. A Rust callee is a compiler-declared constant of the
    /// DEFINING crate's environment (`declare_rust_callees` in
    /// `trust-certify`), never island text, and the importer has no
    /// table to declare it from — so islands that contain a Rust-calling def
    /// do not elaborate on the importer's side at all, and every certificate
    /// of that crate refuses. Without this note that refusal reads as kernel
    /// skew ("the islands no longer elaborate under this compiler's Clean
    /// kernel"), which sends the user to rebuild a dependency that is fine.
    ///
    /// A well-founded / per-equation def is pure Clean text and re-elaborates
    /// anywhere, so it never blocks a sibling: `None`.
    ///
    /// Still a REFUSAL reason only: the caller is already on a fatal path, and
    /// a forged notice can change only which explanation the user reads.
    #[must_use]
    pub fn sibling_import_note(&self, sibling: &str) -> Option<String> {
        let decl = &self.decl;
        match &self.reason {
            NonExportableReason::UnspellableFaithfulness { .. } => None,
            NonExportableReason::RustCallees => Some(format!(
                "re-admitting `{sibling}` means re-elaborating ALL of its defining crate's \
                 `clean {{ … }}` islands under this compiler's kernel, and those islands also \
                 declare `{decl}`, which calls a Rust `fn` of that crate. A Rust callee is a \
                 constant the compiler declares in the DEFINING crate's Clean environment, \
                 never island text, and this crate has no table of those callees to declare \
                 it from (that wire is a later increment of the Lean-calls-Rust lane). The \
                 islands therefore do not elaborate here, and no certificate from that crate \
                 can be re-admitted — `{sibling}`'s included, although `{sibling}` itself \
                 calls no Rust. This is a measured boundary of the compiler, not a rule about \
                 what you may write (ruling v7/D2), and it is NOT kernel skew: rebuilding the \
                 dependency will not change it.\n\
                 options:\n\
                 - call `{sibling}` from an ordinary `pub fn` in its defining crate and call \
                   that wrapper from here (keep the wrapper non-generic and without \
                   `#[inline]`, or its body is instantiated in this crate and lands here \
                   again);\n\
                 - move the defs you call across crates into a crate whose islands call no \
                   Rust `fn` — such a crate's islands re-elaborate anywhere;\n\
                 - restate `{decl}` without the Rust callee (a wrapping op, a select, a \
                   projection …), which makes every certificate of its crate importable \
                   again."
            )),
        }
    }
}

fn put_str(out: &mut Vec<u8>, text: &str) {
    // Names and an enum variant's `Debug` rendering; a >4 GiB field is not a
    // state either constructor can produce.
    let len = u32::try_from(text.len()).expect("a notice field exceeds u32 bytes");
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(text.as_bytes());
}

/// A cursor over notice bytes. Same discipline as the digest reader: every
/// read checks the remaining length FIRST, so a truncated or hostile input
/// refuses with a named field instead of panicking or over-allocating.
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize, field: &'static str) -> Result<&'a [u8], NoticeDecodeRefusal> {
        let remaining = self.bytes.len() - self.at;
        if remaining < n {
            return Err(NoticeDecodeRefusal::Truncated { field, needed: n, remaining });
        }
        let slice = &self.bytes[self.at..self.at + n];
        self.at += n;
        Ok(slice)
    }

    fn u8(&mut self, field: &'static str) -> Result<u8, NoticeDecodeRefusal> {
        Ok(self.take(1, field)?[0])
    }

    fn non_empty_str(&mut self, field: &'static str) -> Result<String, NoticeDecodeRefusal> {
        let len = self.take(4, field)?;
        let len = u32::from_le_bytes([len[0], len[1], len[2], len[3]]) as usize;
        let bytes = self.take(len, field)?;
        let text = std::str::from_utf8(bytes).map_err(|_| {
            NoticeDecodeRefusal::Malformed { field, detail: "not valid UTF-8".to_owned() }
        })?;
        if text.is_empty() {
            return Err(NoticeDecodeRefusal::Malformed {
                field,
                detail: "empty; this field names something and an unnameable notice cannot \
                         be reported"
                    .to_owned(),
            });
        }
        Ok(text.to_owned())
    }
}

/// Why bytes that begin with the notice magic were not a whole notice.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum NoticeDecodeRefusal {
    /// The format version is not one this reader knows.
    UnknownFormatVersion {
        /// The version tag found.
        found: u8,
        /// The format version this reader supports.
        supported: u8,
    },
    /// The input ended inside a field.
    Truncated {
        /// The field being read when the input ran out.
        field: &'static str,
        /// Bytes the field needed.
        needed: usize,
        /// Bytes that were left.
        remaining: usize,
    },
    /// A field was present but not well-formed.
    Malformed {
        /// The field.
        field: &'static str,
        /// What was wrong with it.
        detail: String,
    },
    /// Bytes remained after a complete record.
    TrailingBytes {
        /// How many.
        count: usize,
    },
}

impl NoticeDecodeRefusal {
    /// The v7/D3 note: why the bytes were refused, and what to do, with
    /// options.
    #[must_use]
    pub fn note(&self) -> String {
        let options = "Either way the definition is NOT imported: a damaged notice is never \
             reinterpreted as a certificate.\n\
             options:\n\
             - rebuild the dependency with this toolchain (a fresh encode writes a \
               well-formed row for every Clean-origin definition);\n\
             - if the bytes came through a transport, check it for truncation or \
               re-encoding — the format is exact bytes, not text;\n\
             - if the producer is a newer toolchain, rebuild THIS crate's toolchain or the \
               dependency so both speak the same format version — there is no best-effort \
               cross-version parse, on purpose.";
        match self {
            Self::UnknownFormatVersion { found, supported } => format!(
                "non-exportable notice format version {found} is unknown to this reader \
                 (supported: {supported}); an unknown version is REFUSED, never best-effort \
                 parsed.\n{options}"
            ),
            Self::Truncated { field, needed, remaining } => format!(
                "the non-exportable notice is truncated inside `{field}`: {needed} byte(s) \
                 needed, {remaining} left.\n{options}"
            ),
            Self::Malformed { field, detail } => {
                format!("the non-exportable notice's `{field}` is malformed: {detail}.\n{options}")
            }
            Self::TrailingBytes { count } => format!(
                "{count} byte(s) remain after a complete non-exportable notice; a record with \
                 a tail is not the record it appears to be, so it is refused whole.\n{options}"
            ),
        }
    }
}
