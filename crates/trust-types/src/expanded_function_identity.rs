//! Explicit provenance of a compiler-captured expanded typed function.
//!
//! This is not the digest of ordinary function source text. Serialized records
//! are correlation data; only a live compiler capture binds their provenance.

use serde::{Deserialize, Serialize};

use crate::{CompilerContractBundle, SourceSpan, VerifiableFunction};

pub const EXPANDED_FUNCTION_IDENTITY_SCHEMA: &str = "trust.expanded-function-input.v1";
pub const MAX_EXPANSION_SOURCE_BYTES: usize = 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpansionSourceFragment {
    pub span: SourceSpan,
    pub byte_len: u64,
    pub sha256: String,
}

impl ExpansionSourceFragment {
    pub fn from_exact_snippet(span: SourceSpan, text: &str) -> Option<Self> {
        let fragment = Self {
            span,
            byte_len: u64::try_from(text.len()).ok()?,
            sha256: crate::stable_sha256_hex(text.as_bytes()),
        };
        fragment.is_well_formed().then_some(fragment)
    }

    fn is_well_formed(&self) -> bool {
        self.byte_len > 0
            && self.byte_len <= MAX_EXPANSION_SOURCE_BYTES as u64
            && !self.span.file.is_empty()
            && self.span.file.len() <= 4096
            && self.span.line_start > 0
            && (self.span.line_start, self.span.col_start)
                <= (self.span.line_end, self.span.col_end)
            && crate::digest::is_stable_sha256_hex(&self.sha256)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpandedFunctionIdentity {
    pub schema: String,
    pub function_path: String,
    /// Rustc's stable crate identity and crate-local DefPathHash component.
    pub function_def_path_hash: [u64; 2],
    pub macro_path: String,
    pub macro_def_path_hash: [u64; 2],
    pub definition: ExpansionSourceFragment,
    pub invocation: ExpansionSourceFragment,
    /// Full existing typed function and compiler contract input, not a pretty
    /// printed template, call-site surrogate, or rustc's noncryptographic hash.
    pub typed_input_sha256: String,
}

impl ExpandedFunctionIdentity {
    pub fn is_well_formed(&self) -> bool {
        let path = |p: &str| !p.is_empty() && p.trim() == p && p.len() <= 4096;
        self.schema == EXPANDED_FUNCTION_IDENTITY_SCHEMA
            && path(&self.function_path)
            && path(&self.macro_path)
            && self.function_def_path_hash[0] == self.macro_def_path_hash[0]
            && self.definition.is_well_formed()
            && self.invocation.is_well_formed()
            && crate::digest::is_stable_sha256_hex(&self.typed_input_sha256)
    }

    pub fn matches_input(
        &self,
        function: &VerifiableFunction,
        contracts: &CompilerContractBundle,
    ) -> bool {
        self.is_well_formed()
            && self.function_path == function.def_path
            && expanded_typed_input_digest(function, contracts).as_deref()
                == Some(&self.typed_input_sha256)
    }

    pub fn digest(&self) -> Option<String> {
        if !self.is_well_formed() {
            return None;
        }
        framed_digest("trust.expanded-function-origin.v1", self)
    }
}

/// Hash the exact existing typed inputs. Capture callers must obtain both from
/// the same actual compiler owner before using this digest as provenance.
pub fn expanded_typed_input_digest(
    function: &VerifiableFunction,
    contracts: &CompilerContractBundle,
) -> Option<String> {
    #[derive(Serialize)]
    struct Input<'a> {
        function: &'a VerifiableFunction,
        compiler_contracts: &'a CompilerContractBundle,
    }
    framed_digest(
        "trust.expanded-function-typed-input.v1",
        &Input { function, compiler_contracts: contracts },
    )
}

fn framed_digest(domain: &str, input: &impl Serialize) -> Option<String> {
    let bytes = crate::original_vc_snapshot::bounded_identity_json(input)?;
    Some(crate::digest::stable_sha256_hex_parts(&[
        b"trustc.digest-frame.v1",
        &(domain.len() as u64).to_be_bytes(),
        domain.as_bytes(),
        &(bytes.len() as u64).to_be_bytes(),
        bytes.as_bytes(),
    ]))
}

impl PartialOrd for ExpansionSourceFragment {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ExpansionSourceFragment {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let key = |s: &Self| {
            (s.span.line_start, s.span.col_start, s.span.line_end, s.span.col_end, s.byte_len)
        };
        self.span
            .file
            .cmp(&other.span.file)
            .then_with(|| key(self).cmp(&key(other)))
            .then_with(|| self.sha256.cmp(&other.sha256))
    }
}
impl PartialOrd for ExpandedFunctionIdentity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ExpandedFunctionIdentity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            &self.schema,
            &self.function_path,
            self.function_def_path_hash,
            &self.macro_path,
            self.macro_def_path_hash,
            &self.definition,
            &self.invocation,
            &self.typed_input_sha256,
        )
            .cmp(&(
                &other.schema,
                &other.function_path,
                other.function_def_path_hash,
                &other.macro_path,
                other.macro_def_path_hash,
                &other.definition,
                &other.invocation,
                &other.typed_input_sha256,
            ))
    }
}
