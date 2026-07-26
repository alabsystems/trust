//! Trust: the first-class contract-clause vocabulary the two-language design
//! adds to the Rust AST — native signature clauses and their `by <thm>`
//! citations, first-class loop clauses, and the parser-authored ordering
//! metadata that reconstructs one function-wide clause order out of seven
//! physical storage lanes.
//!
//! It lives beside `ast.rs` rather than inside it because none of it exists
//! upstream: keeping it in its own file means a merge of upstream's `ast.rs`
//! never collides with Trust's clause surface, and a reader can see the whole
//! addition without diffing a five-thousand-line file.

use rustc_macros::{Decodable, Encodable, Walkable};
use rustc_span::{Span, Symbol};
use thin_vec::ThinVec;

use super::{Expr, FnContract};

/// Trust: one first-class native contract clause payload (two-language design
/// D0/D1) with its optional `by <thm>` citation (E9). Both parts are verifier
/// vocabulary — never name-resolved or type-checked by rustc. Citation
/// identity is canonicalized by the parser; its source span is retained
/// separately for lossless formatting and diagnostics.
#[derive(Clone, Copy, Encodable, Decodable, Debug, Walkable)]
pub struct TrustNativeClause {
    /// The predicate payload span.
    pub predicate: Span,
    /// The payload's token-rendered spelling, captured by the parser from the
    /// exact tokens it consumed. Macro expansion can stamp every payload token
    /// with one call-site span (proc macros legitimately do), so when
    /// `predicate.from_expansion()` the span cannot recover the authored text
    /// and this token-identity spelling is the sole faithful authority.
    pub payload: Symbol,
    /// The optional `by <thm>` citation (E9).
    pub citation: Option<TrustCitation>,
}

/// Canonical identity and authored spelling range for a Clean theorem
/// citation. `name` is the dot-joined sequence of validated identifier
/// segments; comments and whitespace affect only `span`, never identity.
#[derive(Clone, Copy, Encodable, Decodable, Debug, PartialEq, Eq, Walkable)]
pub struct TrustCitation {
    pub name: Symbol,
    pub span: Span,
}

/// Trust: FIRST-CLASS loop clauses (two-language design E4/E5):
/// `while cond invariant P decreases e { .. }`. Like the native signature
/// clauses, the predicates and citations are verifier vocabulary, not Rust.
/// Their authored order and source spans are preserved, and they must never be
/// name-resolved, def-collected, or type-checked. Lowering threads them into
/// the enclosing function's `rustc_hir::FnContract` so the `trust_contracts`
/// query can pair each clause with its loop header.
#[derive(Clone, Encodable, Decodable, Debug, Default, Walkable)]
pub struct LoopContract {
    /// Authored clauses in exact source order. Keeping a single ordered stream
    /// is semantically relevant: tooling, diagnostics, and verifier metadata
    /// must not rewrite `decreases e invariant P` into `invariant P decreases
    /// e`. The parser enforces at most one [`LoopClauseKind::Decreases`].
    pub clauses: ThinVec<LoopClause>,
}

/// One first-class clause authored on a `while` loop.
///
/// The keyword span is the right diagnostic anchor for clause-level errors;
/// [`TrustNativeClause`] retains the predicate and optional citation spans.
#[derive(Clone, Copy, Encodable, Decodable, Debug, Walkable)]
pub struct LoopClause {
    pub kind: LoopClauseKind,
    pub keyword_span: Span,
    pub clause: TrustNativeClause,
}

/// Surface kind of a first-class loop clause.
#[derive(Clone, Copy, Encodable, Decodable, Debug, PartialEq, Eq, Walkable)]
pub enum LoopClauseKind {
    /// `invariant P` (E4).
    Invariant,
    /// `decreases e` (E5).
    Decreases,
}

/// Which first-class function-contract surface an authored clause belongs to.
///
/// This is recorded independently of the clause's AST storage lane so the
/// parser can retain one exact, function-wide authored order.
#[derive(Clone, Copy, Encodable, Decodable, Debug, PartialEq, Eq)]
pub enum FnContractClauseKind {
    Requires,
    Ensures,
    /// `decreases e` — the function-recursion termination measure (E5).
    Decreases,
}

/// The AST lane carrying an authored function-contract clause.
///
/// Typed clauses contain Rust expressions, opaque clauses retain only an
/// attribute payload span, and native clauses retain verifier-language spans
/// plus optional citations.
#[derive(Clone, Copy, Encodable, Decodable, Debug, PartialEq, Eq)]
pub enum FnContractClauseLane {
    Typed,
    Opaque,
    Native,
}

/// Parser-authored identity for one function-contract clause.
///
/// `ordinal` is global across requires, ensures, and decreases. `lane_index` is local to
/// the `(kind, lane)` pair and makes the marker stream independently
/// checkable against the seven physical AST vectors. Neither source spans nor
/// lane concatenation are authoritative for clause order: macro expansion can
/// assign exactly equal spans to distinct clauses.
#[derive(Clone, Copy, Encodable, Decodable, Debug, PartialEq, Eq)]
pub struct FnContractClauseMarker {
    pub ordinal: u32,
    pub kind: FnContractClauseKind,
    pub lane: FnContractClauseLane,
    pub lane_index: u32,
}

/// A reference to the AST value in one physical function-contract lane.
///
/// Consumers may inspect the lane shape, but only
/// [`FnContract::ordered_clause_refs`] can bind one of these references to a
/// validated marker: [`OrderedFnContractClauseRef`]'s fields are private.
#[derive(Clone, Copy, Debug)]
pub enum FnContractClauseRef<'a> {
    Typed(&'a Expr),
    Opaque(Span),
    Native(&'a TrustNativeClause),
}

/// One function-contract clause restored from the parser-authored marker
/// stream.
#[derive(Clone, Copy, Debug)]
pub struct OrderedFnContractClauseRef<'a> {
    marker: FnContractClauseMarker,
    clause: FnContractClauseRef<'a>,
}

impl<'a> OrderedFnContractClauseRef<'a> {
    /// Return the parser-authored identity validated against the physical AST lane.
    pub fn marker(self) -> FnContractClauseMarker {
        self.marker
    }

    /// Return the clause reference bound to [`Self::marker`].
    pub fn clause(self) -> FnContractClauseRef<'a> {
        self.clause
    }
}

/// Why a parser-authored function-contract marker stream could not be
/// reconciled with the seven physical AST lanes.
///
/// This structural validator lives in `rustc_ast`, which owns both the marker
/// schema and the lane storage. Lowering, pretty-printing, and tools must use
/// it instead of recovering order independently from spans or concatenation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnContractClauseOrderError {
    TooManyClauses,
    AmbiguousLegacyTypedLane(FnContractClauseKind),
    InvalidLane {
        kind: FnContractClauseKind,
        lane: FnContractClauseLane,
    },
    NonDenseOrdinal {
        position: usize,
        ordinal: u32,
    },
    NonDenseLaneIndex {
        kind: FnContractClauseKind,
        lane: FnContractClauseLane,
        expected: usize,
        lane_index: u32,
    },
    MissingLaneValue {
        kind: FnContractClauseKind,
        lane: FnContractClauseLane,
        lane_index: usize,
    },
    UnmarkedLaneValue {
        kind: FnContractClauseKind,
        lane: FnContractClauseLane,
        marked: usize,
        stored: usize,
    },
}

const FN_CONTRACT_CLAUSE_LANE_IDENTITIES: [(FnContractClauseKind, FnContractClauseLane); 7] = [
    (FnContractClauseKind::Requires, FnContractClauseLane::Typed),
    (FnContractClauseKind::Requires, FnContractClauseLane::Opaque),
    (FnContractClauseKind::Requires, FnContractClauseLane::Native),
    (FnContractClauseKind::Ensures, FnContractClauseLane::Typed),
    (FnContractClauseKind::Ensures, FnContractClauseLane::Opaque),
    (FnContractClauseKind::Ensures, FnContractClauseLane::Native),
    (FnContractClauseKind::Decreases, FnContractClauseLane::Native),
];

impl FnContractClauseMarker {
    /// Dense slot for this marker's `(kind, lane)` pair.
    const fn lane_slot(self) -> Option<usize> {
        use FnContractClauseKind::{Decreases, Ensures, Requires};
        use FnContractClauseLane::{Native, Opaque, Typed};

        match (self.kind, self.lane) {
            (Requires, Typed) => Some(0),
            (Requires, Opaque) => Some(1),
            (Requires, Native) => Some(2),
            (Ensures, Typed) => Some(3),
            (Ensures, Opaque) => Some(4),
            (Ensures, Native) => Some(5),
            (Decreases, Native) => Some(6),
            (Decreases, Typed | Opaque) => None,
        }
    }
}

impl FnContract {
    /// Cardinality of each physical clause lane in the same order as
    /// [`FnContractClauseMarker::lane_slot`].
    ///
    /// The legacy singleton typed fields are accepted only when their modern
    /// vector lane is empty. Having both representations is ambiguous and
    /// therefore cannot be assigned an authored ordinal.
    fn clause_lane_lengths(&self) -> Result<[usize; 7], FnContractClauseOrderError> {
        if !self.requires_clauses.is_empty() && self.requires.is_some() {
            return Err(FnContractClauseOrderError::AmbiguousLegacyTypedLane(
                FnContractClauseKind::Requires,
            ));
        }
        if !self.ensures_clauses.is_empty() && self.ensures.is_some() {
            return Err(FnContractClauseOrderError::AmbiguousLegacyTypedLane(
                FnContractClauseKind::Ensures,
            ));
        }

        Ok([
            if self.requires_clauses.is_empty() {
                usize::from(self.requires.is_some())
            } else {
                self.requires_clauses.len()
            },
            self.trust_opaque_requires.len(),
            self.trust_native_requires.len(),
            if self.ensures_clauses.is_empty() {
                usize::from(self.ensures.is_some())
            } else {
                self.ensures_clauses.len()
            },
            self.trust_opaque_ensures.len(),
            self.trust_native_ensures.len(),
            self.trust_native_decreases.len(),
        ])
    }

    /// Resolve the parser-authored marker stream to references into the seven
    /// physical AST lanes.
    ///
    /// No source-position or grouped-lane fallback is permitted: macro
    /// expansion can assign equal spans to distinct clauses, so only the dense
    /// marker stream owns authored identity and order.
    pub fn ordered_clause_refs(
        &self,
    ) -> Result<Vec<OrderedFnContractClauseRef<'_>>, FnContractClauseOrderError> {
        let stored_lengths = self.clause_lane_lengths()?;
        let mut consumed = [0usize; 7];
        let mut ordered = Vec::with_capacity(self.clause_order.len());
        for (position, marker) in self.clause_order.iter().copied().enumerate() {
            let expected_ordinal =
                u32::try_from(position).map_err(|_| FnContractClauseOrderError::TooManyClauses)?;
            if marker.ordinal != expected_ordinal {
                return Err(FnContractClauseOrderError::NonDenseOrdinal {
                    position,
                    ordinal: marker.ordinal,
                });
            }

            let Some(slot) = marker.lane_slot() else {
                return Err(FnContractClauseOrderError::InvalidLane {
                    kind: marker.kind,
                    lane: marker.lane,
                });
            };
            let lane_index = usize::try_from(marker.lane_index)
                .map_err(|_| FnContractClauseOrderError::TooManyClauses)?;
            if lane_index != consumed[slot] {
                return Err(FnContractClauseOrderError::NonDenseLaneIndex {
                    kind: marker.kind,
                    lane: marker.lane,
                    expected: consumed[slot],
                    lane_index: marker.lane_index,
                });
            }
            let clause = match (marker.kind, marker.lane) {
                (FnContractClauseKind::Requires, FnContractClauseLane::Typed) => self
                    .requires_clauses
                    .get(lane_index)
                    .map(Box::as_ref)
                    .or_else(|| {
                        (self.requires_clauses.is_empty() && lane_index == 0)
                            .then(|| self.requires.as_deref())
                            .flatten()
                    })
                    .map(FnContractClauseRef::Typed),
                (FnContractClauseKind::Ensures, FnContractClauseLane::Typed) => self
                    .ensures_clauses
                    .get(lane_index)
                    .map(Box::as_ref)
                    .or_else(|| {
                        (self.ensures_clauses.is_empty() && lane_index == 0)
                            .then(|| self.ensures.as_deref())
                            .flatten()
                    })
                    .map(FnContractClauseRef::Typed),
                (FnContractClauseKind::Requires, FnContractClauseLane::Opaque) => self
                    .trust_opaque_requires
                    .get(lane_index)
                    .copied()
                    .map(FnContractClauseRef::Opaque),
                (FnContractClauseKind::Ensures, FnContractClauseLane::Opaque) => self
                    .trust_opaque_ensures
                    .get(lane_index)
                    .copied()
                    .map(FnContractClauseRef::Opaque),
                (FnContractClauseKind::Requires, FnContractClauseLane::Native) => {
                    self.trust_native_requires.get(lane_index).map(FnContractClauseRef::Native)
                }
                (FnContractClauseKind::Ensures, FnContractClauseLane::Native) => {
                    self.trust_native_ensures.get(lane_index).map(FnContractClauseRef::Native)
                }
                (FnContractClauseKind::Decreases, FnContractClauseLane::Native) => {
                    self.trust_native_decreases.get(lane_index).map(FnContractClauseRef::Native)
                }
                (
                    FnContractClauseKind::Decreases,
                    FnContractClauseLane::Typed | FnContractClauseLane::Opaque,
                ) => None,
            };
            let Some(clause) = clause else {
                return Err(FnContractClauseOrderError::MissingLaneValue {
                    kind: marker.kind,
                    lane: marker.lane,
                    lane_index,
                });
            };
            consumed[slot] += 1;
            ordered.push(OrderedFnContractClauseRef { marker, clause });
        }

        for (slot, (&marked, stored)) in consumed.iter().zip(stored_lengths).enumerate() {
            if marked != stored {
                let Some((kind, lane)) = FN_CONTRACT_CLAUSE_LANE_IDENTITIES.get(slot).copied()
                else {
                    return Err(FnContractClauseOrderError::TooManyClauses);
                };
                return Err(FnContractClauseOrderError::UnmarkedLaneValue {
                    kind,
                    lane,
                    marked,
                    stored,
                });
            }
        }
        Ok(ordered)
    }
}
