//! Trust (SAFETY-ASSUME-1, ruled 2026-10-17): a user-written `unsafe { }` block
//! whose `// SAFETY:` comment sits where `clippy::undocumented_unsafe_blocks`
//! accepts one is a DECLARED ASSUMPTION. docs/DECISION_QUEUE.md "SAFETY-ASSUME-1"
//! is the ruling ("FIX THE SCANNERS TO ACCEPT SOME KIND OF ALLOWED TAG!").
//!
//! ## The rows it replaces
//!
//! Trust has no model of most unsafe operations, and every one it cannot model
//! gets an always-`Bool(true)` row that `refute_unsafe_demand_findings` forces
//! `failed`: vcgen's byte-frozen `[unsafe] missing SAFETY comment on unsafe block`
//! stand-in and its `[unsafe:reborrow]` row, and the compiler's
//! `[unsafe:unmodeled-call]` (`synthetic_unmodeled_unsafe_call_vcs`) and
//! `[unsafe:union-field]` / `[unsafe:mutable-static]` /
//! `[unsafe:layout-constrained-field]` rows (`synthetic_nonmodeled_unsafe_op_vcs`).
//! vcgen never read a comment (it has no source map; `check_unsafe` is passed
//! `&[]`), so the stand-in's claim was false for every block that HAS one, and
//! `targo trust build --allow-l0-gaps` failed on documented code.
//!
//! ## The rule
//!
//! For a local `fn` / associated `fn` / closure body (not promoted, an `Item`
//! instance, not Clean-origin), each MIR operation that sits in a DECLARED block
//! has those rows WITHHELD, and each declared block that lost at least one row
//! publishes ONE `assumption:safety-comment` row instead (`skipped`, solver
//! `trust-safety-comment`, located at the block, its description naming the
//! comment's `file:line:col`). Advisory counts it assumed; the default (strict)
//! lane and memory-safe pass CONDITIONALLY; `-Ztrust-policy=certify` refuses the
//! function ([`abort_on_safety_comment_assumptions`]). It is never proved and never
//! refuted, and a verdict that carries it is never spent for another body
//! (`verdict_rests_on_user_axiom_for`, the panic-free registration).
//!
//! A block is DECLARED when all of these hold:
//!
//! * it is `UnsafeSource::UserProvided`, its span has the root syntax context, and
//!   the source text at its start reads `unsafe` (clippy's
//!   `is_unsafe_from_proc_macro`);
//! * a `// SAFETY:` comment (any case, `/* SAFETY: */` too) is placed where clippy
//!   accepts one with its default configuration (`accept-comment-above-statement`
//!   and `accept-comment-above-attributes` both true): on the lines directly above
//!   the block, inside it right after the `{`, or directly above the `let`, the
//!   assignment or the expression statement that contains it. The ports below are
//!   clippy's `span_has_safety_comment` / `text_has_safety_comment`,
//!   `block_has_inner_safety_comment` and `block_parents_have_safety_comment`, with
//!   every branch where clippy PRETENDS a comment was found (an unreadable source
//!   file, an unsupported parent) answering "no comment" instead.
//!
//! An operation belongs to the INNERMOST recorded unsafe block whose span contains
//! its span — every unsafe block of the typeck root is recorded, compiler-generated
//! ones included, so a `format_args!`/`.await` block nested in a declared block
//! keeps its operations to itself — and only when every span the operation carries
//! (`source_info.span`, and a call's `fn_span`) has the root context and the
//! operation is the body's own (no inlined scope). Two recorded blocks with the
//! same extent decide nothing.
//!
//! ## Where the decision is made
//!
//! Here, over the very `body` the function was extracted from, BEFORE generation:
//! the declared operations are keyed by MIR `Location` and handed to vcgen as
//! `(BlockId, statement index)` / terminator `BlockId` (the extractor's 1:1
//! numbering; a statement also carries its extracted span, re-checked at the site).
//! vcgen withholds a site only inside `trust_vcgen::with_safety_declared_unsafe_ops`
//! and reports every site it withheld; the compiler withholds its own rows through
//! [`SafetyDeclaration::withhold_terminator`] / [`SafetyDeclaration::withhold_location`],
//! which record as they answer. [`SafetyDeclaration::record`] writes only the
//! blocks that lost a row to the session ledger before the artifacts are
//! collected, and the publication reads that ledger. So a withheld row never
//! vanishes without its assumption row, and a fully modeled block (a proved
//! `get_unchecked`, a `[unsafe:sep:*]` row) keeps its real obligation and is
//! charged nothing.
//!
//! ## What stays as it is (fail-closed residuals)
//!
//! A block with no qualifying comment keeps every row `failed`. Never withheld,
//! even in a declared block: the typed `[unsafe:zeroed]` / `[unsafe:uninitialized]`
//! refutations; every modeled operation's real obligation, and the FAILED stand-in
//! of a modeled call whose row the engine did not mint (vcgen's `decide_site`: a
//! vocabulary item, a FOREIGN memory-map callee, an unchecked index); the FAILED
//! stand-in of a raw-pointer READ the engine did not interpret (it models raw reads
//! with `[unsafe:sep:deref]`, so only a raw REBORROW is declared); `[unsafe:asm]`;
//! the FFI lane's rows; `[unsafe:validity-transmute]` and the `-Zmir-opt-level>=2`
//! inlined-evidence rows. A Rust wrapper's map call (`memmap2::MmapMut::map_mut`)
//! is unmodeled on this side (`call_has_unsafe_model_keyed` is false outside the
//! sysroot): its `[unsafe:unmodeled-call]` row is withheld like any other (the
//! evidence set handed to vcgen still names its block, so vcgen mints no stand-in
//! beside it), and its `[unsafe:sep:map]` row stays when the engine minted one.
//! Not declared at all: a block expanded from a macro
//! (clippy's macro-definition comment rule is not ported), a closure body's
//! operation whose block lies in an inlined scope, an `unsafe fn` body's operation
//! outside any block, and every foreign body.
//!
//! ## Soundness shape
//!
//! The comment is REQUIRED and its position is checked, never its prose; the row
//! states an assumption and is never counted proved. No fact enters any VC, so no
//! other obligation of the body is discharged by it. Every string here is built
//! from `func_path` and rendered source positions; nothing renders a type or a
//! `def_path_str`, so a JSON-only session cannot trip `trimmed_def_paths`.

use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::hir::nested_filter;
use rustc_middle::mir::{BasicBlock, Body, Location, SourceInfo, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::Session;
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::source_map::SourceMap;
use rustc_span::{BytePos, Pos, Span, SyntaxContext};
use trust_types::assumption::{SAFETY_COMMENT_ASSUMPTION_TAG, SAFETY_COMMENT_ROW_SOLVER};
use trust_types::{BlockId, Outcome, SourceSpan, TransportObligationResult};

use super::{PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic};

/// The wire kind of the charge row: `assumption:safety-comment`.
fn safety_comment_row_kind() -> String {
    format!("assumption:{SAFETY_COMMENT_ASSUMPTION_TAG}")
}

/// One declared block: its span and the position of its comment's `SAFETY:`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DeclaredBlock {
    block: Span,
    comment: Span,
}

/// One `unsafe { }` block of the typeck root. `comment` is `Some` only for a
/// DECLARED block; every other one (undocumented, compiler-generated, from a
/// macro) is recorded too, so it shadows the operations it contains.
struct UnsafeBlockSite {
    span: Span,
    comment: Option<Span>,
}

/// The session ledger: the declared blocks of each body that lost at least one
/// row, written by [`SafetyDeclaration::record`] before the body's artifacts are
/// collected and read at publication. A union: a body collected twice keeps every
/// block either collection charged (an extra row is the fail-closed direction).
#[derive(Default)]
struct SafetyCommentLedger {
    charged: FxHashMap<DefId, Vec<DeclaredBlock>>,
}

/// The declared operations of ONE body and which of them lost a row. Empty (the
/// default) for every body out of scope: nothing is withheld.
#[derive(Default)]
pub(super) struct SafetyDeclaration {
    blocks: Vec<DeclaredBlock>,
    /// Whether `blocks[i]` lost at least one row.
    charged: Vec<bool>,
    /// Every declared operation, in MIR order, with its index into `blocks`.
    ops: Vec<(Location, usize)>,
    vcgen_ops: trust_vcgen::SafetyDeclaredUnsafeOps,
}

impl SafetyDeclaration {
    /// The declared operations of `body` (see the module doc).
    pub(super) fn of<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let mut this = Self::default();
        let Some(sites) = unsafe_block_sites(tcx, body) else { return this };
        if sites.iter().all(|site| site.comment.is_none()) {
            return this;
        }
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let block_id = BlockId(bb.as_usize());
            for (index, statement) in data.statements.iter().enumerate() {
                let source_info = &statement.source_info;
                if let Some(declared) = declared_block_of(&sites, body, source_info, None) {
                    this.declare(Location { block: bb, statement_index: index }, declared);
                    this.vcgen_ops.declare_statement(
                        block_id,
                        index,
                        super::source_span_from_rustc_span(tcx, source_info.span),
                    );
                }
            }
            let Some(terminator) = &data.terminator else { continue };
            let fn_span = match &terminator.kind {
                TerminatorKind::Call { fn_span, .. } | TerminatorKind::TailCall { fn_span, .. } => {
                    Some(*fn_span)
                }
                _ => None,
            };
            if let Some(declared) =
                declared_block_of(&sites, body, &terminator.source_info, fn_span)
            {
                this.declare(body.terminator_loc(bb), declared);
                this.vcgen_ops.declare_terminator(block_id);
            }
        }
        this
    }

    fn declare(&mut self, location: Location, declared: DeclaredBlock) {
        let index = match self.blocks.iter().position(|block| *block == declared) {
            Some(index) => index,
            None => {
                self.blocks.push(declared);
                self.charged.push(false);
                self.blocks.len() - 1
            }
        };
        self.ops.push((location, index));
    }

    /// The declared operations in vcgen's keying, for ONE generation scope
    /// (`trust_vcgen::with_safety_declared_unsafe_ops`).
    pub(super) fn take_vcgen_ops(&mut self) -> trust_vcgen::SafetyDeclaredUnsafeOps {
        std::mem::take(&mut self.vcgen_ops)
    }

    /// Whether the operation at `location` is declared, RECORDING that its row is
    /// withheld when it is. The caller drops the row for a `true` answer only.
    pub(super) fn withhold_location(&mut self, location: Location) -> bool {
        let Some(&(_, index)) = self.ops.iter().find(|(op, _)| *op == location) else {
            return false;
        };
        self.charged[index] = true;
        true
    }

    /// [`Self::withhold_location`] for the terminator of block `block` (the
    /// extractor's `BlockId`, `bb.as_usize()`).
    pub(super) fn withhold_terminator(&mut self, body: &Body<'_>, block: BlockId) -> bool {
        if block.0 >= body.basic_blocks.len() {
            return false;
        }
        self.withhold_location(body.terminator_loc(BasicBlock::from_usize(block.0)))
    }

    /// Charge the blocks whose operations vcgen reported withheld.
    pub(super) fn record_vcgen_withheld(
        &mut self,
        body: &Body<'_>,
        withheld: &trust_vcgen::SafetyDeclaredWithheld,
    ) {
        for &(location, index) in &self.ops {
            let block = BlockId(location.block.as_usize());
            let hit = if location == body.terminator_loc(location.block) {
                withheld.terminators.contains(&block)
            } else {
                withheld.statements.contains(&(block, location.statement_index))
            };
            if hit {
                self.charged[index] = true;
            }
        }
    }

    /// Write the charged blocks to the session ledger. Called once per collection,
    /// after every row of the generation is final and before the artifacts are
    /// built (the panic-free registration reads the ledger there).
    pub(super) fn record(self, sess: &Session, def_id: DefId) {
        let charged: Vec<DeclaredBlock> = self
            .blocks
            .iter()
            .zip(&self.charged)
            .filter_map(|(block, &charged)| charged.then_some(*block))
            .collect();
        if charged.is_empty() {
            return;
        }
        sess.with_trust_compiler_state::<SafetyCommentLedger, _>(|ledger| {
            let entry = ledger.charged.entry(def_id).or_default();
            for block in charged {
                if !entry.contains(&block) {
                    entry.push(block);
                }
            }
        });
    }
}

/// Whether `def_id`'s verdict rests on a declared block (some row of it was
/// withheld). Such a verdict is CONDITIONAL: never registered panic-free and never
/// spent as a premise for another body.
pub(super) fn body_carries_declaration(sess: &Session, def_id: DefId) -> bool {
    sess.with_trust_compiler_state::<SafetyCommentLedger, _>(|ledger| {
        ledger.charged.get(&def_id).is_some_and(|blocks| !blocks.is_empty())
    })
}

/// Every `unsafe { }` block of `body`'s typeck root, `None` when the body is out
/// of scope (see the module doc).
fn unsafe_block_sites<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<Vec<UnsafeBlockSite>> {
    if body.source.promoted.is_some() || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return None;
    }
    let local = body.source.def_id().as_local()?;
    if !matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
        return None;
    }
    let root = tcx.typeck_root_def_id_local(local);
    // A Clean-origin def has no HIR body to walk (and is emitted from a
    // kernel-checked definition that cannot spell `unsafe`).
    if crate::clean_origin_mir::is_clean_origin(tcx, local)
        || crate::clean_origin_mir::is_clean_origin(tcx, root)
        || !matches!(tcx.def_kind(root), DefKind::Fn | DefKind::AssocFn)
    {
        return None;
    }
    let hir_body = tcx.hir_maybe_body_owned_by(root)?;
    let mut collector =
        UnsafeBlockCollector { tcx, search: body_search_span(tcx, root), blocks: Vec::new() };
    collector.visit_body(hir_body);
    Some(collector.blocks)
}

/// Walks the typeck root's body and the bodies nested in it (closures, inline
/// consts), not nested items: each item is its own root.
struct UnsafeBlockCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    search: Option<Span>,
    blocks: Vec<UnsafeBlockSite>,
}

impl<'tcx> Visitor<'tcx> for UnsafeBlockCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        if let hir::BlockCheckMode::UnsafeBlock(source) = block.rules {
            let comment = match source {
                hir::UnsafeSource::UserProvided => declared_comment(self.tcx, self.search, block),
                hir::UnsafeSource::CompilerGenerated => None,
            };
            self.blocks.push(UnsafeBlockSite { span: block.span, comment });
        }
        intravisit::walk_block(self, block);
    }
}

/// The declared block an operation belongs to: the innermost recorded block that
/// contains EVERY span the operation carries, when it is a declared one.
fn declared_block_of(
    sites: &[UnsafeBlockSite],
    body: &Body<'_>,
    source_info: &SourceInfo,
    fn_span: Option<Span>,
) -> Option<DeclaredBlock> {
    if source_info.scope.inlined_instance(&body.source_scopes).is_some() {
        return None;
    }
    let mut found: Option<DeclaredBlock> = None;
    for span in std::iter::once(source_info.span).chain(fn_span) {
        if span.is_dummy() || !span.ctxt().is_root() {
            return None;
        }
        let site = innermost_site(sites, span)?;
        let declared = DeclaredBlock { block: site.span, comment: site.comment? };
        match found {
            None => found = Some(declared),
            Some(previous) if previous == declared => {}
            Some(_) => return None,
        }
    }
    found
}

/// The innermost recorded block whose span contains `span`; `None` when there is
/// none, or when two blocks of the smallest extent contain it.
fn innermost_site(sites: &[UnsafeBlockSite], span: Span) -> Option<&UnsafeBlockSite> {
    let extent = |site: &UnsafeBlockSite| site.span.hi().0.saturating_sub(site.span.lo().0);
    let mut best: Option<&UnsafeBlockSite> = None;
    let mut tied = false;
    for site in sites.iter().filter(|site| site.span.contains(span)) {
        match best {
            Some(current) if extent(site) > extent(current) => {}
            Some(current) if extent(site) == extent(current) => tied = true,
            _ => {
                best = Some(site);
                tied = false;
            }
        }
    }
    if tied { None } else { best }
}

/// clippy's `get_body_search_span` for a body owned by `root`: the fn item (or
/// impl / trait fn) itself, from whose first line the comment scan starts. Any
/// other owner answers `None`: no comment is read (clippy widens a const or
/// static owner to its module, which no verified body needs).
fn body_search_span(tcx: TyCtxt<'_>, root: LocalDefId) -> Option<Span> {
    match tcx.hir_node_by_def_id(root) {
        hir::Node::Item(item) if matches!(item.kind, hir::ItemKind::Fn { .. }) => Some(item.span),
        hir::Node::ImplItem(item) if matches!(item.kind, hir::ImplItemKind::Fn(..)) => {
            Some(item.span)
        }
        hir::Node::TraitItem(item) if matches!(item.kind, hir::TraitItemKind::Fn(..)) => {
            Some(item.span)
        }
        _ => None,
    }
}

/// The position of the `SAFETY:` that declares `block`, or `None` (see the module
/// doc). clippy's order: the lines above the block, inside the block, then above
/// the statement that contains it.
fn declared_comment(tcx: TyCtxt<'_>, search: Option<Span>, block: &hir::Block<'_>) -> Option<Span> {
    let span = block.span;
    let source_map = tcx.sess.source_map();
    if span.is_dummy() || !span.ctxt().is_root() || !source_reads_unsafe(source_map, span) {
        return None;
    }
    let position = search
        .and_then(|search| comment_above(source_map, search, span))
        .or_else(|| comment_inside(source_map, span))
        .or_else(|| search.and_then(|search| comment_above_parent(tcx, search, block.hir_id)))?;
    Some(Span::with_root_ctxt(position, position))
}

/// clippy's `is_unsafe_from_proc_macro`, negated: the source at the block's start
/// reads `unsafe`. An unreadable source reads nothing.
fn source_reads_unsafe(source_map: &SourceMap, span: Span) -> bool {
    let file_pos = source_map.lookup_byte_offset(span.lo());
    file_pos
        .sf
        .src
        .as_deref()
        .and_then(|src| src.get(file_pos.pos.to_usize()..))
        .is_some_and(|src| src.starts_with("unsafe"))
}

/// clippy's `walk_span_to_context(span, SyntaxContext::root())`.
fn walk_span_to_root(span: Span) -> Option<Span> {
    let outer = rustc_span::hygiene::walk_chain(span, SyntaxContext::root());
    outer.ctxt().is_root().then_some(outer)
}

/// clippy's `span_has_safety_comment`: a comment on the lines between the start of
/// the enclosing item (`search`) and the line `span` starts on.
fn comment_above(source_map: &SourceMap, search: Span, span: Span) -> Option<BytePos> {
    if !span.ctxt().is_root() {
        return None;
    }
    let unsafe_line = source_map.lookup_line(span.lo()).ok()?;
    let body_span = walk_span_to_root(search)?;
    let body_line = source_map.lookup_line(body_span.lo()).ok()?;
    if !Arc::ptr_eq(&unsafe_line.sf, &body_line.sf) || body_line.line >= unsafe_line.line {
        return None;
    }
    // clippy pretends a comment was found when the text is unavailable; nothing
    // is found here.
    let src = unsafe_line.sf.src.as_deref()?;
    let line_starts: Vec<usize> = unsafe_line.sf.lines()[body_line.line + 1..=unsafe_line.line]
        .iter()
        .map(|start| start.to_usize())
        .collect();
    let offset = text_safety_comment(src, &line_starts)?;
    Some(unsafe_line.sf.start_pos + BytePos(u32::try_from(offset).ok()?))
}

/// clippy's `block_has_inner_safety_comment`: `unsafe { // SAFETY: …`.
fn comment_inside(source_map: &SourceMap, span: Span) -> Option<BytePos> {
    let snippet = source_map.span_to_snippet(span).ok()?;
    let offset = inner_safety_comment(&snippet)?;
    Some(span.lo() + BytePos(u32::try_from(offset).ok()?))
}

/// clippy's `block_parents_have_safety_comment` (with `accept-comment-above-
/// statement`): a comment above the `let`, assignment or statement that contains
/// the block.
fn comment_above_parent(tcx: TyCtxt<'_>, search: Span, block: hir::HirId) -> Option<BytePos> {
    let span = match tcx.parent_hir_node(block) {
        hir::Node::Expr(expr) => statement_span_of(tcx, expr)?,
        hir::Node::Stmt(hir::Stmt {
            kind:
                hir::StmtKind::Let(hir::LetStmt { span, .. })
                | hir::StmtKind::Expr(hir::Expr { span, .. })
                | hir::StmtKind::Semi(hir::Expr { span, .. }),
            ..
        })
        | hir::Node::LetStmt(hir::LetStmt { span, .. }) => *span,
        _ => return None,
    };
    comment_above(tcx.sess.source_map(), search, span)
}

/// clippy's `find_unsafe_block_parent_in_expr`: walk up from the block's
/// expression to the `let` or assignment holding it, or stop at the outermost
/// expression (never a branchy one). A const or static owner answers `None`
/// (fail-closed; clippy reads its item span).
fn statement_span_of<'tcx>(tcx: TyCtxt<'tcx>, expr: &'tcx hir::Expr<'tcx>) -> Option<Span> {
    match tcx.parent_hir_node(expr.hir_id) {
        hir::Node::LetStmt(hir::LetStmt { span, .. })
        | hir::Node::Expr(hir::Expr { kind: hir::ExprKind::Assign(_, _, span), .. }) => Some(*span),
        hir::Node::Expr(parent) => statement_span_of(tcx, parent),
        hir::Node::Item(hir::Item {
            kind: hir::ItemKind::Const(..) | hir::ItemKind::Static(..),
            ..
        })
        | hir::Node::ImplItem(hir::ImplItem { kind: hir::ImplItemKind::Const(..), .. })
        | hir::Node::TraitItem(hir::TraitItem { kind: hir::TraitItemKind::Const(..), .. }) => None,
        _ => (!matches!(
            expr.kind,
            hir::ExprKind::If(..) | hir::ExprKind::Loop(..) | hir::ExprKind::Match(..)
        ))
        .then_some(expr.span),
    }
}

/// clippy's `text_has_safety_comment` with `accept-comment-above-attributes`, over
/// the lines whose starts are `line_starts` (byte offsets into `src`; the last one
/// is the line the block starts on, which is not read). Answers the offset of the
/// `SAFETY:` in `src`.
///
/// Reading upward from the line above the block, skipping blank and attribute
/// lines: a run of `//` lines one of which contains `SAFETY:` (outside a doc-comment
/// code fence); else a trailing `// SAFETY:` / `/* SAFETY:` after code on that one
/// line; else the nearest line that starts a block comment, which must contain
/// `SAFETY:` and be followed by nothing but whitespace up to the block.
fn text_safety_comment(src: &str, line_starts: &[usize]) -> Option<usize> {
    let mut lines = line_starts
        .windows(2)
        .rev()
        .map_while(|window| {
            let (start, end) = (window[0], window[1]);
            let text = src.get(start..end)?;
            let trimmed = text.trim_start();
            Some((start + (text.len() - trimmed.len()), trimmed))
        })
        .filter(|(_, text)| !(text.is_empty() || is_attribute(text)));

    let (line_start, line) = lines.next()?;

    if line.starts_with("//") {
        let mut in_codeblock = false;
        let (mut line, mut line_start) = (line, line_start);
        loop {
            if let Some(doc) = line.strip_prefix("///").or_else(|| line.strip_prefix("//!"))
                && doc.trim_start().starts_with("```")
            {
                in_codeblock = !in_codeblock;
            }
            if !in_codeblock && let Some(position) = line.to_ascii_uppercase().find("SAFETY:") {
                return Some(line_start + position);
            }
            match lines.next() {
                Some((start, text)) if text.starts_with("//") => (line, line_start) = (text, start),
                _ => return None,
            }
        }
    }

    // A comment after code on the line directly above (`let x = // SAFETY: …`):
    // only whitespace between the marker and `SAFETY:`.
    if let Some(comment_start) = [line.find("//"), line.find("/*")].into_iter().flatten().min() {
        let after_marker = &line[comment_start + 2..];
        let trimmed = after_marker.trim_start();
        if trimmed.get(..7).is_some_and(|text| text.eq_ignore_ascii_case("SAFETY:")) {
            return Some(line_start + comment_start + 2 + (after_marker.len() - trimmed.len()));
        }
    }

    // A block comment starting a line, followed only by whitespace to the block.
    let block_start = *line_starts.last()?;
    let (mut line_start, mut line) = (line_start, line);
    loop {
        if line.starts_with("/*") {
            let text = src.get(line_start..block_start)?;
            let mut tokens = rustc_lexer::tokenize(text, rustc_lexer::FrontmatterAllowed::No);
            let comment = tokens.next()?;
            let position =
                text.get(..comment.len as usize)?.to_ascii_uppercase().find("SAFETY:")?;
            return tokens
                .all(|token| token.kind == rustc_lexer::TokenKind::Whitespace)
                .then_some(line_start + position);
        }
        (line_start, line) = lines.next()?;
    }
}

/// clippy's `is_attribute`: an attribute line, skipped by the scan.
fn is_attribute(text: &str) -> bool {
    (text.starts_with("#[") || text.starts_with("#![")) && text.trim_end().ends_with(']')
}

/// The offset of the `SAFETY:` in `unsafe { // SAFETY: …` (or `/* SAFETY: */`),
/// read from the block's own source text.
fn inner_safety_comment(snippet: &str) -> Option<usize> {
    let after_brace = snippet.strip_prefix("unsafe")?.trim_start().strip_prefix('{')?.trim_start();
    let comment =
        after_brace.strip_prefix("//").or_else(|| after_brace.strip_prefix("/*"))?.trim_start();
    comment.to_ascii_uppercase().starts_with("SAFETY:").then(|| snippet.len() - comment.len())
}

/// The charge for one body: one row per declared block that lost a row, in MIR
/// order, and the blocks themselves for the human disclosure.
pub(super) struct SafetyCommentCharge {
    pub(super) rows: Vec<TransportObligationResult>,
    blocks: Vec<DeclaredBlock>,
}

/// The SAFETY-ASSUME-1 seam at publication. `None` when the body carries no
/// declared block (or is a promoted constant or a shim, which share the item's
/// `DefId` and publish none of its rows).
pub(super) fn safety_comment_charge<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> Option<SafetyCommentCharge> {
    if body.source.promoted.is_some() || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return None;
    }
    let blocks = tcx.sess.with_trust_compiler_state::<SafetyCommentLedger, _>(|ledger| {
        ledger.charged.get(&body.source.def_id()).cloned()
    })?;
    if blocks.is_empty() {
        return None;
    }
    let rows = blocks
        .iter()
        .map(|declared| {
            safety_comment_row(
                func_path,
                super::source_span_from_rustc_span(tcx, declared.block),
                &super::source_span_from_rustc_span(tcx, declared.comment),
            )
        })
        .collect();
    Some(SafetyCommentCharge { rows, blocks })
}

/// `file:line:col` (1-based column, as a diagnostic prints it).
fn render_position(at: &SourceSpan) -> String {
    format!("{}:{}:{}", at.file, at.line_start, at.col_start.saturating_add(1))
}

fn charge_detail(func_path: &str, block_at: &SourceSpan, comment_at: &SourceSpan) -> String {
    format!(
        "the unsafe block at {} in `{func_path}` is declared sound by its `// SAFETY:` comment at \
         {}; the unsafe operations in it that Trust does not model are assumed, not proved",
        render_position(block_at),
        render_position(comment_at),
    )
}

const CHARGE_REASON: &str = "declared assumption `safety-comment`: a `// SAFETY:` comment placed \
     where clippy's `undocumented_unsafe_blocks` accepts one declares this block sound; the \
     crate's result is CONDITIONAL on it";

/// One charge row. The `transport_assumption_row` contract (`assumption:<tag>`
/// kind, `skipped`, no typed kind, "unverified assumption: " description, no
/// full-verifier marker text in any field), built without a `TyCtxt` so the shape
/// is unit-tested as a whole.
fn safety_comment_row(
    func_path: &str,
    block_at: SourceSpan,
    comment_at: &SourceSpan,
) -> TransportObligationResult {
    TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: safety_comment_row_kind(),
        original_vc_snapshot: None,
        typed_kind: None,
        description: format!(
            "unverified assumption: {}",
            charge_detail(func_path, &block_at, comment_at)
        ),
        location: Some(block_at),
        outcome: Outcome::Skipped,
        solver: SAFETY_COMMENT_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(CHARGE_REASON.to_string()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        grade: None,
    }
}

/// `rows` with every pre-existing row of the charge kind removed and the charge
/// (if any) appended. `None` — use `rows` unchanged — when there is no charge and
/// nothing to strip.
pub(super) fn rows_with_safety_comment_assumptions(
    rows: &[TransportObligationResult],
    charge: Option<&SafetyCommentCharge>,
) -> Option<Vec<TransportObligationResult>> {
    let kind = safety_comment_row_kind();
    if charge.is_none() && !rows.iter().any(|row| row.kind == kind) {
        return None;
    }
    let mut out: Vec<TransportObligationResult> =
        rows.iter().filter(|row| row.kind != kind).cloned().collect();
    if let Some(charge) = charge {
        out.extend(charge.rows.iter().cloned());
    }
    Some(out)
}

/// The zero-obligation rows of a charged body: the composed rows with the charge
/// appended and WITHOUT the proved `no_obligations` row — a body whose unsafe
/// block is assumed is not "trivially panic-free" (the same rule as an instance
/// hypothesis). Uncharged rows pass through with any stale charge-kind row
/// stripped.
pub(super) fn zero_obligation_rows(
    rows: Vec<TransportObligationResult>,
    charge: Option<&SafetyCommentCharge>,
) -> Vec<TransportObligationResult> {
    let kind = safety_comment_row_kind();
    let Some(charge) = charge else {
        return if rows.iter().any(|row| row.kind == kind) {
            rows.into_iter().filter(|row| row.kind != kind).collect()
        } else {
            rows
        };
    };
    let mut out: Vec<TransportObligationResult> =
        rows.into_iter().filter(|row| row.kind != kind && row.kind != "no_obligations").collect();
    out.extend(charge.rows.iter().cloned());
    out
}

const DISCLOSURE_NOTE: &str = "recorded as `assumption:safety-comment` (skipped, NOT proved): \
     the crate's result is CONDITIONAL on each declared block being sound, and \
     `-Ztrust-policy=certify` refuses it";

/// The human disclosure on every non-`certify` lane (human output only; targo
/// reads the row).
pub(super) fn warn_safety_comment_assumptions(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &SafetyCommentCharge,
) {
    prepare_safety_comment_warning(tcx, body, func_path, charge).emit(tcx);
}

// Trust: keep real block/comment spans and their original interleaved order.
pub(super) fn prepare_safety_comment_warning(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &SafetyCommentCharge,
) -> PreparedLocatedDiagnostic {
    let summary = match charge.blocks.len() {
        1 => "an unsafe block is ASSUMED sound on its `// SAFETY:` comment, not proved".to_string(),
        n => format!(
            "{n} unsafe blocks are ASSUMED sound on their `// SAFETY:` comments, not proved"
        ),
    };
    let span = tcx.def_span(body.source.def_id());
    let header = format!("Trust verification advisory for `{func_path}`: {summary}");
    let mut children = Vec::new();
    for block in &charge.blocks {
        children.push(PreparedDiagnosticChild::SpanNote(
            block.block,
            "the unsafe operations in this block that Trust does not model are assumed sound"
                .into(),
        ));
        children.push(PreparedDiagnosticChild::SpanNote(
            block.comment,
            "declared by this `SAFETY:` comment".into(),
        ));
    }
    children.push(PreparedDiagnosticChild::Note(DISCLOSURE_NOTE.into()));
    PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: false, header, children },
    }
}

/// `certify` refuses a function carrying the charge. Emitted in every output
/// mode, like the other certify aborts; the message renders only `func_path`.
pub(super) fn abort_on_safety_comment_assumptions(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &SafetyCommentCharge,
) {
    prepare_safety_comment_refusal(tcx, body, func_path, charge).emit(tcx);
}

// Trust: prepare the certify refusal as DATA; the original wrapper still emits.
pub(super) fn prepare_safety_comment_refusal(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &SafetyCommentCharge,
) -> PreparedLocatedDiagnostic {
    let summary = match charge.blocks.len() {
        1 => {
            "an unsafe block is sound only by its `// SAFETY:` comment, not by a proof".to_string()
        }
        n => format!(
            "{n} unsafe blocks are sound only by their `// SAFETY:` comments, not by a proof"
        ),
    };
    let span = tcx.def_span(body.source.def_id());
    let header = format!("Trust certify verification failed for `{func_path}`: {summary}");
    let mut children = Vec::new();
    for block in &charge.blocks {
        children.push(PreparedDiagnosticChild::SpanNote(
            block.block,
            "the unsafe operations in this block are not proved".into(),
        ));
        children.push(PreparedDiagnosticChild::SpanNote(
            block.comment,
            "declared sound only by this `SAFETY:` comment".into(),
        ));
    }
    children.push(PreparedDiagnosticChild::Note(
        "under `-Ztrust-policy=certify` an `assumption:safety-comment` row is fatal; the default \
         lane records it and passes CONDITIONALLY"
            .into(),
    ));
    PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: true, header, children },
    }
}

#[cfg(test)]
mod tests;
