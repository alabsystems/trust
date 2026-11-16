//! The Creusot/pearlite ingestion lane's tippy arm (two-language design v5,
//! §3.2 MIGRATE): the attribute family is read as zero-authority sugar and the
//! machine-faithful subset is proposed as native signature clauses. The lint
//! NEVER asserts a proposition: its outputs are rewrite proposals and
//! per-attribute disclosures, and the proposed clause is proved — or refused —
//! by `targo trust check` like any hand-written clause.
//!
//! Exactness arguments for the machine-applicable subset (each anchored on the
//! compiler's own semantics, not on pearlite folklore):
//!
//! * comparisons map verbatim: Trust elaborates machine comparisons through `toNat` (unsigned) / the sign-flip order
//!   key (signed), whose order IS the machine order (`crates/trust-spec-elab/src/lib.rs:441-443`, `:321-337`);
//! * `old(x)` where `x` is an immutable by-value parameter maps to `x`: entry and exit values coincide for exactly this
//!   class, which is the compiler's own by-value prime-collapse rule
//!   (`rustc_mir_transform/src/trust_verify.rs:20169-20183`);
//! * `result` is the native reserved identifier for the return value;
//! * arithmetic maps verbatim only when it is machine-spelled (no `@` views, no `Int`, no non-machine literal suffixes)
//!   — Trust's encoding is exact wrapping (`trust-spec-elab/src/lib.rs:412`), so the machine spelling denotes the
//!   machine value on both sides.
//!
//! Everything else is DISCLOSED per attribute with the blocker named and the
//! fix options listed (v7/D3): `@`/Int reads (a false-proof vector under
//! exact wrapping), quantifiers (DEFERRED per the R4 §2 doctrine in
//! `trust-spec-elab` — auto-application waits for the bounded-domain
//! encoding), prophecy `^`, and any clause referencing a parameter that is
//! not immutable by-value (MutablePostStateAmbiguity: pearlite reads the
//! entry value, so an exit-state re-reading would silently change the
//! author's proposition).
//!
//! Translation fidelity of the rewrite itself is prose-trusted at this layer
//! and gated downstream by the blob-equivalence harness
//! (`targo-trust/tests/creusot_spec_equivalence.rs`): the compiler's spec-emit
//! artifact renders goals for the PROPOSED clause and for an INDEPENDENTLY
//! authored native clause, and the two are byte-compared. The mapper never
//! renders a goal.

use std::collections::BTreeMap;

use clippy_utils::diagnostics::span_lint_and_then;
use rustc_ast::token::{Delimiter, LitKind, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast::{
    self as ast, AttrArgs, AttrItem, AttrKind, Attribute, BindingMode, ByRef, FnRetTy, Mutability, PatKind, TyKind,
};
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass, declare_lint_pass};
use rustc_span::Span;

declare_clippy_lint! {
    /// ### What it does
    /// Reads the Creusot/pearlite attribute family (any path spelling with a
    /// `creusot_contracts`/`creusot_std`/`creusot` segment: `#[creusot_contracts::requires(..)]`,
    /// `#[creusot_contracts::ensures(..)]`, `#[creusot_contracts::variant(..)]`,
    /// `#[creusot_contracts::logic]`, ...) as zero-authority sugar. For the
    /// machine-faithful subset — boolean operators, comparisons, machine
    /// arithmetic, `old()` on immutable by-value parameters, and `result` —
    /// it proposes a machine-applicable rewrite into Trust's first-class
    /// `requires`/`ensures` signature clauses. Every attribute outside that
    /// subset gets a per-attribute disclosure naming the blocker and the fix
    /// options.
    ///
    /// ### Why is this bad?
    /// Outside the Creusot toolchain these attributes expand to no-ops: the
    /// specs are silently UNVERIFIED while the build reports green. Trust's
    /// two-language design (v5, §3.2 MIGRATE) admits them only as a
    /// zero-authority ingestion lane — foreign spec text may *propose* a
    /// native clause, never assert a proposition. The proposed clause carries
    /// no verdict until `targo trust check` proves it, and the rewrite's
    /// fidelity is gated by the spec-emit blob-equivalence harness, not
    /// assumed by this lint.
    ///
    /// ### Example
    /// ```ignore
    /// #[creusot_contracts::ensures(result >= lo)]
    /// fn floor_at(lo: u64, x: u64) -> u64 { if x < lo { lo } else { x } }
    /// ```
    /// Use instead:
    /// ```ignore
    /// fn floor_at(lo: u64, x: u64) -> u64 ensures result >= lo { if x < lo { lo } else { x } }
    /// ```
    #[clippy::version = "1.97.0"]
    pub TRUST_CREUSOT_SPEC_SUGAR,
    style,
    "creusot/pearlite spec attribute instead of Trust-native signature clauses"
}

declare_lint_pass!(CreusotSpecSugar => [TRUST_CREUSOT_SPEC_SUGAR]);

impl EarlyLintPass for CreusotSpecSugar {
    fn check_item(&mut self, cx: &EarlyContext<'_>, item: &ast::Item) {
        if let ast::ItemKind::Fn(fn_) = &item.kind {
            check_fn_carrier(cx, &item.attrs, fn_);
        }
    }

    fn check_trait_item(&mut self, cx: &EarlyContext<'_>, item: &ast::AssocItem) {
        if let ast::AssocItemKind::Fn(fn_) = &item.kind {
            check_fn_carrier(cx, &item.attrs, fn_);
        }
    }

    fn check_impl_item(&mut self, cx: &EarlyContext<'_>, item: &ast::AssocItem) {
        if let ast::AssocItemKind::Fn(fn_) = &item.kind {
            check_fn_carrier(cx, &item.attrs, fn_);
        }
    }
}

/// Crate segments that mark the Creusot attribute family. Matched anywhere
/// before the terminal segment so renamed re-export spellings
/// (`creusot_std::prelude::requires`) are still recognized.
const FAMILY_CRATES: [&str; 3] = ["creusot_contracts", "creusot_std", "creusot"];

/// The E3-fragment machine surface types. A clause is machine-applicable only
/// when every referenced parameter (and `result`, if referenced) has one of
/// these types — the fragment where the pearlite reading and the native
/// reading provably coincide.
const MACHINE_TYPES: [&str; 13] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "bool",
];

#[derive(Clone, Copy, PartialEq)]
enum ClauseKind {
    Requires,
    Ensures,
}

impl ClauseKind {
    fn keyword(self) -> &'static str {
        match self {
            ClauseKind::Requires => "requires",
            ClauseKind::Ensures => "ensures",
        }
    }
}

enum FamilyAttr {
    Clause(ClauseKind),
    /// A non-clause pearlite marker (`variant`, `logic`, ...), disclosed with
    /// its own migration note.
    Marker(&'static str),
}

fn family_attr(item: &AttrItem) -> Option<FamilyAttr> {
    let segments = &item.path.segments;
    let last = segments.last()?.ident.name;
    let has_family_prefix = segments
        .iter()
        .rev()
        .skip(1)
        .any(|segment| FAMILY_CRATES.contains(&segment.ident.name.as_str()));
    if !has_family_prefix {
        return None;
    }
    match last.as_str() {
        "requires" => Some(FamilyAttr::Clause(ClauseKind::Requires)),
        "ensures" => Some(FamilyAttr::Clause(ClauseKind::Ensures)),
        "variant" => Some(FamilyAttr::Marker("variant")),
        "invariant" => Some(FamilyAttr::Marker("invariant")),
        "logic" => Some(FamilyAttr::Marker("logic")),
        "predicate" => Some(FamilyAttr::Marker("predicate")),
        "law" => Some(FamilyAttr::Marker("law")),
        "trusted" => Some(FamilyAttr::Marker("trusted")),
        "maintains" => Some(FamilyAttr::Marker("maintains")),
        "pure" => Some(FamilyAttr::Marker("pure")),
        "open" => Some(FamilyAttr::Marker("open")),
        "ghost" => Some(FamilyAttr::Marker("ghost")),
        "snapshot" => Some(FamilyAttr::Marker("snapshot")),
        _ => None,
    }
}

/// How a parameter may participate in a migrated clause.
#[derive(Clone, Copy, PartialEq)]
enum ParamKind {
    /// Immutable by-value binding of a machine type: entry and exit values
    /// coincide, so the pearlite (entry) reading maps verbatim.
    Supported,
    /// `mut` binding: pearlite reads the entry value, an exit-state re-reading
    /// would silently change the proposition (MutablePostStateAmbiguity).
    MutBinding,
    /// Behind `&`/`&mut`: two-state semantics belong to the prophecy lane.
    Reference,
    /// By-value but outside the machine fragment at this rung.
    NonMachine,
}

fn is_machine_ty(ty: &ast::Ty) -> bool {
    if let TyKind::Path(None, path) = &ty.kind
        && let [segment] = &path.segments[..]
        && segment.args.is_none()
    {
        return MACHINE_TYPES.contains(&segment.ident.name.as_str());
    }
    false
}

fn param_table(fn_: &ast::Fn) -> BTreeMap<String, ParamKind> {
    let mut table = BTreeMap::new();
    for param in &fn_.sig.decl.inputs {
        let PatKind::Ident(BindingMode(by_ref, mutability), ident, None) = &param.pat.kind else {
            // Destructuring patterns have no single spelling a clause could
            // reference; idents inside them fall out as unknown identifiers.
            continue;
        };
        let kind = if matches!(param.ty.kind, TyKind::Ref(..)) || matches!(by_ref, ByRef::Yes(..)) {
            ParamKind::Reference
        } else if *mutability == Mutability::Mut {
            ParamKind::MutBinding
        } else if is_machine_ty(&param.ty) {
            ParamKind::Supported
        } else {
            ParamKind::NonMachine
        };
        table.insert(ident.name.to_string(), kind);
    }
    table
}

/// One reason a clause is not machine-applicable. Every variant's note carries
/// the fix options (v7/D3: a refusal must carry the fix).
enum Blocker {
    IntView,
    Prophecy,
    Quantifier,
    Implication,
    OldUnsupported(String),
    MutableParam(String),
    ReferenceParam(String),
    NonMachineParam(String),
    UnknownIdent(String),
    ResultInRequires,
    ResultNotMachine,
    WidthSuffix(String),
    Unsupported(String),
}

impl Blocker {
    fn note(&self) -> String {
        match self {
            Blocker::IntView => "pearlite `@` lifts the value to mathematical Int, and Trust's \
                 machine encoding is exact wrapping — an Int reading of arithmetic or comparisons \
                 is the recorded false-proof vector; options: restate the property on machine \
                 values, or move it to a `clean { .. }` island theorem and cite it with \
                 `ensures .. by <theorem>`"
                .to_string(),
            Blocker::Prophecy => "`^` (pearlite prophecy/final value — and bitwise xor, which is \
                 also outside the subset) has no native carrier here; the `&mut` two-state lane \
                 is trust-wp's RustHorn prophecy domain (v6/D3); option: restructure the contract \
                 to speak only about by-value entry/exit values"
                .to_string(),
            Blocker::Quantifier => "quantifier migration is DEFERRED (R4 \u{a7}2 doctrine, \
                 `trust-spec-elab`): a unique machine typing for an Int-relaxed binder is \
                 measurement-only evidence, and auto-application waits for the bounded-domain \
                 encoding; options: keep the attribute (zero-authority, disclosed), or hand-write \
                 the native clause with an explicit machine-typed binder and prove it via \
                 `targo trust check`"
                .to_string(),
            Blocker::Implication => "`==>` migrates with the quantifier rung and is not in the \
                 machine-applicable subset; option: rewrite `a ==> b` as `!(a) || b` by hand"
                .to_string(),
            Blocker::OldUnsupported(detail) => format!(
                "`old(..)` is migratable only when its operand is an immutable by-value machine \
                 parameter — there `old(x)` and `x` provably coincide (the compiler's own \
                 by-value prime-collapse rule); here {detail}, and the entry state has no other \
                 native spelling yet"
            ),
            Blocker::MutableParam(name) => format!(
                "the clause reads parameter `{name}`, whose binding is mutable: pearlite reads \
                 the ENTRY value, and an exit-state re-reading would silently change the \
                 proposition (MutablePostStateAmbiguity); options: drop the `mut` from the \
                 binding, or bind the entry value in a new immutable parameter and restate"
            ),
            Blocker::ReferenceParam(name) => format!(
                "the clause reads parameter `{name}`, which lives behind a reference: two-state \
                 `&mut` semantics belong to the prophecy lane (trust-wp, v6/D3) and shared-borrow \
                 views are not in the machine fragment; option: restate over by-value machine \
                 parameters"
            ),
            Blocker::NonMachineParam(name) => format!(
                "parameter `{name}` is outside the machine fragment (u8..u128, usize, i8..i128, \
                 isize, bool) at this rung; option: restate the property in a `clean {{ .. }}` \
                 island over the value's model"
            ),
            Blocker::UnknownIdent(name) => format!(
                "`{name}` is not a parameter of this function; the machine-applicable subset maps \
                 only parameter reads, `result`, `old(..)`, literals, and machine operators"
            ),
            Blocker::ResultInRequires => "`result` has no meaning in a precondition".to_string(),
            Blocker::ResultNotMachine => "the clause reads `result`, and the return type is \
                 outside the machine fragment at this rung; option: restate the property in a \
                 `clean { .. }` island over the return value's model"
                .to_string(),
            Blocker::WidthSuffix(suffix) => format!(
                "integer suffix `{suffix}` is not a machine width, and stripping it would re-read \
                 the literal at a different width — the recorded false-proof vector (the \
                 spec-surface design's pearlite-migration hazard); the width must be preserved, \
                 so this clause is not rewritten"
            ),
            Blocker::Unsupported(what) => format!(
                "{what} is outside the machine-applicable subset (boolean operators, comparisons, \
                 machine arithmetic, `old(..)` on immutable by-value parameters, `result`)"
            ),
        }
    }
}

struct ClauseCx<'a> {
    kind: ClauseKind,
    params: &'a BTreeMap<String, ParamKind>,
    ret_machine: bool,
}

#[derive(Default)]
struct Classification {
    parts: Vec<String>,
    blockers: Vec<Blocker>,
    /// Set when a dominant blocker (quantifier) makes finer classification of
    /// the remaining tokens noise rather than signal.
    halt: bool,
}

impl Classification {
    fn block(&mut self, blocker: Blocker) {
        self.blockers.push(blocker);
    }

    /// The proposed native clause text, only meaningful when no blocker fired.
    fn render(&self) -> String {
        let mut text = self.parts.join(" ");
        while text.contains("( ") {
            text = text.replace("( ", "(");
        }
        while text.contains(" )") {
            text = text.replace(" )", ")");
        }
        text
    }
}

fn classify_stream(tokens: &TokenStream, ccx: &ClauseCx<'_>, out: &mut Classification) {
    let mut iter = tokens.iter().peekable();
    let mut prev_was_eqeq = false;
    while let Some(tree) = iter.next() {
        if out.halt {
            return;
        }
        match tree {
            TokenTree::Delimited(.., Delimiter::Parenthesis, inner) => {
                out.parts.push("(".to_string());
                classify_stream(inner, ccx, out);
                out.parts.push(")".to_string());
                prev_was_eqeq = false;
            },
            TokenTree::Delimited(..) => {
                out.block(Blocker::Unsupported("`{ .. }` / `[ .. ]` grouping".to_string()));
                prev_was_eqeq = false;
            },
            TokenTree::Token(token, _) => {
                let was_eqeq = prev_was_eqeq;
                prev_was_eqeq = matches!(token.kind, TokenKind::EqEq);
                match &token.kind {
                    TokenKind::Ident(name, _) => match name.as_str() {
                        "true" | "false" => out.parts.push(name.to_string()),
                        "forall" | "exists" => {
                            out.block(Blocker::Quantifier);
                            out.halt = true;
                        },
                        "result" => match ccx.kind {
                            ClauseKind::Requires => out.block(Blocker::ResultInRequires),
                            ClauseKind::Ensures if ccx.ret_machine => {
                                out.parts.push("result".to_string());
                            },
                            ClauseKind::Ensures => out.block(Blocker::ResultNotMachine),
                        },
                        "old" => {
                            classify_old_call(&mut iter, ccx, out);
                        },
                        other => match ccx.params.get(other) {
                            Some(ParamKind::Supported) => out.parts.push(other.to_string()),
                            Some(ParamKind::MutBinding) => {
                                out.block(Blocker::MutableParam(other.to_string()));
                            },
                            Some(ParamKind::Reference) => {
                                out.block(Blocker::ReferenceParam(other.to_string()));
                            },
                            Some(ParamKind::NonMachine) => {
                                out.block(Blocker::NonMachineParam(other.to_string()));
                            },
                            None => out.block(Blocker::UnknownIdent(other.to_string())),
                        },
                    },
                    TokenKind::Literal(lit) => match lit.kind {
                        LitKind::Integer => match lit.suffix {
                            None => out.parts.push(lit.symbol.to_string()),
                            Some(suffix) if MACHINE_TYPES.contains(&suffix.as_str()) => {
                                out.parts.push(format!("{}{}", lit.symbol, suffix));
                            },
                            Some(suffix) => out.block(Blocker::WidthSuffix(suffix.to_string())),
                        },
                        LitKind::Bool => out.parts.push(lit.symbol.to_string()),
                        _ => out.block(Blocker::Unsupported(format!("the literal `{}`", lit.symbol))),
                    },
                    // `==>`: pearlite implication lexes as `==` `>`.
                    TokenKind::Gt if was_eqeq => {
                        out.parts.pop();
                        out.block(Blocker::Implication);
                    },
                    TokenKind::EqEq => out.parts.push("==".to_string()),
                    TokenKind::Ne => out.parts.push("!=".to_string()),
                    TokenKind::Lt => out.parts.push("<".to_string()),
                    TokenKind::Le => out.parts.push("<=".to_string()),
                    TokenKind::Gt => out.parts.push(">".to_string()),
                    TokenKind::Ge => out.parts.push(">=".to_string()),
                    TokenKind::AndAnd => out.parts.push("&&".to_string()),
                    TokenKind::OrOr => out.parts.push("||".to_string()),
                    TokenKind::Bang => out.parts.push("!".to_string()),
                    TokenKind::Plus => out.parts.push("+".to_string()),
                    TokenKind::Minus => out.parts.push("-".to_string()),
                    TokenKind::Star => out.parts.push("*".to_string()),
                    TokenKind::Slash => out.parts.push("/".to_string()),
                    TokenKind::Percent => out.parts.push("%".to_string()),
                    TokenKind::At => out.block(Blocker::IntView),
                    TokenKind::Caret => out.block(Blocker::Prophecy),
                    TokenKind::And | TokenKind::Or | TokenKind::Shl | TokenKind::Shr | TokenKind::Tilde => {
                        out.block(Blocker::Unsupported("a bitwise operator".to_string()));
                    },
                    other => out.block(Blocker::Unsupported(format!("the token `{}`", token_kind_label(other)))),
                }
            },
        }
    }
}

fn token_kind_label(kind: &TokenKind) -> String {
    match kind {
        TokenKind::Eq => "=".to_string(),
        TokenKind::Comma => ",".to_string(),
        TokenKind::Semi => ";".to_string(),
        TokenKind::Colon => ":".to_string(),
        TokenKind::PathSep => "::".to_string(),
        TokenKind::Dot => ".".to_string(),
        TokenKind::Question => "?".to_string(),
        TokenKind::FatArrow => "=>".to_string(),
        TokenKind::RArrow => "->".to_string(),
        _ => format!("{kind:?}"),
    }
}

/// `old(x)`: migratable exactly when the operand is a single immutable
/// by-value machine parameter, where `old(x)` and `x` provably coincide.
fn classify_old_call<'a>(
    iter: &mut std::iter::Peekable<impl Iterator<Item = &'a TokenTree>>,
    ccx: &ClauseCx<'_>,
    out: &mut Classification,
) {
    // Copy the `&TokenTree` out of the peek so the operand borrow is tied to
    // the stream, not to the iterator's own mutable borrow.
    let Some(&next) = iter.peek() else {
        // A bare `old` identifier that is not a call: treat as an unknown
        // identifier rather than guessing.
        out.block(Blocker::UnknownIdent("old".to_string()));
        return;
    };
    let TokenTree::Delimited(.., Delimiter::Parenthesis, inner) = next else {
        out.block(Blocker::UnknownIdent("old".to_string()));
        return;
    };
    if ccx.kind == ClauseKind::Requires {
        out.block(Blocker::Unsupported("`old(..)` in a precondition".to_string()));
        iter.next();
        return;
    }
    let operand: Vec<&TokenTree> = inner.iter().collect();
    let detail = match operand.as_slice() {
        [TokenTree::Token(token, _)] => {
            if let TokenKind::Ident(name, _) = &token.kind {
                match ccx.params.get(name.as_str()) {
                    Some(ParamKind::Supported) => {
                        out.parts.push(name.to_string());
                        iter.next();
                        return;
                    },
                    Some(ParamKind::MutBinding) => {
                        format!("`{name}` has a mutable binding")
                    },
                    Some(ParamKind::Reference) => format!("`{name}` lives behind a reference"),
                    Some(ParamKind::NonMachine) => {
                        format!("`{name}` is outside the machine fragment")
                    },
                    None => format!("`{name}` is not a parameter"),
                }
            } else {
                "the operand is not a plain parameter".to_string()
            }
        },
        _ => "the operand is not a plain parameter".to_string(),
    };
    out.block(Blocker::OldUnsupported(detail));
    iter.next();
}

struct NativeProposal {
    attr_span: Span,
    kind: ClauseKind,
    text: String,
}

struct Disclosure {
    attr_span: Span,
    blockers: Vec<Blocker>,
}

fn check_fn_carrier(cx: &EarlyContext<'_>, attrs: &[Attribute], fn_: &ast::Fn) {
    let params = param_table(fn_);
    let ret_machine = match &fn_.sig.decl.output {
        FnRetTy::Ty(ty) => is_machine_ty(ty),
        FnRetTy::Default(_) => false,
    };

    let mut proposals: Vec<NativeProposal> = Vec::new();
    let mut disclosures: Vec<Disclosure> = Vec::new();
    let mut markers: Vec<(Span, &'static str)> = Vec::new();

    for attr in attrs {
        // Attributes materialized by expansion point at foreign code the user
        // cannot rewrite.
        if attr.span.from_expansion() {
            continue;
        }
        let AttrKind::Normal(normal) = &attr.kind else {
            continue;
        };
        let item = &normal.item;
        match family_attr(item) {
            None => {},
            Some(FamilyAttr::Marker(name)) => markers.push((attr.span, name)),
            Some(FamilyAttr::Clause(kind)) => {
                let ccx = ClauseCx {
                    kind,
                    params: &params,
                    ret_machine,
                };
                let mut classification = Classification::default();
                match &item.args {
                    AttrArgs::Delimited(delim) if !delim.tokens.is_empty() => {
                        classify_stream(&delim.tokens, &ccx, &mut classification);
                    },
                    _ => classification.block(Blocker::Unsupported("an empty predicate".to_string())),
                }
                if classification.blockers.is_empty() {
                    proposals.push(NativeProposal {
                        attr_span: attr.span,
                        kind,
                        text: classification.render(),
                    });
                } else {
                    disclosures.push(Disclosure {
                        attr_span: attr.span,
                        blockers: classification.blockers,
                    });
                }
            },
        }
    }

    if !proposals.is_empty() {
        emit_native_proposals(cx, fn_, &proposals);
    }
    for disclosure in disclosures {
        emit_disclosure(cx, &disclosure);
    }
    for (span, name) in markers {
        emit_marker_disclosure(cx, span, name);
    }
}

/// One aggregated machine-applicable rewrite per function: every supported
/// attribute is deleted and the combined native clause text is inserted at the
/// grammar position the parser accepts (after the return type, before any
/// `where` clause — `parse_fn` parses the contract between the declaration
/// and the where clause).
fn emit_native_proposals(cx: &EarlyContext<'_>, fn_: &ast::Fn, proposals: &[NativeProposal]) {
    let insert_at = match &fn_.sig.decl.output {
        FnRetTy::Default(span) => span.shrink_to_hi(),
        FnRetTy::Ty(ty) => ty.span.shrink_to_hi(),
    };
    // Grammar order: requires clauses, then ensures clauses, each kind in
    // authored order.
    let mut clause_text = String::new();
    for kind in [ClauseKind::Requires, ClauseKind::Ensures] {
        for proposal in proposals.iter().filter(|p| p.kind == kind) {
            clause_text.push_str(&format!(" {} {}", kind.keyword(), proposal.text));
        }
    }
    let mut parts: Vec<(Span, String)> = proposals.iter().map(|p| (p.attr_span, String::new())).collect();
    parts.push((insert_at, clause_text));

    span_lint_and_then(
        cx,
        TRUST_CREUSOT_SPEC_SUGAR,
        proposals[0].attr_span,
        "creusot contract attribute; Trust supports first-class signature clauses",
        |diag| {
            diag.multipart_suggestion(
                "migrate the predicate into the signature (zero-authority proposal)",
                parts,
                Applicability::MachineApplicable,
            );
            diag.note(
                "the rewrite carries no verdict: the native clause is proved, or refused, by \
                 `targo trust check`; its translation fidelity is gated by the blob-equivalence \
                 harness (targo-trust/tests/creusot_spec_equivalence.rs), which byte-compares \
                 compiler-emitted goals for the proposed clause against an independently \
                 authored native clause — the lint never renders a goal",
            );
        },
    );
}

fn emit_disclosure(cx: &EarlyContext<'_>, disclosure: &Disclosure) {
    span_lint_and_then(
        cx,
        TRUST_CREUSOT_SPEC_SUGAR,
        disclosure.attr_span,
        "creusot contract attribute outside the machine-applicable subset; it carries no proof \
         authority and is not examined by this build",
        |diag| {
            let mut seen = std::collections::BTreeSet::new();
            for blocker in &disclosure.blockers {
                let note = blocker.note();
                if seen.insert(note.clone()) {
                    diag.note(note);
                }
            }
        },
    );
}

fn emit_marker_disclosure(cx: &EarlyContext<'_>, span: Span, name: &'static str) {
    span_lint_and_then(
        cx,
        TRUST_CREUSOT_SPEC_SUGAR,
        span,
        "creusot/pearlite attribute has no machine-applicable migration; it carries no proof \
         authority and is not examined by this build",
        |diag| {
            let note = match name {
                "variant" => {
                    "`#[variant(..)]` maps to the native `decreases` signature clause, \
                     but the migration harness does not cover termination measures yet; option: \
                     hand-write `decreases <expr>` in the signature and prove it via `targo \
                     trust check`"
                },
                "invariant" => {
                    "loop invariants migrate to the native loop-clause positions; \
                     option: hand-write the native loop `invariant` clause and prove it via \
                     `targo trust check`"
                },
                "logic" | "predicate" | "law" | "open" => {
                    "pearlite logic bodies have no \
                     ingestion rung; option: restate the definition as a `clean { .. }` island \
                     and cite it from `ensures .. by <theorem>`"
                },
                "trusted" => {
                    "`#[trusted]` asserts without proof, which Trust does not admit at \
                     any authority level; without it the function simply stays unverified until \
                     its obligations prove"
                },
                _ => {
                    "no native carrier exists for this marker yet; option: keep the attribute \
                     (zero-authority, disclosed) and track the ingestion ladder in the \
                     two-language design doc"
                },
            };
            diag.note(note);
        },
    );
}
