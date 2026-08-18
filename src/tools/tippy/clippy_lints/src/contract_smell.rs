use clippy_utils::diagnostics::span_lint_and_help;
use rustc_ast::visit::{FnKind, Visitor, walk_block};
use rustc_ast::{
    Block, Expr, ExprKind, FnContract, LoopClause, LoopClauseKind, LoopContract, NodeId, TrustNativeClause,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_lint::{EarlyContext, EarlyLintPass};
use rustc_session::declare_lint_pass;
use rustc_span::{Ident, Span};

declare_clippy_lint! {
    /// ### What it does
    /// Checks first-class contract clauses — `fn f(..) requires P ensures Q`
    /// and `while c invariant P decreases e` — for predicates that cannot
    /// constrain what their clause position promises: a `requires` built only
    /// out of literals, a loop whose `invariant`s name nothing the body works
    /// with, and a loop `decreases` measure the body never touches.
    ///
    /// It deliberately says NOTHING about `ensures`. The ratified design
    /// (D2: entry values + the output record, `x'` ≡ `out.x`) would make an
    /// unprimed-only postcondition vacuous — but the two-state carrier that
    /// design needs (the deep E2 lane) is unimplemented, primes are reserved
    /// grammar the compiler rejects, and a postcondition today is evaluated
    /// purely in the EXIT state, where every unprimed name already denotes
    /// the post-state. Until E2 lands there is nothing here to diagnose. See
    /// the note in `check_signature_clauses` for the measurement and the
    /// restore condition.
    ///
    /// ### Why is this bad?
    /// Each of these parses and elaborates into a real obligation, so nothing
    /// downstream objects — yet the obligation is not the one the author
    /// meant. A literal precondition admits every call or forbids all of
    /// them; a loop measure the body cannot change never decreases, so the
    /// termination obligation it exists to discharge can only fail. The
    /// clause looks like a specification and is not one.
    ///
    /// This check is purely syntactic. It reads the authored clause and
    /// nothing else — never a solver, a proof, or a verification verdict —
    /// so it says only that a clause cannot mean what its position claims,
    /// never whether the program is correct.
    ///
    /// ### Example
    /// ```ignore
    /// while i < n
    ///     invariant true
    ///     decreases n
    /// { i += 1; }
    /// ```
    /// Use instead:
    /// ```ignore
    /// while i < n
    ///     invariant i <= n
    ///     decreases n - i
    /// { i += 1; }
    /// ```
    #[clippy::version = "1.99.0"]
    pub TRUST_CONTRACT_SMELL,
    suspicious,
    "a first-class contract clause that cannot constrain what its position promises"
}

declare_lint_pass!(ContractSmell => [TRUST_CONTRACT_SMELL]);

impl EarlyLintPass for ContractSmell {
    fn check_fn(&mut self, cx: &EarlyContext<'_>, kind: FnKind<'_>, _: Span, _: NodeId) {
        if let FnKind::Fn(_, _, func) = kind
            && let Some(contract) = func.contract.as_deref()
        {
            check_signature_clauses(cx, contract);
        }
    }

    fn check_expr(&mut self, cx: &EarlyContext<'_>, expr: &Expr) {
        if let ExprKind::While(_, body, _, Some(contract)) = &expr.kind {
            check_loop_clauses(cx, contract, body);
        }
    }
}

fn check_signature_clauses(cx: &EarlyContext<'_>, contract: &FnContract) {
    for clause in &contract.trust_native_requires {
        if let Some((span, facts)) = authored(clause)
            && facts.names_nothing()
        {
            span_lint_and_help(
                cx,
                TRUST_CONTRACT_SMELL,
                span,
                "this `requires` predicate names no input",
                None,
                "literals alone admit every call or forbid all of them; name the parameter this restricts",
            );
        }
    }

    // NO `ensures` ARM — deliberately, and not an oversight.
    //
    // It used to flag a postcondition that named no `result`/`out`/primed
    // place, on the reasoning that unprimed names are ENTRY values so such a
    // clause restates the precondition. That reasoning is the RATIFIED design
    // — D2 in docs/design/2026-07-09-two-language-spec-surface.md:
    // "parameters denote entry values, same as in `requires`"; `x'` ≡
    // `out.x` — so the arm was not invented, it enforced the design of
    // record. But the two-state carrier D2 needs (the deep E2 lane; see
    // tests/ui/trust/e2_by_value_prime_discharge.rs, which discharges only
    // the trivial by-value case) is NOT IMPLEMENTED. Today's carrier is
    // one-state: `trust_contract_query` rejects every `&mut`-relevant primed
    // place ("a prime is reserved native grammar for a post-state place, but
    // the current contract carrier has no entry/post-state environment with
    // which to bind it"), and the single state an `ensures` is evaluated in
    // is the EXIT state. So on the shipped compiler, unprimed names in a
    // postcondition already ARE the post-state, and the check was reporting
    // correct, proved contracts as vacuous — enforcing the designed future
    // against the only spelling the present can verify.
    //
    // Measured on stage2 `b371488b94`, two bodies under one clause
    // (`ensures !self.flag`): the body writing `false` proves 2/2, one
    // kernel-certified; the body writing `true` is REFUTED 0/2 with
    // `verified_counterexample = true`. Entry-value semantics cannot tell
    // those apart — nothing constrains the caller's entry value, so neither
    // could prove and neither could be refuted. The verifier is reading the
    // exit state.
    //
    // The arm was also unfixable in place, because its advice had no valid
    // spelling: its own "use instead" example, `ensures balance' == balance -
    // amount`, fails to verify — "primed post-state identifier `balance'` has
    // no verified MIR state binding", fail-closed Unknown. Following the lint
    // turned a fully proved contract into an unverifiable one, and there was
    // no `ensures` that both satisfied the lint and verified.
    //
    // RESTORE THIS ARM when the deep E2 lane lands D2's two-state carrier —
    // when primes lower to bound MIR places for `&mut` borrows, not just the
    // by-value identity case. At that point unprimed names become entry
    // values, the original reasoning becomes true, and `self`-rooted places
    // must be counted as post-state. NOTE that day is also the day every
    // existing `self.field` postcondition in downstream code silently changes
    // meaning (exit → entry), so restoring the arm is part of that migration,
    // not an independent cleanup.
    let _ = &contract.trust_native_ensures;
}

/// Report loop clauses that cannot bear on the iteration they annotate.
///
/// The comparison set is every name the body mentions, not the names it can be
/// shown to assign. Assignment is not decidable here — a call, a macro, or an
/// aliasing write mutates through names this pass cannot resolve — and an
/// over-wide set is the safe direction: it can only suppress a report, never
/// invent one. So a clause that survives the filter genuinely shares no name
/// with the body, and the diagnostic claims exactly that and no more.
fn check_loop_clauses(cx: &EarlyContext<'_>, contract: &LoopContract, body: &Block) {
    let mut body_names = BodyNames::default();
    walk_block(&mut body_names, body);
    if body_names.0.is_empty() {
        // A body that names nothing shares nothing with any clause, so every
        // clause would report. The loop is degenerate, not misspecified.
        return;
    }

    let mut first_invariant: Option<Span> = None;
    let mut invariant_touches_body = false;
    for clause in &contract.clauses {
        let Some((span, facts)) = authored_loop_clause(clause) else {
            continue;
        };
        let touches_body = facts.names.iter().any(|name| body_names.0.contains(*name));
        match clause.kind {
            LoopClauseKind::Invariant => {
                invariant_touches_body |= touches_body;
                first_invariant = first_invariant.or(Some(span));
            },
            LoopClauseKind::Decreases if !touches_body => {
                span_lint_and_help(
                    cx,
                    TRUST_CONTRACT_SMELL,
                    span,
                    "this `decreases` measure names nothing the loop body works with",
                    None,
                    "a measure the body cannot change never decreases; measure what the iteration consumes",
                );
            },
            LoopClauseKind::Decreases => {},
        }
    }

    if let Some(span) = first_invariant
        && !invariant_touches_body
    {
        span_lint_and_help(
            cx,
            TRUST_CONTRACT_SMELL,
            span,
            "no `invariant` on this loop names anything its body works with",
            None,
            "an invariant independent of the iteration carries no induction hypothesis into it",
        );
    }
}

/// The authored span and predicate facts of a signature clause, or `None` when
/// expansion produced it.
///
/// A clause stamped with a call-site span cannot be pointed at usefully, and
/// its author cannot rewrite it: the predicate belongs to the macro.
fn authored(clause: &TrustNativeClause) -> Option<(Span, PredicateFacts<'_>)> {
    (!clause.predicate.from_expansion()).then(|| (clause.predicate, scan(clause.payload.as_str())))
}

/// As [`authored`], but anchored on the clause keyword so the diagnostic covers
/// `invariant P` rather than the bare predicate.
fn authored_loop_clause(clause: &LoopClause) -> Option<(Span, PredicateFacts<'_>)> {
    let (span, facts) = authored(&clause.clause)?;
    (!clause.keyword_span.from_expansion()).then(|| (clause.keyword_span.to(span), facts))
}

/// Names read out of one rendered clause predicate.
struct PredicateFacts<'a> {
    /// Every identifier-shaped token, in authored order.
    names: Vec<&'a str>,
}

impl PredicateFacts<'_> {
    /// Whether the predicate is built entirely from literals, so that no
    /// argument can change its truth value.
    fn names_nothing(&self) -> bool {
        self.names.iter().all(|name| matches!(*name, "true" | "false"))
    }
}

/// Read the names out of a clause's token-rendered payload.
///
/// The payload, not the source span, is the faithful spelling: expansion can
/// stamp one call-site span on every token of a clause, and the parser records
/// this rendering from the exact tokens it consumed. Reading it needs no source
/// map, so the same answer holds for macro-generated and hand-written clauses.
///
/// The scan is deliberately not a parser. Verifier vocabulary is not Rust — it
/// admits quantifier binders, `==>`, and primed names that no Rust grammar
/// accepts — and the only question asked here is which names a predicate
/// mentions, which survives any disagreement about how they are combined.
fn scan(payload: &str) -> PredicateFacts<'_> {
    let bytes = payload.as_bytes();
    let mut facts = PredicateFacts { names: Vec::new() };
    let mut i = 0;
    while i < bytes.len() {
        let byte = bytes[i];
        if byte == b'"' {
            i = skip_string(bytes, i);
        } else if byte == b'\'' {
            // A prime is consumed with the name it modifies below, so a quote
            // reached here opens a lifetime or a character literal.
            i = skip_quote(bytes, i);
        } else if byte.is_ascii_digit() {
            // A numeric literal is one token, suffix included: `1u8` must not
            // contribute the name `u8`.
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
        } else if is_name_start(byte) {
            let start = i;
            i += 1;
            while i < bytes.len() && is_name_continue(bytes[i]) {
                i += 1;
            }
            let name = &payload[start..i];
            facts.names.push(name);
            if bytes.get(i) == Some(&b'\'') {
                // A post-state projection is the name glued to a single quote.
                // Nothing reads that fact today (the `ensures` arm is retired
                // — see `check_signature_clauses`), but the prime must still
                // be CONSUMED here: left behind, it would open a lifetime or
                // character literal and swallow the rest of the predicate,
                // corrupting the name list the surviving arms depend on.
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    facts
}

/// Index just past the string literal opening at `open`.
fn skip_string(bytes: &[u8], open: usize) -> usize {
    let mut i = open + 1;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => i += 2,
            b'"' => return i + 1,
            _ => i += 1,
        }
    }
    bytes.len()
}

/// Index just past the character literal or lifetime opening at `open`.
///
/// Neither contributes a name: a lifetime is not a value, and a character
/// literal has no name in it.
fn skip_quote(bytes: &[u8], open: usize) -> usize {
    let mut i = open + 1;
    if bytes.get(i) == Some(&b'\\') {
        // An escape is any length (`'\u{1F600}'`), so scan for the closer.
        i += 2;
        while i < bytes.len() {
            if bytes[i] == b'\'' {
                return i + 1;
            }
            i += 1;
        }
        return bytes.len();
    }
    // `'x'` closes two bytes on; anything else is a lifetime name.
    if bytes.get(open + 2) == Some(&b'\'') {
        return open + 3;
    }
    while i < bytes.len() && is_name_continue(bytes[i]) {
        i += 1;
    }
    i
}

fn is_name_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic() || !byte.is_ascii()
}

fn is_name_continue(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphanumeric() || !byte.is_ascii()
}

/// Every name a loop body mentions.
///
/// Walking to `visit_ident` reaches path segments, bindings, fields, and method
/// names alike. Collecting all of them — not only the ones in write position —
/// is what makes the loop reports safe to emit; see [`check_loop_clauses`].
#[derive(Default)]
struct BodyNames(FxHashSet<String>);

impl<'ast> Visitor<'ast> for BodyNames {
    fn visit_ident(&mut self, ident: &'ast Ident) {
        self.0.insert(ident.name.as_str().to_owned());
    }
}

#[cfg(test)]
mod tests_for_scan {
    use super::scan;

    /// A prime must be CONSUMED with the name it modifies. Nothing reads
    /// "is post-state" any more (the `ensures` arm is retired), but if the
    /// quote were left behind it would open a lifetime and swallow the rest of
    /// the predicate — so the name list is the property worth pinning.
    #[test]
    fn a_trailing_quote_is_consumed_with_its_name() {
        let facts = scan("balance'== balance - amount");

        assert_eq!(facts.names, ["balance", "balance", "amount"]);
    }

    #[test]
    fn a_predicate_naming_values_is_not_literal_only() {
        let facts = scan("x <= 1000 && y <= 1000");

        assert!(!facts.names_nothing());
        assert_eq!(facts.names, ["x", "y"]);
    }

    #[test]
    fn output_record_names_are_ordinary_names_to_the_scanner() {
        assert_eq!(scan("result >= x").names, ["result", "x"]);
        assert_eq!(scan("out.result >= x").names, ["out", "result", "x"]);
    }

    #[test]
    fn a_lifetime_is_not_a_prime_and_contributes_no_name() {
        let facts = scan("forall i: & 'a u32, * i > 0");

        assert_eq!(facts.names, ["forall", "i", "u32", "i"]);
    }

    #[test]
    fn a_character_literal_closes_without_priming_its_contents() {
        let facts = scan("c == 'x' && d == '\\u{41}'");

        assert_eq!(facts.names, ["c", "d"]);
    }

    #[test]
    fn a_literal_suffix_is_part_of_the_literal() {
        let facts = scan("0 < 1u8 && 2.5f32 < 3");

        assert!(facts.names_nothing());
    }

    #[test]
    fn a_string_literal_hides_its_contents() {
        let facts = scan("tag == \"result x'\"");

        assert_eq!(facts.names, ["tag"]);
    }

    #[test]
    fn boolean_literals_name_nothing() {
        assert!(scan("true").names_nothing());
        assert!(scan("false").names_nothing());
        assert!(scan("1 + 1 == 2").names_nothing());
        assert!(!scan("x").names_nothing());
    }
}
