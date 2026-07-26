//! trust-js-regexp: spec-exact ECMA-262 §22.2 RegExp pattern semantics.
//!
//! The faithful tier's standalone regular-expression engine: compile a
//! Pattern (as UTF-16 code units + a flags string) and run it against an
//! input (as UTF-16 code units). Everything is either **spec-exact per
//! ES2025 §22.2** or a **typed refusal** — never a guessed match result.
//! Results become trace observables judged against real engines, so a wrong
//! answer here is a gate-fatal divergence later; refusal is always sound.
//!
//! # What is implemented (exact)
//!
//! The full main-spec Pattern grammar and matching semantics:
//! disjunction/alternative backtracking in the spec's continuation order,
//! greedy/lazy quantifiers with the spec's `RepeatMatcher` empty-match rule
//! and capture-reset-per-iteration, assertions (`^ $ \b \B`), lookahead and
//! lookbehind (lookbehind matches backwards, direction compiled in),
//! character classes with case-insensitive `Canonicalize` (non-Unicode mode:
//! Default Case Conversion uppercasing with the single-code-unit restriction
//! and the ASCII asymmetry rule; `u`/`v` modes: simple case folding),
//! `\d \D \s \S \w \W` exact sets (including the `ui`-mode extended word
//! characters U+017F/U+212A), numeric and named backreferences (including
//! case-insensitive and ES2025 duplicate-names-across-alternatives),
//! `\p{…}`/`\P{…}` property escapes from generated Unicode 16.0.0 UCD
//! tables, `u`-mode surrogate-pair code-point semantics, `v`-mode
//! ClassSetExpressions (union/intersection/subtraction, nested classes,
//! `\q{…}` string alternatives, properties of strings), and inline modifiers
//! `(?ims-ims: …)`.
//!
//! # What is refused (typed `Unsupported`, never approximated)
//!
//! Annex-B-only constructs (legacy octal escapes, `\8`/`\9`, extended
//! identity escapes such as `\a`, unbraced/invalid quantifier braces as
//! literals, lone `] { }`, quantified lookahead, `\c` without a control
//! letter, `[a-\d]`-style literal-dash ranges, `\k`/`\p` without their
//! strict-mode meaning, …) and resource-extreme patterns (quantifier bounds
//! ≥ 2^32, pathological nesting depth). In non-Unicode mode a main-grammar
//! parse error is reported as `Unsupported` unless the construct is invalid
//! under Annex B as well (only then is it `Syntax`) — so a `Syntax` verdict
//! is always a real SyntaxError in a conforming engine.
//!
//! # Matching architecture
//!
//! A **backtracking VM** (`vm.rs`) mirroring the spec's
//! Matcher/MatcherContinuation semantics: the compiled program's `Split`
//! preference order is exactly the spec's continuation choice order, the
//! backtrack stack holds the not-yet-taken continuations, and all mutable
//! match state (captures, quantifier counters) is journaled so a backtrack
//! restores precisely the spec's `MatchState`. Quantifiers compile to
//! counter loops (no unrolling) carrying the spec's `RepeatMatcher` rules:
//! per-iteration capture reset, no exit before `min`, and the empty-match
//! check on iterations beyond `min`. Lookarounds run as barriered
//! sub-programs: first success is committed (no backtracking into a
//! lookaround), positive keeps inner captures, negative discards them.
//! Every VM step (including backtrack pops) counts against a step budget
//! (default 10^7); exceeding it returns [`ExecError::Budget`] — a sound
//! refusal that bounds adversarial (ReDoS) backtracking.
//!
//! # Unicode data provenance
//!
//! `src/generated/` is emitted by `scripts/gen_ucd_tables.py` from pinned
//! Unicode 16.0.0 UCD files (URLs + input SHA-256 recorded in the script
//! header and `src/generated/mod.rs`). Unicode 16.0.0 matches the reference
//! engine (Node v24.5.0, `process.versions.unicode == "16.0"`). NOTE:
//! trust-js-parse (same engine family, frozen) has its own private ID_*
//! tables; the duplication is deliberate for now and flagged there and here
//! for a future consolidation pass.
//!
//! # Consumer wiring (trust-js-interp, S1d proper)
//!
//! - `compile(source_units, flags)` at `RegExp(P, F)` / literal evaluation
//!   time; `CompileError::Syntax` maps to the interpreter's SyntaxError
//!   completion, `CompileError::Unsupported` maps to a NoCoverage refusal.
//! - `exec_at(input, start)` is the non-sticky `RegExpBuiltinExec` search
//!   (attempts at `start`, then successive positions via
//!   `AdvanceStringIndex`); `exec_sticky_at` is the sticky (`y`) single
//!   anchored attempt. In u/v mode a `start` inside a surrogate pair
//!   denotes the pair's code point (the attempt begins at its lead unit) —
//!   the spec's unit→code-point index conversion, so the consumer passes
//!   `lastIndex` through unchanged. `lastIndex` bookkeeping,
//!   `global`/`sticky` looping, `hasIndices` array shaping, and `groups`
//!   object construction are consumer-side; [`Pattern`] exposes the flag
//!   accessors, capture count and `group_names()` (name → 1-based group
//!   number, duplicates possible; at most one of a name's groups
//!   participates in any match).
//! - [`MatchResult`] indices are UTF-16 code-unit offsets; `captures[i]` is
//!   group `i + 1`. `ExecError::Budget` must surface as a refusal
//!   (NoCoverage), never as a null match.
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod ast;
mod classes;
mod compile;
mod generated;
mod parser;
mod unicode;
mod vm;

use thiserror::Error;

/// A compile-time refusal or rejection.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum CompileError {
    /// The pattern/flags are a SyntaxError in a conforming ES2025 engine
    /// (in non-Unicode mode: under the Annex B grammar as well).
    #[error("regexp syntax error: {0}")]
    Syntax(String),
    /// Sound refusal: the construct is outside this engine's spec-exact
    /// surface (Annex-B-only syntax, resource-extreme patterns). The
    /// consumer must treat this as NoCoverage, never as a SyntaxError.
    #[error("regexp unsupported: {0}")]
    Unsupported(String),
}

/// An execution-time refusal.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ExecError {
    /// Sound refusal lane (reserved; current patterns refuse at compile).
    #[error("regexp exec unsupported: {0}")]
    Unsupported(String),
    /// The backtracking step budget was exceeded (ReDoS guard). A sound
    /// refusal: the consumer must report NoCoverage, not a null match.
    #[error("regexp exec budget exceeded")]
    Budget,
}

/// Default step budget for one `exec_at`/`exec_sticky_at` call.
pub const DEFAULT_BUDGET: u64 = 10_000_000;

/// One successful match. All positions are UTF-16 code-unit offsets into
/// the input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchResult {
    /// Start of the overall match (group 0).
    pub index: usize,
    /// End of the overall match (group 0).
    pub end: usize,
    /// Captured ranges for groups `1..=n_captures`: `captures[i]` is group
    /// `i + 1`; `None` = the group did not participate (JS `undefined`).
    pub captures: Vec<Option<(usize, usize)>>,
    /// Named groups as (name, 1-based group number), in group-number order.
    /// Duplicate names (ES2025) yield multiple entries; at most one of a
    /// name's groups has `Some` in `captures` for any given match.
    pub named: Vec<(String, usize)>,
}

/// Pattern flags (parsed, validated).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Flags {
    pub has_indices: bool, // d
    pub global: bool,      // g
    pub ignore_case: bool, // i
    pub multiline: bool,   // m
    pub dot_all: bool,     // s
    pub unicode: bool,     // u
    pub unicode_sets: bool, // v
    pub sticky: bool,      // y
}

impl Flags {
    pub(crate) fn parse(flags: &str) -> Result<Flags, CompileError> {
        let mut f = Flags::default();
        for c in flags.chars() {
            let slot = match c {
                'd' => &mut f.has_indices,
                'g' => &mut f.global,
                'i' => &mut f.ignore_case,
                'm' => &mut f.multiline,
                's' => &mut f.dot_all,
                'u' => &mut f.unicode,
                'v' => &mut f.unicode_sets,
                'y' => &mut f.sticky,
                _ => return Err(CompileError::Syntax(format!("invalid flag '{c}'"))),
            };
            if *slot {
                return Err(CompileError::Syntax(format!("duplicate flag '{c}'")));
            }
            *slot = true;
        }
        if f.unicode && f.unicode_sets {
            return Err(CompileError::Syntax("flags u and v are exclusive".into()));
        }
        Ok(f)
    }

    /// Either Unicode flag (`u` or `v`): code-point semantics.
    pub fn has_either_unicode(&self) -> bool {
        self.unicode || self.unicode_sets
    }

    pub fn to_flags_string(&self) -> String {
        let mut s = String::new();
        if self.has_indices { s.push('d'); }
        if self.global { s.push('g'); }
        if self.ignore_case { s.push('i'); }
        if self.multiline { s.push('m'); }
        if self.dot_all { s.push('s'); }
        if self.unicode { s.push('u'); }
        if self.unicode_sets { s.push('v'); }
        if self.sticky { s.push('y'); }
        s
    }
}

/// A compiled pattern.
#[derive(Debug, Clone)]
pub struct Pattern {
    pub(crate) flags: Flags,
    pub(crate) source: Vec<u16>,
    pub(crate) prog: vm::Program,
    pub(crate) n_groups: u32,
    /// (name, 1-based group number), group-number order.
    pub(crate) names: Vec<(String, u32)>,
}

/// Compile `source_units` (pattern source as UTF-16 code units, WITHOUT
/// enclosing slashes) under `flags` (the RegExp flags string).
pub fn compile(source_units: &[u16], flags: &str) -> Result<Pattern, CompileError> {
    let flags = Flags::parse(flags)?;
    let ast = parser::parse(source_units, flags)?;
    let prog = compile::compile(&ast, flags)?;
    let mut names: Vec<(String, u32)> = ast
        .group_names
        .iter()
        .map(|g| (g.name.clone(), g.index))
        .collect();
    names.sort_by_key(|(_, i)| *i);
    Ok(Pattern {
        flags,
        source: source_units.to_vec(),
        prog,
        n_groups: ast.n_groups,
        names,
    })
}

impl Pattern {
    /// Non-sticky search: attempt a match at `start`, then at successive
    /// positions (`AdvanceStringIndex` — by code point in `u`/`v` mode).
    /// This is the search loop of `RegExpBuiltinExec` with `sticky` false.
    pub fn exec_at(&self, input: &[u16], start: usize) -> Result<Option<MatchResult>, ExecError> {
        self.exec_impl(input, start, false, DEFAULT_BUDGET)
    }

    /// Sticky attempt: a single anchored attempt at exactly `start`.
    pub fn exec_sticky_at(
        &self,
        input: &[u16],
        start: usize,
    ) -> Result<Option<MatchResult>, ExecError> {
        self.exec_impl(input, start, true, DEFAULT_BUDGET)
    }

    /// `exec_at` with an explicit step budget (shared across the whole
    /// search, including restarts at later positions).
    pub fn exec_at_with_budget(
        &self,
        input: &[u16],
        start: usize,
        budget: u64,
    ) -> Result<Option<MatchResult>, ExecError> {
        self.exec_impl(input, start, false, budget)
    }

    fn exec_impl(
        &self,
        input: &[u16],
        start: usize,
        sticky: bool,
        budget: u64,
    ) -> Result<Option<MatchResult>, ExecError> {
        if start > input.len() {
            return Ok(None);
        }
        let mut start = start;
        // In u/v mode a unit index inside a surrogate pair denotes the
        // pair's code point (the spec's unit→code-point index conversion in
        // RegExpBuiltinExec): the attempt begins at the pair's lead unit.
        if self.flags.has_either_unicode()
            && start > 0
            && start < input.len()
            && unicode::is_trail(input[start])
            && unicode::is_lead(input[start - 1])
        {
            start -= 1;
        }
        let mut machine = vm::Machine::new(&self.prog, input, budget);
        let mut pos = start;
        loop {
            if let Some(caps) = machine.run(pos)? {
                let captures = (1..=self.n_groups as usize)
                    .map(|g| {
                        let s = caps[2 * g];
                        let e = caps[2 * g + 1];
                        if s == vm::UNSET || e == vm::UNSET { None } else { Some((s, e)) }
                    })
                    .collect();
                return Ok(Some(MatchResult {
                    index: pos,
                    end: caps[1],
                    captures,
                    named: self
                        .names
                        .iter()
                        .map(|(n, i)| (n.clone(), *i as usize))
                        .collect(),
                }));
            }
            if sticky || pos >= input.len() {
                return Ok(None);
            }
            pos += unicode::advance_width(input, pos, self.flags.has_either_unicode());
        }
    }

    /// Number of capturing groups (excluding group 0).
    pub fn n_captures(&self) -> usize {
        self.n_groups as usize
    }

    /// Named groups as (name, 1-based group number), group-number order.
    /// Duplicate names appear once per group carrying the name.
    pub fn group_names(&self) -> &[(String, u32)] {
        &self.names
    }

    /// The pattern source, as given (UTF-16 code units, no slashes).
    pub fn source_units(&self) -> &[u16] {
        &self.source
    }

    pub fn flags(&self) -> Flags {
        self.flags
    }

    pub fn flags_str(&self) -> String {
        self.flags.to_flags_string()
    }
}
