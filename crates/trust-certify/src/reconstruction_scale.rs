// trust-certify: resource gates on the ay → clean_auto reconstruction lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Resource gates on steps 3–5 of `certify_linear_int_fragment` (in the crate
//! root): the in-process ay solve and the clean_auto reconstruction of its
//! refutation.
//!
//! # The hazard
//!
//! clean_auto replays an ay Farkas lemma whose certificate carries a non-unit
//! multiplier `k` with `scale_bound`: a binary doubling chain, `O(log k)` SHARED
//! kernel nodes, which its kernel checks as the DAG it is. Its symbolic
//! additive closeout (`theory_lemma_lra_sum_nf::try_close_int_additive_nf`:
//! `IntAddNf::flatten`, the quadratic `build_close_shape` match, the proof
//! transport) then walks that accumulator as a TREE of `Σ kᵢ · |boundᵢ|`
//! additive leaves. Nothing on that walk is budgeted, and neither
//! `-Ztrust-verify-timeout-ms` nor the function budget reaches it. (The in-tree
//! Farkas lane caps its own repetition for the same reason —
//! `find_farkas_multipliers`' `MULT_SUM_CAP`; this lane had no cap because the
//! repetition happens inside the reconstruction.)
//!
//! Measured on trustc (2026-09-25/26, W4 ALLOC-LEN adversarial rounds 1–2):
//!
//! * a `2^30 · len ≥ 2^63` capacity row under `len < 2^32` (probe a01): more
//!   than 11 minutes at 184 GB, killed;
//! * `String::with_capacity(a.len() + b.len())` under the guards
//!   `a.len() * 4093 < 2^60 ∧ b.len() * 4091 < 2^60` (probe b45): every
//!   coefficient at most `2^12`, but ay's certificate carries `4093/4091`, so
//!   its integer multipliers reach `4093 · 4091 ≈ 2^24` — 37.7 GB in 38 s;
//! * the same guards over a plain bounds check `big[a.len() + b.len()]` (probe
//!   b48) blows up on origin/main too: the mechanism predates ALLOC-LEN, which
//!   only added a realistic entry point.
//!
//! # The two gates
//!
//! Both decide AUTHORITY, never truth: a decline withholds `Certified` and
//! nothing else — the row keeps the verdict its engine gave it — so neither can
//! turn a refuted row green, and neither is a proof premise.
//!
//! 1. **Before the solve**, on the pool: [`pool_coefficient_scale`] must not
//!    exceed [`AY_RECONSTRUCTION_MAX_COEFFICIENT`]. A cheap early decline for
//!    the pools that cannot produce a small certificate (and it spares the ay
//!    solve). It is a PROXY — a multiplier exists to cancel coefficients, but
//!    which ones the certificate needs is not knowable before the solve.
//! 2. **After the solve, before the reconstruction**, on ay's own certificate:
//!    [`alethe_closeout_estimate`] reads every Farkas step of the rendered
//!    proof and bounds the leaves the closeout would walk, exactly as clean_auto
//!    computes its integer multipliers (the step's coefficients scaled by the
//!    LCM of their denominators). This is the gate that bounds the walk; gate 1
//!    only makes it rarer.
//!
//! The exact bound lives inside clean_auto itself — a cap on the leaves the
//! closeout may expand to, counted over the shared DAG before any walk
//! (`MAX_SUM_NF_LEAVES` / `additive_leaf_count_within`, clean `0f4b211a0`,
//! carried into this repository's `first-party/clean` pin by the 2026-09-28 pin
//! train `ca1ef61a3a`, clean `c3a3b2d615`; recorded in `docs/KNOWN_HAZARDS.md`).
//! Gate 2 mirrors that quantity from outside as a second line of defence, and
//! gate 1 may be dropped once its cost is re-measured against the moved pin.

use std::collections::{BTreeMap, BTreeSet};

use trust_types::{Formula, Sort};

use super::{Atom, int_var_name, linear_mul_operands};

/// The largest multiplier scale gate 1 lets through to the ay solve: see
/// [`pool_coefficient_scale`].
///
/// History: round 1 (2026-09-25) capped the pool's LARGEST coefficient at this
/// value, which a01 (`2^30`) needed. Round 2 measured that the largest single
/// coefficient is the wrong quantity — two coprime guard scalings each at most
/// `2^12` (b01/b02/b45/b46/b48) or a chain of small ones (`3·5·7·11·13`, b03)
/// make ay's certificate multiply them — so the scale is now a product.
pub(super) const AY_RECONSTRUCTION_MAX_COEFFICIENT: u128 = 1 << 12;

/// The most additive leaves gate 2 lets the clean_auto closeout walk for one
/// Farkas step: the same quantity, and the same value, as clean_auto's own cap
/// (`MAX_SUM_NF_LEAVES`, clean `0f4b211a0`), so the in-tree gate and the exact
/// fix agree on what is too big. Measured on the trustc closeout: a multiplier of
/// `2^12` over a few-leaf bound costs nothing measurable, `2^14` about 3 s,
/// `2^16` about 90 s (the match is quadratic in the leaves). Measured on the
/// ui/trust + ui/contracts corpus (1752 distinct violations, 2026-09-26): the
/// largest certificate any row reconstructed through this lane was 24 leaves.
pub(super) const AY_RECONSTRUCTION_MAX_CLOSEOUT_LEAVES: u128 = 1 << 12;

// ---------------------------------------------------------------------------
// Gate 1: the pool.
// ---------------------------------------------------------------------------

/// Accumulate `sign · f` into `out`, a linear form keyed by variable name (a
/// renderable var×var product is one key). Like terms MERGE, so `x + x` is
/// `2·x` — the doubling-chain spelling `x₁ = x₀ + x₀` (probe b49) carries a
/// coefficient of 2 that round 1's per-term reading (the largest literal on
/// any one variable occurrence) took as 1. `false` on a shape outside the
/// renderers (`linear_term_to_kernel`/`term_to_kernel`: variables, literals,
/// `Add`, `Sub`, literal×term and var×var `Mul`) or on overflow.
fn accumulate_linear(f: &Formula, sign: i128, out: &mut BTreeMap<String, i128>) -> bool {
    let mut add = |key: String, by: i128| -> bool {
        let slot = out.entry(key).or_insert(0);
        match slot.checked_add(by) {
            Some(v) => {
                *slot = v;
                true
            }
            None => false,
        }
    };
    match f {
        Formula::Var(name, Sort::Int) => add(name.clone(), sign),
        Formula::SymVar(sym, Sort::Int) => add(sym.as_str().to_string(), sign),
        Formula::Int(_) | Formula::UInt(_) => true,
        Formula::Add(a, b) => accumulate_linear(a, sign, out) && accumulate_linear(b, sign, out),
        Formula::Sub(a, b) => match sign.checked_neg() {
            Some(neg) => accumulate_linear(a, sign, out) && accumulate_linear(b, neg, out),
            None => false,
        },
        Formula::Mul(a, b) => match linear_mul_operands(a, b) {
            Some((lit, term)) => match sign.checked_mul(lit) {
                Some(scaled) => accumulate_linear(term, scaled, out),
                None => false,
            },
            // var×var: the one nonlinear shape `term_to_kernel` renders.
            None => match (int_var_name(a), int_var_name(b)) {
                (Some(x), Some(y)) => {
                    let (x, y) = if x <= y { (x, y) } else { (y, x) };
                    add(format!("{x}*{y}"), sign)
                }
                _ => false,
            },
        },
        _ => false,
    }
}

/// The largest absolute coefficient of the atom's variable part `a - b`, like
/// terms merged: `1` for a closed atom (neutral in a product), `u128::MAX` for
/// a shape outside the renderers, so the gate declines rather than guesses on
/// a shape translation might grow to admit. Every atom reaching the gate has
/// already been rendered (`supported_hyps_from_atoms`), and the unit test
/// `every_renderable_term_has_a_finite_scale` pins that renderer and scan
/// agree — round 1's first cut lacked a `Sub` arm and silently withheld 15 ui
/// rows' certificates at `u128::MAX`.
fn atom_scale(atom: &Atom<'_>) -> u128 {
    let (Atom::Le(a, b) | Atom::Lt(a, b)) = atom;
    let mut form = BTreeMap::new();
    if !(accumulate_linear(a, 1, &mut form) && accumulate_linear(b, -1, &mut form)) {
        return u128::MAX;
    }
    form.values().map(|c| c.unsigned_abs()).max().unwrap_or(0).max(1)
}

/// Gate 1's scale: the PRODUCT, over the pool's atoms, of each atom's largest
/// coefficient (like terms merged; see [`atom_scale`]). Saturating.
///
/// WHY A PRODUCT. A Farkas multiplier exists to cancel coefficients, and a
/// certificate that cancels two coprime scalings `p` and `q` needs `p·q`: the
/// guards `a·4093 < K ∧ b·4091 < K` under a same-stride capacity row are
/// certified by ay with coefficients `4093/4091`, integer multipliers
/// `4093·4091` (probe b45), although no literal exceeds `2^12`. Round 1's gate
/// took the MAXIMUM and let exactly that class through.
///
/// WHAT IT IS NOT. A bound: a certificate over many unit rows can still need a
/// large multiplier, and one over two unrelated scalings needs none. Gate 2
/// ([`alethe_closeout_estimate`]) reads the multipliers ay actually chose.
pub(super) fn pool_coefficient_scale(atoms: &[Atom<'_>]) -> u128 {
    atoms.iter().map(atom_scale).fold(1u128, u128::saturating_mul)
}

// ---------------------------------------------------------------------------
// Gate 2: ay's certificate.
// ---------------------------------------------------------------------------

/// What gate 2 reads off ay's rendered refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct CloseoutEstimate {
    /// The largest, over the proof's Farkas steps, of `Σ kᵢ · leavesᵢ`:
    /// saturating, `u128::MAX` for a step whose coefficients cannot be read.
    pub(super) worst_leaves: u128,
    /// Steps rendered `hole` or `trust`: the rendering does not show what they
    /// are, so a raw Farkas lemma among them has no visible multiplier.
    pub(super) opaque_steps: u32,
    /// Farkas steps read.
    pub(super) farkas_steps: u32,
}

/// One parsed s-expression of the Alethe rendering, borrowing its tokens.
#[derive(Debug)]
enum Sx<'a> {
    Atom(&'a str),
    List(Vec<Sx<'a>>),
}

impl<'a> Sx<'a> {
    fn atom(&self) -> Option<&'a str> {
        match self {
            Sx::Atom(s) => Some(s),
            Sx::List(_) => None,
        }
    }
    fn list(&self) -> Option<&[Sx<'a>]> {
        match self {
            Sx::List(items) => Some(items),
            Sx::Atom(_) => None,
        }
    }
}

/// Parse a whole Alethe document into its top-level s-expressions. Iterative
/// (no recursion on nesting depth). `None` on unbalanced parentheses.
fn parse_sexprs(text: &str) -> Option<Vec<Sx<'_>>> {
    let bytes = text.as_bytes();
    let mut stack: Vec<Vec<Sx<'_>>> = vec![Vec::new()];
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => {
                stack.push(Vec::new());
                i += 1;
            }
            b')' => {
                let done = stack.pop()?;
                stack.last_mut()?.push(Sx::List(done));
                i += 1;
            }
            b if b.is_ascii_whitespace() => i += 1,
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'|' | b'"' => {
                let close = bytes[i];
                let start = i;
                i += 1;
                while i < bytes.len() && bytes[i] != close {
                    i += 1;
                }
                if i == bytes.len() {
                    return None;
                }
                i += 1;
                stack.last_mut()?.push(Sx::Atom(&text[start..i]));
            }
            _ => {
                let start = i;
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !matches!(bytes[i], b'(' | b')' | b'|' | b'"' | b';')
                {
                    i += 1;
                }
                stack.last_mut()?.push(Sx::Atom(&text[start..i]));
            }
        }
    }
    if stack.len() != 1 {
        return None;
    }
    stack.pop()
}

/// A non-negative rational `num/den`, reduced, from an Alethe `:args` entry:
/// `3`, `-3`, `4093.0`, `1.5`, `(/ 4093.0 4091.0)`, `(- 3)`. Signs are dropped
/// (a Farkas coefficient is non-negative, and only the magnitude sizes the
/// walk). `None` on anything else, or on a numeral past `u128`.
fn parse_coefficient(sx: &Sx<'_>) -> Option<(u128, u128)> {
    fn numeral(s: &str) -> Option<(u128, u128)> {
        let s = s.strip_prefix('-').unwrap_or(s);
        let (int, frac) = match s.split_once('.') {
            Some((int, frac)) => (int, frac),
            None => (s, ""),
        };
        if int.is_empty() || !int.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        if !frac.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let frac = frac.trim_end_matches('0');
        let mut num: u128 = 0;
        for b in int.bytes().chain(frac.bytes()) {
            num = num.checked_mul(10)?.checked_add(u128::from(b - b'0'))?;
        }
        let den = 10u128.checked_pow(u32::try_from(frac.len()).ok()?)?;
        Some(reduce(num, den))
    }
    match sx {
        Sx::Atom(s) => numeral(s),
        Sx::List(items) => match items.as_slice() {
            [op, x] if op.atom() == Some("-") => parse_coefficient(x),
            [op, n, d] if op.atom() == Some("/") => {
                let (n_num, n_den) = parse_coefficient(n)?;
                let (d_num, d_den) = parse_coefficient(d)?;
                if d_num == 0 {
                    return None;
                }
                Some(reduce(n_num.checked_mul(d_den)?, n_den.checked_mul(d_num)?))
            }
            _ => None,
        },
    }
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn reduce(num: u128, den: u128) -> (u128, u128) {
    let g = gcd(num, den).max(1);
    (num / g, den / g)
}

/// Deepest literal nesting [`literal_leaves`] follows; deeper answers
/// `u128::MAX` (the gate declines — authority only).
const MAX_LITERAL_DEPTH: usize = 512;

/// The additive leaves `IntAddNf::flatten` visits in the translated literal:
/// `+` splits (ay's `translate_nary_arith_app` folds it into `Int.add`), and so
/// — conservatively — does `-`; every other term is one leaf. `let` binders
/// and `(! t :named n)` are followed. Also at least the literal's distinct
/// symbols plus two: ay may hold the literal in a normalized linear form whose
/// rendering (the authored spelling) has fewer leaves, and a normalized form
/// has at most one leaf per variable plus a constant on each side.
fn literal_leaves(literal: &Sx<'_>, named: &mut BTreeMap<String, u128>) -> u128 {
    fn leaves<'a>(
        sx: &Sx<'a>,
        env: &mut Vec<(&'a str, u128)>,
        named: &mut BTreeMap<String, u128>,
        symbols: &mut BTreeSet<&'a str>,
        depth: usize,
    ) -> u128 {
        if depth > MAX_LITERAL_DEPTH {
            return u128::MAX;
        }
        match sx {
            Sx::Atom(s) => {
                if let Some((_, n)) = env.iter().rev().find(|(name, _)| name == s) {
                    return *n;
                }
                if let Some(n) = named.get(*s) {
                    return *n;
                }
                if !s.starts_with(|c: char| c.is_ascii_digit() || c == '-') {
                    symbols.insert(s);
                }
                1
            }
            Sx::List(items) => {
                let Some((head, rest)) = items.split_first() else { return 1 };
                match head.atom() {
                    Some("not") => rest
                        .iter()
                        .map(|x| leaves(x, env, named, symbols, depth + 1))
                        .fold(0, u128::saturating_add),
                    Some("<=" | "<" | ">=" | ">" | "=" | "+" | "-") => rest
                        .iter()
                        .map(|x| leaves(x, env, named, symbols, depth + 1))
                        .fold(0, u128::saturating_add),
                    Some("let") => {
                        let [bindings, body] = rest else { return u128::MAX };
                        let Some(bindings) = bindings.list() else { return u128::MAX };
                        let mark = env.len();
                        let mut bound = Vec::with_capacity(bindings.len());
                        for binding in bindings {
                            let Some([name, value]) = binding.list() else { return u128::MAX };
                            let Some(name) = name.atom() else { return u128::MAX };
                            bound.push((name, leaves(value, env, named, symbols, depth + 1)));
                        }
                        env.extend(bound);
                        let n = leaves(body, env, named, symbols, depth + 1);
                        env.truncate(mark);
                        n
                    }
                    Some("!") => {
                        let Some(term) = rest.first() else { return u128::MAX };
                        let n = leaves(term, env, named, symbols, depth + 1);
                        let mut attrs = rest[1..].iter();
                        while let Some(attr) = attrs.next() {
                            if attr.atom() == Some(":named") {
                                if let Some(name) = attrs.next().and_then(Sx::atom) {
                                    named.insert(name.to_string(), n);
                                }
                            }
                        }
                        n
                    }
                    _ => {
                        // One opaque leaf (a product, an application); its
                        // symbols still count toward the normalized-form floor.
                        let _ = rest
                            .iter()
                            .map(|x| leaves(x, env, named, symbols, depth + 1))
                            .fold(0, u128::saturating_add);
                        1
                    }
                }
            }
        }
    }
    let mut symbols = BTreeSet::new();
    let printed = leaves(literal, &mut Vec::new(), named, &mut symbols, 0);
    printed.max((symbols.len() as u128).saturating_add(2))
}

/// Gate 2's reading of ay's rendered refutation `alethe`: for each Farkas step
/// (`la_generic`, or `lia_generic`, whose missing `:args` clean_auto reads as
/// all-unit), the integer multipliers clean_auto replays — the coefficients
/// times the LCM of their denominators (`rationalize_to_positive_ints`) — times
/// each literal's leaves ([`literal_leaves`]), summed. `None` when the text does
/// not parse as s-expressions.
pub(super) fn alethe_closeout_estimate(alethe: &str) -> Option<CloseoutEstimate> {
    let commands = parse_sexprs(alethe)?;
    let mut estimate = CloseoutEstimate { worst_leaves: 0, opaque_steps: 0, farkas_steps: 0 };
    let mut named = BTreeMap::new();
    for command in &commands {
        let Some(items) = command.list() else { continue };
        // Record `:named` terms wherever they appear, so later references to
        // them are sized (assumptions name terms too).
        if items.first().and_then(Sx::atom) == Some("assume") {
            if let Some(term) = items.get(2) {
                let _ = literal_leaves(term, &mut named);
            }
            continue;
        }
        if items.first().and_then(Sx::atom) != Some("step") {
            continue;
        }
        let keyword = |key: &str| {
            items.iter().position(|x| x.atom() == Some(key)).and_then(|i| items.get(i + 1))
        };
        let Some(rule) = keyword(":rule").and_then(Sx::atom) else {
            estimate.worst_leaves = u128::MAX;
            continue;
        };
        match rule {
            "la_generic" | "lia_generic" => {}
            "hole" | "trust" => {
                estimate.opaque_steps += 1;
                continue;
            }
            _ => continue,
        }
        estimate.farkas_steps += 1;
        let clause = items.get(2).and_then(Sx::list).and_then(|clause| {
            let (head, literals) = clause.split_first()?;
            (head.atom() == Some("cl")).then_some(literals)
        });
        let Some(clause) = clause else {
            estimate.worst_leaves = u128::MAX;
            continue;
        };
        let coefficients: Option<Vec<(u128, u128)>> = match keyword(":args") {
            Some(args) => args.list().and_then(|args| {
                (args.len() == clause.len())
                    .then(|| args.iter().map(parse_coefficient).collect::<Option<Vec<_>>>())
                    .flatten()
            }),
            None => Some(vec![(1, 1); clause.len()]),
        };
        let step = coefficients.and_then(|coefficients| {
            let mut lcm: u128 = 1;
            for &(_, den) in &coefficients {
                lcm = (lcm / gcd(lcm, den).max(1)).checked_mul(den)?;
            }
            let mut total: u128 = 0;
            for (literal, &(num, den)) in clause.iter().zip(&coefficients) {
                let k = num.checked_mul(lcm / den.max(1))?;
                total = total.saturating_add(k.saturating_mul(literal_leaves(literal, &mut named)));
            }
            Some(total)
        });
        estimate.worst_leaves = estimate.worst_leaves.max(step.unwrap_or(u128::MAX));
    }
    Some(estimate)
}

/// Gate 2's measure over ay's rendered refutation: the estimate's
/// `worst_leaves`, or `u128::MAX` — decline — when there is nothing to read.
/// That is: no rendering at all (`None`: ay refused to render against the
/// authored premise scope, while the reconstruction reads its RAW proof and
/// would still run), text that does not parse, or any `hole`/`trust` step (ay
/// renders a Farkas lemma it cannot lower to `la_generic` as `hole`, without
/// its coefficients, and clean_auto still replays the raw multipliers). Each
/// of these withholds `Certified` only; none occurred among the rows the ui
/// corpus certifies through this lane (2026-09-26 census).
pub(super) fn closeout_leaves(alethe: Option<&str>) -> u128 {
    match alethe.and_then(alethe_closeout_estimate) {
        Some(estimate) if estimate.opaque_steps == 0 => estimate.worst_leaves,
        _ => u128::MAX,
    }
}

/// Opt-in census of both gates: with `TRUST_CERTIFY_SCALE_GATE_LOG=<path>`,
/// every decline appends one line to `<path>` naming the gate, its measure and
/// the pool's variables, so a suite run lists every row the gates withheld
/// `Certified` from. Unset — the normal case — it does nothing.
pub(super) fn note_decline(gate: &str, measure: u128, var_names: &BTreeSet<String>) {
    let Some(path) = std::env::var_os("TRUST_CERTIFY_SCALE_GATE_LOG") else { return };
    if let Ok(mut file) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        use std::io::Write as _;
        let names: Vec<&str> = var_names.iter().map(String::as_str).collect();
        let _ = writeln!(file, "gate={gate} scale={measure} vars={}", names.join(","));
    }
}

#[cfg(test)]
#[path = "reconstruction_scale_tests.rs"]
mod tests;
