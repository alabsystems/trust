//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ forbid-output: was not discharged
//! THE THREE-PATH POSITIVE (two-language battery blocker a7).
//!
//! A CONDITIONAL postcondition over a body with three return paths, written as
//! the value-producing `if`/`else if`/`else` EXPRESSION. This file used to be a
//! `check-fail` FRONTIER fixture pinning that this exact source did NOT
//! discharge. It is now the positive, because the cause was found and removed.
//!
//! # What the cause was, measured
//!
//! rustc lowers this body to a Return block with TWO predecessors, not three:
//!
//! ```text
//! bb0: _5 = Ge(a, 1000000);  switchInt(_5) -> [0: bb1, otherwise: bb4]
//! bb1: _6 = Ge(b, a);        switchInt(_6) -> [0: bb3, otherwise: bb2]
//! bb2: _3 = b;  goto -> bb5
//! bb3: _3 = a;  goto -> bb5
//! bb4: _4 = 1000000;  goto -> bb6
//! bb5: _4 = _3;       goto -> bb6      <- the `goto`-only JOIN of the inner if
//! bb6: _0 = _4;  return
//! ```
//!
//! `bb4` is reached by ONE guard path and `bb5` by TWO, and vcgen emitted one
//! postcondition row per PREDECESSOR. So the two rows had different shapes:
//! `bb4`'s a flat `And`, `bb5`'s an `Or([And([guards_1, body]),
//! And([guards_2, body])])`. MEASURED on the managed
//! `trustc 1.99.0-dev (d75f13f97 2026-09-15)`, `-Ztrust-verify-output=both`:
//!
//! ```text
//! vc:…:postcondition:0  proved   trust-full-verifier   (flat; trust-mc PDR receipt)
//! vc:…:postcondition:1  proved   ay-in-process         (Or-shaped; NO receipt)
//! obligation:…:postcondition:0  UNKNOWN  trust-exact-source-clause-discharge
//! ```
//!
//! Both body rows read `Proved` and the clause was still refused, because a
//! source clause composes only from `KernelCertified | FreshExactDirectChcPdr`
//! and the disjunctive row carried neither. On stage1 at `8113b3a0a81`
//! (2026-09-17) the same row was simply `UNKNOWN` instead. Two toolchains, two
//! different verdicts on that row — and the SAME row, the disjunctive one, in
//! both.
//!
//! # Why the row count, the connective and the arithmetic were all red herrings
//!
//! `source_clause_conditional_postcondition_early_return.rs` is this function
//! again — same clause, same three paths, same arithmetic — with the guards
//! spelled as early `return`s. rustc gives each `return` its own `Return`
//! block, so each path gets its own FLAT row, and that file measures
//! `4 proved, 0 failed, 0 unknown` with the marker DISCHARGED on the same
//! toolchain that leaves this one pending.
//!
//! STATED PRECISELY: the disjunctive shape is NECESSARY, not sufficient. The
//! clause's own difficulty decides whether the merged row survives it —
//! `postcondition_composition_at_call_site.rs`'s `clamp_low` is this exact
//! three-arm chain under `ensures result >= 0 && result <= 1000000` and reports
//! `3 proved / 3` today, merged `Or` row and all. So the `Or` shape is what puts
//! a row at RISK, and splitting removes the risk for every clause rather than
//! for the easy ones only.
//!
//! # The fix
//!
//! `generate_v2_contract_vcs_impl` now emits ONE ROW PER ENUMERATED RETURN
//! PATH: a predecessor reached by `n` guard paths contributes `n` flat rows
//! instead of one `Or` of `n`. `Or(t_1..t_n)` is UNSAT exactly when every `t_i`
//! is UNSAT, so the split distributes the path-guard conjunct — it adds no
//! fact, drops none and changes none, and the conjunction of the emitted rows
//! is logically identical to the single row it replaces. (It is not "pure
//! distribution" of the whole pipeline: three steps of the shared tail walk
//! only the positive `And` spine, which an `Or`-rooted row does not have, so a
//! per-path row can be strictly more PROVABLE than the merged row's
//! corresponding disjunct — never more credulous. See
//! `generate_v2_contract_vcs_impl`'s comment.)
//!
//! # What this file asserts — MEASURED 2026-09-18
//!
//! `check-pass` plus `forbid-output: was not discharged`: the clause must
//! DISCHARGE, not merely avoid an error. On a stage1 built from the tree that
//! landed the split, `-Ztrust-verify=on -Ztrust-verify-output=both` on this
//! source reports:
//!
//! ```text
//! note: Trust verification: 4 proved, 0 failed, 0 unknown, 0 timed out, ... out of 4 obligation(s)
//!   vc:…__pick:postcondition:0   proved  trust-full-verifier
//!   vc:…__pick:postcondition:1   proved  trust-full-verifier
//!   vc:…__pick:postcondition:2   proved  trust-full-verifier
//!   obligation:…__pick:postcondition:0  proved  trust-exact-source-clause-discharge
//! ```
//!
//! Three flat per-path rows where there were two rows of different shapes, and
//! the marker discharged. Its one-path-false twin
//! (`..._false_one_path.rs`) measures `2 proved, 2 unknown / 4` on the SAME
//! build, with exactly `postcondition:1` — the violating path's own row —
//! unknown: the split isolates the bad path rather than dissolving it.
//!
//! # What to do when it is RED
//!
//! If it is red, read the marker's own note (the 2026-09-17 diagnostic names
//! the defeated body row) and then:
//!
//!   * every per-path row proved but the marker still pends -> the composition
//!     rule, not the row shape, is the remaining blocker: that is the owner
//!     ruling recorded in `docs/STRICT_VERIFICATION_FRAGMENT.md` §19.3;
//!   * one per-path row is unknown -> the split reached the row but the engine
//!     still declines it; record WHICH row and its evidence status, restore
//!     this file to `check-fail` with a span-anchored ERROR plus a follow-on
//!     NOTE for "was not discharged", and say so. Do NOT relax the
//!     `forbid-output` to keep it green — that assertion is the whole point.
//!
//!     (Spell those annotations only in the restored file, never in prose:
//!     compiletest's scanner matches its `~` marker ANYWHERE on a line,
//!     INCLUDING inside a `//!` doc comment — `errors.rs:load_errors` reads
//!     every line of the file and its regex is unanchored — so a marker written
//!     as an example silently becomes a real expectation, and a bare follow-on
//!     marker with no preceding anchor panics the harness outright.)
//!
//! The negative twins that must stay refused either way are
//! `source_clause_conditional_postcondition_false_one_path.rs` (false on one
//! path, this same shape) and `..._false_twin.rs` (false on two).

pub fn pick(a: u32, b: u32) -> u32
    ensures a <= 1000000 ==> result >= a
{
    if a >= 1000000 {
        1000000
    } else if b >= a {
        b
    } else {
        a
    }
}
