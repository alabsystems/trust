// Trust (2026-10-07, PATH-GUARD-VALUE-1): a path guard is spelled by the VALUE its
// subject holds at the guard, not by the subject's reaching-definition SET.
//
// THE DEFECT. Since S2c deleted the path-guard kill, every path guard has been renamed
// with `version_rename_at` at its SOURCE block's terminal and conjoined with the row's
// body, which is renamed at the ROW's point. A version token spells a reaching-def SET
// (D15), and two points can share a set while reading different values. In
//
// ```text
// let mut len = m;
// for &c in xs {
//     match len { 3 => {} _ => return acc }   // S: guard `len == 3`
//     if c { len = n; }                        // W
//     acc ^= buf[len];                         // B: `len >= 8` violates
// }
// ```
//
// `len` reaches the loop header (the guard's source `S`) as `{m, W}` through the back
// edge and reaches `B` as `{m, W}` through the join after `if c`: one spelling,
// `len#s0_0_s9_0`. The guard `len#s0_0_s9_0 == 3` therefore pinned the value `B`
// reads, the path `S -> W -> B` (where `B` reads `n`) lost its counterexample, and
// the bounds row PROVED — kernel-certified — on a program that panics with
// `xs = [true], m = 3, n = 100`.
//
// THE FIX. Each guard variable keeps its token spelling only when that spelling
// provably names, at the row's block, the value the guard tested; otherwise it is
// spelled with a GUARD-LOCAL token (`crate::GUARD_VALUE_TOKEN_PREFIX`) that no body
// read shares, so the guard constrains a value of its own and nothing else. The
// identity is the SSA [`ValueId`]: the key the dominating-guard miner moved to for
// the same defect (`dominating_facts`, `StmtVersionCtx::value_id_at`), here through
// `StmtVersionCtx::value_id_at_grouped`, which also names a read two or more tracked
// names rebind.
//
// Let the guard read `x` at `(S, |S|)` with token `t` and value id `v`, and let the
// row live in block `B`.
//
//  * `t` absent (bare: entry value or untracked) — unchanged, as before.
//  * `v` is `Entry` or `Def` — keep `x#t`. A `Def` id means the reaching set is that
//    single definition `D`; every point spelling `x#t` reads `D`'s most recent
//    execution, and `D` dominates every such read.
//  * `v` is `Phi { J }` and `B`'s ENTRY reads `x` with the same token AND the same id —
//    keep `x#t`. Within `B` a token changes only at an in-block write, whose token
//    `s{B}_k` is a single definition, so every read of `B` spelled `x#t` reads the
//    value `B`'s entry reads.
//  * `v` is `GroupOut { D }` — a read two or more tracked names rebind
//    (`StmtVersionCtx::value_id_at_grouped`, 2026-10-17): exactly as for `Phi`. Its
//    point, the exit of the group's def site `D`, strictly dominates both reads with
//    no def site of any member after it on the way, so `J = D` below.
//  * otherwise — `x#gv_p{J}` for a join id, `x#gv_b{S}` when no id names the value.
//
// SOUNDNESS. Take a run reaching `B` and erase its loops chronologically. The result
// is a simple CFG path from the entry, so it is one of the enumerated guard paths (a
// truncated list only drops hypotheses), each block on it appears at its LAST visit,
// and each guard on it held at its source's last visit. If `S` and `B` read `x` with
// the same id `J` (a def or a join), `J` dominates both. Were `J` executed after `S`'s
// last visit, that execution would erase `S` from the loop-erased path (`J` precedes
// `S` on every path from the entry) — so the guard tested the very value `B` reads,
// and a shared name is a true equality. A guard-local name is a fresh variable
// carrying only the guard's own constraint: two guards share one only when they read
// the same join (the same value, by the argument above) or come from the same source
// block (once per simple path). So every real violation remains a model of its own
// path disjunct, and UNSAT still means no violation.
//
// REFUTATION polarity cannot use a guard-local name — a weakened path condition can
// manufacture a witness — so [`guard_needs_value_spelling`] lets
// `v2_formula_with_refutation_path_guards` decline instead.
//
// PRECISION. A guard and a read of the same value (no write between them, or a write
// only on a path that does not reach `B` without passing the guard again) keep one
// name exactly as before. A program whose proof needed the guard to constrain a value
// written after it — `if c { len = 2 }` under a `len == 3` loop-head guard — loses
// that proof: the guard does not constrain the written value, and recovering it needs
// path-sensitive join resolution, which this does not attempt.

use trust_types::{BlockId, Formula, VerifiableFunction};

use super::StmtVersionCtx;
use super::version_ssa::ValueId;

/// How the guard variable `name`, read at the terminal of `src`, is spelled in a row of
/// block `at`: `None` when it stays bare, else the full `name#token` spelling.
fn guard_var_spelling(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    src: BlockId,
    terminal: usize,
    at: BlockId,
    name: &str,
) -> Option<String> {
    let token = sv.version_token_at(func, src, terminal, name)?;
    let at_source = sv.value_id_at_grouped(func, src, terminal, name);
    let keep = match at_source {
        Some(ValueId::Entry | ValueId::Def { .. }) => true,
        // Trust (2026-10-17, gate RCA precision T3): a read two or more tracked names
        // rebind is named too (`value_id_at_grouped`; it was `None`, so respelled
        // guard-local even with nothing written between the guard and the row). Its
        // exit value at a def site keeps the token under the row-entry test of a join:
        // the token need not be a singleton.
        Some(id @ (ValueId::Phi { .. } | ValueId::GroupOut { .. })) => {
            (src == at && terminal == 0)
                || (sv.version_token_at(func, at, 0, name).as_deref() == Some(token.as_str())
                    && sv.value_id_at_grouped(func, at, 0, name) == Some(id))
        }
        None => false,
    };
    if keep {
        return Some(format!("{name}#{token}"));
    }
    Some(match at_source {
        Some(ValueId::Phi { node }) => {
            format!("{name}#{}p{node}", crate::GUARD_VALUE_TOKEN_PREFIX)
        }
        _ => format!("{name}#{}b{}", crate::GUARD_VALUE_TOKEN_PREFIX, src.0),
    })
}

/// Zero-allocation check for whether `guard_var_spelling` would give `var_name` a
/// guard-local spelling at `terminal` of `src` for a row of block `at`.
fn guard_var_needs_value_spelling(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    src: BlockId,
    terminal: usize,
    at: BlockId,
    var_name: &str,
) -> bool {
    if var_name.contains('#') {
        return false;
    }
    let Some(token) = sv.version_token_at(func, src, terminal, var_name) else {
        return false;
    };
    let at_source = sv.value_id_at_grouped(func, src, terminal, var_name);
    let keep = match at_source {
        Some(ValueId::Entry | ValueId::Def { .. }) => true,
        Some(id @ (ValueId::Phi { .. } | ValueId::GroupOut { .. })) => {
            (src == at && terminal == 0)
                || (sv.version_token_at(func, at, 0, var_name).as_deref() == Some(token.as_str())
                    && sv.value_id_at_grouped(func, at, 0, var_name) == Some(id))
        }
        None => false,
    };
    !keep || token.starts_with(crate::GUARD_VALUE_TOKEN_PREFIX)
}

/// Zero-allocation check for whether a single variable `var_name` read at the terminal of
/// `src` would receive a guard-local spelling for a row of block `at`.
pub(super) fn guard_var_needs_value_spelling_at(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    src: BlockId,
    at: BlockId,
    var_name: &str,
) -> bool {
    let terminal = source_terminal(func, src);
    guard_var_needs_value_spelling(func, sv, src, terminal, at, var_name)
}

/// The guard `guard` (as `guards::guard_to_formula` lowered it) of an edge leaving
/// `src`, spelled for a row of block `at`: every place read versioned at `src`'s
/// terminal exactly as `version_rename_at` does, except that a read whose token does
/// not name, at `at`, the value the guard tested gets a guard-local spelling (see the
/// module comment). Names already carrying a `#` pass through, as in
/// `version_rename_at`.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn spell_path_guard(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    guard: &Formula,
    src: BlockId,
    at: BlockId,
) -> Formula {
    spell_path_guard_owned(func, sv, guard.clone(), src, at)
}

/// Owned counterpart of [`spell_path_guard`] that maps `guard` in place without cloning.
pub(super) fn spell_path_guard_owned(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    guard: Formula,
    src: BlockId,
    at: BlockId,
) -> Formula {
    let terminal = source_terminal(func, src);
    if !super::path_defs::version_rename_needs_rewrite(&guard, sv, func, src, terminal) {
        return guard;
    }
    guard.map(&mut |node| match node {
        Formula::Var(name, sort) if !name.contains('#') => {
            match guard_var_spelling(func, sv, src, terminal, at, &name) {
                Some(spelled) => Formula::Var(spelled, sort),
                None => Formula::Var(name, sort),
            }
        }
        other => other,
    })
}

/// Whether [`spell_path_guard`] would give some read of `guard` a guard-local spelling
/// for a row of block `at` — i.e. whether the plain token spelling would tie the guard
/// to a value it did not test. The refutation lane declines such a path list.
pub(super) fn guard_needs_value_spelling(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    guard: &Formula,
    src: BlockId,
    at: BlockId,
) -> bool {
    let terminal = source_terminal(func, src);
    trust_types::any_formula_node(guard, &mut |node| {
        matches!(
            node,
            Formula::Var(name, _)
                if guard_var_needs_value_spelling(func, sv, src, terminal, at, name)
        )
    })
}

/// The statement count of `src` (its terminal point), `0` when the slot is missing —
/// the same fallback `v2_formula_with_path_guards_recorded` always used.
fn source_terminal(func: &VerifiableFunction, src: BlockId) -> usize {
    func.body.blocks.get(src.0).filter(|b| b.id == src).map_or(0, |b| b.stmts.len())
}
