//! The translation rules and their approximation direction (Critique C-1,
//! change 3): every rule is exact, over-approximating (more behaviours than
//! the program: a refutation through it is `PC-OVERAPPROX`, C-9), or
//! under-approximating (fewer behaviours: a "not refuted" rests on it, so
//! it is a PRINTED PREMISE of every root that uses it, or a refusal).
//! `tests` check that every `Under` row names a premise or a refusal code.

/// Approximation direction of a rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    Exact,
    /// The model has more behaviours than the program.
    Over,
    /// The model has fewer behaviours than the program.
    Under,
}

/// One translation rule (design §2.4 rows, as C0 implements them).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rule {
    pub id: &'static str,
    pub construct: &'static str,
    pub emits: &'static str,
    pub direction: Direction,
    /// For `Under`: the premise code printed with every verdict that rests
    /// on it, or the refusal code the census raises instead.
    pub premise_or_refusal: Option<&'static str>,
}

const fn rule(
    id: &'static str,
    construct: &'static str,
    emits: &'static str,
    direction: Direction,
    premise_or_refusal: Option<&'static str>,
) -> Rule {
    Rule { id, construct, emits, direction, premise_or_refusal }
}

use Direction::{Exact, Over, Under};

/// Premise: a panic (failed `assert`, a call to a panicking function) ends
/// the path; unwinding into callers' drops is not modeled.
pub const P_PANIC: &str = "P-PANIC-ENDS-PATH";
/// Premise: a wrapping integer `add`/`sub` on a tracked value does not wrap
/// on the explored paths (a path on which it would is cut). Discharged, and
/// not printed, where the census proves it (a descriptor loop's `v + 1`
/// under `v < hi`).
pub const P_NO_WRAP: &str = "P-NO-WRAP";
/// Premise: a `pre_exec` closure is checked in the child of a harness spawn
/// made right after the registration: a plain command, inherited stdio, no
/// other hook (the real command is not seen until C4).
pub const P_HOOK_HARNESS: &str = "P-HOOK-HARNESS";
/// Premise: the site's fd-inherit policy has no lanes (C0 does not compute
/// placement lanes): a descriptor the child must hold but lacks is not
/// reported; leaks are.
pub const P_NO_LANES: &str = "P-NO-LANES";
/// Premise: a raw `fork` succeeds (the derivation's fork step has no
/// failure outcome): the parent's `-1` path is not explored.
pub const P_FORK_SUCCEEDS: &str = "P-FORK-SUCCEEDS";
/// Premise: a std row's steps take their nominal outcome (the derivation
/// lowers rows nominal-only): the row's `Err` path is not explored.
pub const P_STD_ROW_NOMINAL: &str = "P-STD-ROW-NOMINAL";

/// Every rule C0 applies.
pub const RULES: &[Rule] = &[
    rule("const", "Const int/bool", "a literal operand", Exact, None),
    rule("binop-fold", "BinOp/ICmp/Cast over literals", "a folded literal", Exact, None),
    rule("icmp", "ICmp over tracked scalars", "a Cond kept for the branch", Exact, None),
    rule(
        "add-sub",
        "add/sub (wrapping) of tracked scalars",
        "Assign Add, then a wrap check that cuts the path",
        Under,
        Some(P_NO_WRAP),
    ),
    rule(
        "add-overflow",
        "add.overflow/sub.overflow",
        "Assign Add + an exact overflow flag over the i64 sum",
        Exact,
        None,
    ),
    rule(
        "reinterpret",
        "bitcast/zext/sext between integer types",
        "the value in the target type's range (a diamond when the sign changes)",
        Exact,
        None,
    ),
    rule(
        "trunc",
        "trunc of a tracked value",
        "Expr::Opaque (origin: truncating cast)",
        Exact,
        Some("PC-FD-TRUNC"),
    ),
    rule(
        "opaque",
        "a value the census does not track (root scalar parameters, effect-free std/core results, \
         unsupported ops, loads through unknown pointers)",
        "Expr::Opaque: exact while it reaches no operand, guard or loop bound",
        Exact,
        Some("PC-UNTRACKED-FD"),
    ),
    rule(
        "nondet",
        "a guard over an untracked value",
        "Cond::Nondet: both arms explored",
        Over,
        Some("PC-OVERAPPROX"),
    ),
    rule(
        "block-param",
        "block parameters",
        "variables assigned on each incoming edge (parallel copies)",
        Exact,
        None,
    ),
    rule("cell", "non-escaping alloca", "one variable per scalar leaf", Exact, None),
    rule(
        "escape",
        "a pointer to a cell passed to a callee the census does not model",
        "the cell's leaves become untracked (havoc)",
        Exact,
        Some("PC-FD-ESCAPE"),
    ),
    rule("call-body", "a call to a spliced local body", "StmtKind::Call (inlined)", Exact, None),
    rule(
        "libc-clause",
        "a call to a modeled libc clause",
        "an Event with the nominal outcome and ONE representative of the environment failures \
         the clause admits (errno is untracked: every failure binds -1 alike)",
        Exact,
        None,
    ),
    rule(
        "fcntl-arg",
        "fcntl with a command that reads an argument, called without one",
        "nothing (the argument is undefined in C)",
        Exact,
        Some("PC-NONCONST-ARG"),
    ),
    rule(
        "fork",
        "a raw libc fork in the root process",
        "StmtKind::Fork; the child runs a cloned continuation with the result 0",
        Exact,
        None,
    ),
    rule(
        "fork-fails",
        "a raw fork's failure (EAGAIN, ENOMEM)",
        "not explored (the derivation's fork step is nominal only)",
        Under,
        Some(P_FORK_SUCCEEDS),
    ),
    rule(
        "exec-site",
        "an exec* in a forked child",
        "its census site maps to the program site of the child's fork (its verdict is the fork's)",
        Exact,
        None,
    ),
    rule("exec-root", "an exec* in the root process", "nothing", Exact, Some("PC-UNMODELED")),
    rule(
        "forrange",
        "a descriptor loop (v from lo, +1, while v < hi, table-local body) in a forked child",
        "StmtKind::ForRange (one SD-3 step)",
        Exact,
        None,
    ),
    rule(
        "pre-exec-harness",
        "CommandExt::pre_exec(closure) on a command the census does not see",
        "a current Trust SP1 harness Command::spawn (fork path, default strip) running the closure, right after the registration",
        Under,
        Some(P_HOOK_HARNESS),
    ),
    rule(
        "no-lanes",
        "the fd-inherit policy of a spawn site",
        "FdInherit { lanes: [] }",
        Under,
        Some(P_NO_LANES),
    ),
    rule(
        "panic",
        "assert failure, a call to a panicking function",
        "the path ends (a pre_exec hook returns Err)",
        Under,
        Some(P_PANIC),
    ),
    rule(
        "unreachable",
        "unreachable, assume(false)",
        "the path ends (undefined behaviour otherwise)",
        Exact,
        None,
    ),
    rule(
        "exit-root",
        "_exit in the root process",
        "the path ends (single-threaded roots only)",
        Exact,
        None,
    ),
    rule(
        "pure-std",
        "a std/core/alloc function on the census's audited effect-free lists (crate::audit; \
         one dispatching through trait impls only with integer arguments)",
        "an untracked result",
        Exact,
        Some("PC-UNKNOWN-STD"),
    ),
    rule(
        "core-alloc",
        "any other core/alloc (or std) function: a combinator may run a closure or a user impl",
        "nothing",
        Exact,
        Some("PC-UNKNOWN-STD"),
    ),
    rule(
        "std-row",
        "a std-table row the census translates generically (pipe, pair, accept, try_clone)",
        "StdCall::Row, lowered by the derivation with nominal step outcomes",
        Under,
        Some(P_STD_ROW_NOMINAL),
    ),
    rule(
        "thread-spawn",
        "std::thread::spawn and its kin (a closure run on another thread)",
        "nothing (dynamic thread roots are M2's SpawnThread)",
        Exact,
        Some("PC-THREAD-UNRESOLVED"),
    ),
    rule(
        "mem-drop",
        "std::mem::drop(x)",
        "nothing when x's drop glue is certainly empty; otherwise",
        Exact,
        Some("PC-DROP-UNMODELED"),
    ),
    rule(
        "drop-gate",
        "a value on the path whose drop glue may have a platform effect (an fd carrier, a Drop \
         impl), or a body without typeck drop facts",
        "nothing (trust-ir elides drops until Step-2 inc 4b)",
        Exact,
        Some("PC-DROP-ELIDED"),
    ),
    rule(
        "effects-covered",
        "a body on the path whose HIR calls (anything but audited effect-free callees) are not \
         all in its trust-ir, or whose HIR list is unavailable",
        "nothing",
        Exact,
        Some("PC-PRODUCER-ERASED"),
    ),
    rule(
        "upstream-call",
        "a call into an upstream crate (a site when the symbol census lists it spawn-capable, or \
         did not run)",
        "nothing (fragments are C8)",
        Exact,
        Some("PC-UPSTREAM"),
    ),
    rule(
        "load-reinterpret",
        "a load or store of an integer cell as another integer type",
        "the same-width reinterpretation; another width is untracked",
        Exact,
        None,
    ),
    rule(
        "neutral-fd",
        "as_raw_fd / into_raw_fd / from_raw_fd",
        "the carrier's descriptor leaf",
        Exact,
        None,
    ),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_under_approximating_rule_is_a_premise_or_a_refusal() {
        for r in RULES {
            if r.direction == Direction::Under {
                let p = r.premise_or_refusal.unwrap_or_else(|| panic!("{}: no premise", r.id));
                assert!(
                    p.starts_with("P-") || crate::refusal::CATALOG.iter().any(|c| c.code == p),
                    "{}: `{p}` is neither a premise nor a catalog code",
                    r.id
                );
            }
            if r.direction == Direction::Over {
                assert_eq!(r.premise_or_refusal, Some("PC-OVERAPPROX"), "{}", r.id);
            }
        }
    }

    #[test]
    fn rule_ids_are_unique() {
        let mut ids: Vec<_> = RULES.iter().map(|r| r.id).collect();
        ids.sort_unstable();
        let n = ids.len();
        ids.dedup();
        assert_eq!(ids.len(), n);
    }
}
