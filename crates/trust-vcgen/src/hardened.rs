// trust_vcgen/hardened.rs: hardened boundary obligations for compiler workflows
//
// These checks model the "safe Rust but still wrong" classes from the
// coreutils/Rust bug taxonomy: path re-resolution, byte/text boundary loss,
// discarded errors, panic-as-DoS, and trust-domain ordering. Compiler callers
// pass a dependency-tracked hardened/profile decision explicitly; this module
// never consults process-global environment state.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Formula, HardenedVcCategory, Operand, SourceSpan,
    Symbol, Terminator, VcKind, VerifiableFunction, VerificationCondition,
};

use crate::{guards, operand_to_formula};

#[derive(Debug, Clone, Copy)]
struct CallRule {
    needle: &'static str,
    category: HardenedVcCategory,
    detail: &'static str,
}

const CALL_RULES: &[CallRule] = &[
    CallRule {
        needle: "std::fs::remove_file",
        category: HardenedVcCategory::RawPathApi,
        detail: "path removal re-resolves a mutable direntry; use a verified dirfd/handle-relative wrapper",
    },
    CallRule {
        needle: "std::fs::remove_dir",
        category: HardenedVcCategory::RawPathApi,
        detail: "path directory removal re-resolves a mutable direntry; use a verified dirfd/handle-relative wrapper",
    },
    CallRule {
        needle: "std::fs::rename",
        category: HardenedVcCategory::RawPathApi,
        detail: "rename is name-based; hardened code needs source and destination direntry identity contracts",
    },
    CallRule {
        needle: "std::fs::canonicalize",
        category: HardenedVcCategory::PathIdentity,
        detail: "canonicalization is not a filesystem identity proof; compare stable file identity instead",
    },
    CallRule {
        needle: "std::fs::metadata",
        category: HardenedVcCategory::RawPathApi,
        detail: "metadata on a path is a path-resolution check; later path use needs a stable-handle proof",
    },
    CallRule {
        needle: "std::fs::set_permissions",
        category: HardenedVcCategory::PermissionChange,
        detail: "path-based permission changes need stable identity and creation-time mode proofs",
    },
    CallRule {
        needle: "std::fs::File::create",
        category: HardenedVcCategory::RawPathApi,
        detail: "File::create uses path resolution and default creation semantics; use create-at with explicit mode/identity contracts",
    },
    CallRule {
        needle: "std::fs::OpenOptions::open",
        category: HardenedVcCategory::RawPathApi,
        detail: "OpenOptions::open on a path needs explicit no-follow/create/mode and trust-domain contracts",
    },
    CallRule {
        needle: "std::fs::create_dir",
        category: HardenedVcCategory::PermissionCreate,
        detail: "directory creation by path needs creation-time permissions and parent dirfd contracts",
    },
    CallRule {
        needle: "std::fs::read_to_string",
        category: HardenedVcCategory::Utf8Reject,
        detail: "read_to_string rejects non-UTF-8 data; Unix boundary data must stay byte-exact unless UTF-8 is proven",
    },
    CallRule {
        needle: "from_utf8_lossy",
        category: HardenedVcCategory::ByteLoss,
        detail: "lossy UTF-8 conversion can corrupt byte-exact input/output",
    },
    CallRule {
        needle: "to_string_lossy",
        category: HardenedVcCategory::ByteLoss,
        detail: "lossy OS/path conversion can corrupt byte-exact filesystem data",
    },
    CallRule {
        needle: "String::from_utf8",
        category: HardenedVcCategory::Utf8Reject,
        detail: "strict UTF-8 conversion can reject valid Unix filenames or byte streams",
    },
    CallRule {
        needle: "str::from_utf8",
        category: HardenedVcCategory::Utf8Reject,
        detail: "strict UTF-8 conversion can reject valid Unix filenames or byte streams",
    },
    CallRule {
        needle: "core::result::Result::ok",
        category: HardenedVcCategory::ErrorDiscard,
        detail: "Result::ok discards the error channel; hardened code needs a proof-bearing allow or propagation",
    },
    CallRule {
        needle: "unwrap_or_default",
        category: HardenedVcCategory::ErrorDiscard,
        detail: "unwrap_or_default can erase an error into a successful default value",
    },
    CallRule {
        needle: "unwrap",
        category: HardenedVcCategory::PanicBoundary,
        detail: "unwrap is a denial-of-service path unless the success precondition is proven",
    },
    CallRule {
        needle: "expect",
        category: HardenedVcCategory::PanicBoundary,
        detail: "expect is a denial-of-service path unless the success precondition is proven",
    },
    CallRule {
        needle: "std::env::args",
        category: HardenedVcCategory::CompatObservable,
        detail: "CLI boundary uses Unicode String args; compatibility-sensitive tools should model OsString/byte arguments",
    },
    CallRule {
        needle: "stdout",
        category: HardenedVcCategory::ProcessSemantics,
        detail: "stdout pipe behavior depends on SIGPIPE/startup semantics; compatibility-sensitive tools need an explicit process-signal policy",
    },
    CallRule {
        needle: "_print",
        category: HardenedVcCategory::ProcessSemantics,
        detail: "stdout writes must model broken-pipe/SIGPIPE compatibility instead of assuming Rust default process semantics",
    },
    CallRule {
        needle: "Utf8Lossy::from_bytes",
        category: HardenedVcCategory::ByteLoss,
        detail: "internal lossy UTF-8 conversion can corrupt byte-exact input/output",
    },
    CallRule {
        needle: "chroot",
        category: HardenedVcCategory::TrustDomain,
        detail: "root changes must be ordered with name-service, dynamic loading, and privilege-drop effects",
    },
    CallRule {
        needle: "setuid",
        category: HardenedVcCategory::TrustDomain,
        detail: "privilege transition requires a modeled privilege-state contract",
    },
    CallRule {
        needle: "setgid",
        category: HardenedVcCategory::TrustDomain,
        detail: "privilege transition requires a modeled privilege-state contract",
    },
    CallRule {
        needle: "getpwnam",
        category: HardenedVcCategory::TrustDomain,
        detail: "libc name-service lookup may load configuration or modules from the active trust domain",
    },
    CallRule {
        needle: "getgrnam",
        category: HardenedVcCategory::TrustDomain,
        detail: "libc group-service lookup may load configuration or modules from the active trust domain",
    },
    CallRule {
        needle: "get_user_by_name",
        category: HardenedVcCategory::TrustDomain,
        detail: "user lookup wrappers may cross NSS or platform account-service trust domains",
    },
    CallRule {
        needle: "dlopen",
        category: HardenedVcCategory::TrustDomain,
        detail: "dynamic loading must be proven to occur in a trusted domain while privileged",
    },
];

#[derive(Debug, Clone)]
struct CallSite {
    ordinal: usize,
    callee: String,
    span: SourceSpan,
}

/// The registered profiles that carry hardened boundary obligations.
///
/// A closed registry, not a lexical rule: hardened obligations are fail-closed
/// proof requirements on `unwrap`, `expect`, path re-resolution and privilege
/// transitions, so which profiles demand them has to be a decision recorded
/// here, not a consequence of a name happening to mention a platform. Entries
/// are the canonical `_`-separated, lowercase spelling; `normalize_profile`
/// accepts `-` and case variants of the same name.
const HARDENED_PROFILES: &[&str] = &["coreutils_hardened", "hardened", "unix_hardened"];

/// Canonicalize a profile label for registry lookup. `-` and `_` are the same
/// separator to a human writing a profile name, and case is not meaningful,
/// so `coreutils-hardened` and `unix_hardened` reach the same entry. Nothing
/// else is normalized: a profile that merely contains a registered name is a
/// different profile.
fn normalize_profile(profile: &str) -> String {
    profile.trim().to_ascii_lowercase().replace('-', "_")
}

/// Whether `profile` is a registered hardened profile.
///
/// This is the SOLE carrier of the hardened decision. It used to be OR-ed with
/// a separate `-Ztrust-verify-hardened` boolean, which let the compiler's
/// default and Targo's default select different obligation sets for the same
/// source.
pub fn profile_enables_hardened(profile: Option<&str>) -> bool {
    profile.is_some_and(|profile| HARDENED_PROFILES.contains(&normalize_profile(profile).as_str()))
}

pub(crate) fn generate_hardened_vcs(
    func: &VerifiableFunction,
    enabled: bool,
) -> Vec<VerificationCondition> {
    if !enabled {
        return Vec::new();
    }
    generate_hardened_vcs_for_profile(func)
}

/// The function's preconditions that mention a capability predicate
/// (`Formula::Pred`). Their presence marks a cap wrapper (SAFE_API §4.2.7): a
/// dangerous boundary inside the function is safe GIVEN them, so the boundary
/// discharges against them instead of fail-closing on `Bool(true)`.
fn cap_predicate_preconditions(func: &VerifiableFunction) -> Vec<Formula> {
    func.preconditions.iter().filter(|p| formula_mentions_pred(p)).cloned().collect()
}

/// Bridge to the dominated-safe unwrap panic-freedom formula.
fn unwrap_pinned_panic_freedom_formula(
    func: &VerifiableFunction,
    ordinal: usize,
) -> Option<Formula> {
    crate::generate::unwrap_panic_freedom_formula_at_block(func, ordinal)
}

/// True if `Formula::Pred` appears anywhere in `f`.
fn formula_mentions_pred(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |sub| {
        if matches!(sub, Formula::Pred(..)) {
            found = true;
        }
    });
    found
}

pub(crate) fn generate_hardened_vcs_for_profile(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let calls = collect_calls(func);
    let mut vcs = Vec::new();

    // Trust SAFE_API §4.2.7: a hardened boundary inside a CAP WRAPPER — a
    // function carrying capability-predicate (`Formula::Pred`) preconditions — is
    // discharged against those preconditions instead of fail-closing on
    // `Bool(true)`. The boundary VC becomes `Not(And[cap preds])` conjoined with
    // the call-site-live preconditions, so inside the wrapper `pre ∧ ¬pre` is
    // UNSAT (proved — the wrapper may assume its own contract); the real
    // obligation is pushed to callers' precondition VCs. A precondition whose
    // variable was reassigned before the call is dropped by
    // `conjoin_live_preconditions` (same kill as the assert path), so the
    // boundary fails CLOSED rather than discharging against a stale fact.
    let cap_preconds = cap_predicate_preconditions(func);
    let may_reassigned =
        (!cap_preconds.is_empty()).then(|| crate::generate::v2_may_reassigned_per_block(func));
    let empty_kill: FxHashSet<String> = FxHashSet::default();

    for call in &calls {
        for rule in CALL_RULES {
            if call_matches(&call.callee, rule.needle) {
                // Trust (Part B): SUPPRESS the hardened `Result::unwrap` panic twin
                // when the unwrap is PROVABLY infallible — the success-by-construction
                // of a slice->array `try_into`/`try_from` whose slice length provably
                // equals the array length. This reuses the SAME infallibility predicate
                // the per-statement `Call::unwrap::panic-freedom` suppression uses, so
                // the two lanes agree. A genuinely-fallible unwrap (unknown length,
                // user Index impl, non-`try_into` Result) does NOT match and the twin
                // is still emitted (fail-closed). Only the `unwrap` rule
                // (`PanicBoundary`) is gated; every other CALL_RULE is unaffected.
                if rule.needle == "unwrap"
                    && crate::generate::unwrap_call_at_block_is_infallible(func, call.ordinal)
                {
                    continue;
                }
                // Trust (unwrap panic-freedom, dominated-safe): a PanicBoundary
                // twin for an `unwrap`/`expect` whose receiver discriminant is
                // PINNED (the same recognizer + assembled formula the primary
                // `Call::…::panic-freedom` lane solves) carries that refutation
                // formula instead of the fail-closed `Bool(true)` — so both rows
                // keyed to the same call are decided by the SAME obligation
                // (UNSAT ⇒ both prove; SAT ⇒ both stay failed). Every other
                // PanicBoundary (unpinned receiver, cap wrapper, non-Call source)
                // is UNCHANGED and stays fail-closed.
                if rule.category == HardenedVcCategory::PanicBoundary
                    && cap_preconds.is_empty()
                    && let Some(formula) = unwrap_pinned_panic_freedom_formula(func, call.ordinal)
                {
                    vcs.push(hardened_vc_with_formula(
                        func,
                        &call.span,
                        rule.category,
                        call.callee.clone(),
                        rule.detail,
                        formula,
                    ));
                    continue;
                }
                if cap_preconds.is_empty() {
                    // No capability contract: fail closed (unprovable mandate).
                    vcs.push(hardened_vc(
                        func,
                        &call.span,
                        rule.category,
                        &call.callee,
                        rule.detail,
                    ));
                } else {
                    let killed = may_reassigned
                        .as_ref()
                        .and_then(|m| m.get(&BlockId(call.ordinal)))
                        .unwrap_or(&empty_kill);
                    let violation = Formula::Not(Box::new(Formula::And(cap_preconds.clone())));
                    let formula = crate::generate::conjoin_preconditions_versioned(
                        func,
                        BlockId(call.ordinal),
                        &func.preconditions,
                        killed,
                        violation,
                    );
                    vcs.push(hardened_vc_with_formula(
                        func,
                        &call.span,
                        rule.category,
                        call.callee.clone(),
                        rule.detail,
                        formula,
                    ));
                }
            }
        }
    }

    append_assert_panic_vcs(func, &mut vcs);
    append_permission_window_vcs(func, &calls, &mut vcs);
    append_trust_boundary_order_vcs(func, &calls, &mut vcs);
    append_unclassified_opaque_vcs(func, &mut vcs);

    vcs
}

fn collect_calls(func: &VerifiableFunction) -> Vec<CallSite> {
    let mut calls = Vec::new();
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Call { func: callee, span, .. } => {
                calls.push(CallSite {
                    ordinal: block.id.0,
                    callee: callee.clone(),
                    span: span.clone(),
                });
            }
            Terminator::Opaque { kind, span, .. } => {
                if let Some(callee) = opaque_hardened_call_from_kind(kind) {
                    calls.push(CallSite { ordinal: block.id.0, callee, span: span.clone() });
                }
            }
            _ => {}
        }
    }
    calls.sort_by_key(|call| call.ordinal);
    calls
}

fn opaque_hardened_call_from_kind(kind: &str) -> Option<String> {
    kind.strip_prefix("Call::").filter(|callee| !callee.is_empty()).map(ToString::to_string)
}

fn append_unclassified_opaque_vcs(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
    for block in &func.body.blocks {
        let Terminator::Opaque { kind, span, .. } = &block.terminator else {
            continue;
        };
        if opaque_hardened_call_from_kind(kind).is_some() {
            continue;
        }
        // The former fallback reopened `span.file` through cwd/
        // CARGO_MANIFEST_DIR and let untracked, potentially wrong filesystem
        // bytes decide whether a hardened VC existed. An opaque terminator that
        // carries no structured call identity is now an explicit fail-closed
        // hardened boundary until extraction supplies that identity.
        vcs.push(hardened_vc(
            func,
            span,
            HardenedVcCategory::Unknown(Symbol::intern("opaque-terminator")),
            kind,
            "opaque terminator lacks dependency-tracked structured boundary identity",
        ));
    }
}

fn call_matches(callee: &str, needle: &str) -> bool {
    if needle.contains("::") {
        let callee_segments = path_segments(callee);
        let needle_segments = path_segments(needle);
        if needle_segments.is_empty() {
            return false;
        }

        return if is_absolute_rule_path(&needle_segments) {
            callee_segments.as_slice() == needle_segments.as_slice()
        } else {
            callee_segments.ends_with(&needle_segments)
        };
    }

    callee
        .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
        .any(|segment| segment == needle)
}

fn path_segments(path: &str) -> Vec<&str> {
    let bytes = path.as_bytes();
    let mut segments = Vec::new();
    let mut start = 0;
    let mut angle_depth = 0usize;
    let mut index = 0;

    while index < bytes.len() {
        match bytes[index] {
            b'<' => {
                angle_depth += 1;
                index += 1;
            }
            b'>' => {
                angle_depth = angle_depth.saturating_sub(1);
                index += 1;
            }
            b':' if angle_depth == 0 && index + 1 < bytes.len() && bytes[index + 1] == b':' => {
                push_path_segment(&mut segments, &path[start..index]);
                index += 2;
                start = index;
            }
            _ => {
                index += 1;
            }
        }
    }

    push_path_segment(&mut segments, &path[start..]);
    segments
}

fn push_path_segment<'a>(segments: &mut Vec<&'a str>, segment: &'a str) {
    let segment = segment.trim();
    if segment.is_empty() || segment.starts_with('<') {
        return;
    }

    let segment = segment.split(['<', '(']).next().unwrap_or(segment).trim();
    if !segment.is_empty() {
        segments.push(segment);
    }
}

fn is_absolute_rule_path(segments: &[&str]) -> bool {
    matches!(segments.first().copied(), Some("alloc" | "core" | "libc" | "std"))
}

fn append_permission_window_vcs(
    func: &VerifiableFunction,
    calls: &[CallSite],
    vcs: &mut Vec<VerificationCondition>,
) {
    let create = calls.iter().find(|call| is_permission_window_create_call(&call.callee));
    let Some(create) = create else {
        return;
    };

    let ordered_change = calls.iter().find(|call| {
        call.ordinal > create.ordinal && is_permission_window_repair_call(&call.callee)
    });
    let fallback_change = calls.iter().find(|call| is_permission_window_repair_call(&call.callee));

    if let Some(change) = ordered_change.or(fallback_change) {
        vcs.push(hardened_vc(
            func,
            &change.span,
            HardenedVcCategory::PermissionWindow,
            &change.callee,
            "object creation is followed by permission/owner repair; create with final mode/owner under the OS model",
        ));
    }
}

fn is_permission_window_create_call(callee: &str) -> bool {
    call_matches(callee, "File::create")
        || call_matches(callee, "create_dir")
        || call_matches(callee, "OpenOptions::open")
}

fn is_permission_window_repair_call(callee: &str) -> bool {
    call_matches(callee, "set_permissions")
        || call_matches(callee, "set_owner")
        || call_matches(callee, "chown")
}

fn append_trust_boundary_order_vcs(
    func: &VerifiableFunction,
    calls: &[CallSite],
    vcs: &mut Vec<VerificationCondition>,
) {
    let transition = calls.iter().find(|call| is_trust_domain_transition(&call.callee));
    let Some(transition) = transition else {
        return;
    };

    if let Some(late_lookup) = calls
        .iter()
        .find(|call| call.ordinal > transition.ordinal && is_trust_domain_late_effect(&call.callee))
    {
        vcs.push(hardened_vc(
            func,
            &late_lookup.span,
            HardenedVcCategory::TrustDomainOrder,
            &late_lookup.callee,
            "name-service or dynamic-loading effect occurs after a root/group/user trust-domain transition; resolve trusted inputs before crossing the boundary",
        ));
    }
}

fn is_trust_domain_transition(callee: &str) -> bool {
    call_matches(callee, "chroot")
        || call_matches(callee, "setuid")
        || call_matches(callee, "setgid")
}

fn is_trust_domain_late_effect(callee: &str) -> bool {
    call_matches(callee, "getpwnam")
        || call_matches(callee, "getgrnam")
        || call_matches(callee, "get_user_by_name")
        || call_matches(callee, "dlopen")
}

fn append_assert_panic_vcs(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
    // Trust: drop a precondition at any assert whose block may have reassigned one
    // of the precondition's free variables on the way in — an entry contract
    // `lo <= hi` is stale after `hi = big` and would vacuously discharge a real
    // `hi - lo` panic boundary (a false-PROVE). Same kill as the v2 VC sites.
    let may_reassigned = crate::generate::v2_may_reassigned_per_block(func);
    let empty_kill: FxHashSet<String> = FxHashSet::default();

    // Cross-block reaching definitions, including assert-passed CheckedBinaryOp
    // semantics threaded only along no-overflow SUCCESS edges. This connects a
    // downstream assert's free `_N.0` (a CheckedBinaryOp result computed in a
    // PRECEDING block) to its exact `lhs OP rhs` value — e.g. `signed_max`'s
    // `1i128 << (width-1)` shift, where the shift amount `_6 == _7.0` and `_7`
    // is the `width - 1` CheckedSub asserted non-overflowing in the prior block.
    // Without it, `_7.0` is a free var the `width <= 127` path guard cannot
    // bound, and the hardened Shl boundary false-FAILs (`_6 = 200`). Sound: the
    // result def `_N.0 == lhs OP rhs` holds EXACTLY on the no-overflow path the
    // map threads it to. Assert cleanup receives the base outflow without that
    // success fact, and the abstract panic exit is not an in-CFG successor, so
    // conjoining a genuinely-true fact is monotone — it can only turn a
    // false-FAIL into a PROVE for safe code, never make a real panic PROVE.
    let reaching_defs = cross_block_reaching_defs(func);

    // Slice-chunking yield facts (`for c in s.chunks_exact(N) { c[k] }` => the
    // yielded sub-slice's modeled length is `== N`) — the SAME map the L0 lane
    // conjoins (generate::build_slice_iter_yield_guard_map). The hardened
    // BoundsCheck twin otherwise carries that length UNCONSTRAINED and spuriously
    // refutes `c[k]` (k < N). The map keys the fact ONLY to blocks whose genuine
    // Some-payload traces to a `*_exact`/`windows`/`chunks` constructor, so
    // `remainder()` and reassigned bindings get NO fact (fail-closed). Sound: a
    // true `len == N` theorem, conjoined monotonically exactly as in the L0 lane.
    let slice_iter_yield_guards = crate::generate::build_slice_iter_yield_guard_map(func);

    // Function-wide invariant facts (accumulator/cast/min-max/modulo bounds, …):
    // each is UNCONDITIONALLY true (every builder SSA-gates its result), so
    // conjoining the whole set onto ANY VC of `func` is sound. The per-statement
    // arithmetic-safety lane already conjoins these onto every block VC
    // (`generate.rs`: `build_global_invariant_facts` + the block-VC loop); the
    // hardened panic-boundary lane did NOT, so a CHAINED widening add
    // (`(a as u16) + (b as u16) + (c as u16)`, or a3d-kernel
    // `face_active_edge_count`'s bool-sum) over-refutes: the second add's operand
    // `_t.0` (the FIRST add's result) reaches the boundary as a free var carrying
    // only its generic type range (`_t.0 <= 65535`) rather than the accumulator
    // bound `_t.0 <= 510` that `build_accumulator_bound_facts` proves — so the
    // solver fabricates `_t.0 + c > 65535`. Conjoining the SAME global facts the
    // per-statement lane uses closes this: the two lanes now carry identical
    // accumulator/cast hypotheses, so a provably-safe chain PROVES in BOTH while a
    // genuine overflow (unbounded operands, no accumulator fact) still refutes.
    let global_facts = crate::generate::build_global_invariant_facts(func);

    // BoundsCheck asserts whose index is PROVABLY in range via a loop-yield bound
    // (`for i in 0..s.len()` range yield / `for (i, _) in s.iter().enumerate()`
    // index yield). The per-statement bounds VC PROVES these via the SAME yield
    // fact — a fact the per-statement lane conjoins but the hardened twin below does
    // NOT — so the twin over-refutes a provably-safe guarded index unless we skip it
    // here (mirroring the Div/Rem nonzero-constant skip). Built ONCE per function;
    // empty for non-looping code. See `v2_boundscheck_index_in_range_skip_set` for
    // the soundness argument (only a `Lt(index, checked_len)` yield fact keyed to the
    // assert's own index/length qualifies; an unguarded index stays refutable).
    let bounds_yield_skip = crate::generate::v2_boundscheck_index_in_range_skip_set(func);

    for block in &func.body.blocks {
        // `unwind: _`: hardened panic-boundary VC uses only the assert's own fields;
        // the cleanup successor is an unguarded CFG edge handled elsewhere.
        let Terminator::Assert { cond, expected, msg, span, target, unwind: _ } =
            &block.terminator
        else {
            continue;
        };

        // Trust #soundness: a DivisionByZero/RemainderByZero assert whose divisor is
        // a nonzero CONSTANT (e.g. `len % 3`, `len / 4`, `len / 2`) can NEVER panic
        // at runtime, so there is no panic boundary to harden. The per-statement
        // Div/Rem safety VC is already suppressed for this case
        // (generate::v2_divisor_is_nonzero_constant; see generate.rs Div/Rem arms),
        // which leaves the hardened twin with NO proved sibling to subsume it — it
        // then surfaces spuriously as a DESIGN-REQUIREMENT. Skip emitting the twin
        // when the divisor is a nonzero constant, mirroring the per-statement skip.
        // Sound: dropping an obligation for an operation that is provably panic-free
        // can never mask a real panic; a SYMBOLIC or zero divisor does NOT match
        // (fail-closed) and still gets its twin (and a real div-by-zero stays
        // refutable).
        if matches!(msg, AssertMessage::DivisionByZero | AssertMessage::RemainderByZero)
            && crate::generate::v2_block_divrem_divisor_is_nonzero_constant(func, block)
        {
            continue;
        }

        // Trust #soundness: a BoundsCheck assert whose index is PROVABLY in range —
        // a `for i in 0..s.len()` range-yield bound or a `for (i, _) in
        // s.iter().enumerate()` index yield establishing `index < len` for the SAME
        // length the assert checks — can NEVER panic at runtime, so there is no panic
        // boundary to harden. The per-statement bounds VC already PROVES this via
        // build_range_yield_guard_map / build_enumerate_yield_guard_map (yield facts
        // the per-statement lane conjoins onto the bounds VC but this hardened twin
        // does NOT), so the twin otherwise OVER-REFUTES a provably-safe guarded index
        // (per-statement PROVED, hardened twin FAILED). Skip emitting the twin when
        // the index is provably in range, mirroring the Div/Rem skip above. Sound:
        // dropping an obligation for an access that is provably in-bounds can never
        // mask a real OOB panic; an UNGUARDED index, a constant/derived/projected
        // index, or a loop over a DIFFERENT bound (`0..K`, `K != len`) is NOT in the
        // skip set (fail-closed) and still gets its twin (a real OOB stays refutable).
        if matches!(msg, AssertMessage::BoundsCheck) && bounds_yield_skip.contains(&block.id) {
            continue;
        }

        // Trust #soundness: a BoundsCheck assert on a LITERAL in-range index
        // (`cols[0]` on `[Vec4; 4]` — both sides compile-time constants with
        // `index < len`) can NEVER panic, so there is no panic boundary to
        // harden. The per-statement bounds VC is suppressed for exactly this
        // case (see `v2_bounds_assert_const_index_in_range` for why emitting a
        // constant-false violation loses proof authority at the vacuity gate);
        // skip the twin identically, mirroring the Div/Rem and loop-yield
        // skips above. A symbolic, call-written, or genuinely out-of-range
        // constant index is NOT in the shape (fail-closed) and keeps its twin.
        if matches!(msg, AssertMessage::BoundsCheck)
            && crate::generate::v2_bounds_assert_const_index_in_range(func, block, cond, *expected)
        {
            continue;
        }

        // Trust: signed >= 128-bit arithmetic-overflow asserts (`Overflow(Add|Sub)`
        // and `OverflowNeg`) route to a SELF-CONTAINED BV violation instead of the
        // Int-path `extract_assert_passed_semantics` encoding below. The Int path's
        // no-overflow predicate carries this type's `±2^127` range bounds, which the
        // native typed-CHC lane rejects (`parse_i64`) → UNSUPPORTED → UNKNOWN — exactly
        // why `signed_max`'s `_5 - 1` / `signed_min`'s `-_5` stayed UNKNOWN here. The
        // BV core is the `w+1`-bit sign-extension add/sub check (or `x == INT_MIN` for
        // neg) plus the BV-rendered block-defs / dominating guard bounds on the
        // operands, so a value safe ONLY because of a defining shift PROVES. It uses
        // FRESH `__trust_ovf_bv_*` BV vars disjoint from the Int-sorted vars the rest of
        // this loop threads (preconditions / path guards / arg-ranges / cross-block
        // defs), so we MUST NOT conjoin those Int-sorted facts onto the BV core — they
        // share no variable and would double-declare a symbol at two sorts. The BV
        // block-defs are the sole, sound channel for the constraining facts; an
        // unguarded operand carries none, so a real overflow stays SAT/refutable.
        // Widths <= 64 stay on the Int path (the native i64-LIA decides them losslessly
        // AND the Int path keeps the conjoined guards/defs the BV core would drop).
        if let Some(bv_formula) = hardened_signed_bv_overflow_formula(func, block, msg, *target) {
            vcs.push(hardened_vc_with_formula(
                func,
                span,
                HardenedVcCategory::PanicBoundary,
                format!("mir_assert::{msg:?}"),
                assert_panic_detail(msg),
                bv_formula,
            ));
            continue;
        }

        // For a CheckedBinaryOp arithmetic-overflow assert, `cond` is the opaque
        // overflow FLAG (`_N.1`), which `extract_block_definitions` leaves UNBOUND
        // (it skips CheckedBinaryOp). The boundary VC would then degenerate to
        // "free flag is true" — trivially SAT — and refute EVERY arithmetic
        // boundary, even a provably-safe `a as u16 + b as u16`. Use the
        // operand-based no-overflow condition instead (the same precise encoding
        // the per-statement arithmetic-safety VC proves with): `extract_assert_
        // passed_semantics` returns `[in_range, result_def, lhs_range, rhs_range,
        // ..]` (operand ranges source-width-tightened), so the violation is
        // `NOT in_range` under those hypotheses — a safe op discharges, while a
        // genuinely-overflowing one (`u32 + u32`) still fails (its operands are not
        // cast-narrowed, so `in_range` is violable).
        let checked_facts = guards::extract_assert_passed_semantics(func, block);
        // Trust #soundness: a SHIFT-overflow assert (`Overflow(Shl)`/`Overflow(Shr)`)
        // takes the dedicated, lowerable shift VIOLATION (`amount >= width`) as its
        // base, NOT the generic operand-range encoding from
        // `extract_assert_passed_semantics`. That generic encoding is built for
        // arithmetic CheckedBinaryOp asserts; for a shift the native typed-CHC lane
        // cannot lower it, so the hardened twin carried no publishable proof evidence
        // (a3d-kernel `octree_node_count`'s `1u64 << exp` — the lone 84/85 hardened
        // gate miss). The violation is the SAME formula the per-statement
        // `ShiftOverflow` VC proves; the block-def / reaching-def / dominating-guard /
        // precondition conjoining below then supplies the `amount < width` guard, so a
        // guarded shift PROVES and an unguarded one still REFUTES. Falls back to the
        // generic path if the shift operands can't be recovered.
        let shift_violation = match msg {
            AssertMessage::Overflow(op @ (BinOp::Shl | BinOp::Shr)) => {
                crate::generate::v2_assert_shift_violation_formula(func, block, *target, *op)
            }
            _ => None,
        };
        let mut formula = match shift_violation {
            Some(violation) => violation,
            None => match checked_facts.split_first() {
                Some((in_range, hyps)) => {
                    let mut conj = Vec::with_capacity(hyps.len() + 1);
                    conj.push(Formula::Not(Box::new(in_range.clone())));
                    // `extract_assert_passed_semantics` also carries the
                    // success-only `_N.0 ==` unbounded-result equation. MIR's
                    // value field wraps on overflow, so that Eq is false on the
                    // failure path modeled here. Keep only unconditional
                    // operand/source range facts; the exact overflow-flag
                    // biconditional is conjoined separately below.
                    conj.extend(
                        hyps.iter().filter(|fact| !matches!(fact, Formula::Eq(..))).cloned(),
                    );
                    Formula::And(conj)
                }
                None => assert_failure_formula(func, cond, *expected),
            },
        };
        formula = formula_with_block_definitions(func, block, formula);

        // Conjoin the slice-chunking yield fact `chunk__slice_len == N` for this
        // block (surfaced just above as `_meta == chunk__slice_len` via
        // PtrMetadata), so the hardened BoundsCheck twin `k < chunk__slice_len`
        // proves for `k < N`. Byte-identical to the L0 conjunction; the map is
        // empty for every non-chunking block, so this is a no-op elsewhere.
        if let Some(facts) = slice_iter_yield_guards.get(&block.id)
            && !facts.is_empty()
        {
            let mut conj = facts.clone();
            conj.push(formula);
            formula = Formula::And(conj);
        }

        // Define the checked-op overflow flag in terms of its operands. The
        // assert-failure condition is the raw flag `_N.1`; left free, every
        // arithmetic panic boundary fails spuriously. The biconditional
        // `_N.1 <=> result out-of-range` is exact (not an in-range assumption),
        // so a dominating guard discharges the failure while an unguarded
        // overflow stays reachable.
        let flag_defs = guards::extract_overflow_flag_semantics(func, block);
        if !flag_defs.is_empty() {
            let mut clauses = flag_defs;
            clauses.push(formula);
            formula = Formula::And(clauses);
        }

        // NOTE (merge co-evo): co-evo applied the path-map guards here with an
        // UNFILTERED `guarded_formula(func, &entry.guards, formula)`. That is
        // superseded by main's stale-guard-killing application further below
        // (the `formula_survives_redefs`/`killed` filter), which is the SOUND
        // version — an unfiltered dominating guard that this block reassigned
        // would vacuously discharge a real panic boundary (a false-PROVE).
        // Keep only main's filtered application; do NOT re-add the unfiltered one.
        let killed = may_reassigned.get(&block.id).unwrap_or(&empty_kill);
        // Conjoin cross-block reaching definitions (assert-passed result defs +
        // ranges threaded along success edges) BEFORE the path guards, so a
        // downstream guard (`width <= 127`) connects through the threaded
        // `_N.0 == lhs OP rhs` to the asserted shift amount.
        //
        // Trust #soundness: filter these by `killed` like the path guards and
        // preconditions. A reaching def `c == (hi <= K)` relates `c` to the SMT
        // var `hi`, but `c` was defined with the OLD `hi`; after `hi = big` the
        // def is STALE and — combined with a surviving bool path guard `c == 1` —
        // reconstructs the stale `hi <= K`, false-PROVING a boundary that needs
        // `hi > K`. Dropping a stale def is monotone-sound.
        if let Some(defs) = reaching_defs.get(&block.id) {
            let live: Vec<Formula> = defs
                .iter()
                .filter(|d| crate::generate::formula_survives_redefs(d, killed))
                .cloned()
                .collect();
            if !live.is_empty() {
                let mut conj = live;
                conj.push(formula);
                formula = Formula::And(conj);
            }
        }

        // Conjoin the function-wide invariant facts (accumulator/cast/min-max/
        // modulo bounds) exactly as the per-statement arithmetic-safety lane does
        // (`generate.rs` block-VC loop). This is what supplies a CHAINED widening
        // add's accumulator bound `_t.0 <= 510` — the FIRST add's result, which the
        // second add's boundary otherwise sees only as a free `_t.0 <= 65535`
        // (type max), fabricating a spurious `_t.0 + c > 65535`. Conjoined BEFORE
        // the versioning below so the facts are alpha-renamed in lockstep with the
        // body, the SAME ordering the per-statement lane uses. Unfiltered like that
        // lane: each fact is an unconditional SSA-gated truth (monotone — only
        // discharges a false-FAIL, never a real overflow), and the rename makes any
        // fact over a reassigned name disjoint from the live read.
        if !global_facts.is_empty() {
            let mut conj = global_facts.clone();
            conj.push(formula);
            formula = Formula::And(conj);
        }

        // Version the body to its per-block versioned form (preconditions meet it
        // through the version-aware boundary). This MUST run before the path guards
        // below, mirroring the per-statement arithmetic-safety lane's ordering
        // (`generate_v2_safety_vcs`: body rename, THEN `v2_formula_with_path_guards`).
        formula = crate::generate::conjoin_preconditions_versioned(
            func,
            block.id,
            &func.preconditions,
            killed,
            formula,
        );
        // Conjoin the FULL dominating path-condition for this assert's block,
        // gathered by the SAME machinery the per-statement arithmetic/bounds-safety
        // VC uses (`v2_build_path_guard_map` + `v2_formula_with_path_guards`), so the
        // two lanes carry IDENTICAL hypotheses. This captures every branch condition
        // that must hold to reach the block — including NESTED inner guards
        // (`len >= 8` inside `if len <= 16 { if len >= 8 { … bytes[len-8..] … } }`) —
        // in ASSERTED form, source-versioned exactly as the renamed body. The old
        // `path_map()` accumulation (first-predecessor-wins, no source-versioning)
        // surfaced only the OUTER `len <= 16` guard and dropped the inner `len >= 8`,
        // leaving `len - 8` unprovable. The replacement also subsumes the stale-guard
        // kill the prior block applied: guards accumulate strictly along CFG edges and
        // are conjoined EXEMPT from the rename, so a guard over a reassigned body name
        // is name-disjoint from the live versioned read (the kill's drop, by
        // name-disjointness — the same S2c discipline the per-statement lane relies
        // on). SOUNDNESS: a block receives ONLY conditions that dominate it (the
        // sibling `else`/`len < 8` arm's assert never gets `len >= 8`), and an
        // unguarded operand carries no bound, so a real overflow/underflow stays
        // SAT/refutable.
        formula = conjoin_dominating_path_guards(func, block.id, formula);
        // Trust: bound every integer parameter to its type range, exactly as the
        // per-statement arithmetic-safety overflow VC does. Without this the
        // hardened MIR-assert boundary OVER-REFUTES a provably-safe widened add
        // (e.g. `a as u16 + b as u16` with u8 params): the solver, seeing the
        // parameters unconstrained, fabricates a spurious overflow. Sound: a
        // parameter unconditionally holds a value within its type range, so this
        // refutes only spurious counterexamples, never a real panic path.
        formula = crate::generate::conjoin_arg_type_ranges(func, formula);

        vcs.push(hardened_vc_with_formula(
            func,
            span,
            HardenedVcCategory::PanicBoundary,
            format!("mir_assert::{msg:?}"),
            assert_panic_detail(msg),
            formula,
        ));
    }
}

fn assert_failure_formula(func: &VerifiableFunction, cond: &Operand, expected: bool) -> Formula {
    let cond = operand_to_formula(func, cond);
    if expected { Formula::Not(Box::new(cond)) } else { cond }
}

/// Per-block cross-block reaching definitions for hardened panic-boundary VCs.
///
/// Reuses the v2 path-definition fixpoint, which propagates each block's
/// `extract_assert_passed_semantics` (the no-overflow `_N.0 == lhs OP rhs`
/// result def plus operand ranges) ONLY in normal-success outflow. An Assert
/// cleanup edge receives the base outflow without those facts; the abstract
/// panic exit is not an in-CFG successor. Thus the result def never reaches a
/// block where the operation actually wrapped. Returns the
/// facts that hold on EVERY path reaching each block (the join intersection),
/// which is the sound direction: a fact retained here was true along every
/// incoming path, so assuming it as a VC hypothesis cannot mask a real panic.
///
fn cross_block_reaching_defs(
    func: &VerifiableFunction,
) -> trust_types::fx::FxHashMap<BlockId, Vec<Formula>> {
    crate::generate::v2_build_path_definition_map_for_hardened(func)
}

/// Conjoin the full dominating path-condition for `block` onto a hardened
/// panic-boundary `formula`, using the SAME guard-gathering the per-statement
/// arithmetic/bounds-safety VC uses. This captures every branch condition that
/// must hold to reach the assert's block — including NESTED inner guards
/// (`len >= 8` inside `if len <= 16 { if len >= 8 { … } }`) — in ASSERTED form,
/// so the two lanes carry identical hypotheses. See
/// [`crate::generate::v2_conjoin_path_guards_for_hardened`] for the soundness
/// argument (guards accumulate strictly along CFG edges, so a block receives only
/// the conditions that dominate it; an unguarded operand stays refutable).
///
/// MUST be called AFTER the body is versioned (the lane's
/// `conjoin_preconditions_versioned`), matching the per-statement ordering.
fn conjoin_dominating_path_guards(
    func: &VerifiableFunction,
    block: BlockId,
    formula: Formula,
) -> Formula {
    crate::generate::v2_conjoin_path_guards_for_hardened(func, block, formula)
}

/// The self-contained BV overflow-violation formula for a signed >= 128-bit
/// arithmetic-overflow ASSERT (the hardened panic_boundary lane), or `None` when
/// the assert is not signed >= 128-bit add/sub/neg (the caller then keeps the Int
/// path). Delegates to the shared v2 BV builder so the hardened obligation is
/// byte-identical to the per-statement arithmetic-safety BV VC for the same op.
fn hardened_signed_bv_overflow_formula(
    func: &VerifiableFunction,
    block: &BasicBlock,
    msg: &AssertMessage,
    target: BlockId,
) -> Option<Formula> {
    crate::generate::v2_hardened_signed_bv_overflow_formula(func, block, msg, target)
}

fn formula_with_block_definitions(
    func: &VerifiableFunction,
    block: &BasicBlock,
    formula: Formula,
) -> Formula {
    let mut clauses = guards::extract_block_definitions(func, block);
    if clauses.is_empty() {
        return formula;
    }
    clauses.push(formula);
    Formula::And(clauses)
}

fn assert_panic_detail(msg: &AssertMessage) -> String {
    match msg {
        AssertMessage::BoundsCheck => {
            "MIR bounds-check assert can panic; hardened code needs a proven index precondition"
                .to_string()
        }
        AssertMessage::Overflow(_) | AssertMessage::OverflowNeg => {
            "MIR arithmetic assert can panic; hardened code needs proven arithmetic preconditions"
                .to_string()
        }
        AssertMessage::DivisionByZero | AssertMessage::RemainderByZero => {
            "MIR zero-divisor assert can panic; hardened code needs a proven nonzero precondition"
                .to_string()
        }
        AssertMessage::Custom(message) => {
            format!(
                "MIR assert can panic at runtime; hardened code needs this precondition proved: {message}"
            )
        }
        _ => "MIR runtime assert can panic; hardened code needs a proved precondition".to_string(),
    }
}

fn hardened_vc(
    func: &VerifiableFunction,
    span: &SourceSpan,
    category: HardenedVcCategory,
    callee: &str,
    detail: &str,
) -> VerificationCondition {
    hardened_vc_with_formula(func, span, category, callee, detail, Formula::Bool(true))
}

fn hardened_vc_with_formula(
    func: &VerifiableFunction,
    span: &SourceSpan,
    category: HardenedVcCategory,
    callee: impl Into<String>,
    detail: impl Into<String>,
    formula: Formula,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::HardenedBoundary { category, callee: callee.into(), detail: detail.into() },
        function: func.name.clone().into(),
        location: span.clone(),
        // Hardened VCs encode violation conditions. Opaque OS/process/model
        // obligations stay fail-closed as `true`; MIR asserts carry the exact
        // assert-failure condition so solvers can prove the panic path absent.
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody,
    };

    use super::*;

    fn call_block(id: usize, callee: &str) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: callee.to_string(),
                args: vec![Operand::Constant(ConstValue::Unit)],
                dest: Place::local(0),
                target: Some(BlockId(id + 1)),
                span: SourceSpan {
                    file: "src/lib.rs".into(),
                    line_start: id as u32 + 1,
                    ..Default::default()
                },
                atomic: None,
            },
        }
    }

    fn opaque_call_block(id: usize, kind: &str, file: &str, line: u32) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            stmts: vec![],
            terminator: Terminator::Opaque {
                kind: kind.to_string(),
                targets: vec![BlockId(id + 1)],
                span: SourceSpan {
                    file: file.to_string(),
                    line_start: line,
                    line_end: line,
                    ..Default::default()
                },
            },
        }
    }

    fn return_block(id: usize) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts: vec![], terminator: Terminator::Return }
    }

    fn assert_block(id: usize, cond: Operand, expected: bool, msg: AssertMessage) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            stmts: vec![],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond,
                expected,
                msg,
                target: BlockId(id + 1),
                span: SourceSpan {
                    file: "src/lib.rs".into(),
                    line_start: id as u32 + 1,
                    ..Default::default()
                },
            },
        }
    }

    fn test_function(blocks: Vec<BasicBlock>) -> VerifiableFunction {
        VerifiableFunction {
            name: "hardened_fixture".to_string(),
            def_path: "crate::hardened_fixture".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks,
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn has_category(vcs: &[VerificationCondition], expected: HardenedVcCategory) -> bool {
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::HardenedBoundary { category, .. } if *category == expected
            )
        })
    }

    fn has_category_for_callee(
        vcs: &[VerificationCondition],
        expected: HardenedVcCategory,
        expected_callee: &str,
    ) -> bool {
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::HardenedBoundary { category, callee, .. }
                    if *category == expected && callee == expected_callee
            )
        })
    }

    fn hardened_vc_for_category(
        vcs: &[VerificationCondition],
        expected: HardenedVcCategory,
    ) -> &VerificationCondition {
        vcs.iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::HardenedBoundary { category, .. } if *category == expected
                )
            })
            .expect("expected hardened VC category")
    }

    #[test]
    fn hardened_profile_flags_raw_path_and_byte_loss_calls() {
        let func = test_function(vec![
            call_block(0, "std::fs::remove_file"),
            call_block(1, "alloc::string::String::from_utf8_lossy"),
            return_block(2),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::RawPathApi));
        assert!(has_category(&vcs, HardenedVcCategory::ByteLoss));
        assert!(vcs.iter().all(|vc| vc.formula == Formula::Bool(true)));
    }

    #[test]
    fn hardened_profile_recovers_opaque_call_callee_from_native_kind() {
        let func = test_function(vec![
            call_block(0, "std::fs::File::create"),
            opaque_call_block(1, "Call::std::fs::set_permissions", "src/lib.rs", 10),
            return_block(2),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::PermissionChange));
        assert!(has_category(&vcs, HardenedVcCategory::PermissionWindow));
    }

    #[test]
    fn hardened_profile_fails_closed_on_unclassified_opaque_terminators() {
        let func = test_function(vec![
            call_block(0, "std::fs::File::create"),
            opaque_call_block(1, "Call", "src/lib.rs", 4),
            return_block(2),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::HardenedBoundary {
                    category: HardenedVcCategory::Unknown(tag),
                    callee,
                    ..
                } if tag.as_str() == "opaque-terminator" && callee == "Call"
            ) && vc.formula == Formula::Bool(true)
        }));
    }

    #[test]
    fn hardened_profile_flags_remaining_hardened_categories() {
        let func = test_function(vec![
            call_block(0, "std::fs::canonicalize"),
            call_block(1, "std::fs::set_permissions"),
            call_block(2, "std::fs::create_dir"),
            call_block(3, "std::fs::read_to_string"),
            call_block(4, "std::env::args"),
            call_block(5, "std::io::stdio::stdout"),
            call_block(6, "libc::setuid"),
            call_block(7, "libc::getgrnam"),
            call_block(8, "users::get_user_by_name"),
            call_block(9, "core::result::Result::unwrap"),
            return_block(10),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::PathIdentity));
        assert!(has_category(&vcs, HardenedVcCategory::PermissionChange));
        assert!(has_category(&vcs, HardenedVcCategory::PermissionCreate));
        assert!(has_category(&vcs, HardenedVcCategory::Utf8Reject));
        assert!(has_category(&vcs, HardenedVcCategory::CompatObservable));
        assert!(has_category(&vcs, HardenedVcCategory::ProcessSemantics));
        assert!(has_category(&vcs, HardenedVcCategory::TrustDomain));
        assert!(has_category(&vcs, HardenedVcCategory::PanicBoundary));
    }

    #[test]
    fn hardened_profile_matches_native_hardened_fixture_callees() {
        let func = test_function(vec![
            call_block(0, "std::string::String::from_utf8_lossy"),
            call_block(1, "std::sys::os_str::bytes::Slice::to_string_lossy"),
            call_block(2, "core::str::lossy::Utf8Lossy::from_bytes"),
            call_block(3, "std::io::stdio::stdout"),
            call_block(4, "std::io::_print"),
            return_block(5),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::ByteLoss));
        assert!(has_category(&vcs, HardenedVcCategory::ProcessSemantics));
        assert!(has_category_for_callee(
            &vcs,
            HardenedVcCategory::ByteLoss,
            "core::str::lossy::Utf8Lossy::from_bytes"
        ));
        assert!(has_category_for_callee(
            &vcs,
            HardenedVcCategory::ProcessSemantics,
            "std::io::stdio::stdout"
        ));
        assert!(has_category_for_callee(
            &vcs,
            HardenedVcCategory::ProcessSemantics,
            "std::io::_print"
        ));
    }

    #[test]
    fn only_registered_profiles_enable_hardened_obligations() {
        for registered in ["hardened", "unix_hardened", "coreutils_hardened"] {
            assert!(profile_enables_hardened(Some(registered)), "{registered}");
        }
        // Separator and case are spelling, not identity.
        assert!(profile_enables_hardened(Some("coreutils-hardened")));
        assert!(profile_enables_hardened(Some("UNIX_HARDENED")));
        assert!(profile_enables_hardened(Some("  unix-hardened  ")));

        // An unregistered profile gets the ordinary obligation set even when
        // its name mentions a registered one or a platform.
        for unregistered in [
            "ci:unix",
            "unix",
            "coreutils",
            "nonhardened",
            "hardenedness",
            "unixish",
            "mycoreutils",
            "unix_hardened_v2",
            "release",
        ] {
            assert!(!profile_enables_hardened(Some(unregistered)), "{unregistered}");
        }
        assert!(!profile_enables_hardened(None));
    }

    #[test]
    fn the_hardened_registry_is_sorted_and_canonically_spelled() {
        assert!(HARDENED_PROFILES.windows(2).all(|pair| pair[0] < pair[1]));
        for profile in HARDENED_PROFILES {
            assert_eq!(&normalize_profile(profile), profile);
        }
    }

    #[test]
    fn hardened_profile_flags_permission_and_trust_ordering() {
        let func = test_function(vec![
            call_block(0, "std::fs::File::create"),
            call_block(1, "std::fs::set_permissions"),
            call_block(2, "libc::chroot"),
            call_block(3, "libc::getpwnam"),
            return_block(4),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::PermissionWindow));
        assert!(has_category(&vcs, HardenedVcCategory::TrustDomainOrder));
    }

    #[test]
    fn hardened_profile_flags_permission_window_when_mir_blocks_are_not_source_ordered() {
        let func = test_function(vec![
            call_block(10, "std::fs::File::create"),
            call_block(3, "std::fs::set_permissions"),
            return_block(11),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::PermissionWindow));
    }

    #[test]
    fn hardened_profile_flags_privilege_transition_before_late_domain_effect() {
        let func = test_function(vec![
            call_block(0, "libc::setgid"),
            call_block(1, "libloading::os::unix::Library::open::dlopen"),
            return_block(2),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::TrustDomain));
        assert!(has_category(&vcs, HardenedVcCategory::TrustDomainOrder));
    }

    #[test]
    fn hardened_profile_emits_formula_bearing_mir_assert_panic_boundary() {
        let func = test_function(vec![
            assert_block(
                0,
                Operand::Constant(ConstValue::Bool(false)),
                true,
                AssertMessage::Custom("caller validated input".into()),
            ),
            return_block(1),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);

        assert_ne!(vc.formula, Formula::Bool(true));
        assert_eq!(vc.formula, Formula::Not(Box::new(Formula::Bool(false))));
        match &vc.kind {
            VcKind::HardenedBoundary { callee, detail, .. } => {
                assert!(callee.contains("mir_assert"));
                assert!(detail.contains("caller validated input"));
            }
            other => panic!("expected hardened boundary VC, got {other:?}"),
        }
    }

    #[test]
    fn hardened_profile_marks_bounds_asserts_as_panic_boundaries() {
        let func = test_function(vec![
            assert_block(
                0,
                Operand::Constant(ConstValue::Bool(false)),
                false,
                AssertMessage::BoundsCheck,
            ),
            return_block(1),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);

        assert_ne!(vc.formula, Formula::Bool(true));
        assert_eq!(vc.formula, Formula::Bool(false));
        match &vc.kind {
            VcKind::HardenedBoundary { callee, detail, .. } => {
                assert!(callee.contains("BoundsCheck"));
                assert!(detail.contains("bounds-check"));
            }
            other => panic!("expected hardened boundary VC, got {other:?}"),
        }
    }

    #[test]
    fn hardened_profile_mir_assert_panic_boundary_respects_function_preconditions() {
        let mut func = test_function(vec![
            assert_block(
                0,
                Operand::Constant(ConstValue::Bool(false)),
                true,
                AssertMessage::Custom("caller validated input".into()),
            ),
            return_block(1),
        ]);
        let precondition = Formula::Var("caller_ok".to_string(), Sort::Bool);
        func.preconditions.push(precondition.clone());

        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);

        assert_eq!(
            vc.formula,
            Formula::And(vec![precondition, Formula::Not(Box::new(Formula::Bool(false)))])
        );
    }

    // Trust: regression for the precondition-staleness false-PROVE in the hardened
    // panic-boundary path. The block reassigns `hi` (a free var of the entry
    // contract `hi == lo`) before its Assert; the stale precondition must be
    // dropped, otherwise — conjoined with the live `hi == big` — it vacuously
    // discharges a real panic boundary. Mirrors the v2-path kill.
    fn precond_stale_hardened_fn(reassign_hi: bool) -> VerifiableFunction {
        let stmts = if reassign_hi {
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                span: SourceSpan::default(),
            }]
        } else {
            vec![]
        };
        VerifiableFunction {
            name: "precond_stale_hardened".to_string(),
            def_path: "crate::precond_stale_hardened".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("lo".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("big".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts,
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Constant(ConstValue::Bool(false)),
                            expected: true,
                            msg: AssertMessage::Custom("boundary".into()),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 3,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![Formula::Eq(
                Box::new(Formula::Var("hi".into(), Sort::Int)),
                Box::new(Formula::Var("lo".into(), Sort::Int)),
            )],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// True if `formula` contains an equality directly between vars `a` and `b`
    /// (either order). Asserts the entry precondition `hi == lo` is/isn't present
    /// robustly against the parameter type-range bounds now conjoined by
    /// `conjoin_arg_type_ranges` (which make `lo` appear via `0 <= lo <= MAX`
    /// regardless of the stale equality, so a bare free-variable check no longer
    /// distinguishes the dropped precondition).
    /// Strip a `#<token>` version suffix from a var name (the S2c flip renames
    /// `hi` -> `hi#token`), so these structural assertions test the SEMANTIC name.
    fn vname(n: &str) -> &str {
        n.split('#').next().unwrap_or(n)
    }

    fn formula_has_eq_between(formula: &Formula, a: &str, b: &str) -> bool {
        fn var_name(f: &Formula) -> Option<&str> {
            match f {
                Formula::Var(n, _) => Some(vname(n.as_str())),
                _ => None,
            }
        }
        let mut found = false;
        formula.visit(&mut |sub| {
            if let Formula::Eq(l, r) = sub {
                let (ln, rn) = (var_name(l), var_name(r));
                if (ln == Some(a) && rn == Some(b)) || (ln == Some(b) && rn == Some(a)) {
                    found = true;
                }
            }
        });
        found
    }

    #[test]
    fn hardened_panic_boundary_drops_precondition_after_reassignment() {
        let func = precond_stale_hardened_fn(true);
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);
        // `hi` is reassigned before the assert, so the entry contract `hi == lo`
        // is stale and must NOT constrain the boundary. Under the S2c flip this is
        // by NAME-DISJOINTNESS (not drop): the stale `hi == lo` is conjoined BARE
        // while the body's reassigned `hi` is renamed `hi#token` — different SMT
        // variables, so the precondition cannot unify with the body. Assert the body
        // carries a VERSIONED `hi`, proving the bare stale precondition is inert (the
        // flip's equivalent of the old kill's drop).
        assert!(
            format!("{:?}", vc.formula).contains("hi#"),
            "the reassigned `hi` must be versioned so the bare stale `hi == lo` cannot \
             constrain the boundary: {:?}",
            vc.formula
        );
    }

    #[test]
    fn hardened_panic_boundary_keeps_live_precondition() {
        // Control: no reassignment, so `hi == lo` is live and must be conjoined.
        let func = precond_stale_hardened_fn(false);
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);
        assert!(
            formula_has_eq_between(&vc.formula, "hi", "lo"),
            "live precondition `hi == lo` must survive when `hi` is never reassigned; got {:?}",
            vc.formula
        );
    }

    // `if hi <= 1000 { [hi = big;] <panic boundary> }`. The dominating guard
    // resolves to `hi <= 1000`; `path_map()` keeps it with no redef filter, so the
    // hardened lane conjoined it even after `hi = big` (stale) — a false-PROVE of any
    // boundary needing `hi > 1000`. The guard must now be dropped on reassignment.
    fn guard_stale_hardened_fn(reassign_hi: bool) -> VerifiableFunction {
        use trust_types::BinOp;
        let guarded_stmts = if reassign_hi {
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            }]
        } else {
            vec![]
        };
        VerifiableFunction {
            name: "guard_stale_hardened".to_string(),
            def_path: "crate::guard_stale_hardened".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Le,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1000, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(3)),
                            targets: vec![(0, BlockId(3))],
                            otherwise: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: guarded_stmts,
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Constant(ConstValue::Bool(false)),
                            expected: true,
                            msg: AssertMessage::Custom("boundary".into()),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn hardened_panic_boundary_drops_stale_dominating_guard() {
        let vc_smt = |reassign: bool| {
            let func = guard_stale_hardened_fn(reassign);
            let vcs = generate_hardened_vcs_for_profile(&func);
            hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary).formula.to_smtlib()
        };
        // Reassigned: the dominating guard `hi <= 1000` is stale and must be dropped.
        assert!(
            !vc_smt(true).contains("(<= hi 1000)"),
            "stale dominating guard `hi <= 1000` must be dropped after `hi = big`; got {}",
            vc_smt(true)
        );
        // Control: no reassignment -> the guard is live and must be retained.
        assert!(
            vc_smt(false).contains("(<= hi 1000)"),
            "live dominating guard must survive when `hi` is never reassigned; got {}",
            vc_smt(false)
        );
    }

    #[test]
    fn hardened_panic_boundary_conjoins_parameter_type_ranges() {
        // Regression for the panic_boundary OVER-REFUTATION: the hardened MIR-assert
        // boundary must carry parameter type-range bounds (like the per-statement
        // arithmetic-safety overflow VC), else it fabricates a spurious overflow for
        // provably-safe arithmetic (e.g. `a as u16 + b as u16` with u8 params).
        // `big` is a u32 parameter that does NOT appear in the entry precondition
        // `hi == lo`, so its presence proves the type-range bound was conjoined.
        let func = precond_stale_hardened_fn(false);
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);
        assert!(
            vc.formula.free_variables().contains("big"),
            "hardened panic-boundary VC must conjoin parameter type-range bounds (param `big`); got {:?}",
            vc.formula
        );
    }

    #[test]
    fn unwrap_or_default_is_error_discard_not_panic_boundary() {
        let func = test_function(vec![
            call_block(0, "core::result::Result::unwrap_or_default"),
            return_block(1),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert!(has_category(&vcs, HardenedVcCategory::ErrorDiscard));
        assert!(!has_category(&vcs, HardenedVcCategory::PanicBoundary));
    }

    /// Trust (unwrap panic-freedom, dominated-safe): the guarded-unwrap fixture
    /// the primary lane proves — `d = discriminant(r); if d == Ok { r.unwrap() }`
    /// on a MODELED std `Result` receiver.
    fn guarded_unwrap_fixture(guarded: bool) -> VerifiableFunction {
        let result_ty = Ty::Adt { adt_kind: None, layout: None, 
            name: "core::result::Result".into(),
            fields: vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                ("__v0_0".into(), Ty::u64()),
                ("__v1_0".into(), Ty::Unit),
            ],
            variants: vec![
                trust_types::VariantDef {
                    name: "Ok".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), Ty::u64())],
                },
                trust_types::VariantDef {
                    name: "Err".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), Ty::Unit)],
                },
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let unwrap_call = |target: usize| Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: "core::result::Result::<T, E>::unwrap".into(),
            args: vec![Operand::Move(Place::local(1))],
            dest: Place::local(3),
            target: Some(BlockId(target)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            is_foreign: false,
        };
        let blocks = if guarded {
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: unwrap_call(3) },
                return_block(2),
                return_block(3),
            ]
        } else {
            vec![
                BasicBlock { id: BlockId(0), stmts: vec![], terminator: unwrap_call(1) },
                return_block(1),
            ]
        };
        VerifiableFunction {
            name: "unwrap_twin_fixture".into(),
            def_path: "crate::unwrap_twin_fixture".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: result_ty, name: Some("r".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 64, signed: true },
                        name: Some("d".into()),
                    },
                    LocalDecl { index: 3, ty: Ty::u64(), name: Some("x".into()) },
                ],
                blocks,
                arg_count: 1,
                return_ty: Ty::u64(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// The PanicBoundary twin for a PINNED (guarded) unwrap carries the SAME
    /// solvable refutation formula as the primary lane — the body `d == 1`
    /// (Err tag) conjoined with the dominating guard `d == 0` — instead of the
    /// fail-closed `Bool(true)`, so both rows are decided by the same obligation.
    #[test]
    fn hardened_panic_boundary_twin_carries_pinned_unwrap_formula() {
        let func = guarded_unwrap_fixture(true);
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);
        assert_ne!(vc.formula, Formula::Bool(true), "the twin must carry the solvable formula");
        let smt = vc.formula.to_smtlib();
        assert!(smt.contains("(= d 1)"), "twin must carry the Err-tag body: {smt}");
        assert!(smt.contains("(= d 0)"), "twin must carry the dominating Ok guard: {smt}");
    }

    /// A bare PARAM unwrap's twin now carries the shape-(d) FREE-ENTRY-TAG
    /// refutation (`r.__tag == Err`, no dominating guard conjunct) instead of
    /// the fail-closed `Bool(true)` placeholder — the primary lane mints the
    /// same solvable refutation VC (`param_unwrap_refutes_with_free_entry_tag`
    /// in generate.rs), so the twin stays in lockstep: SAT with `r.0 = 1` is a
    /// genuine `Err` witness, and the hardened row FAILS with a model rather
    /// than sitting UNKNOWN.
    #[test]
    fn hardened_panic_boundary_twin_carries_free_entry_tag_refutation() {
        let func = guarded_unwrap_fixture(false);
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_vc_for_category(&vcs, HardenedVcCategory::PanicBoundary);
        assert_ne!(
            vc.formula,
            Formula::Bool(true),
            "a bare param unwrap's twin must carry the shape-(d) refutation"
        );
        let smt = vc.formula.to_smtlib();
        assert!(smt.contains("(= r.0 1)"), "twin must pin the free entry tag to Err: {smt}");
        assert!(!smt.contains("(= r.0 0)"), "no success guard may pin the tag: {smt}");
    }

    #[test]
    fn path_call_matches_require_component_boundaries() {
        assert!(call_matches("std::fs::remove_file", "std::fs::remove_file"));
        assert!(call_matches("std::fs::remove_file::<&std::path::Path>", "std::fs::remove_file"));
        assert!(call_matches("std::fs::File::create", "File::create"));
        assert!(call_matches(
            "core::result::Result::<(), std::io::Error>::ok",
            "core::result::Result::ok"
        ));

        assert!(!call_matches("my_std::fs::remove_file", "std::fs::remove_file"));
        assert!(!call_matches("std::fs::remove_file_at", "std::fs::remove_file"));
        assert!(!call_matches("std::fs::create_dir_all", "std::fs::create_dir"));
        assert!(!call_matches("std::env::args_os", "std::env::args"));
        assert!(!call_matches("std::fs::MyFile::create", "File::create"));
        assert!(call_matches("std::io::stdio::stdout", "stdout"));
        assert!(call_matches("std::io::_print", "_print"));
    }

    #[test]
    fn hardened_profile_ignores_path_rule_prefix_neighbors() {
        let func = test_function(vec![
            call_block(0, "alloc::string::String::from_utf8_lossy"),
            call_block(1, "std::str::from_utf8_unchecked"),
            call_block(2, "my_std::fs::remove_file"),
            call_block(3, "std::fs::remove_file_at"),
            call_block(4, "std::fs::create_dir_all"),
            call_block(5, "std::env::args_os"),
            call_block(6, "std::fs::set_permissions_recursive"),
            return_block(7),
        ]);

        let vcs = generate_hardened_vcs_for_profile(&func);

        assert_eq!(vcs.len(), 1);
        assert!(has_category(&vcs, HardenedVcCategory::ByteLoss));
        assert!(!has_category(&vcs, HardenedVcCategory::Utf8Reject));
        assert!(!has_category(&vcs, HardenedVcCategory::CompatObservable));
        assert!(!has_category(&vcs, HardenedVcCategory::RawPathApi));
    }

    // Trust SAFE_API §4.2.7: cap-wrapper hardened rule.
    fn raw_path_boundary(vcs: &[VerificationCondition]) -> &VerificationCondition {
        vcs.iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::HardenedBoundary { category: HardenedVcCategory::RawPathApi, .. }
                )
            })
            .expect("RawPathApi boundary VC")
    }

    #[test]
    fn cap_wrapper_boundary_discharges_against_predicate_precondition() {
        let dir_open = Formula::Pred(
            trust_types::Symbol::intern("dir_open"),
            vec![Formula::Var("dir".into(), Sort::Int)],
        );

        // A hardened call inside a function carrying a Pred precondition is a cap
        // wrapper: the boundary discharges against the predicate (NOT Bool(true)).
        let mut wrapper =
            test_function(vec![call_block(0, "std::fs::remove_file"), return_block(1)]);
        wrapper.preconditions = vec![dir_open];
        let boundary = raw_path_boundary(&generate_hardened_vcs_for_profile(&wrapper)).clone();
        assert!(
            !matches!(boundary.formula, Formula::Bool(true)),
            "cap wrapper must not fail closed on Bool(true)"
        );
        assert!(
            formula_mentions_pred(&boundary.formula),
            "boundary must be discharged against the cap predicate"
        );

        // Control: the identical raw call WITHOUT a cap precondition stays
        // fail-closed (Bool(true) -> DesignRequirement), unweakened.
        let raw = test_function(vec![call_block(0, "std::fs::remove_file"), return_block(1)]);
        let raw_boundary = raw_path_boundary(&generate_hardened_vcs_for_profile(&raw)).clone();
        assert!(
            matches!(raw_boundary.formula, Formula::Bool(true)),
            "non-cap raw-API use must remain a fail-closed mandate"
        );
    }

    /// True if `formula` syntactically contains `Eq(Var(name), <anything>)` whose
    /// RHS is a `Sub(Var(sub_lhs), Int(sub_rhs))` — i.e. the threaded result def
    /// `name == sub_lhs - sub_rhs`.
    fn formula_has_result_def_sub(
        formula: &Formula,
        name: &str,
        sub_lhs: &str,
        sub_rhs: i128,
    ) -> bool {
        let mut found = false;
        formula.visit(&mut |sub| {
            if let Formula::Eq(l, r) = sub
                && matches!(l.as_ref(), Formula::Var(n, _) if vname(n) == name)
                && let Formula::Sub(sl, sr) = r.as_ref()
                && matches!(sl.as_ref(), Formula::Var(n, _) if vname(n) == sub_lhs)
                && matches!(sr.as_ref(), Formula::Int(v) if *v == sub_rhs)
            {
                found = true;
            }
        });
        found
    }

    /// True if `formula` contains `Le(Var(name), Int(bound))` — the path guard
    /// `name <= bound`.
    fn formula_has_le_var_int(formula: &Formula, name: &str, bound: i128) -> bool {
        let mut found = false;
        formula.visit(&mut |sub| {
            if let Formula::Le(l, r) = sub
                && matches!(l.as_ref(), Formula::Var(n, _) if vname(n) == name)
                && matches!(r.as_ref(), Formula::Int(v) if *v == bound)
            {
                found = true;
            }
        });
        found
    }

    fn hardened_shl_panic_vc(vcs: &[VerificationCondition]) -> &VerificationCondition {
        vcs.iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::HardenedBoundary { category: HardenedVcCategory::PanicBoundary, callee, .. }
                        if callee.contains("Shl")
                )
            })
            .expect("expected a PanicBoundary VC for the Shl assert")
    }

    /// The `signed_max` MIR subset reaching the hardened `1i128 << (width-1)` Shl
    /// boundary: bb4 computes `_7 = CheckedSub(width, 1)` and asserts `!_7.1`;
    /// bb5 reads `_6 = _7.0`, computes `_8 = Lt(_6, 128)` and asserts `_8`
    /// (the Shl-overflow check); bb6 performs the shift. Path guards: `width >= 1`,
    /// `width <= 127`.
    fn signed_max_shl_fixture() -> VerifiableFunction {
        use trust_types::{AssertMessage, BinOp, Projection};
        VerifiableFunction {
            name: "signed_max".to_string(),
            def_path: "signed_max".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
                    LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                    LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
                    LocalDecl {
                        index: 7,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("_7".into()),
                    },
                    LocalDecl { index: 8, ty: Ty::Bool, name: Some("_8".into()) },
                ],
                blocks: vec![
                    // bb0: width >= 1 ?
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Ge,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(3)),
                            targets: vec![(0, BlockId(7))],
                            otherwise: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1: width <= 127 ?
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Le,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(127, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(4)),
                            targets: vec![(0, BlockId(7))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: _7 = CheckedSub(width, 1); assert(!_7.1) -> bb3
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 7,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb3: _6 = _7.0; _8 = Lt(_6, 128); assert(_8, Shl) -> bb4
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(6),
                                rvalue: Rvalue::Use(Operand::Move(Place {
                                    local: 7,
                                    projections: vec![Projection::Field(0)],
                                })),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(8),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    Operand::Copy(Place::local(6)),
                                    Operand::Constant(ConstValue::Uint(128, 32)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place::local(8)),
                            expected: true,
                            msg: AssertMessage::Overflow(BinOp::Shl),
                            target: BlockId(4),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb4: _5 = Shl(1i128, _6); _0 = _5; return
                    BasicBlock {
                        id: BlockId(4),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Shl,
                                    Operand::Constant(ConstValue::Int(1)),
                                    Operand::Move(Place::local(6)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Move(Place::local(5))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(7),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MAX))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Regression: the hardened `Overflow(Shl)` panic-boundary VC for
    /// `signed_max`'s `1i128 << (width-1)` must thread the no-overflow result def
    /// `_7.0 == width - 1` (computed in the PRECEDING CheckedSub block) into the
    /// shift-assert block, so the path guard `width <= 127` can bound the shift
    /// amount `_6 == _7.0`. Without the cross-block thread, `_7.0` is free, the
    /// violation `NOT(_6 < 128)` is SAT (`_6 = 200`), and the provably-safe shift
    /// false-FAILs.
    #[test]
    fn hardened_shl_panic_boundary_threads_checked_sub_result() {
        let func = signed_max_shl_fixture();
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_shl_panic_vc(&vcs);

        // The threaded result def `_7.0 == width - 1` (named `_7.0` via the
        // tuple-field naming convention) must reach the VC.
        assert!(
            formula_has_result_def_sub(&vc.formula, "_7.0", "width", 1),
            "expected threaded result def `_7.0 == width - 1`; got {:?}",
            vc.formula
        );
        // The same-block def `_6 == _7.0` and the path guard `width <= 127` must
        // both be present, so the chain `_6 == _7.0 == width - 1 <= 126 < 128`
        // discharges the violation.
        let has_6_eq_70 = {
            let mut found = false;
            vc.formula.visit(&mut |sub| {
                if let Formula::Eq(l, r) = sub
                    && matches!(l.as_ref(), Formula::Var(n, _) if vname(n) == "_6")
                    && matches!(r.as_ref(), Formula::Var(n, _) if vname(n) == "_7.0")
                {
                    found = true;
                }
            });
            found
        };
        assert!(has_6_eq_70, "expected same-block def `_6 == _7.0`; got {:?}", vc.formula);
        assert!(
            formula_has_le_var_int(&vc.formula, "width", 127),
            "expected path guard `width <= 127` to reach the VC; got {:?}",
            vc.formula
        );
    }

    /// ADVERSARIAL guardrail: a CheckedSub result used as a shift amount WITHOUT a
    /// guard bounding `width` must NOT be discharged — the threaded result def
    /// `_7.0 == width - 1` is true, but with `width` free (only its u32 type range
    /// applies) `_7.0` can be up to `u32::MAX - 1`, so `NOT(_6 < 128)` stays SAT
    /// and the genuinely-unsafe shift still REFUTES. The fix must not inject any
    /// `width <= 127`-style bound for this unguarded case.
    #[test]
    fn hardened_shl_unguarded_checked_sub_remains_refutable() {
        use trust_types::{AssertMessage, BinOp, Projection};
        // fn h(width: u32) -> i128 {
        //   let _7 = CheckedSub(width, 1); assert(!_7.1);
        //   let _6 = _7.0; let _8 = Lt(_6, 128); assert(_8, Shl);
        //   1i128 << _6
        // }  — NO `width <= 127` guard.
        let func = VerifiableFunction {
            name: "h".to_string(),
            def_path: "h".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
                    LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                    LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
                    LocalDecl {
                        index: 7,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("_7".into()),
                    },
                    LocalDecl { index: 8, ty: Ty::Bool, name: Some("_8".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 7,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(6),
                                rvalue: Rvalue::Use(Operand::Move(Place {
                                    local: 7,
                                    projections: vec![Projection::Field(0)],
                                })),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(8),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    Operand::Copy(Place::local(6)),
                                    Operand::Constant(ConstValue::Uint(128, 32)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place::local(8)),
                            expected: true,
                            msg: AssertMessage::Overflow(BinOp::Shl),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Constant(ConstValue::Int(1)),
                                Operand::Move(Place::local(6)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_shl_panic_vc(&vcs);

        // The result def is threaded (it is a true fact), but it bounds `_6` only
        // by `width - 1`; with `width` unconstrained above 128 the violation
        // stays SAT. Crucially, NO `width <= 127`-style upper bound may appear.
        let injects_upper_on_width = {
            let mut found = false;
            vc.formula.visit(&mut |sub| {
                if let Formula::Le(l, r) = sub
                    && matches!(l.as_ref(), Formula::Var(n, _) if n == "width")
                    && matches!(r.as_ref(), Formula::Int(b) if *b <= 127)
                {
                    found = true;
                }
            });
            found
        };
        assert!(
            !injects_upper_on_width,
            "unguarded shift must NOT have any `width <= 127`-style bound injected; got {:?}",
            vc.formula
        );
        // The violation `NOT(_6 < 128)` (i.e. the Lt cond is the assert cond) must
        // still be present and refutable — `_6 < 128` cannot be proven from a free
        // `width`.
        let has_shift_check = {
            let mut found = false;
            vc.formula.visit(&mut |sub| {
                if let Formula::Lt(l, r) = sub
                    && matches!(l.as_ref(), Formula::Var(n, _) if vname(n) == "_6")
                    && matches!(r.as_ref(), Formula::Int(128))
                {
                    found = true;
                }
            });
            found
        };
        assert!(
            has_shift_check,
            "the shift bound check `_6 < 128` must remain in the (refutable) VC; got {:?}",
            vc.formula
        );
    }

    // Trust: regression for the NESTED dominating-guard gap in the hardened
    // panic-boundary lane (aterm-hash `hash_bytes`, the `bytes[len-8..]` `len - 8`
    // CheckedSub inside `if len <= 16 { if len >= 8 { … } }`). The hardened twin's
    // formula previously carried only the OUTER `len <= 16` guard (via `path_map()`,
    // which surfaced one branch's guards) and DROPPED the inner `len >= 8`, leaving
    // `len - 8` underflow-unprovable. The fix conjoins the FULL dominating
    // path-condition the per-statement arithmetic VC uses, so `len >= 8` is asserted.
    //
    // `inner_guard == false` is the ADVERSARIAL control: the SAME `len - 8` op with
    // only the outer `len <= 16` guard (no `len >= 8`) is a genuine underflow and the
    // twin MUST stay refutable — `len >= 8` must NOT be fabricated for that block.
    fn nested_guard_sub_fn(inner_guard: bool) -> VerifiableFunction {
        use trust_types::{BinOp, Projection};
        // 0 ret, 1 len(u64 param), 2 _le16(bool), 3 _ge8(bool), 4 _sub(tuple).
        let locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("len".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("_le16".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("_ge8".into()) },
            LocalDecl { index: 4, ty: Ty::u64(), name: Some("_sub".into()) },
        ];
        // bb0: _le16 = len <= 16; switch _le16 { 0 => ret, _ => bb1 }
        let bb0 = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Le,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(16, 64)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(2)),
                targets: vec![(0, BlockId(5))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        // The `len - 8` CheckedSub + overflow assert (the Sub@173 twin).
        let sub_block = |id: usize| BasicBlock {
            id: BlockId(id),
            stmts: vec![Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(8, 64)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Copy(Place { local: 4, projections: vec![Projection::Field(1)] }),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Sub),
                target: BlockId(4),
                span: SourceSpan::default(),
            },
        };
        let mut blocks = vec![bb0];
        if inner_guard {
            // bb1: _ge8 = len >= 8; switch _ge8 { 0 => ret, _ => bb2 }
            blocks.push(BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(8, 64)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(3)),
                    targets: vec![(0, BlockId(5))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            });
            blocks.push(sub_block(2));
        } else {
            blocks.push(sub_block(1));
        }
        blocks.push(BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return });
        blocks.push(BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return });

        VerifiableFunction {
            name: "hash_bytes_nested_guard".to_string(),
            def_path: "crate::hash_bytes_nested_guard".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::Unit },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// True if the formula ASSERTS `len >= 8` (`Ge(len, 8)`), version-suffix tolerant.
    fn formula_asserts_ge_len_8(f: &trust_types::Formula) -> bool {
        use trust_types::Formula;
        let mut found = false;
        f.visit(&mut |sub| {
            if let Formula::Ge(l, r) = sub
                && matches!(l.as_ref(), Formula::Var(n, _) if vname(n) == "len")
                && matches!(r.as_ref(), Formula::Int(8))
            {
                found = true;
            }
        });
        found
    }

    fn nested_guard_sub_twin(inner_guard: bool) -> VerificationCondition {
        let func = nested_guard_sub_fn(inner_guard);
        let vcs = generate_hardened_vcs_for_profile(&func);
        vcs.into_iter()
            .find(|vc| {
                matches!(&vc.kind,
                    VcKind::HardenedBoundary { category: HardenedVcCategory::PanicBoundary, callee, .. }
                        if callee.contains("Overflow"))
            })
            .expect("expected hardened PanicBoundary twin for the `len - 8` sub")
    }

    #[test]
    fn hardened_panic_boundary_conjoins_inner_dominating_guard() {
        // The `len - 8` op under the nested `if len <= 16 { if len >= 8 { … } }`:
        // the twin MUST carry the inner `len >= 8` in ASSERTED form (the same
        // hypothesis the per-statement arithmetic VC discharges with).
        let vc = nested_guard_sub_twin(true);
        assert!(
            formula_asserts_ge_len_8(&vc.formula),
            "hardened twin must assert the inner dominating guard `len >= 8`; got {:?}",
            vc.formula
        );
        // And it must carry the outer guard too (proving the FULL path-condition).
        let asserts_le_16 = {
            use trust_types::Formula;
            let mut found = false;
            vc.formula.visit(&mut |sub| {
                if let Formula::Le(l, r) = sub
                    && matches!(l.as_ref(), Formula::Var(n, _) if vname(n) == "len")
                    && matches!(r.as_ref(), Formula::Int(16))
                {
                    found = true;
                }
            });
            found
        };
        assert!(
            asserts_le_16,
            "hardened twin must also assert the outer `len <= 16`; got {:?}",
            vc.formula
        );
    }

    // ADVERSARIAL: the SAME `len - 8` op with ONLY the outer `len <= 16` guard (no
    // inner `len >= 8`) is a real underflow. The twin must NOT receive a fabricated
    // `len >= 8` — that block is not dominated by it.
    #[test]
    fn hardened_panic_boundary_no_fabricated_guard_on_unguarded_path() {
        let vc = nested_guard_sub_twin(false);
        assert!(
            !formula_asserts_ge_len_8(&vc.formula),
            "an unguarded `len - 8` (only `len <= 16`) must NOT receive a fabricated `len >= 8`; \
             got {:?}",
            vc.formula
        );
    }

    // ---- BoundsCheck panic-boundary subsumption (loop-yield in-range index) ----

    /// A `for i in 0..s.len() { … s[i] … }` slice index is PROVABLY in range via the
    /// range-yield bound `0 <= i < s.len()`, so the per-statement bounds VC PROVES it.
    /// The hardened panic-boundary lane must then SKIP its `BoundsCheck` twin
    /// (mirroring the Div/Rem nonzero-constant skip) instead of over-refuting a
    /// provably-safe guarded index. Uses the REAL extracted MIR of `for i in
    /// 0..s.len()` (the same fixture the per-statement `for_range_index_yield` test
    /// proves), whose BoundsCheck assert is bb5.
    #[test]
    fn hardened_boundscheck_twin_skipped_for_loop_yielded_index() {
        let func: VerifiableFunction =
            serde_json::from_str(include_str!("../tests/fixtures/for_range_index_mir.json"))
                .expect("fixture MIR must deserialize");

        // The `for i in 0..s.len()` BoundsCheck assert (bb5) is recognized as
        // provably in range...
        let skip = crate::generate::v2_boundscheck_index_in_range_skip_set(&func);
        assert!(
            skip.contains(&BlockId(5)),
            "the `for i in 0..s.len()` BoundsCheck assert (bb5) must be in the loop-yield \
             in-range skip set; skip set = {skip:?}"
        );

        // ...so NO hardened BoundsCheck twin is emitted for it (the per-statement
        // bounds VC already PROVES the access).
        let vcs = generate_hardened_vcs_for_profile(&func);
        assert!(
            !has_category_for_callee(
                &vcs,
                HardenedVcCategory::PanicBoundary,
                "mir_assert::BoundsCheck",
            ),
            "a provably-in-range loop index must NOT get a hardened BoundsCheck twin"
        );
    }

    /// An UNGUARDED slice index `s[i]` (no dominating guard, no loop-yield bound) is a
    /// real panic boundary: the hardened lane must STILL emit its `BoundsCheck` twin
    /// (fail-closed). Guards the soundness direction — the skip must NEVER fire on an
    /// index that is not provably in range.
    #[test]
    fn hardened_boundscheck_twin_emitted_for_unguarded_index() {
        // fn f(s: &[u32], i: usize) { let _ = s[i]; }
        //   bb0: _3 = PtrMetadata(_1); _4 = Lt(_2, _3); assert(_4, BoundsCheck) -> bb1
        let func = VerifiableFunction {
            name: "unguarded_index".to_string(),
            def_path: "crate::unguarded_index".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref {
                            mutable: false,
                            inner: Box::new(Ty::Slice {
                                elem: Box::new(Ty::Int { width: 32, signed: false }),
                            }),
                        },
                        name: Some("s".to_string()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some("i".to_string()),
                    },
                    LocalDecl { index: 3, ty: Ty::Int { width: 64, signed: false }, name: None },
                    LocalDecl { index: 4, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::UnaryOp(
                                    trust_types::UnOp::PtrMetadata,
                                    Operand::Copy(Place::local(1)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Copy(Place::local(3)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place::local(4)),
                            expected: true,
                            msg: AssertMessage::BoundsCheck,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        // No range/enumerate yield payload => nothing provably in range => empty set.
        assert!(
            crate::generate::v2_boundscheck_index_in_range_skip_set(&func).is_empty(),
            "an unguarded index must NOT be recognized as provably in range"
        );

        let vcs = generate_hardened_vcs_for_profile(&func);
        assert!(
            has_category_for_callee(
                &vcs,
                HardenedVcCategory::PanicBoundary,
                "mir_assert::BoundsCheck",
            ),
            "an unguarded slice index must still get a hardened BoundsCheck twin (fail-closed)"
        );
    }
}

// ===========================================================================
// HARDENED panic_boundary signed-128 BV guardrails.
//
// The hardened `Overflow(Sub)` / `OverflowNeg` panic-boundary VCs for signed
// >= 128-bit ops are now emitted in pure QF_BV (the native typed-CHC LIA lane
// cannot represent ±2^127). This module carries a SELF-CONTAINED two's-complement
// witness oracle (`eval_bv` / `eval_bv_bool`, ground — never trusts the solver)
// and proves, on the real `generate_hardened_vcs_for_profile` output:
//   (a) signed_max's `_5 - 1` (shift block-def `_5 = 1 << (width-1)` + the
//       `width <= 127` guard) is UNSAT/provable over the whole free space; and
//   (b) ADVERSARIALLY, `i128::MAX - (-1)`, `-(i128::MIN)`, and UNGUARDED i128
//       sub/neg each yield a SAT/refutable VC — a real overflow NEVER vacuously
//       proves.
// The oracle mirrors `generate.rs::signed_128_overflow_tests` exactly.
// ===========================================================================
#[cfg(test)]
mod hardened_signed_128_overflow_tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, HardenedVcCategory,
        LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
        VcKind, VerifiableBody, VerifiableFunction,
    };

    use super::generate_hardened_vcs_for_profile;

    fn assign(dest: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
    }

    // ---- self-contained SIGNED BITVECTOR witness evaluator (refutability oracle) ----
    //
    // Computes the EXACT two's-complement semantics of the BV violation formula over a
    // concrete witness, so a test can REFUTE the obligation (a real overflow makes the
    // violation TRUE → SAT) or confirm a guarded case is UNSAT. It NEVER trusts the
    // solver. An unmodeled node panics (an unexpected shape fails loudly).
    //
    // BV values are carried as `u128` bit patterns masked to `width` bits.
    fn bv_mask(width: u32) -> u128 {
        if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
    }

    // A bitvector value of width up to 129 bits: `lo` is the low 128 bits, `bit128`
    // is the 129th bit (only set for width == 129).
    #[derive(Clone, Copy, Debug)]
    struct Bv {
        lo: u128,
        bit128: bool,
        width: u32,
    }

    impl Bv {
        fn new(lo: u128, bit128: bool, width: u32) -> Self {
            Bv { lo: lo & bv_mask(width.min(128)), bit128: bit128 && width >= 129, width }
        }
        fn bit(self, i: u32) -> bool {
            if i >= 128 { self.bit128 } else { (self.lo >> i) & 1 == 1 }
        }
    }

    fn eval_bv(f: &Formula, env: &dyn Fn(&str) -> u128) -> Bv {
        match f {
            Formula::BitVec { value, width } => Bv::new(*value as u128, false, *width),
            Formula::Var(name, trust_types::Sort::BitVec(w)) => {
                Bv::new(env(name.as_str()), false, *w)
            }
            Formula::BvAdd(a, b, w) => {
                let va = eval_bv(a, env);
                let vb = eval_bv(b, env);
                let (sum, carry) = va.lo.overflowing_add(vb.lo);
                let bit128 = (va.bit128 ^ vb.bit128) ^ carry;
                Bv::new(sum, bit128, *w)
            }
            Formula::BvSub(a, b, w) => {
                let va = eval_bv(a, env);
                let vb = eval_bv(b, env);
                let (diff, borrow) = va.lo.overflowing_sub(vb.lo);
                let bit128 = (va.bit128 ^ vb.bit128) ^ borrow;
                Bv::new(diff, bit128, *w)
            }
            Formula::BvShl(a, b, w) => {
                let va = eval_bv(a, env);
                let vb = eval_bv(b, env);
                let shifted =
                    if vb.lo >= u128::from(*w) || vb.lo >= 128 { 0 } else { va.lo << vb.lo };
                Bv::new(shifted, false, *w)
            }
            Formula::BvSignExt(a, extra) => {
                let va = eval_bv(a, env);
                let new_w = va.width + extra;
                let sign = va.bit(va.width - 1);
                let bit128 = if new_w >= 129 { sign } else { false };
                let lo = if sign && new_w <= 128 {
                    let high = bv_mask(new_w) ^ bv_mask(va.width);
                    va.lo | high
                } else {
                    va.lo
                };
                Bv::new(lo, bit128, new_w)
            }
            Formula::BvExtract { inner, high, low } => {
                let vi = eval_bv(inner, env);
                let w = high - low + 1;
                let mut out: u128 = 0;
                for i in 0..w {
                    if vi.bit(low + i) {
                        out |= 1u128 << i;
                    }
                }
                Bv::new(out, false, w)
            }
            other => panic!("eval_bv: unhandled BV node {other:?}"),
        }
    }

    fn is_bv_node(f: &Formula) -> bool {
        matches!(
            f,
            Formula::BitVec { .. }
                | Formula::Var(_, trust_types::Sort::BitVec(_))
                | Formula::BvAdd(..)
                | Formula::BvSub(..)
                | Formula::BvShl(..)
                | Formula::BvSignExt(..)
                | Formula::BvExtract { .. }
        )
    }

    fn eval_bv_bool(f: &Formula, env: &dyn Fn(&str) -> u128) -> bool {
        match f {
            Formula::Bool(b) => *b,
            Formula::And(cs) => cs.iter().all(|c| eval_bv_bool(c, env)),
            Formula::Or(cs) => cs.iter().any(|c| eval_bv_bool(c, env)),
            Formula::Not(c) => !eval_bv_bool(c, env),
            Formula::Eq(a, b) => {
                assert!(
                    is_bv_node(a) || is_bv_node(b),
                    "hardened BV oracle: non-BV Eq leaf {f:?} — the BV core must not \
                     conjoin Int-sorted facts"
                );
                let va = eval_bv(a, env);
                let vb = eval_bv(b, env);
                va.lo == vb.lo && va.bit128 == vb.bit128
            }
            Formula::BvULt(a, b, _) => eval_bv(a, env).lo < eval_bv(b, env).lo,
            Formula::BvULe(a, b, _) => eval_bv(a, env).lo <= eval_bv(b, env).lo,
            other => panic!("eval_bv_bool: unhandled node {other:?}"),
        }
    }

    fn hardened_panic_vc<'a>(
        vcs: &'a [trust_types::VerificationCondition],
        msg_needle: &str,
    ) -> &'a trust_types::VerificationCondition {
        vcs.iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::HardenedBoundary { category: HardenedVcCategory::PanicBoundary, callee, .. }
                        if callee.contains(msg_needle)
                )
            })
            .unwrap_or_else(|| panic!("expected a hardened PanicBoundary VC matching {msg_needle:?}"))
    }

    /// `signed_max`'s trailing `_5 - 1`: bb0 guards `width <= 127`; bb1 computes
    /// `_6 = width - 1`, `_5 = 1i128 << _6`, `_9 = CheckedSub(_5, 1)` and asserts
    /// `!_9.1` (Overflow(Sub)). The hardened panic-boundary VC for that assert must
    /// be the BV `_5 - 1` underflow check + the BV shift block-def + the derived
    /// `_6 <= 126` bound — UNSAT over the whole free space (PROVED).
    fn signed_max_sub_hardened_fixture() -> VerifiableFunction {
        VerifiableFunction {
            name: "signed_max".to_string(),
            def_path: "test::signed_max".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
                    LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                    LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
                    LocalDecl {
                        index: 7,
                        ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                        name: Some("_7".into()),
                    },
                    LocalDecl { index: 8, ty: Ty::Bool, name: Some("_8".into()) },
                    LocalDecl {
                        index: 9,
                        ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
                        name: Some("_9".into()),
                    },
                ],
                // FAITHFUL multi-block shape of the real signed_max MIR (deep guard
                // chain bb0→bb2→bb3→bb4→bb5→bb6), so the cross-block `width <= 127`
                // bound must thread through several SwitchInt edges to reach the Sub
                // VC's shift-amount bound — exactly the e2e shape (a single-block
                // fixture masks a path-depth gap in the dominating-bound finder).
                blocks: vec![
                    // bb0: `_2 = Eq(width, 128); switchInt(_2) -> [0: bb2, otherwise: bb1]`
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            2,
                            Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(128, 32)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(2)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1: width == 128 → i128::MAX
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![assign(
                            0,
                            Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MAX))),
                        )],
                        terminator: Terminator::Goto(BlockId(9)),
                    },
                    // bb2: `_3 = Ge(width, 1); switchInt(_3) -> [0: bb8, otherwise: bb3]`
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![assign(
                            3,
                            Rvalue::BinaryOp(
                                BinOp::Ge,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(3)),
                            targets: vec![(0, BlockId(8))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb3: `_4 = Le(width, 127); switchInt(_4) -> [0: bb8, otherwise: bb4]`
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![assign(
                            4,
                            Rvalue::BinaryOp(
                                BinOp::Le,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(127, 32)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(4)),
                            targets: vec![(0, BlockId(8))],
                            otherwise: BlockId(4),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb4: `_7 = SubWithOverflow(width, 1); assert(!_7.1) -> bb5`
                    BasicBlock {
                        id: BlockId(4),
                        stmts: vec![assign(
                            7,
                            Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                        )],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 7,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(5),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb5: `_6 = move(_7.0); _8 = Lt(_6, 128); assert(_8, Shl) -> bb6`
                    BasicBlock {
                        id: BlockId(5),
                        stmts: vec![
                            assign(
                                6,
                                Rvalue::Use(Operand::Move(Place {
                                    local: 7,
                                    projections: vec![Projection::Field(0)],
                                })),
                            ),
                            assign(
                                8,
                                Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    Operand::Copy(Place::local(6)),
                                    Operand::Constant(ConstValue::Uint(128, 32)),
                                ),
                            ),
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place::local(8)),
                            expected: true,
                            msg: AssertMessage::Overflow(BinOp::Shl),
                            target: BlockId(6),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb6: `_5 = Shl(1i128, _6); _9 = SubWithOverflow(_5, 1i128); assert(!_9.1, Sub) -> bb7`
                    BasicBlock {
                        id: BlockId(6),
                        stmts: vec![
                            assign(
                                5,
                                Rvalue::BinaryOp(
                                    BinOp::Shl,
                                    Operand::Constant(ConstValue::Int(1)),
                                    Operand::Move(Place::local(6)),
                                ),
                            ),
                            assign(
                                9,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Sub,
                                    Operand::Copy(Place::local(5)),
                                    Operand::Constant(ConstValue::Int(1)),
                                ),
                            ),
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 9,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(7),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb7: `_0 = move(_9.0)`
                    BasicBlock {
                        id: BlockId(7),
                        stmts: vec![assign(
                            0,
                            Rvalue::Use(Operand::Move(Place {
                                local: 9,
                                projections: vec![Projection::Field(0)],
                            })),
                        )],
                        terminator: Terminator::Goto(BlockId(9)),
                    },
                    // bb8: out-of-contract → i128::MAX
                    BasicBlock {
                        id: BlockId(8),
                        stmts: vec![assign(
                            0,
                            Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MAX))),
                        )],
                        terminator: Terminator::Goto(BlockId(9)),
                    },
                    BasicBlock { id: BlockId(9), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// (a) The hardened panic_boundary VC for `signed_max`'s `_5 - 1` (shift
    ///     block-def + `width <= 127`) is UNSAT/provable in BV over the whole free
    ///     space — so the obligation that was UNKNOWN on the native LIA lane now
    ///     PROVES.
    #[test]
    fn hardened_signed_max_sub_is_provable_unsat() {
        // Force the hardened lane on for the duration (the generator is called
        // directly, so this is belt-and-suspenders; it does not gate the call).
        let func = signed_max_sub_hardened_fixture();
        let vcs = generate_hardened_vcs_for_profile(&func);
        // The multi-block fixture has TWO `Sub` asserts: bb4's u32 `width - 1`
        // (correctly Int-path, no BV) and bb6's i128 `_5 - 1` (the BV-routed one we
        // care about). Select the i128 one by its BV content (a `BvShl` block-def).
        let vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::HardenedBoundary { callee, .. } if callee.contains("Sub"))
                    && {
                        let mut has_bvshl = false;
                        vc.formula.visit(&mut |s| {
                            if matches!(s, Formula::BvShl(..)) {
                                has_bvshl = true;
                            }
                        });
                        has_bvshl
                    }
            })
            .expect("expected a BV-routed i128 `_5 - 1` Sub panic_boundary VC (with a BvShl block-def)");

        // RELIABLE STRUCTURAL CHECK (the witness sweep below leaves Int vars at 0,
        // so it can't discriminate the BV bound value): the BV shift-amount bound
        // MUST be the TIGHT `amt < 127`, threaded from `width <= 127` through the
        // `_6 = move (_7.0)` / `_7 = SubWithOverflow(width, 1)` indirection. The weak
        // `amt < 128` (the Shl-assert bound alone) admits `amt = 127 ⇒ _5 = i128::MIN`
        // and would false-FAIL the provably-safe `_5 - 1`.
        let mut amt_bound: Option<i128> = None;
        vc.formula.visit(&mut |sub| {
            if let Formula::BvULt(l, r, _) = sub
                && matches!(l.as_ref(), Formula::Var(n, _) if n.starts_with("__trust_ovf_bv_amt"))
                && let Formula::BitVec { value, .. } = r.as_ref()
            {
                amt_bound = Some(amt_bound.map_or(*value, |b: i128| b.min(*value)));
            }
        });
        assert_eq!(
            amt_bound,
            Some(127),
            "hardened BV shift-amount bound must be the TIGHT `amt < 127` (from `width <= 127` \
             threaded through `_6 = move (_7.0)` / `_7 = SubWithOverflow(width, 1)`), not the weak \
             `< 128` (which admits `amt = 127 ⇒ _5 = i128::MIN ⇒` false-FAIL); got {amt_bound:?}. \
             formula: {:?}",
            vc.formula
        );

        // The BV core carries `_5 == bvshl(1, amt) ∧ amt < 127` (derived from
        // `width <= 127` through `_6 = width - 1`) ∧ the `w+1`-bit sub overflow
        // check. EXHAUSTIVELY sweep the shift amount in [0, 200] (incl. out-of-bound
        // values the `amt < 127` BV guard must filter), binding the BV `amt`/`_5`
        // views to a CONSISTENT witness. The violation must be FALSE for every
        // witness → UNSAT → PROVED (no underflow feasible).
        let amt_bv = "__trust_ovf_bv_amt__6";
        let _5_bv = "__trust_ovf_bv_lhs__5";
        for amt in 0u128..=200 {
            let _5_val: u128 = if amt >= 128 { 0 } else { 1u128 << amt };
            let env = |name: &str| -> u128 {
                if name == amt_bv {
                    amt
                } else if name == _5_bv {
                    _5_val
                } else {
                    0
                }
            };
            assert!(
                !eval_bv_bool(&vc.formula, &env),
                "hardened `_5 - 1` must be UNSAT (PROVED) for amt={amt} (_5={_5_val}); \
                 a SAT witness here would be a false-FAIL. formula: {:?}",
                vc.formula
            );
        }

        // SANITY: the shift block-def really constrains `_5` — an INCONSISTENT
        // witness (`_5` NOT `1 << amt`) must fail the block-def equality (formula
        // FALSE), proving the UNSAT is REAL, not a dropped def.
        let inconsistent = |name: &str| -> u128 {
            match name {
                n if n == amt_bv => 5,
                n if n == _5_bv => i128::MIN as u128,
                _ => 0,
            }
        };
        assert!(
            !eval_bv_bool(&vc.formula, &inconsistent),
            "inconsistent (_5 != 1<<amt) witness must fail the block-def equality; \
             formula: {:?}",
            vc.formula
        );
    }

    /// (b1) ADVERSARIAL: an UNGUARDED two-operand `a - b` (free i128 params, no
    ///      block-def, no guard) yields a hardened BV Sub VC that is SAT/refutable —
    ///      `i128::MAX - (-1)` (a real positive overflow) must STILL be refuted.
    fn unguarded_i128_sub_hardened_fixture() -> VerifiableFunction {
        VerifiableFunction {
            name: "f".to_string(),
            def_path: "test::f".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::i128(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i128(), name: Some("b".into()) },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
                        name: Some("_3".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            3,
                            Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                        )],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place {
                                local: 3,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn hardened_unguarded_i128_sub_stays_refutable() {
        let func = unguarded_i128_sub_hardened_fixture();
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_panic_vc(&vcs, "Sub");

        let a_bv = "__trust_ovf_bv_lhs_a";
        let b_bv = "__trust_ovf_bv_rhs_b";
        // i128::MAX - (-1) = i128::MAX + 1 overflows above MAX. Must be SAT.
        let overflow = |name: &str| -> u128 {
            if name == a_bv {
                i128::MAX as u128
            } else if name == b_bv {
                (-1i128) as u128
            } else {
                0
            }
        };
        assert!(
            eval_bv_bool(&vc.formula, &overflow),
            "REAL hardened i128 overflow (i128::MAX - (-1)) must satisfy the violation \
             (refutable), never vacuously proved; formula: {:?}",
            vc.formula
        );
        // SAFE 5 - 3 = 2 must be UNSAT (not a false-FAIL).
        let safe = |name: &str| -> u128 {
            if name == a_bv {
                5
            } else if name == b_bv {
                3
            } else {
                0
            }
        };
        assert!(
            !eval_bv_bool(&vc.formula, &safe),
            "SAFE hardened i128 sub (5 - 3) must NOT satisfy the violation; formula: {:?}",
            vc.formula
        );
    }

    /// (b2) ADVERSARIAL: an UNGUARDED shift `_5 = 1i128 << n` (n FREE) then `_5 - 1`
    ///      must STAY refutable — with `n = 127`, `_5 = 2^127 = i128::MIN`, so
    ///      `_5 - 1` underflows. The shift def WITHOUT the `n < 127` bound must NOT
    ///      vacuously prove. (Proves the BOUND, not the def, discharges signed_max.)
    fn unguarded_shift_sub_hardened_fixture() -> VerifiableFunction {
        VerifiableFunction {
            name: "h".to_string(),
            def_path: "test::h".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                    LocalDecl {
                        index: 9,
                        ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
                        name: Some("_9".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            assign(
                                5,
                                Rvalue::BinaryOp(
                                    BinOp::Shl,
                                    Operand::Constant(ConstValue::Int(1)),
                                    Operand::Copy(Place::local(1)),
                                ),
                            ),
                            assign(
                                9,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Sub,
                                    Operand::Copy(Place::local(5)),
                                    Operand::Constant(ConstValue::Int(1)),
                                ),
                            ),
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 9,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Sub),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn hardened_unguarded_shift_sub_stays_refutable() {
        let func = unguarded_shift_sub_hardened_fixture();
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_panic_vc(&vcs, "Sub");

        let amt_bv = "__trust_ovf_bv_amt_n";
        let _5_bv = "__trust_ovf_bv_lhs__5";
        // n = 127 → _5 = 2^127 (= i128::MIN bit pattern). `_5 - 1` underflows. The
        // formula carries the shift def `_5 == bvshl(1, amt)` but NO `amt < 127`
        // bound (n is unguarded), so this witness MUST satisfy the violation (SAT).
        let witness = |name: &str| -> u128 {
            match name {
                n if n == amt_bv => 127,
                n if n == _5_bv => 1u128 << 127,
                _ => 0,
            }
        };
        assert!(
            eval_bv_bool(&vc.formula, &witness),
            "UNGUARDED hardened shift (`1 << n`, n=127) `_5 - 1` MUST be refutable \
             (SAT) — a real i128::MIN - 1 underflow must never be vacuously proved; \
             formula: {:?}",
            vc.formula
        );
    }

    /// `signed_min`'s `-_5` where `_5 = 1i128 << (width-1)`: bb0 guards `width <= 127`;
    /// bb1 computes `_6 = width - 1`, `_5 = 1i128 << _6`, then asserts `OverflowNeg`
    /// (cond `_c = (_5 == INT_MIN)`, expected false) with target bb2 where `_0 = -_5`.
    /// The hardened panic_boundary VC must be the BV `-_5` (`_5 == INT_MIN`) check +
    /// the shift block-def + the derived `_6 <= 126` bound — UNSAT (PROVED), since
    /// `_5 <= 2^126 < 2^127 = -INT_MIN`.
    fn signed_min_neg_hardened_fixture() -> VerifiableFunction {
        VerifiableFunction {
            name: "signed_min".to_string(),
            def_path: "test::signed_min".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                    LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                    LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
                    LocalDecl { index: 7, ty: Ty::i128(), name: Some("_7".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            2,
                            Rvalue::BinaryOp(
                                BinOp::Le,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(127, 32)),
                            ),
                        )],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Move(Place::local(2)),
                            targets: vec![(0, BlockId(3))],
                            otherwise: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            assign(
                                6,
                                Rvalue::BinaryOp(
                                    BinOp::Sub,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            ),
                            assign(
                                5,
                                Rvalue::BinaryOp(
                                    BinOp::Shl,
                                    Operand::Constant(ConstValue::Int(1)),
                                    Operand::Move(Place::local(6)),
                                ),
                            ),
                            // `_3 = (_5 == i128::MIN)` — the neg-overflow cond.
                            assign(
                                3,
                                Rvalue::BinaryOp(
                                    BinOp::Eq,
                                    Operand::Copy(Place::local(5)),
                                    Operand::Constant(ConstValue::Int(i128::MIN)),
                                ),
                            ),
                        ],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place::local(3)),
                            expected: false,
                            msg: AssertMessage::OverflowNeg,
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: _7 = -_5; _0 = _7; return.
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            assign(
                                7,
                                Rvalue::UnaryOp(
                                    trust_types::UnOp::Neg,
                                    Operand::Copy(Place::local(5)),
                                ),
                            ),
                            assign(0, Rvalue::Use(Operand::Copy(Place::local(7)))),
                        ],
                        terminator: Terminator::Return,
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn hardened_signed_min_neg_is_provable_unsat() {
        let func = signed_min_neg_hardened_fixture();
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_panic_vc(&vcs, "OverflowNeg");

        // BV core: `_5 == bvshl(1, amt) ∧ amt < 127` ∧ `_5 == INT_MIN`. For amt in
        // [0, 126], `_5 = 2^amt < 2^127`, so `_5 != INT_MIN` → violation FALSE →
        // UNSAT → PROVED. Sweep amt past the bound to confirm the BV guard filters it.
        let amt_bv = "__trust_ovf_bv_amt__6";
        let _5_bv = "__trust_ovf_bv_neg__5";
        for amt in 0u128..=200 {
            let _5_val: u128 = if amt >= 128 { 0 } else { 1u128 << amt };
            let env = |name: &str| -> u128 {
                if name == amt_bv {
                    amt
                } else if name == _5_bv {
                    _5_val
                } else {
                    0
                }
            };
            assert!(
                !eval_bv_bool(&vc.formula, &env),
                "hardened `-_5` must be UNSAT (PROVED) for amt={amt} (_5={_5_val}); \
                 formula: {:?}",
                vc.formula
            );
        }
    }

    /// (b3) ADVERSARIAL: an UNGUARDED `-x` (free i128 param) yields a hardened BV neg
    ///      VC that is SAT/refutable — `-(i128::MIN)` (a real neg overflow) must STILL
    ///      be refuted (`x == INT_MIN` is the violation).
    fn unguarded_i128_neg_hardened_fixture() -> VerifiableFunction {
        VerifiableFunction {
            name: "g".to_string(),
            def_path: "test::g".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::i128(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                    LocalDecl { index: 3, ty: Ty::i128(), name: Some("_3".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![assign(
                            2,
                            Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(i128::MIN)),
                            ),
                        )],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place::local(2)),
                            expected: false,
                            msg: AssertMessage::OverflowNeg,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1: _3 = -x; _0 = _3; return.
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            assign(
                                3,
                                Rvalue::UnaryOp(
                                    trust_types::UnOp::Neg,
                                    Operand::Copy(Place::local(1)),
                                ),
                            ),
                            assign(0, Rvalue::Use(Operand::Copy(Place::local(3)))),
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i128(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn hardened_unguarded_i128_neg_stays_refutable() {
        let func = unguarded_i128_neg_hardened_fixture();
        let vcs = generate_hardened_vcs_for_profile(&func);
        let vc = hardened_panic_vc(&vcs, "OverflowNeg");

        let x_bv = "__trust_ovf_bv_neg_x";
        // -(i128::MIN) genuinely overflows; violation `x == INT_MIN` must be SAT.
        let overflow = |name: &str| -> u128 { if name == x_bv { i128::MIN as u128 } else { 0 } };
        assert!(
            eval_bv_bool(&vc.formula, &overflow),
            "REAL hardened i128 neg overflow (-(i128::MIN)) must satisfy the violation \
             (refutable); formula: {:?}",
            vc.formula
        );
        // Any non-MIN value must NOT satisfy it (no false-FAIL).
        for safe in [0i128, i128::MIN + 1, i128::MAX, -1] {
            let safe_env = |name: &str| -> u128 { if name == x_bv { safe as u128 } else { 0 } };
            assert!(
                !eval_bv_bool(&vc.formula, &safe_env),
                "SAFE hardened i128 neg (x = {safe}) must NOT satisfy the violation; \
                 formula: {:?}",
                vc.formula
            );
        }
    }
}
