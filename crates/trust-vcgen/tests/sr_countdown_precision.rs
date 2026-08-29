//! PRECISION guard for the self-referential-definition backstop.
//!
//! `sr_countdown_full[u32;N=10;exact]` is GENUINELY SAFE code. Before the
//! versioning fix, the block definition for `remain /= 10_000` stamped its
//! pre-write READ and its post-write SUBJECT with the SAME token, producing
//! `remain#s3_6 == remain#s3_6 / 10_000` — a recurrence that pins `remain` to 0
//! and vacuously discharges the block. The `entry.rs` fail-closed backstop then
//! degraded every such obligation to `UnsupportedMir`, costing real proofs.
//!
//! The backstop stays. This test pins that it has nothing to catch here.

use trust_types::{VcKind, VerifiableFunction};

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

fn backstopped(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "SelfReferentialDefinition" => {
                Some(format!("{:?}: {detail}", vc.location))
            }
            _ => None,
        })
        .collect()
}

/// Every `Eq(Var(l), rhs)` in `f`, as `(l, rhs free-variable names)`.
fn definitions(f: &trust_types::Formula, out: &mut Vec<(String, Vec<String>)>) {
    if let trust_types::Formula::Eq(l, r) = f
        && let Some(name) = l.var_name()
    {
        out.push((name.to_string(), r.free_variables().iter().map(|v| v.to_string()).collect()));
    }
    for c in f.children() {
        definitions(c, out);
    }
}

fn base(v: &str) -> &str {
    v.split('#').next().unwrap_or(v)
}

/// The load-bearing check: the fix must SPLIT the in-place update into two
/// distinct symbols, not merely delete the fact.
///
/// `remain /= 10_000` has to survive as a real, satisfiable hypothesis relating
/// the POST-write `remain` to a DIFFERENT, PRE-write `remain`. A version of this
/// repair that simply dropped the def would satisfy the "not backstopped" test
/// above while silently costing the hypothesis — so assert the def is present AND
/// that its two sides are different SMT variables.
#[test]
fn sr_countdown_full_u32_splits_the_in_place_update() {
    let func = load("sr_countdown_full_u32");
    let mut split = Vec::new();
    let mut collapsed = Vec::new();
    for vc in trust_vcgen::generate_vcs(&func) {
        let mut defs = Vec::new();
        definitions(&vc.formula, &mut defs);
        for (lhs, rhs_vars) in defs {
            if base(&lhs) != "remain" {
                continue;
            }
            for r in rhs_vars.iter().filter(|r| base(r) == "remain") {
                if *r == lhs {
                    collapsed.push(format!("{lhs} == f({r})"));
                } else {
                    split.push(format!("{lhs} == f({r})"));
                }
            }
        }
    }
    assert!(
        collapsed.is_empty(),
        "the pre- and post-write reads of `remain` still share one symbol: {collapsed:?}"
    );
    assert!(
        !split.is_empty(),
        "the `remain /= 10_000` definition must SURVIVE as a two-symbol fact; \
         finding none means the repair dropped the hypothesis instead of versioning it"
    );
}

#[test]
fn sr_countdown_full_u32_is_not_backstopped() {
    let func = load("sr_countdown_full_u32");
    let all = trust_vcgen::generate_vcs(&func);
    let hits = backstopped(&func);
    assert!(
        hits.is_empty(),
        "{} of {} obligations degraded to UnsupportedMir on SAFE code — the \
         self-referential definition is still being minted:\n  {}",
        hits.len(),
        all.len(),
        hits.join("\n  ")
    );
}

/// The `[u64;N=20;exact]` twin, demoted by the identical `remain /= 10_000` def.
#[test]
fn sr_countdown_full_u64_is_not_backstopped() {
    let func = load("sr_countdown_full_u64");
    let all = trust_vcgen::generate_vcs(&func);
    let hits = backstopped(&func);
    assert!(
        hits.is_empty(),
        "{} of {} obligations degraded to UnsupportedMir on SAFE code:\n  {}",
        hits.len(),
        all.len(),
        hits.join("\n  ")
    );
}

/// Laundering control: the refusal must cost a PROOF, never an OBLIGATION.
/// Dropping the bounds rows entirely would make the test above pass vacuously.
#[test]
fn sr_countdown_full_u32_still_carries_its_bounds_obligations() {
    let func = load("sr_countdown_full_u32");
    let vcs = trust_vcgen::generate_vcs(&func);
    let bounds = vcs
        .iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
        })
        .count();
    let overflow =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).count();
    // 7 bounds + 7 overflow = all 14. Before the fix this read 4 + 4, with the
    // other 6 degraded to `UnsupportedMir`. Pinning the FULL count is what makes
    // this a laundering control: dropping a row would fail here, not pass quietly.
    assert_eq!(
        (bounds, overflow, vcs.len()),
        (7, 7, 14),
        "every obligation must be a REAL one: got {bounds} bounds + {overflow} \
         overflow of {} total",
        vcs.len()
    );
}
