//! ADVISORY-REQUIRES-TRANSITIVE-1: `unexposed_requires_bodies`, the rule
//! `entry_requires_charged_only_in_this_crate` applies to the crate's `requires`
//! bodies. Nodes are names; `exposed` lists the members another crate can call (or
//! whose clause nothing charges), `edges` what each body names.

use super::*;

fn unexposed(
    owing: &[&'static str],
    exposed: &[&'static str],
    edges: &[(&'static str, &'static str)],
) -> (Vec<&'static str>, Vec<&'static str>) {
    let mut expanded = Vec::new();
    let set = unexposed_requires_bodies(
        owing,
        |member| exposed.contains(&member),
        |member| {
            expanded.push(member);
            edges.iter().filter(|(from, _)| *from == member).map(|&(_, to)| to).collect()
        },
    );
    let mut answer: Vec<&'static str> =
        owing.iter().copied().filter(|member| set.contains(member)).collect();
    answer.sort_unstable();
    expanded.sort_unstable();
    (answer, expanded)
}

/// The measured shape (`xcmreq_callee.rs`): the `pub` `inc_via` owes `x < 100` and
/// calls the private `bump`, which owes the same. `bump` is exposed through
/// `inc_via`, so nothing is elidable. The rule before this change asked only about
/// `bump` itself and elided its check.
#[test]
fn a_private_callee_of_an_exposed_requires_entry_is_exposed() {
    let (answer, _) = unexposed(&["inc_via", "bump"], &["inc_via"], &[("inc_via", "bump")]);
    assert_eq!(answer, Vec::<&str>::new());
}

/// Exposure follows a chain of `requires` bodies to its end.
#[test]
fn exposure_follows_a_chain_of_requires_bodies() {
    let (answer, _) = unexposed(
        &["entry", "hop", "leaf", "unrelated"],
        &["entry"],
        &[("entry", "hop"), ("hop", "leaf")],
    );
    assert_eq!(answer, vec!["unrelated"]);
}

/// A caller with no `requires` is not a member, so it carries nothing: its charge of
/// the callee's clause holds for every argument. `requires_dep_default_policy.rs`'s
/// `outer`/`inner` control. The non-member is never even expanded.
#[test]
fn a_caller_without_requires_stops_exposure() {
    let (answer, expanded) =
        unexposed(&["entry", "inner"], &["entry"], &[("entry", "outer"), ("outer", "inner")]);
    assert_eq!(answer, vec!["inner"]);
    assert_eq!(expanded, vec!["entry"]);
}

/// A private `requires` body that no exposed body names keeps its elision, and no
/// body is expanded when nothing is exposed (an executable with no extern-indicator
/// `requires` item).
#[test]
fn nothing_exposed_keeps_every_elision() {
    let (answer, expanded) =
        unexposed(&["inner", "helper"], &[], &[("inner", "helper"), ("helper", "inner")]);
    assert_eq!(answer, vec!["helper", "inner"]);
    assert!(expanded.is_empty());
}

/// Recursion, mutual or direct, terminates, and an unexposed cycle stays elidable.
#[test]
fn cycles_terminate() {
    let (answer, expanded) =
        unexposed(&["a", "b", "c"], &["a"], &[("a", "b"), ("b", "a"), ("b", "b"), ("c", "c")]);
    assert_eq!(answer, vec!["c"]);
    assert_eq!(expanded, vec!["a", "b"]);
}

/// An exposed body is never elidable, whatever names it.
#[test]
fn an_exposed_entry_is_never_elidable() {
    let (answer, _) = unexposed(&["p", "q"], &["p"], &[("q", "p")]);
    assert_eq!(answer, vec!["q"]);
}

/// DEFAULT-REQUIRES-OVERRIDE-CHARGE-1: `requires_free_override`, the decision
/// `call_resolves_to_requires_free_override` takes. Items are names; `owing` lists
/// the items that owe their caller a precondition; `resolved` is the item the call
/// runs when it resolves exactly to an `InstanceKind::Item`.
fn skips(named: &'static str, owing: &[&'static str], resolved: Option<&'static str>) -> bool {
    requires_free_override(named, |item| owing.contains(&item), || resolved)
}

/// The measured shape (`ovr.rs`): `c.q(x)` names the default `Tq::q`, which owes
/// `x != 0`, and runs `C`'s override, which owes nothing. The default's clause is
/// not charged.
#[test]
fn a_requires_free_override_skips_the_default_clause() {
    assert!(skips("Tq::q", &["Tq::q"], Some("<C as Tq>::q")));
}

/// `impl Tq for A {}`: the call runs the default body, which assumes its clause.
#[test]
fn a_call_that_runs_the_default_body_keeps_the_charge() {
    assert!(!skips("Tq::q", &["Tq::q"], Some("Tq::q")));
}

/// A generic `T::q`, a `dyn` call (`Virtual`), a shim or a resolution error: the
/// call is not known to run an override, so it keeps the charge.
#[test]
fn an_unresolved_call_keeps_the_charge() {
    assert!(!skips("Tq::q", &["Tq::q"], None));
}

/// An override with a `requires` of its own (refused at the impl): its call keeps
/// the DEFAULT's charge and is not handed the override's clause
/// (ADVISORY-REQUIRES-INSTANCE: no row from an item the call does not name).
#[test]
fn an_override_that_owes_its_own_requires_keeps_the_charge() {
    assert!(!skips("Tq::q", &["Tq::q", "<C as Tq>::q"], Some("<C as Tq>::q")));
}

/// A default that owes nothing has no clause to skip, and the call is not
/// resolved at all: today's path is untouched.
#[test]
fn a_default_that_owes_nothing_is_not_resolved() {
    let mut resolved_asked = false;
    let answer = requires_free_override(
        "Tm::m",
        |_| false,
        || {
            resolved_asked = true;
            Some("<C as Tm>::m")
        },
    );
    assert!(!answer);
    assert!(!resolved_asked);
}
