//@ revisions: report_typo report_bare budget_zero budget_negative budget_float budget_bare facts_empty
//@[report_typo] compile-flags: -Ztrust-platform-report=verbos
//@[report_bare] compile-flags: -Ztrust-platform-report
//@[budget_zero] compile-flags: -Ztrust-platform-budget=0
//@[budget_negative] compile-flags: -Ztrust-platform-budget=-1
//@[budget_float] compile-flags: -Ztrust-platform-budget=1e6
//@[budget_bare] compile-flags: -Ztrust-platform-budget
//@[facts_empty] compile-flags: -Ztrust-platform-dump-facts=
//@ check-fail
//! Trust (platform protocols, plan L1a; FC-7): the remaining `-Ztrust-platform-*` controls refuse
//! every value outside their domain at option parsing. The budget is a positive count of states:
//! `0` would explore nothing, and no value switches the bound off. The facts sink needs a path.

fn main() {}

//[report_typo]~? ERROR incorrect value `verbos` for unstable option `trust-platform-report`
//[report_bare]~? ERROR unstable option `trust-platform-report` requires one of `summary` or `verbose`
//[budget_zero]~? ERROR incorrect value `0` for unstable option `trust-platform-budget`
//[budget_negative]~? ERROR incorrect value `-1` for unstable option `trust-platform-budget`
//[budget_float]~? ERROR incorrect value `1e6` for unstable option `trust-platform-budget`
//[budget_bare]~? ERROR unstable option `trust-platform-budget` requires a positive number of states
//[facts_empty]~? ERROR incorrect value `` for unstable option `trust-platform-dump-facts`
