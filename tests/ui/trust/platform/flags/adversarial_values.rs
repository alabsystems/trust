// ignore-tidy-linelength
//@ revisions: unicode_hyphen nonbreaking_hyphen minus_sign soft_hyphen zero_width_space negated_bang
//@ revisions: negated_dash negated_no assigned_off glob unsupported_upper unsupported_underscore
//@ revisions: good_then_unsupported unsupported_then_good deny_then_allow deny_then_off budget_then_zero budget_hex
//@ revisions: budget_unbounded report_then_bad
//@[unicode_hyphen] compile-flags: -Ztrust-platform-properties=fd‐inherit
//@[nonbreaking_hyphen] compile-flags: -Ztrust-platform-properties=fd‑inherit
//@[minus_sign] compile-flags: -Ztrust-platform-properties=fd−inherit
//@[soft_hyphen] compile-flags: -Ztrust-platform-properties=fd-­inherit
//@[zero_width_space] compile-flags: -Ztrust-platform-properties=fd-inherit​
//@[negated_bang] compile-flags: -Ztrust-platform-properties=!fd-inherit
//@[negated_dash] compile-flags: -Ztrust-platform-properties=-fd-inherit
//@[negated_no] compile-flags: -Ztrust-platform-properties=no-fd-inherit
//@[assigned_off] compile-flags: -Ztrust-platform-properties=fd-inherit=off
//@[glob] compile-flags: -Ztrust-platform-properties=fd-*
//@[unsupported_upper] compile-flags: -Ztrust-platform-properties=LOCK-RELEASE
//@[unsupported_underscore] compile-flags: -Ztrust-platform-properties=lock_release
//@[good_then_unsupported] compile-flags: -Ztrust-platform-properties=fd-inherit -Ztrust-platform-properties=fd-identity
//@[unsupported_then_good] compile-flags: -Ztrust-platform-properties=lock-release -Ztrust-platform-properties=fd-inherit
//@[deny_then_allow] compile-flags: -Ztrust-platform-unanalysed=deny -Ztrust-platform-unanalysed=allow
//@[deny_then_off] compile-flags: -Ztrust-platform-unanalysed=deny -Ztrust-platform-unanalysed=off
//@[budget_then_zero] compile-flags: -Ztrust-platform-budget=5 -Ztrust-platform-budget=0
//@[budget_hex] compile-flags: -Ztrust-platform-budget=0x10
//@[budget_unbounded] compile-flags: -Ztrust-platform-budget=unbounded
//@[report_then_bad] compile-flags: -Ztrust-platform-report=verbose -Ztrust-platform-report=quiet
//@ check-fail
//! Trust (platform protocols, plan L1a; FC-7), adversarial: values the other tests here do not
//! try. Spellings that LOOK like `fd-inherit` (U+2010 hyphen, U+2011 non-breaking hyphen, U+2212
//! minus, a soft hyphen, a trailing zero-width space), spellings that read as switching a property
//! OFF (`!`, `-`, `no-`, `=off`), a glob, and case or separator variants of the two properties
//! this trustc refuses. None may parse as `fd-inherit`, as "check nothing" or as a property
//! accepted inertly: each is a hard error.
//!
//! Repeating an option never launders a bad value: a refused value is an error whether it comes
//! before or after an accepted one, so a later spelling can neither relax `deny` (`allow`, `off`)
//! nor switch the budget off (`0`, `unbounded`) nor slip an unsupported property in beside a
//! supported one.

fn main() {}

//[unicode_hyphen]~? ERROR incorrect value `fd‐inherit` for unstable option `trust-platform-properties`
//[nonbreaking_hyphen]~? ERROR incorrect value `fd‑inherit` for unstable option `trust-platform-properties`
//[minus_sign]~? ERROR incorrect value `fd−inherit` for unstable option `trust-platform-properties`
//[soft_hyphen]~? ERROR incorrect value `fd-­inherit` for unstable option `trust-platform-properties`
//[zero_width_space]~? ERROR incorrect value `fd-inherit​` for unstable option `trust-platform-properties`
//[negated_bang]~? ERROR incorrect value `!fd-inherit` for unstable option `trust-platform-properties`
//[negated_dash]~? ERROR incorrect value `-fd-inherit` for unstable option `trust-platform-properties`
//[negated_no]~? ERROR incorrect value `no-fd-inherit` for unstable option `trust-platform-properties`
//[assigned_off]~? ERROR incorrect value `fd-inherit=off` for unstable option `trust-platform-properties`
//[glob]~? ERROR incorrect value `fd-*` for unstable option `trust-platform-properties`
//[unsupported_upper]~? ERROR incorrect value `LOCK-RELEASE` for unstable option `trust-platform-properties`
//[unsupported_underscore]~? ERROR incorrect value `lock_release` for unstable option `trust-platform-properties`
//[good_then_unsupported]~? ERROR incorrect value `fd-identity` for unstable option `trust-platform-properties`
//[unsupported_then_good]~? ERROR incorrect value `lock-release` for unstable option `trust-platform-properties`
//[deny_then_allow]~? ERROR incorrect value `allow` for unstable option `trust-platform-unanalysed`
//[deny_then_off]~? ERROR incorrect value `off` for unstable option `trust-platform-unanalysed`
//[budget_then_zero]~? ERROR incorrect value `0` for unstable option `trust-platform-budget`
//[budget_hex]~? ERROR incorrect value `0x10` for unstable option `trust-platform-budget`
//[budget_unbounded]~? ERROR incorrect value `unbounded` for unstable option `trust-platform-budget`
//[report_then_bad]~? ERROR incorrect value `quiet` for unstable option `trust-platform-report`
