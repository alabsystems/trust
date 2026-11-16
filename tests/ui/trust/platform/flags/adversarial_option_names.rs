// ignore-tidy-linelength
//@ revisions: singular us_spelling truncated prefix_only capital double_dash trailing_dash
//@ revisions: dumpfacts budgets reports premises env underscore_name split_z
//@[singular] compile-flags: -Ztrust-platform-property=fd-inherit
//@[us_spelling] compile-flags: -Ztrust-platform-unanalyzed=deny
//@[truncated] compile-flags: -Ztrust-platform-propertie=fd-inherit
//@[prefix_only] compile-flags: -Ztrust-platform=fd-inherit
//@[capital] compile-flags: -ZTrust-platform-properties=fd-inherit
//@[double_dash] compile-flags: -Ztrust--platform-properties=fd-inherit
//@[trailing_dash] compile-flags: -Ztrust-platform-properties-=fd-inherit
//@[dumpfacts] compile-flags: -Ztrust-platform-dumpfacts=facts
//@[budgets] compile-flags: -Ztrust-platform-budgets=5
//@[reports] compile-flags: -Ztrust-platform-reports=verbose
//@[premises] compile-flags: -Ztrust-platform-premises=fd-bound
//@[env] compile-flags: -Ztrust-platform-env=program
//@[underscore_name] compile-flags: -Ztrust_platform_properties=lock-release
//@[split_z] compile-flags: -Z trust-platform-properties=lock-release
//@ check-fail
//! Trust (platform protocols, plan L1a; FC-7), adversarial: the OPTION NAME, not only its value.
//! The other tests in this directory misspell values; a misspelt name is the other way a typo
//! could leave a crate unchecked without saying so. Every near miss of the five names (singular,
//! the US spelling `unanalyzed`, a truncation, the bare prefix, a capital, a doubled or trailing
//! separator, a near miss of each other control) is an unknown option and a hard error. So are
//! the two controls the design table names but this trustc does not have (`premises`, plan L3.E,
//! and `env`): asking for them is refused, never accepted inertly.
//!
//! rustc's own name normalization (`_` for `-`) and the split `-Z name=value` form reach the same
//! parser, so neither is a way around the value check: `lock-release` is refused through both.

fn main() {}

//[singular]~? ERROR unknown unstable option: `trust-platform-property`
//[us_spelling]~? ERROR unknown unstable option: `trust-platform-unanalyzed`
//[truncated]~? ERROR unknown unstable option: `trust-platform-propertie`
//[prefix_only]~? ERROR unknown unstable option: `trust-platform`
//[capital]~? ERROR unknown unstable option: `Trust-platform-properties`
//[double_dash]~? ERROR unknown unstable option: `trust--platform-properties`
//[trailing_dash]~? ERROR unknown unstable option: `trust-platform-properties-`
//[dumpfacts]~? ERROR unknown unstable option: `trust-platform-dumpfacts`
//[budgets]~? ERROR unknown unstable option: `trust-platform-budgets`
//[reports]~? ERROR unknown unstable option: `trust-platform-reports`
//[premises]~? ERROR unknown unstable option: `trust-platform-premises`
//[env]~? ERROR unknown unstable option: `trust-platform-env`
//[underscore_name]~? ERROR incorrect value `lock-release` for unstable option `trust_platform_properties`
//[split_z]~? ERROR incorrect value `lock-release` for unstable option `trust-platform-properties`
