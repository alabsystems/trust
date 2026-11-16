//@ revisions: typo case underscore empty trailing_comma leading_comma second_element
//@[typo] compile-flags: -Ztrust-platform-properties=fd-inherrit
//@[case] compile-flags: -Ztrust-platform-properties=FD-INHERIT
//@[underscore] compile-flags: -Ztrust-platform-properties=fd_inherit
//@[empty] compile-flags: -Ztrust-platform-properties=
//@[trailing_comma] compile-flags: -Ztrust-platform-properties=fd-inherit,
//@[leading_comma] compile-flags: -Ztrust-platform-properties=,fd-inherit
//@[second_element] compile-flags: -Ztrust-platform-properties=fd-inherit,fd-inheritt
//@ check-fail
//! Trust (platform protocols, plan L1a; FC-7): `-Ztrust-platform-properties` takes exact
//! spellings only. A typo, a case or separator variant, an empty value and an empty list element
//! are each a hard error at option parsing, before any code is compiled, so a misspelt policy
//! can never parse as "check nothing" and leave a crate unchecked without saying so.

fn main() {}

//[typo]~? ERROR incorrect value `fd-inherrit` for unstable option `trust-platform-properties`
//[case]~? ERROR incorrect value `FD-INHERIT` for unstable option `trust-platform-properties`
//[underscore]~? ERROR incorrect value `fd_inherit` for unstable option `trust-platform-properties`
//[empty]~? ERROR incorrect value `` for unstable option `trust-platform-properties`
//[trailing_comma]~? ERROR incorrect value `fd-inherit,` for unstable option `trust-platform-properties`
//[leading_comma]~? ERROR incorrect value `,fd-inherit` for unstable option `trust-platform-properties`
//[second_element]~? ERROR incorrect value `fd-inherit,fd-inheritt` for unstable option `trust-platform-properties`
