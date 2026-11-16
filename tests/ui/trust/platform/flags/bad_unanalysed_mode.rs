//@ revisions: allow typo upper empty list bare
//@[allow] compile-flags: -Ztrust-platform-unanalysed=allow
//@[typo] compile-flags: -Ztrust-platform-unanalysed=denny
//@[upper] compile-flags: -Ztrust-platform-unanalysed=DENY
//@[empty] compile-flags: -Ztrust-platform-unanalysed=
//@[list] compile-flags: -Ztrust-platform-unanalysed=warn,deny
//@[bare] compile-flags: -Ztrust-platform-unanalysed
//@ check-fail
//! Trust (platform protocols, plan L1a; FC-7): `-Ztrust-platform-unanalysed` is `warn` or `deny`
//! and nothing else. In particular there is no `allow`: a site the pass cannot analyse is always
//! named (FC-1), and a misspelt `deny` must not degrade to the default `warn` in silence.

fn main() {}

//[allow]~? ERROR incorrect value `allow` for unstable option `trust-platform-unanalysed`
//[typo]~? ERROR incorrect value `denny` for unstable option `trust-platform-unanalysed`
//[upper]~? ERROR incorrect value `DENY` for unstable option `trust-platform-unanalysed`
//[empty]~? ERROR incorrect value `` for unstable option `trust-platform-unanalysed`
//[list]~? ERROR incorrect value `warn,deny` for unstable option `trust-platform-unanalysed`
//[bare]~? ERROR unstable option `trust-platform-unanalysed` requires one of `warn` or `deny`
