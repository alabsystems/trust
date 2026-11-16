//@ revisions: lock_release fd_identity beside_fd_inherit verify_on
//@[lock_release] compile-flags: -Ztrust-platform-properties=lock-release
//@[fd_identity] compile-flags: -Ztrust-platform-properties=fd-identity
//@[beside_fd_inherit] compile-flags: -Ztrust-platform-properties=fd-inherit,lock-release
//@[verify_on] compile-flags: -Ztrust-verify=on -Ztrust-platform-properties=lock-release
//@ check-fail
//! Trust (platform protocols, plan L1a; FC-7): `lock-release` and `fd-identity` are properties
//! the design defines but this trustc cannot check (their census lands in plan L4a-L4c). Asking
//! for one is a hard error naming it "not supported by this trustc", never a flag that is
//! accepted and checks nothing. Beside a supported property the whole value is refused, so a
//! policy cannot quietly run with less than it names; and the refusal does not depend on whether
//! verification is on (it happens at option parsing).

fn main() {}

//[lock_release]~? ERROR incorrect value `lock-release` for unstable option `trust-platform-properties`
//[fd_identity]~? ERROR incorrect value `fd-identity` for unstable option `trust-platform-properties`
//[beside_fd_inherit]~? ERROR incorrect value `fd-inherit,lock-release` for unstable option `trust-platform-properties`
//[verify_on]~? ERROR incorrect value `lock-release` for unstable option `trust-platform-properties`
