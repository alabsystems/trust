//@ compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-certified-test-monitors -Ztrust-targo-test-monitor -Ztrust-verify-session=linked-monitor-ui -Ztrust-verify-package-name=certified_monitor_linked_on -Ztrust-verify-crate-role=dependency
//@ no-prefer-dynamic
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=linked-monitor-ui

pub fn guarded(x: u64) -> u64
    requires x == 0
{
    x
}
