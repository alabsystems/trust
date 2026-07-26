//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@ run-pass
//@ dont-check-compiler-stderr
//! Ensures parameter names are entry-state values. The body deliberately
//! overwrites the MIR argument local before returning its original value; a
//! postcondition monitor reading the return-time argument would abort.

fn preserve_entry(mut x: u8) -> u8
    ensures result == x
{
    let entry = x;
    x = 0;
    std::hint::black_box(x);
    entry
}

#[test]
fn certified_monitor_uses_entry_snapshot() {
    assert_eq!(preserve_entry(7), 7);
}
