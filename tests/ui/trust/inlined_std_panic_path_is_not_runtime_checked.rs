// Trust: KNOWN_HAZARDS "under an explicit `-Zinline-mir=yes` (or `-Zmir-opt-level=2`), an
// inlined std panic is a tolerated runtime-checked row". At -O0 each of these calls keeps
// its `Call` terminator and its own call-site row, and the function is refused. An
// explicit MIR inliner removed the call and left the callee's panic in the caller as a
// retained `Assert`, which the default policy tolerated: exit 0, and `f(None)`, `g("é")`,
// `h("ab", 9)`, `i("é", 1)` panic. The `[inlined-panic-path]` row (keyed on the inlined
// scope) restores the refusal under both flags. `ok` (`min`, no panic path) is the control.
// Under both flags `i` is refused first by `inlined_sysroot_panic` (docs/KNOWN_HAZARDS.md, the
// same entry): its inlined `<RangeTo<usize> as SliceIndex<str>>` member keeps an internal
// `Assert` the runtime-checked std-member disposition would tolerate, and that disposition is
// withheld from a body carrying a foreign panic path, with its own error ("Trust full
// verification failed ... a bundled std/core/alloc member's internal Assert was kept as a
// runtime check, and this body carries a foreign panic path the MIR inliner copied into it").
//@ revisions: plain
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP

pub fn f(o: Option<u8>) -> u8 {
    //~^ ERROR Trust strict verification failed for `inlined_std_panic_path_is_not_runtime_checked::f`
    //~| ERROR Trust Level 0 safety verification incomplete for `inlined_std_panic_path_is_not_runtime_checked::f`
    o.unwrap()
}

pub fn g(s: &str) -> usize {
    //~^ ERROR Trust strict verification failed for `inlined_std_panic_path_is_not_runtime_checked::g`
    //~| ERROR Trust Level 0 safety verification incomplete for `inlined_std_panic_path_is_not_runtime_checked::g`
    s.split_at(s.len() / 2).0.len()
}

pub fn h(s: &str, k: usize) -> usize {
    //~^ ERROR Trust strict verification failed for `inlined_std_panic_path_is_not_runtime_checked::h`
    //~| ERROR Trust Level 0 safety verification incomplete for `inlined_std_panic_path_is_not_runtime_checked::h`
    s.split_at(k).0.len()
}

pub fn i(s: &str, k: usize) -> usize {
    //[plain]~^ ERROR Trust strict verification failed for `inlined_std_panic_path_is_not_runtime_checked::i`
    //~^^ ERROR Trust Level 0 safety verification incomplete for `inlined_std_panic_path_is_not_runtime_checked::i`
    s[..k].len()
}

pub fn ok(a: u32, b: u32) -> u32 {
    a.min(b)
}
