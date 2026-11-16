//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ run-pass
//! Policy B as ruled (2026-07-25; docs/design/2026-07-25-completeness-gap-policy-ruling.md):
//! a completeness gap that keeps rustc's runtime check is REPORTED and the build
//! succeeds. `std::env::args` and `str::parse::<u64>` are absent sysroot callees
//! instantiated at foundational types — their only unproved edge is std's own
//! defined panic, vanilla Rust semantics, exactly the argument that already
//! tolerated `std::io::_print`. Before 2026-09-14 the tolerance exempted
//! `_print`/`_eprint` by name and nothing else, so this program — which builds and
//! runs correctly under advisory — was refused by the default lane.
fn main() {
    let s: u64 = std::env::args()
        .skip(1)
        .filter_map(|a| a.parse::<u64>().ok())
        .fold(0u64, |a, b| a.saturating_add(b));
    println!("{}", s);
}
