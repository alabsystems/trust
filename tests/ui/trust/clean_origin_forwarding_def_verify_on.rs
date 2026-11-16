//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=on
//@ dont-check-compiler-stderr
//! **An island `def` whose body calls another island `def` builds with
//! verification ON (Trust, 2026-09-28).**
//!
//! `def viaId x := idA x` plans through the planner's helper expansion as a
//! projection, and `def incAlias x := inc x` as a wrapping add. Both are
//! carrier-gate targets, and a target must carry a kernel-TV companion. The TV
//! source side read the declaration as written, refused the `idA` head, and the
//! build died on "fatal clean-origin evidence disagreement … the expected
//! kernel-TV companion is missing". That happened to every `-Ztrust-verify=on`
//! build of such a crate, whether or not anything called the `def`. With
//! verification off it built and ran. The TV source side now reads a
//! declaration outside its fragment through the same expansion the planner
//! used. The carrier gate still checks the ORIGINAL declaration.

clean {
    def idA (x : UInt64) : UInt64 := x
    def viaId (x : UInt64) : UInt64 := idA x
    def inc (x : UInt64) : UInt64 := x + 1
    def incAlias (x : UInt64) : UInt64 := inc x
}

fn main() {
    let v = viaId(41);
    let w = incAlias(41);
    if v != 41 || w != 42 {
        std::process::abort();
    }
}
