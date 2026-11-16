//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "rlib"]

// A pure spec crate: one island, one theorem, nothing minted. The consumer,
// kernel-obligations-dependency-citation.rs, cites it from a crate with no island.

clean {
    theorem dep_zero : 0 = 0 := rfl
}
