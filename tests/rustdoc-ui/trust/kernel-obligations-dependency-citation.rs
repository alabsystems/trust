// Trust (TG16): TG3's recorded residual, exactly: an island-free crate whose `by`
// clause cites a DEPENDENCY's theorem. Every compilation of this file refuses the
// citation today (cross-crate composition, increment 3, is not wired:
// `clean_extern_proof`), and rustdoc passed it silently because the crate has no
// island. rustdoc now runs the same lane and gives the same verdict. When increment
// 3 lands and rustc accepts this citation, this file flips to check-pass with it.
//
//@ check-fail
//@ compile-flags: -Ztrust-verify=off
//@ aux-build: kernel_obligations_dep_spec.rs
//@ dont-require-annotations: NOTE

extern crate kernel_obligations_dep_spec;

pub fn cites_dependency(x: u64) -> u64
    ensures 0 == 0 by kernel_obligations_dep_spec.dep_zero
    //~^ ERROR cited theorem `kernel_obligations_dep_spec.dep_zero` is not registered in any Clean island or the prelude
{
    x
}
