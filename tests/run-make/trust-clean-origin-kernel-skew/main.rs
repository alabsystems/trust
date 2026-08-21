//! **I7 transport control — the importing side.**
//!
//! Calling `pick` traverses the full import half: the extern `optimized_mir`
//! decode arm (the chokepoint, `rustc_metadata`'s cstore arms) runs
//! `trust_clean_extern_readmission` before serving the body — digest decoded
//! whole, the aux's island sources re-elaborated under THIS compiler's Clean
//! kernel, `readmit` compared every digest field against the locally
//! recomputed facts, and the decoded body re-passed the faithfulness gate.
//!
//! Against the pristine rlib this builds, runs, and prints the projected
//! value. Against the byte-patched rlib the SAME source must refuse at
//! `readmit`'s first comparison — `ReadmissionRefusal::KernelVersionSkew` —
//! and never reach codegen.

extern crate clean_origin_aux;

fn main() {
    let v = clean_origin_aux::m::pick(41, 7);
    println!("picked={v}");
    assert_eq!(
        v, 41,
        "the imported Clean-origin body must be the projection the Clean `def` \
         denotes — 41 is parameter 0"
    );
}
