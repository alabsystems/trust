//@ aux-build: clean_proof_spec_aux.rs
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **A contract that cites a DEPENDENCY's Clean theorem — still refused, but
//! no longer without options.**
//!
//! Cross-crate proof-position citation is not wired: a citation is resolved
//! against THIS crate's `clean { … }` islands and the Clean prelude, and this
//! fixture pins that it stays that way. What changed is the refusal. It used
//! to be emitted with no note, no help and no option of any kind, which made
//! the commonest cross-crate attempt indistinguishable from a typo.
//!
//! It is also the END-TO-END WITNESS for transport (increment 2). The notes
//! below are rendered from `clean_proof_spec_aux`'s
//! `trust_clean_proof_manifest` and its transported island sources — and that
//! crate is PURE SPEC, so before increment 2 it transported nothing at all and
//! these notes could not have been produced. Every sentence in them is a fact
//! of transport: which crates published islands and how many. Nothing here
//! runs a kernel over a dependency's sources or claims the cited declaration
//! exists in one of them; the composition that would
//! (`trust_certify::clean_island::compose_extern_proof_batch`) has no compiler
//! caller.
//!
//! NOT RUN IN THIS LANE. The build lock was held, so no compiler could be
//! built; the annotations below are the messages this lane wrote, matched by
//! substring, and `dont-check-compiler-stderr` means no `.stderr` file is
//! predicted. Run `./x.py test tests/ui/trust/clean_citation_cross_crate_options.rs`
//! before treating it as green.

extern crate clean_proof_spec_aux;

clean {
    theorem local_only : 0 = 0 := rfl
}

/// The crate-qualified spelling ruling R1 reserves. It is refused, and the
/// refusal says the spelling is the right one and names what is missing.
pub fn clamp(x: u64) -> u64
    ensures 0 == 0 by clean_proof_spec_aux.cap_le_bound
    //~^ ERROR cited theorem `clean_proof_spec_aux.cap_le_bound` is not registered in any Clean island or the prelude
    //~| NOTE these crates loaded into this compilation transported Clean proof material
    //~| NOTE names one of those crates, and
{
    x
}

/// The BARE spelling, whose head names no crate. The dependency list is still
/// reported — a bare name is refused for the same reason, and the author still
/// needs to know what is available — but nothing claims the head is a crate.
pub fn clamp_bare(x: u64) -> u64
    ensures 0 == 0 by cap_le_bound
    //~^ ERROR cited theorem `cap_le_bound` is not registered in any Clean island or the prelude
    //~| NOTE these crates loaded into this compilation transported Clean proof material
{
    x
}

/// The control: this crate's OWN island theorem still resolves, with a
/// dependency carrying proof material present. Composition would be the thing
/// that could break this, and there is none.
pub fn untouched(x: u64) -> u64
    ensures 0 == 0 by local_only
{
    x
}

fn main() {}
