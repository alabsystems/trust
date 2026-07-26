// Trust: Regression test for rust-lang#99554
// The orphan check should treat projections defined locally as local types.
// When an associated type is defined in the local crate, the local crate
// controls what the projection normalizes to, so it should be treated as local.
//
//@ check-pass
#![allow(private_interfaces)]

trait LocalTrait {
    type Assoc;
}

struct LocalType;

impl LocalTrait for LocalType {
    type Assoc = LocalType;
}

// This should be accepted: <LocalType as LocalTrait>::Assoc is a local projection
// that normalizes to LocalType (a local type). The orphan check should recognize
// this rather than conservatively treating it as foreign.
impl std::fmt::Display for <LocalType as LocalTrait>::Assoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LocalType")
    }
}

fn main() {}
