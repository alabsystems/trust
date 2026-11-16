//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit, for `vanilla_reach_dependency_stays_closed.rs`: a plain data
//! type of a dependency, and an `io::Error` whose custom payload's destructor
//! panics on 7.

/// Plain data, but a dependency's: std code at it is not admitted by reach.
pub struct Plain(pub u32);

/// A custom `io::Error` payload whose destructor panics on 7.
#[derive(Debug)]
pub struct Bomb(pub u32);

impl std::fmt::Display for Bomb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bomb {}", self.0)
    }
}

impl std::error::Error for Bomb {}

impl Drop for Bomb {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("DEP PAYLOAD DROP PANIC (unverified crate)")
        }
    }
}

/// An `io::Error` carrying a `Bomb`.
pub fn bomb_error(x: u32) -> std::io::Error {
    std::io::Error::other(Bomb(x))
}
