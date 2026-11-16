//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! D2 primes (M0(b1) of docs/design/2026-09-29-descriptor-protocols-as-compiler-errors.md).
//! In an `ensures`, a prime on a `&mut` parameter's pointee names its FINAL value
//! (docs/design/2026-07-09-two-language-spec-surface.md §3, D2): `self'.storage.detached`,
//! or `x'` for a scalar `x: &mut T`. Before, every prime was refused ("primed post-state
//! identifier ... has no verified MIR state binding"), so the post-state of aterm's grid
//! wedge could only be written in the unprimed spelling that D2 gives to the ENTRY value.
//!
//! The prime resolves to the canonical place today's lane reads at exit, so it proves and
//! refutes exactly where the unprimed spelling does today. A clause mixing a primed and an
//! unprimed `&mut` pointee read is refused, since both would still read the exit value.
//!
//! Each exit arm publishes its own postcondition row: in `abort_mutant` the early-return
//! arm — taken only when `detached` is already false — proves (kernel-certified), while
//! the fallthrough and whole-function rows still refute, so its counts read
//! `1 proved, 2 failed`; the mutant still does not prove.

pub struct Storage {
    pub detached: bool,
}

pub struct Window {
    pub storage: Storage,
}

impl Window {
    pub fn abort_fixed(&mut self)
    //~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
        ensures !self'.storage.detached
    {
        if !self.storage.detached {
            return;
        }
        self.storage.detached = false;
    }

    pub fn abort_mutant(&mut self)
    //~^ NOTE Trust verification: 1 proved, 2 failed, 0 unknown
        ensures !self'.storage.detached
    {
        if !self.storage.detached {
            return;
        }
        // MUTANT: `self.storage.detached = false;` deleted.
    }
}

pub fn set_one(x: &mut u32)
//~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    ensures x' == 1
{
    *x = 1;
}

pub fn set_one_mutant(x: &mut u32)
//~^ NOTE Trust verification: 0 proved, 2 failed, 0 unknown
    ensures x' == 1
{
    *x = 2;
}

// Refused: mixed epochs. `x' == *x + 1` over `*x += 1` would compare exit with exit.
pub fn bump(x: &mut u32)
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures x' == *x + 1
{
    *x = x.wrapping_add(1);
}
