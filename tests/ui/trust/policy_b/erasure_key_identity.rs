//@ needs-trust-verify
//@ edition: 2021
//@ no-prefer-dynamic
//@ aux-build:panicking_query_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ revisions: refused control
//@[refused] check-fail
//@[control] check-pass
//! Review round 66, two ways the extractor's total-call licences named the wrong code:
//!
//! * a `HashMap`/`HashSet` query through `K: Borrow<Q>` hashes and compares `Q`, which
//!   the licence never checked (`contains_key(q)` with a dependency `Q` whose `Hash`
//!   panics was proved);
//! * the derived-trait check accepted a key when ANY relevant impl was derived, so a
//!   generic `#[derive(Ord)] struct K<T>` vouched for the hand-written `impl Ord for
//!   K<M>` that actually applies.
//!
//! Both now keep their real callee, so `certify` refuses them.
//!
//! Review round 67: the round-66 rule ("every relevant impl derived") refused EVERY
//! derived key, because core's blanket `impl<F: FnPtr> Ord for F` is always relevant;
//! the gates now ask the trait solver for the impl that actually applies. The
//! `control` revision pins that an ordinary derived key is still erased (it fails
//! under the round-66 rule), so the `refused` revision cannot pass vacuously. Round 67
//! also closed two holes a looser fix would have opened: a user `impl Ord for Box<K>`
//! (`Box` is fundamental) and a user `impl Borrow<Q> for K` on a hash lookup.
#![allow(dead_code)]
#[cfg(refused)]
extern crate panicking_query_dep;
#[cfg(refused)]
use panicking_query_dep::{Q, QS};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use std::marker::PhantomData;

#[cfg(refused)]
#[derive(Hash, PartialEq, Eq)]
pub struct Key;

#[cfg(refused)]
impl Borrow<Q> for Key {
    fn borrow(&self) -> &Q {
        &QS
    }
}

#[cfg(refused)]
pub fn looks_up_a_foreign_query(m: &HashMap<Key, u8>, q: &Q) -> bool {
    //[refused]~^ ERROR Trust strict verification failed for `erasure_key_identity::looks_up_a_foreign_query`
    m.contains_key(q)
}

#[cfg(refused)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct G<T>(pub PhantomData<T>, pub u8);

#[cfg(refused)]
#[derive(Clone, Copy)]
pub struct M;

#[cfg(refused)]
impl PartialEq for G<M> {
    fn eq(&self, o: &Self) -> bool {
        self.1 == o.1
    }
}
#[cfg(refused)]
impl Eq for G<M> {}
#[cfg(refused)]
impl PartialOrd for G<M> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
#[cfg(refused)]
impl Ord for G<M> {
    fn cmp(&self, o: &Self) -> Ordering {
        if self.1 == 7 || o.1 == 7 {
            panic!("user cmp")
        }
        self.1.cmp(&o.1)
    }
}

#[cfg(refused)]
pub fn collects_hand_written_keys(v: &[G<M>]) -> BTreeSet<G<M>> {
    //[refused]~^ ERROR Trust strict verification failed for `erasure_key_identity::collects_hand_written_keys`
    v.iter().copied().collect()
}

#[cfg(refused)]
pub struct Bk(pub u32);

#[cfg(refused)]
impl PartialEq for Box<Bk> {
    fn eq(&self, o: &Self) -> bool {
        self.0 == o.0
    }
}
#[cfg(refused)]
impl Eq for Box<Bk> {}
#[cfg(refused)]
impl PartialOrd for Box<Bk> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
#[cfg(refused)]
impl Ord for Box<Bk> {
    fn cmp(&self, o: &Self) -> Ordering {
        if self.0 == 7 || o.0 == 7 {
            panic!("user Box<Bk>::cmp")
        }
        self.0.cmp(&o.0)
    }
}

/// The comparison sentinel asks the same container question as the collect licences.
#[cfg(refused)]
pub fn compares_boxed_hand_written_keys(a: &Box<Bk>, b: &Box<Bk>) -> bool {
    //[refused]~^ ERROR Trust strict verification failed for `erasure_key_identity::compares_boxed_hand_written_keys`
    a < b
}

#[cfg(control)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct D(pub u8);

#[cfg(control)]
pub fn collects_derived_keys(v: &[D]) -> BTreeSet<D> {
    v.iter().copied().collect()
}

/// Review round 68: the `Borrow` check ran on `Q` with references peeled, so
/// `get::<&RefKey>` (which needs the user impl `RefKey: Borrow<&RefKey>`) looked like
/// `Q == K`.
#[cfg(refused)]
#[derive(PartialEq, Eq, Hash)]
pub struct RefKey;

#[cfg(refused)]
pub static RK0: RefKey = RefKey;
#[cfg(refused)]
pub static RKR: &RefKey = &RK0;

#[cfg(refused)]
impl Borrow<&'static RefKey> for RefKey {
    fn borrow(&self) -> &&'static RefKey {
        &RKR
    }
}

#[cfg(refused)]
pub fn looks_up_through_a_reference_borrow(m: &HashMap<RefKey, u32>, q: &&'static RefKey) -> bool {
    //[refused]~^ ERROR Trust strict verification failed for `erasure_key_identity::looks_up_through_a_reference_borrow`
    m.get::<&'static RefKey>(q).is_some()
}
