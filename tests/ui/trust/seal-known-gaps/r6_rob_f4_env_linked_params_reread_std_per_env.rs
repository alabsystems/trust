//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6RobF4.cell` holds
//@ regex-error-pattern: \(\d+ body\(ies\), \d{5,} instance\(s\) read\)
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F4, a true program refused at a size; lens:
//! robustness). Recorded, not fixed (docs/DECISION_QUEUE.md, "sealed types
//! land with review 6's findings recorded, not fixed").
//! A SMALL INSTANCE: the seal below holds, but its walk reads tens of
//! thousands of instances (56,044 on the review-6 build, where the review-5
//! build read 1,244 for this file), because std's code beneath each fn is
//! read again for every typing environment. At 1,500 such fns a TRUE program
//! is refused at the instance bound ("the crate makes more than 2000000
//! instances of its generic code", 34-37 s; 8 s without the seal; the review-5
//! build holds it in 12-13 s, 46,504 instances). The file passes while the
//! count it prints has five digits or more; the day it falls below 10,000,
//! the file fails: that is the win. Move the program to a must-hold fixture
//! (the 1,500-fn form, if it is cheap enough) and delete this file.
//! The shape: round 6's rule 3 counts a bare type parameter as local in an
//! open reading where `env_mask(scope) != 0`, and an alias of a local trait's
//! item as local always; so every std fn a generic fn calls at its bare
//! parameters is followed, with everything beneath it (HashMap, BTreeMap,
//! sort_by, collect, format!), once per typing environment. `tied!`: an
//! UNUSED `F: FnMut(&mut App)` bound (with `F: FnMut(&mut u8)` the count is
//! the review-5 one); `assoc!`: no `App` at all, fns generic over a local
//! trait's associated types (`P::K`, `P::V`). Each fn has a trait bound of its
//! own, so each has its own typing environment.
//! Root, as its skeptic put it: sealed.rs `names_local_in` ends with `local ||
//! (parameter && open.is_some_and(|scope| self.env_mask(scope) != 0))` and
//! counts a `ty::Alias` as local when `alias_def(alias.kind).is_local()`
//! (replacing round 5's `ty::Alias(..) | ty::Param(_) => !open`); `env_mask`
//! sets a bit for any caller bound that names `App`.

#![allow(unused)]
pub(crate) struct Cell { n: u32 }
impl Cell {
    pub(crate) fn new() -> Self { Cell { n: 0 } }
    pub(crate) fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App {
    pub fn new() -> Self { App { cell: Cell::new() } }
    pub fn tick(&mut self) { self.cell.bump() }
}
use std::collections::{HashMap, BTreeMap, VecDeque, HashSet, BTreeSet, BinaryHeap};
use std::fmt::Debug;
use std::hash::Hash;
macro_rules! tied {
    ($f:ident, $t:ident) => {
        pub trait $t {}
        pub fn $f<K: Hash + Eq + Ord + Clone + Debug + $t, V: Clone + Debug, F: FnMut(&mut App)>(
            m: &mut HashMap<K, V>, b: &mut BTreeMap<K, V>, q: &mut VecDeque<K>, v: &mut Vec<K>, k: K, x: V, f: F,
        ) -> String {
            m.insert(k.clone(), x.clone());
            m.entry(k.clone()).or_insert(x.clone());
            m.retain(|a, _| a != &k);
            b.insert(k.clone(), x.clone());
            b.remove(&k);
            for (a, c) in b.range(k.clone()..) { let _ = (a, c); }
            q.push_back(k.clone());
            q.make_contiguous().sort();
            v.push(k.clone());
            v.sort_by(|a, c| c.cmp(a));
            v.dedup();
            let _ = v.binary_search(&k);
            let hs: HashSet<K> = v.iter().cloned().collect();
            let bs: BTreeSet<K> = hs.into_iter().collect();
            let mut h: BinaryHeap<K> = bs.into_iter().collect();
            h.pop();
            format!("{:?} {:?} {:?}", k, x, v)
        }
    };
}
pub trait Key { type K: Hash + Eq + Ord + Clone + Debug; type V: Clone + Debug; }
macro_rules! assoc {
    ($f:ident, $t:ident) => {
        pub trait $t {}
        pub fn $f<P: Key + $t>(
            m: &mut HashMap<P::K, P::V>, b: &mut BTreeMap<P::K, P::V>, q: &mut VecDeque<P::K>, v: &mut Vec<P::K>, k: P::K, x: P::V,
        ) -> String {
            m.insert(k.clone(), x.clone());
            m.entry(k.clone()).or_insert(x.clone());
            m.retain(|a, _| a != &k);
            b.insert(k.clone(), x.clone());
            b.remove(&k);
            for (a, c) in b.range(k.clone()..) { let _ = (a, c); }
            q.push_back(k.clone());
            q.make_contiguous().sort();
            v.push(k.clone());
            v.sort_by(|a, c| c.cmp(a));
            v.dedup();
            let _ = v.binary_search(&k);
            let hs: HashSet<P::K> = v.iter().cloned().collect();
            let bs: BTreeSet<P::K> = hs.into_iter().collect();
            let mut h: BinaryHeap<P::K> = bs.into_iter().collect();
            h.pop();
            format!("{:?} {:?} {:?}", k, x, v)
        }
    };
}
tied!(a1, A1);
tied!(a2, A2);
tied!(a3, A3);
tied!(a4, A4);
tied!(a5, A5);
tied!(a6, A6);
tied!(a7, A7);
tied!(a8, A8);
tied!(a9, A9);
tied!(a10, A10);
tied!(a11, A11);
tied!(a12, A12);
tied!(a13, A13);
tied!(a14, A14);
tied!(a15, A15);
tied!(a16, A16);
tied!(a17, A17);
tied!(a18, A18);
tied!(a19, A19);
tied!(a20, A20);
assoc!(b1, B1);
assoc!(b2, B2);
assoc!(b3, B3);
assoc!(b4, B4);
assoc!(b5, B5);
assoc!(b6, B6);
assoc!(b7, B7);
assoc!(b8, B8);
assoc!(b9, B9);
assoc!(b10, B10);
assoc!(b11, B11);
assoc!(b12, B12);
assoc!(b13, B13);
assoc!(b14, B14);
assoc!(b15, B15);
assoc!(b16, B16);
assoc!(b17, B17);
assoc!(b18, B18);
assoc!(b19, B19);
assoc!(b20, B20);

clean {
    import Trust.Binding
    namespace R6RobF4
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF4
}
