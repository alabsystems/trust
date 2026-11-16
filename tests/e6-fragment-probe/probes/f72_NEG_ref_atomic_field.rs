//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: The atomic sibling of f71. `AtomicU32` is an `UnsafeCell<u32>`, so the
//@ probe-note: pointee is not `Freeze` and another THREAD may change `seen` during the
//@ probe-note: call — the exact execution owner ruling R1 declines to model. K2's walk
//@ probe-note: names the offending field path in the diagnostic, which `is_freeze`
//@ probe-note: alone cannot: it answers a bool.
//@ probe-note: Kept separate from f71 because the two reach a real program by different
//@ probe-note: routes (a `Cell` is a single-threaded caching field, an atomic a shared
//@ probe-note: counter), and a fix that reached only one would be invisible without both.
clean { def id32a (x : UInt32) : UInt32 := x }
use std::sync::atomic::AtomicU32;
pub struct Hits { pub n: u32, pub seen: AtomicU32 }
impl Hits {
    pub fn n_of(&self) -> u32
        ensures result == id32a(self.n)
    { self.n }
}
