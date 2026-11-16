//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: POSITIVE, MEASURED, and it closes a recorded risk. C2 refuses a pointee
//@ probe-note: with an UNINSTANTIATED type parameter (`has_non_region_param`), but
//@ probe-note: `&Wrapper<u32>` in a non-generic function is fully instantiated and is
//@ probe-note: admitted — so "a generic `T`" is not the refusal, an undecided one is.
//@ probe-note: THE RISK THIS MEASURES. The view re-checks the compiler's
//@ probe-note: `sysroot_authenticated_def_path_str` for the pointee ADT against the name
//@ probe-note: the EXTRACTOR gave it in the IR, and refuses the whole view on a
//@ probe-note: disagreement. The extractor has a second spelling that carries generic args
//@ probe-note: (`..._with_args`), so an instantiated generic was the shape most likely to
//@ probe-note: make the two sides disagree — and a disagreement costs the capability
//@ probe-note: SILENTLY, with no diagnostic anyone would connect to a renaming. They
//@ probe-note: agree: this probe discharges.
//@ probe-note: Like every view row it is `Trusted`/`Constructive`, not `Certified`.
clean { def id32gw (x : UInt32) : UInt32 := x }
pub struct Wrapper<T> { pub v: T }
pub fn get(w: &Wrapper<u32>) -> u32
    ensures result == id32gw(w.v)
{ w.v }
