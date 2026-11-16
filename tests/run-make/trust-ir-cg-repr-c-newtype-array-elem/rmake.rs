//! A `&self` method on an element of a `static` array whose element is a
//! `#[repr(C)]` newtype over a scalar — `AtomicUsize` — compiles, writes THROUGH
//! to the static, and addresses the RIGHT element.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `std_detect`:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... std_detect::detect::cache::do_initialize
//!            (...): Rvalue::Ref source projection is not scalar-bindable
//!
//! raised for `CACHE[0].initialize(..)` on `static CACHE: [Cache; 3]` with
//! `Cache(AtomicUsize)`. The MIR shape is
//!
//!     _4 = const {alloc1: &[Cache; 3]};
//!     _3 = &(*_4)[_5];                      // -O3: &(*_4)[0 of 1]
//!     _2 = Cache::initialize(move _3, ..);  // -O3: &raw const (((*_3).0).0) + atomic_store
//!
//! The by-reference array-element lane refused the ELEMENT type: `AtomicUsize` is
//! `#[repr(C)] struct Atomic<usize> { v: UnsafeCell<Align8<usize>> }`, and rustc
//! keeps a `repr(C)` newtype at `BackendRepr::Memory` (it will not unpack the
//! newtype ABI because "that affects C ABIs"), so `validate_memory_aggregate_
//! field_leaves` — which requires `Scalar` to keep WIDE (`ScalarPair`) leaves out
//! of the memory model — refused a leaf whose bytes are exactly one scalar. The
//! address-taken LOCAL array path already admitted the same element, so
//! `let a = [AtomicUsize::new(0); N]; a[i].store(..)` compiled while
//! `&STATIC[i]` and `&param[i]` did not.
//!
//! The controls are the non-`repr(C)` twins (`Cell<usize>`, a plain newtype),
//! which took the identical address path before the fix and must keep working.
//!
//! This test RUNS the result: the hazard class is a shared-reference write that
//! lands in a SNAPSHOT instead of the static, or in element 0 instead of element
//! i, and only an asserted read-back can see either. It is compiled at both
//! `-Copt-level=0` (the `Index(local)` + out-of-line call shape) and
//! `-Copt-level=3` (the `ConstantIndex` + inlined `&raw const` + `atomic_store`
//! shape `library/std` is actually built at).

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "atomic_elem.rs",
        r#"
use core::cell::Cell;
use core::sync::atomic::{AtomicUsize, Ordering};

// --- the std_detect shape (library/std_detect/src/detect/cache.rs): a
// `static CACHE: [Cache; 3]` whose element is a newtype over `AtomicUsize`,
// initialized through `CACHE[i].initialize(..)` — a `&self` method on an
// element of the static array. ---
pub struct Cache(AtomicUsize);
impl Cache {
    const INITIALIZED_BIT: usize = 1usize << 63;
    const fn uninitialized() -> Self { Cache(AtomicUsize::new(0)) }
    #[inline(never)]
    fn initialize(&self, value: usize) -> usize {
        self.0.store(value | Cache::INITIALIZED_BIT, Ordering::Relaxed);
        value
    }
    #[inline(never)]
    fn raw(&self) -> usize { self.0.load(Ordering::Relaxed) }
}
pub static CACHE: [Cache; 3] =
    [Cache::uninitialized(), Cache::uninitialized(), Cache::uninitialized()];

#[inline(never)]
pub fn do_initialize(v0: usize, v1: usize, v2: usize) {
    CACHE[0].initialize(v0);
    CACHE[1].initialize(v1);
    CACHE[2].initialize(v2);
}
#[inline(never)]
pub fn read_cache(i: usize) -> usize { CACHE[i].raw() }

// --- the same element class through a REFERENCE parameter with a RUNTIME index ---
#[inline(never)]
pub fn set_atomic(a: &[AtomicUsize; 4], i: usize, v: usize) { a[i].store(v, Ordering::Relaxed) }
#[inline(never)]
pub fn get_atomic(a: &[AtomicUsize; 4], i: usize) -> usize { a[i].load(Ordering::Relaxed) }

// --- controls: the non-`repr(C)` twins, which compiled before the fix and take
// the identical address path; they must keep working. ---
#[inline(never)]
pub fn set_cell(a: &[Cell<usize>; 3], i: usize, v: usize) { a[i].set(v) }
#[inline(never)]
pub fn get_cell(a: &[Cell<usize>; 3], i: usize) -> usize { a[i].get() }
pub struct Plain(usize);
impl Plain { #[inline(never)] fn get(&self) -> usize { self.0 } }
pub static PLAIN: [Plain; 3] = [Plain(7), Plain(8), Plain(9)];
#[inline(never)]
pub fn read_plain(i: usize) -> usize { PLAIN[i].get() }

fn main() {
    // The store must go THROUGH to the static (an address, not a snapshot), and
    // it must land in the RIGHT element (element stride 8 — three distinct
    // values, none aliasing element 0).
    assert_eq!(read_cache(0), 0);
    assert_eq!(read_cache(1), 0);
    assert_eq!(read_cache(2), 0);
    do_initialize(0x11, 0x22, 0x33);
    assert_eq!(read_cache(0), 0x11 | (1usize << 63));
    assert_eq!(read_cache(1), 0x22 | (1usize << 63));
    assert_eq!(read_cache(2), 0x33 | (1usize << 63));
    // Read back through the static itself, not through the lane under test.
    assert_eq!(CACHE[1].0.load(Ordering::Relaxed), 0x22 | (1usize << 63));

    let at = [AtomicUsize::new(1), AtomicUsize::new(2), AtomicUsize::new(3), AtomicUsize::new(4)];
    set_atomic(&at, 2, 99);
    assert_eq!(get_atomic(&at, 0), 1);
    assert_eq!(get_atomic(&at, 1), 2);
    assert_eq!(get_atomic(&at, 2), 99);
    assert_eq!(get_atomic(&at, 3), 4);
    assert_eq!(at[2].load(Ordering::Relaxed), 99);
    assert_eq!(at[3].load(Ordering::Relaxed), 4);

    let cells = [Cell::new(5usize), Cell::new(6), Cell::new(7)];
    set_cell(&cells, 1, 60);
    assert_eq!(get_cell(&cells, 0), 5);
    assert_eq!(get_cell(&cells, 1), 60);
    assert_eq!(get_cell(&cells, 2), 7);
    assert_eq!(cells[1].get(), 60);
    assert_eq!(read_plain(0), 7);
    assert_eq!(read_plain(2), 9);

    println!("repr(C) newtype array elements ok");
}
"#,
    );

    // Both the -O0 shape (`Index(local)` + out-of-line `&self` call) and the
    // -O3 shape `library/std` is built at (`ConstantIndex` + inlined
    // `&raw const (((*r).0).0)` + `atomic_store`).
    for (opt, out) in [("0", "atomic_elem_o0"), ("3", "atomic_elem_o3")] {
        rustc()
            .edition("2021")
            .input("atomic_elem.rs")
            .crate_type("bin")
            .output(out)
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .run();

        run(out).assert_stdout_contains("repr(C) newtype array elements ok");
    }
}
