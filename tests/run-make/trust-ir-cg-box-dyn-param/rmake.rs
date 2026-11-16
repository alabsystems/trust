//! A `Box<dyn Trait>` parameter taken BY VALUE compiles, and both of its lanes
//! survive the boundary.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `panic_unwind::imp::panic(data: Box<dyn Any + Send>)`:
//!
//!     [TCG-REGALLOC-063] ... malformed trust_ir: function
//!     _RNvNtCsk1CSwHtk9gB_12panic_unwind3imp5panic entry parameter 0 has type
//!     Struct([I64, I64]), signature parameter has type Array(I64, 2)
//!
//! An INTERNAL INCONSISTENCY, not a missing feature. A `Box<dyn>` local's slot,
//! and so the entry-block parameter stored into it, is typed by
//! `memory_backed_local_layout`, whose `Box<dyn>` arm answers
//! `fat_ptr_memory_layout()`; the SIGNATURE is typed by
//! `fat_ptr_or_memory_aggregate_layout`, which has no `Box<dyn>` arm and falls
//! through to the generic aggregate walk, i.e. `memory_slot_lane_ty(16, 8)`.
//! `fat_ptr_slot_ty()` hand-spelled the 16-byte slot as `Tuple([I64, I64])`
//! while `memory_slot_lane_ty` had moved to `Array(I64, 2)` — the same type, but
//! not the same `Ty`, and the adapter compares `Ty`s. The fix derives
//! `fat_ptr_slot_ty()` from `memory_slot_lane_ty`, so a two-lane slot has one
//! spelling whichever helper produced it. The same drift refused every
//! `-> Box<dyn Trait>` call destination with "memory aggregate call return type
//! does not match destination slot layout"; `forward(ident(b))` pins that half.
//!
//! This test RUNS the result rather than only compiling it: the hazard class for
//! a two-lane parameter is a TORN pair (a data half whose vtable half was dropped
//! or swapped), and `downcast_ref` consulting the vtable's `TypeId` is what
//! catches one that compiled — through a CUSTOM trait, because `Any::type_id`
//! and `downcast_ref` are separate still-open gaps. `wrap` is `imp::panic`'s exact shape (the parameter
//! moved into a heap struct); the `Exception` is leaked on purpose so nothing
//! here depends on nested `Box` drop glue, which is a separate gap.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "boxdyn.rs",
        r#"
// A CUSTOM trait, not `Any` — `<T as Any>::type_id` returns a 16-byte `TypeId`
// and `downcast_ref` is a virtual call returning an aggregate, both of which are
// separate, still-open gaps that would fail this test for a reason that has
// nothing to do with the by-value boundary under test.
pub trait Tr { fn tag(&self) -> i64; fn payload(&self) -> u64; }
pub struct Val(u64);
impl Tr for Val { fn tag(&self) -> i64 { 7 } fn payload(&self) -> u64 { self.0 } }

pub struct Exception {
    pub class: u64,
    pub canary: *const u8,
    pub cause: Box<dyn Tr + Send>,
}
pub static CANARY: u8 = 0;

// --- the shape that FAILED: a `Box<dyn Trait>` parameter, by value ---
#[inline(never)] pub fn ident(b: Box<dyn Tr + Send>) -> Box<dyn Tr + Send> { b }
#[inline(never)] pub fn forward(b: Box<dyn Tr + Send>) -> Box<dyn Tr + Send> { ident(b) }
// `panic_unwind::imp::panic`'s shape: the parameter is moved into a heap struct.
#[inline(never)] pub fn wrap(data: Box<dyn Tr + Send>) -> *mut Exception {
    Box::into_raw(Box::new(Exception { class: 0x5, canary: &CANARY, cause: data }))
}
// --- the sibling two-lane parameters, which must not regress ---
#[inline(never)] pub fn slice_len(s: &[u8]) -> usize { s.len() }
#[inline(never)] pub fn slice_ident(s: &[u8]) -> &[u8] { s }
#[inline(never)] pub fn dyn_tag(a: &(dyn Tr + Send)) -> i64 { a.tag() }
#[inline(never)] pub fn dyn_payload(a: &(dyn Tr + Send)) -> u64 { a.payload() }

fn main() {
    let b: Box<dyn Tr + Send> = Box::new(Val(42));
    let b = forward(ident(b));
    // Both lanes must survive: `tag()`/`payload()` are dispatched through the
    // VTABLE lane and read the value through the DATA lane — a torn or swapped
    // lane fails one of the two.
    assert_eq!(dyn_tag(&*b), 7);
    assert_eq!(dyn_payload(&*b), 42);
    let e = wrap(b);
    // Leaked on purpose: nothing here depends on nested `Box` drop glue.
    let e: &Exception = unsafe { &*e };
    assert_eq!(e.class, 5);
    assert!(std::ptr::eq(e.canary, &CANARY));
    assert_eq!(dyn_tag(&*e.cause), 7);
    assert_eq!(dyn_payload(&*e.cause), 42);
    let hay: &[u8] = b"hello world";
    assert_eq!(slice_len(hay), 11);
    assert_eq!(slice_ident(hay), b"hello world");
    println!("box-dyn param round trips ok");
}
"#,
    );

    rustc()
        .input("boxdyn.rs")
        .crate_type("bin")
        // -O3 is the level `library/std` is built at and the shape the fix is
        // for. At -O0 `Box::<Exception>::into_raw` takes a different, still-open
        // path ("Place projection"), unrelated to the by-value boundary under test.
        .opt_level("3")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        // The verifier is a separate axis; this test is about codegen alone.
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        // The by-value boundary is the subject; unwind cleanup of temporaries is a
        // separate lane (`[TCG-EH-DROP-O3]`) and is deliberately kept out of scope.
        .arg("-Cpanic=abort")
        .run();

    run("boxdyn").assert_stdout_contains("box-dyn param round trips ok");
}
