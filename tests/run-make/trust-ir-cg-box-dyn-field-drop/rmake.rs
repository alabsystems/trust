//! A `Box<S>` whose plain payload owns `Box<dyn Trait>` fields drops correctly:
//! every payload destructor runs exactly once, in declaration order, and the
//! program keeps running afterwards (both heap blocks are freed through the real
//! allocator, so a wrong free would crash here, not pass).
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `panic_unwind`:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... panic_unwind::imp::panic::exception_cleanup
//!            ... TerminatorKind::Drop of Box<imp::Exception> whose payload needs
//!            drop (recursive drop glue not lowered)
//!
//! `Exception { _uwe, canary, cause: Box<dyn Any + Send> }` is boxed by `panic`,
//! handed to the C unwinder, and dropped by `exception_cleanup` through
//! `Box::from_raw`. rustc's glue is three shims deep (`drop_in_place::<Box<S>>`
//! -> `::<S>` -> `::<Box<dyn Trait>>` -> `::<dyn Trait>`, the last a vtable
//! dispatch); the backend lowered none of them. `lower_box_drop_dyn_field_payload`
//! now lowers the whole chain from a single layout-derived plan, calling only the
//! `drop_in_place::<dyn Trait>` shim, which `lower_dyn_place_drop` lowers.
//!
//! The trait here is a custom one rather than `Any` on purpose: `<T as Any>::type_id`
//! (a 16-byte `TypeId` return) is a separate, still-open gap, and pulling it into a
//! vtable would fail this test for a reason that has nothing to do with drop glue.
//!
//! This test RUNS the result rather than only compiling it: the hazard class is a
//! skipped destructor, a double drop, a wrong drop order, a free of a dangling
//! ZST box, or a leak-by-abort on a panicking destructor — none of which a
//! successful compile can show.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, run_fail, rustc};

const FIXTURE: &str = r#"
pub trait Tr { fn tag(&self) -> i64; }

// Single-threaded program: plain statics observe the destructors.
static mut DROPPED_SUM: i64 = 0;
static mut DROP_COUNT: i64 = 0;
// Drop ORDER as a decimal digit string: `ORDER_CODE = ORDER_CODE * 1000 + tag`.
static mut ORDER_CODE: i64 = 0;

fn note(tag: i64) {
    unsafe {
        DROPPED_SUM += tag;
        DROP_COUNT += 1;
        ORDER_CODE = ORDER_CODE * 1000 + tag;
    }
}

// A single-scalar payload with a destructor (vtable drop slot = its Slice-1 glue).
pub struct Payload { pub tag: i64 }
impl Drop for Payload { fn drop(&mut self) { note(self.tag); } }
impl Tr for Payload { fn tag(&self) -> i64 { self.tag } }

// A multi-field payload: the drop slot receives a pointer to an AGGREGATE.
pub struct Wide { pub a: i64, pub b: i64 }
impl Drop for Wide { fn drop(&mut self) { note(self.a * 100 + self.b); } }
impl Tr for Wide { fn tag(&self) -> i64 { self.a } }

// A ZST with NO destructor: its vtable drop slot is NULL and its size word is 0,
// so the virtual drop must be skipped and the (dangling) box must NOT be freed.
pub struct Unit;
impl Tr for Unit { fn tag(&self) -> i64 { -1 } }

// The `panic_unwind::imp::Exception` shape: plain struct, one `Box<dyn>` field.
pub struct Exception { pub canary: usize, pub cause: Box<dyn Tr + Send> }

// Two droppable fields with a no-drop field between them: declaration order.
pub struct Two { pub first: Box<dyn Tr + Send>, pub mid: u32, pub second: Box<dyn Tr + Send> }
// `panic_unwind::imp::Exception`'s exact shape (reviewer improvement): `#[repr(C)]`,
// a 32-byte no-drop leading field like `_Unwind_Exception` (a fn pointer plus two
// words of private data), a `*const u8` canary, and only THEN the `Box<dyn>` —
// so the plan's field offset for `cause` is 40, not 0.
#[repr(C)]
pub struct Uwe { pub class: u64, pub cleanup: Option<extern "C" fn(i32, *mut u8)>, pub private: [*const (); 2] }
#[repr(C)]
pub struct RealException { pub uwe: Uwe, pub canary: *const u8, pub cause: Box<dyn Tr + Send> }
pub static CANARY: u8 = 0;
#[inline(never)]
pub fn make_real(tag: i64) -> Box<RealException> {
    Box::new(RealException {
        uwe: Uwe { class: 0x5245_5354_5445_5354, cleanup: None, private: [core::ptr::null(); 2] },
        canary: &CANARY,
        cause: Box::new(Payload { tag }),
    })
}
#[inline(never)]
pub fn drop_real(b: Box<RealException>) { drop(b); }

#[inline(never)]
pub fn make(tag: i64) -> Box<Exception> {
    Box::new(Exception { canary: 0x5a, cause: Box::new(Payload { tag }) })
}

// `exception_cleanup` verbatim: an `extern "C"` fn that reconstitutes the box
// from a raw pointer and lets it drop (MIR: `drop(_2) -> [.., unwind: terminate(abi)]`).
#[inline(never)]
pub extern "C" fn exception_cleanup(exception: *mut Exception) {
    unsafe {
        let _: Box<Exception> = Box::from_raw(exception);
    }
}

// `Box::into_raw` without the generic call (its body — and a `&mut *b` reborrow —
// carry a place projection the backend does not lower at O0, a separate gap):
// a `Box<T>` IS its pointer, so the transmute is the identity `into_raw` performs.
#[inline(never)]
pub fn into_raw(b: Box<Exception>) -> *mut Exception {
    unsafe { std::mem::transmute::<Box<Exception>, *mut Exception>(b) }
}

// Under `panic=unwind` every `Box::new` is a may-unwind call, and a `Box<dyn>`
// temporary live across one would need a cleanup-pad drop of a `Box<dyn>` LOCAL
// (rustc's `drop_in_place::<Box<dyn Trait>>` glue — a different lane, still
// open). So the two payload boxes are built SIZED first (their cleanup drops are
// the already-lowered Slice-3 lane), then unsized in the aggregate.
#[inline(never)]
pub fn make_two() -> Box<Two> {
    let first = Box::new(Payload { tag: 3 });
    let second = Box::new(Wide { a: 4, b: 2 });
    Box::new(Two { first, mid: 9, second })
}

// The `mem::drop` shape: the dropped box is an entry argument.
#[inline(never)]
pub fn drop_it(b: Box<Exception>) { drop(b); }

#[inline(never)]
pub fn drop_two(t: Box<Two>) { drop(t); }

fn main() {
    // 1. The panic_unwind shape, through the raw-pointer round trip.
    exception_cleanup(into_raw(make(7)));
    assert_eq!(unsafe { DROP_COUNT }, 1);
    assert_eq!(unsafe { DROPPED_SUM }, 7);

    // 2. The same box dropped as an entry argument.
    drop_it(make(11));
    assert_eq!(unsafe { DROP_COUNT }, 2);
    assert_eq!(unsafe { DROPPED_SUM }, 18);

    // 3. Two fields drop in DECLARATION order; the aggregate payload's
    //    destructor sees both of its fields.
    drop_two(make_two());
    assert_eq!(unsafe { DROP_COUNT }, 4);
    assert_eq!(unsafe { DROPPED_SUM }, 18 + 3 + 402);
    assert_eq!(unsafe { ORDER_CODE }, 7_011_003_402);

    // 4. A ZST payload with no destructor: null drop slot, zero-size free skipped.
    //    Surviving this line is the assertion (a free of the dangling box aborts).
    drop_it(Box::new(Exception { canary: 1, cause: Box::new(Unit) }));
    assert_eq!(unsafe { DROP_COUNT }, 4);

    // 5. The allocator is still healthy after every free above: allocate and
    //    drop once more through the same lane.
    exception_cleanup(into_raw(make(1)));
    assert_eq!(unsafe { DROP_COUNT }, 5);
    assert_eq!(unsafe { DROPPED_SUM }, 18 + 3 + 402 + 1);

    // 6. The real panic_unwind layout: the Box<dyn> field at offset 40 behind a
    //    32-byte no-drop `repr(C)` header and a canary.
    let before = unsafe { DROP_COUNT };
    drop_real(make_real(9_000));
    assert_eq!(unsafe { DROP_COUNT }, before + 1);
    assert_eq!(unsafe { DROPPED_SUM }, 18 + 3 + 402 + 1 + 9_000);
    println!("box-dyn-field drops ok");
}
"#;

/// The `panic=unwind` nested cleanup: the FIRST field's destructor panics. rustc's
/// glue then frees that box, still drops the SECOND field, frees the outer box and
/// continues the unwind; `lang_start` catches it and the process exits 101. The
/// second field's destructor printing proves the remaining-field cleanup ran, and
/// the exit code proves the unwind reached the catch rather than aborting.
const PANIC_FIXTURE: &str = r#"
pub trait Tr { fn tag(&self) -> i64; }
// NON-ZST on purpose (reviewer improvement): a ZST payload never allocates, so
// the pad's `vtable size != 0` free branch — the free of the PANICKED field's box
// mid-unwind — would never execute. An `i64` field makes both boxes real.
// Formatting a runtime value inside a `Drop` is a separate lane; record the
// payload through a static instead so the destructor bodies stay plain.
static mut NOTED_V: i64 = 0;
fn note_v(v: i64) { unsafe { NOTED_V += v; } }
pub struct Boom { pub v: i64 }
impl Drop for Boom { fn drop(&mut self) { note_v(self.v); panic!("boom in first"); } }
impl Tr for Boom { fn tag(&self) -> i64 { self.v } }
pub struct Second { pub v: i64 }
impl Drop for Second { fn drop(&mut self) { note_v(self.v); println!("second dropped during unwind"); } }
impl Tr for Second { fn tag(&self) -> i64 { self.v } }
pub struct Two { pub first: Box<dyn Tr + Send>, pub second: Box<dyn Tr + Send> }
#[inline(never)]
pub fn drop_two(t: Box<Two>) { drop(t); }
// Sized boxes first, unsized in the aggregate — see `make_two` in the main fixture.
#[inline(never)]
pub fn make_two() -> Box<Two> {
    let first = Box::new(Boom { v: 40 });
    let second = Box::new(Second { v: 41 });
    Box::new(Two { first, second })
}
fn main() {
    println!("before");
    drop_two(make_two());
    println!("unreachable");
}
"#;

fn main() {
    rfs::write("dropglue.rs", FIXTURE);
    rfs::write("dropglue_panic.rs", PANIC_FIXTURE);

    // Both panic strategies: `abort` takes the plain-call lane, `unwind` the
    // Invoke + synthesized-pad lane (whose NORMAL path this binary exercises).
    for strategy in ["abort", "unwind"] {
        let name = format!("dropglue_{strategy}");
        rustc()
            .edition("2021")
            .input("dropglue.rs")
            .crate_type("bin")
            .crate_name(&name)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg(format!("-Cpanic={strategy}"))
            .run();
        run(&name).assert_stdout_contains("box-dyn-field drops ok");
    }

    // The nested cleanup itself: a panicking first field.
    rustc()
        .edition("2021")
        .input("dropglue_panic.rs")
        .crate_type("bin")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .arg("-Cpanic=unwind")
        .run();
    run_fail("dropglue_panic")
        .assert_exit_code(101)
        .assert_stdout_contains("before")
        .assert_stdout_contains("second dropped during unwind")
        .assert_stdout_not_contains("unreachable");
}
