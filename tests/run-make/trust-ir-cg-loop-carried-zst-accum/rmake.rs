//! A ZERO-SIZED local that is reassigned inside a loop (the `B = ()` accumulator of
//! core's default `try_fold` / `try_rfold`) compiles, and the loop computes the right
//! answer at -O0 and -O3.
//!
//! Regression pin for the refusal that stopped the stage1 `library/core` build:
//!
//!     loop-carried local _4 (type ()) is mutated inside a loop but is neither
//!     memory-backed nor threaded through a loop-header phi — its in-loop update
//!     would be dropped across the back-edge (failing closed rather than miscompiling)
//!
//! raised for `<char::EscapeDebug as Iterator>::try_fold::<(), ..>` (via
//! `<str::EscapeDebug as Display>::fmt` -> `try_for_each`) and
//! `<slice::Iter<u8> as DoubleEndedIterator>::try_rfold::<(), ..>` (via
//! `iter_compare` over `Rev<Cloned<Iter>>`). When `core` itself is compiled those
//! bodies are LOCAL, so they are lowered for real; in a user crate the same shape
//! arises from any generic fold written like core's, which is what this test uses
//! (a local trait with core's exact default-method bodies).
//!
//! The MIR shape is
//!
//!     bb0: _4 = move _2;                        // accum = init   (_4: ())
//!     bb1: _5 = <I as Iterator>::next(..)       // loop header
//!     ..   _12 = move _4; _11 = (move _12, copy _7); _9 = f(_11)
//!     ..   _4 = copy _14;  goto -> bb1           // accum = f(accum, x)?  (in-loop)
//!
//! A 0-byte value cannot be "dropped" across a back-edge, so the gate admits it;
//! every NON-zero-sized loop-carried local keeps the refusal.
//!
//! The test RUNS the binary: the hazard class of the gate is a silently dropped
//! in-loop update, so it asserts the closure's side effects (digit accumulation in
//! ITERATION ORDER, forward and reverse) and the short-circuit value, not merely
//! that the program linked. Expected values are from the LLVM backend.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "zstaccum.rs",
        r#"
#[derive(PartialEq, Clone, Copy)]
pub struct FmtError;

pub struct Counter { i: u32, n: u32 }

// core's `Iterator::try_fold` / `DoubleEndedIterator::try_rfold` default bodies,
// verbatim in shape. `R` is fixed to a concrete `Try` type (the trait is unstable),
// and to a 1-byte `Result<(), FmtError>` — `<str::EscapeDebug as Display>::fmt`'s
// own residual — because at -O0 a by-value `ControlFlow<C, ()>` / `Result<(), u32>`
// argument and `ControlFlow::from_residual` are separate, still-open gaps
// (`[TCG-ARG-ABI]`) that would fail this test for an unrelated reason.
pub trait MyIter {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
    fn next_back(&mut self) -> Option<Self::Item>;
    #[inline]
    fn try_fold<B, F>(&mut self, init: B, mut f: F) -> Result<B, FmtError>
    where Self: Sized, F: FnMut(B, Self::Item) -> Result<B, FmtError> {
        let mut accum = init;
        while let Some(x) = self.next() { accum = f(accum, x)?; }
        Ok(accum)
    }
    #[inline]
    fn try_rfold<B, F>(&mut self, init: B, mut f: F) -> Result<B, FmtError>
    where Self: Sized, F: FnMut(B, Self::Item) -> Result<B, FmtError> {
        let mut accum = init;
        while let Some(x) = self.next_back() { accum = f(accum, x)?; }
        Ok(accum)
    }
}
impl MyIter for Counter {
    type Item = u32;
    #[inline(never)]
    fn next(&mut self) -> Option<u32> {
        if self.i < self.n { self.i += 1; Some(self.i) } else { None }
    }
    #[inline(never)]
    fn next_back(&mut self) -> Option<u32> {
        if self.i < self.n { self.n -= 1; Some(self.n + 1) } else { None }
    }
}

// The same accumulator with an `Option` residual (a different `?` lowering).
#[inline(never)]
fn carried_opt<I: MyIter, B, F: FnMut(B, I::Item) -> Option<B>>(it: &mut I, init: B, mut f: F) -> Option<B> {
    let mut accum = init;
    while let Some(x) = it.next() { accum = f(accum, x)?; }
    Some(accum)
}

#[inline(never)]
fn write_all(it: &mut Counter, out: &mut u64, fail_at: u32) -> Result<(), FmtError> {
    it.try_fold((), |(), x| {
        if x == fail_at { return Err(FmtError) }
        *out = *out * 10 + x as u64;
        Ok(())
    })
}

#[inline(never)]
fn rwrite(it: &mut Counter, out: &mut u64, stop_at: u32) -> Result<(), FmtError> {
    it.try_rfold((), |(), x| {
        if x == stop_at { return Err(FmtError) }
        *out = *out * 10 + x as u64;
        Ok(())
    })
}

fn main() {
    // Runs to exhaustion: every in-loop call's side effect, in forward order.
    let mut o = 0u64;
    let r = write_all(&mut Counter { i: 0, n: 5 }, &mut o, 99);
    if r != Ok(()) { std::process::exit(1); }
    if o != 12345 { std::process::exit(2); }

    // Short-circuits on the 4th element: the residual must escape the loop.
    let mut o = 0u64;
    let r = write_all(&mut Counter { i: 0, n: 5 }, &mut o, 4);
    if r != Err(FmtError) { std::process::exit(3); }
    if o != 123 { std::process::exit(4); }

    // Reverse twin (`try_rfold`), to exhaustion and short-circuited: the digits
    // must come out in REVERSE iteration order and stop exactly before `2`.
    let mut o = 0u64;
    let r = rwrite(&mut Counter { i: 0, n: 5 }, &mut o, 99);
    if r != Ok(()) { std::process::exit(5); }
    if o != 54321 { std::process::exit(6); }
    let mut o = 0u64;
    let r = rwrite(&mut Counter { i: 0, n: 5 }, &mut o, 2);
    if r != Err(FmtError) { std::process::exit(7); }
    if o != 543 { std::process::exit(8); }

    // `Option` residual.
    let mut s = 0u64;
    let r = carried_opt(&mut Counter { i: 0, n: 10 }, (), |(), x| { s += x as u64; Some(()) });
    if r != Some(()) || s != 55 { std::process::exit(9); }
    let mut s = 0u64;
    let r = carried_opt(&mut Counter { i: 0, n: 10 }, (), |(), x| {
        if x == 7 { return None }
        s += x as u64;
        Some(())
    });
    if r != None || s != 21 { std::process::exit(10); }

    // A NON-zero-sized accumulator through the same generic body: the scalar
    // header-phi path, which must be unaffected.
    let r = carried_opt(&mut Counter { i: 0, n: 10 }, 0u64, |a, x| Some(a * 3 + x as u64));
    if r != Some(44281) { std::process::exit(11); }

    // A literal-only line (no format arguments) so the success signal does not
    // depend on the formatting machinery.
    println!("zst-accumulator loops ok");
}
"#,
    );

    for opt in ["0", "3"] {
        let out = format!("zstaccum_o{opt}");
        rustc()
            .input("zstaccum.rs")
            .crate_type("bin")
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
            // Unwind cleanup of temporaries is a separate lane (`[TCG-EH-DROP-O3]`).
            .arg("-Cpanic=abort")
            .output(&out)
            .run();
        // Every value matched the LLVM control iff the marker prints and the exit
        // status is 0; a non-zero status 1..=11 names the check that failed.
        run(&out).assert_stdout_contains("zst-accumulator loops ok");
    }
}
