//! A VIRTUAL call whose by-value return lands in a MEMORY-BACKED destination
//! compiles under trust-ir-cg and stores the right value.
//!
//! Regression pin for the refusal `lower_virtual_call_terminator` raised for
//! every such call, measured at BOTH -O0 and -O3:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... virtual call returning a by-value aggregate
//!            into a memory-backed destination is not yet supported
//!
//! for `_2: &str = <dyn Named>::name(..)` and `_0: Result<(), Full> =
//! <dyn Push>::push(..)` — the latter the exact layout of the
//! `_0: fmt::Result = <dyn fmt::Write>::write_str(..)` arm of every
//! `Formatter::write_fmt` (see `trust-ir-cg-formatter-write-fmt`, which this gap
//! blocked). The direct-call lane already stored such a return
//! (`lower_memory_aggregate_call`); the vtable lane now uses the SAME store
//! (`copy_memory_aggregate_call_result`), under guards that refuse by name
//! (`[TCG-VCALL-MEM-DEST]`) what it cannot carry.
//!
//! The values are the point: a lane copied at the wrong offset, a dropped data
//! half, or an `Err` read back as `Ok` all still "run". So every leg compares
//! stdout against the LLVM control, which must equal the literal below.
//!
//! NEGATIVE: a 32-byte return is `PassMode::Indirect` (the caller's buffer). The
//! vtable lane does not lower the hidden return-buffer convention — its selector
//! marker is keyed by callee symbol and a vtable slot has none — so it must refuse
//! by name rather than copy lanes out of registers the callee never wrote. The
//! refusal is `[TCG-SRET-ABI]` (it replaced the lane's earlier
//! `[TCG-VCALL-MEM-DEST]` spelling when the indirect lanes began placing their
//! returns from rustc's own `FnAbi`): an indirect call has no callee symbol to
//! key the hidden-buffer selector marker by, and trust-ir's call and `FuncTy`
//! carry no `sret` fact of their own.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const VCALL: &str = r#"// A VIRTUAL call whose by-value return lands in a MEMORY-BACKED destination.
trait Named { fn name(&self) -> &str; }
struct A;
struct B(&'static str);
impl Named for A { fn name(&self) -> &str { "alpha" } }
impl Named for B { fn name(&self) -> &str { self.0 } }

// `_2: &str = <dyn Named>::name(..)`: a fat pointer (two register lanes).
#[inline(never)]
fn len_of(n: &dyn Named) -> usize { let s = n.name(); s.len() }
// The DATA half must survive too, not only the length.
#[inline(never)]
fn first(n: &dyn Named) -> u8 { n.name().as_bytes()[0] }

// `_0: Result<(), Full> = <dyn Push>::push(..)` with a ZST error: the exact
// layout of `fmt::Result`, without `core::fmt` in the picture.
struct Full;
trait Push { fn push(&mut self, k: u32) -> Result<(), Full>; }
struct Cap { n: u32, cap: u32 }
impl Push for Cap {
    fn push(&mut self, k: u32) -> Result<(), Full> {
        if self.n + k > self.cap { return Err(Full); }
        self.n += k;
        Ok(())
    }
}
#[inline(never)]
fn via(p: &mut dyn Push, k: u32) -> Result<(), Full> { p.push(k) }

fn main() {
    // Stack locals, not `Box<dyn Named>`: a boxed trait object needs
    // `drop_glue::<Box<dyn Named>>`, a separate refused lane that would stop this
    // leg before it reaches the virtual call under test.
    let a = A;
    let b = B("bravo!");
    let lens = len_of(&a) * 10 + len_of(&b);
    let firsts = first(&a) as u32 * 1000 + first(&b) as u32;
    // Heap-held so the `&mut dyn` coercion reborrows real memory.
    let mut c = Box::new(Cap { n: 0, cap: 5 });
    let p1 = via(&mut *c, 3).is_ok();
    let p2 = via(&mut *c, 4).is_ok();
    let p3 = via(&mut *c, 2).is_ok();
    let push = (p1 as u32) * 100 + (p2 as u32) * 10 + (p3 as u32) + c.n * 1000;
    println!("lens {}", lens);
    println!("firsts {}", firsts);
    println!("push {}", push);
}
"#;

const INDIRECT: &str = r#"// NEGATIVE: a 32-byte by-value return (rustc `PassMode::Indirect`)
// through `dyn` into `_0`.
#[derive(Clone, Copy)]
struct Big { a: u64, b: u64, c: u64, d: u64 }
trait Make { fn make(&self, k: u64) -> Big; }
struct M(u64);
impl Make for M { fn make(&self, k: u64) -> Big { Big { a: self.0, b: k, c: self.0 + k, d: 7 } } }
#[inline(never)]
fn via(m: &dyn Make, k: u64) -> Big { m.make(k) }
fn main() {
    let m: Box<dyn Make> = Box::new(M(40));
    let b = via(&*m, 2);
    std::process::exit(if b.a + b.b + b.c + b.d == 91 { 0 } else { 1 });
}
"#;

/// Reviewer-requested pins for the shapes this patch newly sends to the UNCHANGED
/// return-ABI gate rather than to the new store helper: a `(u32, u32)` return
/// (rustc `PassMode::Pair`, two integer registers) and a `(f64, f64)` return (an
/// HFA in two float registers), each landing in an address-taken destination.
/// The post-patch refusal text is not measured, so each leg asserts the only thing
/// that must hold: the LLVM value, or a named `[TCG-` refusal — never a different
/// value.
const PAIR_RETURNS: &str = r#"
trait Two { fn two(&self, k: u32) -> (u32, u32); fn fl(&self, k: f64) -> (f64, f64); }
struct T(u32);
impl Two for T {
    fn two(&self, k: u32) -> (u32, u32) { (self.0 + k, self.0 * k) }
    fn fl(&self, k: f64) -> (f64, f64) { (self.0 as f64 + k, self.0 as f64 * k) }
}
#[inline(never)]
fn pair_via(t: &dyn Two, k: u32) -> u32 {
    let mut r = t.two(k);
    let p = &mut r;
    p.0 = p.0 * 1000 + p.1;
    r.0
}
#[inline(never)]
fn float_via(t: &dyn Two, k: f64) -> f64 {
    let mut r = t.fl(k);
    let p = &mut r;
    p.0 = p.0 * 1000.0 + p.1;
    r.0
}
fn main() {
    let t = T(std::hint::black_box(6));
    // Integers only: `println!` of an `f64` is a separate refused lane that would stop
    // `main` before either virtual call is reached (measured), making both legs vacuous.
    let pair = pair_via(&t, 7);
    let float = float_via(&t, 0.5) as u64;
    println!("pair {}", pair);
    println!("float {}", float);
}
"#;

/// What `vcall` prints (measured under the LLVM backend at -O0 and -O3).
const VCALL_STDOUT: &str = "lens 56\nfirsts 97098\npush 5101\n";

fn main() {
    rfs::write("vcall.rs", VCALL);
    rfs::write("indirect.rs", INDIRECT);
    rfs::write("pairs.rs", PAIR_RETURNS);

    for opt in ["0", "3"] {
        let control = format!("vcall_llvm{opt}");
        rustc()
            .input("vcall.rs")
            .crate_type("bin")
            .crate_name("vcall")
            .output(&control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        let want = run(&control).stdout_utf8();
        assert_eq!(
            want, VCALL_STDOUT,
            "the LLVM control disagrees at -O{opt}; the fixture changed"
        );

        let bin = format!("vcall{opt}");
        rustc()
            .input("vcall.rs")
            .crate_type("bin")
            .crate_name("vcall")
            .output(&bin)
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
            .arg("-Cpanic=abort")
            .run();
        let got = run(&bin).stdout_utf8();
        assert_eq!(
            got, want,
            "trust-ir-cg -O{opt} stored a virtual call's return into its memory-backed \
             destination wrongly"
        );

        let indirect_control = format!("indirect_llvm{opt}");
        rustc()
            .input("indirect.rs")
            .crate_type("bin")
            .crate_name("indirect")
            .output(&indirect_control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        run(&indirect_control);
        rustc()
            .input("indirect.rs")
            .crate_type("bin")
            .crate_name("indirect")
            .output(&format!("indirect{opt}"))
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run_fail()
            .assert_stderr_contains("[TCG-SRET-ABI]")
            .assert_stderr_contains("PassMode::Indirect")
            .assert_stderr_contains("INDIRECT call")
            .assert_stderr_not_contains("is not yet supported");

        let pairs_control = format!("pairs_llvm{opt}");
        rustc()
            .input("pairs.rs")
            .crate_type("bin")
            .crate_name("pairs")
            .output(&pairs_control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        let pairs_want = run(&pairs_control).stdout_utf8();
        let pairs_bin = format!("pairs{opt}");
        let built = rustc()
            .input("pairs.rs")
            .crate_type("bin")
            .crate_name("pairs")
            .output(&pairs_bin)
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run_unchecked();
        if built.status().success() {
            assert_eq!(
                run(&pairs_bin).stdout_utf8(),
                pairs_want,
                "trust-ir-cg -O{opt} compiled a Pair/HFA virtual return into an \
                 address-taken destination to a DIFFERENT value than LLVM"
            );
        } else {
            let stderr = built.stderr_utf8();
            assert!(
                stderr.contains("[TCG-"),
                "a refused Pair/HFA virtual return must carry a named refusal at -O{opt}: {stderr}"
            );
        }
    }
}
