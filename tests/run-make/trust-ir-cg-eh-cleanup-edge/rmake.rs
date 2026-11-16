//! An unwind CLEANUP landing pad runs the frame's Drops at -O0 AND at -O3, and a
//! call lane that cannot carry the unwind edge refuses instead of skipping them.
//!
//! Regression pin for `[TCG-EH-DROP-O3]`, which failed closed on EVERY needs-drop
//! local dropped on a cleanup pad whenever `-C opt-level` was not 0 under
//! `panic=unwind` -- and so on every such `library/std` body, because std is built
//! at -O3 with panic=unwind (checkpoint A: `<String as Add<&str>>::add`,
//! `RawVec::into_box`, `io::error::Repr::new_simple` / `new_custom`,
//! `<vec::Drain as Drop>::drop`, `<[T; N]>::try_map`, `<trust_bignum::Nat as
//! Display>::fmt`). The gate named four O3 classes from a 2026-07-14 fuzz. Measured
//! again with the gate out of the way (the backend's O3 pass schedule over MIR
//! byte-identical to -Copt-level=3's): the double-drop and both stale-read classes
//! match LLVM; the missing-drop class is a call LANE that emits a plain call for a
//! call with a live cleanup edge (the closure-body lane; by-value aggregate / pair /
//! Option returns), and it miscompiled at -O0 too, where the gate never applied.
//!
//! Each panicking case prints, from its Drops, exactly what the LLVM backend prints
//! (the expected strings below are LLVM's output at -O0 and -O3), then exits 101.
//! A Drop that did not run on the pad is a missing byte; a stale store is a wrong
//! byte; a double drop is an extra byte. `closure` / `closure_mut` are the lane
//! fix (`#[inline(never)]` keeps the closure call out of the MIR inliner at -O3).
//! `aggregate_return` is the by-value aggregate return lane. Until the Trust train that
//! pins trust-cg `7ace0c56` (T8, 2026-10-07) it had no normal-edge continuation and
//! REFUSED with `[TCG-EH-CALL-EDGE]` rather than build a binary that loses `d`'s Drop;
//! trust-cg now compiles it, so it is held to LLVM's output like every other case, on
//! the unwinding path (`d`'s Drop on the pad) and on the normal path.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, run_fail, rustc};

const PRELUDE: &str = r##"#![allow(unused)]
#![feature(stmt_expr_attributes)]
extern "C" { fn write(fd: i32, buf: *const u8, n: usize) -> isize; }
// Raw write(2): no std buffering, so a byte printed by a Drop that runs during
// unwinding is on stdout even though the process then exits 101.
#[inline(never)] fn out(b: u8) { let x = [b, 10u8]; unsafe { write(1, x.as_ptr(), 2); } }
pub struct D { pub a: u8, pub b: u8 }
impl Drop for D { fn drop(&mut self) { out(self.a); } }
#[inline(never)] fn boom(x: u8) { if std::hint::black_box(x) != 0 { panic!("boom") } }
#[inline(never)] fn keep(d: &D) -> u8 { d.b }
"##;

/// (case, body, stdout the LLVM backend produces, whether the case panics)
const CASES: &[(&str, &str, &str, bool)] = &[
    (r##"moved"##, r##"fn c(p: u8) { let g = D { a: 49, b: 0 }; let _k = g; boom(p); }
fn main() { c(1); out(69); }"##, r##"1
"##, true),
    (r##"store"##, r##"fn c(p: u8) { let mut d = D { a: 97, b: 0 }; d.a = 98; boom(p); keep(&d); }
fn main() { c(1); out(69); }"##, r##"b
"##, true),
    (r##"box_store"##, r##"fn c(p: u8) { let mut b = Box::new(D { a: 17, b: 0 }); b.a = 51; boom(p); keep(&b); }
fn main() { c(1); out(69); }"##, r##"3
"##, true),
    (r##"loop_store"##, r##"fn c(p: u8) { let mut d = D { a: 48, b: 0 }; let mut i = 0u8; while i < 3 { d.a = 48 + i; boom(if i == 2 { p } else { 0 }); i += 1; } keep(&d); }
fn main() { c(1); out(69); }"##, r##"2
"##, true),
    (r##"store_between"##, r##"fn c(p: u8) { let mut d = D { a: 49, b: 0 }; let mut i = 0u8; loop { d.a += 1; if i == 2 { boom(p); break; } boom(0); i += 1; } keep(&d); }
fn main() { c(1); out(69); }"##, r##"4
"##, true),
    (r##"order"##, r##"fn c(p: u8) { let x = D { a: 120, b: 0 }; let y = D { a: 121, b: 0 }; boom(p); keep(&x); keep(&y); }
fn main() { c(1); out(69); }"##, r##"y
x
"##, true),
    (r##"two_frames"##, r##"#[inline(never)] fn inner(p: u8) { let e = D { a: 105, b: 0 }; boom(p); keep(&e); }
fn c(p: u8) { let d = D { a: 111, b: 0 }; inner(p); keep(&d); }
fn main() { c(1); out(69); }"##, r##"i
o
"##, true),
    (r##"guard"##, r##"struct G<'a>(&'a mut u8);
impl Drop for G<'_> { fn drop(&mut self) { out(*self.0); } }
fn c(p: u8) { let mut v = 97u8; let g = G(&mut v); *g.0 = 98; boom(p); *g.0 = 99; }
fn main() { c(1); out(69); }"##, r##"b
"##, true),
    (r##"closure"##, r##"fn c(p: u8) { let d = D { a: 71, b: 0 }; let f = #[inline(never)] || boom(p); f(); keep(&d); }
fn main() { c(1); out(69); }"##, r##"G
"##, true),
    (r##"closure_mut"##, r##"fn c(p: u8) { let d = D { a: 72, b: 0 }; let mut n = 0u8; let mut f = #[inline(never)] |q: u8| { n += 1; boom(q); }; f(p); out(48 + n); keep(&d); }
fn main() { c(1); out(69); }"##, r##"H
"##, true),
    (r##"normal_path"##, r##"fn store(p: u8) { let mut d = D { a: 97, b: 0 }; d.a = 98; boom(p); keep(&d); }
fn order(p: u8) { let x = D { a: 120, b: 0 }; let y = D { a: 121, b: 0 }; boom(p); keep(&x); keep(&y); }
#[inline(never)] fn inner(p: u8) { let e = D { a: 105, b: 0 }; boom(p); keep(&e); }
fn two_frames(p: u8) { let d = D { a: 111, b: 0 }; inner(p); keep(&d); }
struct G<'a>(&'a mut u8);
impl Drop for G<'_> { fn drop(&mut self) { out(*self.0); } }
fn guard(p: u8) { let mut v = 97u8; let g = G(&mut v); *g.0 = 98; boom(p); *g.0 = 99; }
fn closure_scalar(p: u8) -> u8 { let d = D { a: 72, b: 0 }; let f = #[inline(never)] |q: u8| -> u8 { boom(q); q + 7 }; let r = f(p); keep(&d); r }
fn main() { store(0); order(0); two_frames(0); guard(0); out(48 + closure_scalar(0)); out(69); }"##, r##"b
y
x
i
o
c
H
7
E
"##, false),
];

const AGGREGATE_RETURN: &str = r##"#[derive(Clone, Copy)] pub struct Big { x: u64, y: u64, z: u64 }
#[inline(never)] fn big(p: u8) -> Big { boom(p); Big { x: 1, y: 2, z: 3 } }
fn c(p: u8) { let d = D { a: 65, b: 0 }; let g = big(p); out(48 + g.z as u8); keep(&d); }"##;
/// (path, main, stdout the LLVM backend produces, whether it panics) for `AGGREGATE_RETURN`.
const AGGREGATE_RETURN_MAINS: &[(&str, &str, &str, bool)] = &[
    ("unwind", "fn main() { c(1); out(69); }", "A\n", true),
    ("normal", "fn main() { c(0); out(69); }", "3\nA\nE\n", false),
];

fn compile(file: &str, name: &str, opt: &str) -> run_make_support::Rustc {
    let mut cmd = rustc();
    cmd.input(file)
        .crate_type("bin")
        .crate_name(name)
        .opt_level(opt)
        .arg("-Zcodegen-backend=trust-ir-cg")
        // The verifier is a separate axis; this test is about codegen alone.
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        // The subject: cleanup pads only exist under unwinding.
        .arg("-Cpanic=unwind")
        // The lane `library/std` is built in. Proof-certificate promotion is a separate
        // axis that, measured on the frozen stage1-r3 plugin, refuses every EH function
        // with `[TCG-REGALLOC-063]` (its relocation inventory does not yet enumerate the
        // LSDA / compact-unwind relocations) and most leaf functions with
        // `[TCG-PROOF-465]` (no proof mapping for `StpPreIndex` / `LdpPostIndex`) --
        // `trust-ir-cg-box-dyn-field-drop`'s unwind fixture is refused the same way.
        // Without this knob every case here would be red for that reason, and the
        // drops on the pad would never be exercised.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1");
    cmd
}

fn main() {
    for opt in ["0", "3"] {
        for (case, body, expected, panics) in CASES {
            let name = format!("{case}_o{opt}");
            let file = format!("{name}.rs");
            rfs::write(&file, format!("{PRELUDE}{body}\n"));
            compile(&file, &name, opt).run();
            if *panics {
                run_fail(&name).assert_exit_code(101).assert_stdout_equals(expected);
            } else {
                run(&name).assert_stdout_equals(expected);
            }
        }

        for (path, main, expected, panics) in AGGREGATE_RETURN_MAINS {
            let name = format!("aggregate_return_{path}_o{opt}");
            let file = format!("{name}.rs");
            rfs::write(&file, format!("{PRELUDE}{AGGREGATE_RETURN}\n{main}\n"));
            compile(&file, &name, opt).run();
            if *panics {
                run_fail(&name).assert_exit_code(101).assert_stdout_equals(expected);
            } else {
                run(&name).assert_stdout_equals(expected);
            }
        }
    }
}
