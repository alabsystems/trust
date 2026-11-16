//! Odd-width by-value aggregate RETURNS cross a real ABI boundary with the right
//! VALUES, and by-value `PassMode::Pair` ARGUMENTS keep failing closed.
//!
//! Regression pin for the refusal that stopped ten `library/std` roots at
//! checkpoint A round three (`core::net::parser`, `Ipv6Addr::to_ipv4_mapped`,
//! `core::escape::{hex_escape, escape_ascii}`, `Copied<slice::Iter<[u8; 2]>>::next`):
//!
//!     [TCG-REGALLOC-063] ... instruction selection failed: unsupported ABI
//!     location for return value: stack-passed returns are not supported
//!
//! Nothing was stack-passed. Each of those functions returns a 3/5/6-byte
//! `BackendRepr::Memory` aggregate (`Option<[u8; 2]>`, `Option<Ipv4Addr>`,
//! `([u8; 4], Range<u8>)`), which rustc returns as `PassMode::Cast` to ONE
//! integer register of exactly that width (i24/i40/i48 in x0). trust-cg's
//! `[TCG-RET-ABI]` gate agreed with that placement; the AArch64 selector then had
//! no single load for a 3/5/6/7-byte lane and refused. It now composes the lane
//! from exact-width loads, exactly as LLVM does (`ldrh` + `ldrb`, `orr .., lsl`).
//!
//! THE BOUNDARY IS THE POINT. A whole-program build cannot see a return-register
//! disagreement, because both sides would be built by the same backend. So every
//! returning function is compiled by trust-ir-cg into an rlib and CALLED FROM AN
//! LLVM-COMPILED `main`, at -O0 and -O3; the same `main` is first run against an
//! LLVM-compiled rlib, which is where the expected values come from.
//!
//! The second half pins the neighbouring `PassMode::Pair` ARGUMENTS: `(i16, i16)`
//! and `{u128, u128}` are two and four register lanes (LLVM's callee for
//! `fn(t: (i16, i16))` is `add w0, w8, w1, sxth`). They used to be refused because
//! trust-cg declared a by-value parameter as ONE value; trust-cg now lowers them
//! as rustc's two ABI values (the two-value `PassMode::Pair` argument lane, with
//! 128-bit scalars as `I128` register-pair lanes), so they are compiled by
//! trust-ir-cg into an rlib and CALLED FROM AN LLVM-COMPILED `main` at -O0 and
//! -O3, values asserted — including the sign of each `i16` half. The escapes the
//! old refusal named must still RUN.
//!
//! `no-proof-certs=1` matches the `library/std` build recipe: at -O0 an unrelated
//! proof-inventory refusal (no proof mapping for `StpPreIndex`) would otherwise
//! stop `Ipv4Addr::new` before the lane under test is reached.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{llvm_nm, rfs, run, rustc};

const LANES: &str = r#"
use std::net::Ipv4Addr;
use std::ops::Range;

// 3 bytes: `Option<[u8; 2]>`, the `Copied<Iter<[u8; 2]>>::next` shape.
#[inline(never)] pub fn ret3(x: u8) -> Option<[u8; 2]> {
    if x == 0 { None } else { Some([x, x.wrapping_mul(3)]) }
}
// 5 bytes: `Option<Ipv4Addr>`, the `to_ipv4_mapped` / `parse_ascii` shape.
#[inline(never)] pub fn ret5(x: u8) -> Option<Ipv4Addr> {
    if x == 0 { None } else { Some(Ipv4Addr::new(x, 0x5a, 0xa5, 0xff)) }
}
// 6 bytes: `([u8; 4], Range<u8>)`, the `core::escape::hex_escape::<4>` shape.
#[inline(never)] pub fn ret6(x: u8) -> ([u8; 4], Range<u8>) {
    ([x, 0x81, 0x7f, 0xfe], x.wrapping_add(1)..0xf0)
}
// 7 bytes: the last width with no single load.
#[inline(never)] pub fn ret7(x: u8) -> [u8; 7] {
    [x, 0xf1, 0xe2, 0xd3, 0xc4, 0xb5, 0xa6]
}
// The std root itself: `Copied<slice::Iter<'_, [u8; 2]>>::next`, monomorphized here.
#[inline(never)] pub fn next_pair<'a>(it: &mut std::slice::Iter<'a, [u8; 2]>) -> Option<[u8; 2]> {
    it.copied().next()
}
// 13 bytes through the C ABI: x0 plus a 5-byte x1 tail.
#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq)] pub struct B13 { pub b: [u8; 13] }
#[inline(never)] pub extern "C" fn ret13(x: u8) -> B13 {
    let mut b = [0u8; 13];
    let mut i = 0;
    while i < 13 { b[i] = x.wrapping_add((i as u8).wrapping_mul(37)); i += 1; }
    B13 { b }
}
"#;

// Every byte differs from its neighbours and the high bit is set in most of
// them, so a lane that is shifted, truncated, sign-extended or read from the
// wrong offset changes an asserted value.
const MAIN: &str = r#"
extern crate lanes;
use lanes::*;
use std::net::Ipv4Addr;
fn main() {
    assert_eq!(ret3(0), None);
    assert_eq!(ret3(0x91), Some([0x91, 0xb3]));
    assert_eq!(ret5(0), None);
    assert_eq!(ret5(0xc3), Some(Ipv4Addr::new(0xc3, 0x5a, 0xa5, 0xff)));
    let (a, r) = ret6(0x7e);
    assert_eq!(a, [0x7e, 0x81, 0x7f, 0xfe]);
    assert_eq!((r.start, r.end), (0x7f, 0xf0));
    assert_eq!(ret7(0x99), [0x99, 0xf1, 0xe2, 0xd3, 0xc4, 0xb5, 0xa6]);
    let arr = [[1u8, 0xfe], [0x80, 0x7f]];
    let mut it = arr.iter();
    assert_eq!(next_pair(&mut it), Some([1, 0xfe]));
    assert_eq!(next_pair(&mut it), Some([0x80, 0x7f]));
    assert_eq!(next_pair(&mut it), None);
    let b = ret13(0xfb);
    let mut want = [0u8; 13];
    for i in 0..13 { want[i] = 0xfbu8.wrapping_add((i as u8).wrapping_mul(37)); }
    assert_eq!(b.b, want);
    println!("odd-width aggregate return lanes ok");
}
"#;

const PAIR_REFUSED: &str = r#"
pub struct U256 { pub lo: u128, pub hi: u128 }
#[inline(never)] pub fn by_pair(t: (i16, i16)) -> i32 { t.0 as i32 * 1000 + t.1 as i32 }
#[inline(never)] pub fn u256_mix(v: U256) -> u128 { v.lo ^ v.hi }
"#;

// The escapes the refusal names, which must compile through trust-ir-cg and run.
const PAIR_ESCAPES: &str = r#"
#[derive(Clone, Copy, Debug, PartialEq)] pub struct U256 { pub lo: u128, pub hi: u128 }
#[inline(never)] pub fn by_array(t: [i16; 2]) -> i32 { t[0] as i32 * 1000 + t[1] as i32 }
#[inline(never)] pub fn by_ref(t: &(i16, i16)) -> i32 { t.0 as i32 * 1000 + t.1 as i32 }
#[inline(never)] pub fn u256_add(a: &U256, b: &U256, out: &mut U256) {
    let (lo, carry) = a.lo.overflowing_add(b.lo);
    out.lo = lo;
    out.hi = a.hi.wrapping_add(b.hi).wrapping_add(carry as u128);
}
"#;

// The `PassMode::Pair` arguments, called across the boundary from LLVM.
const PAIR_ARGS_MAIN: &str = r#"
extern crate pair_refused;
use pair_refused::*;
use std::hint::black_box;
fn main() {
    assert_eq!(by_pair(black_box((-7, 300))), -6700);
    assert_eq!(by_pair(black_box((32767, -32768))), 32734232);
    assert_eq!(by_pair(black_box((-1, -1))), -1001);
    let v = U256 { lo: black_box(u128::MAX), hi: black_box(5) };
    assert_eq!(u256_mix(v), u128::MAX ^ 5);
    let w = U256 { lo: black_box(1), hi: black_box(1u128 << 127) };
    assert_eq!(u256_mix(w), (1u128 << 127) | 1);
    println!("pair args ok");
}
"#;

const PAIR_MAIN: &str = r#"
extern crate escapes;
use escapes::*;
fn main() {
    assert_eq!(by_array([-7, 300]), -6700);
    assert_eq!(by_ref(&(12, -34)), 11966);
    let a = U256 { lo: u128::MAX, hi: 5 };
    let b = U256 { lo: 2, hi: 7 };
    let mut o = U256 { lo: 0, hi: 0 };
    u256_add(&a, &b, &mut o);
    assert_eq!(o, U256 { lo: 1, hi: 13 });
    println!("pair escapes ok");
}
"#;

fn trust_ir_cg(cmd: &mut run_make_support::Rustc) -> &mut run_make_support::Rustc {
    cmd.arg("-Zcodegen-backend=trust-ir-cg").arg("-Ztrust-ir-cg-args=no-proof-certs=1")
}

fn common<'a>(
    cmd: &'a mut run_make_support::Rustc,
    opt: &str,
) -> &'a mut run_make_support::Rustc {
    // The verifier is a separate axis; this test is about codegen alone.
    cmd.edition("2021").opt_level(opt).arg("-Ztrust-verify=off").arg("-Cdebuginfo=0")
}

fn main() {
    rfs::write("lanes.rs", LANES);
    rfs::write("main.rs", MAIN);
    rfs::write("pair_refused.rs", PAIR_REFUSED);
    rfs::write("escapes.rs", PAIR_ESCAPES);
    rfs::write("pair_main.rs", PAIR_MAIN);
    rfs::write("pair_args_main.rs", PAIR_ARGS_MAIN);

    for opt in ["0", "3"] {
        // --- LLVM control: the asserted values are right. ---
        let llvm = format!("llvm{opt}");
        rfs::create_dir_all(&llvm);
        common(rustc().input("lanes.rs").crate_type("rlib").crate_name("lanes"), opt)
            .out_dir(&llvm)
            .run();
        let control = format!("lanes_llvm_o{opt}");
        common(rustc().input("main.rs").crate_type("bin"), opt)
            .extern_("lanes", format!("{llvm}/liblanes.rlib"))
            .output(&control)
            .run();
        run(&control).assert_stdout_contains("odd-width aggregate return lanes ok");

        // --- trust-ir-cg callee, LLVM caller: the ABI boundary under test. ---
        let tcg = format!("tcg{opt}");
        rfs::create_dir_all(&tcg);
        trust_ir_cg(common(rustc().input("lanes.rs").crate_type("rlib").crate_name("lanes"), opt))
            .out_dir(&tcg)
            .run();
        // The rlib must not SHIP an undefined reference. The link below would
        // catch it, but only because this test links; an rlib that is merely
        // published carries the broken member into someone else's build. Measured
        // 2026-09-15: at -O0 this rlib referenced
        // `core::num::<impl usize>::unchecked_sub::precondition_check` — a helper
        // rustc's collector PRUNED, so no crate defines it — from the emitted
        // `slice::Iter<[u8; 2]>::next`, and the compile said nothing.
        let symbols = llvm_nm().input(format!("{tcg}/liblanes.rlib")).run().stdout_utf8();
        for line in symbols.lines() {
            assert!(
                !(line.contains(" U ") && line.contains("precondition_check")),
                "trust-ir-cg rlib ships an undefined `precondition_check` reference \
                 (the callee is pruned by rustc's collector, so nothing defines it): {line}"
            );
        }

        let boundary = format!("lanes_tcg_o{opt}");
        common(rustc().input("main.rs").crate_type("bin"), opt)
            .extern_("lanes", format!("{tcg}/liblanes.rlib"))
            .output(&boundary)
            .run();
        run(&boundary).assert_stdout_contains("odd-width aggregate return lanes ok");

        // --- `PassMode::Pair` by-value arguments cross the boundary with the right values. ---
        let pairs = format!("pairs{opt}");
        rfs::create_dir_all(&pairs);
        trust_ir_cg(
            common(rustc().input("pair_refused.rs").crate_type("rlib").crate_name("pair_refused"), opt),
        )
        .out_dir(&pairs)
        .run();
        let pair_bin = format!("pair_args_o{opt}");
        common(rustc().input("pair_args_main.rs").crate_type("bin"), opt)
            .extern_("pair_refused", format!("{pairs}/libpair_refused.rlib"))
            .output(&pair_bin)
            .run();
        run(&pair_bin).assert_stdout_contains("pair args ok");

        // --- ...and the escapes the old refusal named still compile through trust-ir-cg and run. ---
        let esc = format!("escapes{opt}");
        rfs::create_dir_all(&esc);
        trust_ir_cg(common(rustc().input("escapes.rs").crate_type("rlib").crate_name("escapes"), opt))
            .out_dir(&esc)
            .run();
        let esc_bin = format!("escapes_tcg_o{opt}");
        common(rustc().input("pair_main.rs").crate_type("bin"), opt)
            .extern_("escapes", format!("{esc}/libescapes.rlib"))
            .output(&esc_bin)
            .run();
        run(&esc_bin).assert_stdout_contains("pair escapes ok");
    }
}
