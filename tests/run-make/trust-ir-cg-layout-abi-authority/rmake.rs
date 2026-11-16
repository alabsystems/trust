//! A type's trust-ir REPRESENTATION and its by-value ARGUMENT PLACEMENT are
//! derived from rustc's own `Layout` and `FnAbi` — or the type is refused by name.
//!
//! Regression pin for the root cause behind three separately-refuted patches
//! (union/packed lane reads, `#[repr(u8)]`/`#[repr(C)]` single-variant tagged
//! enums, aligned newtypes and ZST-sibling structs): trust-ir-cg decided a
//! type's representation from hand-written SHAPE predicates that never called
//! `layout_of`, and decided by-value argument placement without ever comparing
//! against rustc's `PassMode`.
//!
//! The scalarized "flattening" was `Tuple([leaf; n])` in DECLARATION order plus
//! two unchecked CLAIMS: (a) lane k sits at the same byte as rustc's field k,
//! and (b) lane index == MIR field index. Both are assertions about rustc's
//! layout; neither was checked against it. Four measured divergence classes
//! followed, one per clause of the gate this test pins:
//!
//!   1. A ZST BEFORE a sized field shifts the lane/field index identity
//!      (`struct T((), u64)` — a write to `.1` landed on lane 0 and was LOST).
//!   2. A single-variant enum whose repr inhibits the layout optimisation keeps
//!      a TAG (`#[repr(C)] enum E { V(i64) }` is 16 bytes with the payload at
//!      8); the flattening dropped it and read the tag as the payload.
//!   3. rustc REORDERS a `repr(Rust)` aggregate by descending alignment, so
//!      declaration-order lanes address the wrong bytes.
//!   4. The rustc image can be WIDER than the lanes
//!      (`#[repr(align(16))] struct A(i64)` is 16 bytes, the lane tuple 8).
//!
//! THE BOUNDARY IS THE POINT. A whole-program differential cannot see any of
//! this: both sides would be built by the same backend and would agree with
//! each other while disagreeing with rustc. So every value here is built and
//! read across a real codegen boundary — an LLVM-compiled helper rlib linked
//! against a trust-ir-cg-compiled `main` — at -O0 and -O3.
//!
//! The second half pins the REFUSAL BOUNDARY: what the bridge cannot place must
//! fail closed with a named refusal that carries its options (an over-aligned
//! newtype RETURNED by value, which rustc passes through the hidden buffer), the
//! shapes that boundary used to hold and no longer does (a `PassMode::Pair`
//! argument, a float ZST-sibling return) must RUN to rustc's values, and the
//! escapes the refusals name must themselves compile and run.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

// Built by LLVM in every leg: it is the independent reader/writer whose idea of
// the bytes is rustc's own.
const HELPER: &str = r#"
// --- class 1: a zero-sized field BEFORE a sized one -------------------------
#[derive(Clone, Copy)] pub struct ZstLead(pub (), pub u64);
#[inline(never)] pub fn zl_read(v: &ZstLead) -> u64 { v.1 }
#[inline(never)] pub fn zl_make(x: u64) -> ZstLead { ZstLead((), x) }

// --- class 2: a TAGGED single-variant enum ----------------------------------
#[derive(Clone, Copy)] #[repr(C)] pub enum TagC { V(i64) }
#[inline(never)] pub fn tc_read(v: &TagC) -> i64 { match *v { TagC::V(x) => x } }
#[inline(never)] pub fn tc_make(x: i64) -> TagC { TagC::V(x) }
#[derive(Clone, Copy)] #[repr(u8)] pub enum TagU8 { V(i64) }
#[inline(never)] pub fn tu_read(v: &TagU8) -> i64 { match *v { TagU8::V(x) => x } }

// --- class 3: rustc REORDERS the variant by descending alignment ------------
#[derive(Clone, Copy)] pub enum Reord { V(u8, i64) }
#[inline(never)] pub fn rd_read(v: &Reord) -> u64 {
    match *v { Reord::V(a, b) => (a as u64).wrapping_mul(1_000_003).wrapping_add(b as u64) }
}
#[inline(never)] pub fn rd_make(a: u8, b: i64) -> Reord { Reord::V(a, b) }

// --- class 4: the rustc image is WIDER than the single leaf -----------------
#[derive(Clone, Copy)] #[repr(align(16))] pub struct Wide(pub i64);
#[inline(never)] pub fn wd_read(v: &Wide) -> i64 { v.0 }
#[inline(never)] pub fn wd_make(x: i64) -> Wide { Wide(x) }

// --- the by-value ARGUMENT placement rustc states as `Indirect` -------------
// Every one of these is 9-16 bytes and `BackendRepr::Memory`, so rustc's Rust
// ABI passes the ADDRESS of a caller-owned copy, not the bytes.
#[derive(Clone, Copy)] pub struct Tri { pub a: u8, pub b: i64, pub c: u16 }
#[inline(never)] pub fn tri_take(v: Tri) -> u64 {
    (v.a as u64).wrapping_mul(1_000_003)
        .wrapping_add((v.b as u64).wrapping_mul(7))
        .wrapping_add(v.c as u64)
}
#[inline(never)] pub fn tri_make(a: u8, b: i64, c: u16) -> Tri { Tri { a, b, c } }
#[derive(Clone, Copy)] pub struct Three32 { pub a: u32, pub b: u32, pub c: u32 }
#[inline(never)] pub fn t32_take(v: Three32) -> u64 {
    (v.a as u64).wrapping_mul(1_000_003)
        .wrapping_add((v.b as u64).wrapping_mul(7))
        .wrapping_add(v.c as u64)
}
#[inline(never)] pub fn t32_make(a: u32, b: u32, c: u32) -> Three32 { Three32 { a, b, c } }
#[derive(Clone, Copy)] pub union ScalarCarrier { pub a: u128, pub b: u64 }
#[inline(never)] pub fn uc_take(v: ScalarCarrier) -> u64 { unsafe { v.a as u64 } }
#[inline(never)] pub fn uc_make(x: u64) -> ScalarCarrier { ScalarCarrier { a: x as u128 } }

// --- the refusal boundary ---------------------------------------------------
// No trust-ir lane is wider than 16 bytes, so these have no expressible image.
#[derive(Clone, Copy)] #[repr(align(128))] pub struct CachePad(pub u64);
#[inline(never)] pub fn cp_make(x: u64) -> CachePad { CachePad(x) }
#[inline(never)] pub fn cp_read(v: &CachePad) -> u64 { v.0 }
// A `PassMode::Pair` by-value argument: two register lanes, one declared value.
#[inline(never)] pub fn pair_take(t: (i32, i32)) -> i64 { t.0 as i64 * 1000 + t.1 as i64 }
#[inline(never)] pub fn pair_take_ref(t: &(i32, i32)) -> i64 { t.0 as i64 * 1000 + t.1 as i64 }
// A ZST-sibling struct with a FLOAT payload. rustc returns it in `d0`
// (`BackendRepr::Scalar(F64)`, `PassMode::Direct`), and the bridge's `F64`
// carrier lands there too; the zero-sized field BEFORE the sized one no longer
// breaks the lane/field index identity (a write to `.1` updates the value), so
// it is placed and must RUN.
#[derive(Clone, Copy)] pub struct ZstF64(pub (), pub f64);
#[inline(never)] pub fn zf_make(x: f64) -> ZstF64 { ZstF64((), x) }
#[inline(never)] pub fn zf_read(v: &ZstF64) -> f64 { v.1 }
#[inline(never)] pub fn zf_out(x: f64, out: &mut ZstF64) { out.1 = x; }
#[inline(never)] pub fn pair_take_arr(t: [i32; 2]) -> i64 { t[0] as i64 * 1000 + t[1] as i64 }
"#;

// Refused: an over-aligned single-scalar newtype RETURNED by value (rustc's
// hidden return buffer), then read by reference.
const REFUSED: &str = r#"
extern crate h;
fn main() {
    let v = h::cp_make(std::hint::black_box(8738));
    println!("{}", h::cp_read(&v));
}
"#;

// A `PassMode::Pair` by-value argument: trust-cg now places it as rustc's two
// ABI values, so it must RUN to rustc's value.
const PAIR: &str = r#"
extern crate h;
fn main() { println!("{}", h::pair_take(std::hint::black_box((3, 4)))); }
"#;

// Refused: an over-aligned single-scalar newtype RETURNED by value. rustc
// returns it through the caller's hidden buffer (`PassMode::Indirect`, `x8`);
// the bridge types it as its one scalar and has no scalar sret lane.
const RETWIDE: &str = r#"
extern crate h;
fn main() { println!("{}", h::wd_read(&h::wd_make(std::hint::black_box(-51)))); }
"#;

// A float-payload ZST-sibling struct RETURNED by value: rustc returns it in
// `d0` (`BackendRepr::Scalar(F64)`), which is where trust-cg's `F64` carrier
// lands too, so it must RUN to rustc's value.
const RETFLOAT: &str = r#"
extern crate h;
fn main() {
    let v = h::zf_make(std::hint::black_box(8738.0));
    // `to_bits()` on purpose: formatting an `f64` trips a SEPARATE, pre-existing
    // gap ("format! placeholder of unsupported type f64").
    println!("{}", h::zf_read(&v).to_bits());
}
"#;

// Every escape the two refusals name, which must compile through trust-ir-cg
// and produce rustc's own values.
const ESCAPES: &str = r#"
extern crate h;
use std::hint::black_box;
fn main() {
    // (1) pass the over-aligned value BY REFERENCE: crosses no by-value
    //     convention and needs no byte image of the object.
    let v = h::CachePad(black_box(8738));
    assert_eq!(h::cp_read(&v), 8738, "align(128) by reference");
    // (2) give the pair argument a shape whose placement trust-cg matches:
    //     an array is one value, a reference crosses no convention.
    assert_eq!(h::pair_take_ref(&(3, 4)), 3004, "pair by reference");
    assert_eq!(h::pair_take_arr([3, 4]), 3004, "pair as an array");
    // (3) return the float-payload value through an out-parameter, which
    //     crosses no return convention -- option (1) of the refusal's own text.
    let mut z = h::ZstF64((), 0.0);
    h::zf_out(black_box(8738.0), &mut z);
    assert_eq!(h::zf_read(&z), 8738.0, "float ZST-sibling via out-parameter");
    println!("refusal escapes ok");
}
"#;

// Compiled by trust-ir-cg. Every value crosses the boundary in both directions:
// built here and read by the LLVM helper, and built by the helper and read here.
const MAIN: &str = r#"
extern crate h;
use h::*;
use std::hint::black_box;
fn main() {
    let x: u64 = black_box(8738);
    let y: i64 = black_box(-51);

    // 1. ZST-sibling: the write must land on the field, not on lane 0.
    let mut z = zl_make(x);
    z.1 = black_box(4242);
    assert_eq!(zl_read(&z), 4242, "zst-sibling write");
    assert_eq!(zl_read(&ZstLead((), x)), x, "zst-sibling build");

    // 2. Tagged single-variant enums: the payload is at rustc's offset, and the
    //    tag the flattening used to drop is not read as the payload.
    assert_eq!(tc_read(&TagC::V(y)), y, "repr(C) tagged enum build");
    assert_eq!(tc_read(&tc_make(y)), y, "repr(C) tagged enum read");
    assert_eq!(tu_read(&TagU8::V(y)), y, "repr(u8) tagged enum build");

    // 3. Reordered variant: rustc puts `.1` at 0 and `.0` at 8.
    let rd_want = 9u64.wrapping_mul(1_000_003).wrapping_add(y as u64);
    assert_eq!(rd_read(&Reord::V(9, y)), rd_want, "reordered build");
    assert_eq!(rd_read(&rd_make(9, y)), rd_want, "reordered read");

    // 4. Wider-than-the-leaf image, built here and read by the helper. (A
    //    `Wide` RETURNED by value is rustc's hidden `x8` buffer — a refused
    //    leg below, `retwide`.)
    assert_eq!(wd_read(&Wide(y)), y, "align(16) newtype build");

    // 5. BY-VALUE ARGUMENT PLACEMENT. Every type here is 9-16 bytes and
    //    `BackendRepr::Memory`, so rustc's own FnAbi passes the ADDRESS of a
    //    caller-owned copy (`PassMode::Indirect { on_stack: false }`) while
    //    trust-cg's classifier would put the BYTES in x0/x1. The callee then
    //    dereferences the value's own bytes as if they were a pointer --
    //    measured as SIGSEGV against every one of these before the fix.
    let tri_want = 9u64.wrapping_mul(1_000_003)
        .wrapping_add((y as u64).wrapping_mul(7))
        .wrapping_add(4242);
    let t = tri_make(9, y, 4242);
    assert_eq!(tri_take(t), tri_want, "indirect by-value struct");
    let q = t32_make(1, 2, 3);
    assert_eq!(t32_take(q), 1_000_003u64 + 14 + 3, "indirect by-value 12-byte struct");
    let u = uc_make(x);
    assert_eq!(uc_take(u), x, "indirect by-value scalar-carrier union");
    // The same values built HERE and passed out, so the lane is exercised in
    // both directions across the boundary.
    assert_eq!(tri_take(Tri { a: 9, b: y, c: 4242 }), tri_want,
               "indirect by-value struct, built here");
    assert_eq!(uc_take(ScalarCarrier { a: x as u128 }), x, "union built here");

    println!("layout authority ok");
}
"#;

fn trust_ir_cg(cmd: &mut run_make_support::Rustc) -> &mut run_make_support::Rustc {
    cmd.arg("-Zcodegen-backend=trust-ir-cg")
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
}

fn common<'a>(cmd: &'a mut run_make_support::Rustc, opt: &str) -> &'a mut run_make_support::Rustc {
    // The verifier is a separate axis; this test is about codegen alone.
    cmd.edition("2021")
        .opt_level(opt)
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
}

fn main() {
    rfs::write("h.rs", HELPER);
    rfs::write("main.rs", MAIN);
    rfs::write("refused.rs", REFUSED);
    rfs::write("pair.rs", PAIR);
    rfs::write("retfloat.rs", RETFLOAT);
    rfs::write("retwide.rs", RETWIDE);
    rfs::write("escapes.rs", ESCAPES);

    for opt in ["0", "3"] {
        // The helper is ALWAYS built by LLVM: it is the independent side.
        let hd = format!("h{opt}");
        rfs::create_dir_all(&hd);
        common(rustc().input("h.rs").crate_type("rlib").crate_name("h"), opt)
            .out_dir(&hd)
            .run();

        // Control: LLVM main, so the asserted values are rustc's own.
        let control = format!("control_o{opt}");
        common(rustc().input("main.rs").crate_type("bin"), opt)
            .extern_("h", format!("{hd}/libh.rlib"))
            .output(&control)
            .run();
        run(&control).assert_stdout_contains("layout authority ok");

        // The lane under test: trust-ir-cg main against the LLVM helper.
        let boundary = format!("tcg_o{opt}");
        trust_ir_cg(common(rustc().input("main.rs").crate_type("bin"), opt))
            .extern_("h", format!("{hd}/libh.rlib"))
            .output(&boundary)
            .run();
        run(&boundary).assert_stdout_contains("layout authority ok");

        // --- THE REFUSAL BOUNDARY: what the bridge cannot place fails closed. ---
        // An over-aligned single-scalar newtype crossing BY VALUE as a return
        // (`#[repr(align(128))]` `CachePad`, `#[repr(align(16))]` `Wide`): rustc
        // returns it through the caller's hidden buffer, and the bridge, which
        // types it as its one scalar, refuses by name rather than read it out of
        // `x0` (`[TCG-RET-ABI]`, the padded-scalar return gate).
        let refused = format!("refused{opt}");
        rfs::create_dir_all(&refused);
        for (src, out) in [("refused.rs", "wide"), ("retwide.rs", "retwide")] {
            trust_ir_cg(common(rustc().input(src).crate_type("bin"), opt))
                .extern_("h", format!("{hd}/libh.rlib"))
                .output(format!("{refused}/{out}"))
                .run_fail()
                .assert_stderr_contains("[TCG-RET-ABI] by-value return")
                .assert_stderr_contains("rustc's layout pads it")
                .assert_stderr_contains("return it through an explicit out-parameter");
        }
        // Formerly refused, now placed as rustc does: a `PassMode::Pair` by-value
        // ARGUMENT (the two-value argument lane) and a float-payload ZST-sibling
        // RETURN (one `F64` in `d0`). Each must RUN to the LLVM control's value.
        for (src, out) in [("pair.rs", "pair"), ("retfloat.rs", "retfloat")] {
            let control = format!("{refused}/{out}_llvm");
            common(rustc().input(src).crate_type("bin"), opt)
                .extern_("h", format!("{hd}/libh.rlib"))
                .output(&control)
                .run();
            let want = run(&control).stdout_utf8();
            let bin = format!("{refused}/{out}");
            trust_ir_cg(common(rustc().input(src).crate_type("bin"), opt))
                .extern_("h", format!("{hd}/libh.rlib"))
                .output(&bin)
                .run();
            assert_eq!(run(&bin).stdout_utf8(), want, "{out} at -O{opt}");
        }

        // The escapes those refusals name must themselves compile and RUN.
        let esc = format!("escapes_o{opt}");
        trust_ir_cg(common(rustc().input("escapes.rs").crate_type("bin"), opt))
            .extern_("h", format!("{hd}/libh.rlib"))
            .output(&esc)
            .run();
        run(&esc).assert_stdout_contains("refusal escapes ok");
    }
}
