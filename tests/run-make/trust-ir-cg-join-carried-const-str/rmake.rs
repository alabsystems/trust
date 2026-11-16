//! A `&str` literal chosen per `match` arm, with a DIFFERENT length on each arm,
//! and then stored into an enum / tuple / struct after the join, compiles and
//! computes the right answer.
//!
//! Regression pin for 30 refusals that stopped the self-host `library/std` build
//! (gimli 0.32.3 `constants.rs`: every `dw!` `static_string` too large to inline,
//! and every `Display::fmt` it was inlined into; rustc-demangle 0.1.27
//! `v0::basic_type`):
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... bulk-append source slice has no
//!            resolvable (data, len) representation
//!
//! The MIR shape is
//!
//!     bb2:  _2 = const "...";  goto -> bb23;
//!     bb3:  _2 = const "_";    goto -> bb23;
//!     bb23: _0 = Option::<&str>::Some(copy _2);
//!
//! (at -O0 through a temp: `_3 = copy _2; _0 = (move _3, copy _1)`). A scalarized
//! const literal carries its length as a COMPILE-TIME side-table entry, and the
//! block-state merge keeps that entry only when every predecessor agrees — so the
//! data pointer crossed the join and the length did not, and the enum/tuple
//! fat-leaf store refused (correctly). The fix slot-backs exactly this local
//! (`compute_memory_backed_locals` rule `(9-join)`), so each arm stores BOTH lanes.
//!
//! This test RUNS the result at -O0 and -O3: the hazard class is a fat pointer
//! whose length is wrong for the arm taken, so the checksum folds in every
//! string's length AND bytes. The expected value is the LLVM control's output at
//! both -O0 and -O3 (also re-checked here against the LLVM backend).
//! `same_len` (equal lengths, which keep the side table) and `via_call` (a
//! join-carried literal passed to a call, already slot-backed) compiled before the
//! fix and must keep compiling.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

// Measured with the LLVM backend at -Copt-level=0 and -Copt-level=3.
const EXPECTED: &str = "join-carried const str checksum 12853285604302766047";

const SOURCE: &str = r##"use std::hint::black_box;

fn mix(h: u64, s: &str) -> u64 {
    let mut h = h.wrapping_mul(1_000_003).wrapping_add(s.len() as u64);
    for b in s.bytes() { h = h.wrapping_mul(31).wrapping_add(b as u64); }
    h
}

// `rustc_demangle::v0::basic_type`: a const literal per arm, different lengths,
// joined into `Some(copy _2)` stored in the memory-backed return.
#[inline(never)]
fn basic_type(tag: u8) -> Option<&'static str> {
    Some(match tag {
        b'b' => "bool", b'c' => "char", b'e' => "str", b'u' => "()",
        b'a' => "i8", b's' => "i16", b'l' => "i32", b'x' => "i64", b'n' => "i128",
        b'i' => "isize", b'h' => "u8", b't' => "u16", b'm' => "u32", b'y' => "u64",
        b'o' => "u128", b'j' => "usize", b'f' => "f32", b'd' => "f64",
        b'z' => "!", b'p' => "_", b'v' => "...",
        _ => return None,
    })
}

// gimli's `dw!` macro: `static_string` on a newtype, inlined into a caller.
#[derive(Clone, Copy)]
pub struct DwSect(pub u32);
impl DwSect {
    pub fn static_string(&self) -> Option<&'static str> {
        Some(match self.0 {
            1 => "DW_SECT_INFO", 3 => "DW_SECT_ABBREV", 4 => "DW_SECT_LINE",
            5 => "DW_SECT_LOCLISTS", 6 => "DW_SECT_STR_OFFSETS", 7 => "DW_SECT_MACRO",
            8 => "DW_SECT_RNGLISTS",
            _ => return None,
        })
    }
}
#[inline(never)]
fn sect_name_len(s: DwSect) -> u64 {
    match s.static_string() { Some(name) => mix(7, name), None => 0 }
}

// The join-carried literal stored as a TUPLE field and as a STRUCT field.
#[inline(never)]
fn tagged(c: u8) -> (&'static str, u8) {
    let s = match c { 0 => "zero", 1 => "one", _ => "many" };
    (s, c)
}
pub struct Named { pub name: &'static str, pub id: u64 }
#[inline(never)]
fn named(c: u8) -> Named {
    let name = if c % 2 == 0 { "even" } else { "odd" };
    Named { name, id: c as u64 }
}

// Must NOT regress: equal-length arms keep the const-length side table.
#[inline(never)]
fn same_len(c: bool) -> Option<&'static str> {
    Some(if c { "ab" } else { "cd" })
}
// Must NOT regress: a join-carried literal passed to a call (already slot-backed).
#[inline(never)]
fn via_call(c: bool) -> usize {
    let s = if c { "ab" } else { "xyz!" };
    black_box(s).len()
}

#[inline(never)]
fn run() -> u64 {
    let tags: &[u8] = b"beunivzq\0";
    let mut h = 0u64;
    let mut i = 0;
    while i < tags.len() {
        h = match basic_type(black_box(tags[i])) { Some(s) => mix(h, s), None => h.wrapping_add(99) };
        i += 1;
    }
    let mut v = 0u32;
    while v < 10 {
        h = h.wrapping_mul(17).wrapping_add(sect_name_len(black_box(DwSect(v))));
        v += 1;
    }
    let mut c = 0u8;
    while c < 3 {
        let (s, n) = tagged(black_box(c));
        h = mix(h, s).wrapping_add(n as u64);
        let r = named(black_box(c));
        h = mix(h, r.name).wrapping_add(r.id);
        c += 1;
    }
    h = match same_len(black_box(true)) { Some(s) => mix(h, s), None => h };
    h = match same_len(black_box(false)) { Some(s) => mix(h, s), None => h };
    h = h.wrapping_add(via_call(black_box(true)) as u64);
    h = h.wrapping_add(via_call(black_box(false)) as u64);
    h
}

fn main() {
    let h = run();
    println!("join-carried const str checksum {}", h);
}
"##;

fn main() {
    rfs::write("joinstr.rs", SOURCE);

    // LLVM control: the expected value is what upstream codegen prints.
    rustc()
        .input("joinstr.rs")
        .crate_type("bin")
        .arg("-Copt-level=3")
        .arg("-Ztrust-verify=off")
        .output("joinstr_llvm")
        .run();
    run("joinstr_llvm").assert_stdout_contains(EXPECTED);

    for opt in ["0", "3"] {
        let bin = format!("joinstr_tcg_o{opt}");
        rustc()
            .input("joinstr.rs")
            .crate_type("bin")
            .arg(format!("-Copt-level={opt}"))
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .output(&bin)
            .run();
        run(&bin).assert_stdout_contains(EXPECTED);
    }
}
