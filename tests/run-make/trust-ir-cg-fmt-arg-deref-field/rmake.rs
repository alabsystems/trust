//! A `format!` placeholder that borrows a FIELD THROUGH A POINTER —
//! `format!("... {}", self.0)` in a `&self` method — compiles, and prints the
//! right value at -O0 and -O3.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build
//! eleven times in `gimli` (checkpoint A, round three):
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... gimli::constants::DwTag as Display>::fmt
//!            ...: format! arg reference does not trace to a value local
//!
//! (also `DwAt`, `DwForm`, `DwAte`, `DwLang`, `DwAddr`, `DwOrd`, `DwDsc`,
//! `DwOp`, `DwEhPe`, `DwCfa`). gimli 0.32's `dw!` macro writes
//!
//!     f.pad(&format!("Unknown {}: {}", stringify!($struct_name), self.0))
//!
//! whose single placeholder argument is `_12 = &((*_1).0: u16)`. The format
//! interception's reference tracer accepted only `&_v` (a bare local) and a
//! bare `&(*_r)` reborrow, so any projected pointee was refused.
//!
//! The fix reads the projected place at the formatting call, which is exactly
//! when `core::fmt` reads it (the `Argument` holds the pointer, not a copy). It
//! is gated to the one shape whose ADDRESS cannot change between the borrow and
//! the call — `(*base).field...` with a unique-def reference/raw-pointer base —
//! and `write!` loads such a value before its up-front reserve can reallocate.
//!
//! What this test pins:
//! * `argplace`: every scalar kind (`u16`, `i32`, `bool`, `char`, `u8`, `u64`
//!   at its maximum, `i32::MIN`), a two-field chain, a RAW-pointer base, and a
//!   pointer stored in memory (`self.inner.a`, lowered through a unique-def
//!   `deref_copy` temp). Run, and the whole stdout compared with the LLVM
//!   backend's output, at -O0 AND -O3.
//! * `append`: the `write!`-into-an-existing-`String` path, whose projected
//!   value is loaded BEFORE the reserve. -O0 only: at -O3 that body is refused
//!   by the separate `core::fmt::rt::ArgumentType` gap, not by this lane.
//! * `repoint`: the gate is load-bearing. NLL accepts re-pointing a reference
//!   while a reborrow of its pointee is live (`format!("{} {}", p.x, { p = b;
//!   0 })`, which LLVM prints as `a.x`); re-reading `(*p).x` at the call would
//!   print `b.x`. It must stay refused, with the [TCG-FMT-ARGPLACE] text.
//! * `dw`: gimli's exact `Display` impl no longer reports this family at any
//!   opt level / panic strategy (at -O3 with `panic=unwind`, std's
//!   configuration, its first failure is now the separate [TCG-EH-DROP-O3]
//!   cleanup-pad lane).
//!
//! `no-proof-certs=1`: proof-certificate promotion is a separate axis (the r3
//! plugin's default lane refuses even a trivial `main` on [TCG-PROOF-465]); this
//! test is about codegen alone, like `-Ztrust-verify=off`.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const ARGPLACE: &str = r#"
extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

#[derive(Clone, Copy)]
pub struct DwTag(pub u16);

pub struct Rec {
    pub a: i32,
    pub b: bool,
    pub c: char,
    pub inner: (u8, u64),
}

impl DwTag {
    // gimli's `format!("Unknown {}: {}", stringify!(DwTag), self.0)`, the
    // `&((*_1).0)` borrow, emitted by FFI instead of `Formatter::pad`.
    #[inline(never)]
    pub fn emit_unknown(&self) {
        let s = format!("Unknown {}: {}", stringify!(DwTag), self.0);
        unsafe {
            write(1, s.as_ptr(), s.len());
            write(1, b"\n".as_ptr(), 1);
        }
    }
}

impl Rec {
    #[inline(never)]
    pub fn emit(&self) {
        let s = format!(
            "a={} b={} c={} n={} w={}",
            self.a, self.b, self.c, self.inner.0, self.inner.1
        );
        unsafe {
            write(1, s.as_ptr(), s.len());
            write(1, b"\n".as_ptr(), 1);
        }
    }
}

pub struct Outer<'a> {
    pub tag: u8,
    pub inner: &'a Rec,
}

impl<'a> Outer<'a> {
    // `self.inner.a`: the inner reference is copied out (`deref_copy`) into a
    // unique-def temp, then `&((*tmp).0)` is borrowed.
    #[inline(never)]
    pub fn emit_nested(&self) {
        let s = format!("nested a={} tag={}", self.inner.a, self.tag);
        unsafe {
            write(1, s.as_ptr(), s.len());
            write(1, b"\n".as_ptr(), 1);
        }
    }
}

// A RAW-pointer base.
#[inline(never)]
pub fn emit_raw(p: *const Rec) {
    let s = unsafe { format!("raw a={} w={}", (*p).a, (*p).inner.1) };
    unsafe {
        write(1, s.as_ptr(), s.len());
        write(1, b"\n".as_ptr(), 1);
    }
}

fn main() {
    DwTag(0x1234).emit_unknown();
    DwTag(0).emit_unknown();
    DwTag(u16::MAX).emit_unknown();
    let r = Rec { a: -42, b: true, c: 'Z', inner: (7, 18_446_744_073_709_551_615) };
    r.emit();
    Rec { a: i32::MIN, b: false, c: 'q', inner: (255, 0) }.emit();
    emit_raw(&r as *const Rec);
    Outer { tag: 3, inner: &r }.emit_nested();
    let done = b"argplace done\n";
    unsafe { write(1, done.as_ptr(), done.len()); }
}
"#;

const APPEND: &str = r#"
use std::fmt::Write as _;
extern "C" { fn write(fd: i32, buf: *const u8, n: usize) -> isize; }
pub struct S { pub x: u32, pub y: i64 }
// `write!` into an EXISTING String, reading `(*r).1` — the placeholder value is
// loaded before the up-front reserve (the preloaded path).
#[inline(never)]
pub fn append(dst: &mut String, r: &S) {
    let _ = write!(dst, "{}|", r.y);
}
fn main() {
    let a = S { x: 41, y: -9_000_000_000 };
    let b = S { x: 1, y: 2 };
    let mut acc = String::from("acc:");
    append(&mut acc, &a);
    append(&mut acc, &b);
    let _ = a.x + b.x;
    unsafe { write(1, acc.as_ptr(), acc.len()); write(1, b"\n".as_ptr(), 1); }
}
"#;

const REPOINT: &str = r#"
pub struct S { pub x: u32 }
// The base reference is RE-POINTED while the reborrow of its pointee is live.
// NLL accepts this; LLVM prints `1 0` (a.x). Reading `(*p).x` at the format
// call would print `2 0` (b.x) — the gate must refuse.
#[inline(never)]
pub fn repoint(a: &S, b: &S) -> usize {
    let mut p = a;
    let s = format!("{} {}", p.x, { p = b; 0 });
    let _ = p;
    s.len()
}
"#;

const DW: &str = r#"
use std::fmt;
#[derive(Clone, Copy)]
pub struct DwTag(pub u16);
impl DwTag {
    #[inline(never)]
    pub fn static_string(&self) -> Option<&'static str> {
        match self.0 { 0x11 => Some("DW_TAG_compile_unit"), _ => None }
    }
}
impl fmt::Display for DwTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if let Some(s) = self.static_string() {
            f.pad(s)
        } else {
            f.pad(&format!("Unknown {}: {}", stringify!(DwTag), self.0))
        }
    }
}
fn main() {
    let a = DwTag(0x11);
    let b = DwTag(0x1234);
    println!("[{}] [{}] [{:>30}]", a, b, b);
}
"#;

const EXPECTED_ARGPLACE: &str = "Unknown DwTag: 4660\nUnknown DwTag: 0\nUnknown DwTag: 65535\na=-42 b=true c=Z n=7 w=18446744073709551615\na=-2147483648 b=false c=q n=255 w=0\nraw a=-42 w=18446744073709551615\nnested a=-42 tag=3\nargplace done\n";

const REFUSED_FAMILY: &str = "does not trace to a value local";

fn tcg(input: &str, name: &str, crate_type: &str, opt: &str, panic: &str) -> run_make_support::Rustc {
    let mut cmd = rustc();
    cmd.input(input)
        .crate_name(name)
        .crate_type(crate_type)
        .opt_level(opt)
        .arg(format!("-Cpanic={panic}"))
        .arg("-Zcodegen-backend=trust-ir-cg")
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        // The verifier is a separate axis; this test is about codegen alone.
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .out_dir(format!("out-{name}-{crate_type}-o{opt}-{panic}"));
    cmd
}

fn main() {
    rfs::write("argplace.rs", ARGPLACE);
    rfs::write("append.rs", APPEND);
    rfs::write("repoint.rs", REPOINT);
    rfs::write("dw.rs", DW);

    for opt in ["0", "3"] {
        // Values: the whole stdout, byte for byte, as the LLVM backend prints it.
        tcg("argplace.rs", "argplace", "bin", opt, "abort").run();
        run(&format!("out-argplace-bin-o{opt}-abort/argplace"))
            .assert_stdout_equals(EXPECTED_ARGPLACE);

        // The gate must keep refusing a base that can be re-pointed.
        tcg("repoint.rs", "repoint", "rlib", opt, "abort")
            .run_fail()
            .assert_stderr_contains("[TCG-FMT-ARGPLACE]")
            .assert_stderr_contains("7repoint")
            .assert_stderr_contains("more than one definition");

        // gimli's exact impl: this family is gone under both panic strategies.
        // (The crate still fails for unrelated lanes, e.g. the `to_owned`
        // `Fn*` shim, so only the absence of THIS family is asserted.)
        for panic in ["abort", "unwind"] {
            tcg("dw.rs", "dw", "rlib", opt, panic)
                .run_unchecked()
                .assert_stderr_not_contains(REFUSED_FAMILY)
                .assert_stderr_not_contains("[TCG-FMT-ARGPLACE]");
        }
    }

    tcg("append.rs", "append", "bin", "0", "abort").run();
    run("out-append-bin-o0-abort/append").assert_stdout_equals("acc:-9000000000|2|\n");
}
