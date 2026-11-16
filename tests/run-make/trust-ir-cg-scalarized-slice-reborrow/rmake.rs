//! A whole-slice reborrow whose source is a SCALARIZED fat pointer compiles,
//! and carries the right data pointer and length.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `addr2line::line::has_forward_slash_root` / `has_backward_slash_root`, and
//! that refuses `core::str::from_utf8_unchecked_mut` itself at -O0:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... memory-backed slice reborrow source is
//!            neither a memory-backed slice nor a const-slice binding
//!
//! The -O3 MIR of `p.starts_with('/')` (`<char as Pattern>::is_prefix_of`, via
//! `encode_utf8` -> `from_utf8_unchecked_mut`) is
//!
//!     _11 = &raw mut (*_9);                       // _9: &mut [u8], memory-backed
//!     _10 = copy _11 as *mut str (PtrToPtr);      // _10 scalarized: data half only
//!     _5 = &(*_10);                                // _5 memory-backed: needs BOTH lanes
//!
//! and `p.get(1..3)` (`SliceIndex<str> for Range<usize>`) ends the same way,
//! `_3 = &(*_4)` over a `*const str` cast of a memory-backed `*const [u8]`. The
//! reborrow arm of `lower_memory_slice_assign` knew a memory-backed source and a
//! const-length binding, and nothing else. It now also recovers the pair of a
//! scalarized source — bound as projected values 0/1, or through its single
//! fat -> fat identity def chain back to a slot, every local on the chain
//! required to have a unique direct def. At -O0 the same shape refuses inside the
//! out-of-line `from_utf8_unchecked_mut` / `is_prefix_of` / `get`
//! monomorphizations and in the direct `b as *mut [u8] as *mut str; &*p` casts,
//! so both levels are run.
//!
//! This test RUNS the result and asserts VALUES: the length is the lane that was
//! missing, the contents catch a data half that points elsewhere, and
//! `u16_view_len` pins that a fat -> fat cast does NOT rescale the element count.
//! The `middle` asserts are LOAD-BEARING and must not be simplified away: a
//! subslice that resolved to its ROOT slice instead of the `[1..3]` window (the
//! hazard of reusing the append lane's back-trace, which follows `Offset` bases)
//! would answer `middle("abcdef")` wrongly. A custom trait object exercises the
//! addr2line functions through dynamic dispatch.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "reborrow.rs",
        r#"
// --- the addr2line shapes (verbatim bodies) ---
pub trait RootKind { fn root(&self) -> u8; }
pub struct P<'a>(pub &'a str);
#[inline(never)] pub fn has_forward_slash_root(p: &str) -> bool { p.starts_with('/') || p.get(1..3) == Some(":/") }
#[inline(never)] pub fn has_backward_slash_root(p: &str) -> bool { p.starts_with('\\') || p.get(1..3) == Some(":\\") }
// LOAD-BEARING: a reborrow that resolved a `[1..3]` subslice to its ROOT slice
// would answer this wrongly; do not simplify it away.
#[inline(never)] pub fn middle(p: &str) -> Option<&str> { p.get(1..3) }
impl RootKind for P<'_> {
    #[inline(never)] fn root(&self) -> u8 {
        (has_forward_slash_root(self.0) as u8) | ((has_backward_slash_root(self.0) as u8) << 1)
    }
}
#[inline(never)] fn root_of(r: &dyn RootKind) -> u8 { r.root() }

// --- a reborrow of a fat -> fat pointer CAST result ---
#[inline(never)] pub fn via_mut_ptr(b: &mut [u8]) -> &str {
    let p = b as *mut [u8] as *mut str;
    unsafe { &*p }
}
#[inline(never)] pub fn via_const_ptr_len(b: &[u8]) -> usize {
    let p = b as *const [u8] as *const str;
    unsafe { (&*p).len() }
}
#[inline(never)] pub fn via_const_ptr_bytes(b: &[u8]) -> &[u8] {
    let p = b as *const [u8] as *const str;
    unsafe { (&*p).as_bytes() }
}
// A fat -> fat cast is a bitwise `{data, len}` copy: the element COUNT is not
// rescaled, so an 11-byte slice viewed as `[u16]` still reports 11.
#[inline(never)] pub fn u16_view_len(b: &[u8]) -> usize {
    let p = b as *const [u8] as *const [u16];
    unsafe { (&*p).len() }
}
#[inline(never)] pub fn via_std(b: &mut [u8]) -> &str {
    unsafe { core::str::from_utf8_unchecked_mut(b) }
}
// control: memory-backed -> memory-backed reborrow
#[inline(never)] pub fn plain_reborrow(b: &[u8]) -> &[u8] { &*b }

fn main() {
    assert!(has_forward_slash_root("/usr"));
    assert!(has_forward_slash_root("C:/x"));
    assert!(!has_forward_slash_root("C:\\x"));
    assert!(!has_forward_slash_root("x/"));
    assert!(!has_forward_slash_root(""));
    assert!(has_backward_slash_root("\\\\srv"));
    assert!(has_backward_slash_root("C:\\x"));
    assert!(!has_backward_slash_root("C:/x"));
    assert_eq!(middle("abcdef"), Some("bc"));
    assert_eq!(middle("ab"), None);
    assert_eq!(middle("a"), None);
    let (a, b, c) = (P("/a"), P("C:\\a"), P("rel"));
    assert_eq!(root_of(&a), 1);
    assert_eq!(root_of(&b), 2);
    assert_eq!(root_of(&c), 0);

    let mut buf = *b"hello world";
    assert_eq!(via_mut_ptr(&mut buf), "hello world");
    assert_eq!(via_mut_ptr(&mut buf).len(), 11);
    assert_eq!(via_const_ptr_len(&buf), 11);
    assert_eq!(via_const_ptr_bytes(&buf), b"hello world");
    assert_eq!(u16_view_len(&buf), 11);
    assert_eq!(via_std(&mut buf), "hello world");
    assert_eq!(plain_reborrow(&buf).len(), 11);
    assert_eq!(via_const_ptr_len(&buf[..3]), 3);
    assert_eq!(via_const_ptr_bytes(&buf[6..]), b"world");
    println!("slice reborrows ok");
}
"#,
    );

    for opt in ["0", "3"] {
        let bin = format!("reborrow_o{opt}");
        rustc()
            .edition("2021")
            .input("reborrow.rs")
            .crate_type("bin")
            .opt_level(opt)
            .panic("abort")
            .output(&bin)
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
        run(&bin).assert_stdout_contains("slice reborrows ok");
    }
}
