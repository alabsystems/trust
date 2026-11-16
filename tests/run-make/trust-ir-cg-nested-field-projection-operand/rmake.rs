//! A nested-aggregate field operand projected THROUGH a pointer, and a CONST
//! nested scalar-field operand of a scalarized aggregate, both compile and
//! compute the right values at -O0 and -O3.
//!
//! ROUND 8 (the const-operand sibling). The projected half above landed first; the
//! CONST half was still refusing `new_dangling` at -O3 on the real suite:
//!
//!     ADT aggregate nested field 0 const operand is not a decodable
//!         scalar-field aggregate
//!
//! The round-5 decoder admitted a lone pointer leaf only when it spelled
//! `TrustIrTy::Ptr`, which this path NEVER produces — `Unique<u8>` flattens to
//! `[PtrConst(U8)]` — so the clause was dead and every pointer-leaf const bailed at
//! the leaf-type gate before the const was read. Four leaf classes were affected
//! and now round-trip: a provenance-free pointer leaf (`ptr_cap`, `raw_pair`,
//! `new_dangling`), a leaf one level DEEPER than the MIR field (`deep` — the decoder
//! had assumed leaf `j` was the `j`-th field), a `bool` leaf whose `bit_width()` is 1
//! but whose image is a byte (`flags`), and a full-width `i128`/`u128` leaf (`wide`,
//! which failed closed as "does not fit i128"). The values are asserted, not just the
//! compile: a mis-decoded pointer, a wrong byte offset, a dropped sign bit and a
//! bool byte outside {0,1} are all silent-wrong-value hazards.
//!
//! The fail-closed BOUNDARY is pinned in the same test (`RELOC`): a const leaf that
//! is a real relocation (`&'static u8`) has no byte image to decode and must refuse
//! BY NAME rather than flatten the relocation to an integer.
//!
//! Regression pin for two stage1 `library/std` refusal families (checkpoint A r3):
//!
//!     nested aggregate field operand uses a projection                       (19)
//!     ADT aggregate nested field N const operand is not a decodable
//!         scalar-field aggregate                                            (8)
//!
//! (1) `_6 = copy (((*_1).4: U32Bytes<LE>).0: [u8; 4])` — object's PE/COFF header
//!     readers after `U32Bytes::get` inlines, and `copy ((*_1).0: [u8; 16])` in
//!     `Ipv6Addr::segments`. `store_operand_into_memory_at` accepted a projected
//!     source only over a MEMORY-BACKED base, never through an entry-arg reference.
//! (2) `Inner { ptr: .., cap: const Cap(NoHighBit(0)), .. }` —
//!     `RawVecInner::try_allocate_in`, and `ptr: const Unique { 0x1 }` once
//!     `String::new()` inlines into `String::from_iter`. A Scalar-ABI aggregate
//!     const is always `ConstValue::Scalar` (rustc's `op_to_const`), and the
//!     nested-const decoder read only `ConstValue::Indirect`.
//!
//! Every function below refused on the pre-fix compiler (-O0: `segments`,
//! `consts`, `try_allocate_in`, `new_dangling`; -O3: all seven), each with one of the
//! two messages above and nothing else. The test RUNS the binary: the hazards are a
//! MIS-ADDRESSED copy (bytes from the pointer's slot instead of the pointee's) and a
//! MIS-DECODED constant (sign, float bits, a dropped pointer address), and only
//! values catch those. The LLVM control runs the same fixture first so a wrong
//! fixture cannot pass.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const FIXTURE: &str = r##"use std::hint::black_box;
use std::marker::PhantomData;
use std::num::NonZeroU32;
use std::ptr::NonNull;

// ---- (1) a nested aggregate operand projected THROUGH a thin pointer ----
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct U32Bytes<E>([u8; 4], PhantomData<E>);
#[derive(Clone, Copy)]
pub struct LittleEndian;
impl<E> U32Bytes<E> {
    #[inline(always)]
    pub fn get(self) -> u32 { u32::from_le_bytes(self.0) }
    pub const fn new(v: u32) -> Self { U32Bytes(v.to_le_bytes(), PhantomData) }
}
#[repr(C)]
pub struct SectionHeader {
    pub name: [u8; 8],
    pub virtual_size: U32Bytes<LittleEndian>,
    pub virtual_address: U32Bytes<LittleEndian>,
    pub size_of_raw_data: U32Bytes<LittleEndian>,
    pub pointer_to_raw_data: U32Bytes<LittleEndian>,
}
// object::read::pe::ImageSectionHeader::pe_file_range
#[inline(never)]
pub fn pe_file_range(h: &SectionHeader) -> (u32, u32) {
    let offset = h.pointer_to_raw_data.get();
    let a = h.virtual_size.get();
    let b = h.size_of_raw_data.get();
    (offset, if a < b { a } else { b })
}
// object::pe::ImageDelayloadDescriptor::is_null
#[inline(never)]
pub fn is_null(h: &SectionHeader) -> bool {
    h.virtual_size.get() == 0
        && h.virtual_address.get() == 0
        && h.size_of_raw_data.get() == 0
        && h.pointer_to_raw_data.get() == 0
}
// the same projected operand as a FIELD of an aggregate built into memory
pub struct Named { pub name: [u8; 8], pub rva: u32 }
#[inline(never)]
pub fn named(h: &SectionHeader) -> Named { Named { name: h.name, rva: h.virtual_address.get() } }

// core::net::Ipv6Addr::segments + the Display zero-run scan
#[derive(Clone, Copy)]
pub struct V6 { octets: [u8; 16] }
impl V6 {
    pub const fn segments(&self) -> [u16; 8] {
        let [a, b, c, d, e, f, g, h] = unsafe { std::mem::transmute::<_, [u16; 8]>(self.octets) };
        [u16::from_be(a), u16::from_be(b), u16::from_be(c), u16::from_be(d),
         u16::from_be(e), u16::from_be(f), u16::from_be(g), u16::from_be(h)]
    }
}
#[inline(never)]
pub fn longest_zero_run(addr: &V6) -> (usize, usize, u32) {
    let segments = addr.segments();
    let (mut ls, mut ll, mut cs, mut cl) = (0usize, 0usize, 0usize, 0usize);
    let mut sum = 0u32;
    let mut i = 0;
    while i < 8 {
        let s = segments[i];
        sum += s as u32;
        if s == 0 {
            if cl == 0 { cs = i; }
            cl += 1;
            if cl > ll { ls = cs; ll = cl; }
        } else {
            cl = 0;
        }
        i += 1;
    }
    (ls, ll, sum)
}

// ---- (2) a CONST nested scalar-field operand of a scalarized aggregate ----
#[derive(Clone, Copy)]
pub struct NoHighBit(usize);
#[derive(Clone, Copy)]
pub struct Cap(NoHighBit);
impl Cap { pub const ZERO: Cap = Cap(NoHighBit(0)); }
#[derive(Clone, Copy)]
pub struct Unique { pub pointer: NonNull<u8> }
pub struct RawInner { pub ptr: Unique, pub cap: Cap, pub align: usize }
#[derive(Clone, Copy)]
pub struct Nz(pub NonZeroU32);
impl Nz { pub const SEVEN: Nz = Nz(NonZeroU32::new(7).unwrap()); }
#[derive(Clone, Copy)]
pub struct Half(pub f64);
impl Half { pub const HALF: Half = Half(0.5); }
#[derive(Clone, Copy)]
pub struct Neg(pub i16);
impl Neg { pub const M3: Neg = Neg(-3); }
pub struct Consts { pub a: u64, pub nz: Nz, pub half: Half, pub neg: Neg }

// alloc::raw_vec::RawVecInner::try_allocate_in's zero-size arm: `cap: const Cap::ZERO`
#[inline(never)]
pub fn try_allocate_in(align: usize, capacity: usize) -> Result<RawInner, u8> {
    if capacity == 0 {
        return Ok(RawInner {
            ptr: Unique { pointer: NonNull::new(align as *mut u8).unwrap() },
            cap: Cap::ZERO,
            align,
        });
    }
    Err(2)
}
// String::new() inlined: `ptr: const Unique { dangling }` (a provenance-free pointer leaf)
#[inline(never)]
pub fn new_dangling(tag: usize) -> Result<RawInner, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(RawInner { ptr: Unique { pointer: NonNull::dangling() }, cap: Cap::ZERO, align: tag })
}
#[inline(never)]
pub fn consts(a: u64) -> Result<Consts, u8> {
    if a == u64::MAX { return Err(3); }
    Ok(Consts { a, nz: Nz::SEVEN, half: Half::HALF, neg: Neg::M3 })
}

// ---- (3) the CONST-operand shapes the round-8 decoder admits ----
// Each is a nested-aggregate CONST operand of an ADT aggregate whose leaves the
// decoder must read byte-exactly at their LAYOUT offsets.

// a PROVENANCE-FREE pointer leaf beside an integer leaf, as an `Indirect` const
// image (`RawVecInner`'s {ptr, cap} shape once `Vec::new()` inlines)
#[derive(Clone, Copy)]
pub struct PtrCap { pub ptr: NonNull<u8>, pub cap: usize }
impl PtrCap { pub const EMPTY: PtrCap = PtrCap { ptr: NonNull::dangling(), cap: 0 }; }
pub struct OuterPtrCap { pub inner: PtrCap, pub tag: usize }
#[inline(never)]
pub fn ptr_cap(tag: usize) -> Result<OuterPtrCap, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(OuterPtrCap { inner: PtrCap::EMPTY, tag })
}

// a RAW pointer leaf with a non-trivial address, beside a narrower integer leaf
#[derive(Clone, Copy)]
pub struct RawPair { pub p: *const u8, pub n: u32 }
impl RawPair { pub const K: RawPair = RawPair { p: 0x30 as *const u8, n: 77 }; }
pub struct OuterRaw { pub r: RawPair, pub tag: usize }
#[inline(never)]
pub fn raw_pair(tag: usize) -> Result<OuterRaw, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(OuterRaw { r: RawPair::K, tag })
}

// TWO levels of nesting: 2 leaves under ONE MIR field, so leaf index != field index
#[derive(Clone, Copy)]
pub struct Cell2(pub usize);
#[derive(Clone, Copy)]
pub struct Mid { pub c: Cell2, pub d: u16 }
#[derive(Clone, Copy)]
pub struct Deep { pub b: Mid }
impl Deep { pub const K: Deep = Deep { b: Mid { c: Cell2(0x1234_5678), d: 9 } }; }
pub struct OuterDeep { pub a: Deep, pub tag: usize }
#[inline(never)]
pub fn deep(tag: usize) -> Result<OuterDeep, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(OuterDeep { a: Deep::K, tag })
}

// a `bool` leaf (a whole byte in memory, `bit_width()` 1) beside a `u8`
#[derive(Clone, Copy)]
pub struct Flags(pub bool, pub u8);
impl Flags { pub const K: Flags = Flags(true, 200); }
pub struct OuterFlags { pub f: Flags, pub tag: usize }
#[inline(never)]
pub fn flags(tag: usize) -> Result<OuterFlags, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(OuterFlags { f: Flags::K, tag })
}

// a NEGATIVE i128 leaf: full-width, so the decode is a reinterpretation, and a
// u128 leaf above i128::MAX, which needs trust-ir's `Constant::u128` spelling
#[derive(Clone, Copy)]
pub struct Wide(pub i128);
impl Wide { pub const K: Wide = Wide(-170141183460469231731687303715884105727); }
#[derive(Clone, Copy)]
pub struct UWide(pub u128);
impl UWide { pub const K: UWide = UWide(0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe); }
pub struct OuterWide { pub w: Wide, pub u: UWide, pub tag: usize }
#[inline(never)]
pub fn wide(tag: usize) -> Result<OuterWide, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(OuterWide { w: Wide::K, u: UWide::K, tag })
}

fn main() {
    let h = SectionHeader {
        name: black_box(0x0000_0074_7865_742eu64).to_le_bytes(),
        virtual_size: U32Bytes::new(0x1234),
        virtual_address: U32Bytes::new(0x2000),
        size_of_raw_data: U32Bytes::new(0x1000),
        pointer_to_raw_data: U32Bytes::new(0xdead_0400),
    };
    assert_eq!(pe_file_range(black_box(&h)), (0xdead_0400, 0x1000));
    assert!(!is_null(black_box(&h)));
    let z = SectionHeader {
        name: black_box(0u64).to_le_bytes(),
        virtual_size: U32Bytes::new(0),
        virtual_address: U32Bytes::new(0),
        size_of_raw_data: U32Bytes::new(0),
        pointer_to_raw_data: U32Bytes::new(0),
    };
    assert!(is_null(black_box(&z)));
    let n = named(black_box(&h));
    assert_eq!(u64::from_le_bytes(n.name), 0x0000_0074_7865_742e);
    assert_eq!(n.rva, 0x2000);

    let v = V6 { octets: [0x20, 0x01, 0x0d, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] };
    assert_eq!(longest_zero_run(black_box(&v)), (2, 5, 0x2001 + 0x0db8 + 1));

    let r = try_allocate_in(black_box(8), black_box(0)).ok().unwrap();
    assert_eq!(r.ptr.pointer.as_ptr() as usize, 8);
    assert_eq!(r.cap.0 .0, 0);
    assert_eq!(r.align, 8);
    assert!(try_allocate_in(black_box(8), black_box(5)).is_err());
    let d = new_dangling(black_box(42)).ok().unwrap();
    assert_eq!(d.ptr.pointer.as_ptr() as usize, 1);
    assert_eq!(d.cap.0 .0, 0);
    assert_eq!(d.align, 42);
    let c = consts(black_box(9)).ok().unwrap();
    assert_eq!(c.a, 9);
    assert_eq!(c.nz.0.get(), 7);
    assert!(c.half.0 == 0.5);
    assert_eq!(c.neg.0, -3);

    let pc = ptr_cap(black_box(7)).ok().unwrap();
    assert_eq!(pc.inner.ptr.as_ptr() as usize, 1);
    assert_eq!(pc.inner.cap, 0);
    assert_eq!(pc.tag, 7);
    let rp = raw_pair(black_box(8)).ok().unwrap();
    assert_eq!(rp.r.p as usize, 0x30);
    assert_eq!(rp.r.n, 77);
    assert_eq!(rp.tag, 8);
    let dp = deep(black_box(9)).ok().unwrap();
    assert_eq!(dp.a.b.c.0, 0x1234_5678);
    assert_eq!(dp.a.b.d, 9);
    assert_eq!(dp.tag, 9);
    let fl = flags(black_box(10)).ok().unwrap();
    assert!(fl.f.0);
    assert_eq!(fl.f.1, 200);
    assert_eq!(fl.tag, 10);
    let wd = wide(black_box(11)).ok().unwrap();
    assert_eq!(wd.w.0, -170141183460469231731687303715884105727);
    assert_eq!(wd.u.0, 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe);
    assert_eq!(wd.tag, 11);

    println!("nested field projection/const operands ok");
}
"##;

/// The fail-closed BOUNDARY of the same family: a const nested-aggregate operand
/// whose leaf is a REAL RELOCATION. Its address is not known until link time, so
/// there is no byte image to decode and the backend must refuse BY NAME rather than
/// flatten the relocation to an integer.
const RELOC: &str = r##"use std::hint::black_box;

// A const nested-aggregate operand whose leaf is a REAL RELOCATION (`&'static u8`).
// Its address is not known until link time, so there is no byte image to decode:
// the backend must refuse BY NAME rather than flatten the relocation to an integer.
static ANCHOR: u8 = 42;
#[derive(Clone, Copy)]
pub struct StaticRef { pub p: &'static u8 }
impl StaticRef { pub const K: StaticRef = StaticRef { p: &ANCHOR }; }
pub struct Outer { pub r: StaticRef, pub tag: usize }
#[inline(never)]
pub fn mk(tag: usize) -> Result<Outer, u8> {
    if tag == usize::MAX { return Err(1); }
    Ok(Outer { r: StaticRef::K, tag })
}
fn main() {
    let o = mk(black_box(7)).ok().unwrap();
    assert_eq!(*o.r.p, 42);
    assert_eq!(o.tag, 7);
    println!("relocation leaf ok");
}
"##;

fn main() {
    rfs::write("nested.rs", FIXTURE);

    for level in ["0", "3"] {
        let control = format!("nested_llvm_o{level}");
        rustc()
            .input("nested.rs")
            .crate_type("bin")
            .crate_name("nested")
            .output(&control)
            .opt_level(level)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .run();
        run(&control).assert_stdout_contains("nested field projection/const operands ok");

        let subject = format!("nested_tcg_o{level}");
        rustc()
            .input("nested.rs")
            .crate_type("bin")
            .crate_name("nested")
            .output(&subject)
            .opt_level(level)
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
        run(&subject).assert_stdout_contains("nested field projection/const operands ok");
    }

    // The fail-closed boundary: the LLVM control runs it (so the fixture is known
    // good), and the backend must REFUSE it by name rather than invent an address.
    rfs::write("reloc.rs", RELOC);
    rustc()
        .input("reloc.rs")
        .crate_type("bin")
        .crate_name("reloc")
        .output("reloc_llvm")
        .opt_level("0")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .run();
    run("reloc_llvm").assert_stdout_contains("relocation leaf ok");
    rustc()
        .input("reloc.rs")
        .crate_type("bin")
        .crate_name("reloc")
        .output("reloc_tcg")
        .opt_level("0")
        .arg("-Zcodegen-backend=trust-ir-cg")
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .run_fail()
        .assert_stderr_contains("[TCG-MIR-UNSUPPORTED]")
        .assert_stderr_contains(
            "const operand is not a decodable scalar-field aggregate",
        )
        .assert_stderr_contains("PROVENANCE-FREE pointer address");
}
