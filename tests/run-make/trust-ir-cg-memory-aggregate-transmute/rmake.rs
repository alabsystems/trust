//! A `Transmute` between two MEMORY-BACKED aggregates of the same size compiles,
//! and reproduces the bytes.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build in
//! `hashbrown`'s NEON group (four functions):
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... memory-backed aggregate assignment
//!            Transmute from non-int / width mismatch
//!
//! raised for `vreinterpret_s8_u8` (`_0 = copy _1 as int8x8_t (Transmute)`),
//! `vreinterpret_u64_u8`, `vcgez_s8` (`i8x8 -> int8x8_t`) and
//! `ptr::read_unaligned::<uint8x8_t>` (`_0 = copy _3 as T (Transmute)` over a
//! `Packed<T>` source) — and, exactly the same way, for `transmute::<Pair, Words>`,
//! `[u8; 16] -> Pair`, `Pair -> Quad([u32; 4])` and `Packed(Pair) -> Pair` in user
//! code at every opt level; and, with the sibling message "memory-backed ENUM
//! assignment Transmute from non-int / width mismatch", for `Pair -> TwoWords`.
//! Every one has a memory-backed source AND destination of equal size, so it is a
//! slot copy the array path already made (`lower_aggregate_transmute_slot_copy`);
//! what refused it was the `int -> Agg` / `int -> Enum` arm of
//! `lower_memory_aggregate_assign`, whose guard admits the DESTINATION and then
//! reported a non-integer source as a failure instead of declining. The fix is an
//! arm AHEAD of both that declines into the slot copy.
//!
//! The `Packed<T> -> T` case is also the alignment case: the packed slot is
//! 1-aligned and the destination 8-aligned, and the copy walks lanes at the
//! weaker alignment.
//!
//! This test RUNS the result at -O0 and -O3 and asserts the bytes on both sides
//! (a copy that landed the wrong lane, or read the wrong slot, cannot pass). The
//! integer arms (`u128 <-> Pair`, `u64 -> Pair32`, `u64 -> [u8; 8]`) run as
//! controls so the new arm cannot have moved them. The asserts compare u64
//! scalars on purpose: `assert_eq!` on an aggregate and a derived `PartialEq`
//! over `[u8; 16]` trip two UNRELATED refusals in `main` and would pin the wrong
//! thing; inputs borrowed by `&` are `static`s for the same reason (a local
//! struct borrowed by `&` hits an unrelated -O0 gap).
//!
//! The ENUM program is built with `-Zub-checks=no` at both levels. At -O0 rustc's
//! default UB checks insert an enum-validity probe before the transmute
//! (`_2 = copy _1 as [MaybeUninit<u8>; 16]; _3 = copy _2[0..8] as u64`), which
//! trips an UNRELATED `Ty::[MaybeUninit<u8>; 8]` refusal first and would hide the
//! arm this pins; -O3 already has UB checks off, so the flag changes nothing there.
//! Its asserts read the destination back through `match` (tag AND payload), and
//! transmute an enum SOURCE back into a struct.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "aggxmute.rs",
        r#"
use std::mem::transmute;

#[repr(C)] #[derive(Clone, Copy)] pub struct Pair { pub a: u64, pub b: u64 }
#[repr(C)] #[derive(Clone, Copy)] pub struct Bytes { pub b: [u8; 16] }
#[repr(C)] #[derive(Clone, Copy)] pub struct Words { pub w: [u64; 2] }
#[repr(C)] #[derive(Clone, Copy)] pub struct Quad(pub [u32; 4]);
#[repr(C)] #[derive(Clone, Copy)] pub struct Pair32 { pub a: u32, pub b: u32 }
#[repr(C, packed)] #[derive(Clone, Copy)] pub struct PackedPair(pub Pair);

// --- aggregate -> aggregate transmutes into a memory-backed destination ---
pub trait Reinterpret { fn as_bytes16(self) -> Bytes; }
impl Reinterpret for Pair {
    #[inline(never)] fn as_bytes16(self) -> Bytes { unsafe { transmute(self) } }
}
impl Reinterpret for Words {
    #[inline(never)] fn as_bytes16(self) -> Bytes { unsafe { transmute(self) } }
}
#[inline(never)] pub fn via_trait<T: Reinterpret>(t: T) -> Bytes { t.as_bytes16() }
#[inline(never)] pub fn pair_to_words(p: Pair) -> Words { unsafe { transmute(p) } }
#[inline(never)] pub fn bytes_to_pair(b: Bytes) -> Pair { unsafe { transmute(b) } }
#[inline(never)] pub unsafe fn read_unaligned_pair(p: *const Pair) -> Pair { std::ptr::read_unaligned(p) }
#[inline(never)] pub fn packed_to_pair(p: &PackedPair) -> Pair {
    let v: PackedPair = *p;
    unsafe { transmute::<PackedPair, Pair>(v) }
}
#[inline(never)] pub fn pair_to_quad(p: &Pair) -> Quad {
    let v: Pair = *p;
    unsafe { transmute::<Pair, Quad>(v) }
}
#[inline(never)] pub fn array_to_pair(b: &[u8; 16]) -> Pair {
    let v: [u8; 16] = *b;
    unsafe { transmute::<[u8; 16], Pair>(v) }
}

// --- controls: the integer arms must not move ---
#[inline(never)] pub fn u128_to_pair(x: u128) -> Pair { unsafe { transmute(x) } }
#[inline(never)] pub fn pair_to_u128(p: Pair) -> u128 { unsafe { transmute(p) } }
#[inline(never)] pub fn int_to_pair32_sum(x: u64) -> u32 {
    let p: Pair32 = unsafe { transmute::<u64, Pair32>(x) };
    p.a.wrapping_add(p.b)
}
#[inline(never)] pub fn int_to_bytes_first(x: u64) -> u8 {
    let b: [u8; 8] = unsafe { transmute::<u64, [u8; 8]>(x) };
    b[0]
}

#[cfg(target_arch = "aarch64")]
mod neon {
    use std::arch::aarch64::*;
    use std::mem::transmute;
    #[inline(never)] pub fn u64_to_u8x8(x: u64) -> uint8x8_t { unsafe { transmute(x) } }
    #[inline(never)] pub fn s8x8_to_u64(a: int8x8_t) -> u64 { unsafe { transmute(a) } }
    #[inline(never)] pub fn u8_as_s8(a: uint8x8_t) -> int8x8_t { unsafe { vreinterpret_s8_u8(a) } }
    #[inline(never)] pub fn u8_as_u64x1(a: uint8x8_t) -> u64 { unsafe { transmute(vreinterpret_u64_u8(a)) } }
    #[inline(never)] pub unsafe fn read_unaligned_v(p: *const uint8x8_t) -> u64 { transmute(std::ptr::read_unaligned(p)) }
}

#[inline(never)] fn word(b: &Bytes, i: usize) -> u64 {
    let mut w = 0u64;
    let mut k = 0;
    while k < 8 { w |= (b.b[i * 8 + k] as u64) << (8 * k); k += 1; }
    w
}

static LO: u64 = 0x0807_0605_0403_0201;
static HI: u64 = 0x100f_0e0d_0c0b_0a09;
static PAIR: Pair = Pair { a: LO, b: HI };
static PACKED: PackedPair = PackedPair(PAIR);
static ARRAY: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

fn main() {
    let lo = LO;
    let hi = HI;
    let p = Pair { a: lo, b: hi };
    let bytes = Bytes { b: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] };
    let words = Words { w: [lo, hi] };
    let x = ((hi as u128) << 64) | lo as u128;

    let t = via_trait(p);
    assert!(word(&t, 0) == lo && word(&t, 1) == hi);
    let t = via_trait(words);
    assert!(word(&t, 0) == lo && word(&t, 1) == hi);
    let w = pair_to_words(p);
    assert!(w.w[0] == lo && w.w[1] == hi);
    let q = bytes_to_pair(bytes);
    assert!(q.a == lo && q.b == hi);
    let q = packed_to_pair(&PACKED);
    assert!(q.a == lo && q.b == hi);
    let quad = pair_to_quad(&PAIR);
    assert!(quad.0[0] == 0x0403_0201 && quad.0[1] == 0x0807_0605);
    assert!(quad.0[2] == 0x0c0b_0a09 && quad.0[3] == 0x100f_0e0d);
    let q = array_to_pair(&ARRAY);
    assert!(q.a == lo && q.b == hi);

    let q = u128_to_pair(x);
    assert!(q.a == lo && q.b == hi);
    assert!(pair_to_u128(p) == x);
    assert!(int_to_pair32_sum(0x0000_0003_0000_0004) == 7);
    assert!(int_to_bytes_first(0x0102_0304_0506_0708) == 0x08);

    // An UNALIGNED source: the `ptr::read_unaligned` `Packed<T> -> T` shape.
    let mut buf = [0u8; 17];
    let mut k = 0;
    while k < 16 { buf[k + 1] = bytes.b[k]; k += 1; }
    let q = unsafe { read_unaligned_pair(buf.as_ptr().add(1).cast()) };
    assert!(q.a == lo && q.b == hi);
    #[cfg(target_arch = "aarch64")]
    {
        let v = neon::u64_to_u8x8(lo);
        assert!(neon::s8x8_to_u64(neon::u8_as_s8(v)) == lo);
        assert!(neon::u8_as_u64x1(v) == lo);
        let r = unsafe { neon::read_unaligned_v(buf.as_ptr().add(1).cast()) };
        assert!(r == lo);
    }
    println!("aggregate transmutes ok");
}
"#,
    );
    rfs::write(
        "enumxmute.rs",
        r#"
use std::hint::black_box;
use std::mem::transmute;

#[repr(C)] #[derive(Clone, Copy)] pub struct Pair { pub a: u64, pub b: u64 }
// A two-variant enum with a u64 payload. `repr(u64)` fixes the layout (RFC 2195:
// a u64 tag at offset 0, the payload at offset 8), so a 16-byte `Pair` whose `a`
// is 0 or 1 is a valid image of `A(b)` / `B(b)`.
#[repr(u64)] #[derive(Clone, Copy)] pub enum TwoWords { A(u64), B(u64) }

// ENUM destination: the memory-backed slot copy arm sits AHEAD of the
// `enum = int as Enum` arm, which used to refuse this as "from non-int".
#[inline(never)] pub fn pair_to_two_words(p: Pair) -> TwoWords { unsafe { transmute(p) } }
// ENUM source into a struct destination.
#[inline(never)] pub fn two_words_to_pair(t: TwoWords) -> Pair { unsafe { transmute(t) } }
// Reads the tag (discriminant) AND the payload out of the destination slot.
#[inline(never)] pub fn two_words_value(t: TwoWords) -> u64 {
    match t { TwoWords::A(x) => x, TwoWords::B(x) => x ^ 0xffff }
}

fn main() {
    let lo = black_box(0x0807_0605_0403_0201u64);
    let hi = black_box(0x100f_0e0d_0c0b_0a09u64);
    // control: a constructed enum through the same reader
    assert!(two_words_value(TwoWords::B(7)) == 7 ^ 0xffff);
    assert!(two_words_value(pair_to_two_words(Pair { a: 0, b: hi })) == hi);
    assert!(two_words_value(pair_to_two_words(Pair { a: 1, b: lo })) == lo ^ 0xffff);
    let e = two_words_to_pair(TwoWords::B(hi));
    assert!(e.a == 1 && e.b == hi);
    let e = two_words_to_pair(TwoWords::A(lo));
    assert!(e.a == 0 && e.b == lo);
    println!("enum transmutes ok");
}
"#,
    );

    for opt in ["0", "3"] {
        let bin = format!("aggxmute_o{opt}");
        rustc()
            .input("aggxmute.rs")
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
        run(&bin).assert_stdout_contains("aggregate transmutes ok");

        let bin = format!("enumxmute_o{opt}");
        rustc()
            .input("enumxmute.rs")
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
            .arg("-Ztrust-verify=off")
            // See the module comment: keeps rustc's -O0 enum-validity probe (an
            // unrelated refusal) out of the function under test.
            .arg("-Zub-checks=no")
            .arg("-Cdebuginfo=0")
            .run();
        run(&bin).assert_stdout_contains("enum transmutes ok");
    }
}
