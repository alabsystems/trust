// Trust: regression test for a wrong-code bug in `MatchBranchSimplification`'s contiguous-range
// fold (`simplify_range_comparison`, rust-lang#123305).
//
// The fold rewrites `lo <= x && x <= hi` into `(x - lo) <= (hi - lo)` and used to unconditionally
// drop the statement defining the first comparison's temp, assuming it was single-use. `GVN` runs
// before this pass and CSEs identical comparisons, so a chain of ranges that share a bound leaves
// ONE such temp defined in the first block and read by several later blocks. Dropping its
// definition left those blocks switching on an uninitialized local, and every input took the first
// arm.
//
// This is not hypothetical: it is the shape of `rustc_abi::Integer::fit_unsigned`, so a `trustc`
// carrying the bug built a compiler that gave every enum needing a multi-byte discriminant a
// 1-byte tag — which then rejected `rustix` with E0080 while validating a promoted `&FileType`.
// The `size_of` assertion below is the self-hosting canary: it fails if the compiler running this
// test was itself built by a miscompiling one.

//@ run-pass
//@ compile-flags: -Copt-level=3 -Zmir-opt-level=3

// The shared bounds that make GVN collapse the comparisons are the whole point of this test.
#![allow(overlapping_range_endpoints)]
#![allow(non_contiguous_range_endpoints)]
#![allow(unreachable_patterns)]

use std::mem::size_of;

// The exact `fit_unsigned` shape: every arm shares the lower bound `0`, so GVN collapses all the
// `Le(const 0, copy x)` tests into a single temp.
#[inline(never)]
fn fit_unsigned(x: u128) -> u32 {
    match x {
        0..=0x0000_0000_0000_00ff => 8,
        0..=0x0000_0000_0000_ffff => 16,
        0..=0x0000_0000_ffff_ffff => 32,
        0..=0xffff_ffff_ffff_ffff => 64,
        _ => 128,
    }
}

// Signed counterpart, whose ranges share no bound; it never regressed, and is here so that a fix
// that simply stops folding is still visibly distinguishable from one that folds correctly.
#[inline(never)]
fn fit_signed(x: i128) -> u32 {
    match x {
        -0x80..=0x7f => 8,
        -0x8000..=0x7fff => 16,
        -0x8000_0000..=0x7fff_ffff => 32,
        _ => 128,
    }
}

// A narrow-width chain sharing an upper bound rather than a lower one.
#[inline(never)]
fn bucket(b: u8) -> u32 {
    match b {
        0x10..=0xff => 1,
        0x08..=0xff => 2,
        0x00..=0xff => 3,
    }
}

// The enum whose layout the miscompiled compiler got wrong: discriminants up to 49152 need a
// 2-byte tag. A 1-byte tag truncates every one of these to 0.
#[derive(Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum FileType {
    RegularFile = 32768,
    Directory = 16384,
    Symlink = 40960,
    Socket = 49152,
    Unknown,
}

impl FileType {
    // Promotes `&Self::RegularFile`; const-validating that promoted is what surfaced the bad tag.
    #[inline(never)]
    fn is_file(self) -> bool {
        self == Self::RegularFile
    }
}

fn main() {
    for (x, want) in [
        (0u128, 8),
        (255, 8),
        (256, 16),
        (49152, 16),
        (65535, 16),
        (65536, 32),
        (1 << 40, 64),
        (u64::MAX as u128, 64),
        (1 << 100, 128),
    ] {
        assert_eq!(fit_unsigned(x), want, "fit_unsigned({x})");
    }

    for (x, want) in
        [(0i128, 8), (127, 8), (128, 16), (-129, 16), (32767, 16), (32768, 32), (-32769, 32)]
    {
        assert_eq!(fit_signed(x), want, "fit_signed({x})");
    }

    for (b, want) in [(0u8, 3), (7, 3), (8, 2), (15, 2), (16, 1), (255, 1)] {
        assert_eq!(bucket(b), want, "bucket({b})");
    }

    assert_eq!(size_of::<FileType>(), 2, "enum tag width");
    assert!(FileType::RegularFile.is_file());
    assert!(!FileType::Directory.is_file());
    assert!(!FileType::Socket.is_file());
}
