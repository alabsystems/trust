//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-SD): a LOCAL scalar static's read DEFERS its CTFE to the
//! crate-finalize seam instead of declining. Inside `mir_built` the eval is
//! the E0391 CTFE-reachability hazard (the library/core wake.rs cycle); at
//! the seam every body owner's `mir_built` is already forced, so
//! `eval_static_initializer` is safe. The global is minted with a
//! `Constant::PhantomData` placeholder that `resolve_pending_consts`
//! patches; the positive ledger (`check_static_global_ledger`) refuses an
//! unpatched placeholder from ever splicing as a real value, and a
//! non-empty `pending_consts` refuses the flip and the derived-MIR
//! differential automatically.

static ANSWER: u64 = 42;
static FLAG: bool = true;

struct Pair {
    a: u32,
    b: u16,
}
// Trust (wave-SD2): a registered all-scalar STRUCT static defers too; the
// seam decodes it by the allocation+layout walk (fields read at rustc's own
// offsets, assembled in declaration order).
static PAIR: Pair = Pair { a: 7, b: 9 };

fn read_static() -> u64 {
    let r = &ANSWER;
    *r
}

fn read_flag() -> bool {
    FLAG
}

fn read_pair() -> u32 {
    let p = &PAIR;
    p.a + p.b as u32
}

fn main() {
    assert_eq!(read_static(), 42);
    assert!(read_flag());
    assert_eq!(read_pair(), 16);
}
