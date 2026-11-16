use super::*;
use crate::create_default_session_globals_then;

#[test]
fn interner_tests() {
    let i = Interner::prefill(&[], &[]);
    // first one is zero:
    assert_eq!(i.intern_str("dog"), Symbol::new(0));
    // re-use gets the same entry, even with a `ByteSymbol`
    assert_eq!(i.intern_byte_str(b"dog"), ByteSymbol::new(0));
    // different string gets a different #:
    assert_eq!(i.intern_byte_str(b"cat"), ByteSymbol::new(1));
    assert_eq!(i.intern_str("cat"), Symbol::new(1));
    // dog is still at zero
    assert_eq!(i.intern_str("dog"), Symbol::new(0));
}

#[test]
fn interner_get() {
    let i = Interner::prefill(&["chicken"], &["cow"]);
    let dog_idx = i.intern_str("dog"); // 2
    let cat_idx = i.intern_str("cat"); // 3
    assert_eq!(i.get_str(Symbol::new(0)), "chicken");
    assert_eq!(i.get_str(Symbol::new(1)), "cow");
    assert_eq!(i.get_str(cat_idx), "cat");
    assert_eq!(i.get_str(dog_idx), "dog");
}

#[test]
fn without_first_quote_test() {
    create_default_session_globals_then(|| {
        let i = Ident::from_str("'break");
        assert_eq!(i.without_first_quote().name, kw::Break);
    });
}

/// trust: THE FROZEN PREINTERNED-INDEX ABI, at string level.
///
/// The `const _: () = assert!(SYMBOL_DIGITS_BASE == ...)` next to the
/// `symbols!` invocation pins how MANY symbols precede the digit/letter
/// prefill. This test pins WHICH ones, in order. A rename, or a swap of two
/// adjacent entries, keeps the count constant, sails past that assertion, and
/// still makes the frozen prebuilt stage1 std unreadable -- `.rmeta` encodes
/// predefined symbols by raw index, so the crate name in the header decodes to
/// the wrong string and every crate resolution fails with E0463 plus
/// `Rejecting via crate name` in `-Zlog=rustc_metadata`. See the `AppendOnly`
/// block in `symbol.rs`.
///
/// The tail (env-derived symbols, then the `AppendOnly` section) is
/// deliberately NOT covered: those indices sit above everything the frozen std
/// can name, and `AppendOnly` exists precisely so that it may grow.
///
/// If this fails and you MEANT to renumber, print the new digest with
///     cargo test -p rustc_span preinterned_index_abi_is_frozen -- --nocapture
/// and update both this constant and `SYMBOL_DIGITS_BASE`'s assertion in the
/// same commit -- and expect every already-built `.rmeta` and every sealed
/// driver to stop interoperating across that commit.
#[test]
fn preinterned_index_abi_is_frozen() {
    // Re-recorded for the 1.101 toolchain port: upstream renamed/reordered
    // preinterned symbols below the frozen len (count unchanged, so
    // `SYMBOL_DIGITS_BASE`'s assertion stands). The whole sysroot is rebuilt
    // in the same step, so no already-built `.rmeta` interoperates across it.
    // Re-recorded again for upstream a0326caa8961: the preinterned string
    // `derive_const_issue` changed "118304" -> "143874" (index and count
    // unchanged), under the same whole-sysroot-rebuild condition.
    // Re-recorded for upstream 76456a688bc0: `derive_const_issue` REMOVED
    // (net -1 entry, SYMBOL_DIGITS_BASE 2398 -> 2397, frozen len 2459),
    // same whole-sysroot-rebuild condition.
    // Re-recorded for upstream ff7c30e864ac (in the 2a01bd6..4c46afa port
    // range): `debug_tuple_fields_finish` REMOVED when the Debug derive
    // switched tuple structs to the debug_struct helpers (net -1 entry,
    // SYMBOL_DIGITS_BASE 2397 -> 2396, frozen len 2458), same
    // whole-sysroot-rebuild condition.
    // Re-recorded for upstream 249cb163c0d0: the keyword-path rework moves
    // `deref`/`field_of`/`offset_of`/`type_ascribe`/`unwrap_binder`/
    // `wrap_binder` from Symbols to Keywords and renames
    // `rustc_as_ptr`/`rustc_never_returns_null_ptr` (net +2 entries,
    // SYMBOL_DIGITS_BASE 2396 -> 2398, frozen len 2460), same
    // whole-sysroot-rebuild condition.
    const FROZEN_DIGEST: u64 = 0xe832_21da_eb1f_da2d;

    create_default_session_globals_then(|| {
        let frozen_len = super::SYMBOL_LOWERCASE_LETTERS_BASE + 26;

        // FNV-1a, written out here so the digest depends on nothing but the
        // strings themselves -- not on any hasher this crate happens to use.
        let mut digest: u64 = 0xcbf2_9ce4_8422_2325;
        let mut feed = |bytes: &[u8]| {
            for &b in bytes {
                digest ^= b as u64;
                digest = digest.wrapping_mul(0x1000_0000_01b3);
            }
        };
        for index in 0..frozen_len {
            feed(&index.to_le_bytes());
            feed(Symbol::new(index).as_str().as_bytes());
            feed(b"\n");
        }

        println!("preinterned index ABI: len {frozen_len}, digest {digest:#018x}");
        assert_eq!(
            digest, FROZEN_DIGEST,
            "the preinterned symbol table changed below index {frozen_len}. \
             Already-built .rmeta names predefined symbols BY INDEX, so the frozen \
             stage1 std will fail to load with E0463 / `Rejecting via crate name`. \
             Add new symbols to the AppendOnly section in symbol.rs, which is \
             interned last and renumbers nothing."
        );
    });
}
