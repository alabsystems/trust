//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (#197 item 3c): a call site may link to the callee's IDENTITY-lowered trust-ir record
// only when the callee's signature is INSTANTIATION-INVARIANT at that site's generic args.
//
// The producer's `map_ty` interns a struct per SPELLING, so `Bar<N, M>` and `Bar<2, [1, 1]>` are
// two `StructId`s for one Rust ADT. Wave-C's admission comment asserted that linking a concrete
// monomorphization to the identity record is sound; that holds for the SHAPE (wave-19's fat/thin
// gate) but not for the interned type identity, and the counterexample is a generic signature
// whose types are all ZSTs — laid out, so the body splices, yet spelled in parameters. The
// assembled module then carried an ill-typed call (`CallArgTypeMismatch`, measured 2 occurrences
// on tests/ui/const-generics/generic_const_parameter_types/inferred_from_arg.rs).
//
// This test is a COMPILE gate, not a validity gate — `validate_module` is a DEBUG-only tripwire
// (see crate_module.rs), so nothing a UI test can assert observes it. What it does guard is the
// hazard the fix actually introduced: `link_sig_is_instantiation_invariant` runs `tcx.fn_sig(..)`
// and `EarlyBinder::instantiate` from inside `mir_built`, and a tcx query from there has closed a
// FATAL E0391 cycle three times in this producer's history (RPIT, self-referential static, TAIT).
// Every arm of the gate is exercised below: declined, linked, and skipped.

#![feature(adt_const_params, generic_const_parameter_types)]
#![expect(incomplete_features)]

// ---- DECLINED: the signature moves under instantiation. ------------------------------------
// `Bar<N, M>` is a ZST, so it is laid out and `takes_bar`'s body splices; the parameter is still
// spelled in `N`/`M`, so the call below must NOT link to it.
struct Bar<const N: usize, const M: [u8; N]>;

fn takes_bar<const N: usize, const M: [u8; N]>(_: Bar<N, M>) {}

// A const-generic ARRAY parameter — the same decline for a non-ZST, and the nested-valtree
// (`SiteValTree::Branch`) path of the site-args encoding.
fn takes_array<const N: usize>(a: [u8; N]) -> usize {
    a.len()
}

// ---- LINKED: generic, but the signature is invariant. --------------------------------------
// `T` appears nowhere in the signature, so the identity record describes every instantiation
// exactly and wave-C's link must survive this change untouched.
fn phantom_generic<T>(x: u32) -> u32 {
    x
}

// The same for a const parameter the signature does not mention.
fn phantom_const<const K: usize>(x: u32) -> u32 {
    x
}

// ---- SKIPPED: no generics at all, the overwhelmingly common case (fast path). ---------------
fn plain(x: u32) -> u32 {
    x
}

// An inherent method on a generic impl: the gate must reach `DefKind::AssocFn` through the
// resolve path, not only free fns through the direct fast path.
struct Wrap<T>(T);

impl<T: Copy> Wrap<T> {
    fn get(&self) -> T {
        self.0
    }
}

fn main() {
    // Inferred args and explicit `_` args are two distinct THIR spellings of the same site.
    takes_bar(Bar::<2, { [1; 2] }>);
    takes_bar::<_, _>(Bar::<2, { [1; 2] }>);

    let n = takes_array([7u8, 8, 9]);
    assert_eq!(n, 3);

    assert_eq!(phantom_generic::<i32>(5), 5);
    assert_eq!(phantom_generic::<String>(6), 6);
    assert_eq!(phantom_const::<3>(7), 7);
    assert_eq!(plain(8), 8);

    assert_eq!(Wrap(9u32).get(), 9);
    assert_eq!(Wrap(true).get(), true);
}
