//! The five PINNED C-ABI entry points of the `Nat` trusted handle runtime.
//!
//! Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//!
//! # What these are
//!
//! `trust_ir_build::validate::TRUSTED_HANDLE_RUNTIMES` pins one runtime row,
//! `("Nat", "trust_bignum::Nat")`, with five entry points named by LINK-TIME
//! SYMBOL and exact signature. A TrustIR module carrying a `Ty::Handle` for
//! that row may only reach the runtime through a bodyless `External` C
//! declaration of one of those symbols; the validator refuses every other
//! origin, and it refuses a module that DEFINES one
//! (`HandleEntryPointDefinedLocally`) — the runtime is linked trusted base,
//! never a validated module.
//!
//! Until this file existed, NOTHING in the workspace exported those symbols:
//! measured, zero `no_mangle` / `extern "C"` items in `trust-bignum`. A
//! handle-bearing module therefore VALIDATED and then failed to LINK. These are
//! the definitions that close that, and the pin is the specification:
//!
//! | symbol                        | pinned signature                  | wraps |
//! |-------------------------------|-----------------------------------|-------|
//! | `trust_bignum_nat_from_u64`   | `(U64) -> Handle`                 | [`Nat::from_u64`] |
//! | `trust_bignum_nat_add`        | `(Handle, Handle) -> Handle`      | [`Nat::add`] |
//! | `trust_bignum_nat_sub`        | `(Handle, Handle) -> Handle`      | [`Nat::sub`] |
//! | `trust_bignum_nat_is_zero`    | `(Handle) -> Bool`                | [`Nat::is_zero`] |
//! | `trust_bignum_nat_drop`       | `(Handle) -> ()`                  | `Box::from_raw` + drop |
//!
//! `Ty::Handle` is pointer-width (`trust_ir::ty`: `bit_width_with` answers
//! `pointer_bits` for it), so a handle is exactly a thin `*mut Nat`. `Nat` is
//! `Sized`, so that pointer carries no metadata.
//!
//! # `sub` IS TRUNCATED SUBTRACTION, NOT MACHINE SUBTRACTION
//!
//! Lean's `Nat.sub` truncates (floors) at zero: `3 - 5 = 0`, not `-2` and not a
//! wrap to `2^64 - 2`. The kernel's own reducers do the same thing limb for
//! limb (`clean-kernel/src/micro/native.rs`:
//! `"Nat.sub" => nat_lit(if x >= y { x - y } else { BigUint::ZERO })`), and
//! [`Nat::sub`] is written to match, with the citation at the operation.
//!
//! This shim must match THAT, and it does so by calling it — it does not
//! re-implement subtraction, and there is deliberately no wrapping or
//! panicking variant behind this symbol. A kernel-checked theorem about `a - b`
//! is a theorem about truncated subtraction; a shim that saturated differently,
//! wrapped, or trapped would make the binary disagree with the proposition the
//! kernel checked, which is a WRONG BINARY rather than a failed proof. Callers
//! that must OBSERVE underflow have `Nat::checked_sub` in Rust; the pinned C
//! surface does not offer it, because the pin does not name it.
//!
//! # TRUSTED BASE — each function here is a new instance of TRUST.md item 9
//!
//! TrustIr's `TRUST.md` item 9 ("The pinned handle runtimes") already names
//! these symbols and states the three things trusted about them: (a) that the
//! pin table is the runtime's real ABI, (b) that each shim is FAITHFUL to the
//! Rust method it wraps, and (c) handle LIFETIME — that every handle passed to
//! a pinned entry point is live and that the release entry point is called at
//! most once per allocation. Nothing re-checks any of it: no proof states it, the
//! reference interpreter places handle modules outside the proven subset, and
//! the Lean model gives `Ty::Handle` a width but no semantics. These bodies are
//! kept to one line each for exactly that reason — the trusted step should be
//! small enough to read in full.
//!
//! # OWNERSHIP: WHO ALLOCATES, WHO BORROWS, WHO RELEASES
//!
//! This section previously read *"the pin defines no `drop`, so a returned
//! handle LEAKS"*, and named the TrustIr-side pin row as the thing that would
//! retire it. That row landed (trust-ir `TRUSTED_HANDLE_RUNTIMES`, role
//! `"drop"`, ratified in `docs/SPEC_RATIFICATIONS.md` §7 on 2026-09-17), so the
//! release shim is here and the disclosure is replaced by the real discipline:
//!
//! * **`from_u64` / `add` / `sub` ALLOCATE.** Each returns a `Box::into_raw`
//!   pointer to a FRESH `Nat`: a brand-new allocation that aliases no argument
//!   and no earlier result. That is a property of the wrapped methods, not a
//!   convention — [`Nat::add`] and [`Nat::sub`] are `(&self, &Self) -> Self`,
//!   so they cannot return one of their operands, and [`Nat::from_u64`] has no
//!   operand to return. Every handle this runtime hands out is therefore owned
//!   by whoever received it.
//! * **`add` / `sub` / `is_zero` only BORROW their arguments.** They take
//!   `*const Nat` and reborrow it shared; none consumes, frees or mutates a
//!   handle. So passing a handle to one of them transfers nothing, and the
//!   caller still owns it afterwards. A producer relies on this: it is what
//!   makes releasing an operand AFTER the arithmetic that read it correct.
//! * **`drop` RELEASES, and it is the only thing that does.** It reconstitutes
//!   the `Box` and drops it, freeing the `Nat` and its limb vector. There is no
//!   other way out: `Retain`/`Release`/`IsUnique`/`Dealloc`/`HeapAlloc` at a
//!   handle type are refused by TrustIr's validator by name, an off-pin release
//!   declaration is `HandleEntryPointSignatureMismatch`, and a second
//!   release-shaped symbol is `HandleForeignDeclaration`.
//!
//! **What nothing checks: that release happens exactly once.** This is part
//! (c) of item 9 and it is a stated NON-guarantee rather than a gap awaiting a
//! fix. A handle is an opaque one-pointer word with no IR provenance, and §7's
//! ratified transport set admits `Copy` and `Select`, so handle values are
//! deliberately NON-LINEAR: two SSA values may denote one allocation. A module
//! that releases the same handle twice, or reads one after releasing it,
//! VALIDATES — trust-ir pins that with two tests so it cannot be misread as a
//! guarantee — and trust-cg admits the call as pinned-runtime transport without
//! deciding anything about liveness either. The runtime and the producer own
//! it, exactly as a C caller owns `free`.
//!
//! **Leaking is still the SOUND direction.** A producer that cannot establish
//! ownership for some shape must not release, and `trust-clean-ir` is written
//! that way: it withholds release from every handle whose provenance it cannot
//! pin down. A leak is a bounded loss of memory; a double free or a
//! use-after-release is arbitrary behavior in the trusted runtime.
//!
//! # The contract each caller must meet
//!
//! Every handle argument must be a non-null, properly aligned, live pointer
//! returned by `from_u64`, `add` or `sub`. A null pointer is the one violation
//! cheap enough to catch, and it is caught: the shim aborts rather than
//! dereference or free it (an `extern "C"` function is `nounwind`, so the
//! assertion terminates the process instead of unwinding into C). Every other
//! violation — a dangling pointer, a pointer into a different type, a pointer
//! this runtime did not allocate, a handle already released, releasing one
//! twice, reading one after release — is undefined behavior the pin makes the
//! caller responsible for.

use alloc::boxed::Box;

use crate::Nat;

/// The pinned `from_u64` entry point: `(U64) -> Handle`.
///
/// Total, exactly like [`Nat::from_u64`] — every `u64` is a `Nat`. Returns a
/// FRESH owning handle, which the caller must release through
/// [`trust_bignum_nat_drop`] or leak; see the module docs on ownership.
#[unsafe(no_mangle)]
pub extern "C" fn trust_bignum_nat_from_u64(value: u64) -> *mut Nat {
    Box::into_raw(Box::new(Nat::from_u64(value)))
}

/// The pinned `add` entry point: `(Handle, Handle) -> Handle`.
///
/// # Safety
///
/// `a` and `b` must each be a non-null, aligned, live handle this runtime
/// produced. Null is caught; see the module docs for the rest of the contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_bignum_nat_add(a: *const Nat, b: *const Nat) -> *mut Nat {
    let (a, b) = unsafe { handle_pair("trust_bignum_nat_add", a, b) };
    Box::into_raw(Box::new(a.add(b)))
}

/// The pinned `sub` entry point: `(Handle, Handle) -> Handle`.
///
/// TRUNCATED subtraction — `a - b` is zero whenever `b > a`, which is Lean's
/// `Nat.sub` and the operation the kernel reduces. See the module docs: this is
/// the one entry point where matching the wrapped Rust method rather than
/// machine subtraction is the whole point.
///
/// # Safety
///
/// As [`trust_bignum_nat_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_bignum_nat_sub(a: *const Nat, b: *const Nat) -> *mut Nat {
    let (a, b) = unsafe { handle_pair("trust_bignum_nat_sub", a, b) };
    Box::into_raw(Box::new(a.sub(b)))
}

/// The pinned `is_zero` entry point: `(Handle) -> Bool`.
///
/// # Safety
///
/// `a` must be a non-null, aligned, live handle this runtime produced.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_bignum_nat_is_zero(a: *const Nat) -> bool {
    unsafe { handle_ref("trust_bignum_nat_is_zero", a) }.is_zero()
}

/// The pinned `drop` entry point: `(Handle) -> ()` — THE RELEASE ENTRY POINT.
///
/// Frees the allocation the handle names, and nothing else: it reconstitutes
/// the `Box` that `from_u64` / `add` / `sub` handed out and drops it, which
/// runs `Nat`'s destructor and returns the limb vector's buffer to the
/// allocator. It is the only way a `Nat` handle is ever released — see the
/// module docs on ownership for why no `Release`/`Dealloc` instruction can
/// substitute — and the only pinned entry point that consumes a handle without
/// producing one, which is why the pin spells its result as an EMPTY return
/// list rather than a `Unit` (those are different `FuncTy`s, and only the empty
/// one describes this `extern "C" fn(*mut Nat)`).
///
/// # Safety
///
/// `handle` must be a non-null, aligned handle THIS runtime allocated — the
/// value `from_u64`, `add` or `sub` returned — and the caller must guarantee
/// two further things nothing here can see:
///
/// * **no use after this call.** Every other handle value denoting this same
///   allocation (a `Copy`, a `Select` arm, a block parameter, a copy the
///   caller kept) is dangling the instant this returns, and reading one is
///   undefined behavior, not a stale answer.
/// * **no second release.** Calling this twice on one allocation is a double
///   free.
///
/// **NOTHING IN TRUST-IR OR TRUST-CG CHECKS EITHER OF THOSE.** `Ty::Handle` is
/// an opaque word with no IR provenance and TrustIr's ratified transport set
/// admits `Copy` and `Select`, so handle values are deliberately non-linear and
/// two SSA values may name one allocation; `validate_module` makes no liveness
/// claim about a handle at all, and a module that double-releases or reads
/// after release VALIDATES (trust-ir pins both as tests, precisely so the
/// non-guarantee is not misread as a guarantee). trust-cg admits the call as
/// pinned-runtime transport and decides nothing about lifetime either. This
/// runtime — and the producer that emits the call — owns the discipline, as
/// `TRUST.md` item 9(c) discloses.
///
/// Null is the one violation cheap enough to catch, and it aborts rather than
/// reach `Box::from_raw`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_bignum_nat_drop(handle: *mut Nat) {
    require_non_null("trust_bignum_nat_drop", handle);
    drop(unsafe { Box::from_raw(handle) });
}

/// Borrow one handle, refusing null loudly.
///
/// # Safety
///
/// As the entry points above. The null refusal itself is [`require_non_null`],
/// so the release entry point — which needs the RAW pointer and cannot take a
/// reference — shares one spelling of it rather than carrying a second copy.
unsafe fn handle_ref<'a>(entry: &str, handle: *const Nat) -> &'a Nat {
    require_non_null(entry, handle);
    unsafe { &*handle }
}

/// The one null refusal, shared by every entry point.
///
/// Five copies of a trusted check are five chances for one of them to drift,
/// and the release entry point is the one that would drift in the worst
/// direction: a null it accepted would reach `Box::from_raw`.
fn require_non_null(entry: &str, handle: *const Nat) {
    assert!(!handle.is_null(), "{entry}: a null `Nat` handle is not a handle");
}

/// Borrow two handles. Aliasing is fine — both borrows are shared.
///
/// # Safety
///
/// As [`handle_ref`].
unsafe fn handle_pair<'a>(entry: &str, a: *const Nat, b: *const Nat) -> (&'a Nat, &'a Nat) {
    unsafe { (handle_ref(entry, a), handle_ref(entry, b)) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shims are the LINKED surface, so the test drives them the way the
    /// linker will: through the raw pointers, not through the Rust methods.
    unsafe fn value(handle: *mut Nat) -> Nat {
        unsafe { *Box::from_raw(handle) }
    }

    /// Release the way the LINKER will — through the pinned symbol — rather
    /// than through the test's own `Box::from_raw`. `value` above reads and
    /// frees in one step, which is convenient for asserting a value; this is
    /// the real release path, and the tests that are ABOUT release use it.
    unsafe fn release(handle: *mut Nat) {
        unsafe { trust_bignum_nat_drop(handle) }
    }

    /// THE FRESHNESS FACT, measured rather than assumed.
    ///
    /// `trust-clean-ir`'s release emitter classifies every handle a producing
    /// entry point returns as a FRESH allocation aliasing nothing, and releases
    /// on that basis. If `add` could hand back one of its operands — or two
    /// calls could return one allocation — that classification would make the
    /// producer double-free. It cannot: the wrapped methods are
    /// `(&self, &Self) -> Self`, so the result is a new `Nat` and
    /// `Box::into_raw` a new allocation. Pointer distinctness is the observable
    /// form of that, and this is the test that holds the producer's assumption
    /// to it.
    #[test]
    fn every_produced_handle_is_a_fresh_allocation_distinct_from_its_operands() {
        let a = trust_bignum_nat_from_u64(6);
        let b = trust_bignum_nat_from_u64(7);
        let sum = unsafe { trust_bignum_nat_add(a, b) };
        let diff = unsafe { trust_bignum_nat_sub(a, b) };
        // Same inputs, a second call: a fresh allocation again, not a cache.
        let sum_again = unsafe { trust_bignum_nat_add(a, b) };
        let zero_a = trust_bignum_nat_from_u64(0);
        let zero_b = trust_bignum_nat_from_u64(0);

        for (label, handle) in
            [("sum", sum), ("diff", diff), ("sum_again", sum_again), ("zero_b", zero_b)]
        {
            assert_ne!(handle, a, "{label} must not alias its `a` operand");
            assert_ne!(handle, b, "{label} must not alias its `b` operand");
        }
        assert_ne!(sum, sum_again, "two calls must not share one allocation");
        assert_ne!(zero_a, zero_b, "two equal literals must not share one allocation");

        unsafe {
            release(a);
            release(b);
            release(sum);
            release(diff);
            release(sum_again);
            release(zero_a);
            release(zero_b);
        }
    }

    /// THE BORROW FACT, measured: the arithmetic entry points do not consume.
    ///
    /// The producer releases an operand AFTER the call that read it, which is
    /// correct exactly while `add`/`sub`/`is_zero` take their arguments by
    /// shared reference and free nothing. So: compute from two operands,
    /// release only the RESULT, and then require both operands to still answer
    /// and still hold their values. If any entry point consumed an argument,
    /// the reads below would be use-after-free.
    #[test]
    fn the_arithmetic_entry_points_borrow_their_operands_and_release_frees_only_the_result() {
        let a = trust_bignum_nat_from_u64(9);
        let b = trust_bignum_nat_from_u64(4);

        let sum = unsafe { trust_bignum_nat_add(a, b) };
        unsafe { release(sum) };
        let diff = unsafe { trust_bignum_nat_sub(a, b) };
        unsafe { release(diff) };
        assert!(!unsafe { trust_bignum_nat_is_zero(a) });

        // Both operands survived every call above, releases included.
        assert_eq!(unsafe { value(a) }, Nat::from_u64(9));
        assert_eq!(unsafe { value(b) }, Nat::from_u64(4));
    }

    /// Release accepts a handle from every entry point that produces one, and
    /// a released allocation's neighbours are unaffected.
    ///
    /// Under Miri or a sanitizer this is also the test that would catch a
    /// producing shim whose pointer did not come from `Box::into_raw`: release
    /// would then be freeing something the allocator never handed out.
    #[test]
    fn the_release_entry_point_accepts_a_handle_from_every_producing_entry_point() {
        let literal = trust_bignum_nat_from_u64(u64::MAX);
        let survivor = trust_bignum_nat_from_u64(1);
        let sum = unsafe { trust_bignum_nat_add(literal, survivor) };
        let difference = unsafe { trust_bignum_nat_sub(sum, survivor) };

        unsafe {
            release(literal);
            release(sum);
            release(difference);
        }

        // The one handle not released still holds its value, so release did
        // not reach past the allocation it was given.
        assert!(!unsafe { trust_bignum_nat_is_zero(survivor) });
        assert_eq!(unsafe { value(survivor) }, Nat::from_u64(1));
    }

    /// A null handle is refused, and the refusal is exercised through
    /// [`require_non_null`] rather than through the entry point.
    ///
    /// NOT a `should_panic` on `trust_bignum_nat_drop` itself, deliberately: an
    /// `extern "C"` function is `nounwind`, so the assertion inside one ABORTS
    /// the process instead of unwinding, and an aborting test is a failing test
    /// however it is annotated. The shared check is an ordinary Rust `fn`, so
    /// this pins the refusal that every entry point — the release one most of
    /// all, since a null it accepted would reach `Box::from_raw` — runs.
    #[test]
    #[should_panic = "a null `Nat` handle is not a handle"]
    fn a_null_handle_is_refused_before_it_reaches_the_allocator() {
        require_non_null("trust_bignum_nat_drop", core::ptr::null());
    }

    #[test]
    fn from_u64_and_add_agree_with_the_rust_methods_they_wrap() {
        let a = trust_bignum_nat_from_u64(u64::MAX);
        let b = trust_bignum_nat_from_u64(1);
        let sum = unsafe { trust_bignum_nat_add(a, b) };
        // Crosses the limb boundary, so this is not a one-limb tautology.
        assert_eq!(unsafe { value(sum) }, Nat::from_u64(u64::MAX).add(&Nat::from_u64(1)));
        assert_eq!(unsafe { value(a) }, Nat::from_u64(u64::MAX));
        assert_eq!(unsafe { value(b) }, Nat::from_u64(1));
    }

    /// THE SEMANTICS THAT MATTER: Lean's `Nat.sub` truncates at zero. A shim
    /// over machine subtraction would answer `2^64 - 2` here and every
    /// kernel-checked theorem about `a - b` would be about a different
    /// function.
    #[test]
    fn sub_is_truncated_not_wrapping_or_signed() {
        let three = trust_bignum_nat_from_u64(3);
        let five = trust_bignum_nat_from_u64(5);
        let under = unsafe { trust_bignum_nat_sub(three, five) };
        assert!(unsafe { trust_bignum_nat_is_zero(under) }, "3 - 5 must truncate to 0");
        assert_eq!(unsafe { value(under) }, Nat::ZERO);

        let over = unsafe { trust_bignum_nat_sub(five, three) };
        assert_eq!(unsafe { value(over) }, Nat::from_u64(2));
        unsafe {
            drop(value(three));
            drop(value(five));
        }
    }

    #[test]
    fn is_zero_answers_for_both_shapes() {
        let zero = trust_bignum_nat_from_u64(0);
        let one = trust_bignum_nat_from_u64(1);
        assert!(unsafe { trust_bignum_nat_is_zero(zero) });
        assert!(!unsafe { trust_bignum_nat_is_zero(one) });
        unsafe {
            drop(value(zero));
            drop(value(one));
        }
    }

    /// `a + a` with ONE handle passed twice: both borrows are shared, so
    /// aliasing a handle is defined.
    #[test]
    fn a_handle_may_be_passed_twice() {
        let a = trust_bignum_nat_from_u64(7);
        let doubled = unsafe { trust_bignum_nat_add(a, a) };
        assert_eq!(unsafe { value(doubled) }, Nat::from_u64(14));
        unsafe { drop(value(a)) };
    }

    /// The symbols the pin names, spelled once in a test, so a rename of any
    /// of the five is caught here rather than at link time in a downstream
    /// repo. The names are the ABI; `TRUSTED_HANDLE_RUNTIMES` pins these exact
    /// strings, and the FUNCTION TYPES on the left are the pinned signatures:
    /// `drop` is `(Handle) -> ()` with NO result, which is why its type has no
    /// `->` at all. A `-> *mut Nat` release would be a different `FuncTy` and
    /// trust-ir refuses it (`HandleEntryPointSignatureMismatch`).
    #[test]
    fn the_five_pinned_entry_points_exist_with_the_pinned_arities() {
        let from_u64: extern "C" fn(u64) -> *mut Nat = trust_bignum_nat_from_u64;
        let add: unsafe extern "C" fn(*const Nat, *const Nat) -> *mut Nat = trust_bignum_nat_add;
        let sub: unsafe extern "C" fn(*const Nat, *const Nat) -> *mut Nat = trust_bignum_nat_sub;
        let is_zero: unsafe extern "C" fn(*const Nat) -> bool = trust_bignum_nat_is_zero;
        let release: unsafe extern "C" fn(*mut Nat) = trust_bignum_nat_drop;
        let four = from_u64(4);
        let zero = from_u64(0);
        let h2 = unsafe { add(four, zero) };
        let another_four = from_u64(4);
        let h3 = unsafe { sub(h2, another_four) };
        assert!(unsafe { is_zero(h3) });
        // Nothing leaks out of this test, which is the whole point of the
        // fifth symbol: every handle it minted goes back through `release`.
        unsafe {
            release(four);
            release(zero);
            release(h2);
            release(another_four);
            release(h3);
        }
    }
}
