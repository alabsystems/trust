//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **Clean-origin purity guard resolves the IMPL, not the trait default.**
//! (`compiler/rustc_mir_transform/src/clean_origin_mir.rs`, `rust_callee_is_pure`;
//! the trait-dispatch fix of 2026-09-15.)
//!
//! `Operand::const_fn_def` names the TRAIT ITEM for a trait-method call, and
//! `optimized_mir` of a trait item is its DEFAULT body, not the impl that will
//! actually run. The guard walked the default, so a PURE default laundered an
//! IMPURE impl straight past the purity gate.
//!
//! That matters because the faithfulness gate is kernel definitional equality,
//! and the kernel is a PURE calculus: `tick (tick x)` denotes one value per
//! argument however the emitter arranges the calls, so only a PURE callee is
//! faithful. An effectful `<Impure as Tick>::tick` (an `AtomicU64::fetch_add`
//! on a `static`) admitted here is a wrong binary out of a kernel-checked
//! declaration.
//!
//! The guard now resolves through `Instance::try_resolve` and inspects the
//! concrete `InstanceKind::Item`; virtual dispatch, shims, intrinsics and every
//! unresolvable edge fail closed. The converse bug the same defect caused — an
//! impure DEFAULT falsely refusing a PURE impl — is pinned run-pass in
//! `tests/two-language-programs/r25_clean_trait_impl_callee`.
//!
//! ANNOTATION FORM CHANGED 2026-09-16. This file asserted the note with
//! `//@ error-pattern:`, a raw-text search over stderr. Since `passes.rs` began
//! demanding the Clean-origin gate at the analysis seam on every lane, the note
//! arrives as a STRUCTURED child diagnostic and compiletest refuses the pattern
//! outright — "is found in structured diagnostics", it says, and names the
//! span-anchored form instead. The
//! assertion is now a span-anchored `ERROR` + `NOTE` pair, which is strictly
//! stronger: a raw-text match would have been satisfied by the same sentence
//! appearing anywhere in the output, including about a different declaration.
//!
//! WHY IT STAYS `check-fail`, and the measurement that once said otherwise.
//! The Clean-origin gates live in the `optimized_mir` provider, and there was a
//! window in which CHECK time demanded that body only under
//! `-Ztrust-ir-lower=on`: measured 2026-09-16 on THIS file, the `check-fail`
//! form compiled clean with nothing but the island note, which is why it was
//! briefly carried as `build-fail` (codegen demands the body, so a build ran
//! the guard), and why three `clean_origin_*_refused` fixtures carried the hole
//! as deliberately-red `_off` revisions
//! (reports/2026-09-14-rust-abi-vararg-producer-half.md). That hole is CLOSED:
//! `passes.rs` now demands the gate at the analysis seam on every lane — via
//! `clean_origin_references::ensure_referenced`, and for every HIR-named
//! Clean-origin def above the `-Ztrust-ir-lower` block — so the same fatal
//! arrives at CHECK time and the earlier `build-fail` reading is obsolete.
//! "On every lane" is a claim about the VERIFICATION FLAGS and nothing wider:
//! neither demand is gated on `-Ztrust-ir-lower`, which is the whole of what
//! changed. Both still sit inside the `front_end_errors_before_trust_hooks`
//! guard, and `ensure_referenced` returns early on an empty registry — so a
//! compilation that already has front-end errors, or that names no Clean-origin
//! def, reaches neither, exactly as it should. `build-fail` would additionally require the check build to PASS,
//! which is now false. The sibling `clean_origin_effectful_callee_refused`
//! records the same 2026-09-16 transition, and
//! `clean_origin_static_read_refused` records its four revisions collapsing to
//! byte-identical diagnostics.
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

trait Tick {
    fn tick(x: u64) -> u64 {
        x
    }
}

struct Impure;

impl Tick for Impure {
    fn tick(_x: u64) -> u64 {
        COUNTER.fetch_add(1, Ordering::SeqCst) + 1
    }
}

fn tick(x: u64) -> u64 {
    <Impure as Tick>::tick(x)
}

clean {
    def twice_tick (x : UInt64) : UInt64 := tick (tick x)
}
// Annotated from OUT here: the `def` line is parsed by Clean and `//` is not a
// Clean comment.
//~^^^^ ERROR Clean declaration `twice_tick` cannot be called from Rust
//~| NOTE may only call a PURE Rust fn

fn main() {
    let _ = twice_tick(0);
}
