//! Compatibility contract attributes for non-tRustc builds.
//!
//! tRustc owns `#[requires]` and `#[ensures]` as first-class compiler syntax.
//! These proc macros are only a stable-Rust compatibility shim for crates that
//! need to parse before the tRustc contract query is available. They must not
//! be treated as the canonical Trust contract representation.
//!
//! `invariant` IS DIFFERENT, and the difference is load-bearing. It is exported
//! here only so that name resolution finds it and tRustc can REFUSE it with a
//! diagnostic that names the fix; it has no verified meaning on any lane. Under
//! `-Z trust-verify=on` the resolver replaces it with the compiler-owned
//! `ExpandTrustInvariant` builtin, which is a hard error. Do not read the
//! passthrough body below as evidence that the annotation means anything.
//!
//! `decreases` IS EXPORTED, and why that is safe while a PASSTHROUGH would not
//! be is the whole point of the D4 lane. D1 originally wrote here "DO NOT ADD
//! `decreases` ... adding a passthrough for it would recreate exactly the
//! silent erasure that `invariant`'s passthrough caused". That is true of a
//! passthrough and false of a DESUGARING: the resolver substitutes
//! `ExpandTrustDecreases` before expansion and that builtin re-emits the NATIVE
//! clause spelling verbatim, so there is no second implementation and nothing
//! to erase. The body below additionally fails CLOSED under an older toolchain
//! that has no such mapping — see the `decreases` docs.

#![forbid(unsafe_code)]

use proc_macro::TokenStream;

fn passthrough(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

/// Compatibility precondition marker.
///
/// The real Trust contract is captured by tRustc before macro-expanded
/// passthrough code reaches verification.
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

/// Compatibility postcondition marker.
///
/// The real Trust contract is captured by tRustc before macro-expanded
/// passthrough code reaches verification.
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    passthrough(attr, item)
}

/// Invariant marker. **Always refused; it verifies nothing on any lane.**
///
/// Unlike [`requires`] and [`ensures`], this attribute has NO verified meaning,
/// so — unlike them — it is NOT a passthrough. It refuses in both directions,
/// and it needs to, because the two modes are refused by different machinery:
///
/// * `-Z trust-verify=on`: the resolver replaces this proc macro with the
///   compiler-owned `ExpandTrustInvariant` builtin before expansion, so the
///   body below never runs and the richer, span-accurate compiler diagnostic
///   is what the user sees. This function must keep EXISTING for that swap to
///   have something to resolve — deleting it would downgrade that diagnostic
///   to a bare E0433.
/// * stable Rust, or `-Z trust-verify=off`: no swap happens, this body runs,
///   and the `compile_error!` below is the refusal. MEASURED: compiletest runs
///   the `ui` suite with `-Z trust-verify=off`, so without this arm a bare
///   `#[trust::invariant(..)]` compiled clean with exit 0 — the erasure was
///   still fully live in every vanilla build.
///
/// A passthrough here would be the exact bug class this crate is meant not to
/// have: an annotation that looks like a specification, is accepted without
/// complaint, and contributes nothing.
#[proc_macro_attribute]
pub fn invariant(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // Emit the diagnostic AND re-emit the item, so the user gets one clear
    // error rather than a cascade of "cannot find type/function" follow-ons.
    let mut out: TokenStream = concat!(
        "compile_error!(\"`trust::invariant` is not a verified contract surface: it is never ",
        "checked on any lane, so it states a guarantee nothing enforces. For a loop invariant, ",
        "use a first-class loop clause: `while <cond> invariant <predicate> { ... }` or ",
        "`loop invariant <predicate> { ... }`. For a ",
        "condition that must hold on entry, use `#[trust::requires(<predicate>)]`. For a ",
        "condition that must hold on return, use `#[trust::ensures(move |r: &T| <predicate>)]`. ",
        "Otherwise delete the attribute: leaving it in place states nothing.\");",
    )
    .parse()
    .expect("the compile_error! invocation above is a string literal and must parse");
    out.extend(item);
    out
}

/// Compatibility termination-measure marker for a recursive function.
///
/// tRustc replaces this proc macro with a compiler-owned builtin that desugars
/// the annotation into the FIRST-CLASS clause `fn f(..) decreases <e>` — the
/// identical token stream an author writing the native clause would produce.
/// The two surfaces therefore share one parse, one AST lane and one lowering;
/// they cannot drift, because there is only one of them.
///
/// This export exists because WITHOUT it the compat surface deleted a working
/// clause: `#[trust::decreases(e)]` verifies with exactly native semantics on
/// the `register_tool(trust)` surface, while a crate that links this shim got
/// E0433 for the same source bytes (measured on trust-e26541e3). A crate that
/// must also build on stock Rust has no other spelling available, so the
/// termination measure was simply unwritable there.
///
/// THIS BODY MUST FAIL CLOSED, and that is not a theoretical concern — it was
/// MEASURED. `requires`/`ensures` may safely be passthroughs because EVERY
/// tRustc that has ever shipped substitutes a builtin for them, so the body
/// only ever runs in a non-verifying build. `decreases` is new, so a shim built
/// from this source can be handed to an OLDER toolchain that has no mapping for
/// it — and that is the normal configuration, not an exotic one: ay's
/// verification ratchet compiles `crates/trust-spec/src/lib.rs` with whatever
/// toolchain it is measuring (`trust_verification_ratchet_gate.sh`). Measured
/// with this file's export against the sealed `trust-e26541e3`:
///
///     #[trust::decreases(0)]   // a FALSE measure
///     fn g(n: u32) -> u32 { if n == 0 { 0 } else { g(n - 1) } }
///
/// compiled to `termination/proved` — bit-identical to the same function with
/// no clause at all, while the first-class `decreases 0` correctly refuses. The
/// passthrough had erased the measure and the function was then CREDITED. That
/// is precisely the fake-proof class this campaign exists to remove, and adding
/// the export without this guard would have introduced a fresh one.
///
/// So the expansion carries a marker that is a hard error EXACTLY when the body
/// running is a bug. `trust_verify` is injected by the compiler only when
/// verification is enabled, so:
///
///   * verification ON  + a toolchain that substitutes the builtin — this body
///     never runs at all and no marker exists;
///   * verification ON  + a toolchain that does NOT substitute it — the marker
///     survives cfg-stripping and the build fails, naming the mismatch,
///     instead of silently erasing the clause;
///   * verification OFF — the marker is stripped, the attribute is inert, and
///     nothing is checked or credited anyway.
#[proc_macro_attribute]
pub fn decreases(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut out = passthrough(attr, item);
    out.extend(
        r#"#[cfg(trust_verify)]
           ::core::compile_error!(
               "`#[trust::decreases]` reached the trust-spec compatibility \
                passthrough with verification ENABLED. This toolchain does not \
                substitute the compiler-owned `decreases` builtin, so the \
                termination measure would be silently ERASED and the function \
                credited as if it had been checked. Use a toolchain that maps \
                `trust::decreases`, or write the first-class clause \
                `fn f(..) decreases <e>`."
           );"#
            .parse::<TokenStream>()
            .expect("the marker is a string literal in this file and always parses"),
    );
    out
}
