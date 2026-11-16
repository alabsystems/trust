// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Trust (WS5.2, F-087 / F-092): `Function.name` IS the link-time symbol.
//!
//! trust-ir v41 ratified `Function.name` as the LINK-TIME SYMBOL and split the human def-path out
//! into `Function.display_path` (SPEC §1.1; `DuplicateFunctionSymbol` is the validator's
//! backstop). Until this module, the crate producer named every body by its `def_path_str` — a
//! display label that is not injective, is not what the object file exports, and is not what a
//! second crate's declaration of the same item says. Two emitted crates therefore could not link
//! by symbol, and a Clean island's `m::program` collided with a Rust `program` (F-092).
//!
//! Everything this module computes is computed ONCE, at crate finalization, where `tcx` is past
//! every `mir_built` (the E0391 re-entrancy family this producer keeps meeting forbids asking
//! `symbol_name` from inside the hook). Nothing here guesses a name: a body with no computable
//! symbol is REFUSED by name, and a declaration with no computable symbol is named by a reserved
//! spelling no linker can bind ([`unlinked_declaration_name`]).
//!
//! # Which instance a definition is
//!
//! Crate assembly lowers pre-monomorphization, one body per `DefIndex`, so a definition's
//! instance is its identity instance:
//!
//! * a `fn` / associated fn / constructor: `GenericArgs::identity_for_item`;
//! * a closure / coroutine / coroutine-closure body: the args of its OWN type,
//!   `type_of(def)` — NOT `identity_for_item`. A closure's generics carry three (a coroutine's
//!   five) synthetic own type parameters for the kind, signature and upvar tuple (see the
//!   `ExprKind::Closure` arm of `rustc_hir_analysis`'s `generics_of`), so the identity args of
//!   EVERY closure mention a type parameter and would refuse every closure. Those parameters are
//!   fixed by the closure's own definition, and `type_of` spells them concretely; what can still
//!   make a closure generic is its enclosing item, which the parent args then carry. (The WS5.2
//!   roadmap text says closures in non-generic parents have concrete IDENTITY args; that is the
//!   `requires_monomorphization` trap `trust_verify`'s R17 correction records, and it is
//!   corrected here rather than implemented.)
//!
//! If the instance still names a non-region parameter the definition is generic, the module is
//! monomorphic (SPEC §1), and no symbol exists: [`definition_link_symbol`] refuses. `splice_ok`
//! already refuses a generic body whose lowering MENTIONS a parameter (`symbolic`); a generic
//! body whose lowering never touches its parameters (`fn single_instance<T>(v: u32) -> u32`, or
//! a closure inside a generic item) used to splice under its def path and is refused here — each
//! caller links a different monomorphization, and this pre-monomorphization body is none of
//! them. A caller's edge to one of its instances is a declaration named by THAT instance's
//! symbol — with the one exception below.
//!
//! # RESIDUAL: the one place `Function.name` is not yet the link-time symbol
//!
//! A bodyless declaration of a concrete GENERIC instance of a local `fn` / associated fn — the
//! callee the D17 instance lane (`rustc_codegen_trust_cg`'s `instance_assembly.rs`) APPENDS at
//! codegen — keeps its PRE-WS5.2 spelling: its display path, or the pin's injective
//! `!trust_bodyless_instance::<path>::<definition>-<hex(key)>` collision form, with no
//! `display_path` ([`keeps_instance_lane_spelling`]). The frozen lane (D17,
//! `scripts/frozen-files.txt`, BYTE-IDENTICAL) assumes exactly that spelling twice: its append
//! refuses an instance body whose symbol another row already holds (a symbol-named declaration
//! of the same instance would be that row), and its relink accepts a host declaration only by
//! display path or collision form (`instance_admission::declaration_names_instance`). Naming
//! these rows by symbol would turn `tests/run-make/trust-cg-f1-generic-instance` from compiled to
//! refused; widening what the frozen files accept needs a reviewed waiver, so the open item is
//! `docs/OPEN_ISSUES.md` D17-DECL-SYMBOL-1 and this carve-out is its interim, fail-closed
//! answer: the instance lane behaves as at the pin, and such a row names no linkable identity (a
//! consumer binding by symbol cannot resolve it, the same reading as
//! [`unlinked_declaration_name`]).
//!
//! # Initializer bodies
//!
//! A `{const-init}` / `{static-init}` body is never a link target (nothing calls an initializer
//! by symbol), so it gets the reserved, charset-safe `__trust_init_<stable definition hex>`
//! spelling and `Linkage::Internal`; its human path goes to `display_path`.

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;

/// The coverage tag prefix of a body refused for having no link-time symbol.
pub const NO_LINK_SYMBOL_TAG: &str = "NoLinkTimeSymbol(";

/// The coverage tag prefix of a body refused because a call edge it mints names a link symbol
/// another row of the same module already holds (see [`symbol_collision_reason`]).
pub const LINK_SYMBOL_COLLISION_TAG: &str = "LinkSymbolCollision(";

/// The reserved prefix of an initializer body's name. `__` + an ASCII tag + hex: inside every
/// measured mangling alphabet, outside every Rust mangling scheme's grammar (`_R`, `_ZN`), so
/// it can neither be mistaken for nor collide with a real symbol.
pub const INITIALIZER_SYMBOL_PREFIX: &str = "__trust_init_";

/// The reserved prefix of a declaration whose callee has no computable link-time symbol. It
/// begins with `!`, which no symbol mangling emits, so a consumer binding by symbol can never
/// resolve it — the fail-closed reading of "this edge names no linkable identity".
pub const UNLINKED_DECLARATION_PREFIX: &str = "!trust_unlinked_callee::";

/// The named refusal for a body with no computable link-time symbol.
pub fn no_link_symbol_reason(def_path: &str, why: &str) -> String {
    format!(
        "{NO_LINK_SYMBOL_TAG}{def_path}): no link-time symbol for `{def_path}`: the trust-ir \
         module is monomorphic (SPEC §1) — {why}. The body is refused (lowered for coverage, \
         never spliced): `Function.name` is the link-time symbol, and a name the object file \
         does not export would be a guess. Options: call it from a non-generic item so the \
         instance a caller uses is the one this crate module could name, or wait for per-instance \
         lowering (B8), which gives each monomorphization its own body."
    )
}

/// The named per-body refusal for a call edge whose declaration would claim a link symbol that
/// another row already holds.
pub(crate) fn symbol_collision_reason(symbol: &str, callee: &str, holder: &str) -> String {
    format!(
        "{LINK_SYMBOL_COLLISION_TAG}{symbol}): this body mints a call edge to bodyless \
         declaration `{callee}`, whose link-time symbol `{symbol}` is already held by {holder}. \
         `Function.name` is the link-time symbol, so one symbol names at most one row \
         (`DuplicateFunctionSymbol`); the producer spelled this callee two ways (for example two \
         observed result types, `|ret:`, or two result arities, `|nres:`) and cannot tell which \
         spelling is the callee's, so it refuses every body minting a colliding edge instead of \
         picking one. The rest of the crate module is assembled and validated. Options: report \
         the pair of spellings (a producer inconsistency), or restructure the call so both sites \
         bind the result the same way."
    )
}

/// The instance args of a definition's IDENTITY instance, or why there is no such instance.
/// See the module docs for why a closure-family body reads its own type instead of
/// `identity_for_item`.
fn definition_instance_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Result<ty::GenericArgs<'tcx>, String> {
    match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(..) => {
            Ok(ty::GenericArgs::identity_for_item(tcx, def_id))
        }
        DefKind::Closure | DefKind::SyntheticCoroutineBody => {
            match tcx.type_of(def_id).instantiate_identity().skip_normalization().kind() {
                ty::Closure(_, args) | ty::Coroutine(_, args) | ty::CoroutineClosure(_, args) => {
                    Ok(*args)
                }
                other => Err(format!(
                    "the closure-family body's own type is `{other:?}`, not a closure, coroutine \
                     or coroutine-closure, so there is no instance to name"
                )),
            }
        }
        other => Err(format!("a `{other:?}` definition exports no function symbol")),
    }
}

/// `tcx.symbol_name` of a definition's identity instance, or the named refusal.
///
/// `Err` is the full [`no_link_symbol_reason`] text; the caller records it as the body's
/// unsupported reason, so coverage says exactly why the body is absent.
pub fn definition_link_symbol(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    def_path: &str,
) -> Result<String, String> {
    let args = definition_instance_args(tcx, def_id)
        .map_err(|why| no_link_symbol_reason(def_path, &why))?;
    if args.has_non_region_param() {
        return Err(no_link_symbol_reason(
            def_path,
            "the definition's instance still names a generic type or const parameter, so each \
             caller links a different monomorphization and this pre-monomorphization body is \
             none of them",
        ));
    }
    if args.has_infer() || args.has_escaping_bound_vars() {
        return Err(no_link_symbol_reason(
            def_path,
            "the definition's instance args are not fully resolved (inference variables or \
             escaping bound variables remain)",
        ));
    }
    // Trust (1.101): an always-const fn (`const fn` under `const fn` stability
    // attributes such as `#[rustc_const_stable_indirect]`-adjacent always-const
    // items) never reaches codegen, so it HAS no link symbol; upstream's
    // `symbol_name` now debug-asserts exactly that. Refuse with the reason
    // instead of asking.
    if matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) && matches!(tcx.constness(def_id), rustc_hir::Constness::Const { always: true })
    {
        return Err(no_link_symbol_reason(
            def_path,
            "the definition is an always-const fn, which is comptime-only and has no link symbol",
        ));
    }
    let args = tcx.erase_and_anonymize_regions(args);
    Ok(tcx.symbol_name(ty::Instance::new_raw(def_id, args)).name.to_string())
}

/// `tcx.symbol_name` of the exact resolved instance a ledgered call edge names, or `None` when
/// the ledger does not name one this producer can compute.
///
/// Two sources, each exact:
///
/// * a CONCRETE KEY of kind `Item` with its re-materializable args — the resolved instance;
/// * no concrete key, but a LOCAL, non-forced-havoc callee: the ledger admits those edges only
///   for a closure called directly (`admit_closure_callee`) or a local fn lane without site
///   args, and in a body that can splice (a non-generic one) such an edge names the callee's
///   IDENTITY instance — exactly [`definition_link_symbol`]'s. A forced-havoc edge is generic or
///   opaque at the site and gets nothing.
///
/// `None` is not a refusal of the edge — the edge was already fail-closed as a bodyless
/// declaration — it means the declaration is named [`unlinked_declaration_name`] rather than by
/// a symbol this producer would have to guess. The cases: an unresolved, polymorphic, `dyn` or
/// synthetic havoc edge, a reify shim (its symbol also depends on the `ReifyReason`, which the
/// key does not carry), an instance that still names a parameter, or args that do not
/// re-materialize — and, RESIDUAL, a callee [`keeps_instance_lane_spelling`] answers `true` for:
/// that row is named by its pre-WS5.2 spelling, so it claims no symbol.
pub(crate) fn callee_link_symbol(tcx: TyCtxt<'_>, callee: &crate::CalleeRef) -> Option<String> {
    if keeps_instance_lane_spelling(tcx, callee) {
        return None;
    }
    let Some(key) = callee.concrete_key.as_ref() else {
        if callee.is_local && !callee.force_havoc {
            return definition_link_symbol(tcx, callee.def_id, &callee.def_path).ok();
        }
        return None;
    };
    if key.instance_kind() != crate::lineage::ConcreteInstanceKind::Item {
        return None;
    }
    // Trust (1.101): an always-const callee has no link symbol (see
    // `definition_link_symbol`); the declaration keeps its unlinked name.
    if matches!(
        tcx.def_kind(callee.def_id),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) && matches!(tcx.constness(callee.def_id), rustc_hir::Constness::Const { always: true })
    {
        return None;
    }
    let encoded = callee.instance_args.as_ref()?;
    let args = crate::to_mir::rebuild_site_args(tcx, encoded)?;
    if args.has_non_region_param() || args.has_infer() || args.has_escaping_bound_vars() {
        return None;
    }
    Some(tcx.symbol_name(ty::Instance::new_raw(callee.def_id, args)).name.to_string())
}

/// The six facts [`keeps_instance_lane_spelling`] decides on, read from `tcx` and the ledger.
/// Plain booleans so the decision itself, [`instance_lane_spelling_applies`], is TyCtxt-free and
/// its whole truth table is pinned by a unit test.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct InstanceLaneFacts {
    /// The callee definition is in the crate being compiled.
    pub local: bool,
    /// The ledger names the edge by a concrete key of kind `Item` (not a reify shim, not an
    /// unresolved, `dyn` or opaque havoc edge).
    pub item_instance: bool,
    /// `DefKind::Fn` or `DefKind::AssocFn` (no closure, coroutine or constructor).
    pub fn_or_assoc_fn: bool,
    /// A foreign (`extern` block) item.
    pub foreign: bool,
    /// `generics_of(def).requires_monomorphization(tcx)`: every instance of it carries a type or
    /// const argument.
    pub requires_monomorphization: bool,
    /// One of this crate's Clean-origin defs.
    pub clean_origin: bool,
}

/// Trust (WS5.2 NARROWED — RESIDUAL, `docs/DECISION_QUEUE.md` D17-DECL-SYMBOL-1, open for the
/// owner): THE DECISION of [`keeps_instance_lane_spelling`], TyCtxt-free.
///
/// `true` for exactly one shape: the edge names an `Item` instance of a LOCAL, non-foreign,
/// non-Clean-origin `fn` / associated fn that requires monomorphization. That is the callee the
/// frozen D17 lane APPENDS (`instance_assembly.rs`, `Assembler::assemble`: a plain `Item`, local,
/// not foreign, `Fn`/`AssocFn`, args not all regions; `instance_admission` refuses a Clean-origin
/// def), and the only declaration its relink consults on a path that can succeed: a monomorphic
/// local callee is linked to its handoff body directly, never through a declaration, and every
/// other callee shape refuses the edge whatever the declaration is named. Each conjunct only
/// NARROWS the carve-out; a row outside it keeps WS5.2's symbol (or reserved unlinked) name. The
/// Clean-origin exclusion keeps the Clean join's binding of a Clean def's declaration by its
/// link-time symbol (`clean_origin_join`'s `declaration_slot`) untouched.
pub(crate) fn instance_lane_spelling_applies(facts: InstanceLaneFacts) -> bool {
    facts.local
        && facts.item_instance
        && facts.fn_or_assoc_fn
        && !facts.foreign
        && facts.requires_monomorphization
        && !facts.clean_origin
}

/// Trust (WS5.2 NARROWED — RESIDUAL, `docs/DECISION_QUEUE.md` D17-DECL-SYMBOL-1): does a bodyless
/// declaration of `callee` keep its PRE-WS5.2 spelling — its display path, or the pin's injective
/// `!trust_bodyless_instance::` collision form, with no `display_path` — instead of a link-time
/// symbol? See the module docs ("RESIDUAL") for why, and [`instance_lane_spelling_applies`] for
/// the shape. Such a row claims no symbol ([`callee_link_symbol`] answers `None`), so it is never
/// a party to a symbol collision and binds to no definition by symbol.
///
/// The queries run only once the TyCtxt-free conjuncts hold (a local `Item` edge), so nothing is
/// asked of a definition outside the population the carve-out can name.
pub(crate) fn keeps_instance_lane_spelling(tcx: TyCtxt<'_>, callee: &crate::CalleeRef) -> bool {
    let def_id = callee.def_id;
    let local = def_id.is_local();
    let item_instance = callee
        .concrete_key
        .as_ref()
        .is_some_and(|key| key.instance_kind() == crate::lineage::ConcreteInstanceKind::Item);
    if !(local && item_instance) {
        return false;
    }
    let fn_or_assoc_fn = matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn);
    if !fn_or_assoc_fn {
        return false;
    }
    instance_lane_spelling_applies(InstanceLaneFacts {
        local,
        item_instance,
        fn_or_assoc_fn,
        foreign: tcx.is_foreign_item(def_id),
        requires_monomorphization: tcx.generics_of(def_id).requires_monomorphization(tcx),
        clean_origin: declaration_producer(tcx, def_id) == Some(trust_ir::Producer::Clean),
    })
}

/// Trust (WS5.2): name an emitted Clean-origin Function by the LINK-TIME SYMBOL of the Rust item
/// it defines, moving the emitter's Lean spelling (`declaration_symbol`) to `display_path`.
///
/// A Clean-origin row IS the definition of a Rust item this crate minted from the island, so its
/// symbol is that item's symbol — which is also what a Rust caller's declaration of the item is
/// named, and what makes the island's `m::program` and a Rust `program` two different rows
/// (F-092). Done at EMISSION, before the carrier gate mints its token, so the private token
/// authenticates the final Function (name included). `Err` if the emitter already filled
/// `display_path` (the Lean spelling would be lost) or left the name empty.
pub fn bind_clean_origin_link_symbol(
    function: &mut trust_ir::Function,
    link_symbol: &str,
) -> Result<(), String> {
    if function.display_path.is_some() {
        return Err(format!(
            "the emitted Clean-origin function `{}` already carries a display path; binding its \
             Rust link-time symbol would overwrite it",
            function.name
        ));
    }
    if function.name.is_empty() || link_symbol.is_empty() {
        return Err("an empty Clean-origin name or link-time symbol names nothing".to_string());
    }
    let lean = std::mem::replace(&mut function.name, link_symbol.to_string());
    function.display_path = Some(lean);
    Ok(())
}

/// The reserved name of an initializer body (see the module docs).
pub(crate) fn initializer_symbol(definition: crate::lineage::DefinitionIdentity) -> String {
    format!("{INITIALIZER_SYMBOL_PREFIX}{}", definition.symbol_suffix())
}

/// The reserved, never-linkable name of a declaration whose callee has no computable link-time
/// symbol. Injective over what identifies a declaration row: its dedup key (hex-encoded in
/// full, so no key text is ever read as path syntax) AND its stable definition identity, which
/// the key alone does not carry for a concrete-key-less row (two macro-generated items can share
/// a display path, hence a key, while being two definitions).
pub(crate) fn unlinked_declaration_name(
    decl_key: &str,
    definition: Option<crate::lineage::DefinitionIdentity>,
) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out =
        String::with_capacity(UNLINKED_DECLARATION_PREFIX.len() + decl_key.len() * 2 + 40);
    out.push_str(UNLINKED_DECLARATION_PREFIX);
    for byte in decl_key.bytes() {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out.push_str("::");
    match definition {
        Some(definition) => out.push_str(&definition.symbol_suffix()),
        None => out.push_str("unknown"),
    }
    out
}

/// The REAL producer of a bodyless declaration's callee, or `None` when it is not recorded.
///
/// * a LOCAL callee is this crate's own item, so it is produced by the Clean compiler exactly
///   when it is one of this crate's Clean-origin defs, and by this Rust producer otherwise;
/// * a NON-LOCAL callee is `Clean` exactly when its crate lists it in
///   `trust_clean_origin_exports` (rmeta, the I7 export row);
/// * any other non-local callee is `None` — UNRECORDED, never guessed. `TRust` is earned only by
///   a dependency that published a trust-ir identity row (WS5.8), which no dependency does yet.
///   Until this module, every declaration was stamped `TRust`, which `validate_linked_module`
///   would refuse as `ProducerMismatch` the moment an import row named a Clean export.
pub(crate) fn declaration_producer(tcx: TyCtxt<'_>, callee: DefId) -> Option<trust_ir::Producer> {
    match callee.as_local() {
        Some(local) => {
            let is_clean_origin = tcx
                .resolutions(())
                .clean_origin_defs
                .iter()
                .any(|&(clean_def, _, _)| clean_def == local);
            Some(if is_clean_origin {
                trust_ir::Producer::Clean
            } else {
                trust_ir::Producer::TRust
            })
        }
        None => tcx
            .trust_clean_origin_exports(callee.krate)
            .contains(&callee.index)
            .then_some(trust_ir::Producer::Clean),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unlinked_declaration_names_are_injective_and_never_symbols() {
        let d1 = crate::lineage::DefinitionIdentity::test_only(1, 1);
        let d2 = crate::lineage::DefinitionIdentity::test_only(1, 2);
        let a = unlinked_declaration_name("havoc:core::ops::Fn::call", Some(d1));
        let b = unlinked_declaration_name("havoc:core::ops::Fn::call|nres:1", Some(d1));
        let c = unlinked_declaration_name("havoc:core::ops::Fn::call", Some(d2));
        assert_ne!(a, b, "two dedup keys must never share a reserved name");
        assert_ne!(a, c, "two definitions sharing a key must never share a reserved name");
        for name in [&a, &b, &c] {
            assert!(name.starts_with('!'), "`!` is outside every mangling alphabet: {name}");
            assert!(
                !name.contains("::core::"),
                "the reserved name carries no def-path text a reader could mistake for a symbol"
            );
        }
    }

    #[test]
    fn initializer_symbols_are_reserved_and_charset_safe() {
        let symbol = initializer_symbol(crate::lineage::DefinitionIdentity::test_only(1, 2));
        assert!(symbol.starts_with(INITIALIZER_SYMBOL_PREFIX));
        assert!(
            symbol.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'),
            "an initializer symbol stays inside the link-symbol alphabet: {symbol}"
        );
        assert_ne!(symbol, initializer_symbol(crate::lineage::DefinitionIdentity::test_only(1, 3)));
    }

    /// RESIDUAL PIN (D17-DECL-SYMBOL-1): the carve-out from WS5.2 symbol naming applies to
    /// EXACTLY ONE of the 64 fact combinations — a local `Item` instance of a non-foreign,
    /// non-Clean-origin `fn`/associated fn that requires monomorphization. Dropping any conjunct
    /// (widening the carve-out) or adding one that the shape satisfies differently turns this red.
    #[test]
    fn the_instance_lane_spelling_applies_to_exactly_one_fact_combination() {
        let mut admitted = Vec::new();
        for bits in 0u8..64 {
            let facts = InstanceLaneFacts {
                local: bits & 1 != 0,
                item_instance: bits & 2 != 0,
                fn_or_assoc_fn: bits & 4 != 0,
                foreign: bits & 8 != 0,
                requires_monomorphization: bits & 16 != 0,
                clean_origin: bits & 32 != 0,
            };
            if instance_lane_spelling_applies(facts) {
                admitted.push(facts);
            }
        }
        assert_eq!(
            admitted,
            vec![InstanceLaneFacts {
                local: true,
                item_instance: true,
                fn_or_assoc_fn: true,
                foreign: false,
                requires_monomorphization: true,
                clean_origin: false,
            }],
            "the carve-out must stay the D17 lane's appendable callee and nothing wider"
        );
    }

    #[test]
    fn the_refusals_name_their_tag_and_subject() {
        let reason = no_link_symbol_reason("k::id", "generic");
        assert!(reason.starts_with("NoLinkTimeSymbol(k::id): no link-time symbol for `k::id`"));
        assert!(reason.contains("the trust-ir module is monomorphic (SPEC §1)"));
        let collision = symbol_collision_reason("_RNvCs0_1k1f", "k::f", "FuncId 3");
        assert!(collision.starts_with("LinkSymbolCollision(_RNvCs0_1k1f): "));
        assert!(collision.contains("`k::f`") && collision.contains("FuncId 3"));
    }
}
