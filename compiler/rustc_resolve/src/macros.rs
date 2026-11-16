//! A bunch of methods and structures more or less related to resolving macros and
//! interface provided by `Resolver` to macro expander.

use std::mem;
use std::sync::Arc;

use rustc_ast::{self as ast, Crate, DelegationSuffixes, NodeId};
use rustc_ast_pretty::pprust;
use rustc_attr_ir::{Attribute, AttributeKind, CfgEntry, StabilityLevel, StrippedCfgItem};
use rustc_attr_parsing::AttributeParser;
use rustc_data_structures::sync::RwLock;
use rustc_errors::{Applicability, StashKey};
use rustc_expand::base::{
    Annotatable, DeriveResolution, Indeterminate, ResolverExpand, SyntaxExtension,
    SyntaxExtensionKind,
};
use rustc_expand::compile_declarative_macro;
use rustc_expand::expand::{
    AstFragment, AstFragmentKind, Invocation, InvocationKind, SupportsMacroExpansion,
};
use rustc_hir::def::{DefKind, MacroKinds, Namespace, NonMacroAttrKind};
use rustc_hir::def_id::{CrateNum, DefId, LocalDefId};
use rustc_hir::definitions::{DefPath, DefPathData};
use rustc_lint_defs::builtin::{
    LEGACY_DERIVE_HELPERS, OUT_OF_SCOPE_MACRO_CALLS, UNUSED_MACRO_RULES, UNUSED_MACROS,
};
use rustc_middle::middle::stability;
use rustc_middle::ty::{RegisteredTools, TyCtxt};
use rustc_session::Session;
use rustc_session::diagnostics::feature_err;
use rustc_span::def_id::ModId;
use rustc_span::edition::Edition;
use rustc_span::hygiene::{self, AstPass, ExpnData, ExpnKind, LocalExpnId, MacroKind};
use rustc_span::{DUMMY_SP, Ident, Span, Symbol, kw, sym};
// Trust (E5 conservation): the reserved `trust::` attribute vocabulary, derived
// from the code that CONSUMES each name. See the check in `smart_resolve_macro_path`.
use trust_types::trust_attr_namespace::{
    TrustAttrVerdict, classify_trust_attr_path, vocabulary_list,
};

use crate::Namespace::*;
use crate::def_collector::collect_definitions;
use crate::diagnostics::{
    self, AddAsNonDerive, CannotDetermineMacroResolution, CannotFindIdentInThisScope,
    MacroExpectedFound, RemoveSurroundingDerive,
};
use crate::hygiene::Macros20NormalizedSyntaxContext;
use crate::imports::Import;
use crate::{
    BindingKey, CmResolver, Decl, DeclKind, DeriveData, Determinacy, Finalize, IdentKey,
    InvocationParent, ModuleKind, ModuleOrUniformRoot, ParentScope, PathResult, Res,
    ResolutionError, Resolver, ScopeSet, Segment, Used,
};

/// Name declaration produced by a `macro_rules` item definition.
/// Not modularized, can shadow previous `macro_rules` definitions, etc.
#[derive(Debug)]
pub(crate) struct MacroRulesDecl<'ra> {
    pub(crate) decl: Decl<'ra>,
    /// `macro_rules` scope into which the `macro_rules` item was planted.
    pub(crate) parent_macro_rules_scope: MacroRulesScopeRef<'ra>,
    pub(crate) ident: IdentKey,
    pub(crate) orig_ident_span: Span,
}

/// The scope introduced by a `macro_rules!` macro.
/// This starts at the macro's definition and ends at the end of the macro's parent
/// module (named or unnamed), or even further if it escapes with `#[macro_use]`.
/// Some macro invocations need to introduce `macro_rules` scopes too because they
/// can potentially expand into macro definitions.
#[derive(Copy, Clone, Debug)]
pub(crate) enum MacroRulesScope<'ra> {
    /// Empty "root" scope at the crate start containing no names.
    Empty,
    /// The scope introduced by a `macro_rules!` macro definition.
    Def(&'ra MacroRulesDecl<'ra>),
    /// The scope introduced by a macro invocation that can potentially
    /// create a `macro_rules!` macro definition.
    Invocation(LocalExpnId),
}

/// `macro_rules!` scopes are always kept by reference and inside a cell.
/// The reason is that we update scopes with value `MacroRulesScope::Invocation(invoc_id)`
/// in-place after `invoc_id` gets expanded.
/// This helps to avoid uncontrollable growth of `macro_rules!` scope chains,
/// which usually grow linearly with the number of macro invocations
/// in a module (including derives) and hurt performance.
pub(crate) type MacroRulesScopeRef<'ra> = &'ra RwLock<MacroRulesScope<'ra>>;

/// Macro namespace is separated into two sub-namespaces, one for bang macros and
/// one for attribute-like macros (attributes, derives).
/// We ignore resolutions from one sub-namespace when searching names in scope for another.
pub(crate) fn sub_namespace_match(
    candidate: Option<MacroKinds>,
    requirement: Option<MacroKind>,
) -> bool {
    // "No specific sub-namespace" means "matches anything" for both requirements and candidates.
    let (Some(candidate), Some(requirement)) = (candidate, requirement) else {
        return true;
    };
    match requirement {
        MacroKind::Bang => candidate.contains(MacroKinds::BANG),
        MacroKind::Attr | MacroKind::Derive => {
            candidate.intersects(MacroKinds::ATTR | MacroKinds::DERIVE)
        }
    }
}

// We don't want to format a path using pretty-printing,
// `format!("{}", path)`, because that tries to insert
// line-breaks and is slow.
fn fast_print_path(path: &ast::Path) -> Symbol {
    if let [segment] = path.segments.as_slice() {
        segment.ident.name
    } else {
        let mut path_str = String::with_capacity(64);
        for (i, segment) in path.segments.iter().enumerate() {
            if i != 0 {
                path_str.push_str("::");
            }
            if segment.ident.name != kw::PathRoot {
                path_str.push_str(segment.ident.as_str())
            }
        }
        Symbol::intern(&path_str)
    }
}

// Trust: `trust` is predefined for the same reason `clippy` is — it is a tool
// this compiler ships, not a crate the user is expected to depend on. Before
// this, an armed `#[trust::skip]` / `#[trust::assume_total]` / … was
// `E0433: cannot find module or crate 'trust'` in every crate that had not
// hand-written `#![feature(register_tool)] #![register_tool(trust)]`, so the
// verify pass's own opt-out and assumption vocabulary was unusable in exactly
// the third-party-shaped crates that need it (measured: ay's `ay-dpll`,
// `ay-encode`, `ay-sat`).
//
// This does NOT shadow the contract attributes. `trust::requires`/`ensures`/
// `decreases`/`invariant` are resolved as MACROS against an external crate
// named `trust` (the `trust-spec` passthrough shim), which the resolver then
// replaces with the compiler-owned contract builtins — see
// `trust_spec_contract_attr_extension`. Macro resolution wins over tool-attribute
// inertness: measured on a crate carrying BOTH `#![register_tool(trust)]` and
// `--extern trust=<shim>`, `#[trust::invariant(false)]` still reaches the
// `ExpandTrustInvariant` refusal. That precedence is structural, not a
// coincidence to be re-measured: the scope walk in `ident.rs` visits
// `ExternPreludeItems` -> `ExternPreludeFlags` -> `ToolPrelude`, so an extern
// crate named `trust` is found FIRST and the tool binding is never reached.
// It is also why `first-party/ny`'s 88 `#[trust::cite(..)]` sites keep
// working — ny's `trust` is `package = "ny-contracts"`, an ordinary
// extern-prelude proc-macro crate.
//
// Tool registration only decides what happens to a `trust::` path that
// resolves to no macro at all, which used to be a hard E0433 and is now an
// inert tool attribute. The one exception is `trust::requires`/`ensures`
// under verification: `trust_tool_contract_attr_extension` gives those the
// same builtins the shim surface gets, so both spellings reach ONE contract
// grammar (2026-09-29). Registering the tool REQUIRES the
// companion E5 conservation check in `smart_resolve_macro_path` below.
// Without it, a misspelled or unsupported `#[trust::…]` would be silently
// inert, which is strictly worse than the error it replaced. The two are ONE
// change and must not be separated.
const PREDEFINED_TOOLS: &[Symbol] =
    &[sym::clippy, sym::rustfmt, sym::diagnostic, sym::miri, sym::rust_analyzer, sym::trust];

pub(crate) fn registered_attr_tools(tcx: TyCtxt<'_>, (): ()) -> RegisteredTools {
    let (_, pre_configured_attrs) = &*tcx.crate_for_resolver(()).borrow();

    let mut registered_tools =
        if let Some(Attribute::Parsed(AttributeKind::RegisterTool { attr_tools, .. })) =
            AttributeParser::parse_limited(tcx.sess, pre_configured_attrs, &|attr| {
                attr.path_matches(&[sym::register_tool])
                    || attr.path_matches(&[sym::register_attribute_tool])
            })
        {
            attr_tools.into_iter().collect::<RegisteredTools>()
        } else {
            Default::default()
        };

    // We implicitly add predefined tools, but it's not an error to register them explicitly.
    registered_tools.extend(PREDEFINED_TOOLS.iter().cloned().map(Ident::with_dummy_span));
    registered_tools
}

pub(crate) fn registered_lint_tools(tcx: TyCtxt<'_>, (): ()) -> RegisteredTools {
    let (_, pre_configured_attrs) = &*tcx.crate_for_resolver(()).borrow();
    registered_lint_tools_ast(tcx.sess, pre_configured_attrs)
}

pub fn registered_lint_tools_ast(
    sess: &Session,
    pre_configured_attrs: &[ast::Attribute],
) -> RegisteredTools {
    let mut registered_tools =
        if let Some(Attribute::Parsed(AttributeKind::RegisterTool { lint_tools, .. })) =
            AttributeParser::parse_limited(sess, pre_configured_attrs, &|attr| {
                attr.path_matches(&[sym::register_tool])
                    || attr.path_matches(&[sym::register_lint_tool])
            })
        {
            lint_tools.into_iter().collect::<RegisteredTools>()
        } else {
            Default::default()
        };

    // We implicitly add predefined tools, but it's not an error to register them explicitly.
    registered_tools.extend(PREDEFINED_TOOLS.iter().cloned().map(Ident::with_dummy_span));
    registered_tools
}

impl<'ra, 'tcx> ResolverExpand for Resolver<'ra, 'tcx> {
    fn next_node_id(&mut self) -> NodeId {
        self.next_node_id()
    }

    fn invocation_parent(&self, id: LocalExpnId) -> LocalDefId {
        self.invocation_parents[&id].parent_def
    }

    fn mark_scope_with_compile_error(&mut self, id: NodeId) {
        if let Some(id) = self.owners.get(&id).map(|i| i.def_id)
            && self.tcx.def_kind(id).is_module_like()
        {
            self.mods_with_parse_errors.insert(id.to_def_id());
        }
    }

    fn resolve_dollar_crates(&self) {
        hygiene::update_dollar_crate_names(|ctxt| {
            let ident = Ident::new(kw::DollarCrate, DUMMY_SP.with_ctxt(ctxt));
            self.resolve_crate_root(ident).name().unwrap_or(kw::Crate)
        });
    }

    fn visit_ast_fragment_with_placeholders(
        &mut self,
        expansion: LocalExpnId,
        fragment: &AstFragment,
    ) {
        // Trust (I5): decide the Clean-origin mints BEFORE def collection.
        //
        // This is `MacroExpander::collect_invocations`'s call into the resolver
        // — i.e. after `fragment.mut_visit_with(&mut InvocationCollector)` has
        // renumbered every `CleanIslandDecl::node_id` off `DUMMY_NODE_ID`, and
        // immediately before `collect_definitions` runs. `def_collector` cannot
        // evaluate the three mint preconditions itself: they are facts about
        // the crate's Clean environment, which has to be checked as ONE
        // header-first batch.
        //
        // ROOT `AstFragment::Crate` ONLY. `trust_clean_mint::decide` returns the
        // empty decision for every other fragment, so an island introduced by a
        // later macro expansion mints nothing and its declarations never enter
        // the value namespace — the ordinary `E0425`, which is the fail-closed
        // answer. See that module's docs for why widening this is a design
        // question rather than an implementation gap.
        //
        // The root check is spelled at the call site as well as inside
        // `decide`, so a reader of either one sees it.
        if matches!(fragment, AstFragment::Crate(_)) {
            // Trust: a rejected island batch is REPORTED at this seam (see
            // `decide`'s docs): the verify pass that used to be relied on for
            // that never runs once the withheld mint has produced an `E0425`.
            self.clean_origin_mints =
                crate::trust_clean_mint::decide(self.tcx.sess, self.tcx.dcx(), fragment);
            // Trust (I6): a grant whose signature carries `Nat` depends on the
            // `trust_bignum` carrier crate. Load it NOW — before
            // `collect_definitions` feeds any signature — and demote those
            // grants to v7/D3 refusals if it cannot be loaded. Exact trigger:
            // no `Nat`-carrying grant, no load. See the method's docs.
            self.trust_resolve_carrier_crates();
        }

        // Integrate the new AST fragment into all the definition and module structures.
        // We are inside the `expansion` now, but other parent scope components are still the same.
        let parent_scope = ParentScope { expansion, ..self.invocation_parent_scopes[&expansion] };
        let output_macro_rules_scope = collect_definitions(self, fragment, parent_scope);
        self.output_macro_rules_scopes.insert(expansion, output_macro_rules_scope);

        let module = parent_scope.module.expect_local();
        module.unexpanded_invocations.borrow_mut(self).remove(&expansion);
        if let Some(unexpanded_invocations) =
            self.impl_unexpanded_invocations.get_mut(&self.invocation_parent(expansion))
        {
            unexpanded_invocations.remove(&expansion);
        }
    }

    fn register_builtin_macro(&mut self, name: Symbol, ext: SyntaxExtensionKind) {
        if self.builtin_macros.insert(name, ext).is_some() {
            self.dcx().bug(format!("built-in macro `{name}` was already registered"));
        }
    }

    // Create a new Expansion with a definition site of the provided module, or
    // a fake empty `#[no_implicit_prelude]` module if no module is provided.
    fn expansion_for_ast_pass(
        &mut self,
        call_site: Span,
        pass: AstPass,
        features: &[Symbol],
        parent_module_id: Option<NodeId>,
    ) -> LocalExpnId {
        let parent_module = parent_module_id
            .map(|module_id| ModId::new_unchecked(self.owner_def_id(module_id).to_def_id()));
        let expn_id = self.tcx.with_stable_hashing_context(|hcx| {
            LocalExpnId::fresh(
                ExpnData::allow_unstable(
                    ExpnKind::AstPass(pass),
                    call_site,
                    self.tcx.sess.edition(),
                    features.into(),
                    None,
                    parent_module,
                ),
                hcx,
            )
        });

        let parent_scope = parent_module.map_or(self.empty_module, |mod_id| {
            self.expect_module(mod_id.to_def_id()).expect_local()
        });
        self.ast_transform_scopes.insert(expn_id, parent_scope);

        expn_id
    }

    fn resolve_imports(&mut self) {
        self.resolve_imports()
    }

    fn resolve_macro_invocation(
        &mut self,
        invoc: &Invocation,
        eager_expansion_root: LocalExpnId,
        force: bool,
    ) -> Result<Arc<SyntaxExtension>, Indeterminate> {
        let invoc_id = invoc.expansion_data.id;
        let (parent_scope, invocation_parent) = match (
            self.invocation_parent_scopes.get(&invoc_id),
            self.invocation_parents.get(&invoc_id),
        ) {
            (Some(parent_scope), Some(invocation_parent)) => (*parent_scope, *invocation_parent),
            (None, None) => {
                // Eager macro invocations are not collected into the reduced graph, so they
                // inherit their parent scope and invocation parent from the eager expansion root -
                // the macro that requested this eager expansion.
                let parent_scope = *self
                    .invocation_parent_scopes
                    .get(&eager_expansion_root)
                    .expect("non-eager expansion without a parent scope");
                let invocation_parent = *self
                    .invocation_parents
                    .get(&eager_expansion_root)
                    .expect("non-eager expansion without an invocation parent");
                self.invocation_parent_scopes.insert(invoc_id, parent_scope);
                self.invocation_parents.insert(invoc_id, invocation_parent);
                (parent_scope, invocation_parent)
            }
            _ => unreachable!(
                "invocation parent tables must both contain or both miss an invocation"
            ),
        };

        let (mut derives, mut inner_attr, mut deleg_impl) = (&[][..], false, None);
        let (path, kind) = match invoc.kind {
            InvocationKind::Attr { ref attr, derives: ref attr_derives, .. } => {
                derives = self.arenas.alloc_ast_paths(attr_derives);
                inner_attr = attr.style == ast::AttrStyle::Inner;
                (&attr.get_normal_item().path, MacroKind::Attr)
            }
            InvocationKind::Bang { ref mac, .. } => (&mac.path, MacroKind::Bang),
            InvocationKind::Derive { ref path, .. } => (path, MacroKind::Derive),
            InvocationKind::GlobDelegation { ref item, .. } => {
                let ast::AssocItemKind::DelegationMac(deleg) = &item.kind else { unreachable!() };
                let DelegationSuffixes::Glob(star_span) = deleg.suffixes else { unreachable!() };
                deleg_impl = Some((invocation_parent.parent_def, star_span));
                // It is sufficient to consider glob delegation a bang macro for now.
                (&deleg.prefix, MacroKind::Bang)
            }
        };

        // Derives are not included when `invocations` are collected, so we have to add them here.
        let parent_scope = &ParentScope { derives, ..parent_scope };
        let supports_macro_expansion = invoc.fragment_kind.supports_macro_expansion();
        let node_id = invoc.expansion_data.lint_node_id;
        // This is a heuristic, but it's good enough for the lint.
        let looks_like_invoc_in_mod_inert_attr = Some(invocation_parent)
            .filter(|&InvocationParent { parent_def: mod_def_id, in_attr, .. }| {
                in_attr
                    && invoc.fragment_kind == AstFragmentKind::Expr
                    && self.tcx.def_kind(mod_def_id) == DefKind::Mod
            })
            .map(|InvocationParent { parent_def: mod_def_id, .. }| mod_def_id);
        let sugg_span = match &invoc.kind {
            InvocationKind::Attr { item: Annotatable::Item(item), .. }
                if !item.span.from_expansion() =>
            {
                Some(item.span.shrink_to_lo())
            }
            _ => None,
        };
        let (ext, res) = self.smart_resolve_macro_path(
            path,
            kind,
            supports_macro_expansion,
            inner_attr,
            parent_scope,
            node_id,
            force,
            deleg_impl,
            looks_like_invoc_in_mod_inert_attr,
            sugg_span,
        )?;

        let span = invoc.span();
        let def_id = if deleg_impl.is_some() { None } else { res.opt_def_id() };
        self.tcx.with_stable_hashing_context(|hcx| {
            invoc_id.set_expn_data(
                ext.expn_data(
                    parent_scope.expansion,
                    span,
                    fast_print_path(path),
                    kind,
                    def_id,
                    def_id.map(|def_id| self.macro_def_scope(def_id).nearest_parent_mod()),
                ),
                hcx,
            )
        });

        Ok(Arc::clone(ext))
    }

    fn record_macro_rule_usage(&mut self, id: NodeId, rule_i: usize) {
        if let Some((_, rules)) = self.unused_macro_rules.get_mut(&id) {
            rules.remove(rule_i);
        }
    }

    fn check_unused_macros(&mut self) {
        for (_, &(node_id, ident, parent_def_id)) in self.unused_macros.iter() {
            let mut unannotated_mod = None;
            let mut annotated_mod = None;
            if let Some(def_id) = parent_def_id {
                let span = self.def_span(def_id);
                let node_id = self.def_id_to_node_id(def_id.expect_local());
                if ast::CRATE_NODE_ID != node_id {
                    if self.macro_use_mods.contains(&node_id) {
                        annotated_mod = Some(span);
                    } else {
                        unannotated_mod = Some(span.shrink_to_lo());
                    }
                }
            }

            self.lint_buffer.buffer_lint(
                UNUSED_MACROS,
                node_id,
                ident.span,
                diagnostics::UnusedMacroDefinition {
                    name: ident.name,
                    unannotated_mod,
                    annotated_mod,
                },
            );
            // Do not report unused individual rules if the entire macro is unused
            self.unused_macro_rules.swap_remove(&node_id);
        }

        for (&node_id, (def_id, unused_arms)) in self.unused_macro_rules.iter() {
            if unused_arms.is_empty() {
                continue;
            }
            let ext = self.local_macro_map[&def_id];
            let SyntaxExtensionKind::MacroRules(ref m) = ext.kind else {
                continue;
            };
            for arm_i in unused_arms.iter() {
                if let Some((ident, rule_span)) = m.get_unused_rule(arm_i) {
                    self.lint_buffer.buffer_lint(
                        UNUSED_MACRO_RULES,
                        node_id,
                        rule_span,
                        diagnostics::MacroRuleNeverUsed { n: arm_i + 1, name: ident.name },
                    );
                }
            }
        }
    }

    fn has_derive_copy(&self, expn_id: LocalExpnId) -> bool {
        self.containers_deriving_copy.contains(&expn_id)
    }

    fn has_derive_ord(&self, expn_id: LocalExpnId) -> bool {
        self.containers_deriving_ord.contains(&expn_id)
    }

    fn resolve_derives(
        &mut self,
        expn_id: LocalExpnId,
        force: bool,
        derive_paths: &dyn Fn() -> Vec<DeriveResolution>,
    ) -> Result<(), Indeterminate> {
        // Block expansion of the container until we resolve all derives in it.
        // This is required for two reasons:
        // - Derive helper attributes are in scope for the item to which the `#[derive]`
        //   is applied, so they have to be produced by the container's expansion rather
        //   than by individual derives.
        // - Derives in the container need to know whether one of them is a built-in `Copy`.
        //   (But see the comment mentioning #124794 below.)
        // Temporarily take the data to avoid borrow checker conflicts.
        let mut derive_data = mem::take(&mut self.derive_data);
        let entry = derive_data.entry(expn_id).or_insert_with(|| DeriveData {
            resolutions: derive_paths(),
            helper_attrs: Vec::new(),
            has_derive_copy: false,
            has_derive_ord: false,
        });
        let parent_scope = self.invocation_parent_scopes[&expn_id];
        for (i, resolution) in entry.resolutions.iter_mut().enumerate() {
            if resolution.exts.is_none() {
                resolution.exts = Some(Arc::clone(
                    match self.cm().resolve_derive_macro_path(
                        &resolution.path,
                        &parent_scope,
                        force,
                        None,
                    ) {
                        Ok((Some(ext), _)) => {
                            if !ext.helper_attrs.is_empty() {
                                let span = resolution.path.segments.last().unwrap().ident.span;
                                let ctxt = Macros20NormalizedSyntaxContext::new(span.ctxt());
                                entry.helper_attrs.extend(
                                    ext.helper_attrs
                                        .iter()
                                        .map(|&name| (i, IdentKey { name, ctxt }, span)),
                                );
                            }
                            entry.has_derive_copy |= ext.builtin_name == Some(sym::Copy);
                            entry.has_derive_ord |= ext.builtin_name == Some(sym::Ord);
                            ext
                        }
                        Ok(_) | Err(Determinacy::Determined) => self.dummy_ext(MacroKind::Derive),
                        Err(Determinacy::Undetermined) => {
                            assert!(self.derive_data.is_empty());
                            self.derive_data = derive_data;
                            return Err(Indeterminate);
                        }
                    },
                ));
            }
        }
        // Sort helpers in a stable way independent from the derive resolution order.
        entry.helper_attrs.sort_by_key(|(i, ..)| *i);
        let helper_attrs = entry
            .helper_attrs
            .iter()
            .map(|&(_, ident, orig_ident_span)| {
                let res = Res::NonMacroAttr(NonMacroAttrKind::DeriveHelper);
                let decl = self.arenas.new_pub_def_decl(res, orig_ident_span, expn_id);
                (ident, orig_ident_span, decl)
            })
            .collect();
        self.helper_attrs.insert(expn_id, helper_attrs);
        // Mark this derive as having `Copy` either if it has `Copy` itself or if its parent derive
        // has `Copy`, to support `#[derive(Copy, Clone)]`, `#[derive(Clone, Copy)]`, or
        // `#[derive(Copy)] #[derive(Clone)]`. We do this because the code generated for
        // `derive(Clone)` changes if `derive(Copy)` is also present.
        //
        // FIXME(#124794): unfortunately this doesn't work with `#[derive(Clone)] #[derive(Copy)]`.
        // When the `Clone` impl is generated the `#[derive(Copy)]` hasn't been processed and
        // `has_derive_copy` hasn't been set yet.
        if entry.has_derive_copy || self.has_derive_copy(parent_scope.expansion) {
            self.containers_deriving_copy.insert(expn_id);
        }
        // Similar to the above `Copy` and `Clone` case, the code generated for
        // `derive(PartialOrd)` changes if `derive(Ord)` is also present.
        // FIXME(makai410): this also doesn't work with `#[derive(PartialOrd)] #[derive(Ord)]`.
        if entry.has_derive_ord || self.has_derive_ord(parent_scope.expansion) {
            self.containers_deriving_ord.insert(expn_id);
        }
        assert!(self.derive_data.is_empty());
        self.derive_data = derive_data;
        Ok(())
    }

    fn take_derive_resolutions(&mut self, expn_id: LocalExpnId) -> Option<Vec<DeriveResolution>> {
        self.derive_data.remove(&expn_id).map(|data| data.resolutions)
    }

    // The function that implements the resolution logic of `#[cfg_accessible(path)]`.
    // Returns true if the path can certainly be resolved in one of three namespaces,
    // returns false if the path certainly cannot be resolved in any of the three namespaces.
    // Returns `Indeterminate` if we cannot give a certain answer yet.
    fn cfg_accessible(
        &mut self,
        expn_id: LocalExpnId,
        path: &ast::Path,
    ) -> Result<bool, Indeterminate> {
        self.path_accessible(expn_id, path, &[TypeNS, ValueNS, MacroNS])
    }

    fn macro_accessible(
        &mut self,
        expn_id: LocalExpnId,
        path: &ast::Path,
    ) -> Result<bool, Indeterminate> {
        self.path_accessible(expn_id, path, &[MacroNS])
    }

    // Trust (D21): keep an invalid quoted-span index fallible for the caller.
    fn get_proc_macro_quoted_span(&self, krate: CrateNum, id: usize) -> Option<Span> {
        self.cstore().get_proc_macro_quoted_span_untracked(self.tcx, krate, id)
    }

    fn declare_proc_macro(&mut self, id: NodeId) {
        self.proc_macros.push(self.owner_def_id(id))
    }

    fn append_stripped_cfg_item(
        &mut self,
        parent_node: NodeId,
        ident: Ident,
        cfg: CfgEntry,
        cfg_span: Span,
    ) {
        self.stripped_cfg_items.push(StrippedCfgItem {
            parent_scope: parent_node,
            ident,
            cfg: (cfg, cfg_span),
        });
    }

    fn registered_attr_tools(&self) -> &RegisteredTools {
        self.registered_attr_tools
    }

    fn registered_lint_tools(&self) -> &RegisteredTools {
        self.registered_lint_tools
    }

    fn register_glob_delegation(&mut self, invoc_id: LocalExpnId) {
        self.glob_delegation_invoc_ids.insert(invoc_id);
    }

    fn glob_delegation_suffixes(
        &self,
        trait_def_id: DefId,
        impl_def_id: LocalDefId,
        star_span: Span,
    ) -> Result<Vec<(Ident, Option<Ident>)>, Indeterminate> {
        let target_trait = self.expect_module(trait_def_id);
        if target_trait.has_unexpanded_invocations(self) {
            return Err(Indeterminate);
        }
        // FIXME: Instead of waiting try generating all trait methods, and pruning
        // the shadowed ones a bit later, e.g. when all macro expansion completes.
        // Pros: expansion will be stuck less (but only in exotic cases), the implementation may be
        // less hacky.
        // Cons: More code is generated just to be deleted later, deleting already created `DefId`s
        // may be nontrivial.
        if let Some(unexpanded_invocations) = self.impl_unexpanded_invocations.get(&impl_def_id)
            && !unexpanded_invocations.is_empty()
        {
            return Err(Indeterminate);
        }

        let mut idents = Vec::new();
        target_trait.for_each_child(self, |this, ident, orig_ident_span, ns, _binding| {
            if let Some(overriding_keys) = this.impl_binding_keys.get(&impl_def_id)
                && overriding_keys.contains(&BindingKey::new(ident, ns))
            {
                // The name is overridden, do not produce it from the glob delegation.
            } else {
                // FIXME: Adjust hygiene for idents from globs, like for glob imports.
                idents.push((ident.orig(star_span.with_ctxt(orig_ident_span.ctxt())), None));
            }
        });
        Ok(idents)
    }

    fn insert_impl_trait_name(&mut self, id: NodeId, name: Symbol) {
        self.impl_trait_names.insert(id, name);
    }
}

impl<'ra, 'tcx> Resolver<'ra, 'tcx> {
    /// Resolve macro path with error reporting and recovery.
    /// Uses dummy syntax extensions for unresolved macros or macros with unexpected resolutions
    /// for better error recovery.
    fn smart_resolve_macro_path(
        &mut self,
        path: &ast::Path,
        kind: MacroKind,
        supports_macro_expansion: SupportsMacroExpansion,
        inner_attr: bool,
        parent_scope: &ParentScope<'ra>,
        node_id: NodeId,
        force: bool,
        deleg_impl: Option<(LocalDefId, Span)>,
        invoc_in_mod_inert_attr: Option<LocalDefId>,
        suggestion_span: Option<Span>,
    ) -> Result<(&'ra Arc<SyntaxExtension>, Res), Indeterminate> {
        // Trust: `mut` retained so the spec-contract hook below can swap the
        // resolved extension for the compiler-owned contract builtin.
        let (mut ext, res) = match self.cm_mut().resolve_macro_or_delegation_path(
            path,
            kind,
            parent_scope,
            force,
            deleg_impl,
            invoc_in_mod_inert_attr.map(|def_id| (def_id, node_id)),
            None,
            suggestion_span,
        ) {
            Ok((Some(ext), res)) => (ext, res),
            Ok((None, res)) => (self.dummy_ext(kind), res),
            Err(Determinacy::Determined) => (self.dummy_ext(kind), Res::Err),
            Err(Determinacy::Undetermined) => return Err(Indeterminate),
        };

        if let Some(contract_ext) = self.trust_spec_contract_attr_extension(kind, ext, res) {
            ext = contract_ext;
        } else if let Some(contract_ext) = self.trust_tool_contract_attr_extension(
            kind,
            path,
            res,
            // Trust: a `Res::NonMacroAttr` skips the "expected non-macro
            // attribute" check below, which only `Res::Def` reaches. Swapping in
            // a macro extension there would hand the expander an attribute macro
            // in a position that cannot expand one, so the swap requires an
            // OUTER attribute in an expanding position; anywhere else the tool
            // attribute stays inert exactly as before.
            matches!(supports_macro_expansion, SupportsMacroExpansion::Yes { .. }) && !inner_attr,
        ) {
            ext = contract_ext;
        }

        // Everything below is irrelevant to glob delegation, take a shortcut.
        if deleg_impl.is_some() {
            if !matches!(res, Res::Err | Res::Def(DefKind::Trait, _)) {
                self.dcx().emit_err(MacroExpectedFound {
                    span: path.span,
                    expected: "trait",
                    article: "a",
                    found: res.descr(),
                    macro_path: &pprust::path_to_string(path),
                    remove_surrounding_derive: None,
                    add_as_non_derive: None,
                });
                return Ok((self.dummy_ext(kind), Res::Err));
            }

            return Ok((ext, res));
        }

        // Report errors for the resolved macro.
        for (idx, segment) in path.segments.iter().enumerate() {
            if let Some(args) = &segment.args {
                self.dcx().emit_err(diagnostics::GenericArgumentsInMacroPath { span: args.span() });
            }
            if kind == MacroKind::Attr && segment.ident.as_str().starts_with("rustc") {
                if idx == 0 {
                    self.dcx().emit_err(diagnostics::AttributesStartingWithRustcAreReserved {
                        span: segment.ident.span,
                    });
                } else {
                    self.dcx().emit_err(diagnostics::AttributesContainingRustcAreReserved {
                        span: segment.ident.span,
                    });
                }
            }
        }

        match res {
            Res::Def(DefKind::Macro(_), def_id) => {
                if let Some(def_id) = def_id.as_local() {
                    self.unused_macros.swap_remove(&def_id);
                    if self.proc_macro_stubs.contains(&def_id) {
                        self.dcx().emit_err(diagnostics::ProcMacroSameCrate {
                            span: path.span,
                            is_test: self.tcx.sess.is_test_crate(),
                        });
                    }
                }
                // Trust: `sym::trust` is exempt. This compiler predefines the
                // `trust` tool AND resolves `trust::requires`/`ensures`/… as
                // macros against the extern `trust` shim, with macro resolution
                // winning structurally (see the PREDEFINED_TOOLS note above);
                // both spellings reach one contract grammar, so for this one
                // tool there is no ambiguity to report. Upstream's error keeps
                // applying to every other tool namespace.
                if kind == MacroKind::Attr
                    && let [tool, _second, ..] = path.segments.as_slice()
                    && tool.ident.name != sym::trust
                    && self.registered_attr_tool_decls.contains_key(&IdentKey::new(tool.ident))
                {
                    self.dcx().emit_err(diagnostics::ToolAttrAmbiguity {
                        path_span: path.span,
                        attr_path: pprust::path_to_string(path),
                        tool: tool.ident.name,
                    });
                }
            }
            Res::NonMacroAttr(..) | Res::Err => {}
            _ => panic!("expected `DefKind::Macro` or `Res::NonMacroAttr`"),
        };

        self.check_stability_and_deprecation(&ext, path, node_id);

        let unexpected_res = if !ext.macro_kinds().contains(kind.into()) {
            Some((kind.article(), kind.descr_expected()))
        } else if matches!(res, Res::Def(..)) {
            match supports_macro_expansion {
                SupportsMacroExpansion::No => Some(("a", "non-macro attribute")),
                SupportsMacroExpansion::Yes { supports_inner_attrs } => {
                    if inner_attr && !supports_inner_attrs {
                        Some(("a", "non-macro inner attribute"))
                    } else {
                        None
                    }
                }
            }
        } else {
            None
        };
        if let Some((article, expected)) = unexpected_res {
            let path_str = pprust::path_to_string(path);

            let mut err = MacroExpectedFound {
                span: path.span,
                expected,
                article,
                found: res.descr(),
                macro_path: &path_str,
                remove_surrounding_derive: None,
                add_as_non_derive: None,
            };

            // Suggest moving the macro out of the derive() if the macro isn't Derive
            if !path.span.from_expansion()
                && kind == MacroKind::Derive
                && !ext.macro_kinds().contains(MacroKinds::DERIVE)
                && ext.macro_kinds().contains(MacroKinds::ATTR)
            {
                err.remove_surrounding_derive = Some(RemoveSurroundingDerive { span: path.span });
                err.add_as_non_derive = Some(AddAsNonDerive { macro_path: &path_str });
            }

            self.dcx().emit_err(err);

            return Ok((self.dummy_ext(kind), Res::Err));
        }

        // We are trying to avoid reporting this error if other related errors were reported.
        if res != Res::Err && inner_attr && !self.features.custom_inner_attributes() {
            let is_macro = match res {
                Res::Def(..) => true,
                Res::NonMacroAttr(..) => false,
                _ => unreachable!(),
            };
            let msg = if is_macro {
                "inner macro attributes are unstable"
            } else {
                "custom inner attributes are unstable"
            };
            feature_err(&self.tcx.sess, sym::custom_inner_attributes, path.span, msg).emit();
        }

        // Trust (E5 CONSERVATION): the `trust::` tool namespace is RESERVED. A name
        // in it that no consumer claims is a HARD ERROR naming the attribute —
        // never silence.
        //
        // WHAT WAS BROKEN. rustc resolves `#[<tool>::<anything>]` to an INERT tool
        // attribute without ever looking at `<anything>` (see the tool-module arm
        // in `ident.rs`), so — measured on the sealed toolchain `trust-e26541e3` —
        // `#[trust::totally_made_up_clause(whatever @@ nonsense)]` compiled with
        // ZERO diagnostics and a verification ledger identical, row for row and
        // solver for solver, to the same file carrying no attribute at all. A
        // one-keystroke `#[trust::assume_totall]` was likewise nothing, while its
        // author believed a property had been stated and checked. That reaches the
        // fake-proof class without writing a single false predicate.
        //
        // WHY HERE. This is the seam upstream used to validate the
        // `diagnostic::` namespace (since moved to `rustc_attr_parsing`), and
        // for the same reason: it
        // is the ONE point every tool attribute passes through, exactly once.
        // Measured via the `diagnostic::` twin on the sealed toolchain, it fires on
        // item, field, statement, expression, `mod`, `impl`, `trait` and
        // crate-root-inner positions, on macro-generated attributes, and on an
        // ACTIVE `cfg_attr` branch — each exactly once. It does NOT fire on a
        // `cfg`-eliminated branch, which is correct: an attribute that is not part
        // of this compilation states nothing about it. A HIR attribute walk was the
        // obvious alternative and is worse: lowering ALIASES one attribute slice
        // onto several HIR ids (a `let` statement's attrs, tuple-struct ctors), so
        // it double-reports without an `AttrId` set, and it cannot see an attribute
        // that expansion consumed. (Should macro resolution ever revisit one path,
        // `DiagCtxt` already suppresses a byte-identical diagnostic at the same
        // span, so the error stays one-per-attribute either way. Measured on the
        // `diagnostic::` twin: exactly one report per occurrence in all ten
        // positions tested.)
        //
        // WHY KEYED ON THE RESOLUTION, NOT THE SPELLING. Trust has a SECOND
        // attribute surface: a stable-Rust passthrough proc-macro crate literally
        // named `trust` (`--extern trust=`), intercepted by
        // `trust_spec_contract_attr_extension` below. Its attributes resolve to
        // `Res::Def(DefKind::Macro(..), ..)`, not to a tool attribute, and that
        // surface ALREADY fails closed on an unknown name — an unexported name
        // simply does not resolve, which is an ordinary hard resolution error.
        // Matching the literal `trust::` spelling instead of the resolution would
        // double-diagnose that surface and could reject a legitimate proc macro.
        //
        // WHY IT IS *NOT* GATED ON VERIFICATION — this was gated on
        // `trust_verification_enabled()` when E5 was written, and predefining the
        // tool (#42, above in `PREDEFINED_TOOLS`) makes that gate a hole.
        // The reasoning that justified it — "under `-Ztrust-verify=off` this
        // compiler is bit-for-bit upstream, and stock rustc accepts any
        // tool-attribute name" — assumed a crate only ever reached the tool arm by
        // hand-writing `#![register_tool(trust)]`. It no longer does. Registration
        // happens in the RESOLVER and is unconditional, so the INERTNESS it
        // introduces is unconditional too: with the gate in place,
        // `#[trust::asume_total]` in a dependency unit (targo appends
        // `-Ztrust-verify=off` to every one of those) goes from `E0433: cannot find
        // module or crate 'trust'` straight to silence — a strictly worse outcome
        // than the error it replaced, in exactly the lane nobody is watching.
        // Running unconditionally preserves the PREVIOUS behaviour rather than
        // tightening it: the spelling was already fatal under `off`, and only the
        // error's identity changes. The residual divergence is predefinition
        // itself, not this refusal, and a crate that registers an unrelated tool it
        // calls `trust` is the cost of RESERVING the namespace — the same trade
        // `trust_spec_contract_attr_extension` below already makes for an unrelated
        // crate named `trust`, with the same `--unverified` route out.
        //
        // SCOPE, stated rather than implied: this is a NAME check. It does not
        // validate PAYLOADS (`#[trust::skip(garbage @@ here)]` keeps compiling —
        // the consumer owns its payload) and it does not validate POSITIONS (a
        // claimed name on an item kind no consumer reads is still silently
        // dropped). Both remain open, and are documented in
        // `trust_types::trust_attr_namespace`.
        if res == Res::NonMacroAttr(NonMacroAttrKind::Tool)
            && let [namespace, ..] = &*path.segments
            && namespace.ident.name == sym::trust
        {
            // `Symbol::as_str` borrows from the symbol; materialize owned strings
            // first so the `&str` slice handed to the classifier outlives the call.
            let owned: Vec<String> =
                path.segments.iter().map(|segment| segment.ident.name.to_string()).collect();
            let segments: Vec<&str> = owned.iter().map(String::as_str).collect();
            if let TrustAttrVerdict::Unclaimed { nearest } = classify_trust_attr_path(&segments) {
                let written = segments[1..].join("::");
                let mut err = self.dcx().struct_span_err(
                    path.span,
                    format!("Trust: `#[trust::{written}]` is not a Trust attribute"),
                );
                err.note(
                    "`trust::` is a RESERVED namespace: every name in it must be claimed by a \
                     compiler consumer, so a misspelled or invented clause can never be silently \
                     ignored while its author believes it was verified",
                );
                err.note(format!("the claimed vocabulary is: {}", vocabulary_list()));
                if let Some(nearest) = nearest {
                    err.help(format!("did you mean `#[trust::{nearest}]`?"));
                }
                err.help(
                    "to state a property this compiler has no name for yet, write it as a \
                     `requires` / `ensures` clause or a `clean { .. }` island — an unrecognized \
                     attribute states nothing",
                );
                // The escape hatch is spelled differently per driver, and naming
                // only the compiler flag would be wrong for most users: Targo
                // REFUSES a caller-supplied `-Ztrust-verify=off` while a
                // verification session is active ("reserved for Targo's resolved
                // compilation-unit scope"), so a `targo` user told to pass that
                // flag would hit a second refusal. `--unverified` lowers onto the
                // same off-switch for the whole build and is the one they can use.
                err.help(
                    "to compile this crate outside the Trust attribute vocabulary: under Targo \
                     use `targo --unverified`, which lowers onto the same off-switch (Targo \
                     refuses a caller-supplied `-Ztrust-verify=off` while a verification session \
                     is active); calling `trustc` directly, pass `-Ztrust-verify=off`",
                );
                // A crate that registers a tool it independently calls `trust` lands
                // here too. That is the cost of RESERVING the namespace, and it is
                // the same trade `trust_spec_contract_attr_extension` below already
                // makes for an unrelated crate named `trust`; the help above is
                // their route.
                err.emit();
            }
        }

        Ok((ext, res))
    }

    fn trust_spec_contract_attr_extension(
        &self,
        kind: MacroKind,
        resolved_ext: &Arc<SyntaxExtension>,
        res: Res,
    ) -> Option<&'ra Arc<SyntaxExtension>> {
        // Trust: with `-Z trust-verify=off` (vanilla mode / bootstrap) macro
        // resolution is bit-for-bit upstream — no contract-macro swap. This is
        // also the escape hatch for depending on an unrelated crate that
        // happens to be named `trust`.
        if !self.tcx.sess.trust_verification_enabled() {
            return None;
        }
        let Res::Def(DefKind::Macro(macro_kinds), def_id) = res else {
            return None;
        };
        if kind != MacroKind::Attr || !macro_kinds.contains(MacroKinds::ATTR) {
            return None;
        }

        // `trust-spec` is a stable-Rust passthrough proc-macro crate with lib
        // crate name `trust`. In tRustc, those proc macros must be replaced
        // after name resolution and before expansion so the compiler-owned
        // contract lowering sees the original attribute payload. Resolver
        // metadata does not carry Cargo package identity, so the identity check
        // accepts exactly the crate-root `requires`/`ensures`/`decreases`
        // attribute proc macros of an external crate named `trust`.
        //
        // Trust: the decision keys on the RESOLVED def, not the literal
        // invocation path — `use trust::requires; #[requires(..)]`,
        // `use trust::requires as pre;`, `#[::trust::requires(..)]`, and Cargo
        // package renames all resolve to the same trust-spec proc macro and
        // must all get the compiler-owned builtin. Keying on the literal
        // `trust::requires` spelling let every other spelling fall through to
        // the passthrough macro: the code compiled clean while the contract
        // was silently never verified (fail-open).
        if def_id.is_local() || self.tcx.crate_name(def_id.krate).as_str() != "trust" {
            return None;
        }
        // Trust: upstream moved the `CrateStore` trait to `rustc_crate_store`
        // (not a `rustc_resolve` dependency); `TyCtxt::def_path` on a non-local
        // `DefId` (guaranteed above) is the same untracked CStore `def_path`.
        let attribute_name = trust_spec_contract_def_path_attr(&self.tcx.def_path(def_id))?;
        let (_, builtin_name) =
            trust_spec_contract_builtin_name_from_symbols(sym::trust, attribute_name)?;

        let builtin_kind = self.builtin_macros.get(&builtin_name)?.clone();
        let mut ext = SyntaxExtension::default(builtin_kind, resolved_ext.edition);
        ext.span = resolved_ext.span;
        ext.allow_internal_unstable = Some(vec![sym::contracts_internals].into());
        ext.builtin_name = Some(builtin_name);
        ext.collapse_debuginfo = resolved_ext.collapse_debuginfo;
        // Trust: upstream now stores syntax extensions as arena-borrowed
        // `&'ra Arc<SyntaxExtension>` (see `ResolverArenas::alloc_macro` /
        // `dummy_ext`), so the contract replacement is arena-allocated to match
        // `smart_resolve_macro_path`'s `&'ra Arc<SyntaxExtension>` result type.
        Some(self.arenas.alloc_macro(ext))
    }

    /// Trust: the predefined `trust` TOOL surface, `#[trust::requires(..)]` and
    /// `#[trust::ensures(..)]` written with no `trust` crate in scope, gets the
    /// same compiler-owned contract builtin as the trust-spec shim surface in
    /// [`Self::trust_spec_contract_attr_extension`].
    ///
    /// WHY. Without it the two spellings of ONE clause took two contract
    /// systems. The shim surface reached the contract grammar and the typed
    /// query; the tool surface stayed an inert attribute that
    /// `trust-mir-extract`'s `extract_contracts` read back out of raw HIR, with
    /// no typed proposition behind it. Measured on seal `321aaeda7`
    /// (2026-09-29) with the grid wedge's shape: native `ensures
    /// !self.storage.detached` proves the fixed body (3 proved), the shim
    /// surface gives the same rows, and the tool surface ends at "compiler
    /// contract predicate `!self.storage.detached` was not lowered into a typed
    /// verifier formula" for the fixed body and for the mutant alike, so it
    /// could not tell the bug from the fix. docs/TWO_LANGUAGE_100_PERCENT_GOAL.md
    /// §3 requires every `#[trust::...]` contract to be an exact desugaring
    /// into the one grammar/query path.
    ///
    /// SCOPE. Only the exact two-segment paths `trust::requires` and
    /// `trust::ensures`, and only under verification: with `-Ztrust-verify=off`
    /// the attribute stays inert, as every tool attribute is upstream.
    /// `decreases` and `invariant` keep their tool-surface consumers, which UI
    /// tests pin; moving them is a separate change.
    fn trust_tool_contract_attr_extension(
        &self,
        kind: MacroKind,
        path: &ast::Path,
        res: Res,
        outer_attr_in_expanding_position: bool,
    ) -> Option<&'ra Arc<SyntaxExtension>> {
        if !self.tcx.sess.trust_verification_enabled()
            || kind != MacroKind::Attr
            || !outer_attr_in_expanding_position
            || res != Res::NonMacroAttr(NonMacroAttrKind::Tool)
        {
            return None;
        }
        let [namespace, attribute] = &*path.segments else {
            return None;
        };
        if namespace.args.is_some()
            || attribute.args.is_some()
            || !matches!(attribute.ident.name, sym::requires | sym::ensures)
        {
            return None;
        }
        let (_, builtin_name) = trust_spec_contract_builtin_name_from_symbols(
            namespace.ident.name,
            attribute.ident.name,
        )?;

        let builtin_kind = self.builtin_macros.get(&builtin_name)?.clone();
        let mut ext = SyntaxExtension::default(builtin_kind, path.span.edition());
        ext.span = path.span;
        ext.allow_internal_unstable = Some(vec![sym::contracts_internals].into());
        ext.builtin_name = Some(builtin_name);
        Some(self.arenas.alloc_macro(ext))
    }

    pub(crate) fn resolve_derive_macro_path<'r>(
        self: CmResolver<'r, 'ra, 'tcx>,
        path: &ast::Path,
        parent_scope: &ParentScope<'ra>,
        force: bool,
        ignore_import: Option<Import<'ra>>,
    ) -> Result<(Option<&'r Arc<SyntaxExtension>>, Res), Determinacy> {
        self.resolve_macro_or_delegation_path(
            path,
            MacroKind::Derive,
            parent_scope,
            force,
            None,
            None,
            ignore_import,
            None,
        )
    }

    fn resolve_macro_or_delegation_path<'r>(
        mut self: CmResolver<'r, 'ra, 'tcx>,
        ast_path: &ast::Path,
        kind: MacroKind,
        parent_scope: &ParentScope<'ra>,
        force: bool,
        deleg_impl: Option<(LocalDefId, Span)>,
        invoc_in_mod_inert_attr: Option<(LocalDefId, NodeId)>,
        ignore_import: Option<Import<'ra>>,
        suggestion_span: Option<Span>,
    ) -> Result<(Option<&'ra Arc<SyntaxExtension>>, Res), Determinacy> {
        let path_span = ast_path.span;
        let mut path = Segment::from_path(ast_path);

        // Possibly apply the macro helper hack
        if deleg_impl.is_none()
            && kind == MacroKind::Bang
            && let [segment] = path.as_slice()
            && segment.ident.span.ctxt().outer_expn_data().local_inner_macros
        {
            let root = Ident::new(kw::DollarCrate, segment.ident.span);
            path.insert(0, Segment::from_ident(root));
        }

        let res = if deleg_impl.is_some() || path.len() > 1 {
            let ns = if deleg_impl.is_some() { TypeNS } else { MacroNS };
            let res = match self.reborrow().maybe_resolve_path(
                &path,
                Some(ns),
                parent_scope,
                ignore_import,
            ) {
                PathResult::NonModule(path_res) if let Some(res) = path_res.full_res() => Ok(res),
                PathResult::Indeterminate if !force => return Err(Determinacy::Undetermined),
                PathResult::NonModule(..)
                | PathResult::Indeterminate
                | PathResult::Failed { .. } => Err(Determinacy::Determined),
                PathResult::Module(ModuleOrUniformRoot::Module(module)) => {
                    Ok(module.res().unwrap())
                }
                PathResult::Module(..) => unreachable!(),
            };

            self.multi_segment_macro_resolutions.borrow_mut_checked(&self).push((
                path,
                path_span,
                kind,
                *parent_scope,
                res.ok(),
                ns,
            ));

            self.prohibit_imported_non_macro_attrs(None, res.ok(), path_span);
            res
        } else {
            let binding = self.reborrow().resolve_ident_in_scope_set(
                path[0].ident,
                ScopeSet::Macro(kind),
                parent_scope,
                None,
                None,
                None,
            );
            let binding = binding.map_err(|determinacy| {
                Determinacy::determined(determinacy == Determinacy::Determined || force)
            });
            if let Err(Determinacy::Undetermined) = binding {
                return Err(Determinacy::Undetermined);
            }

            self.single_segment_macro_resolutions.borrow_mut_checked(&self).push((
                path[0].ident,
                kind,
                *parent_scope,
                binding.ok(),
                suggestion_span,
            ));

            let res = binding.map(|binding| binding.res());
            self.prohibit_imported_non_macro_attrs(binding.ok(), res.ok(), path_span);
            self.reborrow().report_out_of_scope_macro_calls(
                ast_path,
                parent_scope,
                invoc_in_mod_inert_attr,
                binding.ok(),
            );
            res
        };

        let res = res?;
        let ext = match deleg_impl {
            Some((impl_def_id, star_span)) => match res {
                Res::Def(DefKind::Trait, def_id) => {
                    let edition = self.tcx.sess.edition();
                    Some(self.arenas.alloc_macro(SyntaxExtension::glob_delegation(
                        def_id,
                        impl_def_id,
                        star_span,
                        edition,
                    )))
                }
                _ => None,
            },
            None => self.get_macro(res),
        };
        Ok((ext, res))
    }

    pub(crate) fn finalize_macro_resolutions(&mut self, krate: &Crate) {
        let check_consistency = |this: &Self,
                                 path: &[Segment],
                                 span,
                                 kind: MacroKind,
                                 initial_res: Option<Res>,
                                 res: Res| {
            if let Some(initial_res) = initial_res {
                if res != initial_res {
                    if this.ambiguity_errors.is_empty() {
                        // Make sure compilation does not succeed if preferred macro resolution
                        // has changed after the macro had been expanded. In theory all such
                        // situations should be reported as errors, so this is a bug.
                        this.dcx().span_delayed_bug(span, "inconsistent resolution for a macro");
                    }
                }
            } else if this.tcx.dcx().has_errors().is_none() && this.privacy_errors.is_empty() {
                // It's possible that the macro was unresolved (indeterminate) and silently
                // expanded into a dummy fragment for recovery during expansion.
                // Now, post-expansion, the resolution may succeed, but we can't change the
                // past and need to report an error.
                // However, non-speculative `resolve_path` can successfully return private items
                // even if speculative `resolve_path` returned nothing previously, so we skip this
                // less informative error if no other error is reported elsewhere.

                let err = this.dcx().create_err(CannotDetermineMacroResolution {
                    span,
                    kind: kind.descr(),
                    path: Segment::names_to_string(path),
                });
                err.stash(span, StashKey::UndeterminedMacroResolution);
            }
        };

        let macro_resolutions = self.multi_segment_macro_resolutions.take(self);
        for (mut path, path_span, kind, parent_scope, initial_res, ns) in macro_resolutions {
            // FIXME: Path resolution will ICE if segment IDs present.
            for seg in &mut path {
                seg.id = None;
            }
            match self.cm_mut().resolve_path(
                &path,
                Some(ns),
                &parent_scope,
                Some(Finalize::new(ast::CRATE_NODE_ID, path_span)),
                None,
                None,
            ) {
                PathResult::NonModule(path_res) if let Some(res) = path_res.full_res() => {
                    check_consistency(self, &path, path_span, kind, initial_res, res)
                }
                // This may be a trait for glob delegation expansions.
                PathResult::Module(ModuleOrUniformRoot::Module(module)) => check_consistency(
                    self,
                    &path,
                    path_span,
                    kind,
                    initial_res,
                    module.res().unwrap(),
                ),
                path_res @ (PathResult::NonModule(..) | PathResult::Failed { .. }) => {
                    let mut suggestion = None;
                    let (span, message, label, module, segment, help) = match path_res {
                        PathResult::Failed {
                            span, label, module, segment, message, help, ..
                        } => {
                            // try to suggest if it's not a macro, maybe a function
                            if let PathResult::NonModule(partial_res) = self
                                .cm()
                                .maybe_resolve_path(&path, Some(ValueNS), &parent_scope, None)
                                && partial_res.unresolved_segments() == 0
                            {
                                let sm = self.tcx.sess.source_map();
                                let exclamation_span = sm.next_point(span);
                                suggestion = Some((
                                    vec![(exclamation_span, "".to_string())],
                                    format!(
                                        "{} is not a macro, but a {}, try to remove `!`",
                                        Segment::names_to_string(&path),
                                        partial_res.base_res().descr()
                                    ),
                                    Applicability::MaybeIncorrect,
                                ));
                            }
                            (span, message, label, module, segment.name, help)
                        }
                        PathResult::NonModule(partial_res) => {
                            let found_an = partial_res.base_res().article();
                            let found_descr = partial_res.base_res().descr();
                            let scope = match &path[..partial_res.unresolved_segments()] {
                                [.., prev] => {
                                    format!("{found_descr} `{}`", prev.ident)
                                }
                                _ => found_descr.to_string(),
                            };
                            let expected_an = kind.article();
                            let expected_descr = kind.descr();
                            let expected_name = path[partial_res.unresolved_segments()].ident;

                            (
                                path_span,
                                format!(
                                    "cannot find {expected_descr} `{expected_name}` in {scope}"
                                ),
                                match partial_res.base_res() {
                                    Res::Def(
                                        DefKind::Mod | DefKind::Macro(..) | DefKind::ExternCrate,
                                        _,
                                    ) => format!(
                                        "partially resolved path in {expected_an} {expected_descr}",
                                    ),
                                    _ => format!(
                                        "{expected_an} {expected_descr} can't exist within \
                                         {found_an} {found_descr}"
                                    ),
                                },
                                None,
                                path.last().map(|segment| segment.ident.name).unwrap(),
                                None,
                            )
                        }
                        _ => unreachable!(),
                    };
                    self.report_error(
                        span,
                        ResolutionError::FailedToResolve {
                            segment,
                            label,
                            suggestion,
                            help,
                            module,
                            message,
                        },
                    );
                }
                PathResult::Module(..) | PathResult::Indeterminate => unreachable!(),
            }
        }

        let macro_resolutions = self.single_segment_macro_resolutions.take(self);
        for (ident, kind, parent_scope, initial_binding, sugg_span) in macro_resolutions {
            match self.cm_mut().resolve_ident_in_scope_set(
                ident,
                ScopeSet::Macro(kind),
                &parent_scope,
                Some(Finalize::new(ast::CRATE_NODE_ID, ident.span)),
                None,
                None,
            ) {
                Ok(binding) => {
                    let initial_res = initial_binding.map(|initial_binding| {
                        self.record_use(ident, initial_binding, Used::Other);
                        initial_binding.res()
                    });
                    let res = binding.res();
                    let seg = Segment::from_ident(ident);
                    check_consistency(self, &[seg], ident.span, kind, initial_res, res);
                    if res == Res::NonMacroAttr(NonMacroAttrKind::DeriveHelperCompat) {
                        let node_id = self
                            .invocation_parents
                            .get(&parent_scope.expansion)
                            .map_or(ast::CRATE_NODE_ID, |parent| {
                                self.def_id_to_node_id(parent.parent_def)
                            });
                        self.lint_buffer.buffer_lint(
                            LEGACY_DERIVE_HELPERS,
                            node_id,
                            ident.span,
                            diagnostics::LegacyDeriveHelpers { span: binding.span },
                        );
                    }
                }
                Err(..) => {
                    let expected = kind.descr_expected();

                    let mut err = self.dcx().create_err(CannotFindIdentInThisScope {
                        span: ident.span,
                        expected,
                        ident,
                    });
                    self.unresolved_macro_suggestions(
                        &mut err,
                        kind,
                        &parent_scope,
                        ident,
                        krate,
                        sugg_span,
                    );
                    err.emit();
                }
            }
        }

        let builtin_attrs = mem::take(&mut self.builtin_attrs);
        for (ident, parent_scope) in builtin_attrs {
            let _ = self.cm_mut().resolve_ident_in_scope_set(
                ident,
                ScopeSet::Macro(MacroKind::Attr),
                &parent_scope,
                Some(Finalize::new(ast::CRATE_NODE_ID, ident.span)),
                None,
                None,
            );
        }
    }

    fn check_stability_and_deprecation(
        &mut self,
        ext: &SyntaxExtension,
        path: &ast::Path,
        node_id: NodeId,
    ) {
        let span = path.span;
        if let Some(stability) = &ext.stability
            && let StabilityLevel::Unstable { reason, issue, implied_by, .. } = stability.level
        {
            let feature = stability.feature;

            let is_allowed =
                |feature| self.features.enabled(feature) || span.allows_unstable(feature);
            let allowed_by_implication = implied_by.is_some_and(|feature| is_allowed(feature));
            if !is_allowed(feature) && !allowed_by_implication {
                stability::report_unstable(
                    self.tcx.sess,
                    feature,
                    reason.to_opt_reason(),
                    issue,
                    span,
                    stability::UnstableKind::Regular,
                );
            }
        }
        if let Some(depr) = &ext.deprecation {
            let path = pprust::path_to_string(path);
            stability::early_report_macro_deprecation(
                &mut self.lint_buffer,
                depr,
                span,
                node_id,
                path,
            );
        }
    }

    fn prohibit_imported_non_macro_attrs(
        &self,
        decl: Option<Decl<'ra>>,
        res: Option<Res>,
        span: Span,
    ) {
        if let Some(Res::NonMacroAttr(kind)) = res {
            if kind != NonMacroAttrKind::Tool && decl.is_none_or(|b| b.is_import()) {
                self.dcx().emit_err(diagnostics::CannotUseThroughAnImport {
                    span,
                    article: kind.article(),
                    descr: kind.descr(),
                    binding_span: decl.map(|d| d.span),
                });
            }
        }
    }

    fn report_out_of_scope_macro_calls<'r>(
        mut self: CmResolver<'r, 'ra, 'tcx>,
        path: &ast::Path,
        parent_scope: &ParentScope<'ra>,
        invoc_in_mod_inert_attr: Option<(LocalDefId, NodeId)>,
        decl: Option<Decl<'ra>>,
    ) {
        if let Some((mod_def_id, node_id)) = invoc_in_mod_inert_attr
            && let Some(decl) = decl
            // This is a `macro_rules` itself, not some import.
            && let DeclKind::Def(res, _) = decl.kind
            && let Res::Def(DefKind::Macro(kinds), def_id) = res
            && kinds.contains(MacroKinds::BANG)
            // And the `macro_rules` is defined inside the attribute's module,
            // so it cannot be in scope unless imported.
            && self.tcx.is_descendant_of(def_id, mod_def_id)
        {
            // Try to resolve our ident ignoring `macro_rules` scopes.
            // If such resolution is successful and gives the same result
            // (e.g. if the macro is re-imported), then silence the lint.
            let no_macro_rules = self.arenas.alloc_macro_rules_scope(MacroRulesScope::Empty);
            let ident = path.segments[0].ident;
            let fallback_binding = self.reborrow().resolve_ident_in_scope_set(
                ident,
                ScopeSet::Macro(MacroKind::Bang),
                &ParentScope { macro_rules: no_macro_rules, ..*parent_scope },
                None,
                None,
                None,
            );
            if let Ok(fallback_binding) = fallback_binding
                && fallback_binding.res().opt_def_id() == Some(def_id)
            {
                // Silence `unused_imports` on the fallback import as well.
                self.get_mut().record_use(ident, fallback_binding, Used::Other);
            } else {
                let location = match parent_scope.module.kind {
                    ModuleKind::Def(kind, def_id, _, name) => {
                        if let Some(name) = name {
                            format!("{} `{name}`", kind.descr(def_id))
                        } else {
                            "the crate root".to_string()
                        }
                    }
                    ModuleKind::Block => "this scope".to_string(),
                };
                self.tcx.sess.psess.buffer_lint(
                    OUT_OF_SCOPE_MACRO_CALLS,
                    path.span,
                    node_id,
                    diagnostics::OutOfScopeMacroCalls {
                        span: path.span,
                        path: pprust::path_to_string(path),
                        location,
                    },
                );
            }
        }
    }

    pub(crate) fn check_reserved_macro_name(&self, name: Symbol, span: Span, res: Res) {
        // Reserve some names that are not quite covered by the general check
        // performed on `Resolver::builtin_attrs`.
        if name == sym::cfg || name == sym::cfg_attr {
            let macro_kinds = res.macro_kinds();
            if macro_kinds.is_some() && sub_namespace_match(macro_kinds, Some(MacroKind::Attr)) {
                self.dcx()
                    .emit_err(diagnostics::NameReservedInAttributeNamespace { span, ident: name });
            }
        }
    }

    /// Compile the macro into a `SyntaxExtension` and its rule spans.
    ///
    /// Possibly replace its expander to a pre-defined one for built-in macros.
    pub(crate) fn compile_macro(
        &self,
        macro_def: &ast::MacroDef,
        ident: Ident,
        attrs: &[rustc_attr_ir::Attribute],
        span: Span,
        node_id: NodeId,
        edition: Edition,
    ) -> SyntaxExtension {
        let mut ext = compile_declarative_macro(
            self.tcx.sess,
            self.features,
            macro_def,
            ident,
            attrs,
            span,
            node_id,
            edition,
        );

        if let Some(builtin_name) = ext.builtin_name {
            // The macro was marked with `#[rustc_builtin_macro]`.
            if let Some(builtin_ext_kind) = self.builtin_macros.get(&builtin_name) {
                // The macro is a built-in, replace its expander function
                // while still taking everything else from the source code.
                ext.kind = builtin_ext_kind.clone();
            } else {
                self.dcx().emit_err(diagnostics::CannotFindBuiltinMacroWithName { span, ident });
            }
        }

        ext
    }

    fn path_accessible(
        &self,
        expn_id: LocalExpnId,
        path: &ast::Path,
        namespaces: &[Namespace],
    ) -> Result<bool, Indeterminate> {
        let span = path.span;
        let path = &Segment::from_path(path);
        let parent_scope = self.invocation_parent_scopes[&expn_id];

        let mut indeterminate = false;
        for ns in namespaces {
            match self.cm().maybe_resolve_path(path, Some(*ns), &parent_scope, None) {
                PathResult::Module(ModuleOrUniformRoot::Module(_)) => return Ok(true),
                PathResult::NonModule(partial_res) if partial_res.unresolved_segments() == 0 => {
                    return Ok(true);
                }
                PathResult::NonModule(..) |
                // HACK(Urgau): This shouldn't be necessary
                PathResult::Failed { is_error_from_last_segment: false, .. } => {
                    self.dcx().emit_err(diagnostics::CfgAccessibleUnsure { span });

                    // If we get a partially resolved NonModule in one namespace, we should get the
                    // same result in any other namespaces, so we can return early.
                    return Ok(false);
                }
                PathResult::Indeterminate => indeterminate = true,
                // We can only be sure that a path doesn't exist after having tested all the
                // possibilities, only at that time we can return false.
                PathResult::Failed { .. } => {}
                PathResult::Module(_) => panic!("unexpected path resolution"),
            }
        }

        if indeterminate {
            return Err(Indeterminate);
        }

        Ok(false)
    }
}

fn trust_spec_contract_builtin_name_from_symbols(
    namespace: Symbol,
    attribute: Symbol,
) -> Option<(Symbol, Symbol)> {
    if namespace != sym::trust {
        return None;
    }

    // Trust: map onto the Trust-specific contract builtins (not upstream's
    // `contracts_requires`/`contracts_ensures`), so the injected clauses carry
    // their trust-spec ORIGIN into the parser. Trust-origin payloads may be
    // spec-only syntax (`result`, `old()`, `forall`, `==>`) that must bypass
    // name resolution and typeck, while upstream `core::contracts` clauses
    // keep upstream's typed lowering unchanged.
    //
    // Trust: `invariant` is mapped too, but its builtin is a REFUSAL rather
    // than a lowering (`ExpandTrustInvariant`). It must be listed here for the
    // same fail-open reason the two clauses above are: an unmapped attribute
    // falls through to trust-spec's passthrough proc macro and is erased with
    // no diagnostic at all. Mapping it is what makes the refusal reachable.
    // `decreases` is deliberately absent — trust-spec exports no `decreases`,
    // so it is already E0433, and adding a mapping without a trust-spec export
    // would be dead code while ADDING one to trust-spec would create a second
    // silent erasure.
    let builtin = match attribute {
        sym::requires => sym::trust_contracts_requires,
        sym::ensures => sym::trust_contracts_ensures,
        // Trust (D4): `decreases` has no upstream `core::contracts` spelling,
        // so there is no typed lane for it to join and nothing to keep it
        // distinguishable FROM. Its builtin desugars to the native `decreases
        // e` clause verbatim. Without this arm the attribute reaches no
        // builtin at all and trust-spec has no such proc macro, so linking the
        // compat shim turned a clause that VERIFIES on the first-class and
        // tool-attribute surfaces into E0433 -- measured on trust-e26541e3.
        sym::decreases => sym::trust_contracts_decreases,
        // Trust (D1): `invariant` maps onto a REFUSAL builtin. Without this arm
        // the trust-spec passthrough proc macro runs and the annotation is
        // ERASED with no diagnostic, and the function is then credited as
        // verified -- measured on trust-e26541e3.
        sym::invariant => sym::trust_contracts_invariant,
        _ => return None,
    };
    Some((attribute, builtin))
}

/// Trust: if `def_path` has the shape of a trust-spec contract proc macro —
/// a single crate-root `MacroNs(requires|ensures|decreases|invariant)` component with
/// disambiguator 0 — return the attribute name.
///
/// `invariant` is included so its REFUSAL builtin is reachable; see
/// `trust_spec_contract_builtin_name_from_symbols`.
fn trust_spec_contract_def_path_attr(def_path: &DefPath) -> Option<Symbol> {
    let [component] = &def_path.data[..] else {
        return None;
    };
    if component.disambiguator != 0 {
        return None;
    }
    match component.data {
        DefPathData::MacroNs(name)
            if name == sym::requires
                || name == sym::ensures
                || name == sym::decreases
                || name == sym::invariant =>
        {
            Some(name)
        }
        _ => None,
    }
}

#[cfg(test)]
fn trust_spec_contract_def_path_matches(def_path: &DefPath, attribute: Symbol) -> bool {
    trust_spec_contract_def_path_attr(def_path) == Some(attribute)
}

#[cfg(test)]
mod tests;
