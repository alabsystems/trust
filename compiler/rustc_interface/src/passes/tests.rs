//! A driver callback that swapped a Trust-critical query provider would
//! silently relocate proof authority out of the compiler. These cases pin
//! the rejection to Trust semantics being active and to the exact provider
//! set, so adding a provider without listing it here fails loudly.

use rustc_middle::util::Providers;

use super::{
    DEFAULT_QUERY_PROVIDERS, changed_trust_critical_query_provider,
    query_override_callback_conflicts, trust_critical_provider_violation,
};

#[test]
fn query_override_callbacks_are_rejected_only_for_trust_semantics() {
    assert!(query_override_callback_conflicts(true, true));
    assert!(!query_override_callback_conflicts(true, false));
    assert!(!query_override_callback_conflicts(false, true));
    assert!(!query_override_callback_conflicts(false, false));
}

#[test]
fn adversarial_callback_cannot_replace_trust_critical_providers() {
    let canonical = *DEFAULT_QUERY_PROVIDERS;
    assert_eq!(changed_trust_critical_query_provider(&canonical), None);
    let defaults = Providers::default();

    macro_rules! assert_query_swap_rejected {
        ($field:ident) => {{
            let mut changed = canonical;
            changed.queries.$field = |_, _| {
                panic!(
                    "adversarial `{}` provider must never execute in this comparison test",
                    stringify!($field),
                )
            };
            assert_eq!(
                changed_trust_critical_query_provider(&changed),
                Some(stringify!($field)),
                "adversarial replacement of `{}` escaped the Trust provider boundary",
                stringify!($field),
            );
        }};
    }

    assert_query_swap_rejected!(analysis);
    assert_query_swap_rejected!(codegen_fn_attrs);
    assert_query_swap_rejected!(crates);
    assert_query_swap_rejected!(dependency_formats);
    assert_query_swap_rejected!(exported_generic_symbols);
    assert_query_swap_rejected!(exported_non_generic_symbols);
    assert_query_swap_rejected!(foreign_modules);
    assert_query_swap_rejected!(hir_attr_map);
    assert_query_swap_rejected!(hir_crate_items);
    assert_query_swap_rejected!(has_alloc_error_handler);
    assert_query_swap_rejected!(has_global_allocator);
    assert_query_swap_rejected!(has_panic_handler);
    assert_query_swap_rejected!(index_ast);
    assert_query_swap_rejected!(lower_to_hir);
    assert_query_swap_rejected!(thir_body);
    assert_query_swap_rejected!(typeck_root);
    assert_query_swap_rejected!(closure_typeinfo);
    assert_query_swap_rejected!(mir_keys);
    assert_query_swap_rejected!(mir_built);
    assert_query_swap_rejected!(mir_borrowck);
    assert_query_swap_rejected!(mir_const_qualif);
    assert_query_swap_rejected!(mir_promoted);
    assert_query_swap_rejected!(mir_drops_elaborated_and_const_checked);
    assert_query_swap_rejected!(mir_for_ctfe);
    assert_query_swap_rejected!(optimized_mir);
    assert_query_swap_rejected!(native_libraries);
    assert_query_swap_rejected!(resolver_for_lowering_raw);
    assert_query_swap_rejected!(type_of);
    assert_query_swap_rejected!(fn_sig);
    assert_query_swap_rejected!(generics_of);
    assert_query_swap_rejected!(layout_of);
    assert_query_swap_rejected!(eval_to_const_value_raw);
    assert_query_swap_rejected!(resolve_instance_raw);
    assert_query_swap_rejected!(adt_def);
    assert_query_swap_rejected!(param_env);
    assert_query_swap_rejected!(region_scope_tree);
    assert_query_swap_rejected!(symbol_name);
    assert_query_swap_rejected!(associated_item);
    assert_query_swap_rejected!(impl_trait_header);
    assert_query_swap_rejected!(codegen_fn_attrs);
    assert_query_swap_rejected!(coroutine_for_closure);
    assert_query_swap_rejected!(coroutine_kind);
    assert_query_swap_rejected!(crate_name);
    assert_query_swap_rejected!(def_kind);
    assert_query_swap_rejected!(def_span);
    assert_query_swap_rejected!(fn_arg_idents);
    assert_query_swap_rejected!(attrs_for_def);
    assert_query_swap_rejected!(get_lang_items);
    assert_query_swap_rejected!(defined_lang_items);
    assert_query_swap_rejected!(diagnostic_items);
    assert_query_swap_rejected!(intrinsic_raw);
    assert_query_swap_rejected!(is_copy_raw);
    assert_query_swap_rejected!(try_normalize_generic_arg_after_erasing_regions);
    assert_query_swap_rejected!(trust_contracts);
    assert_query_swap_rejected!(trust_proof_results);

    macro_rules! assert_extern_query_swap_rejected {
        ($field:ident) => {{
            let mut changed = canonical;
            changed.extern_queries.$field = defaults.extern_queries.$field;
            assert_eq!(
                changed_trust_critical_query_provider(&changed),
                Some(concat!("extern::", stringify!($field))),
                "adversarial replacement of extern `{}` escaped the Trust provider boundary",
                stringify!($field),
            );
        }};
    }
    assert_extern_query_swap_rejected!(codegen_fn_attrs);
    assert_extern_query_swap_rejected!(crate_dep_kind);
    assert_extern_query_swap_rejected!(def_kind);
    assert_extern_query_swap_rejected!(dylib_dependency_formats);
    assert_extern_query_swap_rejected!(exported_generic_symbols);
    assert_extern_query_swap_rejected!(exported_non_generic_symbols);
    assert_extern_query_swap_rejected!(has_alloc_error_handler);
    assert_extern_query_swap_rejected!(has_global_allocator);
    assert_extern_query_swap_rejected!(has_panic_handler);
    assert_extern_query_swap_rejected!(is_compiler_builtins);
    assert_extern_query_swap_rejected!(is_panic_runtime);
    assert_extern_query_swap_rejected!(is_profiler_runtime);
    assert_extern_query_swap_rejected!(native_libraries);
    assert_extern_query_swap_rejected!(num_extern_def_ids);
    assert_extern_query_swap_rejected!(panic_in_drop_strategy);
    assert_extern_query_swap_rejected!(required_panic_strategy);
    assert_extern_query_swap_rejected!(used_crate_source);

    let mut changed = canonical;
    changed.hooks.build_mir_inner_impl = |_, _| panic!("adversarial MIR builder");
    assert_eq!(changed_trust_critical_query_provider(&changed), Some("build_mir_inner_impl"));

    let mut changed = canonical;
    changed.hooks.try_destructure_mir_constant_for_user_output =
        |_, _, _| panic!("adversarial MIR constant destructurer");
    assert_eq!(
        changed_trust_critical_query_provider(&changed),
        Some("try_destructure_mir_constant_for_user_output")
    );
}

#[test]
fn adversarial_callback_cannot_replace_upstream_trust_ir_inputs() {
    let canonical = *DEFAULT_QUERY_PROVIDERS;

    macro_rules! assert_extern_query_swap_rejected {
        ($field:ident) => {{
            let mut changed = canonical;
            changed.extern_queries.$field = |_, _| panic!(
                "adversarial external `{}` provider must never execute in this comparison test",
                stringify!($field),
            );
            assert_eq!(
                changed_trust_critical_query_provider(&changed),
                Some(concat!("extern::", stringify!($field))),
                "adversarial replacement of external `{}` escaped the Trust provider boundary",
                stringify!($field),
            );
        }};
    }

    assert_extern_query_swap_rejected!(type_of);
    assert_extern_query_swap_rejected!(fn_sig);
    assert_extern_query_swap_rejected!(generics_of);
    assert_extern_query_swap_rejected!(adt_def);
    assert_extern_query_swap_rejected!(associated_item);
    assert_extern_query_swap_rejected!(impl_trait_header);
    assert_extern_query_swap_rejected!(codegen_fn_attrs);
    assert_extern_query_swap_rejected!(coroutine_for_closure);
    assert_extern_query_swap_rejected!(coroutine_kind);
    assert_extern_query_swap_rejected!(crate_name);
    assert_extern_query_swap_rejected!(def_kind);
    assert_extern_query_swap_rejected!(def_span);
    assert_extern_query_swap_rejected!(fn_arg_idents);
    assert_extern_query_swap_rejected!(attrs_for_def);
    assert_extern_query_swap_rejected!(defined_lang_items);
    assert_extern_query_swap_rejected!(diagnostic_items);
    assert_extern_query_swap_rejected!(intrinsic_raw);
}

#[test]
fn unrelated_backend_and_callback_query_overrides_remain_available() {
    let mut providers = *DEFAULT_QUERY_PROVIDERS;
    let defaults = Providers::default();
    // LLVM/GCC backend customization.
    providers.queries.global_backend_features = defaults.queries.global_backend_features;
    // rustdoc's reduced lint surface.
    providers.queries.lint_mod = defaults.queries.lint_mod;
    providers.queries.used_trait_imports = defaults.queries.used_trait_imports;
    // Proof telemetry is diagnostic-only and cannot change a verdict.
    providers.queries.trust_proof_telemetry = defaults.queries.trust_proof_telemetry;
    assert_eq!(changed_trust_critical_query_provider(&providers), None);
}

#[test]
fn canonical_provider_boundary_is_inactive_for_vanilla_rustc_frontends() {
    let mut providers = *DEFAULT_QUERY_PROVIDERS;
    providers.queries.mir_built = Providers::default().queries.mir_built;
    assert_eq!(
        trust_critical_provider_violation(&providers, false),
        None,
        "-Ztrust-verify=off frontends that do not lower Trust IR retain upstream override authority"
    );
    assert_eq!(trust_critical_provider_violation(&providers, true), Some("mir_built"));
}
