//@ revisions: compose_scope compose_scope_off bundle_cap bundle_cap_default max_bundle max_bundle_default no_declared no_declared_off mc_on mc_off
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[compose_scope] rustc-env:TRUST_COMPOSE_NO_SCOPE=1
//@[compose_scope_off] rustc-env:TRUST_COMPOSE_NO_SCOPE=0
//@[bundle_cap] rustc-env:TRUST_BUNDLE_CAP=128
//@[bundle_cap_default] rustc-env:TRUST_BUNDLE_CAP=32
//@[max_bundle] rustc-env:TRUST_MAX_BUNDLE_FUNCTIONS=512
//@[max_bundle_default] rustc-env:TRUST_MAX_BUNDLE_FUNCTIONS=96
//@[no_declared] rustc-env:TRUST_NO_BUNDLE_DECLARED=1
//@[no_declared_off] rustc-env:TRUST_NO_BUNDLE_DECLARED=0
//@[mc_on] rustc-env:TRUST_MC_DATAFLOW_CHC=1
//@[mc_off] rustc-env:TRUST_MC_DATAFLOW_CHC=0
//@ check-fail
//@ dont-check-compiler-stderr

// Trust: these are presence-based refusals of untracked semantic inputs.
// Off/default-valued spellings are included deliberately; this file grants
// no experiment, bundle, CHC result, or proof credit.
pub fn identity(value: u32) -> u32 {
    value
}
//[compose_scope]~? ERROR environment variable `TRUST_COMPOSE_NO_SCOPE` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[compose_scope_off]~? ERROR environment variable `TRUST_COMPOSE_NO_SCOPE` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[bundle_cap]~? ERROR environment variable `TRUST_BUNDLE_CAP` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[bundle_cap_default]~? ERROR environment variable `TRUST_BUNDLE_CAP` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[max_bundle]~? ERROR environment variable `TRUST_MAX_BUNDLE_FUNCTIONS` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[max_bundle_default]~? ERROR environment variable `TRUST_MAX_BUNDLE_FUNCTIONS` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[no_declared]~? ERROR environment variable `TRUST_NO_BUNDLE_DECLARED` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[no_declared_off]~? ERROR environment variable `TRUST_NO_BUNDLE_DECLARED` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[mc_on]~? ERROR environment variable `TRUST_MC_DATAFLOW_CHC` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[mc_off]~? ERROR environment variable `TRUST_MC_DATAFLOW_CHC` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
