//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: diverging_name_dep.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! A panic NAME is not a panic entry point (DIVERGE-ANCHOR-1).
//!
//! trust-ir-bridge lowers a diverging call (`target: None`) whose callee name matches
//! `is_panic_call`, `is_diverging_panic_or_abort_terminal` or `is_ub_if_reached_call`
//! to `Assert(false)` + a `PanicFreedom` row + `Unreachable`, and that encoding
//! REPLACES the `[trust-absent-callee-assumption] ... may panic` row an absent callee
//! otherwise carries. The two are not equally strict: under the default policy the
//! site row is `runtime_checked` and accepted while the absent-callee row is refused,
//! and a UB name mints no whole-function aggregate, so under certify nothing public was
//! left. The extractor routed an uninhabited NON-`!` return (`-> Void`) the same way,
//! by name. Each `v_*` below calls the dependency's same-named function with
//! `null_mut()` at `x == 5`; every callee body segfaults there.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, each revision's flags
//! with `--emit=metadata`, 2026-10-04): under default every named `-> !` victim and
//! `v_void_panicking_x`/`v_void_process_abort` printed only warnings
//! (`panic freedom ... is reachable`, runtime_checked) and was ACCEPTED, and
//! `v_intrinsics_unreachable`/`v_void_intrinsics_unreachable` printed nothing; under
//! certify the UB pair still printed nothing (only a `native-verification-gap` row).
//! Under memory-safe every victim was already refused (the UB pair without its Level 0
//! warning). The controls `v_boom` and `v_void_boom` were refused in every revision. Linking
//! the default-accepted library and calling `v(5)` exits 139 (SIGSEGV) for
//! `panicking::anything` and `unwrap_failed`, and for `intrinsics::unreachable`
//! accepted under certify.
//!
//! AFTER (predicted, then measured): the bridge arm also requires the call's
//! `callee_key` to say "defined in a real sysroot crate", and the extractor routing the
//! same of the callee's DefId, so every victim takes its control's path: a `-> !`
//! callee keeps the absent-callee row, a `-> Void` callee stays an unsupported
//! terminator. The annotations are what the BEFORE compiler prints for a twin of this
//! file, line for line, whose dependency renames every function to a name no
//! recognizer matches (`b000` ... `void::b103`): exactly the path the fix leaves.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. Each named `-> !` victim reads as
//! `v_boom`, each `-> Void` victim as `v_void_boom`.

#![allow(unreachable_code)]

extern crate diverging_name_dep as dep;

pub fn v_panic_nounwind(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_panic_nounwind`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_panic_nounwind`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_panic_nounwind`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_panic_nounwind`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::panic_nounwind(core::ptr::null_mut())
    }
    x
}

pub fn v_panicking_anything(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_panicking_anything`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_panicking_anything`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_panicking_anything`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_panicking_anything`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::panicking::anything(core::ptr::null_mut())
    }
    x
}

pub fn v_unwrap_failed(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_unwrap_failed`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_unwrap_failed`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_unwrap_failed`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_unwrap_failed`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::unwrap_failed(core::ptr::null_mut())
    }
    x
}

pub fn v_expect_failed(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_expect_failed`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_expect_failed`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_expect_failed`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_expect_failed`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::expect_failed(core::ptr::null_mut())
    }
    x
}

pub fn v_raw_vec_handle_error(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_raw_vec_handle_error`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_raw_vec_handle_error`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_raw_vec_handle_error`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_raw_vec_handle_error`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::raw_vec::handle_error(core::ptr::null_mut())
    }
    x
}

pub fn v_raw_vec_capacity_overflow(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_raw_vec_capacity_overflow`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_raw_vec_capacity_overflow`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_raw_vec_capacity_overflow`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_raw_vec_capacity_overflow`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::raw_vec::capacity_overflow(core::ptr::null_mut())
    }
    x
}

pub fn v_handle_alloc_error(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_handle_alloc_error`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_handle_alloc_error`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_handle_alloc_error`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_handle_alloc_error`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::handle_alloc_error(core::ptr::null_mut())
    }
    x
}

pub fn v_rust_alloc_error_handler(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_rust_alloc_error_handler`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_rust_alloc_error_handler`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_rust_alloc_error_handler`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_rust_alloc_error_handler`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::__rust_alloc_error_handler(core::ptr::null_mut())
    }
    x
}

pub fn v_rdl_oom(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_rdl_oom`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_rdl_oom`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_rdl_oom`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_rdl_oom`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::__rdl_oom(core::ptr::null_mut())
    }
    x
}

pub fn v_process_abort(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_process_abort`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_process_abort`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_process_abort`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_process_abort`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::process::abort(core::ptr::null_mut())
    }
    x
}

pub fn v_intrinsics_abort(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_intrinsics_abort`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_intrinsics_abort`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_intrinsics_abort`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_intrinsics_abort`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::intrinsics::abort(core::ptr::null_mut())
    }
    x
}

pub fn v_slice_index_fail(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_slice_index_fail`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_slice_index_fail`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_slice_index_fail`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_slice_index_fail`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::slice_index_fail(core::ptr::null_mut())
    }
    x
}

pub fn v_do_panic_runtime(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_do_panic_runtime`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_do_panic_runtime`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_do_panic_runtime`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_do_panic_runtime`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::do_panic::runtime(core::ptr::null_mut())
    }
    x
}

pub fn v_int_log10_panic_for_nonpositive_argument(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_int_log10_panic_for_nonpositive_argument`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_int_log10_panic_for_nonpositive_argument`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_int_log10_panic_for_nonpositive_argument`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_int_log10_panic_for_nonpositive_argument`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::int_log10::panic_for_nonpositive_argument(core::ptr::null_mut())
    }
    x
}

pub fn v_thread_local_panic_access_error(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_thread_local_panic_access_error`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_thread_local_panic_access_error`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_thread_local_panic_access_error`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_thread_local_panic_access_error`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::thread::local::panic_access_error(core::ptr::null_mut())
    }
    x
}

pub fn v_intrinsics_unreachable(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_intrinsics_unreachable`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_intrinsics_unreachable`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_intrinsics_unreachable`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_intrinsics_unreachable`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::intrinsics::unreachable(core::ptr::null_mut())
    }
    x
}

pub fn v_boom(x: u32) -> u32 {
    //[default,memsafe]~^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_boom`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `diverging_site_requires_sysroot_callee::v_boom`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_boom`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_boom`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        dep::boom(core::ptr::null_mut())
    }
    x
}

pub fn v_void_panicking_x(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_panicking_x`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_sysroot_callee::v_void_panicking_x`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_panicking_x`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_void_panicking_x`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match dep::void::panicking::x(core::ptr::null_mut()) {}
    }
    x
}

pub fn v_void_process_abort(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_process_abort`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_sysroot_callee::v_void_process_abort`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_process_abort`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_void_process_abort`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match dep::void::process::abort(core::ptr::null_mut()) {}
    }
    x
}

pub fn v_void_intrinsics_unreachable(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_intrinsics_unreachable`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_sysroot_callee::v_void_intrinsics_unreachable`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_intrinsics_unreachable`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_void_intrinsics_unreachable`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match dep::void::intrinsics::unreachable(core::ptr::null_mut()) {}
    }
    x
}

pub fn v_void_boom(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_boom`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust full verification failed for `diverging_site_requires_sysroot_callee::v_void_boom`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `diverging_site_requires_sysroot_callee::v_void_boom`: 1 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `diverging_site_requires_sysroot_callee::v_void_boom`: at least one result is not an authenticated memory-safe assumption
    if x == 5 {
        match dep::void::boom(core::ptr::null_mut()) {}
    }
    x
}
