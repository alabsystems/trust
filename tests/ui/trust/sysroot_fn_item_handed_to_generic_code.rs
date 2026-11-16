//@ revisions: aus_current_certify aus_now_certify aus_random_state_certify aus_park_certify
//@ revisions: park_certify yield_now_certify sleep_certify bare_current_certify
//@ revisions: aus_current_ms aus_now_ms aus_random_state_ms park_ms sleep_ms bare_current_ms
//@ revisions: catch_unwind_current_certify
//@ revisions: aus_default_certify drop_certify aus_string_new_certify aus_default_ms drop_ms
//@ revisions: aus_current_default park_default
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[aus_current_certify] compile-flags: -Ztrust-policy=certify
//@[aus_now_certify] compile-flags: -Ztrust-policy=certify
//@[aus_random_state_certify] compile-flags: -Ztrust-policy=certify
//@[aus_park_certify] compile-flags: -Ztrust-policy=certify
//@[park_certify] compile-flags: -Ztrust-policy=certify
//@[yield_now_certify] compile-flags: -Ztrust-policy=certify
//@[sleep_certify] compile-flags: -Ztrust-policy=certify
//@[bare_current_certify] compile-flags: -Ztrust-policy=certify
//@[aus_current_ms] compile-flags: -Ztrust-policy=memory-safe
//@[aus_now_ms] compile-flags: -Ztrust-policy=memory-safe
//@[aus_random_state_ms] compile-flags: -Ztrust-policy=memory-safe
//@[park_ms] compile-flags: -Ztrust-policy=memory-safe
//@[sleep_ms] compile-flags: -Ztrust-policy=memory-safe
//@[bare_current_ms] compile-flags: -Ztrust-policy=memory-safe
//@[catch_unwind_current_certify] compile-flags: -Ztrust-policy=certify
//@[aus_default_certify] compile-flags: -Ztrust-policy=certify
//@[drop_certify] compile-flags: -Ztrust-policy=certify
//@[aus_string_new_certify] compile-flags: -Ztrust-policy=certify
//@[aus_default_ms] compile-flags: -Ztrust-policy=memory-safe
//@[drop_ms] compile-flags: -Ztrust-policy=memory-safe
//@[aus_current_certify] check-fail
//@[aus_now_certify] check-fail
//@[aus_random_state_certify] check-fail
//@[aus_park_certify] check-fail
//@[park_certify] check-fail
//@[yield_now_certify] check-fail
//@[sleep_certify] check-fail
//@[bare_current_certify] check-fail
//@[aus_current_ms] check-fail
//@[aus_now_ms] check-fail
//@[aus_random_state_ms] check-fail
//@[park_ms] check-fail
//@[sleep_ms] check-fail
//@[bare_current_ms] check-fail
//@[catch_unwind_current_certify] check-fail
//@[aus_default_certify] check-fail
//@[drop_certify] check-pass
//@[aus_string_new_certify] check-fail
//@[aus_default_ms] check-fail
//@[drop_ms] check-pass
//@[aus_current_default] check-pass
//@[park_default] check-pass
//@ dont-check-compiler-stderr
//@[aus_current_certify] dont-require-annotations: ERROR
//@[aus_now_certify] dont-require-annotations: ERROR
//@[aus_random_state_certify] dont-require-annotations: ERROR
//@[aus_park_certify] dont-require-annotations: ERROR
//@[park_certify] dont-require-annotations: ERROR
//@[yield_now_certify] dont-require-annotations: ERROR
//@[sleep_certify] dont-require-annotations: ERROR
//@[bare_current_certify] dont-require-annotations: ERROR
//@[aus_current_ms] dont-require-annotations: ERROR
//@[aus_now_ms] dont-require-annotations: ERROR
//@[aus_random_state_ms] dont-require-annotations: ERROR
//@[park_ms] dont-require-annotations: ERROR
//@[sleep_ms] dont-require-annotations: ERROR
//@[bare_current_ms] dont-require-annotations: ERROR
//@[catch_unwind_current_certify] dont-require-annotations: ERROR
//@[aus_default_certify] dont-require-annotations: ERROR
//@[drop_certify] dont-require-annotations: ERROR
//@[aus_string_new_certify] dont-require-annotations: ERROR
//@[aus_default_ms] dont-require-annotations: ERROR
//@[drop_ms] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A std/core/alloc function ITEM handed to generic code as a value — bare, or
//! inside `AssertUnwindSafe` — is called inside that code through its `FnOnce`
//! shim, where no row of the caller is guaranteed to charge it. Under
//! `-Ztrust-policy=certify` and `-Ztrust-policy=memory-safe`, which refuse the
//! `runtime_checked` row the default policy tolerates for such a std routine, it
//! must be refused unless it needs no such row.
//!
//! The indirect-call gate asked a foreign item with
//! `foreign_fn_item_type_arg_is_accounted`, whose vanilla-sysroot arm (the default
//! policy's standard) it applied on EVERY policy.
//!
//! BEFORE (stage 1 of `6011b74bad` — main `77e5f14c07` plus the wave-9 commits —
//! each revision's own flags with `--emit=metadata`, diagnostics matched as
//! compiletest matches them; measured 2026-10-03):
//!  * the seven `aus_*_certify`/`park_certify`/`yield_now_certify`/`sleep_certify`
//!    and the five `aus_*_ms`/`park_ms`/`sleep_ms` revisions built exit 0 with no
//!    error, and the same programs built exit 0 under `-Ztrust-policy=strict`;
//!  * `bare_current_certify` and `bare_current_ms` exited 1, refused only by the bare
//!    twin's absent-callee row, which survives because `strip_generics` misreads the
//!    `->` of the item type; the gate's NOTE (certify) and ERROR (memory-safe) they
//!    carry here were missing, so their refusal no longer rests on that parse;
//!  * `catch_unwind_current_certify` was already refused by other rows (a pin), and
//!    every check-pass revision passed.
//! `std::thread::current` panics once the thread's TLS is torn down.
//!
//! AFTER (predicted, then MEASURED on the stage 1 of `1ab78ed8e8`, where every
//! revision behaves as annotated): on `certify` and memory-safe the gate resolves a
//! foreign item only when it is a constructor or a sysroot item
//! `sysroot_fn_item_cannot_panic` proves (`trust_verify/sysroot_callable_item.rs`),
//! and the refusal names it.
//!
//! Controls, measured the same before: `<u32 as Default>::default`, `drop::<u32>`
//! and `String::new` handed over pass certify and memory-safe, and stay passing —
//! each is shown unable to panic (measured on the same stage 1 with the vanilla arm
//! switched off by a `#[global_allocator]`, which leaves exactly the new rule). The
//! default policy keeps the vanilla arm (`*_default` build, before and after).
//!
//! Trust (POISON-EVICTION-FALSE-PROOF-1, 2026-11-12): RE-PINNED. The two
//! `AssertUnwindSafe` controls under certify and memory-safe (`aus_default_*`,
//! `aus_string_new_certify`) now refuse; `drop_certify`/`drop_ms` still pass and keep
//! the gate's admitting path. Each control passed only because the poison loop evicted
//! the bundled `<AssertUnwindSafe<fn() -> _ {item}> as FnOnce<()>>::call_once` and then
//! `Option::unwrap_or_else`, and the withdrawn call took credit. The loop now keeps a
//! member that a retained call still names (MEASURED with `TRUST_MEMBER_PANIC_CENSUS=1`
//! on this branch's stage 1: `evicting=[]`, `call_once … called by
//! Option::<_>::unwrap_or_else`), and the kept shim's call to the item's own
//! `<fn() -> _ {item} as FnOnce<()>>::call_once` is an absent-callee row that certify
//! and memory-safe refuse. The item still cannot panic; what is lost is lowering that
//! shim call to the item's body. The lost admission is docs/DECISION_QUEUE.md
//! POISON-EVICTION-KEEP-1.

use std::panic::AssertUnwindSafe;

#[cfg(any(aus_current_certify, aus_current_default))]
// ZERO-ROW-GATE (2026-10-10) refused this body while it published zero rows. Since the merge of
// 2026-10-14 the call carries the counted panic-freedom aggregate (the soundness line's
// carrier for a call into a bundled body), kept `runtime_checked`: `0 proved, 1
// runtime-checked`, a default-policy warning, so the default policy keeps the vanilla
// arm again, as the header says (measured on the merged stage 1, 2026-10-15). The gate
// is unchanged; the body is no longer zero-row.
pub fn p(o: Option<std::thread::Thread>) -> std::thread::Thread {
    //[aus_current_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[aus_current_certify]~| NOTE current` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(AssertUnwindSafe(std::thread::current))
}

#[cfg(aus_current_ms)]
pub fn p(o: Option<std::thread::Thread>) -> std::thread::Thread {
    //[aus_current_ms]~^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`: a function called through a fn pointer
    //[aus_current_ms]~| NOTE current` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(AssertUnwindSafe(std::thread::current))
}

#[cfg(aus_now_certify)]
pub fn p(o: Option<std::time::Instant>) -> std::time::Instant {
    //[aus_now_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[aus_now_certify]~| NOTE now` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(AssertUnwindSafe(std::time::Instant::now))
}

#[cfg(aus_now_ms)]
pub fn p(o: Option<std::time::Instant>) -> std::time::Instant {
    //[aus_now_ms]~^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`: a function called through a fn pointer
    //[aus_now_ms]~| NOTE now` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(AssertUnwindSafe(std::time::Instant::now))
}

#[cfg(aus_random_state_certify)]
pub fn p(
    //[aus_random_state_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[aus_random_state_certify]~| NOTE new` is a std/core/alloc function handed to generic code as a value
    o: Option<std::collections::hash_map::RandomState>,
) -> std::collections::hash_map::RandomState {
    o.unwrap_or_else(AssertUnwindSafe(std::collections::hash_map::RandomState::new))
}

#[cfg(aus_random_state_ms)]
pub fn p(
    //[aus_random_state_ms]~^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`: a function called through a fn pointer
    //[aus_random_state_ms]~| NOTE new` is a std/core/alloc function handed to generic code as a value
    o: Option<std::collections::hash_map::RandomState>,
) -> std::collections::hash_map::RandomState {
    o.unwrap_or_else(AssertUnwindSafe(std::collections::hash_map::RandomState::new))
}

#[cfg(aus_park_certify)]
pub fn p(o: Option<()>) {
    //[aus_park_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[aus_park_certify]~| NOTE park` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(AssertUnwindSafe(std::thread::park))
}

#[cfg(any(park_certify, park_default))]
// ZERO-ROW-GATE (2026-10-10) refused this body while it published zero rows. Since the merge of
// 2026-10-14 the call carries the counted panic-freedom aggregate (the soundness line's
// carrier for a call into a bundled body), kept `runtime_checked`: `0 proved, 1
// runtime-checked`, a default-policy warning, so the default policy keeps the vanilla
// arm again, as the header says (measured on the merged stage 1, 2026-10-15). The gate
// is unchanged; the body is no longer zero-row.
pub fn p(o: Option<()>) {
    //[park_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[park_certify]~| NOTE park` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(std::thread::park)
}

#[cfg(park_ms)]
pub fn p(o: Option<()>) {
    //[park_ms]~^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`: a function called through a fn pointer
    //[park_ms]~| NOTE park` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(std::thread::park)
}

#[cfg(yield_now_certify)]
pub fn p(o: Option<()>) {
    //[yield_now_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[yield_now_certify]~| NOTE yield_now` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(std::thread::yield_now)
}

#[cfg(sleep_certify)]
pub fn p(o: Option<std::time::Duration>) -> Option<()> {
    //[sleep_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[sleep_certify]~| NOTE sleep` is a std/core/alloc function handed to generic code as a value
    o.map(std::thread::sleep)
}

#[cfg(sleep_ms)]
pub fn p(o: Option<std::time::Duration>) -> Option<()> {
    //[sleep_ms]~^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`: a function called through a fn pointer
    //[sleep_ms]~| NOTE sleep` is a std/core/alloc function handed to generic code as a value
    o.map(std::thread::sleep)
}

#[cfg(bare_current_certify)]
pub fn p(o: Option<std::thread::Thread>) -> std::thread::Thread {
    //[bare_current_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[bare_current_certify]~| NOTE current` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(std::thread::current)
}

#[cfg(bare_current_ms)]
pub fn p(o: Option<std::thread::Thread>) -> std::thread::Thread {
    //[bare_current_ms]~^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`: a function called through a fn pointer
    //[bare_current_ms]~| NOTE current` is a std/core/alloc function handed to generic code as a value
    o.unwrap_or_else(std::thread::current)
}

#[cfg(catch_unwind_current_certify)]
pub fn p() -> Option<std::thread::Thread> {
    //[catch_unwind_current_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    std::panic::catch_unwind(AssertUnwindSafe(std::thread::current)).ok()
}

// ---- controls ----

#[cfg(any(aus_default_certify, aus_default_ms))]
pub fn p(o: Option<u32>) -> u32 {
    //[aus_default_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    //[aus_default_ms]~^^ ERROR Trust memory-safe verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    o.unwrap_or_else(AssertUnwindSafe(<u32 as Default>::default))
}

#[cfg(any(drop_certify, drop_ms))]
pub fn p(o: Option<u32>) -> Option<()> {
    o.map(drop::<u32>)
}

#[cfg(aus_string_new_certify)]
pub fn p(o: Option<String>) -> String {
    //[aus_string_new_certify]~^ ERROR Trust strict verification failed for `sysroot_fn_item_handed_to_generic_code::p`
    o.unwrap_or_else(AssertUnwindSafe(String::new))
}
