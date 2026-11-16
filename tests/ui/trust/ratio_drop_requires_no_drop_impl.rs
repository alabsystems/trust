//@ revisions: default certify
//@ needs-trust-verify
//@ aux-build:num_rational_evil.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! A type's drop is panic-free because the compiler certified it has no panicking
//! `Drop`, never because its path looks like `num_rational::Ratio` (RATIO-DROP-1).
//!
//! The bridge's drop classifier (`is_panic_free_drop_ext`) had an arm for
//! `name.starts_with("num_rational") && name.ends_with("::Ratio")` that walked the
//! fields as if the type had no `Drop` impl. `auxiliary/num_rational_evil.rs`, a
//! verify-off dependency, defines `Ratio { x: u8 }` with a `Drop` that panics; its
//! path matched, so `victim`'s `drop(r)` read panic-free: `victim` drew no
//! diagnostic, and alone in a crate it built exit 0 under certify (`assert proved`,
//! trust-mc, `1 proved`). The run witness (`ratio_drop_requires_no_drop_impl_run.rs`)
//! panics `evil Ratio drop`.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, 2026-10-04; each
//! revision's flags with `--emit=metadata`, the aux built with its own flags):
//! `victim` drew no diagnostic in either revision. `victim_scope_end`, which drops
//! `r` at the end of its own body, was refused already by the root-body check ("this
//! body drops a value whose type carries `num_rational_evil::Ratio`"), but its bridge
//! row was ALSO read panic-free, so its Level-0 diagnostic was missing. The two
//! `victim` annotations and the `victim_scope_end` Level-0 annotation did not fire;
//! the `full verification failed` annotation fires BEFORE as well.
//!
//! AFTER (predicted, then measured): the name arm is gone (both the `Ty::Adt` and
//! the `Ty::Datatype` spelling), so the drop is credited only through the compiler's
//! `structural_drop` set (`!has_dtor`, or a destructor proved panic-free), which a
//! panicking `Drop` never enters. The annotations are what the BEFORE compiler prints
//! for a twin of this file that links the same dependency under the crate name
//! `evil_ratio` (`extern crate evil_ratio as num_rational_evil;`): the drop-glue row
//! `[trust-drop-glue-assumption] drop glue for `evil_ratio::Ratio` has unproven
//! panic-freedom` stays `runtime_checked`; default a WARN and an ERROR per
//! function, certify two ERRORs.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `victim` and `victim_scope_end` read
//! `assert runtime_checked` (the drop-glue row) instead of proved.
//!
//! The real `num_rational::Ratio` has no `Drop` impl, so the compiler's closure puts
//! it in `structural_drop` and its fields are walked exactly as before; that path is
//! pinned by the trust-ir-bridge unit test
//! `a_structural_ratio_walks_its_fields_in_both_spellings`.

extern crate num_rational_evil;

pub fn victim(r: num_rational_evil::Ratio) -> u8 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `ratio_drop_requires_no_drop_impl::victim`
    //[default]~^^ ERROR Trust strict verification failed for `ratio_drop_requires_no_drop_impl::victim`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `ratio_drop_requires_no_drop_impl::victim`
    //[certify]~^^^^ ERROR Trust strict verification failed for `ratio_drop_requires_no_drop_impl::victim`
    let v = r.x;
    drop(r);
    v
}

pub fn victim_scope_end(r: num_rational_evil::Ratio) -> u8 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `ratio_drop_requires_no_drop_impl::victim_scope_end`
    //[default]~^^ ERROR Trust full verification failed for `ratio_drop_requires_no_drop_impl::victim_scope_end`: this body drops a value whose type carries
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `ratio_drop_requires_no_drop_impl::victim_scope_end`
    //[certify]~^^^^ ERROR Trust full verification failed for `ratio_drop_requires_no_drop_impl::victim_scope_end`: this body drops a value whose type carries
    r.x
}
