//@ revisions: unopt opt
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//! TG3 negative control: the twin of `off_import_discharge.rs` with ONE `&&`
//! of the kernel mutated to `||`. The island's theorem is unchanged and is now
//! false about the body, so the build must fail with verification off — the
//! kernel judges the imported term of the body that is actually compiled, not
//! the clause text or the theorem's own statement.
//!
//! Before TG3 neither file could build with verification off (the island
//! needed a verification walk); a lane that refused both would pass this test
//! vacuously, which is why the positive twin exists.

pub fn member_approval(authority: bool, eligible: bool, writer: bool) -> bool
    ensures result == (authority && (eligible && writer)) by member_approval_is_exact
    //~^ ERROR cited theorem `member_approval_is_exact` is not registered
{
    authority || (eligible && writer)
}

clean {
    theorem member_approval_is_exact (authority eligible writer : Bool) :
        trust_import_off_import_mutant__member_approval authority eligible writer =
            (authority && eligible && writer) := by
      simp only [trust_import_off_import_mutant__member_approval]
}
//~^^^^^ ERROR `member_approval_is_exact` did not elaborate

fn main() {
    let _ = member_approval(true, false, false);
}
