//@ revisions: valid bad_recursive_call
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[valid] build-pass
//@[bad_recursive_call] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Source-to-verdict soundness gate for the fresh-context definition-entry
//! `requires` exemption. The function's own exact source-owned precondition is
//! available as an entry assumption, but a recursive call is a distinct
//! call-site proof request even though its callee name and predicate text match
//! the definition. The valid revision establishes that request. The bad
//! revision passes a concrete counterexample; it must remain visible and make
//! strict verification fail rather than borrowing the definition-entry skip.

#[cfg(valid)]
pub fn recursive_requires(n: u32)
    requires n > 0
{
    if n > 1 {
        recursive_requires(n - 1);
    }
}

#[cfg(bad_recursive_call)]
pub fn recursive_requires(n: u32) //[bad_recursive_call]~ NOTE [precond] FAILED
//[bad_recursive_call]~| NOTE Trust verification: 2 proved, 1 failed
//[bad_recursive_call]~| ERROR Trust strict verification failed for
    requires n > 0
{
    if n > 0 {
        recursive_requires(0);
    }
}

fn main() {}
