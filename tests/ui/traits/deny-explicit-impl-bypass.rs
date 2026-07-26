// Regression test for rust-lang#153649: final methods and #[rustc_deny_explicit_impl]
// bypass through impl checking paths.
//
// This test verifies that:
// 1. `#[rustc_deny_explicit_impl]` traits cannot have user-provided impls
// 2. `final fn` methods in traits cannot be overridden
// 3. These checks are enforced independently of coherence success

#![feature(rustc_attrs)]
#![feature(final_associated_functions)]

// Test 1: #[rustc_deny_explicit_impl] cannot be bypassed
#[rustc_deny_explicit_impl]
#[rustc_dyn_incompatible_trait]
trait SealedTrait {
    fn sealed_method() -> u32 { 42 }
}

impl SealedTrait for u32 {
    //~^ ERROR explicit impls for the `SealedTrait` trait are not permitted
    fn sealed_method() -> u32 { 0 }
}

// Test 2: final fn cannot be overridden
trait HasFinalMethod {
    final fn immutable() -> u32 { 100 }
    fn mutable() -> u32;
}

impl HasFinalMethod for u64 {
    fn immutable() -> u32 { 999 }
    //~^ ERROR cannot override `immutable` because it already has a `final` definition in the trait
    fn mutable() -> u32 { 1 }
}

// Test 3: final fn with self receiver cannot be overridden
trait HasFinalSelfMethod {
    final fn get_value(&self) -> u32 { 42 }
}

impl HasFinalSelfMethod for String {
    fn get_value(&self) -> u32 { 0 }
    //~^ ERROR cannot override `get_value` because it already has a `final` definition in the trait
}

fn main() {}
