//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 19 review (2026-10-06): a vtable carrier demanded from a discharge is
//! verified CALLEE-FIRST. Both coercions are declared before the carrier impls and
//! before the carriers' local callee (`helper`/`helper_v`), so no call edge orders
//! them first: the discharge demands `<W<T> as Run>::run`'s verification itself.
//! Before the fix it demanded the carrier alone, which was then verified before its
//! callee, found no `Via` record for `helper` and was refused ("Trust strict
//! verification failed for `<W<T> as Run>::run`", `early_good` refused on strict);
//! and `early_bad` got NO discharge row (`helper_v::<Bad>` was walked before
//! `helper_v` was in the ledger). Now:
//! * `early_good` (control): no error; the carrier keeps its advisory warning;
//! * `early_bad`: a `failed` discharge row naming the vtable of `V<Bad>`.
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;
pub struct Bad;

// Both coercions are declared BEFORE the carrier impls and before the carriers' local
// callees: the carrier is demanded from the discharge, and its callee must be verified
// before it.
pub fn early_good(w: &W<Good>) -> &dyn Run {
    w
}

pub fn early_bad(v: &V<Bad>) -> &dyn Run {
    //[advisory]~^ WARN Trust instance discharge not established for `vtable_carrier_declared_late::early_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `vtable_carrier_declared_late::early_bad`
    //[strict]~^^^ NOTE [an instance created by the vtable of `V<Bad>` as `dyn Run`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `vtable_carrier_declared_late::early_bad`
    v
}

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

impl Tr for Bad {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<vtable_carrier_declared_late::Bad as vtable_carrier_declared_late::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_carrier_declared_late::Bad as vtable_carrier_declared_late::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<vtable_carrier_declared_late::Bad as vtable_carrier_declared_late::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_carrier_declared_late::Bad as vtable_carrier_declared_late::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<vtable_carrier_declared_late::Bad as vtable_carrier_declared_late::Tr>::m`
        panic!("bad")
    }
}

pub trait Run {
    fn run(&self) -> u32;
}

pub struct W<T>(pub T);
pub struct V<T>(pub T);

impl<T: Tr> Run for W<T> {
    fn run(&self) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `<vtable_carrier_declared_late::W<T> as vtable_carrier_declared_late::Run>::run`
    //[strict]~^^ WARN Trust verification advisory for `<vtable_carrier_declared_late::W<T> as vtable_carrier_declared_late::Run>::run`
    //[certify]~^^^ ERROR Trust certify verification failed for `<vtable_carrier_declared_late::W<T> as vtable_carrier_declared_late::Run>::run`
        helper(&self.0)
    }
}

impl<T: Tr> Run for V<T> {
    fn run(&self) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `<vtable_carrier_declared_late::V<T> as vtable_carrier_declared_late::Run>::run`
    //[strict]~^^ WARN Trust verification advisory for `<vtable_carrier_declared_late::V<T> as vtable_carrier_declared_late::Run>::run`
    //[certify]~^^^ ERROR Trust certify verification failed for `<vtable_carrier_declared_late::V<T> as vtable_carrier_declared_late::Run>::run`
        helper_v(&self.0)
    }
}

fn helper<T: Tr>(t: &T) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `vtable_carrier_declared_late::helper`
    //[strict]~^^ WARN Trust verification advisory for `vtable_carrier_declared_late::helper`
    //[certify]~^^^ ERROR Trust certify verification failed for `vtable_carrier_declared_late::helper`
    t.m()
}

fn helper_v<T: Tr>(t: &T) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `vtable_carrier_declared_late::helper_v`
    //[strict]~^^ WARN Trust verification advisory for `vtable_carrier_declared_late::helper_v`
    //[certify]~^^^ ERROR Trust certify verification failed for `vtable_carrier_declared_late::helper_v`
    t.m()
}
