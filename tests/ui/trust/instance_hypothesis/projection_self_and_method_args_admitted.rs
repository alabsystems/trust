//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 18 (pins, no behaviour change): three call shapes preview2 named on its
//! ~200 class-1 rows are ALREADY admitted by §2.3 on main, and stay so. The rows named
//! them only as the panic-freedom fold's REPRESENTATIVE (its first marked site); the
//! site that kept each row `failed` was an argument shape (item 18 shapes 1 and 2).
//! * a PROJECTION self type, `<<S as Serializer>::SerializeStruct as
//!   SerializeStruct>::serialize_field::<u32>` and `::end` (`mentions_only_own_params`
//!   walks into the alias and finds only `S`);
//! * a method with its OWN generic arguments, `next_element::<U>` (the body's own
//!   parameter) and `next_element::<u32>` (concrete): both are the body's own choice;
//! * an argument-position `impl Trait` receiver, `<impl AsRef<Name> as AsRef<Name>>::as_ref`
//!   (the synthetic parameter is the body's own).
//! Every site gets one hypothesis row and nothing is `failed`. `ser` and `next_two`
//! also carry the generic DROP-GLUE row of their projection/parameter-typed locals
//! (`[trust-drop-glue-assumption]`, `runtime_checked`; OD-1 item 14(a) keeps it out of
//! the hypothesis lane), which strict and certify refuse, unchanged here.
pub trait SerializeStruct {
    fn serialize_field<V: ?Sized>(&mut self, key: &'static str, value: &V);
    fn end(self) -> u32;
}

pub trait Serializer {
    type SerializeStruct: SerializeStruct;
    fn serialize_struct(self, name: &'static str, len: usize) -> Self::SerializeStruct;
}

pub fn ser<S: Serializer>(s: S, a: u32) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `projection_self_and_method_args_admitted::ser`: 3 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `projection_self_and_method_args_admitted::ser`: 3 instance hypothesis row(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `projection_self_and_method_args_admitted::ser`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `projection_self_and_method_args_admitted::ser`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust certify verification failed for `projection_self_and_method_args_admitted::ser`: 3 instance hypothesis row(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `projection_self_and_method_args_admitted::ser`: 1 obligation(s) were not fully verified
    let mut st = s.serialize_struct("X", 1);
    st.serialize_field("a", &a);
    st.end()
}

pub trait SeqAccess {
    fn next_element<T: Default>(&mut self) -> Option<T>;
}

pub fn next_two<A: SeqAccess, U: Default>(a: &mut A) -> (Option<U>, Option<u32>) {
    //[advisory]~^ WARN Trust verification advisory for `projection_self_and_method_args_admitted::next_two`: 2 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `projection_self_and_method_args_admitted::next_two`: 2 instance hypothesis row(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `projection_self_and_method_args_admitted::next_two`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `projection_self_and_method_args_admitted::next_two`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust certify verification failed for `projection_self_and_method_args_admitted::next_two`: 2 instance hypothesis row(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `projection_self_and_method_args_admitted::next_two`: 1 obligation(s) were not fully verified
    let u = a.next_element::<U>();
    let n = a.next_element::<u32>();
    (u, n)
}

pub struct Name;

pub trait Width {
    fn width(&self) -> u32;
}

pub fn impl_arg<W: Width>(vb: &impl AsRef<W>) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `projection_self_and_method_args_admitted::impl_arg`: 2 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `projection_self_and_method_args_admitted::impl_arg`: 2 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `projection_self_and_method_args_admitted::impl_arg`: 2 instance hypothesis row(s)
    vb.as_ref().width()
}
