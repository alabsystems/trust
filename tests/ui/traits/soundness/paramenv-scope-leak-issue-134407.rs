// Trust: regression test for rust-lang#134407
// Part of #859
//
// ParamEnv where-clause scope leak via escaping bound variables. Predicates
// with escaping bound variables could leak through ParamEnv both before and
// after normalization. The trait solver could instantiate these unresolved
// binders to prove obligations that should not hold, enabling unsound
// lifetime extension.
//
// The fix filters predicates with escaping bound variables from ParamEnv
// during construction and after normalization.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/134407
//
// STATUS: Fixed. Predicates with escaping bound vars are now filtered from
// ParamEnv in param_env() construction and normalize_param_env_or_error().

trait Convert<'a, 'b> {
    fn convert(x: &'a str) -> &'b str;
}

// This impl exploits escaping bound vars in the where-clause to create
// unsound implied bounds in the ParamEnv.
impl<'a, 'b> Convert<'a, 'b> for ()
where
    for<'c, 'd> &'c &'d (): Sized,
{
    fn convert(x: &'a str) -> &'b str {
        // With the bug: compiles, unsound
        // With the fix: rejected because 'a: 'b cannot be proved
        x //~ ERROR lifetime may not live long enough
    }
}

fn extend_lifetime<'a, 'b>(x: &'a str) -> &'b str {
    <() as Convert<'a, 'b>>::convert(x)
}

fn main() {
    let s = String::from("hello world");
    let r = extend_lifetime(&s);
    drop(s);
    // Use-after-free if the bug is exploitable
    println!("{}", r);
}
