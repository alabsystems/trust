//@ known-bug: #84591
//@ check-pass
// Trust: regression test for rust-lang#84591
// Part of #859
//
// HRTB on subtrait unsoundly provides HRTB on supertrait with weaker
// implied bounds. When a subtrait bound like
//   `for<'a, 'b> Subtrait<'a, 'b, &'b &'a ()>`
// requires `'a: 'b` for the type `&'b &'a ()` to be well-formed,
// the compiler incorrectly implies
//   `for<'a, 'b> Supertrait<'a, 'b>`
// where `'a` and `'b` are universally quantified WITHOUT the outlives
// relation. This allows extending arbitrary lifetimes.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/84591
//
// STATUS: This currently COMPILES on stable Rust since 1.7 (unsound).
// When fixed, the compiler should reject the implied supertrait bound.

trait Subtrait<'a, 'b, R>: Supertrait<'a, 'b> {}
trait Supertrait<'a, 'b> {
    fn convert<T: ?Sized>(x: &'a T) -> &'b T;
}

fn need_hrtb_subtrait<'a_, 'b_, S, T: ?Sized>(x: &'a_ T) -> &'b_ T
where
    S: for<'a, 'b> Subtrait<'a, 'b, &'b &'a ()>,
{
    need_hrtb_supertrait::<S, T>(x)
}

fn need_hrtb_supertrait<'a_, 'b_, S, T: ?Sized>(x: &'a_ T) -> &'b_ T
where
    S: for<'a, 'b> Supertrait<'a, 'b>,
{
    S::convert(x)
}

struct MyStruct;
impl<'a: 'b, 'b> Supertrait<'a, 'b> for MyStruct {
    fn convert<T: ?Sized>(x: &'a T) -> &'b T {
        x
    }
}
impl<'a, 'b> Subtrait<'a, 'b, &'b &'a ()> for MyStruct {}

fn extend_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    need_hrtb_subtrait::<MyStruct, T>(x)
}

fn main() {
    let d;
    {
        let x = "Hello World".to_string();
        d = extend_lifetime(&x);
    }
    // Use-after-free: prints garbage if the bug is exploitable.
    println!("{}", d);
}
