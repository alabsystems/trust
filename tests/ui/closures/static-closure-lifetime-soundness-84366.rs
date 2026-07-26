// tRust compatibility guard for rust-lang#84366-shaped code.
//
// Current upstream-compatible Rust accepts this generic associated-type pattern
// once the Display obligation is explicit. A future verifier-only rejection must
// not leak into vanilla upstream compatibility mode.
//@ check-pass

use std::fmt;

trait Trait {
    type Associated;
}

impl<R, F: Fn() -> R> Trait for F {
    type Associated = R;
}

fn static_transfers_to_associated<T: Trait + 'static>(
    _: &T,
    x: T::Associated,
) -> Box<dyn fmt::Display>
where
    T::Associated: fmt::Display,
{
    Box::new(x)
}

fn make_static_displayable<'a>(s: &'a str) -> Box<dyn fmt::Display> {
    let f = || -> &'a str { "" };
    static_transfers_to_associated(&f, s)
}

fn main() {
    let d;
    {
        let x = "Hello World".to_string();
        d = make_static_displayable(&x);
    }
    println!("{}", d);
}
