// Regression test for rust-lang/rust#125267
// Query structure dependent compile time issue: exponential blowup with
// chained equality-constrained trait bounds (Parser::or_unify pattern).
//
// The old trait solver exhibited exponential time complexity when resolving
// chains of `or_unify` calls with `Output = Self::Output, Error = Self::Error`
// equality constraints. The next-solver's canonical goal caching and search
// graph memoization should resolve this.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Trust: next-solver compile-time regression test

//@ check-pass
//@ compile-flags: -Znext-solver=globally

#![allow(unused_variables, dead_code)]

struct ParsedItem<'a, T> {
    value: T,
    remaining: &'a [u8],
}

trait Parser<'a>: Sized {
    type Output;
    type Error;

    fn parse(self, input: &'a [u8]) -> Result<ParsedItem<'a, Self::Output>, Self::Error> {
        loop {}
    }

    fn map<F, NewOutput>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Output) -> NewOutput + Copy,
    {
        loop {}
    }

    fn or_unify<P2>(self, other: P2) -> OrUnify<Self, P2>
    where
        P2: Parser<'a, Output = Self::Output, Error = Self::Error>,
    {
        loop {}
    }
}

struct Verbatim<'a>(&'a [u8]);

impl<'a, 'b> Parser<'a> for Verbatim<'b> {
    type Output = &'b [u8];
    type Error = ();
}

struct OrUnify<P1, P2> {
    p1: P1,
    p2: P2,
}

impl<'a, P1, P2> Parser<'a> for OrUnify<P1, P2>
where
    P1: Parser<'a>,
    P2: Parser<'a, Output = P1::Output, Error = P1::Error>,
{
    type Output = P1::Output;
    type Error = P1::Error;
}

struct Map<P, F> {
    parser: P,
    f: F,
}

impl<'a, P, F, NewOutput> Parser<'a> for Map<P, F>
where
    P: Parser<'a>,
    F: Fn(P::Output) -> NewOutput + Copy,
{
    type Output = NewOutput;
    type Error = P::Error;
}

// This chain of 9 or_unify calls caused exponential compile time (~471 seconds)
// with the old solver. With the next-solver it should complete quickly.
pub fn parse_month_name(input: &[u8]) {
    let _ = Verbatim(b"Jan")
        .map(|_| 1u8)
        .or_unify(Verbatim(b"Feb").map(|_| 2))
        .or_unify(Verbatim(b"Mar").map(|_| 3))
        .or_unify(Verbatim(b"Apr").map(|_| 4))
        .or_unify(Verbatim(b"May").map(|_| 5))
        .or_unify(Verbatim(b"Jun").map(|_| 6))
        .or_unify(Verbatim(b"Jul").map(|_| 7))
        .or_unify(Verbatim(b"Aug").map(|_| 8))
        .or_unify(Verbatim(b"Sep").map(|_| 9))
        .parse(input);
}

fn main() {}
