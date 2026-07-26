// A unit enum contributes both an aggregate branch and its discriminant leaf
// to a valtree. This used to bypass the node limit entirely because neither
// node was counted, and the array allocated its full child vector up front.

#![feature(adt_const_params)]
#![allow(incomplete_features)]

use std::marker::ConstParamTy;

const LEN: usize = 50_000;

#[derive(Clone, Copy, ConstParamTy, Eq, PartialEq)]
enum Unit {
    Value,
}

const LARGE: [Unit; LEN] = [Unit::Value; LEN];

struct Witness<const VALUE: [Unit; LEN]>;

fn force_valtree(_: Witness<LARGE>) {}
//~^ ERROR maximum number of nodes exceeded
//~| ERROR maximum number of nodes exceeded
//~| ERROR maximum number of nodes exceeded

fn main() {}
