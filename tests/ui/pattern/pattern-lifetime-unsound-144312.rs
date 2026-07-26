// Trust: Regression test for rust-lang#144312
// Match ergonomics pattern binding lifetime unsoundness.
//
// When match ergonomics implicitly peels references from the scrutinee type,
// the binding created for a variable must not have a lifetime that exceeds the
// peeled reference's lifetime. Without the subregion constraint, this code could
// compile and produce a dangling reference.
//
// The unsoundness requires: a structural pattern (tuple, struct, etc.) that triggers
// auto-peeling of a reference, followed by a binding that inherits by-ref mode.

fn tuple_pattern_lifetime_escape() -> &'static i32 {
    let local = 42;
    let r: &(i32, i32) = &(local, 0);

    // Match ergonomics peels the `&` from `&(i32, i32)`, giving inherited binding
    // mode `ref`. The binding `x` gets type `&'fresh i32`. Without the fix, `'fresh`
    // is unconstrained and could extend beyond `r`'s lifetime.
    let x = match r {
        (x, _) => x,
    };
    x //~ ERROR cannot return value referencing
}

fn nested_ref_tuple_escape() -> &'static i32 {
    let local = 10;
    let inner: &(i32,) = &(local,);
    let outer: &&(i32,) = &inner;

    // Double peel: &&(i32,) -> &(i32,) -> (i32,). Binding gets `ref` for `i32`.
    // The fresh region must be bounded by the outermost peeled region.
    let val = match outer {
        (v,) => v,
    };
    val //~ ERROR cannot return value referencing
}

fn struct_pattern_lifetime_escape() -> &'static i32 {
    struct Pair {
        first: i32,
        second: i32,
    }

    let local = Pair { first: 1, second: 2 };
    let r: &Pair = &local;

    // Match ergonomics peels `&Pair`, giving default binding mode `ref`.
    // The binding for `first` must not outlive the peeled reference.
    let escaped = match r {
        Pair { first, .. } => first,
    };
    escaped //~ ERROR cannot return value referencing
}

fn main() {}
