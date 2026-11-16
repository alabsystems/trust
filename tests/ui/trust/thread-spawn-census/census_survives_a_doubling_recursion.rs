//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `grow` recurses at `(T, T)`: the n-th instance's type has 2^n leaves at
//! nesting depth n. The spawn census walked instances to the recursion limit
//! by depth alone, and rustc's own questions about a type (`needs_drop`) are
//! linear in its leaves: the compiler never finished, in the verified lane
//! with no flag as well. A type past a size limit is refused as one past the
//! depth limit is, before rustc is asked about it. Nothing calls `grow`: the
//! census walks every body.

#[allow(dead_code)]
fn grow<T: Clone>(n: u32, v: T) {
    if n > 0 {
        grow(n - 1, (v.clone(), v.clone()));
    }
}

fn main() {}
