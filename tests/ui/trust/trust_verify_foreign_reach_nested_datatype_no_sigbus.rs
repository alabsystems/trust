//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust

// Trust: a NESTED datatype handed to a sysroot generic took `trustc` down with a SIGBUS —
// a native stack overflow inside the verifier — under the DEFAULT (strict) policy.
//
// REPRODUCED 2026-09-26 on stage2 `29b6f15c7`: `push_nested` below, alone in a crate,
// exits 138 (SIGBUS) in 2 s with `-Ztrust-verify=on`, and compiles with it off. Its
// backtrace is one cycle, "recursed 39 times" before the printer gave up:
// `trust_verify::ty_reaches_foreign_user_code` through `AdtDef::all_fields`.
//
// THE MECHANISM. A body that fails full verification is re-examined for a MASKED
// fail-closed source, and a sysroot callee (`Vec::push` here) instantiated at a type
// that can reach foreign code counts as one. `ty_reaches_foreign_user_code` answers that
// by walking the type: a local or sysroot ADT through its arguments AND its fields. Its
// only cut was a memo, and a memo only cuts a type it has SEEN. `Nested<u8>` reaches
// `Nested<Vec<u8>>` through `Box`, which reaches `Nested<Vec<Vec<u8>>>`, each a new type,
// so the walk never met one twice and ran until the stack did. The fix cuts a re-entry of
// the same ADT at strictly larger arguments — the extractor's own rule for this shape —
// and answers `true`, the predicate's fail-closed answer.
//
// WHY `check-fail` IS THE ASSERTION. These bodies do not verify (`Vec::push` has an
// unproved panic edge), so a correct compiler exits 1 with a verification error.
// compiletest compares the exit status with 1, and a compiler that dies on a signal has
// none, so this file is red on the crash and green on any ordinary verdict. Which verdict
// is not the point; that `trustc` returns one is. Under `-Ztrust-policy=advisory` (what
// `targo trust check --allow-l0-gaps` passes) the walk is not reached at all — measured,
// the same file exits 0 there — which is why the survey lane never saw this.

// ── REPRODUCED: the argument grows through a sysroot container on each level ────────
pub enum Nested<T> {
    Leaf(T),
    Nest(Box<Nested<Vec<T>>>),
}

pub fn push_nested<'a>(v: &mut Vec<&'a Nested<u8>>, n: &'a Nested<u8>) {
    v.push(n);
}

// ── Same walk, argument DOUBLING through a tuple (also `nominal_frontier`'s shape) ───
pub struct Perfect<T> {
    pub v: T,
    pub next: Option<Box<Perfect<(T, T)>>>,
}

pub fn push_perfect<'a>(v: &mut Vec<&'a Perfect<u8>>, p: &'a Perfect<u8>) {
    v.push(p);
}

// ── Control: a REGULAR recursive type. The memo's coinductive entry answers its
// re-entry, the new cut is never reached, and the verdict is what it always was. ──────
pub enum Flat<T> {
    Leaf(T),
    Nest(Box<Flat<T>>),
}

pub fn push_flat<'a>(v: &mut Vec<&'a Flat<u8>>, f: &'a Flat<u8>) {
    v.push(f);
}
