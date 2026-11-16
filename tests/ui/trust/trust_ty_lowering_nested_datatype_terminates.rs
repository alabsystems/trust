//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr

// `-Ztrust-verify=on` is LOAD-BEARING, as in `trust_vtable_key_reentrancy_cycle.rs`:
// compiletest appends `-Ztrust-verify=off` to every test compilation unless the test
// asks, and the defect lives in the extractor, which only runs when verification does.

// Trust: a NESTED datatype — a generic type whose recursive occurrence changes its own
// argument — used to make `trustc` run forever inside the verifier's type lowering.
//
// REPRODUCED 2026-09-26 on stage2 `29b6f15c7`: `Perfect` below plus one function naming
// it did not finish in 240 s with verification on, and compiles in 2.1 s with it off.
// Every sampled frame of the working thread was `ty_convert::nominal_frontier`, under
// `canonical_cut_set`.
//
// THE MECHANISM. `canonical_cut_set` discovers the nominal types reachable from a
// local's type. `Perfect<u32>` reaches `Perfect<(u32, u32)>`, which reaches
// `Perfect<((u32, u32), (u32, u32))>`, and so on — an infinite node set, which that
// discovery already bounds (`MAX_CANONICAL_CUT_NODES`). What it did not bound was the
// cost of ONE node: the frontier of the field `v: T_k` was computed by walking the type
// as a TREE, and `T_k` is a tuple DAG with k distinct nodes and 2^k leaves. The only
// limit was the 64-level depth bound, i.e. 2^64 visits. The type is not pathological —
// this is the textbook perfect-tree encoding — and nothing about it is unsound or
// unusual for rustc, which never expands it.
//
// WHAT THIS TEST ASSERTS: that `trustc` TERMINATES on these shapes. Which obligations
// end up proved is a coverage question recorded elsewhere; a hang is not a verdict.
// The walk itself, its exactness against the pre-fix walk and its step bound are unit
// tested in `crates/trust-mir-extract/src/ty_frontier.rs`.

// ── REPRODUCED: the argument DOUBLES through a tuple on each level ───────────────────
pub struct Perfect<T> {
    pub v: T,
    pub next: Option<Box<Perfect<(T, T)>>>,
}

// Naming the type in the SIGNATURE is what makes the extractor lower it (the argument
// local's type); the body is trivial so no unrelated obligation decides the verdict.
pub fn perfect_tag(_p: &Perfect<u32>) -> u32 {
    7
}

// ── Same doubling behind references: `Ref` is peeled by the same walk ────────────────
pub struct PerfectRef<'a, T> {
    pub v: &'a T,
    pub next: Option<&'a PerfectRef<'a, (&'a T, &'a T)>>,
}

pub fn perfect_ref_tag(_p: &PerfectRef<'_, u8>) -> u32 {
    8
}

// ── Control: a nested datatype whose argument grows LINEARLY (`Vec<T>`) ──────────────
// Terminated before the fix too — its frontier per node is one path, not a tree — and
// is kept to show the fix is about repeated children, not about nested datatypes.
pub enum Nested<T> {
    Leaf(T),
    Nest(Box<Nested<Vec<T>>>),
}

pub fn nested_tag(n: &Nested<u8>) -> u32 {
    match n {
        Nested::Leaf(_) => 0,
        Nested::Nest(_) => 1,
    }
}

fn main() {}
