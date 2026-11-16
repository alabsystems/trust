//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! CONSTRUCTING an aggregate that holds an array whose length is a NAMED const (`[u8; BUF]`,
//! the ring-buffer idiom) LOWERS under `strict` — where any producer refusal is a compile error
//! — and costs the program's text, not BUF.
//!
//! The THIR producer builds a tuple/struct as a seed constant plus one `InsertField` per field.
//! The seed of an array lane is ONE trust-ir v50 `Constant::Splat` (`seed_nonempty_array`), and
//! so is the differential's dead-seed zero for the MIR oracle's aggregate `Undef`
//! (`zero_const_depth`): one element whatever BUF is.
//!
//! History. Both used to be one constant PER ELEMENT, so until 2026-09-28 an alias-length array
//! above `MAX_MATERIALIZED_ARRAY_LEN` (65536) was DECLINED where `map_ty` evaluates its length —
//! here the struct field types, which register with their `BUF` unevaluated — and `reset` and
//! `wrap` were refused whole. On 2026-09-23 that gate was removed for a day: `reset` (at
//! `1 << 24`) took 3.7 GB and wrote a 285 MB IR artifact, `wrap` at `1 << 26` grew into a 4 GiB
//! ceiling and was killed, and tests/ui/consts/promoted_size_overflow.rs ICEd (`capacity
//! overflow` inside `zero_const_depth`) instead of reporting its E0080. The splat made the gate
//! unnecessary, and it is deleted.
//!
//! BUF is 2^17: just past the deleted gate, so re-adding it (or any length refusal on this
//! path) turns this file red under `strict`, while a regression back to one constant per element
//! costs 2^17 constants — a few MB — rather than the machine-sized compile a huge BUF would be in
//! a suite that runs without a memory ceiling. MEASURED 2026-09-28 on the commit-2 stage1 under
//! `taskpolicy -m 4096`, `-Ztrust-ir-lower=strict -Ztrust-verify=on`: rc 0, 182 MB, 1.3 s. Flatness
//! at a huge BUF is measured by hand under a ceiling, never in the suite (see
//! trust_ir_huge_array_construction_value_proportional.rs, which stays `ignore-test`):
//! `taskpolicy -m 4096 <stage1 Mach-O rustc> -Ztrust-verify=on --crate-type=lib <file>`.

#![allow(dead_code)]

const BUF: usize = 1 << 17;

pub struct Ring {
    buf: [u8; BUF],
    head: usize,
}

// A struct-literal construction whose seed covers the array lane.
pub fn reset(r: &mut Ring) {
    *r = Ring { buf: r.buf, head: 0 };
}

pub struct S {
    pub a: [u8; BUF],
    pub b: u8,
}

pub fn wrap(a: [u8; BUF]) -> S {
    S { a, b: 1 }
}
