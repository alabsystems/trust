//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

// Trust (vtable slice 10 — the const-param/assoc-const SAMPLE COLUMN): chain item (5) of
// the vtable campaign. A SYMBOLIC body's parametric reads have no value at `mir_built` on
// either side: the THIR producer spells them `GlobalAddr`+`Load` of ONE value-less
// `__trust_constparam_*`/`__trust_symconst_*` carrier (wave-CP / totality Batch C), the MIR
// oracle's bridge spells each occurrence a fresh live integer-sorted `Inst::Undef`
// (`ConstValue::ConstParam` / `OpaqueScalar` arms) — so the whole family was held at the
// LIVE-havoc gate. The differential now treats the parameter as an interpretation INPUT:
// when the single-parameter pairing audit holds (exactly one distinct carrier; producer
// Load count == oracle live-Undef count; shape equality per occurrence), both sides receive
// the same `sample_values(carrier.ty)` sample per execution, substituted into per-sample
// CLONES only — the producer module, `Lowered::symbolic`, the splice, and the verifier
// lanes are untouched, and the carrier globals are never loaded (the slice-4 zero-fill trap
// cannot apply).
//
// Every lane below is one body shape of the pre-registered population measured on
// postbuild-vtable10 (62 rows, Agreed 2578 -> 2640). Each must keep COMPILING — a lowering
// decline is a coverage decision, never an error — and each pins one arm of the column.

// CONST-PARAM ARITHMETIC (division::with_bound::{constant#N}): the demanded-type respell —
// the oracle Undef is declared `u64` (width-collapsed constant lane) but consumed by a
// faithful-dest `BinOp { ty: usize }`; the substitution realizes the sample at the
// CONSUMER-demanded spelling on the oracle side and at the carrier's faithful spelling on
// the producer side (same 64-bit value semantics, the per-side-realization precedent).
pub fn with_bound<const N: usize>()
where
    [u8; N / 2]: Sized,
{
    let _: [u8; N / 2] = [0; N / 2];
}

// CONST-PARAM COMPARISON (less_than::test::{constant#N}): ICmp consumers stamped from the
// constant's own contextless type — declared and demanded agree at u64.
pub struct Foo<const B: bool>;
pub fn test<const N: usize>() -> Foo<{ N > 10 }>
where
    Foo<{ N > 10 }>: Sized,
{
    Foo
}

// CONST-PARAM CAST (abstract-const-as-cast-4): `Cast` demands its `src_ty`.
pub struct EvaluatableU128<const N: u128>;
pub fn use_cast<const N: usize>()
where
    EvaluatableU128<{ N as u128 }>: Sized,
{
}

// RETURN-ONLY CONST PARAMS at other widths (invalid-const-value-soundness::*_consumer,
// const_fn_in_generics::identity): the Return slot demands the signature type; bool
// realizes `Constant::Bool` and samples both truth values (2), i32 samples 7 boundaries.
pub fn bool_consumer<const B: bool>() -> bool {
    B
}
pub fn u8_consumer<const N: u8>() -> u8 {
    N
}
pub fn i32_consumer<const N: i32>() -> i32 {
    N
}

// GENERIC ASSOC CONST (dropck/single-satisfied/issue-89146 shape): the `__trust_symconst_`
// lane — `OpaqueScalar` carries NO identity on the oracle side, so ONLY the
// single-parameter uniqueness argument can bind it; a second distinct carrier refuses.
pub trait HasSize {
    const SIZE: usize;
}
pub fn assoc_read<G: HasSize>()
where
    [(); G::SIZE]: Sized,
{
}

// DEAD PARAMETRIC READ (issue-55219::stuff): zero consumers — the substitution keeps the
// Undef's declared type and the pair agrees on the unit return for every sample.
pub struct Wrapper<T>(T);
impl<T> Wrapper<T> {
    const HASH_LEN: usize = 20;
    pub fn stuff() {
        let _ = Self::HASH_LEN;
    }
}

// SCOPE PIN — a char const param stays a fail-closed decline on the oracle side (the
// extractor has no char ConstParam spelling; the body keeps its coverage-only skip, and the
// column's shape key refuses Char in any case).
pub fn char_consumer<const C: char>() -> char {
    C
}

fn main() {}
