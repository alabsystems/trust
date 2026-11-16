//@ dont-check-compiler-stderr
//@ check-fail
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ forbid-output: UnsignableRustAbiDeclaration
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! RE-PINNED 2026-10-15 (thir-generic-instance-callee; measured on the stage 1 of this change).
//! Until this change the DERIVED body below was refused at crate assembly: it mints a call edge
//! to `std::clone::impls::<impl std::clone::Clone for &T>::clone`, whose parameter is a
//! REFERENCE TO A POINTER (`&&T`), and the producer declined to sign that parameter (the
//! dropped-borrow guard in `recover_callee_param_tys`), so every body minting it was refused
//! with `UnsignableRustAbiDeclaration`. The guard stood in for a call-site defect (a
//! value-for-pointer carrier passing `P` where `&P` was due), which is now closed at the call
//! site (`ref_arg_pointee_may_be_pointer`); the parameter is signed `ptr` and the derived body
//! lowers and splices. The `forbid-output` keeps that class closed.
//!
//! The ONE error left is a different, pre-existing producer limit that the newly spliced derive
//! exposes: `dup`'s `h.clone()` mints an edge to `<Holder<'a> as Clone>::clone` as a bodyless
//! INSTANCE declaration (its generic arguments are the erased lifetime), and that symbol is now
//! also held by the derived DEFINITION, so crate assembly refuses `dup` with
//! `LinkSymbolCollision` rather than pick a spelling. While the derive was refused there was no
//! definition to collide with. Closing it is instance-keyed crate assembly (the pointer-args
//! plan's A5), not this change; when it closes, the annotation below goes and this file is
//! `check-pass`. compiletest fails on any unannotated error, so every OTHER body here, the
//! derive included, is still pinned to lower.
//!
//! History (2026-09-19): strict could not SEE the per-body refusal until `FinalizeSummary`
//! grew its `refused_bodies` channel; before that this file compiled at exit 0 over a refused
//! body. See `reports/2026-09-14-rust-abi-vararg-producer-half.md`.
//!
//! Trust (wave-CR): a call whose result is a THIN REFERENCE returns a pointer
//! that is valid for its lifetime by Rust's type system, so it joins the
//! ledgers a ref param gets: its deref is a `Load`, a `&mut` result takes a
//! `Store`, and it may be returned onward. Every body here carried
//! `Deref(non-borrow ptr)` (or `Assign(*r= non-mut-borrow ptr)`) before the
//! wave; `strict` turns that into a compile error, so this file is the
//! mutation check.
struct Cell {
    v: i32,
}
impl Cell {
    fn get(&self) -> &i32 {
        &self.v
    }
}
fn pick<'a>(a: &'a u64, b: &'a u64, first: bool) -> &'a u64 {
    if first { a } else { b }
}
fn read(c: &Cell) -> i32 {
    *c.get()
}
fn slot(x: &mut i32) -> &mut i32 {
    x
}
fn write(v: i32) -> i32 {
    let mut a = v;
    *slot(&mut a) = 7;
    *slot(&mut a) += 1;
    a
}
fn choose(x: u64, y: u64) -> u64 {
    *pick(&x, &y, x > y)
}
fn forward(c: &Cell) -> &i32 {
    c.get()
}
#[derive(Clone)]
enum Holder<'a> {
    Some(&'a i32),
    None,
}
// Re-pinned 2026-10-15 (the merge of 2026-10-14 brought WS5.2, 87388a9d3ec): `dup` is refused
// too, as a fail-closed cascade of the derive refusal above. `Function.name` is now the
// link-time symbol, the refused derived `clone` still holds its row (lowered for coverage,
// never spliced), and `h.clone()` mints a bodyless declaration of the same symbol, so WS5.2
// refuses the minting body rather than pick one of the two rows (`LinkSymbolCollision`).
fn dup<'a>(h: &Holder<'a>) -> Holder<'a> {
    //~^ ERROR LinkSymbolCollision(
    h.clone()
}
fn main() {
    let mut c = Cell { v: 1 };
    let h = Holder::Some(&c.v);
    let h2 = dup(&h);
    let held = match h2 {
        Holder::Some(_) => 8,
        Holder::None => -1,
    };
    let ok = held == 8 && read(&c) == 1 && write(1) == 8 && choose(3, 9) == 9 && *forward(&c) == 8;
    std::process::exit(!ok as i32);
}
