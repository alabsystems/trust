//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
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
fn dup<'a>(h: &Holder<'a>) -> Holder<'a> {
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
