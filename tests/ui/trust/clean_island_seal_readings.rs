//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_readings_holds.rs` (`Trust.Protocol.Seal`): a
//! chain of 48 generic fns whose last swaps the two `(T, App)` it is handed down
//! the chain. The seal must FAIL at that swap: a reading shared by the fns of
//! one environment still finds what each body does.

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell, k: u8 }
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }
fn f1<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f2(v, a, b) }
fn f2<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f3(v, a, b) }
fn f3<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f4(v, a, b) }
fn f4<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f5(v, a, b) }
fn f5<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f6(v, a, b) }
fn f6<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f7(v, a, b) }
fn f7<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f8(v, a, b) }
fn f8<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f9(v, a, b) }
fn f9<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f10(v, a, b) }
fn f10<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f11(v, a, b) }
fn f11<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f12(v, a, b) }
fn f12<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f13(v, a, b) }
fn f13<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f14(v, a, b) }
fn f14<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f15(v, a, b) }
fn f15<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f16(v, a, b) }
fn f16<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f17(v, a, b) }
fn f17<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f18(v, a, b) }
fn f18<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f19(v, a, b) }
fn f19<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f20(v, a, b) }
fn f20<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f21(v, a, b) }
fn f21<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f22(v, a, b) }
fn f22<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f23(v, a, b) }
fn f23<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f24(v, a, b) }
fn f24<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f25(v, a, b) }
fn f25<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f26(v, a, b) }
fn f26<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f27(v, a, b) }
fn f27<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f28(v, a, b) }
fn f28<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f29(v, a, b) }
fn f29<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f30(v, a, b) }
fn f30<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f31(v, a, b) }
fn f31<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f32(v, a, b) }
fn f32<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f33(v, a, b) }
fn f33<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f34(v, a, b) }
fn f34<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f35(v, a, b) }
fn f35<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f36(v, a, b) }
fn f36<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f37(v, a, b) }
fn f37<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f38(v, a, b) }
fn f38<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f39(v, a, b) }
fn f39<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f40(v, a, b) }
fn f40<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f41(v, a, b) }
fn f41<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f42(v, a, b) }
fn f42<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f43(v, a, b) }
fn f43<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f44(v, a, b) }
fn f44<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f45(v, a, b) }
fn f45<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f46(v, a, b) }
fn f46<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); f47(v, a, b) }
fn f47<T: Clone + Ord>(v: Vec<T>, a: &mut (T, App), b: &mut (T, App)) -> Vec<T> { let mut v: Vec<T> = v.iter().map(|x| x.clone()).collect(); v.sort(); f48(v, a, b) }
fn f48<U: Clone + Ord>(v: Vec<U>, a: &mut (U, App), b: &mut (U, App)) -> Vec<U> { let mut v: Vec<U> = v.iter().map(|x| x.clone()).collect(); v.sort(); core::mem::swap(a, b); v } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(U, App)`, which holds a `Cell`, in `f48`:
fn main() { let mut a = (1u8, App::new()); let mut b = (2u8, App::new()); a.1.cell.bump(); f1(vec![1u8], &mut a, &mut b); }

clean {
    import Trust.Binding
    namespace Readings
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Readings
}
//~^^^^ ERROR seal `Readings.cell` on `Cell` does not hold
