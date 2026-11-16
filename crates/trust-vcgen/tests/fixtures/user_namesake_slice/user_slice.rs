// SLICE-ZERO-SIZE-NAME-1 real-MIR fixture: user methods that merely share the NAME
// of core's panicking slice methods. None of them panics for any argument.
pub struct Grid { pub w: usize }
impl Grid {
    pub fn windows(&self, n: usize) -> usize { self.w ^ n }
    pub fn chunks(&self, n: usize) -> usize { self.w.wrapping_add(n) }
    pub fn rchunks_exact(&self, n: usize) -> usize { n }
}
pub trait Tiles { fn chunks_exact(&self, n: usize) -> usize; }
pub struct G2;
impl Tiles for G2 { fn chunks_exact(&self, n: usize) -> usize { n } }
pub struct W<S: ?Sized>(pub u8, pub core::marker::PhantomData<S>);
impl<S: ?Sized> W<S> { pub fn windows(&self, n: usize) -> usize { n } }
pub trait Tr {
    fn swap(&self, i: usize, j: usize) -> usize;
    fn split_at(&self, m: usize) -> usize;
    fn windows(&self, n: usize) -> usize;
}
impl Tr for [u8] {
    fn swap(&self, i: usize, j: usize) -> usize { i ^ j }
    fn split_at(&self, m: usize) -> usize { m }
    fn windows(&self, n: usize) -> usize { n }
}
pub fn p1(g: &Grid, k: usize) -> usize { g.windows(k) }
pub fn p2(g: &Grid) -> usize { g.chunks(0) }
pub fn p3(g: &Grid) -> usize { g.rchunks_exact(0) }
pub fn p4(g: &G2, k: usize) -> usize { g.chunks_exact(k) }
pub fn p5<T>(w: &W<[T]>, k: usize) -> usize { w.windows(k) }
pub fn p6(s: &[u8], i: usize, j: usize) -> usize { s.swap(i, j) }
pub fn p7(s: &[u8], m: usize) -> usize { Tr::split_at(s, m) }
pub fn p8(s: &[u8], n: usize) -> usize { Tr::windows(s, n) }
