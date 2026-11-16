// SLICE-ZERO-SIZE-NAME-1 real-MIR fixture: user methods that are RENAMED off the names
// of core's panicking slice methods. None of them panics for any argument.
pub struct Grid { pub w: usize }
impl Grid {
    pub fn wndws(&self, n: usize) -> usize { self.w ^ n }
    pub fn chnks(&self, n: usize) -> usize { self.w.wrapping_add(n) }
    pub fn rchnks_exact(&self, n: usize) -> usize { n }
}
pub trait Tiles { fn chnks_exact(&self, n: usize) -> usize; }
pub struct G2;
impl Tiles for G2 { fn chnks_exact(&self, n: usize) -> usize { n } }
pub struct W<S: ?Sized>(pub u8, pub core::marker::PhantomData<S>);
impl<S: ?Sized> W<S> { pub fn wndws(&self, n: usize) -> usize { n } }
pub trait Tr {
    fn swp(&self, i: usize, j: usize) -> usize;
    fn splt_at(&self, m: usize) -> usize;
    fn wndws(&self, n: usize) -> usize;
}
impl Tr for [u8] {
    fn swp(&self, i: usize, j: usize) -> usize { i ^ j }
    fn splt_at(&self, m: usize) -> usize { m }
    fn wndws(&self, n: usize) -> usize { n }
}
pub fn r1(g: &Grid, k: usize) -> usize { g.wndws(k) }
pub fn r2(g: &Grid) -> usize { g.chnks(0) }
pub fn r3(g: &Grid) -> usize { g.rchnks_exact(0) }
pub fn r4(g: &G2, k: usize) -> usize { g.chnks_exact(k) }
pub fn r5<T>(w: &W<[T]>, k: usize) -> usize { w.wndws(k) }
pub fn r6(s: &[u8], i: usize, j: usize) -> usize { s.swp(i, j) }
pub fn r7(s: &[u8], m: usize) -> usize { Tr::splt_at(s, m) }
pub fn r8(s: &[u8], n: usize) -> usize { Tr::wndws(s, n) }
