// SLICE-ZERO-SIZE-NAME-1 real-MIR fixture: core's own panicking slice methods keep
// their rows (c1..c4 unguarded, g1/g2 guarded).
pub fn c1(s: &[u8], k: usize) -> usize { s.windows(k).count() }
pub fn c2(s: &[u8]) -> usize { s.chunks(0).count() }
pub fn c3(s: &[u8], m: usize) -> usize { s.split_at(m).0.len() }
pub fn c4(s: &mut [u8], i: usize, j: usize) { s.swap(i, j) }
pub fn g1(s: &[u8], k: usize) -> usize { if k != 0 { s.chunks(k).count() } else { 0 } }
pub fn g2(s: &mut [u8], i: usize, j: usize) { if i < s.len() && j < s.len() { s.swap(i, j) } }
