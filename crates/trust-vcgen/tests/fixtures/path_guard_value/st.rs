pub fn st_switch_scalar_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { len = n; }
        acc ^= buf[len];
    }
    acc
}
pub fn st1_switch_range_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> usize {
    let mut len = m;
    let mut acc = 0;
    for &c in xs {
        match len { 0 | 1 | 2 | 3 => {} _ => return acc }
        if c { len = n; }
        acc ^= buf[..len].len();
    }
    acc
}
