pub fn tuple_swap_bug(buf: &[u8; 8], c: bool, y0: usize) -> u8 {
    let mut t = (0usize, y0);
    if c {
        t = (t.1, t.0);
    } else {
        t = (0, 0);
    }
    assert!(t.1 < 8);
    assert!(c);
    buf[t.0]
}

pub fn self_update_ctl(buf: &[u8; 8], c: bool, k: usize) -> u8 {
    let mut acc = 0u8;
    let i = k & 7;
    if c {
        acc ^= 2;
    } else {
        acc ^= 1;
    }
    acc ^ buf[i]
}

pub fn merge_const_ctl(buf: &[u8; 8], c: bool) -> u8 {
    let x;
    if c {
        x = 3usize;
    } else {
        x = 5usize;
    }
    buf[x]
}
