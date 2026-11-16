// foldconfirm: independent re-creation of the hunter's Finding 1 (order_safe_ctl) and
// its raw-pointer variants (order_raw_ctl, order2_ctl, order3_ctl), plus bug twins.
pub struct S {
    pub f: u8,
    pub g: u8,
}

pub fn order_safe_ctl(m: &mut S, n: usize, t: &[u8; 4]) -> u8 {
    std::hint::black_box(&m);
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let y = &mut m.f;
    let z = &mut l[k];
    *z = 2;
    *y = 3;
    *z = 2;
    t[l[k]] ^ (*rk as u8)
}

pub fn order_safe_bug(m: &mut S, n: usize, t: &[u8; 4]) -> u8 {
    std::hint::black_box(&m);
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let y = &mut m.f;
    let z = &mut l[k];
    *z = 2;
    *y = 3;
    *z = 6;
    t[l[k]] ^ (*rk as u8)
}

pub fn order_raw_ctl(m: &mut S, n: usize, t: &[u8; 4]) -> u8 {
    std::hint::black_box(&m);
    let k = n & 3;
    let rk = &k;
    let mut l = [0usize; 4];
    let y: *mut u8 = &mut m.f as *mut u8;
    let z: *mut usize = &mut l[k] as *mut usize;
    unsafe {
        *z = 2;
        *y = 3;
        *z = 2;
    }
    t[l[k]] ^ (*rk as u8)
}

pub fn order2_ctl(m: &mut S, n: usize, t: &[u8; 4]) -> u8 {
    let k: usize = n & 3;
    let k2: usize = (n >> 2) & 3;
    let refs: [&usize; 2] = [&k, &k2];
    let kk = *refs[(n >> 4) & 1];
    let mut l = [0usize; 4];
    let sm: *const usize = (&raw const m) as *const usize;
    l[0] = unsafe { *sm };
    let y: *mut u8 = &mut m.f as *mut u8;
    let z: *mut usize = &mut l[k] as *mut usize;
    unsafe {
        *z = 2;
        *y = 3;
        *z = 2;
    }
    t[l[k]] ^ (kk as u8)
}

pub fn order3_ctl(m: &mut S, n: usize, t: &[u8; 4]) -> u8 {
    let k: usize = n & 3;
    let k2: usize = (n >> 2) & 3;
    let refs: [&usize; 2] = [&k, &k2];
    let kk = *refs[(n >> 4) & 1];
    let mut l = [0usize; 4];
    let sm: *const usize = (&raw const m) as *const usize;
    l[0] = unsafe { *sm };
    let z: *mut usize = &mut l[k] as *mut usize;
    let y: *mut u8 = &mut m.f as *mut u8;
    unsafe {
        *z = 2;
        *y = 3;
        *z = 2;
    }
    t[l[k]] ^ (kk as u8)
}
