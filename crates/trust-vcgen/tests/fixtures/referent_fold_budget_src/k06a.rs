// ALIASED-GUARD variant of stall/kNN.rs, K=6: every index temporary is also
// shared-borrowed (the way `println!("{}", i)` borrows a local), so no store
// through another element borrow can be dismissed without attributing it: the
// referent fold's pruning does not apply and every walk needs every other pointer.
pub fn chain(a0: &mut [u32; 8], a1: &mut [u32; 8], a2: &mut [u32; 8], a3: &mut [u32; 8], a4: &mut [u32; 8], a5: &mut [u32; 8], n: usize) -> u32 {
    let i0 = (n >> 0) & 7;
    let i1 = (n >> 1) & 7;
    let i2 = (n >> 2) & 7;
    let i3 = (n >> 3) & 7;
    let i4 = (n >> 4) & 7;
    let i5 = (n >> 5) & 7;
    let k0 = &i0;
    let k1 = &i1;
    let k2 = &i2;
    let k3 = &i3;
    let k4 = &i4;
    let k5 = &i5;
    let p0 = &mut a0[i0];
    let p1 = &mut a1[i1];
    let p2 = &mut a2[i2];
    let p3 = &mut a3[i3];
    let p4 = &mut a4[i4];
    let p5 = &mut a5[i5];
    *p0 = 1;
    *p1 = 2;
    *p2 = 3;
    *p3 = 4;
    *p4 = 5;
    *p5 = 6;
    let mut s = 0u32;
    s ^= *p0;
    s ^= *p1;
    s ^= *p2;
    s ^= *p3;
    s ^= *p4;
    s ^= *p5;
    s ^= *k0 as u32;
    s ^= *k1 as u32;
    s ^= *k2 as u32;
    s ^= *k3 as u32;
    s ^= *k4 as u32;
    s ^= *k5 as u32;
    s
}
