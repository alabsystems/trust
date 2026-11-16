// STALL class repro, K=6 element borrows with local index guards.
// main d36c551fa: referent_fold::is_stable re-walks every store-through-pointer's
// referent with no memo when nested (K! growth); seal 020d4ef7ef has no stability walk.
pub fn chain(a0: &mut [u32; 8], a1: &mut [u32; 8], a2: &mut [u32; 8], a3: &mut [u32; 8], a4: &mut [u32; 8], a5: &mut [u32; 8], n: usize) -> u32 {
    let i0 = (n >> 0) & 7;
    let i1 = (n >> 1) & 7;
    let i2 = (n >> 2) & 7;
    let i3 = (n >> 3) & 7;
    let i4 = (n >> 4) & 7;
    let i5 = (n >> 5) & 7;
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
    s = s.wrapping_add(*p0);
    s = s.wrapping_add(*p1);
    s = s.wrapping_add(*p2);
    s = s.wrapping_add(*p3);
    s = s.wrapping_add(*p4);
    s = s.wrapping_add(*p5);
    s
}
