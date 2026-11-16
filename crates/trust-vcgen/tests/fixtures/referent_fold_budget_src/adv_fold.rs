// Class-1 soundness probe: the false proof referent_fold (0bbb2e326c) closes.
// `*r = 3` stores into the OLD `p`; after `p = o`, `p.a == o.a` is arbitrary.
pub struct S {
    pub a: u8,
    pub b: u8,
}
pub fn sf_field_reseat_bug<'a>(mut p: &'a mut S, o: &'a mut S, t: &[u8; 4]) -> u8 {
    let r = &mut p.a;
    p = o;
    *r = 3;
    t[p.a as usize]
}
pub fn sf_field_ctl(p: &mut S, t: &[u8; 4]) -> u8 {
    let r = &mut p.a;
    *r = 3;
    t[p.a as usize]
}
