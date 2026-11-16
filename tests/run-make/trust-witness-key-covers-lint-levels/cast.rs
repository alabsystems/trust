pub struct P { pub a: u8, pub b: u8 }
fn mk(a: u8, b: u8) -> P { P { a, b } }
fn pa(p: &P) -> u8 { p.a }
fn pb(p: &P) -> u8 { p.b }
pub fn big(x: u8, y: u8) -> P {
    let p1 = mk(x as u8, y);
    let p2 = mk(pa(&p1), pb(&p1));
    let p3 = mk(pb(&p2), pa(&p2));
    let p4 = mk(pa(&p3), pb(&p3));
    let p5 = mk(pb(&p4), pa(&p4));
    let p6 = mk(pa(&p5), pb(&p5));
    let p7 = mk(pb(&p6), pa(&p6));
    let p8 = mk(pa(&p7), pb(&p7));
    mk(pb(&p8), pa(&p8))
}
