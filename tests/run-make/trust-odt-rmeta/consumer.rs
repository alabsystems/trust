// Trust: consume the actual metadata in an ordinary build with verification off.
extern crate odt_aux;
pub fn field(p: odt_aux::Pair) -> u32 { p.0 }
pub fn choose(e: odt_aux::Decision) -> u8 {
    match e { odt_aux::Decision::Zebra => 0, odt_aux::Decision::Alpha => 1 }
}
