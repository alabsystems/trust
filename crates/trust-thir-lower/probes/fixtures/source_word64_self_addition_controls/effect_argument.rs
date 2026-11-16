fn effect() {}
fn double(x: u64) -> u64 { x.wrapping_add({ effect(); x }) }
