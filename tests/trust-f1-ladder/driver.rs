extern crate rung;
fn main() { let x: u64 = std::env::args().nth(1).unwrap().parse().unwrap(); let r = rung::rung(x); println!("{}", r); }
