#![feature(rustc_attrs)]
#![allow(internal_features)]

#[inline(never)]
#[rustc_clean(cfg = "warm", loaded_from_disk = "items_of_instance")]
fn plus_one(value: u64) -> u64 {
    value.wrapping_add(1)
}
#[inline(never)]
fn twice(value: u64) -> u64 {
    value.wrapping_mul(2)
}
static FUNCTIONS: [fn(u64) -> u64; 2] = [plus_one, twice];
trait Value {
    fn value(&self) -> u64;
}
impl Value for u64 {
    #[inline(never)]
    fn value(&self) -> u64 {
        *self
    }
}
static OBJECT: &(dyn Value + Sync) = &13_u64;
static BYTES: [u8; 8] = [13, 17, 19, 23, 29, 31, 37, 41];
unsafe extern "C" {
    fn abs(value: i32) -> i32;
}
// Trust: a MIR unsizing request and a CTFE static vtable materialization
// are distinct collector paths. Exercise both instead of assuming that
// reading OBJECT creates a fresh symbolic vtable request in main.
#[inline(never)]
fn direct_object(value: &u64) -> u64 {
    let object: &(dyn Value + Sync) = value;
    std::hint::black_box(object).value()
}
fn main() {
    let table = std::hint::black_box(&FUNCTIONS);
    let first = table[0](10);
    let second = table[1](10);
    let object = std::hint::black_box(OBJECT).value();
    assert_eq!(direct_object(&std::hint::black_box(17_u64)), 17);
    let sum: u64 = std::hint::black_box(&BYTES).iter().map(|&v| v as u64).sum();
    let foreign = unsafe { abs(std::hint::black_box(-37)) };
    assert_eq!((first, second, object, sum, foreign), (11, 20, 13, 210, 37));
    println!("cache={first},{second},{object},{sum},{foreign}");
}
