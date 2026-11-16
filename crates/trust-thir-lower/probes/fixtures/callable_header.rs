#![allow(dead_code)]
struct Packet { hi: u64, lo: u16 }
fn identity<T>(value: T) -> T { value }
fn relay<T>(prefix: [u8; 2], value: T) -> T { let _ = prefix; identity(value) }
fn main() {
    let _ = identity::<u64>(19);
    let _ = identity::<[u8; 3]>([1, 2, 3]);
    let _ = identity::<[u8; 0]>([]);
    let _ = identity::<Packet>(Packet { hi: 5, lo: 2 });
    let _ = relay::<[u64; 3]>([1, 2], [3, 4, 5]);
    let value = 23u64;
    let _ = identity::<&u64>(&value);
    let _ = identity::<()>(());
}
