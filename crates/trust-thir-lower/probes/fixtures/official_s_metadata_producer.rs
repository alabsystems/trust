#[inline(never)] pub fn identity<T>(x: T) -> T { x }
#[inline(never)] pub fn relay<T>(x: T) -> T { identity(x) }
#[inline(never)] pub fn slots<'a: 'a, T: Copy, const N: u64>(x: T) -> T { identity(x) }
#[inline(never)] pub fn scalar_const<const N: u64>() -> u64 { N }
#[inline(never)] pub fn const_relay<const N: u64>() -> u64 { scalar_const::<N>() }
#[inline] pub fn mix(x: u64) -> u64 { x ^ 7 }
#[inline] pub fn twice(x: u64) -> u64 { mix(mix(x)) }
#[track_caller] pub fn tracked<T>(x: T) -> T { x }
pub fn overflow<T>(x: u64) -> u64 { x + 1 }
pub fn apply_once<F: FnOnce(u64) -> u64>(f: F, x: u64) -> u64 { f(x) }
pub fn apply_ref<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64 { f(x) }
pub fn apply_mut<F: FnMut(u64) -> u64>(f: &mut F, x: u64) -> u64 { f(x) }
