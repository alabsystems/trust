pub fn later(v: &mut [u8]) {
    if v.len() > 1 {
        v.swap(0, 1)
    }
}

pub fn mix(x: u64, y: u64) -> u64 {
    let a = x ^ y;
    let b = (a << 7) | (a >> 57);
    let c = b ^ (x >> 3);
    let d = c ^ (y << 11);
    let e = (d << 13) | (d >> 51);
    let f = e ^ (a >> 5);
    let g = f ^ (b << 2);
    let h = (g << 17) | (g >> 47);
    h ^ c ^ d ^ e ^ f
}

#[macro_export]
macro_rules! twice {
    ($e:expr) => {
        $crate::mix($e, $e)
    };
}

#[inline]
pub fn same<T: Copy + PartialEq + core::fmt::Debug>(a: T, b: T) -> T {
    assert_eq!(a, b);
    a
}
