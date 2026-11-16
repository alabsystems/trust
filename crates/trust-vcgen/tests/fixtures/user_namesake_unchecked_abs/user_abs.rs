// User functions merely NAMED `abs` under a path that mentions `core::num::` /
// `std::num::`; none of them can panic.
pub struct G<T>(pub T);
impl<T> G<T> {
    #[inline(never)]
    pub fn abs(x: i32) -> i32 { x ^ 1 }
}
pub mod mycore { pub mod num { #[inline(never)] pub fn abs(x: i32) -> i32 { x ^ 1 } } }
pub mod mystd { pub mod num { #[inline(never)] pub fn abs(x: i32) -> i32 { x ^ 1 } } }
pub fn a4(x: i32) -> i32 { G::<core::num::Wrapping<i32>>::abs(x) }
pub fn c1(x: i32) -> i32 { mycore::num::abs(x) }
pub fn s1(x: i32) -> i32 { mystd::num::abs(x) }
// Controls: core's own signed `abs`.
pub fn e1(x: i32) -> i32 { x.abs() }
pub fn e2(x: i32) -> i32 { if x != i32::MIN { x.abs() } else { 0 } }
