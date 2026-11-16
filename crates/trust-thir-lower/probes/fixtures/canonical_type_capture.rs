#![allow(dead_code)]
pub fn identity<T, const N: usize>(value: [T; N]) -> [T; N] { value }
pub fn bytes<const N: usize>(value: [u8; N]) -> [u8; N] { value }
pub fn with_lifetime<'a, T: 'a, const N: usize>(_: &'a u8, value: [T; N]) -> [T; N] { value }
pub fn relay<T, const N: usize>(value: [T; N]) -> [T; N] { identity(value) }
pub fn relay_twice<T, const N: usize>(value: [T; N]) -> [T; N] { identity(identity(value)) }
pub fn inspect<T: Copy, const N: usize>(value: [T; N]) -> T { value[0] }
pub struct Nominal<T>(pub T);
pub fn nominal<T>(value: Nominal<T>) -> Nominal<T> { value }
pub enum Choice<T> { Value(T), Empty }
pub fn nominal_enum<T>(value: Choice<T>) -> Choice<T> { value }
pub struct NominalArray<T, const N: usize>(pub [T; N]);
pub fn nominal_array<T, const N: usize>(value: NominalArray<T, N>) -> NominalArray<T, N> { value }
pub struct OtherNominal<T>(pub T);
pub fn two_nominals<T: Copy>(left: Nominal<T>, _: OtherNominal<T>) -> Nominal<T> { left }
pub fn nominal_field<T: Copy>(value: Nominal<T>) -> T { value.0 }
pub fn nominal_construct<T>(value: T) -> Nominal<T> { Nominal(value) }
pub union NominalUnion<T: Copy> { pub value: T, pub word: u64 }
pub fn nominal_union<T: Copy>(value: NominalUnion<T>) -> NominalUnion<T> { value }
pub fn ground_nominal<T>(value: Nominal<u8>) -> Nominal<u8> { value }
pub fn tuple_identity<T>(value: (T, u8)) -> (T, u8) { value }
pub fn tuple_nested<T, const N: usize>(value: (T, [u8; N])) -> (T, [u8; N]) { value }
pub fn tuple_forward<T>(value: (T, u8)) -> (T, u8) { tuple_identity(value) }
pub fn tuple_two_types<T: Copy>(left: (T, u8), _: (u8, T)) -> (T, u8) { left }
pub fn tuple_lifetime<'a, T: 'a>(_: &'a u8, value: (T, u8)) -> (T, u8) { value }
pub fn fixed(value: [u16; 3]) -> [u16; 3] { value }
fn main() {
    let _ = identity::<u16, 3>([1, 2, 3]);
    let _ = identity::<u8, 0>([]);
    let _ = bytes::<4>([1, 2, 3, 4]);
    let _ = with_lifetime::<u8, 2>(&0, [1, 2]);
    let _ = relay::<u16, 3>([1, 2, 3]);
    let _ = nominal::<u16>(Nominal(7));
    let _ = nominal_enum::<u8>(Choice::Value(3));
    let _ = nominal_array::<u16, 3>(NominalArray([1, 2, 3]));
    let _ = two_nominals::<u8>(Nominal(1), OtherNominal(2));
    let _ = tuple_identity::<u16>((7, 1));
    let _ = tuple_identity::<u8>((2, 3));
    let _ = tuple_nested::<u16, 3>((4, [1, 2, 3]));
    let _ = tuple_forward::<u16>((5, 6));
    let _ = tuple_two_types::<u16>((7, 8), (9, 10));
    let _ = tuple_lifetime::<u16>(&0, (11, 12));
}
