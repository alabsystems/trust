// Actual-THIR fixture: no fabricated default exists for the pointer-bearing Err.
#![allow(dead_code)]
#[derive(Clone, Copy)]
pub struct RichError { pub address: *const u8, pub code: u64, pub metadata: u64 }
#[derive(Clone, Copy)]
pub enum RichEnum { Pointer(RichError), Text(&'static str), Code(u64) }
pub fn result_struct(input: Result<(), RichError>) -> Result<u64, RichError> {
    input?;
    Ok(7)
}
pub fn result_enum(input: Result<(), RichEnum>) -> Result<u64, RichEnum> {
    input?;
    Ok(11)
}
pub fn legacy_scalar(input: Result<(), u64>) -> Result<u64, u64> { input?; Ok(13) }
pub fn direct_fat(input: Result<(), &'static str>) -> Result<u64, &'static str> { input?; Ok(17) }
pub fn generic_error<E>(input: Result<(), E>) -> Result<u64, E> { input?; Ok(19) }
pub fn borrowed(input: &Result<(), RichError>) -> Result<u64, RichError> { (*input)?; Ok(23) }
pub struct Converted(pub RichError);
impl From<RichError> for Converted { fn from(e: RichError) -> Self { Self(e) } }
pub fn converting(input: Result<(), RichError>) -> Result<u64, Converted> { input?; Ok(29) }
// Existing direct-reference / pointer and bare-param custody walls stay closed.
pub fn direct_borrow<'a>(input: Result<(), &'a RichError>) -> Result<u64, &'a RichError> {
    input?; Ok(31)
}
pub fn direct_pointer(input: Result<(), *const u8>) -> Result<u64, *const u8> { input?; Ok(37) }
pub struct Wrapped<E> { pub payload: E, pub address: *const u8 }
pub fn wrapped_generic<E>(input: Result<(), Wrapped<E>>) -> Result<u64, Wrapped<E>> {
    input?; Ok(41)
}
pub fn non_scalar_success(input: Result<RichError, RichEnum>) -> Result<RichError, RichEnum> {
    let value = input?; Ok(value)
}
