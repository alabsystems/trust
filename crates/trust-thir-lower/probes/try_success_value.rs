// Actual-THIR controls for complete success values carried through core `?`.
#![allow(dead_code)]

#[derive(Clone, Copy)]
pub struct RichError {
    pub address: *const u8,
    pub code: u64,
    pub metadata: u64,
}

#[derive(Clone, Copy)]
pub struct Nested {
    pub signed: i64,
    pub float: f64,
}

#[derive(Clone, Copy)]
pub struct RichValue {
    pub address: *const u8,
    pub code: u64,
    pub nested: Nested,
}

#[derive(Clone, Copy)]
pub enum RichEnum {
    Pointer(RichValue),
    Text(&'static str),
    Code(u64),
}

pub fn float32(input: Result<f32, RichError>) -> Result<f32, RichError> {
    let value = input?;
    Ok(value)
}

pub fn float64(input: Result<f64, RichError>) -> Result<f64, RichError> {
    let value = input?;
    Ok(value)
}

pub fn rich_struct(input: Result<RichValue, RichError>) -> Result<RichValue, RichError> {
    let value = input?;
    Ok(value)
}

pub fn rich_enum(input: Result<RichEnum, RichError>) -> Result<RichEnum, RichError> {
    let value = input?;
    Ok(value)
}

pub fn option_struct(input: Option<RichValue>) -> Option<RichValue> {
    let value = input?;
    Some(value)
}

pub fn operand_once(
    counter: &mut u32,
    input: Result<RichValue, RichError>,
) -> Result<RichValue, RichError> {
    let value = {
        *counter += 1;
        input
    }?;
    Ok(value)
}

pub fn legacy(input: Result<u32, u32>) -> Result<u64, u32> {
    let value = input?;
    Ok(u64::from(value))
}

pub fn unit(input: Result<(), RichError>) -> Result<u64, RichError> {
    input?;
    Ok(71)
}

pub fn direct_reference<'a>(input: Result<&'a u64, RichError>) -> Result<&'a u64, RichError> {
    let value = input?;
    Ok(value)
}

pub fn direct_pointer(input: Result<*const u8, RichError>) -> Result<*const u8, RichError> {
    let value = input?;
    Ok(value)
}

pub fn direct_fat(input: Result<&'static str, RichError>) -> Result<&'static str, RichError> {
    let value = input?;
    Ok(value)
}

pub fn generic<T>(input: Result<T, RichError>) -> Result<T, RichError> {
    let value = input?;
    Ok(value)
}

pub struct Wrapped<T> {
    pub value: T,
    pub address: *const u8,
}

pub fn wrapped_generic<T>(input: Result<Wrapped<T>, RichError>) -> Result<Wrapped<T>, RichError> {
    let value = input?;
    Ok(value)
}

pub union Choice {
    pub integer: u64,
    pub pointer: *const u8,
}

pub struct WithUnion {
    pub value: Choice,
}

pub fn nested_union(input: Result<WithUnion, RichError>) -> Result<WithUnion, RichError> {
    let value = input?;
    Ok(value)
}

pub struct Converted(pub RichError);

impl From<RichError> for Converted {
    fn from(error: RichError) -> Self {
        Self(error)
    }
}

pub fn converting(input: Result<RichValue, RichError>) -> Result<RichValue, Converted> {
    let value = input?;
    Ok(value)
}
