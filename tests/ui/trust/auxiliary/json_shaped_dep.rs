//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! The shape of `serde_json::json!` interpolation, reduced: a macro that expands
//! to `$crate::to_value(&$e).unwrap()` over a generic, `Result`-returning
//! dependency function. Unlike serde_json's, this `to_value` is infallible BY
//! CONSTRUCTION (every `Ser` impl here returns `Ok`) and carries no `unsafe`, so
//! a consumer that declares it may re-derive it. Consumed by
//! `foreign_result_unwrap_in_dep_macro_stays_failed.rs` (DECISION_QUEUE
//! "JSON-UNWRAP-1").
#![crate_name = "json_shaped_dep"]

pub enum Value {
    Str(String),
    Num(u64),
}

#[derive(Debug)]
pub struct Error;

pub trait Ser {
    fn ser(&self) -> Result<Value, Error>;
}

impl Ser for u64 {
    fn ser(&self) -> Result<Value, Error> {
        Ok(Value::Num(*self))
    }
}

impl Ser for str {
    fn ser(&self) -> Result<Value, Error> {
        Ok(Value::Str(String::from(self)))
    }
}

impl<T: Ser + ?Sized> Ser for &T {
    fn ser(&self) -> Result<Value, Error> {
        (**self).ser()
    }
}

pub fn to_value<T: Ser>(value: T) -> Result<Value, Error> {
    value.ser()
}

// serde_json's interpolation is ONE line (`macros.rs:279`), so every site's row
// carries the same span. The two arms below expand identically but sit on
// different lines, only so the consuming test can pin EACH site's row by its
// span (`[$e]` is the `&str` site, the bare arm the `u64` site).
#[macro_export]
macro_rules! json_like {
    ([$e:expr]) => {
        $crate::to_value(&$e).unwrap()
    };
    ($e:expr) => {
        $crate::to_value(&$e).unwrap()
    };
}
