// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `json!` macro.
//!
//! # The one deliberate difference from the incumbent
//!
//! `serde_json::json!` lowers an interpolated expression with
//! `serde_json::to_value`, which requires `Serialize`. This crate has no serde
//! dependency by design, so interpolation here requires `Into<Value>` instead.
//!
//! That covers every literal, every `&str`/`String`, every integer and float,
//! every `Vec<T: Into<Value>>` and every `Option<T: Into<Value>>` — which is
//! what the overwhelming majority of the 1454 `json!` sites in this tree
//! interpolate. It does NOT cover `json!(some_derived_struct)`. Those sites
//! compile again unchanged the moment the serde layer lands and supplies a
//! blanket `impl<T: Serialize> From<T> for Value`; until then the macro is
//! honest about the gap instead of silently accepting and mis-serializing.

/// Constructs a [`crate::Value`] from a JSON literal.
#[macro_export]
macro_rules! json {
    ($($json:tt)+) => {
        $crate::json_internal!($($json)+)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! json_internal {
    //////////////////////////////////////////////////////////////////////////
    // TT muncher for parsing the inside of an array [...]. Produces a vec![...]
    // of the elements.
    //////////////////////////////////////////////////////////////////////////

    // Done with trailing comma.
    (@array [$($elems:expr,)*]) => {
        $crate::json_internal_vec![$($elems,)*]
    };

    // Done without trailing comma.
    (@array [$($elems:expr),*]) => {
        $crate::json_internal_vec![$($elems),*]
    };

    // Next element is `null`.
    (@array [$($elems:expr,)*] null $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!(null)] $($rest)*)
    };

    // Next element is `true`.
    (@array [$($elems:expr,)*] true $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!(true)] $($rest)*)
    };

    // Next element is `false`.
    (@array [$($elems:expr,)*] false $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!(false)] $($rest)*)
    };

    // Next element is an array.
    (@array [$($elems:expr,)*] [$($array:tt)*] $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!([$($array)*])] $($rest)*)
    };

    // Next element is a map.
    (@array [$($elems:expr,)*] {$($map:tt)*} $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!({$($map)*})] $($rest)*)
    };

    // Next element is an expression followed by comma.
    (@array [$($elems:expr,)*] $next:expr, $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!($next),] $($rest)*)
    };

    // Last element is an expression with no trailing comma.
    (@array [$($elems:expr,)*] $last:expr) => {
        $crate::json_internal!(@array [$($elems,)* $crate::json_internal!($last)])
    };

    // Comma after the most recent element.
    (@array [$($elems:expr),*] , $($rest:tt)*) => {
        $crate::json_internal!(@array [$($elems,)*] $($rest)*)
    };

    //////////////////////////////////////////////////////////////////////////
    // TT muncher for parsing the inside of an object {...}.
    //////////////////////////////////////////////////////////////////////////

    // Done.
    (@object $object:ident () () ()) => {};

    // Insert the current entry followed by trailing comma.
    (@object $object:ident [$($key:tt)+] ($value:expr) , $($rest:tt)*) => {
        let _ = $object.insert(($($key)+).into(), $value);
        $crate::json_internal!(@object $object () ($($rest)*) ($($rest)*));
    };

    // Current entry followed by unexpected token.
    (@object $object:ident [$($key:tt)+] ($value:expr) $unexpected:tt $($rest:tt)*) => {
        $crate::json_unexpected!($unexpected);
    };

    // Insert the last entry without trailing comma.
    (@object $object:ident [$($key:tt)+] ($value:expr)) => {
        let _ = $object.insert(($($key)+).into(), $value);
    };

    // Next value is `null`.
    (@object $object:ident ($($key:tt)+) (: null $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!(null)) $($rest)*);
    };

    // Next value is `true`.
    (@object $object:ident ($($key:tt)+) (: true $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!(true)) $($rest)*);
    };

    // Next value is `false`.
    (@object $object:ident ($($key:tt)+) (: false $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!(false)) $($rest)*);
    };

    // Next value is an array.
    (@object $object:ident ($($key:tt)+) (: [$($array:tt)*] $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!([$($array)*])) $($rest)*);
    };

    // Next value is a map.
    (@object $object:ident ($($key:tt)+) (: {$($map:tt)*} $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!({$($map)*})) $($rest)*);
    };

    // Next value is an expression followed by comma.
    (@object $object:ident ($($key:tt)+) (: $value:expr , $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!($value)) , $($rest)*);
    };

    // Last value is an expression with no trailing comma.
    (@object $object:ident ($($key:tt)+) (: $value:expr) $copy:tt) => {
        $crate::json_internal!(@object $object [$($key)+] ($crate::json_internal!($value)));
    };

    // Missing value for last entry.
    (@object $object:ident ($($key:tt)+) (:) $copy:tt) => {
        $crate::json_internal!();
    };

    // Missing colon and value for last entry.
    (@object $object:ident ($($key:tt)+) () $copy:tt) => {
        $crate::json_internal!();
    };

    // Misplaced colon.
    (@object $object:ident () (: $($rest:tt)*) ($colon:tt $($copy:tt)*)) => {
        $crate::json_unexpected!($colon);
    };

    // Found a comma inside a key.
    (@object $object:ident ($($key:tt)*) (, $($rest:tt)*) ($comma:tt $($copy:tt)*)) => {
        $crate::json_unexpected!($comma);
    };

    // Munch a token into the current key.
    (@object $object:ident ($($key:tt)*) ($tt:tt $($rest:tt)*) $copy:tt) => {
        $crate::json_internal!(@object $object ($($key)* $tt) ($($rest)*) ($($rest)*));
    };

    //////////////////////////////////////////////////////////////////////////
    // The primary rules.
    //////////////////////////////////////////////////////////////////////////

    (null) => {
        $crate::Value::Null
    };

    (true) => {
        $crate::Value::Bool(true)
    };

    (false) => {
        $crate::Value::Bool(false)
    };

    ([]) => {
        $crate::Value::Array($crate::json_internal_vec![])
    };

    ([ $($tt:tt)+ ]) => {
        $crate::Value::Array($crate::json_internal!(@array [] $($tt)+))
    };

    ({}) => {
        $crate::Value::Object($crate::Map::new())
    };

    ({ $($tt:tt)+ }) => {
        $crate::Value::Object({
            let mut object = $crate::Map::new();
            $crate::json_internal!(@object object () ($($tt)+) ($($tt)+));
            object
        })
    };

    // Any `Into<Value>`. See the module docs for why this is `Into` and not
    // `Serialize`.
    ($other:expr) => {
        ::core::convert::Into::<$crate::Value>::into($other)
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! json_internal_vec {
    ($($content:tt)*) => {
        vec![$($content)*]
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! json_unexpected {
    () => {};
}

#[cfg(test)]
mod tests {
    use crate::Value;

    #[test]
    fn literals_and_nesting() {
        let v = json!({"b": 1, "a": [1, 2, {"z": null}], "c": {}, "d": [], "e": "x"});
        assert_eq!(v.to_string(), r#"{"a":[1,2,{"z":null}],"b":1,"c":{},"d":[],"e":"x"}"#);
        assert_eq!(json!(null), Value::Null);
        assert_eq!(json!(true).to_string(), "true");
        assert_eq!(json!(1.0).to_string(), "1.0");
        assert_eq!(json!(1).to_string(), "1");
    }

    #[test]
    fn interpolation() {
        let n = 7u32;
        let s = String::from("hi");
        let v = json!({ "n": n, "s": s, "arr": vec![1u8, 2, 3] });
        assert_eq!(v.to_string(), r#"{"arr":[1,2,3],"n":7,"s":"hi"}"#);
    }
}
