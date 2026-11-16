//! Complete JSON identity without floating-point rounding or global numeric
//! feature changes. Objects reject duplicates; numbers retain exact lexemes.
use std::collections::BTreeMap;
use std::fmt;

use serde::de::{self, MapAccess, Visitor};
use serde::ser::{SerializeMap, SerializeSeq};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::value::RawValue;

use crate::{Result, refusal};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Json {
    Null,
    Bool(bool),
    String(String),
    Number(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

impl Json {
    pub(super) fn parse(bytes: &[u8]) -> Result<Self> {
        let raw: Box<RawValue> = serde_json::from_slice(bytes)
            .map_err(|e| refusal(format!("invalid metadata JSON: {e}")))?;
        Self::from_raw(&raw, 0)
    }

    fn from_raw(raw: &RawValue, depth: usize) -> Result<Self> {
        if depth > 128 {
            return Err(refusal("metadata JSON exceeds the finite nesting limit"));
        }
        let text = raw.get();
        let invalid = |e| refusal(format!("invalid metadata JSON: {e}"));
        match text.as_bytes().first() {
            Some(b'n') => Ok(Self::Null),
            Some(b't') => Ok(Self::Bool(true)),
            Some(b'f') => Ok(Self::Bool(false)),
            Some(b'"') => Ok(Self::String(serde_json::from_str(text).map_err(invalid)?)),
            Some(b'[') => {
                let children: Vec<Box<RawValue>> = serde_json::from_str(text).map_err(invalid)?;
                children
                    .iter()
                    .map(|child| Self::from_raw(child, depth + 1))
                    .collect::<Result<Vec<_>>>()
                    .map(Self::Array)
            }
            Some(b'{') => {
                let children: UniqueObject = serde_json::from_str(text).map_err(invalid)?;
                children
                    .0
                    .into_iter()
                    .map(|(name, child)| Ok((name, Self::from_raw(&child, depth + 1)?)))
                    .collect::<Result<BTreeMap<_, _>>>()
                    .map(Self::Object)
            }
            Some(b'-' | b'0'..=b'9') => Ok(Self::Number(text.into())),
            _ => Err(refusal("invalid metadata JSON token")),
        }
    }

    pub(super) fn get(&self, field: &str) -> Option<&Self> {
        match self {
            Self::Object(fields) => fields.get(field),
            _ => None,
        }
    }
    pub(super) fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(text) => Some(text),
            _ => None,
        }
    }
    pub(super) fn as_array(&self) -> Option<&Vec<Self>> {
        match self {
            Self::Array(array) => Some(array),
            _ => None,
        }
    }
    pub(super) fn as_u64(&self) -> Option<u64> {
        match self {
            Self::Number(text) if text.bytes().all(|b| b.is_ascii_digit()) => text.parse().ok(),
            _ => None,
        }
    }
    pub(super) fn is_object(&self) -> bool {
        matches!(self, Self::Object(_))
    }
}

struct UniqueObject(BTreeMap<String, Box<RawValue>>);
impl<'de> Deserialize<'de> for UniqueObject {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        struct Object;
        impl<'de> Visitor<'de> for Object {
            type Value = UniqueObject;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a metadata object with unique keys")
            }
            fn visit_map<A: MapAccess<'de>>(
                self,
                mut map: A,
            ) -> std::result::Result<Self::Value, A::Error> {
                let mut fields = BTreeMap::new();
                while let Some(name) = map.next_key::<String>()? {
                    if fields.contains_key(&name) {
                        return Err(de::Error::custom("duplicate metadata JSON key"));
                    }
                    fields.insert(name, map.next_value()?);
                }
                Ok(UniqueObject(fields))
            }
        }
        deserializer.deserialize_map(Object)
    }
}

impl Serialize for Json {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        match self {
            Self::Null => serializer.serialize_unit(),
            Self::Bool(value) => serializer.serialize_bool(*value),
            Self::String(text) => serializer.serialize_str(text),
            Self::Number(text) => {
                let raw = RawValue::from_string(text.clone()).map_err(serde::ser::Error::custom)?;
                raw.serialize(serializer)
            }
            Self::Array(values) => {
                let mut seq = serializer.serialize_seq(Some(values.len()))?;
                for value in values {
                    seq.serialize_element(value)?;
                }
                seq.end()
            }
            Self::Object(fields) => {
                let mut map = serializer.serialize_map(Some(fields.len()))?;
                for (name, value) in fields {
                    map.serialize_entry(name, value)?;
                }
                map.end()
            }
        }
    }
}
