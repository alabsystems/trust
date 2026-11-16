//! A bounded serde traversal that rejects duplicate keys before typed decoding.
use std::collections::BTreeSet;
use std::fmt;

use serde::de::{self, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};

pub(super) struct Document;

impl<'de> Deserialize<'de> for Document {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(Unique)
    }
}

struct Unique;
impl<'de> Visitor<'de> for Unique {
    type Value = Document;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("duplicate-free finite JSON")
    }
    fn visit_unit<E: de::Error>(self) -> Result<Document, E> {
        Ok(Document)
    }
    fn visit_bool<E: de::Error>(self, _: bool) -> Result<Document, E> {
        Ok(Document)
    }
    fn visit_i64<E: de::Error>(self, _: i64) -> Result<Document, E> {
        Ok(Document)
    }
    fn visit_u64<E: de::Error>(self, _: u64) -> Result<Document, E> {
        Ok(Document)
    }
    fn visit_f64<E: de::Error>(self, _: f64) -> Result<Document, E> {
        Ok(Document)
    }
    fn visit_str<E: de::Error>(self, _: &str) -> Result<Document, E> {
        Ok(Document)
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Document, A::Error> {
        while seq.next_element::<Document>()?.is_some() {}
        Ok(Document)
    }
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Document, A::Error> {
        let mut seen = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !seen.insert(key) {
                return Err(de::Error::custom("duplicate census JSON key"));
            }
            map.next_value::<Document>()?;
        }
        Ok(Document)
    }
}
