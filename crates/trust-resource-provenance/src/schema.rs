// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The existing version-one custodian book, shared by readers and writers.
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::{fmt, io};

use serde::de::{self, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use serde_json::{Map, Value, json};

pub const MAX_JSON: usize = 1024 * 1024;
pub const MAX_INSTANCES: usize = 128;

pub(crate) fn refused(why: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, why)
}

/// Original filesystem identity; these numbers grant no resource authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FileId {
    pub dev: u64,
    pub ino: u64,
}

/// One immutable image, native lifetime and bound listener observation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub pid: u32,
    pub birth: u64,
    pub host: String,
    pub boot: String,
    pub digest: String,
    pub image: FileId,
    pub directory: FileId,
    pub socket_hex: String,
    pub socket: FileId,
}

/// The exact bounded version-one wire book. Encoding also validates its rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Book {
    pub version: u32,
    pub instances: Vec<Record>,
}

pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8] = b"0123456789abcdef";
    bytes
        .iter()
        .flat_map(|b| [DIGITS[usize::from(b >> 4)] as char, DIGITS[usize::from(b & 15)] as char])
        .collect()
}

pub fn unhex(text: &str) -> io::Result<Vec<u8>> {
    if text.len() > 32768 || text.len() % 2 != 0 {
        return Err(refused("invalid bounded path hex"));
    }
    let nibble = |b| match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'f' => Ok(b - b'a' + 10),
        _ => Err(refused("noncanonical hex")),
    };
    text.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|b| Ok(nibble(b[0])? * 16 + nibble(b[1])?))
        .collect()
}

pub fn digest_shaped(text: &str) -> bool {
    text.len() == 64 && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn object<'a>(value: &'a Value, fields: &[&str]) -> io::Result<&'a Value> {
    let map = value.as_object().ok_or_else(|| refused("expected object"))?;
    if map.len() != fields.len() || fields.iter().any(|key| !map.contains_key(*key)) {
        return Err(refused("unexpected or missing book field"));
    }
    Ok(value)
}
fn number(value: &Value) -> io::Result<u64> {
    value.as_u64().ok_or_else(|| refused("expected unsigned integer"))
}
fn text(value: &Value) -> io::Result<String> {
    value.as_str().map(str::to_owned).ok_or_else(|| refused("expected string"))
}
impl FileId {
    /// Identity from the actual opened object's metadata, shared with cache writers.
    pub fn of_metadata(meta: &std::fs::Metadata) -> Self {
        use std::os::unix::fs::MetadataExt as _;
        Self { dev: meta.dev(), ino: meta.ino() }
    }
    fn decode(value: &Value) -> io::Result<Self> {
        let map = object(value, &["dev", "ino"])?;
        Ok(Self { dev: number(&map["dev"])?, ino: number(&map["ino"])? })
    }
    fn value(self) -> Value {
        json!({"dev":self.dev,"ino":self.ino})
    }
}
impl Record {
    fn decode(value: &Value) -> io::Result<Self> {
        let row = object(
            value,
            &[
                "pid",
                "birth",
                "host",
                "boot",
                "digest",
                "image",
                "directory",
                "socket_hex",
                "socket",
            ],
        )?;
        let record = Self {
            pid: u32::try_from(number(&row["pid"])?).map_err(|_| refused("invalid pid"))?,
            birth: number(&row["birth"])?,
            host: text(&row["host"])?,
            boot: text(&row["boot"])?,
            digest: text(&row["digest"])?,
            image: FileId::decode(&row["image"])?,
            directory: FileId::decode(&row["directory"])?,
            socket_hex: text(&row["socket_hex"])?,
            socket: FileId::decode(&row["socket"])?,
        };
        record.validate()?;
        Ok(record)
    }
    fn validate(&self) -> io::Result<()> {
        if self.pid <= 1
            || self.birth == 0
            || !digest_shaped(&self.digest)
            || [&self.host, &self.boot].iter().any(|s| s.is_empty() || s.len() > 256)
        {
            return Err(refused("invalid instance record"));
        }
        self.socket_path().map(drop)
    }
    pub fn socket_path(&self) -> io::Result<PathBuf> {
        let bytes = unhex(&self.socket_hex)?;
        if bytes.contains(&0) {
            return Err(refused("invalid socket path"));
        }
        let path = PathBuf::from(OsString::from_vec(bytes));
        if !path.is_absolute() {
            return Err(refused("socket path is not absolute"));
        }
        Ok(path)
    }
    fn value(&self) -> Value {
        json!({"pid":self.pid,"birth":self.birth,"host":self.host,"boot":self.boot,
            "digest":self.digest,"image":self.image.value(),"directory":self.directory.value(),
            "socket_hex":self.socket_hex,"socket":self.socket.value()})
    }
}
impl Book {
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() > MAX_JSON {
            return Err(refused("oversized instance book"));
        }
        let Strict(value) = serde_json::from_slice(bytes).map_err(io::Error::other)?;
        let map = object(&value, &["version", "instances"])?;
        if number(&map["version"])? != 1 {
            return Err(refused("unsupported instance book"));
        }
        let rows = map["instances"].as_array().ok_or_else(|| refused("invalid instances"))?;
        if rows.len() > MAX_INSTANCES {
            return Err(refused("oversized instance book"));
        }
        let book = Self {
            version: 1,
            instances: rows.iter().map(Record::decode).collect::<io::Result<_>>()?,
        };
        book.validate()?;
        Ok(book)
    }
    fn validate(&self) -> io::Result<()> {
        if self.version != 1 || self.instances.len() > MAX_INSTANCES {
            return Err(refused("unsupported or oversized instance book"));
        }
        for (i, row) in self.instances.iter().enumerate() {
            row.validate()?;
            if self.instances[..i].iter().any(|old| {
                old.pid == row.pid
                    && old.birth == row.birth
                    && old.host == row.host
                    && old.boot == row.boot
            }) {
                return Err(refused("duplicate native lifetime"));
            }
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let bytes = serde_json::to_vec(&json!({"version":1,"instances":self.instances.iter().map(Record::value).collect::<Vec<_>>()})).map_err(io::Error::other)?;
        if bytes.len() > MAX_JSON {
            return Err(refused("oversized instance book"));
        }
        Ok(bytes)
    }
}

// Value alone silently replaces duplicate keys. Preserve the original typed
// book's duplicate-field refusal without introducing a procedural derive.
struct Strict(Value);
impl<'de> Deserialize<'de> for Strict {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct StrictVisitor;
        impl<'de> Visitor<'de> for StrictVisitor {
            type Value = Strict;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("duplicate-free JSON")
            }
            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Strict, E> {
                Ok(Strict(Value::Bool(v)))
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Strict, E> {
                Ok(Strict(v.into()))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Strict, E> {
                Ok(Strict(v.into()))
            }
            fn visit_f64<E: de::Error>(self, _: f64) -> Result<Strict, E> {
                Err(E::custom("floating point is not an instance-book field"))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Strict, E> {
                Ok(Strict(v.into()))
            }
            fn visit_string<E: de::Error>(self, v: String) -> Result<Strict, E> {
                Ok(Strict(v.into()))
            }
            fn visit_unit<E: de::Error>(self) -> Result<Strict, E> {
                Ok(Strict(Value::Null))
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut rows: A) -> Result<Strict, A::Error> {
                let mut out = Vec::new();
                while let Some(Strict(value)) = rows.next_element()? {
                    out.push(value);
                }
                Ok(Strict(Value::Array(out)))
            }
            fn visit_map<A: MapAccess<'de>>(self, mut fields: A) -> Result<Strict, A::Error> {
                let mut out = Map::new();
                while let Some(key) = fields.next_key::<String>()? {
                    if out.contains_key(&key) {
                        return Err(de::Error::custom("duplicate JSON field"));
                    }
                    let Strict(value) = fields.next_value()?;
                    out.insert(key, value);
                }
                Ok(Strict(Value::Object(out)))
            }
        }
        d.deserialize_any(StrictVisitor)
    }
}

#[cfg(test)]
#[path = "schema/tests.rs"]
mod tests;
