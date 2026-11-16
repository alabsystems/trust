// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Authenticated observations share the exact original Context authority. No
//! measurement, scalar or liveness description is an allocation capability.
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{ContextQuery, ContextReply, ContextUnavailable};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pressure {
    Unknown,
    Normal,
    Warn,
    Critical,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Thermal {
    Unknown,
    Nominal,
    Fair,
    Serious,
    Critical,
}
/// Age belongs to the original cached observation, never the RPC cache hit.
/// Consumers add monotonic time since receipt and apply their freshness bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Snapshot {
    pub cpus: u32,
    pub busy_millicores: Option<u64>,
    pub available_memory_bytes: Option<u64>,
    pub pressure: Pressure,
    pub thermal: Thermal,
    pub sample_age_ns: u64,
    pub window_ns: u64,
}
#[derive(Clone, PartialEq, Eq)]
pub struct TelemetryQuery {
    pub query: ContextQuery,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TelemetryReply {
    pub context: ContextReply,
    pub snapshot: Snapshot,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TelemetryResponse {
    Ready(Box<TelemetryReply>),
    Unavailable(ContextUnavailable),
}

impl TelemetryQuery {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(9);
        e.bytes(&self.query.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 9)?;
        let query = ContextQuery::decode(&d.bytes()?)?;
        d.done()?;
        Ok(Self { query })
    }
}
impl Snapshot {
    fn validate(self) -> io::Result<()> {
        if self.cpus == 0
            || self.cpus > 1_048_576
            || self.busy_millicores.is_some_and(|busy| busy > u64::from(self.cpus) * 1000)
            || self.busy_millicores.is_some()
                && (self.window_ns == 0 || self.window_ns > 60_000_000_000)
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn encode(self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.number(self.cpus.into());
        optional_encode(e, self.busy_millicores);
        optional_encode(e, self.available_memory_bytes);
        e.number(match self.pressure {
            Pressure::Unknown => 0,
            Pressure::Normal => 1,
            Pressure::Warn => 2,
            Pressure::Critical => 3,
        });
        e.number(match self.thermal {
            Thermal::Unknown => 0,
            Thermal::Nominal => 1,
            Thermal::Fair => 2,
            Thermal::Serious => 3,
            Thermal::Critical => 4,
        });
        e.number(self.sample_age_ns);
        e.number(self.window_ns);
        Ok(())
    }
    fn decode(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self {
            cpus: d.narrow()?,
            busy_millicores: optional_decode(d)?,
            available_memory_bytes: optional_decode(d)?,
            pressure: match d.number()? {
                0 => Pressure::Unknown,
                1 => Pressure::Normal,
                2 => Pressure::Warn,
                3 => Pressure::Critical,
                _ => return Err(invalid()),
            },
            thermal: match d.number()? {
                0 => Thermal::Unknown,
                1 => Thermal::Nominal,
                2 => Thermal::Fair,
                3 => Thermal::Serious,
                4 => Thermal::Critical,
                _ => return Err(invalid()),
            },
            sample_age_ns: d.number()?,
            window_ns: d.number()?,
        };
        value.validate()?;
        Ok(value)
    }
}
fn optional_encode(e: &mut Encoder, value: Option<u64>) {
    match value {
        None => e.number(0),
        Some(value) => {
            e.number(1);
            e.number(value);
        }
    }
}
fn optional_decode(d: &mut Decoder<'_>) -> io::Result<Option<u64>> {
    match d.number()? {
        0 => Ok(None),
        1 => Ok(Some(d.number()?)),
        _ => Err(invalid()),
    }
}
impl TelemetryReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(10);
        e.bytes(&self.context.encode()?)?;
        self.snapshot.encode(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &TelemetryQuery) -> io::Result<Self> {
        let mut d = header(bytes, 10)?;
        let context = ContextReply::decode(&d.bytes()?, &query.query)?;
        let snapshot = Snapshot::decode(&mut d)?;
        d.done()?;
        Ok(Self { context, snapshot })
    }
}
impl TelemetryResponse {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        match self {
            Self::Ready(value) => value.encode(),
            Self::Unavailable(value) => {
                let mut e = Encoder::new(11);
                e.bytes(&value.encode()?)?;
                e.finish()
            }
        }
    }
    pub fn decode(bytes: &[u8], query: &TelemetryQuery) -> io::Result<Self> {
        if header(bytes, 10).is_ok() {
            return TelemetryReply::decode(bytes, query).map(Box::new).map(Self::Ready);
        }
        let mut d = header(bytes, 11)?;
        let value = ContextUnavailable::decode(&d.bytes()?, &query.query)?;
        d.done()?;
        Ok(Self::Unavailable(value))
    }
}
