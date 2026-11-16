//! Checked immutable native-object inventory and descriptor-service substrate.
//!
//! This module never loads a DSO or enables compiler macro admission. A prepared
//! closure is structural owner-bound data, not authenticated tool provenance.
//! The kernel service is private until its full trusted launcher is qualified.
mod admission;
mod bootstrap;
mod closure;
mod configuration;
mod elf;
mod grant;
mod io;
mod kernel;
mod mappings;
mod owner;
mod receipt;

#[cfg(feature = "static-fixture")]
mod entry_fixture;
#[cfg(feature = "static-fixture")]
#[doc(hidden)]
pub use entry_fixture::entry_fixture;

#[cfg(test)]
mod entry_tests;

pub use closure::{
    NativeClosure, NativeInputReceipt, NativeObjectPlan, NativeObjectReceipt, NativeRole, digest,
};
pub(crate) use configuration::Configuration;
use trust_process_isolation::{Budget, Charge};

use crate::Error;

const OBJECTS: usize = 27;
const ALIASES: usize = 8;
const NAME: usize = 255;
const PATH: usize = 1024;
const BANK_FIRST: u32 = 33;
const BANK_LAST: u32 = 63;

fn check(b: &Budget) -> Result<(), Error> {
    b.check().map_err(Error::Budget)
}
fn charge(b: &Budget, delta: Charge) -> Result<(), Error> {
    b.charge(delta).map_err(Error::Budget)
}
fn contract(b: &Budget, reason: &'static str) -> Error {
    b.refuse(trust_process_isolation::Error::Phase);
    Error::Contract(reason)
}
fn reserve<T>(n: usize, b: &Budget) -> Result<Vec<T>, Error> {
    let bytes = n
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| Error::Budget(b.refuse(trust_process_isolation::Error::Overflow)))?;
    charge(b, Charge { allocation_bytes: bytes as u64, ..Charge::default() })?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(n)
        .map_err(|_| Error::Budget(b.refuse(trust_process_isolation::Error::Allocation)))?;
    let slack = result
        .capacity()
        .checked_sub(n)
        .and_then(|n| n.checked_mul(std::mem::size_of::<T>()))
        .ok_or_else(|| Error::Budget(b.refuse(trust_process_isolation::Error::Overflow)))?;
    charge(b, Charge { allocation_bytes: slack as u64, ..Charge::default() })?;
    check(b)?;
    Ok(result)
}

#[cfg(test)]
mod tests;
