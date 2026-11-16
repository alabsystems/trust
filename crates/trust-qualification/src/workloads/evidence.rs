//! Bound observations before cloning or hex-expanding them into retained data.
use std::io::{self, Write};

use serde::Serialize;
use serde_json::{Value, json};
use trust_test_execution::workload::MAX_CAPTURE_BYTES;

use crate::tree;

pub(super) const MAX_OBSERVATION_BYTES: usize = 8 * 1024 * 1024;
const MAX_OBSERVATIONS: usize = 32 * 1024 * 1024;
const MAX_RAW: usize = 128 * 1024 * 1024;
const MAX_STDERR: usize = 1024 * 1024;
const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 64;

#[derive(Default)]
pub(super) struct Budget {
    raw: usize,
    observations: usize,
}
pub(super) struct Stored<T> {
    pub value: T,
    pub complete: bool,
}
impl Budget {
    pub fn raw(&mut self, stdout: &[u8], stderr: &[u8]) -> Stored<Value> {
        let out = stdout.len().min(MAX_CAPTURE_BYTES).min(MAX_RAW - self.raw);
        self.raw += out;
        let err = stderr.len().min(MAX_STDERR).min(MAX_RAW - self.raw);
        self.raw += err;
        let complete = out == stdout.len() && err == stderr.len();
        let out_hash = tree::hash_bytes(&stdout[..out]);
        let err_hash = tree::hash_bytes(&stderr[..err]);
        Stored {
            complete,
            value: json!({"stdout_hex":hex(&stdout[..out]),"stderr_hex":hex(&stderr[..err]),
            "stdout_seen_bytes":stdout.len(),"stderr_seen_bytes":stderr.len(),
            "stdout_consumer_truncated":out!=stdout.len(),"stderr_consumer_truncated":err!=stderr.len(),
            "stdout_prefix_sha256":out_hash,"stderr_prefix_sha256":err_hash,
            "stdout_sha256":(out==stdout.len()).then_some(&out_hash),
            "stderr_sha256":(err==stderr.len()).then_some(&err_hash)}),
        }
    }
    pub fn value(&mut self, value: &Value) -> Stored<Value> {
        if !bounded_shape(value) {
            return Stored {
                complete: false,
                value: json!({"omitted":true,"scope":"typed observation only; original process bytes remain separate",
                "reason":"workload observation exceeds depth/node bound"}),
            };
        }
        self.serialize(value)
    }
    pub fn serialize(&mut self, value: &impl Serialize) -> Stored<Value> {
        let limit = MAX_OBSERVATION_BYTES.min(MAX_OBSERVATIONS - self.observations);
        let mut writer = Prefix { bytes: Vec::new(), limit };
        let encoded = serde_json::to_writer(&mut writer, value);
        self.observations += writer.bytes.len();
        if encoded.is_ok() {
            if let Ok(value) = serde_json::from_slice(&writer.bytes) {
                return Stored { value, complete: true };
            }
        }
        Stored {
            complete: false,
            value: json!({"serialized_observation_prefix_hex":hex(&writer.bytes),
            "serialized_observation_prefix_bytes":writer.bytes.len(),"truncated_or_invalid":true,
            "scope":"bounded serialization of supplied observation; not original process bytes or an execution grant"}),
        }
    }
}
struct Prefix {
    bytes: Vec<u8>,
    limit: usize,
}
impl Write for Prefix {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.is_empty() {
            return Ok(0);
        }
        let count = bytes.len().min(self.limit - self.bytes.len());
        if count == 0 {
            return Err(io::Error::other("workload observation byte bound exhausted"));
        }
        let needed = self.bytes.len() + count;
        if needed > self.bytes.capacity() {
            // Amortize serde's many small writes while preserving the exact
            // retained-byte bound, including a near-exhausted aggregate budget.
            let capacity =
                self.bytes.capacity().saturating_mul(2).max(4096).max(needed).min(self.limit);
            self.bytes.try_reserve_exact(capacity - self.bytes.len()).map_err(io::Error::other)?;
        }
        self.bytes.extend_from_slice(&bytes[..count]);
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
fn bounded_shape(value: &Value) -> bool {
    let mut remaining = MAX_NODES;
    let mut pending = vec![(value, 0usize)];
    while let Some((value, depth)) = pending.pop() {
        if remaining == 0 || depth > MAX_DEPTH {
            return false;
        }
        remaining -= 1;
        match value {
            Value::Array(values) => {
                if values.len() > remaining.saturating_sub(pending.len()) {
                    return false;
                }
                pending.extend(values.iter().map(|value| (value, depth + 1)));
            }
            Value::Object(values) => {
                if values.len() > remaining.saturating_sub(pending.len()) {
                    return false;
                }
                pending.extend(values.values().map(|value| (value, depth + 1)));
            }
            _ => {}
        }
    }
    true
}
fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(char::from(DIGITS[(byte >> 4) as usize]));
        output.push(char::from(DIGITS[(byte & 15) as usize]));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    struct CountingAllocator;
    thread_local! {static ALLOCATIONS:std::cell::Cell<Option<usize>>=const{std::cell::Cell::new(None)};}
    #[global_allocator]
    static ALLOCATOR: CountingAllocator = CountingAllocator;
    unsafe impl std::alloc::GlobalAlloc for CountingAllocator {
        unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
            let _ = ALLOCATIONS.try_with(|count| {
                if let Some(value) = count.get() {
                    count.set(Some(value + 1))
                }
            });
            unsafe { std::alloc::System.alloc(layout) }
        }
        unsafe fn dealloc(&self, pointer: *mut u8, layout: std::alloc::Layout) {
            unsafe { std::alloc::System.dealloc(pointer, layout) }
        }
        unsafe fn realloc(
            &self,
            pointer: *mut u8,
            layout: std::alloc::Layout,
            size: usize,
        ) -> *mut u8 {
            let _ = ALLOCATIONS.try_with(|count| {
                if let Some(value) = count.get() {
                    count.set(Some(value + 1))
                }
            });
            unsafe { std::alloc::System.realloc(pointer, layout, size) }
        }
    }
    #[test]
    fn bounded_evidence_does_not_allocate_per_raw_byte_or_small_json_write() {
        let raw = vec![0xab; 512 * 1024];
        let value = Value::Array(vec![Value::Null; 2048]);
        ALLOCATIONS.with(|count| count.set(Some(0)));
        let encoded = hex(&raw);
        let hex_allocations = ALLOCATIONS.with(|count| count.replace(None)).unwrap();
        assert_eq!(encoded.len(), raw.len() * 2);
        assert!(encoded.starts_with("abababab") && encoded.ends_with("abababab"));
        assert!(hex_allocations < 10, "raw prefix allocated {hex_allocations} times");
        let mut budget = Budget::default();
        ALLOCATIONS.with(|count| count.set(Some(0)));
        let stored = budget.value(&value);
        let observation_allocations = ALLOCATIONS.with(|count| count.replace(None)).unwrap();
        assert!(stored.complete);
        assert_eq!(stored.value, value);
        assert!(
            observation_allocations < 100,
            "small JSON writes allocated {observation_allocations} times"
        );
    }
    #[test]
    fn raw_prefix_is_bounded_before_retention_and_never_claims_the_full_digest() {
        let mut budget = Budget { raw: MAX_RAW - 3, observations: 0 };
        let stored = budget.raw(b"abcde", b"stderr");
        assert!(!stored.complete);
        assert_eq!(stored.value["stdout_hex"], "616263");
        assert_eq!(stored.value["stdout_seen_bytes"], 5);
        assert_eq!(stored.value["stderr_hex"], "");
        assert!(stored.value["stdout_sha256"].is_null());
        assert_eq!(budget.raw, MAX_RAW);
    }
    #[test]
    fn oversized_and_nested_observations_retain_finite_explicit_incomplete_data() {
        let mut budget = Budget { raw: 0, observations: MAX_OBSERVATIONS - 32 };
        let stored = budget.value(&json!({"observed":"z".repeat(1024)}));
        assert!(!stored.complete);
        assert_eq!(stored.value["serialized_observation_prefix_bytes"], 32);
        assert_eq!(stored.value["serialized_observation_prefix_hex"].as_str().unwrap().len(), 64);
        assert_eq!(budget.observations, MAX_OBSERVATIONS);
        let mut nested = Value::Null;
        for _ in 0..=MAX_DEPTH {
            nested = json!([nested]);
        }
        let stored = Budget::default().value(&nested);
        assert!(!stored.complete);
        assert_eq!(stored.value["omitted"], true);
    }
}
