// A realistic bounded-stack container — HAND-AUTHORED source; the MIR dumps are
// real trustc output (the "not hand-authored" applies to the MIR JSON, not this file).
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
pub struct Stack { buf: [u64; 32], len: u32, cap: u32 }
impl Stack {
    pub fn len(&self) -> u64 { self.len as u64 }
    pub fn capacity(&self) -> u64 { self.cap as u64 }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn is_full(&self) -> bool { self.len() == self.capacity() }
    pub fn remaining(&self) -> u64 { self.capacity() - self.len() }
    pub fn has_len(&self, n: u64) -> bool { self.len() == n }
    pub fn at_least(&self, n: u64) -> bool { self.len() >= n }
    pub fn double_len(&self) -> u64 { self.len() + self.len() }
}
