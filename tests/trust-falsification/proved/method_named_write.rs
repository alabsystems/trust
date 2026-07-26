// T1 regression, inherent-method face: a plain Rust method literally named
// `write` (no unsafe, no FFI) must not bind the POSIX write(2) summary via
// last-segment name matching (the aterm-update-core `Sentinel::write` class —
// that method was renamed to dodge the false refutation; this fixture keeps
// the original shape provable so the rename can be reverted).
// This file must PROVE (exit 0).
#![crate_type = "lib"]

pub struct Sentinel {
    state: u32,
}

impl Sentinel {
    #[must_use]
    pub fn new() -> Self {
        Self { state: 0 }
    }

    /// Inherent method named `write` — must verify as ordinary Rust code.
    pub fn write(&mut self, v: u32) {
        self.state = v;
    }

    #[must_use]
    pub fn read(&self) -> u32 {
        self.state
    }
}

impl Default for Sentinel {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait-face twin: `io::Write`-style trait method resolution paths also end
/// in `::write` and must not bind the POSIX summary.
pub fn write_all_units(out: &mut Vec<u8>, n: usize) {
    use std::io::Write;
    // Vec<u8>'s io::Write is infallible; the unwrap is the documented contract.
    let bounded = n.min(64);
    for _ in 0..bounded {
        out.write_all(&[0u8]).unwrap_or_default();
    }
}
