// MUTANT twin of proved/get_some_index_increment.rs: the Some arm RE-SEATS the
// index to usize::MAX before the increment — the get-contract fact is stale for
// the poisoned read and the consumers must DROP it (the block redefines the
// fact's variable); `usize::MAX + 1` overflows at runtime.
#![crate_type = "lib"]

pub struct It {
    flags: &'static [u32],
    idx: usize,
}

impl It {
    pub fn poisoned(&mut self) -> usize {
        while let Some(_flag) = self.flags.get(self.idx) {
            self.idx = usize::MAX;
            let x = self.idx + 1;
            return x;
        }
        0
    }
}
