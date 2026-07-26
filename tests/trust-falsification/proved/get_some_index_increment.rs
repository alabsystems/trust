// Trust R2 family 2 (bitflags `IterNames::next`, semver `numeric_identifier`):
// `slice.get(idx) == Some` implies `idx < slice.len() <= isize::MAX` (the
// `<[T]>::get` contract + the allocation-size axiom), so the get-guarded
// `idx += 1` cannot overflow usize. The corpus measurement found this exact
// idiom FALSE-REFUTED (bitflags 2.x src/iter.rs:117/172, semver 1.0.28
// src/parse.rs:174). Mutant twins: get_some_reseat_max_overflow.rs (index
// re-seated inside the arm), get_some_cross_slice_oob.rs (wrong slice).
#![crate_type = "lib"]

pub struct It {
    flags: &'static [u32],
    idx: usize,
}

impl Iterator for It {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        while let Some(flag) = self.flags.get(self.idx) {
            self.idx += 1;
            if *flag != 0 {
                return Some(*flag);
            }
        }
        None
    }
}
