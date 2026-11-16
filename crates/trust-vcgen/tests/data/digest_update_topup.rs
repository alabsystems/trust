//! TRUST-KI-1015-1, the top-up shape of aterm-digest `Sha256::update` (sha256.rs:103-106 at
//! aterm 848d791bd): one correct program and wrong twins that really panic.
//! Field order mirrors `Sha256` (`buf_len` is field 2).

pub const BLOCK_LEN: usize = 64;

pub struct Acc {
    pub state: [u32; 8],
    pub buf: [u8; BLOCK_LEN],
    pub buf_len: usize,
    pub len: u64,
}

impl Acc {
    /// CORRECT. `BLOCK_LEN - buf_len` passed, so `buf_len <= 64`, and `take <= 64 - buf_len`:
    /// the slice `buf_len..buf_len + take` is in `buf`, and neither Add overflows.
    pub fn top_up(&mut self, data: &[u8]) -> usize {
        if self.buf_len > 0 {
            let take = (BLOCK_LEN - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            return take;
        }
        0
    }

    /// WRONG: one byte of room too many. `buf_len = 1`, `data.len() = 64`: `buf[1..65]` panics.
    pub fn top_up_room_past_end(&mut self, data: &[u8]) -> usize {
        if self.buf_len > 0 {
            let take = (BLOCK_LEN + 1 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            return take;
        }
        0
    }

    /// WRONG: `max` for `min`. `buf_len = 1`, `data.len() = 100`: `buf[1..101]` panics.
    pub fn top_up_max(&mut self, data: &[u8]) -> usize {
        if self.buf_len > 0 {
            let take = (BLOCK_LEN - self.buf_len).max(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            return take;
        }
        0
    }

    /// Writes `buf_len` through `&mut self` between the two reads of `top_up_callee_writes`.
    #[inline(never)]
    pub fn fill_to_end(&mut self, n: usize) -> usize {
        self.buf_len = BLOCK_LEN;
        n
    }

    /// WRONG: a callee that takes `&mut self` really writes `buf_len` between the room read and
    /// the slice read. `buf_len = 1`, `data.len() = 1`: room 63, take 1, then `buf[64..65]` panics.
    pub fn top_up_callee_writes(&mut self, data: &[u8]) -> usize {
        if self.buf_len > 0 {
            let take = (BLOCK_LEN - self.buf_len).min(self.fill_to_end(data.len()));
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            return take;
        }
        0
    }

    /// WRONG: `take` wraps when `data` is empty. `buf_len = 1`, `data.len() = 0`:
    /// `take = usize::MAX`, so `buf_len + take` overflows.
    pub fn top_up_wrapping_take(&mut self, data: &[u8]) -> usize {
        if self.buf_len > 0 {
            let take = (BLOCK_LEN - self.buf_len).min(data.len()).wrapping_sub(1);
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            return take;
        }
        0
    }
}

/// A raw pointer parked by [`stash`] and written by [`poke`]: the channel through which a callee
/// handed only values writes caller memory, once an EARLIER callee received a `&mut` into it.
static STASH: core::sync::atomic::AtomicPtr<usize> =
    core::sync::atomic::AtomicPtr::new(core::ptr::null_mut());

/// Keeps a raw child of `p` past the call.
#[inline(never)]
pub fn stash(p: &mut usize) {
    STASH.store(p, core::sync::atomic::Ordering::Relaxed);
}

/// A value-only callee that writes nothing.
#[inline(never)]
pub fn mix(n: usize) -> usize {
    n.rotate_left(5) ^ 0x9e37
}

/// Reads and writes back `*p`.
#[inline(never)]
pub fn touch(p: &mut usize) {
    *p = core::hint::black_box(*p);
}

/// Takes and returns a value; writes `BLOCK_LEN` through the parked pointer, if any.
#[inline(never)]
pub fn poke(n: usize) -> usize {
    let p = STASH.load(core::sync::atomic::Ordering::Relaxed);
    if !p.is_null() {
        unsafe { *p = BLOCK_LEN };
    }
    n
}

impl Acc {
    /// WRONG: `&mut self.buf_len` reached a callee BEFORE the value-only call, which writes it
    /// through the parked pointer. `buf_len = 1`, `data.len() = 1`: room 63, `poke` sets
    /// `buf_len = 64`, then `buf[64..65]` panics.
    pub fn top_up_stashed(&mut self, data: &[u8]) -> usize {
        if self.buf_len > 0 {
            stash(&mut self.buf_len);
            let take = (BLOCK_LEN - self.buf_len).min(poke(data.len()));
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            return take;
        }
        0
    }

    /// CORRECT: a guard read, a value-only call and an index read, round a loop. `buf_len`
    /// escapes (`touch`) only after the loop, on no path back to `mix`.
    pub fn mark_rounds(&mut self, rounds: usize) -> usize {
        let mut acc = 0;
        for _ in 0..rounds {
            if self.buf_len < BLOCK_LEN {
                acc = mix(acc);
                self.buf[self.buf_len] = 1;
            }
        }
        touch(&mut self.buf_len);
        acc
    }

    /// WRONG: the channel opened AFTER the value-only call in the text, reaching it round the
    /// loop. Round 1 parks `&mut self.buf_len`; round 2's `poke` sets it to 64 after the guard:
    /// `buf_len = 10`, two rounds, panics at `buf[64]`.
    pub fn mark_rounds_stashed(&mut self, rounds: usize) -> usize {
        let mut acc = 0;
        for _ in 0..rounds {
            if self.buf_len < BLOCK_LEN {
                acc = poke(acc);
                self.buf[self.buf_len] = 1;
            }
            stash(&mut self.buf_len);
        }
        acc
    }
}

// The escape reach of ESCAPE-HAVOC-FLOW-1 on the shapes its adversarial review found load-bearing
// (records digest-update-topup-review2). Each WRONG program below panics natively in a DEFINED
// execution, debug and release alike. Its panicking row stays FAILED only because an escape site
// of `self` reaches the value-only `poke` on some CFG path. With reach ignored, the join, the
// recursion and the sibling field PROVE; with reach taken in text order, the two loops PROVE.

impl Acc {
    /// WRONG: the escape on one arm of an `if`, joined before the value-only call. `flag`,
    /// `buf_len = 10`: `poke` sets `buf_len = 64` after the guard, and `buf[64]` panics.
    pub fn reach_join_if(&mut self, flag: bool, x: usize) -> usize {
        if flag {
            stash(&mut self.buf_len);
        }
        if self.buf_len < BLOCK_LEN {
            let a = poke(x);
            self.buf[self.buf_len] = 1;
            return a;
        }
        0
    }

    /// WRONG: a `loop` whose `break` sits between the use and the escape. Round 1 parks
    /// `&mut self.buf_len`; round 2's `poke` writes 64 after the guard. `buf_len = 10`,
    /// `rounds = 1`: `buf[64]` panics.
    pub fn reach_loop_break(&mut self, rounds: usize) -> usize {
        let mut i = 0;
        loop {
            if self.buf_len < BLOCK_LEN {
                let a = poke(i);
                self.buf[self.buf_len] = a as u8;
            }
            if i >= rounds {
                break;
            }
            stash(&mut self.buf_len);
            i += 1;
        }
        i
    }

    /// WRONG: the escape in an inner loop reaches the outer loop's next round. `buf_len = 10`,
    /// `outer = 2`, `inner = 1`: `buf[64]` panics in round 2.
    pub fn reach_nested_loop(&mut self, outer: usize, inner: usize) -> usize {
        let mut acc = 0;
        for _ in 0..outer {
            if self.buf_len < BLOCK_LEN {
                acc = poke(acc);
                self.buf[self.buf_len] = 1;
            }
            for _ in 0..inner {
                stash(&mut self.buf_len);
            }
        }
        acc
    }

    /// WRONG: recursion. The inner invocation parks a pointer derived from the outer `self`
    /// (through the recursive call's `&mut *self`, an escape site before `poke`). The outer's
    /// `poke`, after the recursive call returns, writes through it: a CHILD write of the outer's
    /// own protected `self`, so the execution is defined. `buf_len = 10`, `n = 1`: `buf[64]`
    /// panics in the outer frame.
    pub fn reach_rec_inner_frame(&mut self, n: usize) -> usize {
        if n > 0 {
            self.reach_rec_inner_frame(n - 1);
        }
        if self.buf_len < BLOCK_LEN {
            let a = poke(n);
            self.buf[self.buf_len] = 1;
            if n == 0 {
                stash(&mut self.buf_len);
            }
            return a;
        }
        0
    }
}

/// `Acc` with a fixed layout: `buf_len` sits right after `buf`.
#[repr(C)]
pub struct AccC {
    pub buf: [u8; BLOCK_LEN],
    pub buf_len: usize,
    pub len: u64,
}

/// A raw child of a `&mut [u8; 64]` parked by [`stash_buf`].
static STASH_BUF: core::sync::atomic::AtomicPtr<u8> =
    core::sync::atomic::AtomicPtr::new(core::ptr::null_mut());

/// Keeps a raw child of `b` past the call.
#[inline(never)]
pub fn stash_buf(b: &mut [u8; BLOCK_LEN]) {
    STASH_BUF.store(b.as_mut_ptr(), core::sync::atomic::Ordering::Relaxed);
}

/// Takes and returns a value; writes `BLOCK_LEN` into the `usize` right after a parked
/// `[u8; 64]`, if any.
#[inline(never)]
pub fn poke_past_buf(n: usize) -> usize {
    let p = STASH_BUF.load(core::sync::atomic::Ordering::Relaxed);
    if !p.is_null() {
        unsafe { *(p.add(BLOCK_LEN) as *mut usize) = BLOCK_LEN };
    }
    n
}

impl AccC {
    /// WRONG: the SIBLING field `&mut self.buf` is parked, and `poke_past_buf` writes `buf_len`
    /// through it. Defined under Tree Borrows (a pointer derived from `&mut self.buf` may reach
    /// the rest of the allocation, and the write is a child write of the protected `self`), UB
    /// under Stacked Borrows. A fact of only one model is no premise, so the row must stay
    /// FAILED. `buf_len = 10`: `buf[64]` panics.
    pub fn reach_sibling_field(&mut self, x: usize) -> usize {
        stash_buf(&mut self.buf);
        if self.buf_len < BLOCK_LEN {
            let a = poke_past_buf(x);
            self.buf[self.buf_len] = 1;
            return a;
        }
        0
    }
}

// PROVED BY PREMISE: the boundary of rule (b) (docs/TCB.md, "Calls whose arguments grant no
// write"). Each program below panics natively in a DEBUG build, and each panic needs a pointer
// that ANOTHER invocation created (an earlier call, the outer frame of a recursion, or the caller
// before the entry) to write `*self` while this invocation's protected `self` is live. That
// write is UB. Under Stacked Borrows, the fresh `&mut` the caller or outer frame retags for this
// invocation pops the parked pointer's item. Under Tree Borrows, it is a foreign write to a
// location of this invocation's protected `self` that the guard read initialized. Rule (b) rests
// on that protector, and rustc relies on the same fact: in a RELEASE build, `noalias` lets LLVM
// fold the reload, and none of these programs panics. The rows are PROVED: on main only
// `premise_before_entry`'s, since main's rule (b) asked for no escape site anywhere; with
// ESCAPE-HAVOC-FLOW-1, all four.

impl Acc {
    /// PROVED BY PREMISE: correct within one invocation (the escape comes after the use). A
    /// SECOND call's `poke` writes 64 through the FIRST call's stash. `buf_len = 10`, two calls:
    /// `buf[64]` panics in a debug build.
    pub fn premise_next_call(&mut self, x: usize) -> usize {
        if self.buf_len < BLOCK_LEN {
            let a = poke(x);
            self.buf[self.buf_len] = 1;
            stash(&mut self.buf_len);
            return a;
        }
        0
    }

    /// PROVED BY PREMISE: the escape on an early-return path, which reaches no call of this
    /// invocation. A later call's `poke` writes through it. `buf_len = 10`, `park` then
    /// `!park`: `buf[64]` panics in a debug build.
    pub fn premise_early_return(&mut self, park: bool, x: usize) -> usize {
        if park {
            stash(&mut self.buf_len);
            return 0;
        }
        if self.buf_len < BLOCK_LEN {
            let a = poke(x);
            self.buf[self.buf_len] = 1;
            return a;
        }
        0
    }

    /// PROVED BY PREMISE: the outer frame parks, then recurses. The inner frame's `poke` writes
    /// through the outer's stash, a SIBLING of the inner's protected `self`. `buf_len = 10`,
    /// `n = 1`: `buf[64]` panics in the inner frame in a debug build.
    pub fn premise_outer_frame(&mut self, n: usize, x: usize) -> usize {
        if n == 1 {
            stash(&mut self.buf_len);
            return self.premise_outer_frame(0, x);
        }
        if self.buf_len < BLOCK_LEN {
            let a = poke(x);
            self.buf[self.buf_len] = 1;
            return a;
        }
        0
    }

    /// PROVED BY PREMISE, on main as well: `self` has no escape site at all. The CALLER parks
    /// `&mut acc.buf_len` before the call, and `poke` writes through it. `buf_len = 10`:
    /// `buf[64]` panics in a debug build.
    pub fn premise_before_entry(&mut self, x: usize) -> usize {
        if self.buf_len < BLOCK_LEN {
            let a = poke(x);
            self.buf[self.buf_len] = 1;
            return a;
        }
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn acc(buf_len: usize) -> Acc {
        Acc { state: [0; 8], buf: [0; BLOCK_LEN], buf_len, len: 0 }
    }

    fn panics(f: impl FnOnce() + std::panic::UnwindSafe) -> String {
        let e = std::panic::catch_unwind(f).expect_err("must panic");
        e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default()
    }

    #[test]
    fn correct_rounds_never_panic() {
        for buf_len in 0..=BLOCK_LEN + 3 {
            let mut a = acc(buf_len);
            a.mark_rounds(5);
        }
    }

    #[test]
    fn correct_never_panics() {
        for buf_len in 0..=BLOCK_LEN {
            for n in [0usize, 1, 2, 62, 63, 64, 65, 200] {
                let data = vec![7u8; n];
                let mut a = acc(buf_len);
                let take = a.top_up(&data);
                assert!(a.buf_len <= BLOCK_LEN);
                assert!(take <= n);
            }
        }
    }

    #[test]
    fn wrong_twins_really_panic() {
        let m = panics(|| { acc(1).top_up_room_past_end(&[7u8; 64]); });
        println!("top_up_room_past_end: {m}");
        assert!(m.contains("out of range"), "{m}");
        let m = panics(|| { acc(1).top_up_max(&[7u8; 100]); });
        println!("top_up_max: {m}");
        assert!(m.contains("out of range"), "{m}");
        let m = panics(|| { acc(1).top_up_max(&[]); });
        println!("top_up_max (empty data): {m}");
        assert!(m.contains("range end index 63 out of range for slice of length 0"), "{m}");
        let m = panics(|| { acc(1).top_up_callee_writes(&[7u8; 1]); });
        println!("top_up_callee_writes: {m}");
        assert!(m.contains("out of range") || m.contains("starts at"), "{m}");
        let m = panics(|| { acc(1).top_up_wrapping_take(&[]); });
        println!("top_up_wrapping_take: {m}");
        assert!(m.contains("overflow"), "{m}");
        let m = panics(|| { acc(1).top_up_stashed(&[7u8; 1]); });
        println!("top_up_stashed: {m}");
        assert!(m.contains("out of range") || m.contains("starts at"), "{m}");
        STASH.store(core::ptr::null_mut(), core::sync::atomic::Ordering::Relaxed);
        let m = panics(|| { acc(10).mark_rounds_stashed(2); });
        println!("mark_rounds_stashed: {m}");
        assert!(m.contains("index out of bounds"), "{m}");
        STASH.store(core::ptr::null_mut(), core::sync::atomic::Ordering::Relaxed);
    }

    fn reset() {
        STASH.store(core::ptr::null_mut(), core::sync::atomic::Ordering::Relaxed);
        STASH_BUF.store(core::ptr::null_mut(), core::sync::atomic::Ordering::Relaxed);
    }

    /// Runs `f` with both stashes empty; prints `PANIC <name> <line>:<col> <message>` or
    /// `NOPANIC <name>`, and returns the panic's `line:col` and message.
    fn observe(name: &str, f: impl FnOnce() + std::panic::UnwindSafe) -> Option<(String, String)> {
        reset();
        let at = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let hook_at = at.clone();
        std::panic::set_hook(Box::new(move |info| {
            if let Some(l) = info.location() {
                *hook_at.lock().unwrap() = format!("{}:{}", l.line(), l.column());
            }
        }));
        let r = std::panic::catch_unwind(f);
        let _ = std::panic::take_hook();
        reset();
        match r {
            Ok(()) => {
                println!("NOPANIC {name}");
                None
            }
            Err(e) => {
                let m = e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default();
                let at = at.lock().unwrap().clone();
                println!("PANIC {name} {at} {m}");
                Some((at, m))
            }
        }
    }

    /// A reach twin panics, in a defined execution, at `buf[64]` on its pinned line.
    fn reach_panics(name: &str, line: u32, f: impl FnOnce() + std::panic::UnwindSafe) {
        let (at, m) = observe(name, f).unwrap_or_else(|| panic!("{name} must panic"));
        assert!(at.starts_with(&format!("{line}:")), "{name}: panicked at {at}, not line {line}");
        assert!(m.contains("the len is 64 but the index is 64"), "{name}: {m}");
    }

    #[test]
    fn reach_join_if_really_panics() {
        reach_panics("reach_join_if", 174, || { acc(10).reach_join_if(true, 0); });
    }

    #[test]
    fn reach_loop_break_really_panics() {
        reach_panics("reach_loop_break", 188, || { acc(10).reach_loop_break(1); });
    }

    #[test]
    fn reach_nested_loop_really_panics() {
        reach_panics("reach_nested_loop", 206, || { acc(10).reach_nested_loop(2, 1); });
    }

    #[test]
    fn reach_rec_inner_frame_really_panics() {
        reach_panics("reach_rec_inner_frame", 226, || { acc(10).reach_rec_inner_frame(1); });
    }

    #[test]
    fn reach_sibling_field_really_panics() {
        reach_panics("reach_sibling_field", 275, || {
            AccC { buf: [0; BLOCK_LEN], buf_len: 10, len: 0 }.reach_sibling_field(0);
        });
    }

    // The PROVED-BY-PREMISE programs: what a native build does with an execution that is UB.
    // Observed, never asserted.

    #[test]
    fn premise_next_call_observed() {
        observe("premise_next_call", || {
            let mut a = acc(10);
            a.premise_next_call(0);
            a.premise_next_call(0);
        });
    }

    #[test]
    fn premise_early_return_observed() {
        observe("premise_early_return", || {
            let mut a = acc(10);
            a.premise_early_return(true, 0);
            a.premise_early_return(false, 0);
        });
    }

    #[test]
    fn premise_outer_frame_observed() {
        observe("premise_outer_frame", || { acc(10).premise_outer_frame(1, 0); });
    }

    #[test]
    fn premise_before_entry_observed() {
        observe("premise_before_entry", || {
            let mut a = acc(10);
            stash(&mut a.buf_len);
            a.premise_before_entry(0);
        });
    }
}
