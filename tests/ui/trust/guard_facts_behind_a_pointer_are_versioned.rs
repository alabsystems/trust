//@ needs-trust-verify
//@ edition: 2021
//@ revisions: ascii_mut_receiver ascii_handout_elsewhere ascii_iter_mut_then_write
//@ revisions: ascii_shared_reader_between range_read_only range_sibling_field_handed_out
//@ revisions: ascii_reloaded_pointer ascii_field_of_mut ascii_holder_method
//@ revisions: range_reloaded_pointer range_field_of_mut range_wrapper_method
//@ revisions: range_shared_reborrow range_bound_itself_handed_out
//@ revisions: range_store_outside_loop range_exit_path_uses_the_bound
//@ revisions: over_refusal_range_handout_outside_loop over_refusal_range_handout_on_exit_path
//@ revisions: ascii_iter_mut_payload_handed_out ascii_option_payload_handed_out range_bound_in_a_holder
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[ascii_mut_receiver] check-pass
//@[ascii_handout_elsewhere] check-fail
//@[ascii_iter_mut_then_write] check-pass
//@[ascii_shared_reader_between] check-pass
//@[range_read_only] check-pass
//@[range_sibling_field_handed_out] check-pass
//@[ascii_reloaded_pointer] check-fail
//@[ascii_field_of_mut] check-fail
//@[ascii_holder_method] check-fail
//@[range_reloaded_pointer] check-fail
//@[range_field_of_mut] check-fail
//@[range_wrapper_method] check-fail
//@[range_shared_reborrow] check-fail
//@[range_bound_itself_handed_out] check-fail
//@[range_store_outside_loop] check-pass
//@[over_refusal_range_handout_outside_loop] check-fail
//@[over_refusal_range_handout_on_exit_path] check-fail
//@[range_exit_path_uses_the_bound] check-fail
//@[ascii_iter_mut_payload_handed_out] check-fail
//@[ascii_option_payload_handed_out] check-fail
//@[range_bound_in_a_holder] check-fail
//! **A guard fact about a value behind a pointer is a claim about that value where
//! the guard read it (Trust, 2026-09-29).**
//!
//! Two facts are read through a pointer: the TRUE-set of an ascii predicate
//! (`x.is_ascii_digit()` over `x: &mut u8`), and a range bound copied out of a
//! struct (`for i in 0..s.n` over `s: &mut S`). Both used to be stated on the BARE
//! name of the pointee, which the version rename binds to whatever it holds at each
//! USE. A whole-function scan then had to rule out every write in between, and the
//! escape audit measured seven shapes it missed: a pointer reloaded from memory at
//! each use (`x: &mut &mut u8`, a `&mut` field, a holder's `self.cur` or
//! `self.inner`) is a new temp at each read, and a shared reborrow `&*s` is not
//! written through while `s` is. Each was proved and panics; the holder shape was
//! kernel-certified, and its verified build elided the overflow check and returned
//! 240. The scan also refused correct programs whose pointer was handed out
//! anywhere else in the function.
//!
//! Both facts now ask about the MEMORY, not about the local a read names.
//! `local_defs::deref_read_is_never_written` follows every pointer derived from the
//! read's root reference (copies, reloads, shared and mutable reborrows) and answers
//! yes only when no store overlaps the place and no pointer that can reach it is
//! handed out; a shared reference to a place with no `UnsafeCell` on its path, and a
//! reborrow of a DISJOINT place (`&mut s.buf` beside `s.n`), write nothing. When it
//! answers yes the fact is stated bare and holds everywhere. Otherwise the ascii set
//! is versioned just after the predicate call returns (`guards::ascii_predicate_bound`),
//! so a use connects to it only when the version fabric sees no write in between, and
//! the range bound is withheld.
//!
//! * `ascii_mut_receiver` … `range_sibling_field_handed_out`: POSITIVE.
//! * `ascii_reloaded_pointer` … `range_bound_itself_handed_out`: NEGATIVE — each
//!   changes the tested value between the test and the use, and panics.
//! * `range_store_outside_loop`: POSITIVE. A range bound needs its place unSTORED only
//!   on the paths from the copy the `Range` took to the blocks that name the loop
//!   variable (`iterator_yield::end_bound_unwritten_until_used`), so a store to it
//!   before the loop or after it keeps the bound.
//! * `range_exit_path_uses_the_bound`: NEGATIVE. The hand-out is on a path that leaves
//!   the loop, but that path still names `i` after it, and `s.n - i` underflows there.
//! * `over_refusal_*`: CORRECT programs refused, pinned so a change is seen. A
//!   HAND-OUT of the `&mut` counts wherever it is: the callee can turn it into a raw
//!   pointer that outlives the borrow, and a later call handed nothing can write
//!   through it (`let p = raw_of(s); for i in 0..s.n { poke(p); … }` was proved and
//!   panics when hand-outs were judged by region). Telling such a callee from `shrink`
//!   needs a summary of what the callee exports.
//! * `ascii_iter_mut_payload_handed_out`, `ascii_option_payload_handed_out`,
//!   `range_bound_in_a_holder`: NEGATIVE, found by the precondition audit of the
//!   first version of this fix. A pointer moved out of an `Option` or an iterator
//!   result is named through that aggregate, so the fabric versions neither the test
//!   nor a later hand-out of it; the ascii set stayed bare and the stability gate
//!   asked only about the pointer local (`letter_counts` uppercased the byte, then
//!   subtracted `b'a'`, and its verified build returned 7). A bound read through a
//!   reference copied out of a local tuple is named at the parameter, while the
//!   pointer-family walk stopped at the copy and never saw `shrink(s)`.

#[cfg(any(
    ascii_handout_elsewhere,
    ascii_reloaded_pointer,
    ascii_field_of_mut,
    ascii_option_payload_handed_out
))]
fn zero(p: &mut u8) {
    *p = 0;
}

#[cfg(any(
    range_read_only,
    range_store_outside_loop,
    over_refusal_range_handout_outside_loop,
    over_refusal_range_handout_on_exit_path,
    range_exit_path_uses_the_bound,
    range_reloaded_pointer,
    range_field_of_mut,
    range_shared_reborrow,
    range_bound_in_a_holder
))]
pub struct S {
    pub n: usize,
}

#[cfg(any(
    over_refusal_range_handout_outside_loop,
    over_refusal_range_handout_on_exit_path,
    range_exit_path_uses_the_bound,
    range_reloaded_pointer,
    range_field_of_mut,
    range_shared_reborrow,
    range_bound_in_a_holder
))]
fn shrink(s: &mut S) {
    s.n = 0;
}

#[cfg(ascii_mut_receiver)]
pub fn digit_in_place(x: &mut u8) -> u8 {
    if x.is_ascii_digit() { *x - b'0' } else { 0 }
}

#[cfg(ascii_mut_receiver)]
pub fn digits_to_values(v: &mut [u8]) {
    for x in v.iter_mut() {
        if x.is_ascii_digit() {
            *x -= b'0';
        }
    }
}

#[cfg(ascii_handout_elsewhere)]
pub fn handout_before_test(x: &mut u8) -> u8 {
    zero(x);
    let d = x.is_ascii_digit();
    if d { *x - b'0' } else { 0 }
}

#[cfg(ascii_handout_elsewhere)]
pub fn handout_after_use(x: &mut u8) -> u8 {
    //[ascii_handout_elsewhere]~^ ERROR Trust strict verification failed for `guard_facts_behind_a_pointer_are_versioned::handout_after_use`
    // CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
    // `*x - b'0'` under `x.is_ascii_digit()`, nothing written between, is refuted at `*x = 0`:
    // the guard fact on `*x` does not reach the read when `x` is handed out ANYWHERE in the
    // body (here after the read, or on the other branch).
    // Fail-closed: refused, never proved. Flip back to `check-pass` when it returns.
    let d = x.is_ascii_digit();
    let r = if d { *x - b'0' } else { 0 };
    zero(x);
    r
}

#[cfg(ascii_handout_elsewhere)]
pub fn handout_on_other_branch(x: &mut u8) -> u8 {
    //[ascii_handout_elsewhere]~^ ERROR Trust strict verification failed for `guard_facts_behind_a_pointer_are_versioned::handout_on_other_branch`
    // See `handout_after_use` (CAPABILITY LOSS, re-pinned 2026-10-15).
    if x.is_ascii_digit() {
        *x - b'0'
    } else {
        zero(x);
        0
    }
}

#[cfg(ascii_iter_mut_then_write)]
fn normalize(p: &mut u8) {
    if *p == b'9' {
        *p = b'0';
    }
}

#[cfg(ascii_iter_mut_then_write)]
pub fn sum_then_normalize(v: &mut [u8]) -> u32 {
    let mut s = 0u32;
    for x in v.iter_mut() {
        if x.is_ascii_digit() {
            s = s.wrapping_add((*x - b'0') as u32);
        }
        normalize(x);
    }
    s
}

#[cfg(ascii_shared_reader_between)]
fn show(x: &u8) -> u8 {
    *x
}

#[cfg(ascii_shared_reader_between)]
pub fn reader_between(x: &mut u8) -> u8 {
    let d = x.is_ascii_digit();
    let _ = show(x);
    if d { *x - b'0' } else { 0 }
}

#[cfg(range_read_only)]
pub fn count_down(s: &mut S) -> usize {
    let mut t = 0usize;
    for i in 0..s.n {
        t ^= s.n - i - 1;
    }
    t
}

#[cfg(range_read_only)]
impl S {
    pub fn count_down_self(&mut self) -> usize {
        let mut t = 0usize;
        for i in 0..self.n {
            t ^= self.n - i - 1;
        }
        t
    }
}

#[cfg(any(range_sibling_field_handed_out, range_bound_itself_handed_out))]
pub struct B {
    pub n: usize,
    pub buf: Vec<u8>,
}

#[cfg(range_sibling_field_handed_out)]
pub fn push_while_counting(b: &mut B) -> usize {
    let mut t = 0usize;
    for i in 0..b.n {
        b.buf.push(1);
        t ^= b.n - i - 1;
    }
    t
}

#[cfg(range_bound_itself_handed_out)]
fn clear(n: &mut usize) {
    *n = 0;
}

#[cfg(range_bound_itself_handed_out)]
pub fn clear_while_counting(b: &mut B) -> usize {
    //[range_bound_itself_handed_out]~^ ERROR Trust
    let mut t = 0usize;
    for i in 0..b.n {
        clear(&mut b.n);
        t ^= b.n - i - 1;
    }
    t
}

#[cfg(range_store_outside_loop)]
pub fn store_then_count_down(s: &mut S) -> usize {
    s.n = 5;
    let mut t = 0usize;
    for i in 0..s.n {
        t ^= s.n - i - 1;
    }
    s.n = 0;
    t
}

#[cfg(over_refusal_range_handout_outside_loop)]
pub fn shrink_then_count_down(s: &mut S) -> usize {
    //[over_refusal_range_handout_outside_loop]~^ ERROR Trust
    shrink(s);
    let mut t = 0usize;
    for i in 0..s.n {
        t ^= s.n - i - 1;
    }
    t
}

#[cfg(over_refusal_range_handout_outside_loop)]
pub fn count_down_then_shrink(s: &mut S) -> usize {
    let mut t = 0usize;
    for i in 0..s.n {
        t ^= s.n - i - 1;
    }
    shrink(s);
    t
}

#[cfg(over_refusal_range_handout_outside_loop)]
impl S {
    fn reset(&mut self) {
        self.n = 0;
    }

    pub fn drain(&mut self) -> usize {
        let mut t = 0usize;
        for i in 0..self.n {
            t ^= self.n - i - 1;
        }
        self.reset();
        t
    }
}

#[cfg(over_refusal_range_handout_on_exit_path)]
pub fn early_exit(s: &mut S) -> usize {
    //[over_refusal_range_handout_on_exit_path]~^ ERROR Trust
    let mut t = 0usize;
    for i in 0..s.n {
        if i == 1000 {
            shrink(s);
            return 0;
        }
        t ^= s.n - i - 1;
    }
    t
}

#[cfg(ascii_reloaded_pointer)]
pub fn reloaded(x: &mut &mut u8) -> u8 {
    //[ascii_reloaded_pointer]~^ ERROR Trust
    let d = x.is_ascii_digit();
    zero(*x);
    if d { **x - b'0' } else { 0 }
}

#[cfg(ascii_field_of_mut)]
pub struct H<'a> {
    pub p: &'a mut u8,
}

#[cfg(ascii_field_of_mut)]
pub fn field_of_mut(h: &mut H) -> u8 {
    //[ascii_field_of_mut]~^ ERROR Trust
    let d = h.p.is_ascii_digit();
    zero(h.p);
    if d { *h.p - b'0' } else { 0 }
}

#[cfg(ascii_holder_method)]
pub struct Q<'a> {
    pub cur: &'a mut u8,
}

#[cfg(ascii_holder_method)]
impl<'a> Q<'a> {
    fn consume(&mut self) {
        *self.cur = b' ';
    }

    pub fn digit(&mut self) -> u8 {
        //[ascii_holder_method]~^ ERROR Trust
        let d = self.cur.is_ascii_digit();
        self.consume();
        if d { *self.cur - b'0' } else { 0 }
    }
}

#[cfg(range_reloaded_pointer)]
pub fn reloaded(s: &mut &mut S) -> usize {
    //[range_reloaded_pointer]~^ ERROR Trust
    let mut t = 0usize;
    for i in 0..s.n {
        shrink(*s);
        t ^= s.n - i - 1;
    }
    t
}

#[cfg(range_field_of_mut)]
pub struct H<'a> {
    pub s: &'a mut S,
}

#[cfg(range_field_of_mut)]
pub fn field_of_mut(h: &mut H) -> usize {
    //[range_field_of_mut]~^ ERROR Trust
    let mut t = 0usize;
    for i in 0..h.s.n {
        shrink(h.s);
        t ^= h.s.n - i - 1;
    }
    t
}

#[cfg(range_wrapper_method)]
pub struct Inner {
    pub n: usize,
}

#[cfg(range_wrapper_method)]
pub struct W<'a> {
    pub inner: &'a mut Inner,
}

#[cfg(range_wrapper_method)]
impl<'a> W<'a> {
    fn touch(&mut self) {
        self.inner.n = 0;
    }

    pub fn count_down(&mut self) -> usize {
        //[range_wrapper_method]~^ ERROR Trust
        let mut t = 0usize;
        for i in 0..self.inner.n {
            self.touch();
            t ^= self.inner.n - i - 1;
        }
        t
    }
}

#[cfg(range_shared_reborrow)]
pub fn shared_reborrow(s: &mut S) -> usize {
    //[range_shared_reborrow]~^ ERROR Trust
    let mut t = 0usize;
    let r: &S = &*s;
    for i in 0..r.n {
        shrink(s);
        t ^= s.n - i - 1;
    }
    t
}

#[cfg(range_exit_path_uses_the_bound)]
pub fn shrink_then_use(s: &mut S, stop: usize) -> usize {
    //[range_exit_path_uses_the_bound]~^ ERROR Trust
    let mut t = 0usize;
    for i in 0..s.n {
        if i == stop {
            shrink(s);
            return s.n - i;
        }
        t ^= i;
    }
    t
}

#[cfg(ascii_iter_mut_payload_handed_out)]
pub fn letter_counts(word: &mut [u8]) -> u32 {
    //[ascii_iter_mut_payload_handed_out]~^ ERROR Trust
    let mut mask = 0u32;
    for b in word.iter_mut() {
        if b.is_ascii_lowercase() {
            b.make_ascii_uppercase();
            let idx = *b - b'a';
            mask |= 1u32 << (idx % 32);
        }
    }
    mask
}

#[cfg(ascii_option_payload_handed_out)]
pub fn digit_of_option(o: Option<&mut u8>) -> u8 {
    //[ascii_option_payload_handed_out]~^ ERROR Trust
    if let Some(x) = o {
        let d = x.is_ascii_digit();
        zero(x);
        if d {
            return *x - b'0';
        }
    }
    0
}

#[cfg(range_bound_in_a_holder)]
pub fn bound_through_a_tuple(s: &mut S) -> usize {
    //[range_bound_in_a_holder]~^ ERROR Trust
    let mut t = 0usize;
    let pair: (&S, u8) = (&*s, 0);
    let r = pair.0;
    for i in 0..r.n {
        shrink(s);
        t ^= s.n - i - 1;
    }
    t
}
