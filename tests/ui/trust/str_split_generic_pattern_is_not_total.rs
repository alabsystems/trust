//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! A str iterator built from a pattern that carries user code is not a total
//! receiver, whatever type the extractor gives that code (ITER-RECV-1).
//!
//! `ty_is_str_iterator_receiver` admitted a `Split`-family receiver unless its
//! pattern state carried a closure, fn item, fn pointer, coroutine or non-std ADT.
//! Both of its walks ended in `_ => false`, so a generic `&mut F` (the extractor
//! renders a type parameter `Ty::Unsupported`) passed as "no closure here". The
//! `into_iter`/`next` calls of `count_pieces` were summarized as total, the loop
//! read `unreach proved` and nothing else, and the function was Clean-kernel
//! certified. Driven by `s.split(&mut |c| table[c as usize])` with a 4-entry
//! table, the certified function panics `index out of bounds: the len is 4 but the
//! index is 97` (the witness, `str_split_generic_pattern_is_not_total_run.rs`).
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, 2026-10-04; each
//! revision's flags with `--emit=metadata`): both revisions built exit 0 with no
//! Trust diagnostic; `count_pieces` read `unreach proved` only. The annotations
//! below did not fire.
//!
//! AFTER (predicted, then measured): the gate is positive
//! (`str_iterator_state_is_benign`): every value the receiver carries must be a
//! scalar, `str` bytes, or a std-anchored ADT of such, so the generic `F` fails it
//! and the calls fall through to the absent-callee path. The annotations are what
//! the BEFORE compiler prints for a twin of this file whose `count_pieces` takes
//! `Split<'a, fn(char) -> bool>` (a fn pointer, which the old gate already
//! refused): default `1 runtime-checked` (`[trust-absent-callee-assumption]` on
//! `SplitInternal::<'_, fn(char) -> bool>::next`), a WARN and an ERROR; certify two
//! ERRORs. A second twin that keeps the generic `F` and calls `it.nth(0)` (which
//! no total arm recognizes) printed the same two diagnostics at the same levels.
//! Counts are left out of the annotations: the lie may charge `into_iter` too.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `count_pieces` gains a runtime-checked
//! row; the std controls still read `unreach proved` only.
//!
//! The controls carry no annotation and read `unreach proved` in both revisions,
//! BEFORE and in both twins: the std `char` and `&str` patterns and `Chars`, whose
//! searcher state is all std ADTs over scalars and `&str` bytes.

pub fn count_pieces<'a, 'b, F: FnMut(char) -> bool>(it: core::str::Split<'a, &'b mut F>) -> usize {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `str_split_generic_pattern_is_not_total::count_pieces`
    //[default]~^^ ERROR Trust strict verification failed for `str_split_generic_pattern_is_not_total::count_pieces`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `str_split_generic_pattern_is_not_total::count_pieces`
    //[certify]~^^^^ ERROR Trust strict verification failed for `str_split_generic_pattern_is_not_total::count_pieces`
    let mut n = 0usize;
    for _p in it {
        n = n.wrapping_add(1);
    }
    n
}

pub fn count_char_pieces<'a>(it: core::str::Split<'a, char>) -> usize {
    let mut n = 0usize;
    for _p in it {
        n = n.wrapping_add(1);
    }
    n
}

pub fn count_str_pieces<'a, 'b>(it: core::str::Split<'a, &'b str>) -> usize {
    let mut n = 0usize;
    for _p in it {
        n = n.wrapping_add(1);
    }
    n
}

pub fn count_chars(it: core::str::Chars<'_>) -> usize {
    let mut n = 0usize;
    for _c in it {
        n = n.wrapping_add(1);
    }
    n
}
