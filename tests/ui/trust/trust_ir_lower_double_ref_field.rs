//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-ADB): the wave-DPE "DB-L" slot — `&r` where the LOCAL `r`
//! already holds a ledgered pointer — is a NAMED-LOCAL snapshot, and joins
//! `local_snapshot_ptrs` beside `borrow_ptrs`.
//!
//! That ledger's charter is exactly this distinction: the snapshot pointers
//! minted by the LOCAL-borrow arm for a NAMED local, as opposed to the rvalue
//! arm's snapshot of a TEMPORARY. Borrowck cannot let an aggregate carrying a
//! named-local snapshot leave the frame, which is the property
//! `borrow_ptr_field_admissible`'s named-frame half reads. The wave-DB RVALUE
//! twin deliberately does NOT move — that is the promotable-temporary class
//! (the measured `tests/ui/nll/issue-52992.rs` divergence).

pub struct Test<'a>(pub &'a &'a [i32; 3]);

pub fn build() -> i32 {
    let slice: &[i32; 3] = &[1, 2, 3];
    let x = Test(&slice);
    let Test(inner) = x;
    inner[0] + inner[2]
}

fn main() {
    assert_eq!(build(), 4);
}
