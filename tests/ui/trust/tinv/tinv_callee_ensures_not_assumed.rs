//@ revisions: lie control
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib -Ztrust-tinv
//@ rustc-env:TRUST_TINV_NOTES=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ [lie] forbid-output: certified: #
//@ [lie] forbid-output: proved UNDER this crate's certified type invariant
//! TINV step 10.6 "measure" (plan `tinv_plan_step10`, KNOWN_HAZARDS 10.4 item (4)): does a
//! TINV certificate row assume a callee's AUTHORED `ensures`? If it did, the certificate
//! would rest on a clause the main pass verifies only LATER, and a false clause would
//! certify a false invariant. Here `lie` claims `result <= b.len()` and returns `k`
//! (its own postcondition row fails in the main pass), and `set` writes `self.i = lie(..)`:
//! the only thing that could prove `set`'s Return row for `i <= len(b)` is `lie`'s false
//! `ensures`. The TINV walk runs under a FRESH `VcgenContext` with no callee summaries
//! (`generate/tinv_rows.rs`, `tinv_check_rows_recorded`: `VcgenContext::for_function` and
//! `generate_v2_safety_vcs_impl_with_origins_checked(.., None)`), so the row stays refuted
//! and nothing about `P` is certified or assumed anywhere in the crate.
//!
//! MEASURED 2026-10-10 (stage 1 of `tinv/step10-install`): `lie` revision — no type
//! invariant of `P` is certified; `i <= len(b)` (#2) is dropped Refuted at `set`'s return.
//! `control` revision — `set` guards the write itself (`if k <= self.b.len()`), with no
//! callee contract involved, and the same conjunct certifies: the shape is certifiable, so
//! the `lie` drop is the missing `ensures`, not an unrelated gap (and `rest` consumes it:
//! the step-10.7 consumer list names it).
#![forbid(unsafe_code)]

struct P<'a> {
    //[lie]~^ NOTE TINV: no type invariant of `tinv_callee_ensures_not_assumed::P` is certified
    //[lie]~| NOTE conjunct #2 dropped (Refuted) at return
    //[control]~^^^ NOTE certified: #2 `i <= len(b)`
    //[control]~^^^^ NOTE consumed by 1 function(s)
    b: &'a [u8],
    i: usize,
}

fn lie(b: &[u8], k: usize) -> usize
    ensures result <= b.len()
{
    let _ = b;
    k
}

impl<'a> P<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    #[cfg(lie)]
    fn set(&mut self, k: usize) {
        self.i = lie(self.b, k);
    }

    #[cfg(control)]
    fn set(&mut self, k: usize) {
        let _ = lie(self.b, k);
        if k <= self.b.len() {
            self.i = k;
        }
    }

    fn rest(&self) -> &'a [u8] {
        &self.b[self.i..]
    }
}

pub fn run(b: &[u8], k: usize) -> usize {
    let mut p = P { b, i: 0 };
    let _ = p.peek();
    p.set(k);
    p.rest().len()
}
