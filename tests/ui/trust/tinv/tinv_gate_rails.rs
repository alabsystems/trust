//@ revisions: control pub_field no_forbid cell generic raw_ptr stash coroutine off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ [control] compile-flags: -Ztrust-tinv
//@ [pub_field] compile-flags: -Ztrust-tinv
//@ [no_forbid] compile-flags: -Ztrust-tinv
//@ [cell] compile-flags: -Ztrust-tinv
//@ [generic] compile-flags: -Ztrust-tinv
//@ [raw_ptr] compile-flags: -Ztrust-tinv
//@ [stash] compile-flags: -Ztrust-tinv
//@ [coroutine] compile-flags: -Ztrust-tinv
//@ rustc-env:TRUST_TINV_NOTES=1
//@ [off] rustc-env:TRUST_TINV=1
//@ [off] forbid-output: TINV:
//@ [pub_field] forbid-output: certified:
//@ [no_forbid] forbid-output: certified:
//@ [cell] forbid-output: certified:
//@ [generic] forbid-output: certified:
//@ [raw_ptr] forbid-output: certified:
//@ [stash] forbid-output: certified:
//@ [coroutine] forbid-output: certified:
//@ [control] forbid-output: withheld at G
//@ [control] forbid-output: withheld by the escape census
//@ [raw_ptr] forbid-output: withheld at G
//@ [stash] forbid-output: withheld at G
//@ [coroutine] forbid-output: withheld at G
//! TINV steps 5 and 6b (design §3 G1, G2a, G4, G12; §2 P2 census, D2, D4): each
//! revision breaks ONE premise of `S`'s invariant `i <= len(b)` and must be
//! withheld, with a note naming the gate. `control` is the same type with no
//! breach: it must not be withheld by any gate or by the census (whether its
//! conjuncts then certify is the mint's business; measured 2026-10-06 on real MIR,
//! none does yet — see `tinv_p1_json_parser`).
//! `off` (no `-Ztrust-tinv`) runs nothing and reports nothing, although it sets the
//! retired `TRUST_TINV=1` environment switch (step 10.0: only the tracked option enables it).
#![cfg_attr(not(no_forbid), forbid(unsafe_code))]

#[cfg(not(any(pub_field, cell, generic)))]
struct S {
    //[no_forbid]~^ NOTE withheld at G2a
    //[raw_ptr]~^^ NOTE a raw pointer is taken to storage that holds it
    //[stash]~^^^ NOTE TINV D2 field-borrow provenance
    //[coroutine]~^^^^ NOTE TINV D4
    //[control]~^^^^^ NOTE candidate conjuncts (untrusted)
    b: Vec<u8>,
    i: usize,
}

#[cfg(pub_field)]
struct S {
    //[pub_field]~^ NOTE withheld at G1: field `i` is `pub`
    b: Vec<u8>,
    pub i: usize,
}

#[cfg(cell)]
struct S {
    //[cell]~^ NOTE withheld at G4
    b: Vec<u8>,
    i: usize,
    hits: core::cell::Cell<u32>,
}

#[cfg(generic)]
struct S<T> {
    //[generic]~^ NOTE withheld at G12
    b: Vec<T>,
    i: usize,
}

#[cfg(not(any(cell, generic)))]
impl S {
    fn new(b: Vec<u8>) -> S {
        S { b, i: 0 }
    }

    fn step(&mut self) {
        if self.i < self.b.len() {
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
}

#[cfg(cell)]
impl S {
    fn new(b: Vec<u8>) -> S {
        S { b, i: 0, hits: core::cell::Cell::new(0) }
    }

    fn step(&mut self) {
        self.hits.set(self.hits.get().wrapping_add(1));
        if self.i < self.b.len() {
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
}

#[cfg(generic)]
impl<T: Copy> S<T> {
    fn new(b: Vec<T>) -> S<T> {
        S { b, i: 0 }
    }

    fn step(&mut self) {
        if self.i < self.b.len() {
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<T> {
        self.b.get(self.i).copied()
    }
}

// A raw pointer to `i` is taken in safe code; writing through it (in another crate,
// or later with `unsafe`) breaks `i <= len(b)` invisibly.
#[cfg(raw_ptr)]
impl S {
    pub fn leak(&mut self) -> *mut usize {
        &raw mut self.i
    }
}

// The `&mut` to `i` outlives the call: `Vec::push` stores it (the alias arrives as
// the `T` value, not at a `&'r mut` parameter whose region stays local).
#[cfg(stash)]
impl S {
    fn stash<'a>(&'a mut self, slots: &mut Vec<&'a mut usize>) {
        slots.push(&mut self.i);
    }
}

// An async body writes `i` across a suspension point: the window is open while the
// future is parked.
#[cfg(coroutine)]
impl S {
    async fn park(&mut self) {
        self.i = usize::MAX;
        core::future::ready(()).await;
        self.i = 0;
    }
}

#[cfg(not(generic))]
pub fn drive(b: Vec<u8>) -> Option<u8> {
    let mut s = S::new(b);
    s.step();
    s.peek()
}

#[cfg(generic)]
pub fn drive(b: Vec<u8>) -> Option<u8> {
    let mut s = S::new(b);
    s.step();
    s.peek()
}
