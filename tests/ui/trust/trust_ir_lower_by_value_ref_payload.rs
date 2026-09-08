//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-RB: an explicit `ref x` payload binding on a BY-VALUE enum scrutinee.
// The scrutinee is PROMOTED once into a frame slot (Alloca + whole-value Store,
// dominating every arm), and each `ref` bind is the deref lane's interior GEP
// with the slot as its base — same six-gate chain (fat wall, param lane, thin
// binding, descriptor presence, offset, agreement). The bound pointer joins
// `borrow_ptrs` only: a slot address dies with the frame, so every return
// escape fails closed — including through a JOIN PARAM, which carries no
// ledger of its own and laundered `E::A(ref x) => x as *const i64` clean until
// the merge started marking params fed by ledgered borrow pointers
// (probe-measured on this lane's first build; both refuters pinned below in
// doc form). Shared refs only; `ref mut` keeps the catch-all refusal.

pub enum E {
    A(i64),
    B(u32),
}

pub fn both_ref(e: E) -> i64 {
    match e {
        E::A(ref x) => *x,
        E::B(ref y) => *y as i64,
    }
}

pub fn mixed(e: E) -> i64 {
    match e {
        E::A(v) => v,
        E::B(ref y) => *y as i64,
    }
}

pub fn accumulate(e: E) -> i64 {
    let mut acc = 0i64;
    match e {
        E::A(ref x) => {
            acc += *x;
        }
        E::B(ref y) => {
            acc += *y as i64;
        }
    }
    acc
}

// The two refuter shapes — `E::A(ref x) => x as *const i64` returned as the
// arm result, and the same pointer smuggled out through a merged local — must
// keep refusing with Return(borrow ptr escapes tail). They are compile-valid
// Rust (raw casts launder the borrow), so they live in the probe suite rather
// than in this check-pass fixture.

fn main() {}
