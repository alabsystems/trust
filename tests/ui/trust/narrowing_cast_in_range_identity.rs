//@ revisions: holds holds_cert holds_signed liars
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[holds_cert] compile-flags: -Ztrust-policy=certify
//@[holds] check-pass
//@[holds_cert] check-pass
//@[holds_signed] check-pass
//@[liars] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[liars] dont-require-annotations: ERROR
//! A narrowing integer cast whose source is representable in the target type is the
//! identity on that value (VC-NARROW-CAST-FALSE-REFUTE-1; 2026-10-11).
//!
//! `trust_vcgen`'s block-definition extractor (`guards.rs`, the `Rvalue::Cast` arm)
//! modelled a strictly narrowing int->int cast (`x as u8` for `x: u32`, `c as u8` for a
//! `char`) as a FREE value of the target type: it emitted only the target-type range
//! `0 <= _5 <= 255`, and nothing tied `_5` to `x`. So `TABLE[c as u8 as usize]` under
//! `c.is_ascii()` — the common ASCII lookup idiom — and `arr[x as u8 as usize]` under
//! `x < 0x80` were refuted at `_5 = 128`, published as `[bounds] FAILED
//! (trust-full-verifier); counterexample: verified_counterexample = true` with no real
//! assignment; `(x as u8) + 0x7f` and `1u32 << (x as u8)` under the same kind of guard
//! were `[overflow:add]` / `[shift:left] FAILED` ("UNGROUNDED").
//!
//! The extractor now also emits, for a strictly narrowing cast (and a same-width
//! unsigned->signed reinterpret), `(to_min <= src && src <= to_max) => dest == src`
//! (for an unsigned source, `src <= to_max => dest == src`): Rust's `as` returns the
//! value unchanged whenever it is representable in the target. Outside that range the
//! implication is vacuous, so it never contradicts the range.
//!
//! BEFORE (the stage 1 of `1213387e6d`, `scratchpad/stage1-w24probe`, measured
//! 2026-10-11 with this header's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata --error-format=json -A unused`;
//! `scratchpad/scout24/D/ui/`):
//! * `holds` exits 1 with 20 errors: each of the 10 functions reads "Trust Level 0
//!   safety verification incomplete … 1 obligation(s) were not proved" and "Trust strict
//!   verification failed". `a6`, `b1`, `n1`, `n2`, `n4`, `n6` and `us8` are refused on
//!   `[bounds] FAILED (trust-full-verifier); counterexample: verified_counterexample =
//!   true`, `add_u8` and `add_edge` on `[overflow:add] FAILED (ay-in-process)` and
//!   `shl_u8` on `[shift:left] FAILED (ay-in-process)`, all three "UNGROUNDED".
//! * `holds_cert` (`certify`) exits 1 with the same 20 errors.
//! * `holds_signed` exits 1 with 4 errors: `i16n` and `i8n`, each on `[bounds] FAILED
//!   (trust-full-verifier); counterexample: verified_counterexample = true`.
//! * `liars` exits 1 with 16 errors, two per liar, each on a FAILED row; the annotated
//!   one is required. Every liar panics for some input under stock `rustc` 1.97.1
//!   (`scratchpad/scout24/D/oracle/oracle.rs`: `l1(0x80)`, `l2(0x7f)`, `l3(0x80)`,
//!   `st1(200)`, `st2(&[200, 5])`, `st3(200, 1)`, `add_l(0x81)`, `shl_l(0x20)`), while
//!   no `holds*` function panics over its input domain. `st1`..`st3` bind the cast's
//!   source and then REWRITE it before the guard reads it (straight-line and
//!   loop-carried): the identity must describe the value the cast saw, never a later
//!   one.
//!
//! AFTER (predicted; not built — the fix is in `crates/` only and needs a rebuilt
//! stage 1): `holds`, `holds_cert` and `holds_signed` exit 0; `liars` still exits 1
//! with every liar refused. vcgen's half is pinned on real MIR in
//! `crates/trust-vcgen/tests/narrowing_cast_identity_realmir.rs`: with the fix every
//! `holds*` row is proved by the in-process router, every row of `holds` (the
//! unsigned sources) is kernel-certified by `trust_certify::certify_vc`, and every
//! liar's panicking row stays refuted and uncertified; without the fix every `holds*`
//! row is refuted. `holds_signed` is the least certain prediction: its rows are proved
//! by SMT but not kernel-certified, so it rests on the default policy accepting the
//! trust-vc lane's proof without a kernel certificate; it is kept out of `certify`.

// ---- holds: every cast here is lossless on the guarded path ----

#[cfg(any(holds, holds_cert))]
pub mod holds {
    // The ASCII lookup-table idiom.
    pub fn a6(c: char) -> u8 {
        let arr = [0u8; 0x80];
        if c.is_ascii() { arr[c as u8 as usize] } else { 0 }
    }

    pub fn b1(x: u32) -> u8 {
        let arr = [0u8; 0x80];
        if x < 0x80 { arr[x as u8 as usize] } else { 0 }
    }

    pub fn n1(x: u32) -> u8 {
        let arr = [0u8; 0x80];
        if x < 0x80 { arr[x as u16 as usize] } else { 0 }
    }

    pub fn n2(x: u16) -> u8 {
        let arr = [0u8; 0x80];
        if x < 0x80 { arr[x as u8 as usize] } else { 0 }
    }

    pub fn n4(x: u32) -> u8 {
        let arr = [0u8; 0x80];
        if x < 0x80 {
            let b = x as u8;
            arr[b as usize]
        } else {
            0
        }
    }

    pub fn n6(x: u64) -> u8 {
        let arr = [0u8; 0x80];
        if x < 0x80 { arr[x as u32 as usize] } else { 0 }
    }

    pub fn us8(x: usize) -> u8 {
        let arr = [0u8; 0x80];
        if x < 0x80 { arr[(x as u8) as usize] } else { 0 }
    }

    pub fn add_u8(x: u32) -> u8 {
        if x < 0x80 { (x as u8) + 0x7f } else { 0 }
    }

    pub fn shl_u8(x: u32) -> u32 {
        if x < 8 { 1u32 << (x as u8) } else { 0 }
    }

    // The 8-bit edge: `0x80u8 + 0x7f == 0xff` fits.
    pub fn add_edge(x: u32) -> u8 {
        if x <= 0x80 { (x as u8) + 0x7f } else { 0 }
    }
}

// ---- holds_signed: a SIGNED source needs both bounds of the target ----
//
// Their identity's antecedent is `to_min <= x && x <= to_max`; the crate tests prove it
// by SMT, but `trust-certify` has no kernel lane for a two-atom antecedent, so these
// are kept out of `holds_cert` (KNOWN_HAZARDS VC-NARROW-CAST-FALSE-REFUTE-1).

#[cfg(holds_signed)]
pub mod holds_signed {
    pub fn i16n(x: i32) -> u8 {
        let arr = [0u8; 0x80];
        if x >= 0 && x < 0x80 { arr[(x as i16) as usize] } else { 0 }
    }

    pub fn i8n(x: i32) -> u8 {
        let arr = [0u8; 0x80];
        if x >= 0 && x < 0x80 { arr[(x as u8) as usize] } else { 0 }
    }
}

// ---- liars: each panics for some input and must stay refused ----

#[cfg(liars)]
pub fn l1(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::l1`
    let arr = [0u8; 0x80];
    if x <= 0x80 { arr[x as u8 as usize] } else { 0 }
}

#[cfg(liars)]
pub fn l2(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::l2`
    let arr = [0u8; 0x7f];
    if x < 0x80 { arr[x as u8 as usize] } else { 0 }
}

#[cfg(liars)]
pub fn l3(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::l3`
    let arr = [0u8; 0x80];
    if x < 0x180 { arr[x as u8 as usize] } else { 0 }
}

// The guard reads `y` AFTER it is rewritten: the cast saw the old value (x = 200
// panics).
#[cfg(liars)]
pub fn st1(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::st1`
    let arr = [0u8; 0x80];
    let mut y = x;
    let b = y as u8;
    y = 0;
    if y < 0x80 { arr[b as usize] } else { 0 }
}

// Loop-carried: `b` is the previous element's cast, the guard tests the current one
// (`[200, 5]` panics).
#[cfg(liars)]
pub fn st2(xs: &[u32]) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::st2`
    let arr = [0u8; 0x80];
    let mut b = 0u8;
    let mut r = 0u8;
    for &y in xs {
        if y < 0x80 {
            r = arr[b as usize];
        }
        b = y as u8;
    }
    r
}

// Loop-carried through a counter: `b` is cast from `y` before `y` is rebound (x = 200,
// n = 1 panics).
#[cfg(liars)]
pub fn st3(x: u32, n: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::st3`
    let arr = [0u8; 0x80];
    let mut y = x;
    let mut r = 0u8;
    let mut i = 0u32;
    while i < n {
        let b = y as u8;
        y = i;
        if y < 0x80 {
            r = arr[b as usize];
        }
        i += 1;
    }
    r
}

// `x = 0x81`: `0x81u8 + 0x7f` overflows (its hold twin `add_edge` stops at `0x80`).
#[cfg(liars)]
pub fn add_l(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::add_l`
    if x <= 0x81 { (x as u8) + 0x7f } else { 0 }
}

// `x = 0x20`: a shift by 32 overflows a `u32`.
#[cfg(liars)]
pub fn shl_l(x: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::shl_l`
    if x <= 0x20 { 1u32 << (x as u8) } else { 0 }
}

// UNION-SIBLING-WRITE-1 (wave-24 review, 2026-10-12): a union's fields overlap, so the
// identity bound to `u.a` at the cast must not survive a write of `u.b`. `u_dst_add(0)`
// (`u.a` reads 200) and `u_src_idx(200)` (the guard reads the rewritten `u.a`) panic.
// These rows were PROVED on the stage 1 of `51eac007f3` (the advisory lane elided
// `u_dst_add`'s overflow check: `union_sibling_write_elide_run.rs`); this revision was
// refused all the same, by the union bodies' structural rows, so it pins the refusal,
// not the row: the rows are pinned by `narrowing_cast_identity_realmir.rs`.
#[cfg(liars)]
pub union V { pub a: u8, pub b: i8 }
#[cfg(liars)]
pub union U { pub a: u32, pub b: f32 }

#[cfg(liars)]
pub fn u_dst_add(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::u_dst_add`
    let mut u = V { a: 0 };
    u.a = x as u8;
    u.b = -56;
    if x < 0x80 { (unsafe { u.a }) + 0x7f } else { 0 }
}

#[cfg(liars)]
pub fn u_src_idx(x: u32) -> u8 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `narrowing_cast_in_range_identity::u_src_idx`
    let arr = [0u8; 0x80];
    let mut u = U { a: x };
    let b = unsafe { u.a } as u8;
    u.b = f32::from_bits(5);
    if unsafe { u.a } < 0x80 { arr[b as usize] } else { 0 }
}
