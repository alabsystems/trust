//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ edition: 2021
//! Trust (B5 stage 1b, reads): a yield-free CAPTURING coroutine body — an
//! `async fn` reading its own parameters — lowers clean. Stage 1b signed its
//! env as the upvar-typed `coroutine::{path}` struct (one `__upvar{i}` per
//! parameter, the MIR-side oracle's differential-lane spelling); this file
//! pins the READ side: every parameter read is an `ExtractField` on the
//! by-value env (scalar, `&T`, struct, array and tuple upvars alike), and a
//! captured `&T`/`&mut T` joins the ref-param ledgers so its deref is the
//! ref-param `Load`/`Store`. On the signing-only build every one of these
//! bodies stopped at `UpvarRef(non-closure env pointee)`; `strict` turns that
//! into a compile error, so this file is the mutation check.
//!
//! EFFECT CONSERVATION (D28, 2026-10-01): `main` drops six coroutine VALUES (a coroutine's drop
//! glue depends on its state and saved locals, which rustc's own `needs_drop` does not compute
//! either), while each coroutine body's drop of its OWN env runs only its `Copy` upvars' glue and
//! stays clean. The direct trust-ir emits no `Drop` yet, so the effect-conservation gate tags each
//! such body `Abstracted(drop, ..)` and strict refuses it (expected below). A producer tag would
//! still be its own, unannotated, strict error, so this file keeps its mutation check.
struct S {
    a: i64,
    b: i64,
}
async fn add(x: u32, y: u32) -> u32 {
    x + y
}
async fn pick(flag: bool, p: &i32) -> i32 {
    if flag { *p } else { 0 }
}
async fn field(s: S) -> i64 {
    s.a - s.b
}
async fn arr(xs: [u8; 4], i: u8) -> u8 {
    xs[1] ^ i
}
async fn pair(t: (u16, u16)) -> u16 {
    t.0 + t.1
}
async fn bump(p: &mut u64) {
    *p += 1;
}
fn main() {
    //~^ ERROR the effect-conservation check refused it against the built MIR
    let _a = add(1, 2);
    let x = 3;
    let _p = pick(true, &x);
    let _f = field(S { a: 4, b: 1 });
    let _r = arr([1, 2, 3, 4], 9);
    let _t = pair((1, 2));
    let mut v = 7u64;
    let _b = bump(&mut v);
}
