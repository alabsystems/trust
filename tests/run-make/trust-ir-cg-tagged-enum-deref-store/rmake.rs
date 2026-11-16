//! A TAGGED (non-niche) multi-variant enum stored into a POINTEE FIELD through
//! `&mut` compiles, and both of its lanes land where the reader looks.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `memchr` once the fat-leaf lane had landed:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... memchr::memmem::FindRevIter::next ...:
//!            Ty::core::option::Option<usize>
//!
//! The MIR shape (-O3) is
//!
//!     ((*_1).2: Option<usize>) = copy _0;   // self.pos = Some(i), folded onto _0
//!
//! `lower_deref_aggregate_memory_store` declined the multi-variant enum
//! destination (it is not a tagless aggregate), and the decline fell through to
//! the SCALAR-leaf deref store, which asked for ONE trust-ir scalar for a two-lane
//! `{tag, payload}` value. The fix routes a `Use` operand into an enum destination
//! through `store_operand_into_memory_at` — the variant-agnostic slot lane copy
//! the array-element store (`arr[i] = move t`) already used.
//!
//! The functions below are the bisection set: every rvalue shape rustc produces
//! for the store (a copy of the memory-backed return local, a spilled temp, a
//! by-value param, a const, a call destination) at BOTH -O0 and -O3, since the
//! two opt levels produce different rvalues for the same source. Each one
//! refused before the fix; `read_pos` (the read-back) worked and must keep working.
//!
//! This test RUNS the result rather than only compiling it: the hazard class is a
//! store that writes ONE lane of the enum (a stale tag makes the iterator loop or
//! lose an element; a stale payload yields the wrong index), so the asserted
//! values, in order, are what matter.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

fn main() {
    rfs::write(
        "tagged.rs",
        r#"

// --- the WIDENING verdict #8 measured and asked to pin: single-scalar NICHE
// enums (`Option<&T>`, `Option<bool>`) also refused here before the fix with
// the same `Ty::` text and now take the same variant-agnostic lane copy. A
// torn tag/payload shows up as the wrong Option on read-back. ---
pub struct Niche { pub r: Option<&'static u64>, pub b: Option<bool>, pub pad: u8 }
pub static SEVEN: u64 = 7;
#[inline(never)] pub fn set_r(n: &mut Niche, v: Option<&'static u64>) { n.r = v; }
#[inline(never)] pub fn set_b(n: &mut Niche, v: Option<bool>) { n.b = v; }
#[inline(never)] pub fn get_r(n: &Niche) -> Option<u64> { n.r.copied() }
#[inline(never)] pub fn get_b(n: &Niche) -> Option<bool> { n.b }
pub struct It<'h> {
    haystack: &'h [u8],
    pos: Option<usize>,
}

#[inline(never)]
fn rfind_byte(h: &[u8], b: u8) -> Option<usize> {
    let mut d = 0usize;
    while d < h.len() {
        let j = h.len() - 1 - d;
        if h[j] == b { return Some(j); }
        d += 1;
    }
    None
}

// The memchr `FindRevIter::next` shape verbatim: at -O3 `self.pos = Some(i)`
// folds into `((*_1).1) = copy _0` (a copy of the memory-backed RETURN local);
// at -O0 rustc spills `Some(i)` to a temp and stores `move _t`.
impl<'h> Iterator for It<'h> {
    type Item = usize;
    #[inline(never)]
    fn next(&mut self) -> Option<usize> {
        let pos = match self.pos { None => return None, Some(pos) => pos };
        let haystack = match self.haystack.get(..pos) { None => return None, Some(h) => h };
        let result = rfind_byte(haystack, b'a');
        match result {
            None => None,
            Some(i) => {
                if pos == i { self.pos = pos.checked_sub(1); } else { self.pos = Some(i); }
                Some(i)
            }
        }
    }
}

// `((*_1).1) = copy _2` — a by-value enum PARAM.
#[inline(never)]
pub fn store_param(it: &mut It<'_>, v: Option<usize>) { it.pos = v; }
// `_t = Some(i); ((*_1).1) = move _t` — an inline construction spilled to a temp.
#[inline(never)]
pub fn store_some(it: &mut It<'_>, i: usize) { it.pos = Some(i); }
// `((*_1).1) = const None` (-O3) / `= move _t` (-O0).
#[inline(never)]
pub fn store_none(it: &mut It<'_>) { it.pos = None; }
// `((*_1).1) = move _3` — a memory-backed CALL destination.
#[inline(never)]
pub fn store_call(it: &mut It<'_>, b: u8) { it.pos = rfind_byte(it.haystack, b); }
// The read-back, by value (worked before; must keep working).
#[inline(never)]
pub fn read_pos(it: &It<'_>) -> Option<usize> { it.pos }

fn main() {
    let hay: &[u8] = b"abcabca";
    let mut it = It { haystack: hay, pos: Some(hay.len()) };

    // The tag AND the payload must both land: assert the exact values, in order.
    // A store that wrote only one lane would either keep a stale payload
    // (wrong index) or a stale tag (an endless iterator / a lost element).
    assert_eq!(it.next(), Some(6));
    assert_eq!(it.next(), Some(3));
    assert_eq!(it.next(), Some(0));
    assert_eq!(it.next(), None);
    assert_eq!(it.next(), None);

    store_param(&mut it, Some(4));
    assert_eq!(read_pos(&it), Some(4));
    store_param(&mut it, None);
    assert_eq!(read_pos(&it), None);

    store_some(&mut it, 2);
    assert_eq!(read_pos(&it), Some(2));
    store_none(&mut it);
    assert_eq!(read_pos(&it), None);

    store_call(&mut it, b'c');
    assert_eq!(read_pos(&it), Some(5));
    store_call(&mut it, b'z');
    assert_eq!(read_pos(&it), None);

    // A stored `Some` must be observable through the iterator again, i.e. the
    // write went to the SAME bytes `next` reads.
    store_some(&mut it, 4);
    assert_eq!(it.next(), Some(3));
    assert_eq!(it.next(), Some(0));
    assert_eq!(it.next(), None);


    // Niche-enum deref stores: both the Some/None tag and the payload must survive.
    let mut n = Niche { r: None, b: None, pad: 0xAB };
    set_r(&mut n, Some(&SEVEN));   assert_eq!(get_r(&n), Some(7));
    set_b(&mut n, Some(true));     assert_eq!(get_b(&n), Some(true));
    set_b(&mut n, Some(false));    assert_eq!(get_b(&n), Some(false));
    set_r(&mut n, None);           assert_eq!(get_r(&n), None);
    set_b(&mut n, None);           assert_eq!(get_b(&n), None);
    assert_eq!(n.pad, 0xAB);       // a neighbouring byte is untouched
    println!("tagged-enum deref stores ok");
}
"#,
    );

    // Both opt levels: the std build is -O3 (`copy _0` / `const None`), and -O0
    // produces the spilled-temp forms — different rvalues for the same source.
    for (name, level) in [("tagged_o0", "0"), ("tagged_o3", "3")] {
        rustc()
            .input("tagged.rs")
            .crate_type("bin")
            .crate_name(name)
            .opt_level(level)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .run();
        run(name).assert_stdout_contains("tagged-enum deref stores ok");
    }
}
