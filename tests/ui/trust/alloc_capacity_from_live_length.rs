//@ needs-trust-verify
//@ edition: 2021
//@ revisions: str_len slice_len from_elem resize string_len vec_len half_stride_sum same_stride_sum wider_target zst_source reserve param_count reseated_count alias_count raw_slice_len zst_guarded wide_target_guarded huge_target_guarded tuple_source array_source zst_tuple_source wide_two_terms_guarded same_stride_sum_coprime_guarded same_stride_sum_coprime_direct_guarded index_coprime_guarded index_coprime_direct_guarded struct_source nested_struct_source enum_source zst_struct_source generic_struct_source narrow_struct_source struct_len_plus_one pointer_struct_source pointer_recursive_source recursive_enum_source pointer_vec_len pointer_wider_target pointer_generic_source pointer_generic_concrete_part pointer_len_plus_one
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[str_len] check-pass
//@[slice_len] check-pass
//@[from_elem] check-pass
//@[resize] check-fail
//@[string_len] check-pass
//@[vec_len] check-pass
//@[half_stride_sum] check-pass
//@[same_stride_sum] check-fail
//@[wider_target] check-fail
//@[zst_source] check-fail
//@[reserve] check-fail
//@[param_count] check-fail
//@[reseated_count] check-fail
//@[alias_count] check-fail
//@[raw_slice_len] check-fail
//@[zst_guarded] check-fail
//@[wide_target_guarded] check-fail
//@[huge_target_guarded] check-fail
//@[tuple_source] check-pass
//@[array_source] check-pass
//@[zst_tuple_source] check-fail
//@[wide_two_terms_guarded] check-pass
//@[same_stride_sum_coprime_guarded] check-fail
//@[same_stride_sum_coprime_direct_guarded] check-pass
//@[index_coprime_guarded] check-fail
//@[index_coprime_direct_guarded] check-pass
//@[struct_source] check-pass
//@[nested_struct_source] check-pass
//@[enum_source] check-pass
//@[zst_struct_source] check-fail
//@[generic_struct_source] check-fail
//@[narrow_struct_source] check-fail
//@[struct_len_plus_one] check-fail
//@[pointer_struct_source] check-pass
//@[pointer_recursive_source] check-pass
//@[recursive_enum_source] check-pass
//@[pointer_vec_len] check-pass
//@[pointer_wider_target] check-fail
//@[pointer_generic_source] check-fail
//@[pointer_generic_concrete_part] check-pass
//@[pointer_len_plus_one] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! (2026-10-02) The "1 skipped" in a summary below is the allocator premise this
//! rlib's allocating functions now carry (`contract:global-alloc-dealloc-panic-free`,
//! DISCHARGED: the final link chooses the global allocator; see
//! `policy_b/global_allocator_is_chosen_by_the_final_link.rs`). It is not this file's
//! subject; every other count is unchanged.
//!
//! Trust (W4 ALLOC-LEN, 2026-09-25): a capacity that IS the length of a live
//! sequence is not an unbounded allocation — and its capacity-overflow panic is
//! discharged only by a theorem, never waved through.
//!
//! `crates/trust-vcgen/src/generate/alloc_len.rs` has the argument;
//! `docs/TCB.md` ("Live-length capacity") has the premise. In short: a
//! DefId-keyed fresh exact-capacity constructor (`Vec::with_capacity`,
//! `vec![x; n]`, `String::with_capacity`) whose count is `PtrMetadata` of a
//! slice REFERENCE or an authenticated `str`/`[T]`/`String`/`Vec` `len()` call
//! (or the sum of two) drops the availability ceiling — the `collect` sibling's
//! premise — and keeps the RawVec capacity-overflow disjunct unless
//! `T * len <= S * len <= isize::MAX` (target stride `T`, source stride `S`, one
//! term) or `T * (S1 + S2) <= S1 * S2` (two terms) proves it.
//!
//! # Before (measured on stage-1 `trustc 0.10.0+gab7e41892`, 2026-09-25)
//!
//! EVERY revision was rc=1 with `[unbounded_allocation] FAILED (ay-in-process)`
//! — the check-pass ones at the availability witness `268435456` (2^28) or its
//! byte-scaled twin. That includes the unaimed programs this pins: `d0/p05`
//! (`str_len`'s shape), `d5/p12` (`slice_len`'s) and `d0/p08`.
//!
//! # After
//!
//! The six check-pass revisions carry NO allocation row at all. The rails:
//!
//! * `resize` — `v.resize(xs.len(), 0)` is NOT admitted, although `xs.len()`
//!   is a live length: `resize` grows through `RawVec::grow_amortized`, which
//!   requests `max(2 * capacity, new_len)`, so an existing capacity above
//!   `isize::MAX / 2` bytes panics "capacity overflow" even though
//!   `new_len * 4` fits. (A first draft of this change admitted it — measured
//!   rc=0 on its stage 1 — and this rail is why it does not.)
//! * `same_stride_sum` — `tests/ordinary-rust-sweep` t23,
//!   `String::with_capacity(a.len() + b.len())`. STILL refused, now by the kept
//!   capacity row with a counterexample at `2^63` — two live `&str`s may together
//!   exceed `isize::MAX` in the type model although neither can alone. A correct
//!   refusal (the sweep README's classification), with the right witness now.
//! * `wider_target` — `Vec::<u64>::with_capacity(bytes.len())`: `8 * len` can
//!   exceed `isize::MAX` for a byte slice. Since adversarial round 1 (below) a
//!   wider target keeps the availability ceiling too. Its witness was the 256 MiB
//!   byte budget (`len = 2^25`) until that budget was deleted with trust-ir's
//!   `ALLOC_BYTE_BUDGET` (2026-10-08, ALLOC-BYTE-1); it is now the element ceiling,
//!   `len = 2^28`, and the row stays refused. That witness is the CEILING's, a value
//!   threshold kept as OPEN debt (DECISION_QUEUE ALLOC-ELEM-CEILING-1), not the
//!   panic's: 2 GiB of `u64` does not overflow, the capacity line is about
//!   `len = 2^60` (the witness before round 1), and it is the one to pin when the
//!   ceiling goes.
//! * `zst_source` — `Vec::<u8>::with_capacity(units.len())` over `&[()]`: a ZST
//!   slice's length is NOT bounded by `isize::MAX`. WITNESSED at runtime with a
//!   verify-off build: `from_units(&vec![(); usize::MAX])` panics
//!   `capacity overflow`. Since round 1 it keeps the availability ceiling (a ZST
//!   source holds no memory), so the witness is `2^28`; before it was `2^63`.
//! * `reserve` — `reserve`'s count is ADDITIONAL capacity; the existing length
//!   it adds to is not modeled, so it is not admitted (availability row kept).
//! * `param_count` — an opaque `usize` parameter (the correct refusals `d1/p06`
//!   and `d1/p15` have this shape); WITNESSED: `sized(usize::MAX)` panics.
//! * `reseated_count`, `alias_count` — a length local rebound, directly or
//!   through a `&mut`, is no longer a length; `aliased("a", usize::MAX)` panics.
//! * `raw_slice_len` — a RAW slice pointer's metadata bounds nothing
//!   (`ptr::slice_from_raw_parts(p, usize::MAX)` is safe to build).
//!
//! # Adversarial round 1 (2026-09-25): availability needs `S_i >= T`
//!
//! The first version dropped the availability ceiling for EVERY len-derived
//! count, on the premise that it "allocates at most a constant factor of memory
//! the program already holds". Refuted twice; the ceiling is now dropped only
//! when every term's source stride is known, non-zero and at least the target's
//! (`alloc_len::availability_theorem_holds`), so the allocation is at most the
//! counted bytes. Each rail below was rc=0 on the w4-alloc-str stage 1
//! (`0.10.0+gab7e41892` + b06b56569a) or, for `huge_target_guarded`, never
//! finished there:
//!
//! * `zst_guarded` (probe a02) — `Vec::<u8>::with_capacity(z.len())` over
//!   `&[()]` under `z.len() < 2^60`: a ZST slice holds no memory. WITNESSED:
//!   `z = vec![(); 1 << 55]` aborts "memory allocation of 36028797018963968 bytes
//!   failed".
//! * `wide_target_guarded` (a11) — `Vec::<[u8; 1 << 14]>::with_capacity(s.len())`
//!   under `s.len() < 2^40`: WITNESSED, a 64 GiB zeroed source asks 2^50 bytes
//!   and aborts.
//! * `huge_target_guarded` (a01) — the same at `[u8; 1 << 30]` under `< 2^32`.
//!   On the w4-alloc-str stage 1 this row's capacity-only form was proved by ay
//!   and then held the compiler in clean_auto's proof reconstruction (> 11 min,
//!   184 GB — `trust-certify`'s `AY_RECONSTRUCTION_MAX_COEFFICIENT`); now it is
//!   the ordinary row, refused in seconds as on origin/main. WITNESSED: a 1 MiB
//!   source asks 1 PiB and aborts.
//! * `zst_tuple_source` — a tuple of ZSTs is zero-sized too (stride bound 0).
//!
//! And two over-refusals it removes / one shape it must not hang on:
//!
//! * `tuple_source` (probe a09), `array_source` — the source stride is now a
//!   LOWER bound through tuples and arrays (`(u8, u8)` is at least 2 bytes,
//!   `[u16; 4]` exactly 8), so `T <= S` proves both halves.
//! * `wide_two_terms_guarded` — two `&[[u8; 1 << 20]]` lengths under `< 1024`
//!   each: availability-bounded (`T = S1 = S2`), not capacity-safe, so it is the
//!   capacity-only row `2^20 * (a + b) >= 2^63`, TRUE under the guards. Its
//!   Farkas certificate needs a `2^20` multiplier on every guard, the hang shape
//!   above; the certify gate declines it (the row stays proved, not
//!   kernel-certified) and the compile finishes.
//!
//! # Adversarial round 2 (2026-09-26): the certify gate must bound PRODUCTS
//!
//! Round 1's certify gate capped the pool's largest literal coefficient at
//! `2^12`. The re-probe got past it with coefficients all at most `2^12` whose
//! Farkas certificate multiplies them: under `a.len() * 4093 < K ∧
//! b.len() * 4091 < K` ay certifies with the coefficient `4093/4091`, so
//! clean_auto's integer multipliers are `4093 · 4091 ≈ 2^24` and its closeout
//! walks a tree of that many copies (docs/KNOWN_HAZARDS.md). `trust-certify`
//! now bounds the pool's coefficient PRODUCT before the solve and the leaves of
//! ay's actual certificate after it (`reconstruction_scale.rs`). Each revision
//! below is a proved row whose certification used to run away; the rows stay
//! proved (not kernel-certified) and the compile finishes in seconds.
//!
//! Measured 2026-09-26 on the round-1 stage 1 (`snap-w4f-alloc_str-r1`) and on
//! origin/main (`snap-w4f-alloc_str-base`, `c2e3daed7`), each compile killed at
//! an 8 GB RSS limit:
//!
//! * `same_stride_sum_coprime_guarded` — probe b45 verbatim: t23 under the two
//!   coprime-scaled guards. Round 1: killed at 8 GB after 22 s. origin/main:
//!   rc=1 in 12 s (it has no capacity-only row to certify). Check-FAIL, and
//!   correctly: `a.len() * 4093` can overflow for a `&str` longer than
//!   `2^64 / 4093` bytes, which the type model allows (origin/main fails the same
//!   two `Mul` rows). The capacity row itself is proved.
//! * `same_stride_sum_coprime_direct_guarded` — the same with direct guards
//!   first, so the multiplications cannot overflow, and everything proves. A
//!   positive twin, not a hang rail: ay certifies this row through the direct
//!   guards (round 1: rc=0 in 38 s; origin/main: rc=1 on its availability row).
//! * `index_coprime_guarded` — probe b48 verbatim, a plain bounds check under
//!   the same guards: the entry point origin/main already had. Killed at 8 GB
//!   after 15 s on origin/main and after 22 s on round 1. Check-fail on the same
//!   two `Mul` rows; the index row proves.
//! * `index_coprime_direct_guarded` — its direct-guarded twin: everything
//!   proves. ay still certifies the index row through the coprime guards, so it
//!   blew up before too: killed at 8 GB after 51 s on origin/main and after 39 s
//!   on round 1.

//!
//! # User ADT sources (ALLOC-STRIDE-ADT-1, 2026-10-07)
//!
//! `element_stride_lower_bound` sized only primitives, tuples and arrays, so a
//! user struct/enum source had stride 0 and kept both rows. An extractor-minted
//! ADT is now sized by a LOWER bound of its layout (struct: field sum; union:
//! largest field; enum: largest variant payload; rustc's layout size when
//! recorded — the faithful lane only). On the verifier lane, which decides these
//! rows, only the field-level bound applies, and it counts only primitive and
//! array bytes: a `Vec`, `String`, `Arc`, `Box` or reference field sizes 0. So
//! clean-ck0's six `Vec::with_capacity(src.len())` rows, whose sources are
//! pointer-heavy, are NOT discharged by this (DECISION_QUEUE ALLOC-STRIDE-ADT-2).
//!
//! Before, measured on the preview3 stage 1 (main without the change): the
//! first seven revisions below were rc=1 with `[unbounded_allocation] FAILED
//! (ay-in-process)`, and so was `pointer_struct_source` (measured 2026-10-07,
//! the same stage 1). After: first measured 2026-10-07 on the ALLOC-STRIDE-ADT-2
//! stage 1, i.e. WITH the element-size table on top (every revision of this file
//! passed there), so the check-pass of `struct_source`, `nested_struct_source`
//! and `enum_source` is not evidence for the structural bound alone; the rails
//! keep their row —
//!
//! * `zst_struct_source` — a unit struct holds no memory (bound 0);
//! * `generic_struct_source` — a generic field sizes 0 (no guess);
//! * `narrow_struct_source` — a target (88 bytes) wider than the source's bound
//!   (80) keeps availability unbounded;
//! * `struct_len_plus_one` — clean-ck0 `term.rs`: `len + 1` is not a length;
//! * `pointer_struct_source` — a clean-ck0-shaped element (`String`, `u32`,
//!   `Vec`, `Arc`: 64 bytes) into a 24-byte target: the verifier lane's bound is
//!   4 (the `u32`), so the row stays. It becomes provable only with rustc's
//!   element size on the verifier lane (ALLOC-STRIDE-ADT-2) — and since that
//!   change it is a check-pass revision (below).
//!
//! # The compiler's element-size table (ALLOC-STRIDE-ADT-2, 2026-10-07)
//!
//! The TrustVerify site now hands vcgen rustc's `layout_of` size of every slice/
//! `Vec` source element key (`trust_vcgen::ElemSizeTable`, beside the function on
//! its `VcgenContext`, never in it), so a pointer-heavy element is sized from below
//! by its real size. A proof session runs the `-O0` MIR pipeline (T6,
//! DECISION_QUEUE MIRPIPE-1), where `LowerSliceLenCalls` turns `src.len()` into
//! `PtrMetadata`; the `<[T]>::len` CALL shape survives only at
//! `-Zmir-opt-level=0`, which a proof session refuses, so the four `_o0` twins
//! this change first carried (`pointer_struct_source`, `pointer_wider_target`,
//! `pointer_generic_source`, `pointer_len_plus_one` at `-Zmir-opt-level=0`) were
//! deleted when T6 landed (2026-10-10).
//!
//! * `pointer_struct_source` — `Info` (`String`, `u32`, `Vec`, `Arc`: 64
//!   bytes) into `[u64; 3]` (24): check-pass;
//! * `pointer_recursive_source` — `Node` (a recursive enum `Term`, a `String`, an
//!   `Arc<str>`: 56 bytes) into 24: check-pass;
//! * `recursive_enum_source` — `&[Term]` (16 bytes — `App`'s first `Box` is the
//!   niche — and a by-name datatype key) into `[u64; 2]` (16);
//! * `pointer_vec_len` — `Vec::len` of a `&Vec<Info>` (the `Ty::Seq` path);
//! * `pointer_wider_target` — `Info` (64) into `[u64; 9]` (72): KEPT;
//! * `pointer_generic_source` — `&[(Vec<T>, T)]`: a generic element has no
//!   layout, so no table row, and neither part sizes: KEPT;
//! * `pointer_generic_concrete_part` — `&[(String, T)]` into 24: the tuple key is
//!   poisoned (generic), but its `String` part is monomorphic and sized (24), and a
//!   tuple is at least the sum of its parts whatever `T` is, so the row is
//!   discharged — soundly, for every instantiation (measured: a first draft of this
//!   test expected KEPT here, and the stage 1 discharged it);
//! * `pointer_len_plus_one` — `src.len() + 1` is not a length: KEPT.

#[cfg(any(
    struct_source,
    nested_struct_source,
    narrow_struct_source,
    struct_len_plus_one
))]
pub struct Plain {
    pub a: [u64; 10],
}

#[cfg(struct_source)]
pub fn heads(src: &[Plain]) -> Vec<u64> {
    Vec::with_capacity(src.len())
}

#[cfg(nested_struct_source)]
pub struct Outer {
    pub p: Plain,
    pub x: u8,
}

#[cfg(nested_struct_source)]
pub fn inners(src: &[Outer]) -> Vec<[u64; 10]> {
    Vec::with_capacity(src.len())
}

#[cfg(enum_source)]
pub enum Cell {
    Pair([u64; 2]),
    Empty,
}

#[cfg(enum_source)]
pub fn firsts_of(src: &[Cell]) -> Vec<u64> {
    Vec::with_capacity(src.len())
}

#[cfg(zst_struct_source)]
pub struct Marker;

#[cfg(zst_struct_source)]
pub fn from_markers(src: &[Marker]) -> Vec<u8> {
    //[zst_struct_source]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len())
}

#[cfg(generic_struct_source)]
pub struct Wrap<T>(pub T);

#[cfg(generic_struct_source)]
pub fn from_wrapped<T>(src: &[Wrap<T>]) -> Vec<u8> {
    //[generic_struct_source]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len())
}

#[cfg(narrow_struct_source)]
pub fn widen_plain(src: &[Plain]) -> Vec<[u64; 11]> {
    //[narrow_struct_source]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len())
}

#[cfg(struct_len_plus_one)]
pub fn one_more(src: &[Plain]) -> Vec<Plain> {
    //[struct_len_plus_one]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len() + 1)
}

#[cfg(any(
    pointer_struct_source,
    pointer_vec_len,
    pointer_wider_target,
    pointer_len_plus_one
))]
pub struct Info {
    pub name: String,
    pub n: u32,
    pub kids: Vec<u64>,
    pub a: std::sync::Arc<u64>,
}

#[cfg(pointer_struct_source)]
pub fn from_infos(src: &[Info]) -> Vec<[u64; 3]> {
    Vec::with_capacity(src.len())
}

#[cfg(any(pointer_recursive_source, recursive_enum_source))]
pub enum Term {
    Var(u32),
    App(Box<Term>, Box<Term>),
}

#[cfg(pointer_recursive_source)]
pub struct Node {
    pub t: Term,
    pub name: String,
    pub tag: std::sync::Arc<str>,
}

#[cfg(pointer_recursive_source)]
pub fn from_nodes(src: &[Node]) -> Vec<[u64; 3]> {
    Vec::with_capacity(src.len())
}

#[cfg(recursive_enum_source)]
pub fn from_terms(src: &[Term]) -> Vec<[u64; 2]> {
    Vec::with_capacity(src.len())
}

#[cfg(pointer_vec_len)]
pub fn from_info_vec(src: &Vec<Info>) -> Vec<[u64; 3]> {
    Vec::with_capacity(src.len())
}

#[cfg(pointer_wider_target)]
pub fn widen_infos(src: &[Info]) -> Vec<[u64; 9]> {
    //[pointer_wider_target]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len())
}

#[cfg(pointer_generic_source)]
pub fn from_vec_pairs<T>(src: &[(Vec<T>, T)]) -> Vec<[u64; 3]> {
    //[pointer_generic_source]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len())
}

#[cfg(pointer_generic_concrete_part)]
pub fn from_named<T>(src: &[(String, T)]) -> Vec<[u64; 3]> {
    Vec::with_capacity(src.len())
}

#[cfg(pointer_len_plus_one)]
pub fn one_more_info(src: &[Info]) -> Vec<[u64; 3]> {
    //[pointer_len_plus_one]~^ NOTE [unbounded_allocation] FAILED
    Vec::with_capacity(src.len() + 1)
}

#[cfg(str_len)]
pub fn copy_str(s: &str) -> String {
    //[str_len]~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2 obligation(s)
    let mut out = String::with_capacity(s.len());
    out.push_str(s);
    out
}

#[cfg(slice_len)]
pub fn dedup_ports(ports: &[u16]) -> Vec<u16> {
    //[slice_len]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    let mut seen: Vec<u16> = Vec::with_capacity(ports.len());
    for &p in ports {
        if !seen.contains(&p) {
            seen.push(p);
        }
    }
    seen
}

#[cfg(from_elem)]
pub fn zeroed_like(s: &str) -> Vec<u8> {
    //[from_elem]~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2 obligation(s)
    vec![0u8; s.len()]
}

#[cfg(resize)]
pub fn grow_to(v: &mut Vec<u32>, xs: &[u32]) {
    //[resize]~^ NOTE [unbounded_allocation] FAILED
    v.resize(xs.len(), 0);
}

#[cfg(string_len)]
pub fn copy_string(st: &String) -> String {
    //[string_len]~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2 obligation(s)
    String::with_capacity(st.len())
}

#[cfg(vec_len)]
pub fn same_capacity(v: &Vec<u32>) -> Vec<u32> {
    //[vec_len]~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2 obligation(s)
    Vec::with_capacity(v.len())
}

#[cfg(half_stride_sum)]
pub fn bytes_for(a: &[u16], b: &[u16]) -> Vec<u8> {
    //[half_stride_sum]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    Vec::with_capacity(a.len() + b.len())
}

#[cfg(same_stride_sum)]
pub fn cat(a: &str, b: &str) -> String {
    //[same_stride_sum]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _3 = 9223372036854775808
    String::with_capacity(a.len() + b.len())
}

#[cfg(wider_target)]
pub fn widen(bytes: &[u8]) -> Vec<u64> {
    //[wider_target]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _2 = 268435456, bytes__slice_len = 268435456
    Vec::with_capacity(bytes.len())
}

#[cfg(zst_source)]
pub fn from_units(units: &[()]) -> Vec<u8> {
    //[zst_source]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _2 = 268435456
    Vec::with_capacity(units.len())
}

#[cfg(reserve)]
pub fn append_room(v: &mut Vec<u8>, s: &str) {
    //[reserve]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _4 = 268435456
    v.reserve(s.len());
}

#[cfg(param_count)]
pub fn sized(n: usize) -> Vec<u8> {
    //[param_count]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: n = 268435456
    Vec::with_capacity(n)
}

#[cfg(reseated_count)]
pub fn scaled(s: &str) -> Vec<u8> {
    //[reseated_count]~^ NOTE [unbounded_allocation] FAILED
    let mut n = s.len();
    n = n.wrapping_mul(1 << 20);
    Vec::with_capacity(n)
}

#[cfg(alias_count)]
pub fn aliased(s: &str, big: usize) -> Vec<u8> {
    //[alias_count]~^ NOTE [unbounded_allocation] FAILED
    let mut n = s.len();
    let p = &mut n;
    *p = big;
    Vec::with_capacity(n)
}

#[cfg(raw_slice_len)]
pub fn from_raw(s: &[u8]) -> Vec<u8> {
    //[raw_slice_len]~^ NOTE [unbounded_allocation] FAILED
    let p: *const [u8] = core::ptr::slice_from_raw_parts(s.as_ptr(), usize::MAX);
    Vec::with_capacity(p.len())
}

#[cfg(zst_guarded)]
pub fn from_units_guarded(z: &[()]) -> Vec<u8> {
    //[zst_guarded]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _2 = true, _3 = 268435456
    if z.len() < (1usize << 60) { Vec::with_capacity(z.len()) } else { Vec::new() }
}

#[cfg(wide_target_guarded)]
pub fn pages_for(s: &[u8]) -> Vec<[u8; 1 << 14]> {
    //[wide_target_guarded]~^ NOTE [unbounded_allocation] FAILED (ay-in-process)
    if s.len() < (1usize << 40) { Vec::with_capacity(s.len()) } else { Vec::new() }
}

#[cfg(huge_target_guarded)]
pub fn gigabytes_for(s: &[u8]) -> Vec<[u8; 1 << 30]> {
    //[huge_target_guarded]~^ NOTE [unbounded_allocation] FAILED (ay-in-process)
    if s.len() < (1usize << 32) { Vec::with_capacity(s.len()) } else { Vec::new() }
}

#[cfg(tuple_source)]
pub fn firsts(pairs: &[(u8, u8)]) -> Vec<u8> {
    //[tuple_source]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    let mut out = Vec::with_capacity(pairs.len());
    for &(a, _) in pairs {
        out.push(a);
    }
    out
}

#[cfg(array_source)]
pub fn packed(quads: &[[u16; 4]]) -> Vec<u64> {
    //[array_source]~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2 obligation(s)
    Vec::with_capacity(quads.len())
}

#[cfg(zst_tuple_source)]
pub fn from_unit_pairs(units: &[((), ())]) -> Vec<u8> {
    //[zst_tuple_source]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _2 = 268435456
    Vec::with_capacity(units.len())
}

#[cfg(wide_two_terms_guarded)]
pub fn both_pages(a: &[[u8; 1 << 20]], b: &[[u8; 1 << 20]]) -> Vec<[u8; 1 << 20]> {
    //[wide_two_terms_guarded]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 4 obligation(s)
    if a.len() < 1024 && b.len() < 1024 { Vec::with_capacity(a.len() + b.len()) } else { Vec::new() }
}

// The four `*_coprime_*` counts below dropped by one row per `1usize << N` on 2026-10-13
// (SELF-GUARDED-LITERAL-OPERAND-2, wave 26): a signed-literal shift amount used to carry a
// generic `overflow` row beside its `shift:left` row; the literal cast source now binds by
// value, so only the `shift:left` row remains. No verdict moved (JSON row differential,
// docs/KNOWN_HAZARDS.md LITERAL-PAIR-WIDTH-1 entry).
#[cfg(same_stride_sum_coprime_guarded)]
pub fn cat_scaled(a: &str, b: &str) -> String {
    //[same_stride_sum_coprime_guarded]~^ NOTE Trust verification: 4 proved, 2 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 8 obligation(s)
    //[same_stride_sum_coprime_guarded]~^^ NOTE [overflow:mul] FAILED (ay-in-process)
    if a.len() * 4093 < (1usize << 60) && b.len() * 4091 < (1usize << 60) {
        String::with_capacity(a.len() + b.len())
    } else {
        String::new()
    }
}

#[cfg(same_stride_sum_coprime_direct_guarded)]
pub fn cat_scaled_bounded(a: &str, b: &str) -> String {
    //[same_stride_sum_coprime_direct_guarded]~^ NOTE Trust verification: 8 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 10 obligation(s)
    if a.len() < (1usize << 40)
        && b.len() < (1usize << 40)
        && a.len() * 4093 < (1usize << 60)
        && b.len() * 4091 < (1usize << 60)
    {
        String::with_capacity(a.len() + b.len())
    } else {
        String::new()
    }
}

#[cfg(index_coprime_guarded)]
pub fn pick(a: &str, b: &str, big: &[u8; 1 << 12]) -> u8 {
    //[index_coprime_guarded]~^ NOTE Trust verification: 4 proved, 2 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 6 obligation(s)
    //[index_coprime_guarded]~^^ NOTE [overflow:mul] FAILED (ay-in-process)
    let c = a.len() + b.len();
    if a.len() * 4093 < (1usize << 22) && b.len() * 4091 < (1usize << 22) { big[c] } else { 0 }
}

#[cfg(index_coprime_direct_guarded)]
pub fn pick_bounded(a: &str, b: &str, big: &[u8; 1 << 12]) -> u8 {
    //[index_coprime_direct_guarded]~^ NOTE Trust verification: 8 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 8 obligation(s)
    let c = a.len() + b.len();
    if a.len() < (1usize << 40)
        && b.len() < (1usize << 40)
        && a.len() * 4093 < (1usize << 22)
        && b.len() * 4091 < (1usize << 22)
    {
        big[c]
    } else {
        0
    }
}
