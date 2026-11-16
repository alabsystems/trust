//@ revisions: title_case lowercase_after_next flat_map_unbounded_fanout btree_range
//@ revisions: zst_map_source zst_flat_map_source
//@ revisions: capitalize_root title_one_direct title_one_direct_census zst_enum_payload_source
//@ revisions: btree_range_certify btree_range_debug_std
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[title_case] check-fail
//@[capitalize_root] check-pass
//@[title_one_direct] check-fail
//@[title_one_direct] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[title_one_direct_census] check-pass
//@[title_one_direct_census] ignore-std-debug-assertions (measured with a release-like std only)
//@[zst_enum_payload_source] check-fail
//@[lowercase_after_next] check-pass
//@[flat_map_unbounded_fanout] check-fail
//@[btree_range] check-pass
//@[btree_range] ignore-std-debug-assertions (pinned by `btree_range_debug_std`)
//@[btree_range_certify] check-fail
//@[btree_range_certify] compile-flags: -Ztrust-policy=certify
//@[btree_range_certify] ignore-std-debug-assertions (measured with a release-like std only)
//@[btree_range_debug_std] check-fail
//@[btree_range_debug_std] needs-std-debug-assertions
//@[zst_map_source] check-fail
//@[zst_flat_map_source] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W4 ITER-HOF (c): `collect` element counts the bounded-source walk could not
//! establish, so `UnboundedAllocation::Iterator::collect::count-not-derivable` —
//! a row with NO runtime fallback — refused programs whose collect is a constant
//! multiple of an input they already hold.
//!
//!  * `title_case` is unaimed-90 d0/p06 verbatim. `capitalize` collects
//!    `first.to_uppercase().chain(chars.flat_map(|c| c.to_lowercase()))`: a
//!    case mapping yields at most three `char`s (`CaseMappingIter(array::
//!    IntoIter<char, 3>)`), so the chain yields at most `3 + 3 * word.len()`.
//!    `chars` is advanced by one `next` first (its `&mut` conduit feeds only
//!    `next`, which `local_def` already admits). `title_case` then maps
//!    `capitalize` — a LOCAL fn item, W4 (b) — over `split(' ')`.
//!    Trust (2026-10-01, fix round 2 of this item, on main `123f22d176`):
//!    `title_case` is REFUSED again, and not for anything this item touches —
//!    `capitalize_root` (the same `capitalize`, as its own public root) still
//!    builds, and `title_one_direct` (`capitalize(s)` called DIRECTLY, no fn item,
//!    no `map`) is refused with the same single row. In a CALLER's bundle core's
//!    `FlattenCompat::<Map<Chars, {closure}>, ToLowercase>::iter_fold::<(),
//!    {closure}>` (reached through `String`'s `extend`) is declined at enqueue
//!    (the `core::iter::` plumbing family) and its absent-callee row names a user
//!    closure, so it is `NOT-VANILLA` and fatal (`TRUST_VANILLA_DEBUG`). The
//!    W4-era main (`3b30328c07`) never reached that member, and `library/` has not
//!    changed since; the bundle that reaches it is main's kept bundle (KNOWN_HAZARDS
//!    "CLOSED 2026-09-29 — the bundled std-member tolerance …", whose capability
//!    losses are this same class). Pinned so a repair of that class shows here.
//!    `title_one_direct` runs with the sysroot panic census withheld
//!    (`TRUST_NO_SYSROOT_CENSUS=1`, 2026-10-08, std-absent-callee), so it keeps
//!    pinning that class. With the census on (`title_one_direct_census`) the
//!    caller's bundle no longer reaches that member: the census derives the
//!    adapter constructors `capitalize` calls (`to_uppercase`, `chain`, `flat_map`,
//!    `Chars::next`) panic-free, the bundle lowers differently, and `title_one`
//!    builds with its rows reported, as `capitalize_root` does. Not a repair of the
//!    class: no census grant reaches the user closure (every `fold`/`for_each`/
//!    `collect` instance that calls it is censused NOT total).
//!  * `lowercase_after_next` isolates the hand-advanced source.
//!  * `flat_map_unbounded_fanout` is the control: `repeat(c).take(k)` per item
//!    is NOT a constant fanout, and the `count-not-derivable` row must stay (it
//!    is the refusing row here, measured).
//!  * `btree_range` (unaimed-90 d1/p11): `BTreeMap::range` is now a keyed
//!    collection producer, so the count row is GONE. It was the refusing row
//!    before (2 obligations not verified: the count row plus the panic-freedom
//!    aggregate). What happens to the aggregate depends on how std was built.
//!    - `btree_range` (std WITHOUT debug assertions: the sealed channel's std,
//!      `scripts/recreate_bootstrap.py`'s `debug-assertions-std = false`):
//!      BUILDS under the default policy. The `range` order assertion is
//!      kernel-certified from the `from >= to` guard. The one remaining row is the
//!      aggregate, whose absent callee is `NodeRef::search_tree_for_bifurcation::
//!      <u64, Range<u64>>`: a sysroot routine at foundational types, so the row is
//!      runtime-checked and reported, not failed. Its panics are std's own
//!      bound-order checks, which the guard rules out. `btree_range_certify` pins
//!      that this row earns no proof credit: certify refuses it.
//!    - `btree_range_debug_std` (std WITH debug assertions): REFUSED, with ONE
//!      unverified obligation and the Level 0 note a warning. The aggregate also
//!      folds a call to `btree::mem::replace` that std's `btree::map::Range::next`
//!      hands a closure DEFINED in `alloc` (`LeafRange::perform_next_checked`). A
//!      sysroot closure is not foundational (`ty_is_foundational` has no
//!      `ty::Closure` arm), so the row is fatal: unaimed-90 lever S1, not this
//!      item. `policy_b/btree_range_order_charged.rs#guarded_debug_std` pins the
//!      same mechanism.
//!    Trust (2026-11-08): the count is TWO since `3da832a919` (trust-mc
//!    `824fd9248` validates the whole TrustIr module before BMC and refuses an
//!    invalid one outright). This bundle holds one layout-unevidenced cast,
//!    `RawVecInner::try_allocate_in`'s `Alignment -> NonNull<u8>` reinterpret
//!    (`struct -> struct` with no size layout metadata), which the bridge keeps
//!    emitting as a VISIBLE blocker by design
//!    (`layout_sensitive_cast_fallback_tests::a_non_identity_unevidenceable_reinterpret_stays_a_visible_blocker`).
//!    Before, trust-mc still credited `assertion:0` from that malformed module
//!    (native `proved=1`); now the native lane proves nothing in it
//!    (`proved=0, unsupported=2`), so both rows count as not fully verified. The
//!    order assertion itself is still proved in-process (`ay-in-process`), and
//!    the refusing row is unchanged. The cast leaves when a layout-evidence leg
//!    gives bridge structs a size.
//!    Trust (2026-10-05): this revision was ONE unconditional `check-fail`, pinned
//!    with a debug-assertions std. No compiler commit flipped it. On m14, whose
//!    stage 1 std has no debug assertions, it was red ("did not emit an error") on
//!    stage 1 of origin/main `361160e17a` and of `4463aeeb6d`: rc=0 with the rows
//!    above, and no row naming `mem::replace`. Stage 1 of `ee3f51541d` (before this
//!    item landed, same std) prints the same rows plus the count row, so the only
//!    row that changed on that std is the one this item's count derivation removes
//!    (`1851e76e2a`, landed in `ef6ec419d7`). Split by std, as
//!    `btree_range_order_charged.rs` is. `btree_range_debug_std` keeps the original
//!    pin and was not re-measured: no debug-assertions stage 1 exists on m14.
//!
//!  * `zst_map_source` / `zst_flat_map_source`: the NARROWING the self-check of
//!    this change found. `vec![(); n]` allocates nothing, so its length is
//!    bounded by no gated allocation; the leaf grant used to treat `&[()]` like any
//!    slice. `zst_map_source` built rc=0 BEFORE this change and `f(usize::MAX)`
//!    panicked "capacity overflow" (exit 101, verify-off run) — a false accept of
//!    the class unaimed-90 lists as a correct refusal when spelled `vec![0; n]`.
//!    `zst_flat_map_source` is the same hole through the new `flat_map` step.
//!  * `zst_enum_payload_source` (adversarial probe p29, fix round 2 of this item,
//!    2026-10-01): `Option<Infallible>` is zero-sized — `None` is its only value —
//!    but main's F3 allow-list read the VARIANTLESS enum `Infallible` (rendered as
//!    one synthetic `__tag` field and no variants) as a sized, inhabited struct, so
//!    the slice was a bounded source. Built rc=0 on main `07091c92c1` and on fix
//!    round 1; a `usize::MAX`-long slice (`set_len` on a `Vec` of the ZST) panicked
//!    "capacity overflow" (verify-off driver exit 101). Closed in
//!    `ty_is_definitely_nonzero_sized`/`ty_is_definitely_inhabited`
//!    (`adt_is_variantless_enum_rendering`).
//!
//! BEFORE (stage-1 snapshot `fb304b993`, two commits behind this branch's base
//! `3b30328c07`; neither intervening commit touches these lanes): `title_case` and
//! `lowercase_after_next` refused (flat_map `NOT-VANILLA`, fn-item `collect`
//! `NOT-VANILLA`, and `count-not-derivable` on every collect); `btree_range`
//! refused with 2 obligations not verified.

#[cfg(any(title_case, title_one_direct, title_one_direct_census))]
fn capitalize(word: &str) -> String {
    let mut chars = word.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars.flat_map(|c| c.to_lowercase())).collect(),
        None => String::new(),
    }
}

/// "hello WORLD foo" -> "Hello World Foo"
#[cfg(title_case)]
pub fn title_case(s: &str) -> String {
    //[title_case]~^ ERROR Trust strict verification failed for `iter_hof_collect_counts::title_case`: 1 obligation(s) were not fully verified
    s.split(' ').map(capitalize).collect::<Vec<_>>().join(" ")
}

#[cfg(capitalize_root)]
pub fn capitalize(word: &str) -> String {
    let mut chars = word.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars.flat_map(|c| c.to_lowercase())).collect(),
        None => String::new(),
    }
}

#[cfg(any(title_one_direct, title_one_direct_census))]
pub fn title_one(s: &str) -> String {
    //[title_one_direct]~^ ERROR Trust strict verification failed for `iter_hof_collect_counts::title_one`: 1 obligation(s) were not fully verified
    capitalize(s)
}

#[cfg(lowercase_after_next)]
pub fn tail_lower(word: &str) -> String {
    let mut chars = word.chars();
    let _ = chars.next();
    chars.flat_map(|c| c.to_lowercase()).collect()
}

#[cfg(flat_map_unbounded_fanout)]
pub fn expand(s: &str, k: usize) -> String {
    //[flat_map_unbounded_fanout]~^ ERROR Trust Level 0 safety verification incomplete
    //[flat_map_unbounded_fanout]~| ERROR Trust strict verification failed
    s.chars().flat_map(|c| std::iter::repeat(c).take(k)).collect()
}

#[cfg(any(btree_range, btree_range_certify, btree_range_debug_std))]
pub struct EventLog {
    events: std::collections::BTreeMap<u64, String>,
}

#[cfg(any(btree_range, btree_range_certify, btree_range_debug_std))]
impl EventLog {
    pub fn between(&self, from: u64, to: u64) -> Vec<&str> {
        //[btree_range]~^ WARN Trust verification advisory for `iter_hof_collect_counts::EventLog::between`: 1 obligation(s) were not fully verified
        //[btree_range]~| NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked
        //[btree_range]~| NOTE an unproven panic-freedom obligation for a call into std/core/alloc whose body is not in the lowered bundle
        //[btree_range_certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `iter_hof_collect_counts::EventLog::between`: 1 obligation(s) were not proved
        //[btree_range_certify]~| ERROR Trust strict verification failed for `iter_hof_collect_counts::EventLog::between`: 1 obligation(s) were not fully verified
        //[btree_range_certify]~| NOTE runtime-checked obligations lack a static proof and are not permitted under `-Z trust-policy=certify`
        //[btree_range_debug_std]~^^^^^^^ ERROR 2 obligation(s) were not fully verified
        if from >= to {
            return Vec::new();
        }
        self.events.range(from..to).map(|(_, m)| m.as_str()).collect()
    }
}

#[cfg(zst_map_source)]
pub fn f(n: usize) -> Vec<u8> {
    //[zst_map_source]~^ ERROR Trust Level 0 safety verification incomplete
    //[zst_map_source]~| ERROR Trust strict verification failed
    let v = vec![(); n];
    v.iter().map(|_| 1u8).collect()
}

#[cfg(zst_flat_map_source)]
pub fn f(n: usize) -> String {
    //[zst_flat_map_source]~^ ERROR Trust Level 0 safety verification incomplete
    //[zst_flat_map_source]~| ERROR Trust strict verification failed
    let v = vec![(); n];
    v.iter().flat_map(|_| 'A'.to_lowercase()).collect()
}

#[cfg(zst_enum_payload_source)]
pub fn f(v: &[Option<core::convert::Infallible>]) -> Vec<u8> {
    //[zst_enum_payload_source]~^ ERROR Trust Level 0 safety verification incomplete
    //[zst_enum_payload_source]~| ERROR Trust strict verification failed
    v.iter().map(|_| 1u8).collect()
}
