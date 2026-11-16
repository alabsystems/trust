// Yield-value guards for the iterator shapes whose element bounds are
// recoverable from MIR: integer ranges, `enumerate`, `slice::iter` and
// `str::char_indices`. Tracing a `next()` destination back to the iterator's
// construction site is what turns an opaque loop variable into a bounded one.

use super::*;

// ======================================================================
// Range-iterator yield facts (`for i in start..end { a[i] }`)
// ======================================================================
//
// rustc desugars a `for` loop over an exclusive range into a `Range::next`
// iterator: the loop variable `i` is bound as the `Some` payload of
// `<Range as Iterator>::next(&mut it)`. By the semantics of exclusive-range
// `next`, EVERY yielded value `v` satisfies `original_start <= v < end` (the
// iterator only advances forward, and an out-of-range/empty range yields `None`
// — the `None` arm, never the `Some` arm where `i` is read). So `start <= i <
// end` is a sound, loop-invariant fact about the payload. Emitting it discharges
// the `a[i]` bounds obligation, making the ubiquitous `for i in 0..s.len() {
// s[i] }` idiom PROVE instead of being false-refuted (an inferiority case: rustc
// accepts it). This mirrors the Ord::min/max/clamp call-result modeling above,
// but for the iterator's yielded value rather than a call's return.
//
// SOUNDNESS GATES (any miss → no fact, never a wrong one):
//   * Exact std `Range` yields `< end`; fixed-width integer `RangeInclusive`
//     yields `<= end`. Inclusive origins enter ONLY the yield-fact map, never
//     the exclusive trip-count/BMC API. `RangeFrom` remains unbounded/excluded.
//     A closed endpoint never becomes `end + 1`, including at the machine maximum.
//     The `Rev` and `StepBy` adapters ARE traced through (the call-hop below): their
//     `next` yields the SAME `[start, end)` value set or a subset, never outside it.
//   * The bounds come from the ORIGINAL constructor. Only the original yield
//     set is used: `next` consumes from it. Neither bound denotes iterator state.
//   * `into_iter` is treated as the identity ONLY when its argument traces to a
//     literal `Range` aggregate (for any `I: Iterator`, `into_iter(i) == i`, and
//     `Range: Iterator`); a non-Range `into_iter` (e.g. `Vec`) fails the
//     aggregate gate and emits nothing.
//   * THE PAYLOAD LOCAL IS GATED, NOT ASSUMED: `start <= payload < end` is a GLOBAL
//     fact keyed on the payload's BARE name (attached per-block independently of the
//     BFS guard map, whose loop-join weakening would otherwise drop it), and
//     `generate::safety` conjoins it BEFORE the version rename
//     (`conjoin_preconditions_versioned_at_point_recorded`), which rewrites the whole
//     row, so the bare name is versioned with the body: the fact binds to whichever
//     version of the payload is live at the row's use point in the block under proof
//     (the block terminal for an assert row). The hardened twin
//     (`hardened::append_assert_panic_vcs`) conjoins it the same way, before its own
//     rename at the block terminal (`conjoin_preconditions_versioned`). That is
//     a claim about EVERY value the name can hold, and it is licensed by
//     [`payload_carries_global_fact`] = `local_defs::is_single_static_assignment`:
//     the payload's writes on every channel must be exactly the one `Some`-payload
//     `Use` — no second whole write, no projected/discriminant write, no `&mut`/`&raw`
//     alias, no unlocatable write, and never a parameter. A `mut` pattern binding
//     falsifies the old "assigned exactly once (a fresh for-binding temp)" assumption:
//     `for mut i in 0..5usize { i = n; t = a[i]; }` lowers to `_10 = ((_7 as Some).0);
//     _10 = _2; _12 = _10; assert(Lt(_12, 5))`, and with the fact minted on the bare
//     `i` the rename bound `0 <= i < 5` to the POST-reassignment version, the path
//     went UNSAT, and the bounds row was PROVED and kernel-certified on the pristine
//     driver while `payload_param_for(&a, 50)` panics. Eleven probes proved that way
//     (`for`/`if let`/conditional/`i += 1`/signed/`enumerate`/`windows` forms); all are
//     pinned on real MIR in `tests/escaped_local_seam_realmir.rs` (the `payload_*`
//     rows). A payload that fails the gate gets NO fact — never a refutation from an
//     invented one — and the `Option` local above it is gated by [`next_call_receivers`]
//     (its writes must be `next` calls and nothing else), so no hop below the payload
//     carries a first-write assumption: the index temp `_12 = _10` is an in-block
//     definition the block encoder equates, not a name a fact is keyed on.
//   * A `next` RESULT written by SEVERAL `Iterator::next` calls (`let o = if c {
//     small.next() } else { big.next() }`) is admitted as a JOIN, never attributed to
//     one call: `local_defs::value_calls` requires that the calls are the local's ONLY
//     write channels, EVERY receiver must trace through the same gates, and the fact
//     is the DISJUNCTION of the per-receiver yield facts (see
//     [`build_range_yield_guard_map`]). One receiver that does not trace withholds
//     the whole fact. The call-through-temp spelling rustc emits for a loop-carried
//     `o = it.next()` (`_12 = next(..); _4 = move _12`) is admitted by the same seam
//     question (`local_defs::body_call_through_temp_index`) as one more producing call.
//   * A `__slice_len` TERM IS A NAME, NOT A VALUE. `slice_len_formula(s)` returns the
//     variable `{s}__slice_len`, and `path_defs::write_covers_derived_slice_len` makes
//     every whole write of `s` a write of that derived name too: the version rename
//     rebinds it exactly as it rebinds `s`. So a range END or an enumerate SLICE that
//     resolves to `{s}__slice_len` inlines a NAME into the payload's fact, and the
//     fact `i < s__slice_len` is a claim about every version of `s` — false the moment
//     `s` is reseated inside the loop. `for i in 0..s.len() { s = &a[..1]; s[i] }`
//     (`len_method_reseat`, `len_ufcs_param_reseat` on a `mut` parameter, the
//     `enumerate` twins) PROVED and kernel-certified at `-Copt-level=1`, where
//     `PtrMetadata(copy s)` names the user's local directly; at `-O0` rustc's copy temp
//     (`_7 = copy _2; PtrMetadata(move _7)`) keyed the name on a single-write temp and
//     shielded it BY ACCIDENT, not by the gate. The licence is ONE question, shared by
//     every producer that inlines a length (`generate::slice_len_licence`, round A8 —
//     the min/max, modulo and division lanes inlined the same name licensed by
//     `is_parameter` alone and proved `let n = s.len().min(100); s = b; s[..n]`
//     kernel-certified): the place OWNING the metadata (the fat pointer;
//     `metadata_owner`) must be `local_defs::path_is_single_static_assignment` —
//     bound once, never aliased at or above the path, writes strictly inside it
//     (`(*s)[i] = v`, `&raw const (*s)`) ignored — and so must every place the block
//     encoder's length ties can equate it with (the whole-local `Use`/`Ref`/
//     `CopyForDeref` chain from the owner's root, re-rooted through a projected
//     owner); an `as_bytes` redirect is followed to the receiver it is keyed on. A
//     chain that ends at a constant-length place (`&[T; N]`, a const-generic array) is
//     stable by construction. The fact is stated on EVERY licensed spelling of the end
//     — the root's canonical name (`callee_summaries::param_slice_len`) and the read
//     temp's own (`resolve_range_bound_alias_formulas`) — because the obligation reads
//     whichever the bounds check canonicalizes to. A miss withholds the fact outright
//     — the bare SSA bound local (`let n = s.len()`, `let_n_reseat`) is NOT
//     substituted for it either, see `resolve_range_bound_formula` — so the payload
//     stays unpinned and the callee-return havoc lane can decline the row to Unknown
//     instead of refuting it on an ungrounded length.
/// `Some(payload)` extraction projection `(_x as Downcast(1)).Field(0)`.
/// In `Option<T>`, `Some` is variant index 1 with a single field 0.
pub(super) fn is_some_payload_projection(projections: &[trust_types::Projection]) -> bool {
    matches!(projections, [trust_types::Projection::Downcast(1), trust_types::Projection::Field(0)])
}

/// Strip every `<…>` group (generic args, `<impl u8>` segments, qualified-self
/// prefixes) and re-join the non-empty `::` segments — the same normalization
/// discipline as trust-ir-bridge's `strip_generics`, local to vcgen because the
/// two crates deliberately share no utility surface.
///
/// Trust (W4 ITER-HOF (c), 2026-09-25): the `>` of an ARROW is not a bracket. A
/// function ITEM or pointer type inside a turbofish carries one —
/// `<Split<'_, char> as core::iter::traits::iterator::Iterator>::map::<String,
/// for<'_> fn(&'_ str) -> String {m3::ident}>` is how `s.split(' ').map(ident)`
/// renders — and counting it closed the group one character early, so the rest of
/// the turbofish (` String {m3::ident}`) leaked into the "stripped" path and every
/// recognizer keyed on it missed. MEASURED: that is why `split(' ').map(ident)
/// .collect()` minted `UnboundedAllocation::Iterator::collect::count-not-derivable`
/// while the byte-identical closure spelling `.map(|w| ident(w))` did not — the
/// bounded-source walk could not authenticate `map` as a std adaptor. The same
/// defect was closed for the reverse scan in `method_tail` and in
/// `sep_engine::strip_turbofish_args`; this is the forward scan's twin. It is a
/// PARSE repair: a correctly delimited group is dropped whole, exactly as any
/// other generic argument always was, and no recognizer's own gate changes.
struct GenericsStripper;

impl GenericsStripper {
    /// Zero-allocation fast path when every `<…>` group sits at the tail of `s`
    /// (`Trait<Args>`, `Adt<Args>`, `fn_name::<Args>`, `sink::<Args>::<__trust_elem_bytes@N>`),
    /// returning the borrowed prefix with any turbofish `::` stripped.
    #[inline]
    fn try_trailing(s: &str) -> Option<&str> {
        let lt_idx = s.find('<')?;
        let prefix = &s[..lt_idx];
        if prefix.is_empty()
            || prefix.starts_with(':')
            || prefix.contains('>')
            || prefix.contains(":::")
        {
            return None;
        }
        let trimmed = prefix.strip_suffix("::").unwrap_or(prefix);
        if trimmed.is_empty() || trimmed.ends_with(':') {
            return None;
        }
        let tail = s[lt_idx..].as_bytes();
        let mut i = 0usize;
        let mut depth = 0usize;
        while i < tail.len() {
            if depth == 0 {
                if tail[i] == b'<' {
                    depth = 1;
                    i += 1;
                    continue;
                }
                if tail[i..].starts_with(b"::<") {
                    depth = 1;
                    i += 3;
                    continue;
                }
                return None;
            }
            match tail[i] {
                b'<' => depth += 1,
                b'>' if i > 0 && tail[i - 1] == b'-' => {}
                b'>' => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        Some(trimmed)
    }
}

pub(super) fn vc_strip_generics_cow(s: &str) -> std::borrow::Cow<'_, str> {
    if !s.as_bytes().iter().any(|&b| b == b'<' || b == b'>') && !s.contains(":::") {
        return std::borrow::Cow::Borrowed(s.trim_matches(':'));
    }
    if let Some(stripped) = GenericsStripper::try_trailing(s) {
        return std::borrow::Cow::Borrowed(stripped);
    }
    let bytes = s.as_bytes();
    let mut without_generics = String::with_capacity(s.len());
    let mut depth = 0usize;
    let mut run_start = 0usize;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'<' => {
                if depth == 0 && i > run_start {
                    without_generics.push_str(&s[run_start..i]);
                }
                depth += 1;
            }
            // The arrow's `>`: text, never a closing bracket.
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' => {
                if depth > 0 {
                    depth -= 1;
                    if depth == 0 {
                        run_start = i + 1;
                    }
                } else {
                    if i > run_start {
                        without_generics.push_str(&s[run_start..i]);
                    }
                    run_start = i + 1;
                }
            }
            _ => {}
        }
    }
    if depth == 0 && run_start < s.len() {
        without_generics.push_str(&s[run_start..]);
    }
    if !without_generics.contains(":::")
        && !without_generics.starts_with(':')
        && !without_generics.ends_with(':')
    {
        return std::borrow::Cow::Owned(without_generics);
    }
    let mut out = String::with_capacity(without_generics.len());
    for seg in without_generics.split("::").filter(|seg| !seg.is_empty()) {
        if !out.is_empty() {
            out.push_str("::");
        }
        out.push_str(seg);
    }
    std::borrow::Cow::Owned(out)
}

pub(super) fn vc_strip_generics(callee: &str) -> String {
    vc_strip_generics_cow(callee).into_owned()
}

/// Single-pass decomposition of a qualified callee spelling
/// `<Recv as TraitPath>::method[::<…>]` or `<Recv>::method`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ParsedQualifier<'a> {
    pub(super) inner: &'a str,
    pub(super) self_ty: &'a str,
    pub(super) trait_path: Option<&'a str>,
    pub(super) method: &'a str,
}

impl<'a> ParsedQualifier<'a> {
    #[inline]
    pub(super) fn parse(callee: &'a str) -> Option<Self> {
        let rest = callee.strip_prefix('<')?;
        // Find both the matching top-level close of the opening `<` and the last
        // depth-1 ` as ` split inside the qualifier in a single ASCII byte scan.
        // An arrow's `>` (`<Map<I, fn(&str) -> String {f}> as Iterator>::collect`)
        // is not a bracket — see `vc_strip_generics`.
        let bytes = rest.as_bytes();
        let mut depth = 1usize;
        let mut close = None;
        let mut as_split = None;
        for (i, &b) in bytes.iter().enumerate() {
            match b {
                b'<' => depth += 1,
                b'>' if i > 0 && bytes[i - 1] == b'-' => {}
                b'>' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(i);
                        break;
                    }
                }
                b' ' if depth == 1 && bytes[i..].starts_with(b" as ") => {
                    as_split = Some(i);
                }
                _ => {}
            }
        }
        let close = close?;
        let method = rest[close + 1..].strip_prefix("::")?;
        let inner = &rest[..close];
        Some(match as_split {
            Some(split) => {
                Self { inner, self_ty: &inner[..split], trait_path: Some(&inner[split + 4..]), method }
            }
            None => Self { inner, self_ty: inner, trait_path: None, method },
        })
    }
}

/// Split a QUALIFIED callee spelling into its qualifier group and its method:
/// `<Recv as TraitPath>::method[::<…>]` -> `("Recv as TraitPath", "method…")`,
/// `<Recv>::method` -> `("Recv", "method…")`. `None` for an unqualified path.
///
/// ONE parser for the qualified spelling. Both [`vc_qualified_trait_method`]
/// (which needs the TRAIT half) and [`vc_qualified_self_ty`] (which needs the
/// SELF half) route through it, so the two halves can never disagree about where
/// the qualifier ends.
#[cfg_attr(not(test), allow(dead_code))]
fn vc_qualifier_group(callee: &str) -> Option<(&str, &str)> {
    let q = ParsedQualifier::parse(callee)?;
    Some((q.inner, q.method))
}

/// Parse the QUALIFIED impl spelling `<Recv as TraitPath>::method[::<…>]`,
/// returning `(TraitPath, method)`. The trait path may itself contain `::` and
/// nested `<…>`; the receiver/trait split is the LAST top-level-within-the-
/// qualifier ` as `, and the method is everything after the qualifier's closing
/// `>::` (trailing turbofish stripped by the caller via [`vc_strip_generics`]).
pub(super) fn vc_qualified_trait_method(callee: &str) -> Option<(&str, &str)> {
    let q = ParsedQualifier::parse(callee)?;
    Some((q.trait_path?, q.method))
}

/// The SELF (receiver) type of a qualified callee spelling — the OTHER half of
/// [`vc_qualified_trait_method`]'s split, and the half that carries the identity
/// of the value the method is called ON.
///
/// `<alloc::vec::Vec<u8> as core::iter::…::IntoIterator>::into_iter` -> `alloc::vec::Vec<u8>`
/// `<[u8]>::iter` (a qualifier with no ` as `) -> `[u8]`
/// `core::slice::<impl [u8]>::iter` (unqualified) -> `None`
///
/// WHY THIS EXISTS. `trust_types::path_root_is_authenticated_sysroot_crate` is a
/// ROOT test and says so: *a caller holding a qualified spelling must split it*.
/// A caller that instead anchors the RAW qualified string refuses every
/// `<Self as Trait>::m` callee out of hand, because such a string starts with
/// `<` — and `.into_iter()` is ALWAYS that spelling. Anchoring the TRAIT half
/// is not a substitute for anchoring the SELF half and vice versa: for
/// `<mycrate::Endless as core::iter::…::IntoIterator>::into_iter` the trait half
/// authenticates perfectly while the receiver is a user type, and for
/// `<alloc::vec::Vec<u8> as mycrate::MyTrait>::into_iter` it is the other way
/// round. Each caller anchors the half its own claim is about.
pub(super) fn vc_qualified_self_ty(callee: &str) -> Option<&str> {
    Some(ParsedQualifier::parse(callee)?.self_ty)
}

/// Peel the reference/raw-pointer prefixes rustc renders in front of a type
/// (`&`, `&'a `, `&mut `, `&'a mut `, `*const `, `*mut `), so the ROOT of
/// `&'a alloc::vec::Vec<u8>` is read from `alloc::vec::Vec<u8>`.
///
/// A reference's collection/iterator identity is its pointee's — `(&vec)
/// .into_iter()` yields the vec's elements — so peeling is exactly the
/// normalization the receiver anchor needs, and it is the same rule
/// `alloc_vcs::ty_is_authenticated_std_iterator` applies to `Ty::Ref`.
pub(super) fn vc_peel_reference_prefixes(ty: &str) -> &str {
    let mut ty = ty.trim();
    loop {
        let next = if let Some(r) = ty.strip_prefix('&') {
            let r = r.trim_start();
            // an explicit lifetime, e.g. `&'a T` / `&'_ T`
            let r = match r.strip_prefix('\'') {
                Some(after) => match after.find(char::is_whitespace) {
                    Some(i) => after[i..].trim_start(),
                    None => "",
                },
                None => r,
            };
            r.strip_prefix("mut ").map_or(r, str::trim_start)
        } else if let Some(r) = ty.strip_prefix("*const ") {
            r
        } else if let Some(r) = ty.strip_prefix("*mut ") {
            r
        } else {
            return ty;
        };
        let next = next.trim();
        if next == ty {
            return ty;
        }
        ty = next;
    }
}

/// Authenticate a std ITERATOR-PROTOCOL trait method across every spelling the
/// extractor produces:
///  * the GENERIC trait-fn path `…::{Trait}::{method}` — accepted only when the
///    trait path is CRATE-ANCHORED to `core::iter::`/`std::iter::` (the historical
///    bare `ends_with("Iterator::next")` accepted a USER trait named `Iterator`
///    too — a latent unsound-fact accept this rewrite closes);
///  * the QUALIFIED impl spelling `<Recv as TraitPath>::{method}` where
///    `TraitPath` is a `core::iter::`/`std::iter::`-anchored path whose last
///    segment is `{trait_last}` (the definition-path renderer emits
///    `core::iter::traits::iterator::Iterator` — the spelling whose silent
///    mismatch dropped the range/step_by/enumerate yield facts and turned
///    provably-safe loops into FALSE counterexamples).
///
/// A short qualified spelling such as `<Range as Iterator>::next` is not
/// authoritative: a user trait may have that same final segment and may be
/// implemented for the standard Range type. The trailing `::` in each accepted
/// namespace prefix is likewise load-bearing: `core::iteration::Iterator` is
/// not the standard iterator trait.
///
/// NAME-ONLY: every caller keeps its own receiver/aggregate trace as the
/// load-bearing soundness gate, exactly as before.
pub(super) fn vc_callee_is_std_iter_trait_method(
    callee: &str,
    trait_last: &str,
    method: &str,
) -> bool {
    if super::method_tail(callee) != method
        || !(callee.contains("core::iter::") || callee.contains("std::iter::"))
        || !callee.contains(trait_last)
    {
        return false;
    }
    if callee.starts_with('<') {
        if let Some((trait_path, m)) = vc_qualified_trait_method(callee) {
            let trait_path = vc_strip_generics_cow(trait_path);
            let m = vc_strip_generics_cow(m);
            return m == method
                && (trait_path.starts_with("core::iter::") || trait_path.starts_with("std::iter::"))
                && trait_path.rsplit("::").next() == Some(trait_last);
        }
        return false;
    }
    let normalized = vc_strip_generics_cow(callee);
    if let Some(trait_path) = normalized.strip_suffix(method).and_then(|s| s.strip_suffix("::"))
        && (trait_path.starts_with("core::iter::") || trait_path.starts_with("std::iter::"))
        && trait_path.rsplit("::").next() == Some(trait_last)
    {
        return true;
    }
    false
}

pub(super) fn vc_callee_is_std_iter_trait_method_any(
    callee: &str,
    trait_last: &str,
    methods: &[&str],
) -> bool {
    if !methods.contains(&super::method_tail(callee))
        || !(callee.contains("core::iter::") || callee.contains("std::iter::"))
        || !callee.contains(trait_last)
    {
        return false;
    }
    if callee.starts_with('<') {
        if let Some((trait_path, m)) = vc_qualified_trait_method(callee) {
            let trait_path = vc_strip_generics_cow(trait_path);
            if !(trait_path.starts_with("core::iter::") || trait_path.starts_with("std::iter::"))
                || trait_path.rsplit("::").next() != Some(trait_last)
            {
                return false;
            }
            let m = vc_strip_generics_cow(m);
            return methods.contains(&m.as_ref());
        }
        return false;
    }
    let normalized = vc_strip_generics_cow(callee);
    let Some((trait_path, m)) = normalized.rsplit_once("::") else {
        return false;
    };
    methods.contains(&m)
        && (trait_path.starts_with("core::iter::") || trait_path.starts_with("std::iter::"))
        && trait_path.rsplit("::").next() == Some(trait_last)
}

/// Authenticate an INHERENT `<[T]>` slice method: the callee is DEFINED in a real
/// sysroot crate (its compiler-minted `callee_key`), is not a trait method, and
/// generic-strips to `core::slice::{method}` / `std::slice::{method}` — both the
/// generic `core::slice::<impl [T]>::{method}` and the monomorphized
/// `core::slice::<impl [u8]>::{method}` do. Inherent impls on primitives exist
/// only in std, so the anchored form is authoritative.
///
/// Trust (2026-10-04, SLICE-INHERENT-1): the key gate is new, and the arm that
/// accepted `[T]` ANYWHERE plus a `::{method}` leaf is gone. That arm matched a
/// user method whose OWNER is instantiated at a slice — `impl<S: ?Sized> W<S> {
/// fn windows(&self, n: usize) -> It }` called in `fn f<T>(w: &W<[T]>)` renders
/// `crate::W::<[T]>::windows` — and every consumer then minted std's yield fact
/// for the user's iterator: `len(win) == n` (`windows`/`chunks_exact`),
/// `1 <= len <= n` (`chunks`), `i < len(s)` (`iter().enumerate()`), and a trip
/// count of `N` (`iter` over `&[T; N]`). Measured on `scratchpad/stage1-w11fix`:
/// each read `slice proved` or `overflow:add proved` (the trip twin's overflow
/// check ELIDED) on a user iterator that runs past the bound. The `[T]` arm
/// added nothing for std, whose generic spelling the anchored arm already
/// covers.
pub(super) fn vc_callee_is_slice_inherent(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
    method: &str,
) -> bool {
    // Trust (2026-09-29, composed with SLICE-INHERENT-1): an unauthenticated crate
    // stamp refuses too, whatever the key says.
    if !trust_types::CalleeKey::opt_is_real_sysroot(callee_key)
        || !(callee.starts_with("core::slice::") || callee.starts_with("std::slice::"))
        || !callee.contains(method)
        || callee.contains(" as ")
        || trust_types::path_has_unauthenticated_crate_stamp(callee)
    {
        return false;
    }
    let normalized = vc_strip_generics_cow(callee);
    (normalized.starts_with("core::slice::") || normalized.starts_with("std::slice::"))
        && normalized.strip_suffix(method).is_some_and(|s| s.ends_with("::"))
}

pub(super) fn vc_callee_is_slice_inherent_any(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
    methods: &[&str],
) -> bool {
    if !trust_types::CalleeKey::opt_is_real_sysroot(callee_key)
        || !(callee.starts_with("core::slice::") || callee.starts_with("std::slice::"))
        || callee.contains(" as ")
        || trust_types::path_has_unauthenticated_crate_stamp(callee)
    {
        return false;
    }
    let normalized = vc_strip_generics_cow(callee);
    let Some((_, m)) = normalized.rsplit_once("::") else {
        return false;
    };
    (normalized.starts_with("core::slice::") || normalized.starts_with("std::slice::"))
        && methods.contains(&m)
}

/// Authenticate an inherent method on the canonical `alloc`/`std` `Vec`.
/// A user free function whose path merely mentions `Vec`, or a user trait impl
/// on `Vec`, must not mint empty-start/push/length facts.
pub(super) fn vc_callee_is_std_vec_inherent(callee: &str) -> bool {
    if callee.contains(" as ") {
        return false;
    }
    let normalized = callee.strip_prefix('<').unwrap_or(callee);
    normalized.starts_with("alloc::vec::Vec") || normalized.starts_with("std::vec::Vec")
}

pub(super) fn callee_is_iterator_next(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "next")
}

pub(super) fn callee_is_into_iter(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "IntoIterator", "into_iter")
}

/// `Iterator::rev`. `Rev<Range>::next` yields EXACTLY the values of the inner
/// `[start, end)` range (in reverse order), so the yield invariant
/// `start <= v < end` holds identically — `rev` is transparent for tracing the
/// underlying Range. (Only `rev`: value-transforming adapters like `map`/`filter`
/// would be UNSOUND to hop, and the Range-aggregate gate would not stop them.)
pub(super) fn callee_is_rev(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "rev")
}

/// `Iterator::step_by`. `StepBy<Range>::next` yields a SUBSET of the inner `[start, end)`
/// range (`start`, `start+k`, … while `< end`), so the yield invariant `start <= v < end`
/// holds identically — transparent for tracing the underlying Range like `rev`. Unlike `rev`
/// it is a TWO-arg call (`step_by(self_iter, step)`); the inner iterator is `args[0]`. The
/// `step` never widens the value set (any `step >= 1` yields a subset; `step == 0` PANICS
/// inside `step_by` before any value is yielded, so a yielded `v`'s invariant stays sound).
pub(super) fn callee_is_step_by(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "step_by")
}

/// EXCLUSIVE `std::ops::Range` only — NOT `RangeInclusive` (yield `<= end`),
/// `RangeFrom`, etc. The exclusive-range yield invariant is `start <= v < end`.
pub(super) fn aggregate_is_exclusive_range(name: &str) -> bool {
    range_family_adt_name(name) == Some("Range")
}

/// Canonical Range-family identity across rustc path-printing versions.
///
/// Older extracted MIR used the public re-export spelling `core::ops::RangeTo`;
/// current rustc emits an instantiated defining-module spelling such as
/// `core::ops::range::RangeTo<usize>`. These are the same lang-library ADT.
/// Strip instantiated generic groups, then match only the exact `core`/`std`
/// defining/re-export paths (never a user type whose tail happens to be
/// `RangeTo`) so a compiler path-format change cannot silently delete the
/// slice-index panic obligation or broaden the trusted recognizer.
pub(super) fn range_family_adt_name(name: &str) -> Option<&'static str> {
    if !(name.starts_with("core::ops::") || name.starts_with("std::ops::"))
        || !name.contains("Range")
    {
        return None;
    }
    let stripped = vc_strip_generics_cow(name);
    let tail = ["core::ops::range::", "std::ops::range::", "core::ops::", "std::ops::"]
        .into_iter()
        .find_map(|prefix| stripped.strip_prefix(prefix))?;
    match tail {
        "Range" => Some("Range"),
        "RangeTo" => Some("RangeTo"),
        "RangeFrom" => Some("RangeFrom"),
        "RangeInclusive" => Some("RangeInclusive"),
        "RangeFull" => Some("RangeFull"),
        // Trust (2026-09-25, std-range-family): `..=b`. Not an iterator, so the
        // bounded-source lanes never see it; the slice-index and BTree `range`
        // lanes already named it and silently never matched.
        "RangeToInclusive" => Some("RangeToInclusive"),
        _ => None,
    }
}

/// Trust: 2026-09-16 — THE ORIGIN HOP. The definition an ITERATOR local was built
/// from, for the tracers in this family and nowhere else.
///
/// The value resolver `local_defs::unique_value_def` refuses a local with a
/// `&mut`/`&raw` alias (`LocalWrite::Escape`), because a store through the alias
/// can make the one `Assign` it saw stale — `x3::pesc`, a kernel-certified false
/// proof, closed 2026-09-15. Every Rust `for` loop is on that channel: the
/// `Iterator::next` desugar borrows `&mut iter` once per iteration, so the loop's
/// iterator local (`_5 = move _4; _7 = &mut _5; next(move _7)`) has an initializer
/// the resolver will not hand back, and the tracers below stopped at it.
///
/// This helper asks `local_defs::unique_initializing_def` instead — "what was this
/// local BUILT FROM" — and that question's contract requires the CALLER to argue
/// that the part of the answer it reads survives every write that can arrive
/// through the alias. The argument, which every consumer of this hop inherits:
///
///  1. [`iter_mut_borrows_only_feed_next`] is an affirmative allow-list: every
///     `&mut`/`&raw` conduit of `local` is defined once, is never read, written
///     through, dropped, or passed anywhere except as argument 0 of a std
///     `Iterator::next` call. The initializing def is the local's ONLY other write
///     (the origin question refuses a second whole write, a call destination, a
///     projected/discriminant/deinit write and an unlocatable write). So the ONLY
///     mutation `local` ever undergoes is `Iterator::next` on itself.
///  2. `Iterator::next` on the std iterators these tracers accept (`Range`,
///     the yield-only integer `RangeInclusive` extension,
///     `Rev<Range>`, `StepBy<Range>`, `slice::Iter`, `Enumerate<slice::Iter>`,
///     `Windows`/`Chunks`/`ChunksExact`) CONSUMES from the iterator and never
///     reseats it onto another collection. Hence every value it yields is a value
///     the ITERATOR IT WAS BUILT FROM would have yielded — the YIELD SET of the
///     initializer contains the yield set at every later `next` — and the number
///     of yields is at most the initializer's. The callee identity is pinned by the
///     tracers' own gates: the trace bottoms out in a `core::ops::Range` aggregate,
///     a `<[T]>::iter`/`windows`/`chunks*` call or an array-typed `into_iter`
///     argument, and no user impl can attach to those receiver types.
///
/// What the argument does NOT give, and what the tracers therefore withhold:
///
///  * the iterator's STATE. `Range::next` advances `start` and `Rev::next` retracts
///    `end`, so neither operand of the origin aggregate is the current field. The
///    range tracer's consumers read only what the yield-set argument licenses:
///    `start <= v < end` of every yield (every yield of a `Range{s, e}`, however far
///    consumed, is an element of `[s, e)`) and an UPPER bound `e - s` on the trip
///    count. The first recovery withheld `start` across this hop out of caution
///    about a consumer that would read it as position; measured, no consumer does,
///    and the withholding cost `for i in 0..5i32 { a[i as usize] }` its proof. The
///    decision to admit it, and what stays unlicensed, is written on
///    [`RangeOrigin`].
///  * EXACTNESS of the trip count. `let mut it = 0..8; it.next(); for i in it {}`
///    passes gate 1 (both `&mut it` conduits feed `next`) and runs SEVEN times; the
///    origin says eight. `end - start` through this hop is an over-approximation,
///    which is what `build_accumulator_bound_facts` needs (a bound of the form
///    `acc <= init + K * max` is monotone in `K`) and what the BMC refutation lane
///    must NOT take — it unrolls EXACTLY `K` iterations and fences that itself with
///    `body_is_straight_line_reduction`'s single-`next`-site requirement.
///
/// The pesc shape cannot pass: `m` is not an iterator, its conduit `p` is written
/// through (`*p = ..`), and gate 1 refuses a write rooted at a conduit. Pinned by
/// `tests/escaped_local_seam_realmir.rs` on the real compiler's MIR.
pub(super) fn iterator_origin_def(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    let def = crate::local_defs::unique_initializing_def(func, local)?;
    iter_mut_borrows_only_feed_next(func, local).then_some(def)
}

/// The exclusive-`Range` aggregate an iterator was traced back to: its `start` and
/// `end` operands, read as the bounds of the iterator's YIELD SET and as nothing else.
///
/// Every value the iterator yields, however far it has been consumed, satisfies
/// `start <= v < end`, and it yields at most `end - start` values. Both halves are
/// licensed by the same argument ([`iterator_origin_def`]'s): under the conduit gate the
/// iterator's only mutation is `Iterator::next` on itself, which consumes from — and
/// never adds to — the yield set of the `Range{start, end}` it was built from; `Rev`
/// yields the same set, `StepBy` a subset, `into_iter` is the identity.
///
/// # The `start` decision (2026-09-16), and what is NOT licensed
///
/// The first recovery WITHHELD `start` across the origin hop (this field was an
/// `Option`, `None` there), so that no consumer could read it as the iterator's
/// POSITION: `Range::next` advances the aggregate's `start` field, so after one
/// `next` the initializer's `start` is stale AS STATE. Measured cost: `for i in
/// 0..5i32 { a[i as usize] }` went from 2 proved to Unknown on the pristine driver's
/// own MIR, because the bounds row needs `i >= 0` before the `as usize` cast and only
/// `i < 5` was minted. The adversarial re-review asked for the decision to be made and
/// pinned. It is made here: `start` IS admitted, because every consumer of this struct
/// reads it as a YIELD fact, never as state —
///
///  * `build_range_yield_guard_map` and `overflow_vc::v2_bv_yield_constraints` mint
///    `start <= payload` on the `Some` payload of `next` — a fact about a yielded
///    value, true of every element of the yield set;
///  * `loop_bounds::range_trip_count_upper_bound` reads `end - start` as an UPPER
///    bound on the number of yields — the cardinality of the yield set, which a
///    stray `next` before the loop can only shrink (`stray_next`: 8 read, 7 real);
///  * of the two callers of `loop_bounds::loop_var_const_range` — which surfaces `start` as an
///    `Option<i128>`, `Some` only for a CONSTANT start — `loop_bounds::build_flattened_index_facts`
///    discards it and reads `end` only, while `overflow_vc::v2_bv_yield_constraints` (the bullet
///    above) uses a `Some` start as the yield fact `start <= y` and emits nothing on `None`.
///
/// `Range::next` yields `start, start+1, .., end-1` and nothing else, so `v >= start`
/// holds of every yield with the same force as `v < end`; withholding one and not the
/// other was caution about a consumer that does not exist. What remains unlicensed,
/// and what no consumer may add: reading `start` as the CURRENT position of the
/// iterator (it is not — `stray_next` pins that a `next` before the loop is admitted),
/// or `end - start` as an EXACT trip count (the BMC lane fences exactness itself).
/// The pin for the decision is `tests/escaped_local_seam_realmir.rs::
/// a_signed_range_index_cast_to_usize_proves_again`, with the measured verdicts on it.
#[derive(Clone, Copy, Debug)]
pub(super) struct RangeOrigin<'a> {
    pub(super) start: &'a Operand,
    pub(super) end: &'a Operand,
}

/// Trace the receiver of an `Iterator::next` call back to the originating
/// exclusive-`Range` aggregate. Walks the for-loop desugaring `next(&mut it)` ->
/// `it = into_iter(range)` -> `range = Range { start, end }` through whole-local
/// Ref/Use copies and the single `into_iter` call, bounded by `fuel`. Returns None
/// on any ambiguity. A hop through [`iterator_origin_def`] — the for-loop iterator
/// local, whose `&mut` conduit feeds `next` — is admitted; the result is the yield
/// set's bounds, see [`RangeOrigin`] for what that does and does not license.
pub(super) fn trace_local_to_range_aggregate(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<RangeOrigin<'_>> {
    // Preserve the exclusive-only contract used by trip-count and BMC consumers.
    trace_local_to_range_yield_origin(func, local, fuel, false)
        .map(|origin| RangeOrigin { start: origin.start, end: origin.end })
}

/// Bounds of yielded integer values only. An inclusive endpoint licenses `v <= end`,
/// never `v < end`, `end + 1`, iterator state, an exact trip count, or a witness.
#[derive(Clone, Copy, Debug)]
struct RangeYieldOrigin<'a> {
    start: &'a Operand,
    end: &'a Operand,
    end_inclusive: bool,
}

/// The inclusive extension accepts only extracted, fixed-width machine integers.
/// Do not infer a target width for an unresolved `PtrSizedInt`, or give a custom
/// `Step` implementation integer-order facts merely because it lives in a range.
fn inclusive_bounds_are_machine_integers(
    func: &VerifiableFunction,
    start: &Operand,
    end: &Operand,
) -> bool {
    let Some(start_ty) = crate::operand_ty_cow(func, start) else { return false };
    let Some(end_ty) = crate::operand_ty_cow(func, end) else { return false };
    matches!(start_ty.as_ref(), Ty::Int { width: 8 | 16 | 32 | 64 | 128, .. }) && start_ty == end_ty
}

fn trace_local_to_range_yield_origin(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
    allow_inclusive: bool,
) -> Option<RangeYieldOrigin<'_>> {
    if fuel == 0 || crate::local_defs::is_parameter(func, local) {
        return None;
    }
    // (a) A statement definition of this whole local — the seam's VALUE resolver first;
    // when that declines, the seam's ORIGIN question under `iterator_origin_def`'s gate.
    let def = crate::local_defs::unique_value_def(func, local)
        .or_else(|| iterator_origin_def(func, local));
    if let Some(rvalue) = def {
        return match rvalue {
            Rvalue::Aggregate(
                trust_types::AggregateKind::Adt { name, variant: 0, .. },
                operands,
            ) if aggregate_is_exclusive_range(name) && operands.len() == 2 => {
                Some(RangeYieldOrigin {
                    start: &operands[0],
                    end: &operands[1],
                    end_inclusive: false,
                })
            }
            Rvalue::Aggregate(
                trust_types::AggregateKind::Adt { name, variant: 0, .. },
                operands,
            ) if allow_inclusive
                && range_family_adt_name(name) == Some("RangeInclusive")
                && operands.len() == 3
                && matches!(operands[2], Operand::Constant(ConstValue::Bool(false)))
                && inclusive_bounds_are_machine_integers(func, &operands[0], &operands[1]) =>
            {
                Some(RangeYieldOrigin {
                    start: &operands[0],
                    end: &operands[1],
                    end_inclusive: true,
                })
            }
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_range_yield_origin(func, place.local, fuel - 1, allow_inclusive)
            }
            // Trust (2026-10-03): a REBORROW `&mut (*q)` points wherever `q` points, so it
            // traces as `q` (whose own `&mut iter` definition the arm above follows). The
            // pre-optimization MIR the whole-crate summaries are extracted from
            // (`mir_drops_elaborated_and_const_checked`) spells a `for` loop's receiver
            // `_11 = &mut iter; _10 = &mut (*_11); next(_10)`, and without this hop no
            // range-loop payload traced there (the optimized body has one `&mut iter`).
            // It names the same iterator; the iterator's own origin stays under
            // `iterator_origin_def`'s conduit gate below, so a reseat through the
            // reborrow still fails closed.
            Rvalue::Ref { place, .. } if place.projections.as_slice() == [Projection::Deref] => {
                trace_local_to_range_yield_origin(func, place.local, fuel - 1, allow_inclusive)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_range_yield_origin(func, p.local, fuel - 1, allow_inclusive)
            }
            _ => None,
        };
    }
    // (b) Otherwise the local is a call destination. `into_iter` is identity,
    // and `rev` preserves the underlying exclusive/inclusive yield set. The
    // constructor and every adapter hop use the same write-channel gate.
    //
    // THE CALL-DESTINATION HOP IS GATED (`call_dest_hop`): the one `Call` must be the
    // local's ONLY write channel. Until 2026-09-16 this arm took the FIRST call writing
    // the local, so `let mut r = (0..5).rev(); r = (0..100).rev(); for i in r { a[i] }`
    // traced to `Range{0, 5}` and PROVED `a[i]` in range on a `[u8; 5]` — kernel-
    // certified on the pristine driver — while the program indexes 99. See
    // [`call_dest_hop`] for the channel argument and the five measured witnesses.
    let (callee, args) = call_dest_hop(func, local)?;
    // `a..=b` is a constructor call in the original Clean canary's real MIR.
    // Reuse the existing exact std identity gate and the same all-write-channel
    // origin hop as every iterator tracer; a reseat never picks an old constructor.
    if allow_inclusive
        && super::alloc_vcs::is_range_inclusive_new_call(callee)
        && args.len() == 2
        && inclusive_bounds_are_machine_integers(func, &args[0], &args[1])
    {
        return Some(RangeYieldOrigin { start: &args[0], end: &args[1], end_inclusive: true });
    }
    // `into_iter`/`rev` are 1-arg (inner iterator); `step_by` is 2-arg (inner + step).
    // All three preserve the original yield SET (or a subset), so the inner
    // iterator is `args[0]` in every case.
    if (callee_is_into_iter(callee) || callee_is_rev(callee)) && args.len() == 1
        || callee_is_step_by(callee) && args.len() == 2
    {
        if let Operand::Copy(p) | Operand::Move(p) = &args[0]
            && p.projections.is_empty()
        {
            return trace_local_to_range_yield_origin(func, p.local, fuel - 1, allow_inclusive);
        }
    }
    None
}

/// Trust: 2026-09-16 — THE CALL-DESTINATION HOP, for every iterator tracer in this
/// family (`trace_local_to_range_aggregate`, `trace_local_to_enumerated_slice`,
/// `container_len::trace_slice_iter_item`,
/// `loop_bounds::trace_iter_to_into_iter_arg`) and nowhere else. The `(callee, args)`
/// of the `Call` that produces `local`, IFF that call is the local's ONE write channel.
///
/// # The hole this closes
///
/// Each tracer resolves an iterator local through the seam's VALUE resolver, then the
/// ORIGIN question under [`iterator_origin_def`]'s gate, and — when both decline
/// because the local is a CALL DESTINATION (`WholeOpaque`, which neither hands back) —
/// hopped into the call's `args[0]`. That hop used to be a bare block scan, `for block
/// in blocks { if Call { dest.local == local } .. }`, which takes the FIRST call
/// writing the local and asks nothing about the local's OTHER writes. So a call-dest
/// iterator local RESEATED after its constructor traced to the constructor:
///
///  * `let mut r = (0..5usize).rev(); r = (0..100usize).rev(); for i in r { a[i] }`
///    on a `[u8; 5]` — `_3 = rev(_4)` then `_3 = move _5` (a second, NAMED whole
///    write) — traced to `Range{0, 5}`, minted the yield fact `i < 5`, and PROVED the
///    bounds row, kernel-certified, on the pristine driver (2 proved, 0 failed,
///    rc = 0). The program panics at `i == 99`.
///  * the same through a conduit: `let p = &mut r; *p = (0..100usize).rev();` — the
///    reseat names `p` as its place, so no scan keyed on `r` sees it (`LocalWrite::
///    Escape` is the only trace it leaves on `r`), and the hop took the first call.
///  * `into_iter` instead of `rev`, both spellings; and `a.iter().enumerate()`
///    reseated to `b.iter().enumerate()` through a conduit, which proved
///    `SliceBoundsCheck` on `a[i]` for `i < 100`.
///
/// All five are pinned on the compiler's own `-Copt-level=0` MIR in
/// `tests/escaped_local_seam_realmir.rs` (the `reseated call destination` rows).
///
/// # The gate — the same two-question ladder as the `Assign` hop, one channel at a time
///
/// 1. `local_defs::unique_value_call` — the `WholeOpaque` half of the VALUE resolver,
///    and the question the reviewer named. `Some` only when the local is not a
///    parameter and its writes, on EVERY channel, are exactly one `Call` destination:
///    no second `Call`/`TailCall`, no `WholeNamed` `Assign` beside it (the `r = ..`
///    reseat), no `Partial` store, no `Unlocatable` write, and no `Escape`.
/// 2. When that declines, `local_defs::unique_initializing_call` UNDER
///    [`iter_mut_borrows_only_feed_next`] — the ORIGIN question for a call destination,
///    which readmits exactly one channel, the `&mut`/`&raw` alias, and only when the
///    affirmative conduit allow-list holds (every conduit defined once, never read,
///    never written through, never dropped, passed only as argument 0 of a std
///    `Iterator::next`). This is the same licence, with the same argument, under which
///    [`iterator_origin_def`] readmits the alias for an `Assign`-initialised iterator;
///    it is needed here because the `for`-loop desugar's `&mut iter` conduit sits on
///    the CALL DESTINATION itself whenever the identity `into_iter` copy is folded
///    away — every `-Copt-level=1` body, and the bounded-reduction lane's synthetic
///    fixtures spell it directly (`_4 = into_iter(a); _7 = &mut _4; next(_7)`), so a
///    gate that refused the alias outright turned that lane's refutation producer off
///    (11 of its pinned rows) for no soundness gain: with the conduit discipline the
///    local's only mutation is `next` on itself, and the yield set of the constructor's
///    result contains every later yield.
///
/// A local with any other write channel — a second whole write, a projected store, a
/// `Drop`, an unlocatable write, a conduit that is written through (`*p = ..`), read,
/// dropped, or handed to any call but `next` — has no single constructor to hop into,
/// and the tracer declines: `Unknown`, honest. The five witnesses split exactly along
/// those lines: `dbl_rev`/`dbl_into` refuse at question 1 AND 2 (a `WholeNamed` beside
/// the call); `alias_rev`/`alias_into`/`enum_reseat` pass neither (question 1 sees the
/// `Escape`, question 2's gate sees the store rooted at the conduit).
///
/// # Why the hop is safe once the gate passes
///
/// Under question 1 the value `local` holds at every read is the call's result. Under
/// question 2 the local's only mutation is `next` on itself, which consumes from — and
/// never adds to — the yield set of the call's result. Either way the iterator IS
/// `callee(args[0], ..)` for everything the tracers read: their callee-identity gates
/// license only yield-set facts about `args[0]` (`into_iter`/`rev`/`step_by`/`enumerate`
/// preserve or shrink the inner yield set; `<[T]>::iter`/`windows`/`chunks*` fix the
/// slice or the sub-slice length), and the inner local is resolved by the same ladder
/// recursively, so a reseat ANYWHERE along the chain — of the iterator local, of a `Use`
/// copy, of the inner call destination — is refused at the hop that would have crossed
/// it.
///
/// Every consumer asks for the whole-local destination; a projected destination is
/// `Partial` and never reaches either question.
pub(super) fn call_dest_hop(func: &VerifiableFunction, local: usize) -> Option<(&str, &[Operand])> {
    call_dest_hop_keyed(func, local).map(|(callee, args, _)| (callee, args))
}

/// [`call_dest_hop`], plus the hopped call's compiler-minted `callee_key`, for a
/// consumer whose recognizer decides on the key (SLICE-INHERENT-1). Same gate,
/// same call.
pub(super) fn call_dest_hop_keyed(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(&str, &[Operand], Option<&trust_types::CalleeKey>)> {
    let terminator = crate::local_defs::unique_value_call(func, local).or_else(|| {
        let init_call = crate::local_defs::unique_initializing_call(func, local)?;
        iter_mut_borrows_only_feed_next(func, local).then_some(init_call)
    })?;
    match terminator {
        Terminator::Call { func: callee, args, dest, callee_key, .. }
            if dest.projections.is_empty() =>
        {
            Some((callee.as_str(), args.as_slice(), callee_key.as_ref()))
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "call_dest_hop_gate_tests.rs"]
mod call_dest_hop_gate_tests;

/// Trace a local holding a slice-index Range/RangeTo/RangeFrom aggregate to its
/// bound operands, following whole-local `Ref`/`Use` copies (bounded by `fuel`).
/// Returns `None` on any ambiguity — the caller MUST fail closed when the receiver
/// is a real slice (a missing bound here is a missing OOB obligation), never skip.
pub(super) fn trace_local_to_range_family(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<RangeFamilyOperands<'_>> {
    if fuel == 0 || crate::local_defs::is_parameter(func, local) {
        return None;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, local) {
        return match rvalue {
            Rvalue::Aggregate(
                trust_types::AggregateKind::Adt { name, variant: 0, .. },
                operands,
            ) => {
                let n = name.as_str();
                if aggregate_is_exclusive_range(n) && operands.len() == 2 {
                    Some(RangeFamilyOperands::Exclusive(&operands[0], &operands[1]))
                } else if range_family_adt_name(n) == Some("RangeTo") && operands.len() == 1 {
                    Some(RangeFamilyOperands::To(&operands[0]))
                } else if range_family_adt_name(n) == Some("RangeFrom") && operands.len() == 1 {
                    Some(RangeFamilyOperands::From(&operands[0]))
                } else {
                    None
                }
            }
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_range_family(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_range_family(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    None
}

/// THE ENTRANCE HOP — the fifth hop of the tracers, and the one the census of
/// call-destination hops did not cover. The RECEIVER local (argument 0) of the one
/// `Iterator::next` call that is `next_result_local`'s ONLY write channel; `None`
/// whenever that local is written anywhere else.
///
/// Every yield tracer is ENTERED from the `next` RESULT: `build_range_yield_guard_map`
/// sees `_i = ((_o as Some).0)` and asks "which iterator did `_o` come out of", and
/// the answer's constructor fact is then minted onto `_i`. That question used to be a
/// bare block scan — `for block in blocks { if Call { dest.local == _o } .. }` — which
/// took the FIRST `next` call writing `_o` in block order and asked nothing about the
/// local's other writes. rustc's `expr_into_dest` lowering of
///
/// ```text
/// let mut small = 0..5usize; let mut big = 50..100usize;
/// let o = if c { small.next() } else { big.next() };
/// if let Some(i) = o { a[i] } else { 0 }        // a: &[u8; 5]
/// ```
///
/// writes `_o` from TWO `next` calls in two branches, and the scan attributed the
/// payload to `small`, minted `0 <= i < 5`, and PROVED the bounds row — kernel-
/// certified, on the pristine driver (2 proved, 0 failed) — while `two_next_if(false,
/// ..)` panics at index 50. The same shape proves through the enumerate tracer, the
/// `windows`/`chunks` tracer, the array-trip-count tracer, and in `loop`/`match`
/// form; exchanging the two arms flips the verdict to a refutation, so the verdict
/// depended on nothing but block order. All of it is pinned on the compiler's own
/// `-Copt-level=0` MIR in `tests/escaped_local_seam_realmir.rs` (the `two_next_*`
/// rows).
///
/// The gate is `local_defs::unique_value_call` — the VALUE question, not the origin
/// twin: the `next` result is a plain call destination in every desugar (`for`,
/// `while let`, a `let` binding), never `&mut`-borrowed and never reseated, so the
/// stricter question over-refuses nothing the tracers' rows need (`u64_acc`,
/// `range_acc`, `grid_plain`, `ctl_rev_ok`, `stepby_acc`, `signed_range` and the
/// bounded-reduction rows all still prove; measured). Under it, the value `_o` holds at
/// the payload read IS that one call's result, so the receiver's yield set contains the
/// payload — the only fact the tracers below go on to mint. A named `Assign` beside
/// the call, a `&mut _o`, a projected store or an unlocatable write all have no
/// producing call, and the tracer declines: `Unknown`, honest. A SECOND `next` writing
/// the same local is the one shape with a sound answer beyond "decline": the JOIN —
/// see [`next_call_receivers`], of which this is the one-call form.
///
/// The receiver must be a whole local (`args[0]` unprojected); the tracers resolve it
/// through the value resolver, the gated origin question and [`call_dest_hop`], so a
/// reseat ANYWHERE below this hop is refused at the hop that would have crossed it.
pub(super) fn next_call_receiver(
    func: &VerifiableFunction,
    next_result_local: usize,
) -> Option<usize> {
    match crate::local_defs::unique_value_call(func, next_result_local)? {
        Terminator::Call { func: callee, args, dest, .. }
            if dest.projections.is_empty()
                && args.len() == 1
                && callee_is_iterator_next(callee) =>
        {
            match &args[0] {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Trust: 2026-09-16 (round A5) — THE JOINED ENTRANCE. The receiver local of EVERY
/// `Iterator::next` call writing `next_result_local`, when those calls are the local's
/// ONLY write channels (`local_defs::value_calls`) and each is a std `Iterator::next`
/// with a whole-local receiver; `None` when any write is not such a call.
///
/// [`next_call_receiver`] is this with exactly one element. With `k > 1` elements the
/// value `_o` holds at the payload read is the result of ONE of the `k` calls — no
/// `Assign`, projected store, `SetDiscriminant`, alias or unlocatable write can have
/// put anything else there — so the payload is a yield of one of the `k` receivers,
/// and the only fact a consumer may mint is the DISJUNCTION of the per-receiver
/// yield facts, each receiver traced through the same gates as the single case. The
/// entrance gate's own witness `two_next_if` (`0..5` against `50..100`, `a: &[u8; 5]`)
/// gets `(0 <= i < 5) ∨ (50 <= i < 100)` and the bounds row stays REFUTED, now with a
/// witness the program realises; its correct twin `two_next_if_ok` (`2..5`) gets
/// `(0 <= i < 5) ∨ (2 <= i < 5)` and PROVES — where the previous round refuted it
/// over the unmodelled payload, a false refutation. A receiver that does not trace
/// withholds the whole fact (see the consumers), never the other branch's alone.
pub(super) fn next_call_receivers(
    func: &VerifiableFunction,
    next_result_local: usize,
) -> Option<Vec<usize>> {
    crate::local_defs::value_calls(func, next_result_local)?
        .into_iter()
        .map(|terminator| match terminator {
            Terminator::Call { func: callee, args, dest, .. }
                if dest.projections.is_empty()
                    && args.len() == 1
                    && callee_is_iterator_next(callee) =>
            {
                match &args[0] {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                        Some(p.local)
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

/// Find the `Iterator::next` call whose destination is `next_result_local` and
/// trace its receiver to the originating exclusive-`Range` ([`RangeOrigin`]). The
/// entrance is gated by [`next_call_receiver`] — ONE producing call. The joined form
/// is [`next_call_range_origins`].
pub(super) fn next_call_range_operands(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<RangeOrigin<'_>> {
    let receiver = next_call_receiver(func, next_result_local)?;
    trace_local_to_range_aggregate(func, receiver, fuel)
}

/// The [`RangeOrigin`] of EVERY `next` call writing `next_result_local` — the joined
/// entrance ([`next_call_receivers`]). `None` unless every receiver traces; a consumer
/// must disjoin the per-origin facts, never pick one.
pub(super) fn next_call_range_origins(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<Vec<RangeOrigin<'_>>> {
    next_call_receivers(func, next_result_local)?
        .into_iter()
        .map(|receiver| trace_local_to_range_aggregate(func, receiver, fuel))
        .collect()
}

/// Yield-only inclusive/exclusive entrance. Deliberately separate from
/// `next_call_range_origins`, whose exclusive cardinality contract must not widen.
fn next_call_range_yield_origins(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<Vec<RangeYieldOrigin<'_>>> {
    next_call_receivers(func, next_result_local)?
        .into_iter()
        .map(|receiver| trace_local_to_range_yield_origin(func, receiver, fuel, true))
        .collect()
}

pub(super) fn body_has_iterator_next(func: &VerifiableFunction) -> bool {
    super::terminator_presence_for(func).has_iterator_next_call
}

/// Negative-only provenance for the inclusive extension. Its interval is true
/// of every yielded value, but does not say which value a particular `next`
/// returns (or whether an adapter skips it). Generic SAT over such a value is
/// not an executable counterexample. Keep both the field and its licensed SSA
/// alias: statement encoding may fold the alias back into the `Some` field.
pub(crate) fn inclusive_range_yield_set_only_values(func: &VerifiableFunction) -> Vec<String> {
    if !body_has_iterator_next(func) {
        return Vec::new();
    }
    let mut names = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: dest,
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } = stmt
            else {
                continue;
            };
            if !dest.projections.is_empty() || !is_some_payload_projection(&src.projections) {
                continue;
            }
            let Some(origins) = next_call_range_yield_origins(func, src.local, 16) else {
                continue;
            };
            if !origins.iter().any(|origin| origin.end_inclusive) {
                continue;
            }
            names.push(place_to_var_name(func, src));
            // A reassigned alias may now be a genuine input value. Withhold on
            // that name only under the same global-value licence as the facts.
            if payload_carries_global_fact(func, dest.local) {
                names.push(place_to_var_name(func, dest));
            }
        }
    }
    names.sort_unstable();
    names.dedup();
    names
}

/// Trust: 2026-09-16 (round A5) — THE PAYLOAD GATE. True iff a fact keyed on the BARE
/// name of `payload_local` may be attached to every block that mentions it.
///
/// The yield-fact builders (`build_range_yield_guard_map`,
/// `build_enumerate_yield_guard_map`) mint `start <= p < end` / `0 <= p < len` on the
/// `Some`-payload local `p` and `generate::safety` conjoins those facts AFTER the
/// version rename, so the bare name binds to whichever version of `p` is terminal in
/// the block under proof.
/// The fact is therefore a claim about EVERY value the name can denote, and the
/// licence for that is `local_defs::is_single_static_assignment`: exactly one whole
/// write on every channel (the `Some`-payload `Use` the builder is looking at — a
/// second whole write, `WholeNamed` or `WholeOpaque`, refuses), no `Partial` write, no
/// `Escape`, no `Unlocatable` write, and never a parameter (its entry definition is a
/// second value). Refusing is a decline to `Unknown`; it never invents a refutation.
///
/// Without it a `mut` binding reassigned after the extraction — `for mut i in 0..5usize
/// { i = n; t = a[i]; }` — was PROVED and kernel-certified on the pristine driver
/// (`Ge(i#s5_1, 0) ∧ Lt(i#s5_1, 5) ∧ Eq(i#s5_1, n)` on the post-reassignment version,
/// UNSAT) while the program panics at `n = 50`. See the module banner and the
/// `payload_*` rows of `tests/escaped_local_seam_realmir.rs`.
///
/// Trust: 2026-10-12 (CHUNKS-MUT-PAYLOAD-1) — the slice-iterator builder
/// (`container_len::build_slice_iter_yield_guard_map`) no longer asks this gate. Its
/// fact `len(p) == n` / `1 <= len(p) <= n` is keyed on the NAME `{p}__slice_len`, which
/// `slice_len_licence::licensed_slice_len_formula` licenses
/// (`local_defs::path_is_single_static_assignment` over `p` and its tie chain): that
/// refuses every write and mutable alias AT or above `p`, as this gate does, and ignores
/// what is strictly inside it. This gate counts rustc's own length read of a `&mut [T]`
/// payload, `&raw const (*p)`, as an escape, so `for w in a.chunks_exact_mut(4) { w[3] =
/// 1 }` got no fact and was refuted at `w__slice_len = 0`. This gate is unchanged.
pub(super) fn payload_carries_global_fact(func: &VerifiableFunction, payload_local: usize) -> bool {
    crate::local_defs::is_single_static_assignment(func, payload_local)
}

/// Resolve a range bound operand to the canonical formula the bounds obligation
/// compares against, so the yield fact discharges it. For the `0..s.len()` idiom
/// `end` is a local defined by `PtrMetadata(s)`/`Len(s)`; resolve it to the SAME
/// `slice_len_formula(s)` term the index VC uses — but ONLY under
/// [`licensed_slice_len_formula`]'s root licence, because that term is a NAME the
/// version rename rebinds on every whole write of `s` (round A6; see the module
/// banner and [`slice_len_name_is_stable`]).
///
/// Trust: 2026-09-16 (round A5) — RETURNS `None` INSTEAD OF THE BARE NAME when the
/// operand's root local is not single-valued. The result is INLINED into a fact keyed
/// on some OTHER name (the payload's `i < end`), or into a violation, so version
/// renaming cannot rebind it: `i < n` with `n` spelled bare is a claim about every
/// value `n` holds, and it is false the moment `n` has a second write. `let mut n =
/// 5; for i in 0..n { n = 100; a[i] }` (correct, `a: &[u8; 5]`) was REFUTED with a
/// counterexample on the previous round — the bare `n` renamed to the post-store
/// version `100`, so `i < 100` no longer discharged `i < 5` — and the mirror `let mut
/// n = 100; for i in 0..n { n = 5; a[i] }` (panics at `i == 5`) is the same fallback
/// read in the proving direction. The gate is `local_defs::is_single_static_assignment`
/// on the root local (a never-written parameter passes; a written one, an aliased one,
/// a projected write, an unlocatable write refuse), and for a PROJECTED operand
/// (`(*self).n`) additionally no projected write of the root anywhere in the body.
/// Constants always resolve. Every caller declines on `None`: the yield builders emit
/// no fact.
///
/// Trust: 2026-10-14 — THIS RESOLVER IS FOR FACTS KEYED ON ANOTHER NAME (a payload's
/// `i < end`, a window's `len(w) == n`, an `unwrap_or` default), never for a bound
/// stated in an obligation AT A CALL. Its joined-copy fallback (below) hands back the
/// bare name of a single-assignment copy of a multiply-written local: a name of one
/// value, so a payload fact on it is true, and a fact is a hypothesis, which a free
/// name only weakens. An obligation stated at a call meets the copy's value only where
/// the copy's definition reaches the row, and refutes on an arbitrary model where it
/// does not (a copy made in a loop body ahead of a write of its source). Every
/// call-site lane (the slice range index and its char-boundary axiom and endpoint
/// facts, `BTreeMap::range`, `VecDeque::range`) asks
/// `panic_calls::range_bound_at_call_formula` instead, which never takes the fallback
/// (`tests/range_bound_joined_copy_realmir.rs`).
pub(super) fn resolve_range_bound_formula(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Formula> {
    resolve_range_bound_formula_with(func, operand, fuel, true)
}

/// [`resolve_range_bound_formula`] WITHOUT the joined-copy fallback: a copy of a
/// multiply-written local resolves to nothing. The bare copy name is one value, but it
/// is connected to that value only where its defining block is conjoined; a lane that
/// reads the bound AT a call does not conjoin it, so it asks this first, then its
/// exact-at-call resolutions, and never the fallback (`&b[..k]` with `let k = if n <
/// b.len() { n } else { b.len() }`, `range_bound_joined_before_its_call.rs`, was refuted
/// with the copy temp free). The one place that order is spelled is
/// `panic_calls::range_bound_at_call_formula`.
pub(super) fn resolve_range_bound_formula_exact(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Formula> {
    resolve_range_bound_formula_with(func, operand, fuel, false)
}

fn resolve_range_bound_formula_with(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
    joined_copy: bool,
) -> Option<Formula> {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else {
        // A constant (or any operand that is not a place) names no local.
        return Some(operand_to_formula(func, operand));
    };
    if !p.projections.is_empty() {
        // A projected read (`(*self).n`): the bare formula is a global claim about the
        // root AND the projected slot, so both must be stable.
        // Trust: 2026-09-16 (round A9) — AND every index local the projection embeds
        // (`(*a)[j]` is spelled `a*[_j]`, the index by NUMBER): the slot the name
        // selects is one slot only while `j` is one value. `let mut j = 0; if a[j] > 5
        // { return 0 } j = k; for i in 0..a[j] { b[i] }` (`b: &[u8; 5]`) minted `i <
        // a*[_4]` off the guarded FIRST slot and the loop ran to the reseated SECOND
        // one: `b[i]` PROVED kernel-certified, `f(&[3, 100], &b, 1)` panics
        // (`index_elem_end_bug`, `index_elem_end_param_bug`, `field_index_end_bug`,
        // `index_elem_end_arr_bug` — `r5b_*` rows of `tests/escaped_local_seam_realmir.rs`;
        // the SSA-index controls `ctl_index_elem_end_ssa` / `ctl_index_elem_end_guarded`
        // keep their proofs, a never-written parameter passing the licence).
        // Trust: 2026-09-29 — a read THROUGH a reference asks about the memory, not
        // the local: every pointer derived from the read's root reference, including
        // reloads (`_18 = copy (*_1)`) and shared reborrows, is followed
        // (`local_defs::deref_read_is_never_written`). The per-local form missed four
        // shapes that were proved and panic (`b01`–`b08` of the escape audit).
        // Merge 2026-10-14: the pointer-family walk ends only at a parameter or a local
        // of reference type, so it refuses every read through a reference to the body's
        // OWN storage (`let z = &len; ..*z`, `for i in 0..*z`: the walk reaches `len`,
        // not a reference). Such a read folds (`crate::canonical_place`) to that storage
        // itself, with no `Deref` left, and upstream's licence answers it: the pointer
        // holds one value and is never written through a projection (below), and
        // `projected_bound_names_one_value` requires the STORAGE to hold one value with
        // no mutable or raw alias (`is_single_static_assignment`) and no projected
        // write. The `ploss_adv` H1 controls `pc02` / `pc04` prove on it; memory behind
        // a pointer (a fold that keeps a `Deref`) still needs the family walk.
        let per_local = || {
            crate::local_defs::is_single_static_assignment(func, p.local)
                && !local_has_projected_write(func, p.local)
                && crate::local_defs::place_index_locals_are_single_static_assignment(func, p)
        };
        let stable = if matches!(p.projections.first(), Some(trust_types::Projection::Deref)) {
            crate::local_defs::deref_read_is_never_written(func, p)
                || (per_local()
                    && !crate::canonical_place(func, p)
                        .projections
                        .iter()
                        .any(|q| matches!(q, trust_types::Projection::Deref)))
        } else {
            per_local()
        };
        if !stable {
            return None;
        }
        // Trust: 2026-10-08 (H1, STALE-BOUND-CALL-RENAME — FALSE PROOF) — and the
        // licence must be about the storage the formula NAMES, not only the pointer the
        // read goes through: `projected_bound_names_one_value`.
        let formula = operand_to_formula(func, operand);
        return projected_bound_names_one_value(func, p, &formula).then_some(formula);
    }
    if fuel > 0 {
        match crate::local_defs::unique_value_def(func, p.local) {
            // Trust: 2026-09-16 (round A6) — the canonical `{root}__slice_len` term is a
            // NAME the version rename rebinds (see the module banner), so it is handed
            // back only under `licensed_slice_len_formula`'s root licence. A MODELLED
            // length whose root fails it (`mut s` reseated in the loop, `mut s: &[u8]`
            // with a body write, a projected slot written in the body, `let n = s.len()`
            // over any of those) resolves to NOTHING — not to the bare bound local
            // either: a bare `n` is a true fact about one version, but the encoder ties
            // it to `s__slice_len` at ONE program point and the obligation reads the
            // length at another, so the fact discharges nothing, and a payload it pins
            // is one the callee-return havoc lane can no longer decline honestly
            // (`len_reseat_after_loop`, a correct program, kept a spurious refutation
            // with the bare fallback; `let_n_reseat` kept an ungrounded one). An
            // UNMODELLED length (no `slice_len_formula` at all) still falls through to
            // the bare local exactly as before.
            // Trust: 2026-09-16 (round A8) — the name minted is the ROOT's canonical
            // one (`callee_summaries::param_slice_len`: whole-local copies, the
            // `&(*root)` / `&raw const (*root)` reborrows and slice-preserving casts
            // are followed to the root FIRST, then the licence is asked there), with
            // the temp-keyed licence as the fallback for a root the walk cannot
            // name. At `-Copt-level=0` a `&mut [T]` length read is `_5 = &(*_1);
            // PtrMetadata(move _5)`, and a fact keyed on `_5__slice_len` reached an
            // obligation spelled on `s__slice_len` (through the bounds check's own
            // `&raw const (*_1)` tie) only when the borrow tie of bb0 happened to be
            // carried; the root's name connects by construction (`a8_ctl_mut_*_o0`).
            Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => {
                if matches!(
                    crate::ptr_metadata_model(func, inner),
                    crate::PtrMetadataModel::Length(_)
                ) {
                    return super::callee_summaries::param_slice_len(func, inner, fuel - 1)
                        .or_else(|| licensed_slice_len_formula(func, inner, fuel - 1));
                }
            }
            Some(Rvalue::Len(place)) => {
                if crate::place_slice_len_formula(func, place).is_some() {
                    return super::callee_summaries::param_slice_len_place(func, place, fuel - 1)
                        .or_else(|| {
                            super::slice_len_licence::licensed_slice_len_formula_place(
                                func,
                                place,
                                fuel - 1,
                            )
                        });
                }
            }
            // Trust: 2026-10-10 — a copy of a JOINED local (`let k = if n > 26 { 26 }
            // else { n }; for i in 0..k`, MIR `_7 = copy _2` with `_2` written on both
            // arms) resolves to the copy's own bare name when the copy is single-valued:
            // `i < _7` is then a claim about one value, the licence the final line below
            // grants any other single-valued bound. Only the multiply-written case falls
            // back; a single-def inner that refuses (a modelled length whose root fails
            // its licence, round A6) still resolves to nothing. Sweep `p50`.
            Some(Rvalue::Use(inner)) => {
                let resolved = resolve_range_bound_formula_with(func, inner, fuel - 1, joined_copy);
                let inner_is_joined = joined_copy
                    && matches!(inner, Operand::Copy(q) | Operand::Move(q)
                    if q.projections.is_empty()
                        && crate::local_defs::unique_value_def(func, q.local).is_none()
                        && !crate::local_defs::is_single_static_assignment(func, q.local));
                if resolved.is_some() || !inner_is_joined {
                    return resolved;
                }
            }
            _ => {}
        }
    }
    // The bare name is a global claim about the local; `is_single_static_assignment`
    // is the licence for one (a never-written parameter included).
    crate::local_defs::is_single_static_assignment(func, p.local)
        .then(|| operand_to_formula(func, operand))
}

// Trust: 2026-09-16 (round A8) — `licensed_slice_len_formula`, `formula_is_slice_len_name`
// and `slice_len_name_is_stable` moved to `generate::slice_len_licence`, the ONE module
// every `slice_len_formula`-inlining producer (this lane, `container_len`,
// `callee_summaries::param_slice_len` and through it the min/max, modulo, division and
// downward-induction facts) asks. The measured hole that forced the move: the min lane
// licensed its root by `is_parameter` alone and proved `let n = s.len().min(100); s = b;
// s[..n]` kernel-certified — see that module's banner.

/// Trust: 2026-09-16 (round A8) — EVERY licensed spelling of a range bound, the
/// canonical one ([`resolve_range_bound_formula`]) first. A `PtrMetadata`/`Len` end
/// has two licensed names when it is read through a reborrow or copy temp: the ROOT's
/// canonical `{s}__slice_len` and the temp's own `{r}__slice_len` — each a name of the
/// same one value, so a fact `payload < name` is true under either, and the yield
/// builders emit BOTH: the obligation is spelled on whichever the bounds check's own
/// length read canonicalizes to, and the borrow tie between the two is a `bb0` block
/// def that the loop-body VC does not always carry. `let r: &[u8] = s; for i in
/// 0..r.len() { t += r[i] }` on `s: &mut [u8]` (`ctl_mut_reborrow_read`, `-O0`) reads
/// its obligation on `r__slice_len` and proved only through the temp's name; `for i in
/// 0..s.len() { s[i] = 0 }` (`ctl_mut_store`, `-O0`) reads it on `s__slice_len` through
/// the check's `&raw const (*s)` tie and proved only through the root's. Any other
/// operand has exactly its one resolution.
pub(super) fn resolve_range_bound_alias_formulas(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Vec<Formula> {
    let mut out: Vec<Formula> =
        resolve_range_bound_formula(func, operand, fuel).into_iter().collect();
    if let Operand::Copy(p) | Operand::Move(p) = operand
        && p.projections.is_empty()
        && fuel > 0
        && !crate::local_defs::is_parameter(func, p.local)
    {
        // Trust: 2026-09-16 (round A9) — the temp's own name is a name of one value
        // only when every index local its read embeds is (`PtrMetadata((*s)[j])` is
        // keyed on `s*[_j]__slice_len`); `licensed_slice_len_formula` refuses that
        // through `metadata_owner`, and the test is repeated here so this arm can
        // never admit what the canonical arm above refuses.
        let index_locals_stable = |op: &Operand| match op {
            Operand::Copy(q) | Operand::Move(q) => {
                crate::local_defs::place_index_locals_are_single_static_assignment(func, q)
            }
            _ => true,
        };
        let direct = match crate::local_defs::unique_value_def(func, p.local) {
            Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner))
                if matches!(
                    crate::ptr_metadata_model(func, inner),
                    crate::PtrMetadataModel::Length(_)
                ) && index_locals_stable(inner) =>
            {
                licensed_slice_len_formula(func, inner, fuel - 1)
            }
            Some(Rvalue::Len(place))
                if crate::local_defs::place_index_locals_are_single_static_assignment(
                    func, place,
                ) =>
            {
                licensed_slice_len_formula(func, &Operand::Copy(place.clone()), fuel - 1)
            }
            Some(Rvalue::Use(inner)) => {
                let mut v = resolve_range_bound_alias_formulas(func, inner, fuel - 1);
                for f in out {
                    if !v.contains(&f) {
                        v.insert(0, f);
                    }
                }
                return v;
            }
            _ => None,
        };
        if let Some(d) = direct
            && !out.contains(&d)
        {
            out.push(d);
        }
    }
    out
}

fn place_mentions_local(place: &Place, local: usize) -> bool {
    place.local == local
        || place
            .projections
            .iter()
            .any(|p| matches!(p, trust_types::Projection::Index(i) if *i == local))
}

fn operand_mentions_local(op: &Operand, local: usize) -> bool {
    matches!(op, Operand::Copy(p) | Operand::Move(p) if place_mentions_local(p, local))
}

fn rvalue_mentions_local(rv: &Rvalue, local: usize) -> bool {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            operand_mentions_local(op, local)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_mentions_local(a, local) || operand_mentions_local(b, local)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_mentions_local(place, local),
        Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_mentions_local(op, local)),
        Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|op| operand_mentions_local(op, local))
        }
        _ => false,
    }
}

fn place_mentions_any_local(place: &Place, locals: &FxHashSet<usize>) -> bool {
    locals.contains(&place.local)
        || place
            .projections
            .iter()
            .any(|p| matches!(p, trust_types::Projection::Index(i) if locals.contains(i)))
}

fn operand_mentions_any_local(op: &Operand, locals: &FxHashSet<usize>) -> bool {
    matches!(op, Operand::Copy(p) | Operand::Move(p) if place_mentions_any_local(p, locals))
}

fn rvalue_mentions_any_local(rv: &Rvalue, locals: &FxHashSet<usize>) -> bool {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            operand_mentions_any_local(op, locals)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_mentions_any_local(a, locals) || operand_mentions_any_local(b, locals)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_mentions_any_local(place, locals),
        Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_mentions_any_local(op, locals)),
        Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|op| operand_mentions_any_local(op, locals))
        }
        _ => false,
    }
}

fn operand_mentions_some_local(op: &Operand) -> bool {
    matches!(op, Operand::Copy(_) | Operand::Move(_))
}

fn rvalue_mentions_some_local(rv: &Rvalue) -> bool {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            operand_mentions_some_local(op)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_mentions_some_local(a) || operand_mentions_some_local(b)
        }
        Rvalue::Ref { .. }
        | Rvalue::AddressOf(_, _)
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::CopyForDeref(_) => true,
        Rvalue::Aggregate(_, ops) => ops.iter().any(operand_mentions_some_local),
        Rvalue::Unsupported { operands, .. } => operands.iter().any(operand_mentions_some_local),
        _ => false,
    }
}

fn block_mentions_any_local(block: &trust_types::BasicBlock, locals: &FxHashSet<usize>) -> bool {
    if locals.len() == 1
        && let Some(&only) = locals.iter().next()
    {
        return block_mentions_local(block, only);
    }
    for stmt in &block.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt
            && (place_mentions_any_local(place, locals)
                || rvalue_mentions_any_local(rvalue, locals))
        {
            return true;
        }
    }
    match &block.terminator {
        Terminator::Call { args, dest, .. } => {
            locals.contains(&dest.local)
                || args.iter().any(|op| operand_mentions_any_local(op, locals))
        }
        Terminator::SwitchInt { discr, .. } => operand_mentions_any_local(discr, locals),
        Terminator::Assert { cond, .. } => operand_mentions_any_local(cond, locals),
        _ => false,
    }
}

fn push_place_mentioned_locals(place: &Place, out: &mut Vec<usize>) {
    out.push(place.local);
    for proj in &place.projections {
        if let trust_types::Projection::Index(i) = proj {
            out.push(*i);
        }
    }
}

fn push_operand_mentioned_locals(op: &Operand, out: &mut Vec<usize>) {
    if let Operand::Copy(p) | Operand::Move(p) = op {
        push_place_mentioned_locals(p, out);
    }
}

fn push_rvalue_mentioned_locals(rv: &Rvalue, out: &mut Vec<usize>) {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            push_operand_mentioned_locals(op, out);
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            push_operand_mentioned_locals(a, out);
            push_operand_mentioned_locals(b, out);
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => push_place_mentioned_locals(place, out),
        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
            for op in ops {
                push_operand_mentioned_locals(op, out);
            }
        }
        _ => {}
    }
}

/// True iff `local` appears anywhere in `block` (as a place root, an `Index`
/// projection, an operand, or a terminator operand/dest). Used to attach a
/// payload's yield fact only to the blocks that reference it.
pub(super) fn block_mentions_local(block: &trust_types::BasicBlock, local: usize) -> bool {
    for stmt in &block.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt
            && (place_mentions_local(place, local) || rvalue_mentions_local(rvalue, local))
        {
            return true;
        }
    }
    match &block.terminator {
        Terminator::Call { args, dest, .. } => {
            dest.local == local || args.iter().any(|op| operand_mentions_local(op, local))
        }
        Terminator::SwitchInt { discr, .. } => operand_mentions_local(discr, local),
        Terminator::Assert { cond, .. } => operand_mentions_local(cond, local),
        _ => false,
    }
}

/// The payload and every SINGLE-ASSIGNMENT local whose one definition computes
/// from it, transitively. For `v[i - 1]` that is `_15 = SubWithOverflow(i, 1)`
/// and `_14 = move (_15.0)`. The bounds check `Lt(_14, len)` sits in a block that
/// never names `i`, yet its obligation is stated over `i` once the block
/// definitions are substituted. So it needs the payload's facts: the
/// ordinary-Rust sweep's `d_prev`, `for i in 1..v.len() { v[i - 1] }`, was
/// refuted with `i = 1`, `len = 0`.
///
/// SOUNDNESS: a payload fact such as `start <= i < end` is true of every value
/// `next` yields, but it is UNSATISFIABLE when the range is empty. So it may only
/// be attached where `i` has been assigned, or it vacuously discharges the block.
/// A block that reads `i` is such a place: MIR reads only initialized locals.
/// A block that reads a single-assignment local defined from `i` is too: its one
/// definition ran and read `i`. A MULTIPLY-assigned local is not: `s = s + i`
/// leaves `s` readable after a loop that never ran, where `1 <= i < len` with
/// `len == 0` would prove anything.
fn locals_derived_from(func: &VerifiableFunction, payload_local: usize) -> FxHashSet<usize> {
    let mut derived = FxHashSet::default();
    derived.insert(payload_local);
    let mut pending: Vec<(usize, &Rvalue)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.projections.is_empty()
                && place.local != payload_local
                && (derived.len() == 1 || !derived.contains(&place.local))
            {
                let mentions = if derived.len() == 1 {
                    rvalue_mentions_local(rvalue, payload_local)
                } else {
                    rvalue_mentions_any_local(rvalue, &derived)
                };
                if mentions {
                    if crate::local_defs::is_single_static_assignment(func, place.local) {
                        derived.insert(place.local);
                    }
                } else if rvalue_mentions_some_local(rvalue) {
                    pending.push((place.local, rvalue));
                }
            }
        }
    }
    if derived.len() == 1 || pending.is_empty() {
        return derived;
    }
    loop {
        let before = derived.len();
        pending.retain(|&(local, rvalue)| {
            if derived.contains(&local) {
                return false;
            }
            if rvalue_mentions_any_local(rvalue, &derived) {
                if crate::local_defs::is_single_static_assignment(func, local) {
                    derived.insert(local);
                }
                return false;
            }
            true
        });
        if derived.len() == before || pending.is_empty() {
            return derived;
        }
    }
}

/// Build the per-block map of range-iterator yield facts. For each payload
/// binding `_p = (next(&mut range) as Some).0`, attach `start <= _p < end` (or
/// `start <= _p <= end` for a modeled inclusive range) to
/// every block that references `_p`. Independent of the BFS guard map so the
/// loop-join weakening cannot drop the fact. See the module banner above for the
/// soundness argument.
pub(super) fn build_range_yield_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    // `(payload local, the facts attached to every block mentioning it)`.
    let mut payloads: Vec<(usize, Vec<Formula>)> = Vec::new();
    if body_has_iterator_next(func) {
        for block in &func.body.blocks {
            for (stmt_index, stmt) in block.stmts.iter().enumerate() {
                let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
                if !dest.projections.is_empty() {
                    continue;
                }
                let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue
                else {
                    continue;
                };
                if !is_some_payload_projection(&src.projections) {
                    continue;
                }
                // THE PAYLOAD GATE — the fact is keyed on `dest`'s bare name; see
                // `payload_carries_global_fact` and the module banner.
                if !payload_carries_global_fact(func, dest.local) {
                    continue;
                }
                // The JOINED entrance: every `next` writing `src.local` must trace.
                let Some(origins) = next_call_range_yield_origins(func, src.local, TRACE_FUEL)
                else {
                    continue;
                };
                // The bounds must still hold the values the yielding `next` saw.
                if bound_rewritten_between_yield_and_extraction(
                    func,
                    src.local,
                    block.id,
                    stmt_index,
                    dest.local,
                    origins.iter().flat_map(|o| [o.start, o.end]),
                ) {
                    continue;
                }
                let payload_var = Formula::var_owned(
                    place_to_var_name(func, &Place::local(dest.local)),
                    Sort::Int,
                );
                // Both are YIELD-SET bounds, with the original endpoint's polarity,
                // however far the iterator has been consumed; see `RangeYieldOrigin`. A
                // bound that does not resolve (a multiply-written `end`) withholds the fact.
                let groups: Option<Vec<Vec<Formula>>> = origins
                    .iter()
                    .map(|RangeYieldOrigin { start, end, end_inclusive }| {
                        let start_f = resolve_range_bound_formula(func, start, TRACE_FUEL)?;
                        // The canonical end first, then every other licensed spelling of
                        // the same value (round A8; `resolve_range_bound_alias_formulas`).
                        let mut end_fs = resolve_range_bound_alias_formulas(func, end, TRACE_FUEL);
                        if end_fs.is_empty() {
                            end_fs.extend(end_bound_unwritten_until_used(func, end, dest.local));
                        }
                        // Trust (2026-10-17, gate RCA precision T8): the END temp itself.
                        if let Some(temp) = end_projected_copy_temp(func, end)
                            && !end_fs.contains(&temp)
                        {
                            end_fs.push(temp);
                        }
                        if end_fs.is_empty() {
                            return None;
                        }
                        let mut group =
                            vec![Formula::Ge(Box::new(payload_var.clone()), Box::new(start_f))];
                        group.extend(end_fs.into_iter().map(|end_f| {
                            if *end_inclusive {
                                Formula::Le(Box::new(payload_var.clone()), Box::new(end_f))
                            } else {
                                Formula::Lt(Box::new(payload_var.clone()), Box::new(end_f))
                            }
                        }));
                        Some(group)
                    })
                    .collect();
                let Some(groups) = groups else { continue };
                payloads.push((dest.local, join_yield_fact_groups(groups)));
            }
        }
    }
    let mut map = attach_payload_facts(func, payloads);
    // Trust (D2 tier 1, 2026-09-24): a closure's `ADAPTER_YIELD` integer-range
    // premise (a constant `start..end`, optionally under `rev`/`step_by`, driving
    // a core adapter), installed by the compiler and re-gated on this body. No
    // premise leaves the map byte-identical for every other body.
    super::extend_with_adapter_premise_facts(func, &mut map, super::AdapterPremiseFamily::IntRange);
    map
}

/// Trust (2026-10-10, review round 100): may a local the yield fact's `bounds` read be REWRITTEN
/// between a write of the `next` result `src` and the payload extraction at
/// `extraction_block.stmts[extraction_stmt]`?
///
/// The yield fact `start <= p < end` names the bounds bare, so the version rename reads
/// them where the payload is used. That is the value the yielding `next` saw only if no
/// write of a bound local runs between that `next` and the extraction. A single
/// static assignment inside a loop is one value PER ITERATION: `let e = k2; if c { if
/// let Some(i) = o { a[i] } } let mut r = 0..e; .. o = r.next()` carries `o` from the
/// previous iteration's `0..e` into one where `e` was redefined, and `i < e` named the
/// new `e`: `a[i]` over `a: &[u8; 26]` was PROVED and indexed 49. The bound locals are
/// the operands' locals and, transitively, every local their definitions read. The
/// walk starts after every write of `src`, stops at a block that rewrites `src` and
/// writes no bound local, and answers `true` when it reaches the extraction having
/// passed a bound write (a write in the extraction block before the extraction
/// counts). A for loop's `next` falls straight through its `Some` switch into the
/// extraction, so a bound defined in an OUTER loop keeps its fact.
pub(super) fn bound_rewritten_between_yield_and_extraction<'a>(
    func: &VerifiableFunction,
    src: usize,
    extraction_block: BlockId,
    extraction_stmt: usize,
    payload: usize,
    bounds: impl IntoIterator<Item = &'a Operand>,
) -> bool {
    let n_locals = func.body.locals.len();
    let mut bound: FxHashSet<usize> = FxHashSet::default();
    let mut work: Vec<usize> = Vec::new();
    for op in bounds {
        push_operand_mentioned_locals(op, &mut work);
    }
    while let Some(local) = work.pop() {
        if local >= n_locals || !bound.insert(local) {
            continue;
        }
        crate::visit_local_write_candidates(
            func,
            &func.body.blocks,
            local,
            |block, stmt| match stmt {
                Some(Statement::Assign { place, rvalue, .. })
                    if place.local == local && place.projections.is_empty() =>
                {
                    push_rvalue_mentioned_locals(rvalue, &mut work);
                }
                Some(_) => {}
                None => {
                    // A `Call` destination is a FRESH value: a later write of an argument does
                    // not change it, and its own re-definition is a write of `local`, which the
                    // walks below count. (Following every call's arguments withheld `h.len()`
                    // for `let h = s.split_at(n).0; for i in 0..h.len() { s = b; h[i] }`, a8
                    // `ctl_call_chain`.) The ONE call the length resolvers look through is
                    // `str::as_bytes`, whose length `slice_len_formula` spells on the RECEIVER
                    // (`guards::as_bytes_length_receiver`): that receiver is a bound local (review
                    // round 106: `let s = pick(a, b, k); .. 0..s.as_bytes().len()` with the
                    // `Option` carried into an iteration with a shorter `s`, kernel-certified).
                    // `guards::base_collection_step` (the `owned_container_len_var` fallback the
                    // `as_bytes` arm takes for a `&String` receiver) also crosses the call dest of
                    // a length-preserving std `deref`/`deref_mut`/`as_slice`, naming the length on
                    // its FIRST argument (review round 107: `let r = <&String as Deref>::deref(&s);
                    // 0..r.as_bytes().len()`, `s` rebound per iteration, kernel-certified).
                    // (DEREF-ANCHOR-1: the hop also reads the receiver's MIR type, exactly as
                    // `base_collection_step` asks it, so this walk follows the same calls.)
                    if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
                        && dest.local == local
                        && let Some(first @ (Operand::Copy(p) | Operand::Move(p))) = args.first()
                        && p.projections.is_empty()
                        && crate::guards::callee_is_length_preserving_deref(callee, func, p)
                    {
                        push_operand_mentioned_locals(first, &mut work);
                    }
                }
            },
        );
        if let Some(receiver) = crate::guards::as_bytes_length_receiver(func, local) {
            push_operand_mentioned_locals(receiver, &mut work);
        }
    }
    // WHOLE writes only. A store THROUGH a bound (`(*v)[i] = x` under `0..v.len()`)
    // changes no length, and a projected bound (`(*s).n`) is licensed by its own
    // stability gate in `resolve_range_bound_formula`; counting element stores refused
    // `for i in 0..v.len() { v[i] = v[i].wrapping_mul(3) }` (sweep r30, u04).
    let writes = |stmt: &Statement, local: usize| match stmt {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => place.local == local && place.projections.is_empty(),
        _ => false,
    };
    let writes_bound = |stmt: &Statement| match stmt {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => {
            place.projections.is_empty() && bound.contains(&place.local)
        }
        _ => false,
    };
    let block_writes_bound_before = |b: &trust_types::BasicBlock, end: usize| {
        b.stmts[..end.min(b.stmts.len())].iter().any(writes_bound)
    };
    let terminator_writes = |b: &trust_types::BasicBlock, local: usize| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == local);
    let terminator_writes_bound = |b: &trust_types::BasicBlock| matches!(&b.terminator, Terminator::Call { dest, .. } if bound.contains(&dest.local));
    let Some(ex) = func
        .body
        .blocks
        .get(extraction_block.0)
        .filter(|b| b.id == extraction_block)
        .map(|_| extraction_block.0)
        .or_else(|| func.body.blocks.iter().position(|b| b.id == extraction_block))
    else {
        return true;
    };
    if bound.is_empty()
        || !func
            .body
            .blocks
            .iter()
            .any(|b| block_writes_bound_before(b, b.stmts.len()) || terminator_writes_bound(b))
    {
        return false;
    }
    let n = func.body.blocks.len();
    let succs: Vec<Vec<usize>> = (0..n)
        .map(|index| {
            let block = &func.body.blocks[index];
            let mut out: Vec<usize> = Vec::new();
            super::loop_bounds::for_each_terminator_succ(&block.terminator, |t| {
                if t < n {
                    out.push(t);
                }
            });
            out
        })
        .collect();
    // (block, a bound write has run since the yield)
    let mut seen: FxHashSet<(usize, bool)> = FxHashSet::default();
    let mut stack: Vec<(usize, bool)> = Vec::new();
    for (index, b) in func.body.blocks.iter().enumerate() {
        let stmt_write = b.stmts.iter().any(|s| writes(s, src));
        if stmt_write || terminator_writes(b, src) {
            // A statement write may precede a bound write in the same block.
            let crossed = (stmt_write && block_writes_bound_before(b, b.stmts.len()))
                || terminator_writes_bound(b);
            stack.extend(succs[index].iter().map(|&t| (t, crossed)));
        }
    }
    while let Some((index, crossed)) = stack.pop() {
        if !seen.insert((index, crossed)) {
            continue;
        }
        let b = &func.body.blocks[index];
        if b.id == extraction_block && (crossed || block_writes_bound_before(b, extraction_stmt)) {
            return true;
        }
        let writes_bound =
            block_writes_bound_before(b, b.stmts.len()) || terminator_writes_bound(b);
        let rewrites_src = b.stmts.iter().any(|s| writes(s, src)) || terminator_writes(b, src);
        if rewrites_src && !writes_bound {
            continue;
        }
        let crossed = crossed || writes_bound;
        stack.extend(succs[index].iter().map(|&t| (t, crossed)));
    }
    // Second leg (review round 102): the fact is attached to every block that names the
    // payload or a local computed from it (`attach_payload_facts`), and the bound is
    // read THERE. A bound redefined AFTER the extraction (an inner loop that rebuilds
    // `e`, then `a[i]`) named the new `e` for the old `i`: PROVED and kernel-certified,
    // indexed 39 into `[u8; 26]`. Walk from the extraction to every attached block; a
    // re-entry of the extraction block extracts a new payload, which the first leg
    // covers. A bound write in an attached block counts wherever it sits.
    let ex_block = &func.body.blocks[ex];
    if ex_block.stmts.iter().skip(extraction_stmt + 1).any(writes_bound)
        || terminator_writes_bound(ex_block)
    {
        return true;
    }
    let derived = locals_derived_from(func, payload);
    let attached = |b: &trust_types::BasicBlock| block_mentions_any_local(b, &derived);
    let mut seen: FxHashSet<(usize, bool)> = FxHashSet::default();
    let mut stack: Vec<(usize, bool)> = succs[ex].iter().map(|&t| (t, false)).collect();
    while let Some((index, crossed)) = stack.pop() {
        if index == ex || !seen.insert((index, crossed)) {
            continue;
        }
        let b = &func.body.blocks[index];
        let writes_bound =
            block_writes_bound_before(b, b.stmts.len()) || terminator_writes_bound(b);
        if attached(b) && (crossed || writes_bound) {
            return true;
        }
        let crossed = crossed || writes_bound;
        stack.extend(succs[index].iter().map(|&t| (t, crossed)));
    }
    false
}

/// The range END copied from behind a reference (`_5 = copy (*_1).0` for `0..s.n`), as
/// the bare name of that place, when nothing writes the place between the copy and any
/// block the yield fact about `payload` is attached to.
///
/// Trust (2026-09-29). `resolve_range_bound_formula` asks the whole function
/// (`local_defs::deref_read_is_never_written`), so a STORE to the bound's place before
/// the loop or after it (`s.n = 5; for i in 0..s.n { … } s.n = 0;`) withheld a correct
/// bound. The fact is attached to the blocks that name the payload or a local computed
/// from it ([`attach_payload_facts`]); it is renamed there at each use, so it holds when
/// the place has the value the copy read, which is what "no store on any path from the
/// copy to that block" gives. The points on such a path are the ones reachable from just
/// after the copy that can still reach an attach block, and only a store there is
/// counted (`local_defs::deref_read_is_unwritten_within`). A store on the way to an
/// attach block OUTSIDE the loop still counts (`if c { s.n = 0; return s.n - i }` names
/// `i` after it). A HAND-OUT of the pointer is counted wherever it is: a callee can
/// turn the `&mut` into a raw pointer that outlives the borrow and is written through
/// later by a call handed nothing (review8 `p4_raw2`, found when hand-outs were judged
/// by region too).
fn end_bound_unwritten_until_used(
    func: &VerifiableFunction,
    end: &Operand,
    payload: usize,
) -> Option<Formula> {
    let (Operand::Copy(e) | Operand::Move(e)) = end else { return None };
    if !e.projections.is_empty() || crate::local_defs::is_parameter(func, e.local) {
        return None;
    }
    let Some(Rvalue::Use(Operand::Copy(read) | Operand::Move(read))) =
        crate::local_defs::unique_value_def(func, e.local)
    else {
        return None;
    };
    if !matches!(read.projections.first(), Some(trust_types::Projection::Deref)) {
        return None;
    }
    let copy_block = crate::local_defs::unique_defining_block(func, e.local)?;
    let copy_stmt = func.body.blocks.get(copy_block)?.stmts.iter().position(|stmt| {
        matches!(stmt, Statement::Assign { place, rvalue: Rvalue::Use(_), .. }
            if place.local == e.local && place.projections.is_empty())
    })?;

    let n = func.body.blocks.len();
    let succs: Vec<Vec<usize>> = (0..n)
        .map(|index| {
            let block = &func.body.blocks[index];
            let mut out: Vec<usize> = Vec::new();
            super::loop_bounds::for_each_terminator_succ(&block.terminator, |t| {
                if t < n {
                    out.push(t);
                }
            });
            out
        })
        .collect();
    // Forward from the copy block's successors.
    let mut after_copy = vec![false; n];
    let mut stack = succs[copy_block].clone();
    while let Some(b) = stack.pop() {
        if !std::mem::replace(&mut after_copy[b], true) {
            stack.extend(succs[b].iter().copied());
        }
    }
    // Backward from every block the fact is attached to.
    let derived = locals_derived_from(func, payload);
    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, targets) in succs.iter().enumerate() {
        for &t in targets {
            predecessors[t].push(b);
        }
    }
    let mut reaches_use = vec![false; n];
    let mut stack: Vec<usize> = (0..n)
        .filter(|&b| block_mentions_any_local(&func.body.blocks[b], &derived))
        .collect();
    while let Some(b) = stack.pop() {
        if !std::mem::replace(&mut reaches_use[b], true) {
            stack.extend(predecessors[b].iter().copied());
        }
    }
    let within = |block: BlockId, at: Option<usize>| {
        let b = block.0;
        if b >= n || !reaches_use[b] {
            return false;
        }
        if after_copy[b] {
            return true;
        }
        // The copy block, not re-entered: only what runs after the copy.
        b == copy_block && at.is_none_or(|k| k > copy_stmt)
    };
    crate::local_defs::deref_read_is_unwritten_within(func, read, &within)
        .then(|| operand_to_formula(func, &Operand::Copy(read.clone())))
}

/// Trust (2026-10-17, gate RCA precision T8): the bare name of the range END temp
/// itself when it is a single-static-assignment whole local whose one value is a copy
/// read out of a PROJECTED place (`_7 = copy (*_1).1` for `0..self.len`).
///
/// The range is built from the temp's value, so every payload the range yields is
/// below that value: `i < _7` is true of the one value `_7` holds
/// (`local_defs::is_single_static_assignment`: never written again, never aliased, no
/// projected or unlocatable write), the licence the global resolver's last line grants
/// any single-valued bound, and the temp is among the bounds
/// `bound_rewritten_between_yield_and_extraction` already guards. Neither
/// `resolve_range_bound_formula` (the place's storage is written somewhere in the body)
/// nor [`end_bound_unwritten_until_used`] (a call is handed a pointer to that storage
/// inside the loop) names such an end, so aterm-font `Buffer::delete_glyphs_inplace`
/// (`for i in 0..self.len { .. if i + 1 < self.len .. self.merge_clusters(i, i + 2) ..
/// } self.len = j`) carried NO yield fact: its `i + 1` row was satisfiable at
/// `i = usize::MAX`, the callee-return decline (`havoc_decline`) then rewrote its KIND
/// to `UnsupportedMir`, and the `arithmetic_overflow_add` row the seal published PROVED
/// went MISSING (candidate gate of 2026-10-16). The temp's name does not track the place
/// after the loop starts, so it is added beside, never instead of, the place's own
/// spelling when [`end_bound_unwritten_until_used`] also licenses that.
fn end_projected_copy_temp(func: &VerifiableFunction, end: &Operand) -> Option<Formula> {
    let (Operand::Copy(e) | Operand::Move(e)) = end else { return None };
    if !e.projections.is_empty()
        || crate::local_defs::is_parameter(func, e.local)
        || !crate::local_defs::is_single_static_assignment(func, e.local)
    {
        return None;
    }
    let Some(Rvalue::Use(Operand::Copy(read) | Operand::Move(read))) =
        crate::local_defs::unique_value_def(func, e.local)
    else {
        return None;
    };
    if read.projections.is_empty() {
        return None;
    }
    match operand_to_formula(func, end) {
        f @ Formula::Var(..) => Some(f),
        _ => None,
    }
}

/// The fact list a payload carries, from the per-receiver fact GROUPS of its joined
/// entrance: ONE group is attached flat (the `Ge`/`Lt` pair), `k > 1`
/// groups become ONE disjunction of their conjunctions — the payload is a yield of
/// one of the `k` receivers, so it satisfies one of the `k` groups. Never a hull, never
/// one group alone.
pub(super) fn join_yield_fact_groups(groups: Vec<Vec<Formula>>) -> Vec<Formula> {
    let mut groups = groups.into_iter();
    match (groups.next(), groups.next()) {
        (None, _) => Vec::new(),
        (Some(only), None) => only,
        (Some(first), Some(second)) => {
            let mut disjuncts = vec![Formula::And(first), Formula::And(second)];
            disjuncts.extend(groups.map(Formula::And));
            vec![Formula::Or(disjuncts)]
        }
    }
}

/// Attach each payload's facts to every block that mentions the payload or a
/// local computed from it ([`locals_derived_from`]) — the per-block map every
/// yield-fact builder returns. Independent of the BFS guard map so the loop-join
/// weakening cannot drop the fact; sound because every payload here passed
/// `payload_carries_global_fact` (the slice-iterator lane: the `{s}__slice_len`
/// name licence, which refuses the same writes at or above the payload; see
/// [`payload_carries_global_fact`]).
pub(super) fn attach_payload_facts(
    func: &VerifiableFunction,
    payloads: Vec<(usize, Vec<Formula>)>,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if payloads.is_empty() || payloads.iter().all(|(_, facts)| facts.is_empty()) {
        return map;
    }
    let relevant: Vec<FxHashSet<usize>> = payloads
        .iter()
        .map(|(payload_local, facts)| {
            if facts.is_empty() {
                FxHashSet::default()
            } else {
                locals_derived_from(func, *payload_local)
            }
        })
        .collect();
    for block in &func.body.blocks {
        for ((_, facts), locals) in payloads.iter().zip(&relevant) {
            if facts.is_empty() || !block_mentions_any_local(block, locals) {
                continue;
            }
            map.entry(block.id).or_default().extend(facts.iter().cloned());
        }
    }
    map
}

// ======================================================================
// Enumerate-iterator index yield facts (`for (i, x) in s.iter().enumerate()`)
// ======================================================================
//
// `s.iter().enumerate()` yields `(count, &elem)` where `count` runs 0, 1, …,
// s.len()-1 — exactly the valid indices, each `< s.len()`. So the index payload
// (the tuple's `.0`, read as `(next(..) as Some).0.0`) provably satisfies
// `0 <= i < s.len()`. Emitting that fact discharges an `s[i]` access inside the
// loop, making `for (i, _) in s.iter().enumerate() { … s[i] … }` PROVE instead of
// false-refuting (the index is otherwise havoc'd out of `next()`). Mirrors the
// range-yield fact, but the bound is the UNDERLYING SLICE's length and the payload
// is the tuple's first field. SOUNDNESS: gated on the Enumerate wrapping a
// `<[T]>::iter` over a concrete slice `s` (so the count's upper bound is exactly
// `s.len()`); any other iterator shape ⇒ no fact.
/// In `Option<(usize, _)>`, the enumerate index is `Some.0` then tuple-field `.0`:
/// projection `[Downcast(1), Field(0), Field(0)]`.
pub(super) fn is_enumerate_index_projection(projections: &[trust_types::Projection]) -> bool {
    matches!(
        projections,
        [
            trust_types::Projection::Downcast(1),
            trust_types::Projection::Field(0),
            trust_types::Projection::Field(0)
        ]
    )
}

pub(super) fn callee_is_enumerate(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "enumerate")
}

/// `<[T]>::iter` — the SLICE iterator. Only this guarantees the enumerate count's
/// upper bound is the slice length (`<[T]>::iter` yields exactly `len` items).
/// Keyed (SLICE-INHERENT-1): a user `W::<[T]>::iter(s)` that yields more than
/// `s.len()` items is not std's.
pub(super) fn callee_is_slice_iter(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    vc_callee_is_slice_inherent(callee, callee_key, "iter")
}

/// Trace an `Iterator::next` receiver local back to the SLICE that an
/// `s.iter().enumerate()` chain enumerates, returning the slice operand. Walks
/// `next(&mut it)` -> `it = into_iter(enum)` -> `enum = enumerate(iter)` ->
/// `iter = <[T]>::iter(s)` through whole-local Ref/Use copies, bounded by `fuel`.
pub(super) fn trace_local_to_enumerated_slice(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<Operand> {
    if fuel == 0 || crate::local_defs::is_parameter(func, local) {
        return None;
    }
    // The seam's VALUE resolver first; when it declines, the ORIGIN hop
    // (`iterator_origin_def`), licensed here because the result is the SLICE the chain
    // enumerates, read for its length: `Enumerate::next` consumes the chain and never
    // reseats it, so every `(count, _)` it yields has `count < len` whatever the
    // iterator's position.
    let def = crate::local_defs::unique_value_def(func, local)
        .or_else(|| iterator_origin_def(func, local));
    if let Some(rvalue) = def {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_enumerated_slice(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_enumerated_slice(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    // The call-destination hop, GATED on the call being the local's only write channel
    // (`call_dest_hop`): `let mut it = a.iter().enumerate(); let p = &mut it; *p =
    // b.iter().enumerate(); for (i, _) in it { a[i] }` used to trace to `a` through the
    // first call and PROVE `SliceBoundsCheck` on the pristine driver while `i` runs to
    // 99 (`enum_reseat`, pinned on real MIR).
    let (callee, args, callee_key) = call_dest_hop_keyed(func, local)?;
    if args.len() != 1 {
        return None;
    }
    // `<[T]>::iter(s)` — the argument IS the slice; return it.
    if callee_is_slice_iter(callee, callee_key) {
        return Some(args[0].clone());
    }
    // `into_iter`/`enumerate` are transparent for tracing to the slice.
    if (callee_is_into_iter(callee) || callee_is_enumerate(callee))
        && let Operand::Copy(p) | Operand::Move(p) = &args[0]
        && p.projections.is_empty()
    {
        return trace_local_to_enumerated_slice(func, p.local, fuel - 1);
    }
    None
}

/// The slice an `s.iter().enumerate()` chain enumerates, for EVERY `Iterator::next`
/// call writing `next_result_local`, traced from each call's RECEIVER. The entrance is
/// the JOINED one ([`next_call_receivers`]): `None` unless the `next` calls are the
/// Option local's only write channels and every receiver traces; a consumer disjoins
/// the per-slice facts (`two_next_enum`: `a.iter().enumerate()` against
/// `b.iter().enumerate()` after `e2.nth(49)` proved `a[i]` and panicked at 50 on the
/// ungated first-call scan; the `nth` conduit now fails `e2`'s trace and the whole
/// fact is withheld).
pub(super) fn next_call_enumerated_slices(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<Vec<Operand>> {
    next_call_receivers(func, next_result_local)?
        .into_iter()
        .map(|receiver| trace_local_to_enumerated_slice(func, receiver, fuel))
        .collect()
}

/// Build the per-block map of enumerate index yield facts: for each
/// `i = (next(&mut enumerate_iter) as Some).0.0`, attach `0 <= i < s.len()` to
/// every block referencing `i`. Computed independently of the BFS guard map, like
/// the range-yield fact, so loop-join weakening cannot drop it.
pub(super) fn build_enumerate_yield_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    if !body_has_iterator_next(func) {
        return FxHashMap::default();
    }
    let mut payloads: Vec<(usize, Vec<Formula>)> = Vec::new();
    for block in &func.body.blocks {
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if !is_enumerate_index_projection(&src.projections) {
                continue;
            }
            // THE PAYLOAD GATE — `for (mut i, _) in a.iter().enumerate() { i = n; a[i] }`
            // proved on the pristine driver without it; see `payload_carries_global_fact`.
            if !payload_carries_global_fact(func, dest.local) {
                continue;
            }
            // The JOINED entrance: every `next` writing `src.local` must trace to a slice
            // whose length is modelled; one that does not withholds the whole fact.
            let Some(slices) = next_call_enumerated_slices(func, src.local, TRACE_FUEL) else {
                continue;
            };
            // Trust (2026-10-10, review round 101): the slice must still be the one the
            // yielding `next` iterated (`bound_rewritten_between_yield_and_extraction`):
            // an `Option` from the previous iteration's `s.iter().enumerate()` got `i <
            // len(s)` for the CURRENT, shorter `s` (kernel-certified, indexed past it).
            if bound_rewritten_between_yield_and_extraction(
                func,
                src.local,
                block.id,
                stmt_index,
                dest.local,
                slices.iter(),
            ) {
                continue;
            }
            let idx =
                Formula::var_owned(place_to_var_name(func, &Place::local(dest.local)), Sort::Int);
            // The slice's length is INLINED into a fact keyed on `idx`: it must be a
            // constant or a `__slice_len` name with one version (`licensed_slice_len_
            // formula`). `for (i, _) in <[u8]>::iter(s).enumerate() { s = &a[..1]; s[i] }`
            // proved at `-O1` on `s__slice_len` renamed to the post-reseat version.
            let groups: Option<Vec<Vec<Formula>>> = slices
                .iter()
                .map(|slice_op| {
                    // Root-canonical first (round A8; see `resolve_range_bound_formula`).
                    let len = super::callee_summaries::param_slice_len(func, slice_op, TRACE_FUEL)
                        .or_else(|| licensed_slice_len_formula(func, slice_op, TRACE_FUEL))?;
                    Some(vec![
                        Formula::Ge(Box::new(idx.clone()), Box::new(Formula::Int(0))),
                        Formula::Lt(Box::new(idx.clone()), Box::new(len)),
                    ])
                })
                .collect();
            let Some(groups) = groups else { continue };
            payloads.push((dest.local, join_yield_fact_groups(groups)));
        }
    }
    attach_payload_facts(func, payloads)
}

// ======================================================================
// CharIndices yield → panic-free str range slicing (R2 corpus family 1)
// ======================================================================
//
// `s.char_indices()` yields `(i, c)` where `i` is the byte offset of the char `c`
// INSIDE `s`: by the `CharIndices` contract every yielded `i` satisfies BOTH
// `i < s.len()` (a char occupies at least one byte at `i`) AND
// `s.is_char_boundary(i)`. So `&s[i..]` / `&s[..i]` at a yielded `i` can NEVER
// panic — neither on bounds nor on the str char-boundary check — and `&s[a..i]`
// can only panic on the `a > i` ordering (when `a` is itself boundary-safe).
// This is the heck `capitalize`/`transform` idiom the corpus measurement found
// FALSE-REFUTED on every str crate.
//
// DESIGN (why a STRUCTURAL discharge at the VC site, not an Int yield fact):
// Trust's range-slice obligation models only the BOUNDS panic; the str
// char-boundary panic is not a formula term. A general Int fact `i < s.len()`
// would let DERIVED indices discharge the bounds VC — `&s[i-1..]` proves bounds
// from `i < len` yet `i-1` may fall mid-char and PANIC (a false proof). The
// structural discharge credits ONLY a bound that IS a yielded index (traced
// through Use-copies with single-def/no-mut-borrow gates at every step), for a
// receiver that IS the iterated string — for exactly those, the boundary panic is
// impossible by contract, so folding the bounds disjunct is a theorem, not an
// approximation. Anything derived (arithmetic, merges, a different string) fails
// the trace and keeps today's refutable VC.
//
// SOUNDNESS GATES (each kills a concrete false-proof channel):
//  * root identity: the sliced receiver and the `char_indices` receiver must trace
//    (Use-copies / `&(*x)` reborrows) to the SAME projection-free root local that
//    is a parameter or single-def, `&str`-typed (shared ref — its referent cannot
//    be resized/mutated in safe Rust), and never `&mut`/`&raw`-borrowed (a
//    `*root = other` rebind would break identity);
//  * iterator integrity: the `CharIndices` local is single-def (the
//    `char_indices` call), never written through a projection, and every
//    `&mut`/`&raw` borrow of it feeds ONLY `Iterator::next` (a `mem::swap(&mut
//    it, &mut other_it)` would splice in yields of a DIFFERENT string);
//  * payload integrity: the `Option` result and the payload binding are
//    single-def, never mut-borrowed, never projection-written (an `as_mut`
//    payload rewrite between `next()` and the read would launder an arbitrary
//    index into a "yield", the hunt-15 class-C channel);
//  * the `next` receiver type must BE `CharIndices` (`std::str::CharIndices` /
//    `core::str::CharIndices` — std-reserved paths), so a user iterator whose
//    `next` yields out-of-range tuples never matches, and adapters (`Peekable`,
//    `Rev`) fail the type gate (their yields are still in-contract, but the
//    trace declines — fail-closed).
/// True iff the ADT path names the std/core `CharIndices` iterator (generic args
/// stripped). `std`/`core` are reserved crate names, so this cannot collide with
/// a user type.
pub(super) fn adt_is_char_indices(name: &str) -> bool {
    if !(name.starts_with("core::str::") || name.starts_with("std::str::")) {
        return false;
    }
    let base = name.split('<').next().unwrap_or(name);
    matches!(
        base,
        "std::str::CharIndices" | "core::str::CharIndices" | "core::str::iter::CharIndices"
    )
}

/// Trust: 2026-10-08 (H1 of the ploss adversarial pass, STALE-BOUND-CALL-RENAME —
/// FALSE PROOF). True iff the formula of the PROJECTED range bound `p` (`(*z)`,
/// `(*p).len`, `(*self).n`) names ONE value at every program point — the contract of
/// [`resolve_range_bound_formula`], whose callers inline the answer into a violation
/// that the version rename re-stamps at the INDEX CALL, or into a payload fact that the
/// rename binds at the row.
///
/// The pointer licence the caller checks (the root of `p` single-valued, never written
/// through a projection, its index locals single-valued) is about the POINTER. The
/// formula names the POINTEE: the referent fold spells `*z` with `z = &len` as `len`,
/// and `*z` with `z = &s.len` as `s*.len`. A write to that storage under ITS OWN name
/// versions the name between the range's construction and the call: a direct `len = n`
/// once `z`'s borrow has ended (safe code), `s.len = n` through the parameter,
/// `(*q).len = n` through an aliasing raw pointer, or a callee's write. The rename then
/// binds the bound to the POST-write value. `let z = &len; let r = ..*z; len = n; if
/// len > 8 { return 0 } buf[r]` (`buf: &[u8; 8]`) was PROVED and kernel-certified at
/// -O0 and -O1 on main c132f5a193 and panics at `m = 100, n = 3`. Eleven reproducers
/// (`..*z`, `0..*z` loop ends, `..(*p).len`, `..=*z`, `*a..*b`, `*z..`, `Bound` pairs)
/// are pinned in `tests/ploss_adv_false_proofs_realmir.rs`. The mirror (guard, then
/// range, then write) was falsely REFUTED by the same binding.
///
/// So the storage the name denotes (`crate::canonical_place`, the fold
/// `place_to_var_name` applies) is licensed by the rule for a bare name:
///  * the body's OWN storage (no `Deref` left after the fold): its root local holds
///    one value (`is_single_static_assignment`: one whole write, no `&mut`/raw alias,
///    no unlocatable write), is never written through a projection, and every index
///    local of the place is single-valued. This is the bare-local licence of the
///    fall-through arm of [`resolve_range_bound_formula`];
///  * memory behind a pointer the fold did not resolve: the pointer licence on the
///    canonical root as well, and NO program point versions the storage the name
///    denotes (`StmtVersionCtx::ever_versioned` of the name up to its first index
///    segment: no store through an alias the oracle sees, no havoc at a call), so no
///    rename can move it to another value. This is the test `range_bound_use` applies
///    to an entry-valued read.
///
/// A miss declines (`None` upstream). The yield builders then emit no fact, and the
/// slice range lane asks `range_bound_use::range_bound_at_call`, which names the bound
/// at its read into the range only when that is its value at the call.
fn projected_bound_names_one_value(
    func: &VerifiableFunction,
    p: &Place,
    formula: &Formula,
) -> bool {
    let referent = crate::canonical_place(func, p);
    if !(crate::local_defs::is_single_static_assignment(func, referent.local)
        && !local_has_projected_write(func, referent.local)
        && crate::local_defs::place_index_locals_are_single_static_assignment(func, &referent))
    {
        return false;
    }
    if !referent.projections.iter().any(|q| matches!(q, trust_types::Projection::Deref)) {
        return true;
    }
    let sv = super::stmt_versions_for(func);
    match formula {
        // The STORAGE is the name up to its first index segment (`a*[_14]` is an
        // element of `a*`): every write the oracle sees to any part of it, or to an
        // ancestor, or a havoc of the pointer, rebinds that prefix
        // (`path_defs::place_names_overlap`). The one other writer of the full name is
        // the definition of an index local it embeds (`write_covers_index_segment`),
        // single-valued by the licence above, so that rebinding renames one value.
        // Asking about the full name instead declined the `-O0` copy temp of
        // `for i in 0..a[j]` (`r5b_ctl_index_elem_end_o0`, a correct program).
        Formula::Var(name, _) => {
            let storage = name.find('[').map_or(name.as_str(), |open| &name[..open]);
            !sv.ever_versioned(func, storage)
        }
        _ => trust_types::all_free_variable_names(formula, &mut |name| {
            !sv.ever_versioned(func, name)
        }),
    }
}

/// True iff `local` is ever written through a projection (`x.f = ..`, `(*x).f = ..`),
/// `SetDiscriminant`, or deinitialized — writes `local_defs::value_count` does NOT see.
pub(super) fn local_has_projected_write(func: &VerifiableFunction, local: usize) -> bool {
    crate::any_local_write_stmt(func, &func.body.blocks, local, |_b, s| match s {
        Statement::Assign { place, .. } => {
            place.local == local && !place.projections.is_empty()
        }
        Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
            place.local == local
        }
        _ => false,
    })
}

/// Trace a `Copy`/`Move` operand to its projection-free ROOT local through
/// whole-local Use-copies and `&(*x)` shared reborrows, then gate the root:
/// `&str`/`&[T]`-typed (shared `Ref` to `Slice`), single-valued, never
/// `&mut`/`&raw`-borrowed, never projection-written. Returns the root local.
///
/// "Single-valued" is `local_defs::holds_one_value`, not `is_parameter(l) || count == 1`: that
/// disjunction let a PARAMETER skip the def count entirely, so `fn f(mut s: &str) {
/// s = t; s.char_indices() }` qualified `s` as a stable root while its bare name means
/// the ENTRY slice. Same class as the parameter-entry-def budget; found by the caller
/// audit, unwitnessed (no probe was built for the CharIndices yield lane).
pub(super) fn charindices_shared_slice_root(
    func: &VerifiableFunction,
    op: &Operand,
) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let mut l = p.local;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, l) {
            break;
        }
        match crate::local_defs::unique_value_def(func, l) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                l = q.local;
            }
            Some(Rvalue::Ref { mutable: false, place: q })
                if q.projections.as_slice() == [trust_types::Projection::Deref] =>
            {
                l = q.local;
            }
            _ => break,
        }
    }
    let root_is_shared_slice = matches!(
        crate::local_ty_ref(func, l),
        Some(Ty::Ref { mutable: false, inner }) if matches!(inner.as_ref(), Ty::Slice { .. })
    );
    if root_is_shared_slice
        && crate::local_defs::holds_one_value(func, l)
        && !guards::local_is_mutably_borrowed(func, l)
        && !local_has_projected_write(func, l)
    {
        Some(l)
    } else {
        None
    }
}

/// True iff every `&mut`/`&raw` borrow of `iter_local` is a single-def temp used
/// ONLY as the receiver (arg 0) of an `Iterator::next` call — the conduit
/// discipline that forbids `mem::swap`/`replace` re-seating the iterator.
///
/// THIS IS THE GATE UNDER WHICH [`iterator_origin_def`] READMITS THE ALIAS CHANNEL,
/// so it must be an AFFIRMATIVE allow-list over everything a conduit can DO, not a
/// deny-list over the misuses someone thought of. A conduit `t = &mut it` may:
///
///  * be defined exactly once (`local_defs::has_one_explicit_def`), and
///  * appear as argument 0 of an `Iterator::next` call.
///
/// Anything else is a refusal: a read of `t` by any rvalue (a copy, a reborrow
/// `&mut *t`, an aggregate capture), `t` as any other call argument or as a
/// `SwitchInt`/`Assert` operand, `t` as a call DESTINATION, and — the half that was
/// MISSING until 2026-09-16 — a WRITE ROOTED AT `t`: a deref store `(*t) = v`, a
/// projected store `(*t).end = v`, a `SetDiscriminant`/`Deinit` of `(*t)`. Those
/// name `t` as their PLACE, not as an operand, so the operand walk never saw them,
/// and `let mut it = 0..5; let p = &mut it; *p = 0..100; for i in it { a[i] }`
/// passed this gate while reseating the whole iterator through the conduit. On the
/// pristine prebuilt driver that program PROVES `a[i]` in range on a `[u8; 5]`
/// (2 proved, 0 failed, rc = 0) and panics at `i == 5`; with the resolver refusing
/// the alias it declines, and a migration onto the origin question over the OLD
/// gate would have handed the false proof straight back. The pin is
/// `tests/escaped_local_seam_realmir.rs::a_reseat_through_the_conduit_is_not_a_fresh_iterator`.
///
/// A `Drop` of the conduit's place is refused too (dropping a `&mut` is a no-op,
/// but a `Drop` rooted at the conduit means it was not a plain receiver temp), and
/// so is any other terminator naming `t`. A `Terminator::Opaque` anywhere in the
/// body is refused upstream by the origin question itself (`LocalWrite::Unlocatable`).
///
/// Trust (2026-10-01): std `Peekable::peek` is admitted beside `next`. It moves at
/// most one item from the wrapped iterator into the `Peekable`'s own buffer, which
/// the next `next` returns, and hands back only a SHARED reference to it: it never
/// reseats the iterator, never adds an item, and cannot rewrite one (`peek_mut`,
/// whose `&mut` result can, stays refused). Sweep q45 (`if it.peek() != Some(&&x)`).
pub(super) fn iter_mut_borrows_only_feed_next(
    func: &VerifiableFunction,
    iter_local: usize,
) -> bool {
    iter_mut_borrows_only_feed(func, iter_local, |_, term, arg_ix| {
        arg_ix == 0
            && matches!(term, Terminator::Call { func: callee, .. }
                if callee_is_iterator_next(callee) || callee_is_std_peekable_peek(callee))
    })
}

/// The sysroot inherent `Peekable::<I>::peek`, by its exact generic-stripped path
/// (no `as` qualification, no unauthenticated crate stamp).
pub(super) fn callee_is_std_peekable_peek(callee: &str) -> bool {
    callee.contains("Peekable")
        && callee.contains("peek")
        && !callee.contains(" as ")
        && !trust_types::path_has_unauthenticated_crate_stamp(callee)
        && vc_strip_generics_cow(callee) == "core::iter::adapters::peekable::Peekable::peek"
}

/// [`iter_mut_borrows_only_feed_next`] with the admitted CALL USE supplied by the
/// caller: a conduit may appear as argument `arg_ix` of the call terminator of
/// block `block_index` exactly when `admit(block_index, terminator, arg_ix)` holds.
/// Every other rule (one definition, never read, never written through, never
/// dropped, switched on or asserted on; a mutable reborrow is itself a conduit;
/// an rvalue the walker cannot enumerate refuses) is the same, so an `admit` that
/// accepts ONE call site makes that call the iterator's only mutator.
pub(super) fn iter_mut_borrows_only_feed(
    func: &VerifiableFunction,
    iter_local: usize,
    admit: impl Fn(usize, &Terminator, usize) -> bool,
) -> bool {
    let mut conduits: Vec<usize> = Vec::new();
    let bad_conduit =
        crate::any_local_write_stmt(func, &func.body.blocks, iter_local, |_b, s| {
            if let Statement::Assign { place, rvalue, .. } = s {
                match rvalue {
                    Rvalue::Ref { mutable: true, place: q } | Rvalue::AddressOf(_, q)
                        if q.local == iter_local =>
                    {
                        if !place.projections.is_empty() {
                            return true;
                        }
                        conduits.push(place.local);
                    }
                    _ => {}
                }
            }
            false
        });
    if bad_conduit {
        return false;
    }
    // Trust (2026-10-03): a worklist, so that a mutable REBORROW of a conduit is itself a
    // conduit. The pre-optimization MIR the whole-crate summaries are extracted from
    // spells a `for` loop's receiver `_11 = &mut iter; _10 = &mut (*_11); next(_10)`;
    // `_10` names the same iterator as `_11`, and it is held to EXACTLY the rules below
    // (one definition, used only as arg 0 of `Iterator::next`, never written through,
    // never dropped/switched on/asserted on), so the iterator is still mutated only by
    // `next`. A SHARED reborrow, a raw pointer, or any other read of a conduit still
    // refuses.
    conduits.sort_unstable();
    conduits.dedup();
    if conduits.is_empty() {
        return true;
    }
    let mut checked: Vec<usize> = Vec::with_capacity(conduits.len());
    while !conduits.is_empty() {
        for &t in &conduits {
            if !crate::local_defs::has_one_explicit_def(func, t) {
                return false;
            }
        }
        checked.extend_from_slice(&conduits);
        let is_conduit = |l: usize| conduits.contains(&l);
        let mut next_conduits: Vec<usize> = Vec::new();
        // Every use of a conduit in the current wave must be an admitted call
        // argument, or a mutable reborrow of it into a fresh whole local (a further
        // conduit).
        for (block_index, b) in func.body.blocks.iter().enumerate() {
            for s in &b.stmts {
                match s {
                    Statement::Assign { place, rvalue, .. } => {
                        // A WRITE ROOTED AT THE CONDUIT — `(*t) = v`, `(*t).f = v` — is
                        // a write to the iterator this scan is vouching for. The
                        // conduit's own single whole definition (`t = &mut it`) is the
                        // one write to `t` itself that the discipline allows.
                        if is_conduit(place.local) && !place.projections.is_empty() {
                            return false;
                        }
                        if let Rvalue::Ref { mutable: true, place: q } = rvalue
                            && is_conduit(q.local)
                            && q.projections.as_slice() == [Projection::Deref]
                            && place.projections.is_empty()
                        {
                            if !checked.contains(&place.local)
                                && !next_conduits.contains(&place.local)
                            {
                                next_conduits.push(place.local);
                            }
                            continue;
                        }
                        let mut used = false;
                        let complete = for_each_rvalue_operand_place(rvalue, &mut |pl| {
                            if is_conduit(pl.local) {
                                used = true;
                            }
                        });
                        // An rvalue the walker cannot enumerate is a read it cannot
                        // rule out — refuse, like a read.
                        if used || !complete {
                            return false;
                        }
                    }
                    Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                        if is_conduit(place.local) =>
                    {
                        return false;
                    }
                    _ => {}
                }
            }
            match &b.terminator {
                Terminator::Call { args, dest, .. } => {
                    if is_conduit(dest.local) {
                        return false;
                    }
                    for (i, a) in args.iter().enumerate() {
                        if let Operand::Copy(pl) | Operand::Move(pl) = a
                            && is_conduit(pl.local)
                            && !admit(block_index, &b.terminator, i)
                        {
                            return false;
                        }
                    }
                }
                Terminator::Drop { place, .. } if is_conduit(place.local) => {
                    return false;
                }
                Terminator::SwitchInt { discr, .. } => {
                    if matches!(discr, Operand::Copy(pl) | Operand::Move(pl) if is_conduit(pl.local))
                    {
                        return false;
                    }
                }
                Terminator::Assert { cond, .. } => {
                    if matches!(cond, Operand::Copy(pl) | Operand::Move(pl) if is_conduit(pl.local))
                    {
                        return false;
                    }
                }
                _ => {}
            }
        }
        conduits = next_conduits;
    }
    true
}

/// STR_BYTE_POSITION (2026-10-04): the iterator local `it`, built by the call
/// terminator of `init_block`, is consumed by EXACTLY ONE dynamic execution of the
/// call terminator of `call_block` (the caller has already pinned, through
/// [`iter_mut_borrows_only_feed`], that its `&mut` conduits feed only that call).
///
/// Two halves:
///  * NO OTHER READ. `it` is never read (a copy, a move, a shared or raw borrow), never
///    an intrinsic's, a `CopyNonOverlapping`'s or a terminator's operand; the body has
///    no `Unsupported` statement or `Opaque` terminator. Only `&mut it` conduit borrows
///    remain. WRITES are not re-scanned here: the caller reached `it` through
///    `local_defs::unique_initializing_call`, which already refuses every write of
///    `it` on every channel except its one call destination and the `&mut` alias.
///  * DYNAMIC ONCE. `call_block` is unreachable from its own successors (normal and
///    unwind) in the CFG with `init_block` removed: a second execution of the call
///    must pass the initializer again, which builds a FRESH iterator. Without this,
///    `while let Some(i) = it.position(..)` re-runs `position` on a consumed
///    iterator and returns an index RELATIVE to the remaining suffix (`"a/é/"` gives
///    `2` the second time, and `&s[3..]` panics).
pub(super) fn iter_consumed_once_by(
    func: &VerifiableFunction,
    it: usize,
    call_block: usize,
    init_block: usize,
) -> bool {
    let blocks = &func.body.blocks;
    let names = |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == it);
    for b in blocks {
        for s in &b.stmts {
            match s {
                Statement::Assign { rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: q } = rvalue
                        && q.local == it
                        && q.projections.is_empty()
                    {
                        continue;
                    }
                    let mut used = false;
                    let complete = for_each_rvalue_operand_place(rvalue, &mut |pl| {
                        if pl.local == it {
                            used = true;
                        }
                    });
                    if used || !complete {
                        return false;
                    }
                }
                Statement::Intrinsic { args, .. } if args.iter().any(names) => return false,
                Statement::CopyNonOverlapping { src, dst, count, .. }
                    if [src, dst, count].into_iter().any(names) =>
                {
                    return false;
                }
                Statement::Unsupported { .. } => return false,
                _ => {}
            }
        }
        match &b.terminator {
            Terminator::Call { args, .. } if args.iter().any(names) => return false,
            Terminator::SwitchInt { discr, .. } if names(discr) => return false,
            Terminator::Assert { cond, .. } if names(cond) => return false,
            // An inline-asm / unmodeled terminator can name anything.
            Terminator::Opaque { .. } => return false,
            _ => {}
        }
    }
    // DYNAMIC ONCE: no path from `call_block`'s successors back to it that avoids
    // `init_block`.
    let push_successors = |bi: usize, work: &mut Vec<usize>| {
        let Some(b) = blocks.get(bi) else { return };
        crate::for_each_terminator_target(&b.terminator, |t| work.push(t.0));
        if let Terminator::Call { unwind, .. }
        | Terminator::Assert { unwind, .. }
        | Terminator::Drop { unwind, .. } = &b.terminator
        {
            work.extend(unwind.cleanup_target().map(|t| t.0));
        }
    };
    let mut seen = vec![false; blocks.len()];
    let mut work = Vec::new();
    push_successors(call_block, &mut work);
    while let Some(bi) = work.pop() {
        if bi == call_block {
            return false;
        }
        if bi == init_block || bi >= seen.len() || seen[bi] {
            continue;
        }
        seen[bi] = true;
        push_successors(bi, &mut work);
    }
    true
}

/// Invoke `f` on every place read by the rvalue's operands (incl. Ref/AddressOf
/// referents and Index projections' bases are NOT recursed — base places only).
///
/// Returns `true` iff EVERY operand of the rvalue was handed to `f`. This walker is
/// the READ half of two conduit allow-lists (`iter_mut_borrows_only_feed_next`,
/// `container_len`'s push-conduit gate), which vouch that a `&mut` temp is used
/// nowhere but as a `next`/`push` receiver — so an rvalue whose operands it cannot
/// enumerate is a read it cannot rule out, and the caller must REFUSE, not shrug.
/// Every variant `trust_types::Rvalue` declares today is named below; the wildcard
/// exists only because the enum is `#[non_exhaustive]` in another crate, and it
/// answers `false`. Until 2026-09-16 it was `_ => {}`, which made `PtrOffset { ptr, .. }`
/// (a MIR `BinOp::Offset`, the post-inlining spelling of `p.add(0)`) and
/// `UncheckedBinaryOp` invisible to both gates.
#[must_use]
pub(super) fn for_each_rvalue_operand_place(rvalue: &Rvalue, f: &mut impl FnMut(&Place)) -> bool {
    let mut on_op = |op: &Operand| {
        if let Operand::Copy(pl) | Operand::Move(pl) = op {
            f(pl);
        }
    };
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            on_op(op)
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => {
            on_op(a);
            on_op(b);
        }
        Rvalue::PtrOffset { ptr, count } => {
            on_op(ptr);
            on_op(count);
        }
        Rvalue::Aggregate(_, ops) => ops.iter().for_each(on_op),
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => f(place),
        Rvalue::Unsupported { operands, .. } => operands.iter().for_each(on_op),
        // `#[non_exhaustive]` in `trust-types`: a variant this crate has never seen may
        // read anything, so the gates that rely on this walk must fail closed.
        _ => return false,
    }
    true
}

/// The `CharIndices` iterator local's SOURCE STRING root: `iter_local` must be
/// single-def by a std/core `char_indices` call whose receiver roots via
/// [`charindices_shared_slice_root`].
pub(super) fn charindices_iter_string_root(
    func: &VerifiableFunction,
    iter_local: usize,
) -> Option<usize> {
    // The call-destination hop, on the same gate as every other tracer's
    // (`call_dest_hop`): the `char_indices` call must be the local's only write
    // channel, with the `&mut` conduit readmitted only under the `next`-only
    // discipline. This used to be `has_one_explicit_def` + no projected write +
    // the conduit gate followed by a first-call scan — the same answer spelled by
    // hand; it is now the seam's.
    // Trust (2026-09-29): the `for` desugar moves the `into_iter` result into the
    // loop's own local (`_4 = move _2`) before `&mut _4` feeds `next`. Follow such
    // whole-local moves through the origin hop ([`iterator_origin_def`]: the
    // iterator's only mutation is `next` on itself, which never changes which string
    // its yields index).
    let mut iter_local = iter_local;
    for _ in 0..4 {
        if crate::local_defs::is_parameter(func, iter_local) {
            return None;
        }
        match crate::local_defs::unique_value_def(func, iter_local)
            .or_else(|| iterator_origin_def(func, iter_local))
        {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                iter_local = q.local;
            }
            _ => break,
        }
    }
    let (mut callee, mut args) = call_dest_hop(func, iter_local)?;
    // Trust (2026-09-29): a `for` loop iterates `IntoIterator::into_iter(it)`, which
    // for an iterator is the identity — `impl<I: Iterator> IntoIterator for I` is the
    // one impl that can apply to std's `CharIndices`, since the trait and the type are
    // both foreign to every user crate. Hop it when its argument is itself a
    // `CharIndices` local, so `for (i, c) in s.char_indices() { .. &s[i..] }` credits
    // `i` as `while let Some((i, c)) = it.next()` already did (p37 of the ordinary-Rust
    // sweep). The hop is the same gated call-destination hop.
    if callee_is_into_iter(callee)
        && let [Operand::Copy(arg) | Operand::Move(arg)] = args
        && arg.projections.is_empty()
        && matches!(
            crate::local_ty_ref(func, arg.local),
            Some(Ty::Adt { name, .. }) if adt_is_char_indices(name)
        )
    {
        (callee, args) = call_dest_hop(func, arg.local)?;
    }
    if method_tail(callee) == "char_indices"
        && (callee.starts_with("core::str::") || callee.starts_with("std::str::"))
        && args.len() == 1
    {
        return charindices_shared_slice_root(func, &args[0]);
    }
    None
}

/// True iff `op` IS (a single-def Use-copy of) the `.0` byte-index payload of a
/// `CharIndices::next() == Some` yield whose iterated string roots to a local in
/// `receiver_roots` — the full gate chain of the module banner above.
pub(super) fn operand_is_charindices_yield_of(
    func: &VerifiableFunction,
    op: &Operand,
    receiver_roots: &FxHashSet<usize>,
) -> bool {
    if receiver_roots.is_empty() {
        return false;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return false };
    if !p.projections.is_empty() || crate::local_defs::is_parameter(func, p.local) {
        return false;
    }
    // The payload read: `_i = Copy((_opt as Some).0.0)`.
    let Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src))) =
        crate::local_defs::unique_value_def(func, p.local)
    else {
        return false;
    };
    if !is_enumerate_index_projection(&src.projections) {
        return false;
    }
    if !crate::local_defs::has_one_explicit_def(func, p.local)
        || guards::local_is_mutably_borrowed(func, p.local)
        || local_has_projected_write(func, p.local)
    {
        return false;
    }
    // The ENTRANCE hop, on the same question as every other tracer's
    // (`next_call_receiver` = `local_defs::unique_value_call`): the producing `next`
    // call must be the Option local's ONLY write channel. This lane already refused a
    // second definition, a `&mut` borrow and a projected store by hand; the seam
    // question refuses all of those and the channels the hand-written list did not
    // name (`Drop`, `Deinit`, an unlocatable write, a `TailCall`).
    let Some(r_local) = next_call_receiver(func, src.local) else { return false };
    if crate::local_defs::is_parameter(func, r_local) {
        return false;
    }
    // The receiver must be a `&mut CharIndices` temp.
    let recv_is_char_indices = matches!(
        crate::local_ty_ref(func, r_local),
        Some(Ty::Ref { mutable: true, inner })
            if matches!(inner.as_ref(), Ty::Adt { name, .. } if adt_is_char_indices(name))
    );
    if !recv_is_char_indices || !crate::local_defs::has_one_explicit_def(func, r_local) {
        return false;
    }
    let Some(Rvalue::Ref { mutable: true, place: it }) =
        crate::local_defs::unique_value_def(func, r_local)
    else {
        return false;
    };
    if !it.projections.is_empty() {
        return false;
    }
    charindices_iter_string_root(func, it.local).is_some_and(|root| receiver_roots.contains(&root))
}

/// std's inherent `str::find` / `str::rfind`, for any pattern
/// (`core::str::<impl str>::find::<char>`). The root must be an authenticated sysroot
/// crate, which a trait-qualified `<R as T>::find` spelling never is.
pub(super) fn callee_is_std_str_find(callee: &str) -> bool {
    matches!(super::method_tail(callee), "find" | "rfind")
        && trust_types::path_root_is_authenticated_sysroot_crate(callee)
        && matches!(
            vc_strip_generics_cow(callee).as_ref(),
            "core::str::find" | "core::str::rfind" | "std::str::find" | "std::str::rfind"
        )
}

/// std's inherent `str::is_char_boundary` (`core::str::<impl str>::is_char_boundary`),
/// authenticated at the sysroot root.
pub(super) fn callee_is_std_str_is_char_boundary(callee: &str) -> bool {
    super::method_tail(callee) == "is_char_boundary"
        && trust_types::path_root_is_authenticated_sysroot_crate(callee)
        && vc_strip_generics_cow(callee) == "core::str::is_char_boundary"
}

/// The results of every `s.is_char_boundary(e)` test of the str-slice endpoint `op`,
/// as one condition (their disjunction; they are one value), or `None` when there is
/// no such test.
///
/// Trust (2026-09-29). `is_char_boundary(e)` is true exactly when `e` is `0`, the
/// length, or the start of a char — so on a path where it held, `&s[..e]` and
/// `&s[e..]` cannot panic on the boundary check and `e <= s.len()`. The test counts
/// only if its result is a single-assignment `bool` whose only write is that call
/// (std's, [`callee_is_std_str_is_char_boundary`]), its receiver is a stable shared
/// string rooted in `receiver_roots` ([`charindices_shared_slice_root`]) and its
/// argument is the SAME value as the endpoint: the same single-assignment local, or
/// the same constant. Neither that local nor the string root may be written inside a
/// cycle ([`local_written_in_a_cycle`]), so each holds one value for the whole run
/// and the result describes the pair the slice uses. `if n <= s.len() && s.is_char_boundary(n) { &s[..n] }` (p59 of
/// the ordinary-Rust sweep) was refuted before, the endpoint having been neither 0
/// nor a yield.
pub(super) fn char_boundary_tests_of(
    func: &VerifiableFunction,
    op: &Operand,
    receiver_roots: &FxHashSet<usize>,
) -> Option<Formula> {
    if receiver_roots.is_empty() || !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    enum EndpointKind {
        Local(usize),
        ConstUint(u128),
    }
    let endpoint = match op {
        Operand::Copy(b) | Operand::Move(b) => {
            if !b.projections.is_empty()
                || !crate::local_defs::is_single_static_assignment(func, b.local)
                || local_written_in_a_cycle(func, b.local)
            {
                return None;
            }
            EndpointKind::Local(b.local)
        }
        Operand::Constant(ConstValue::Uint(b, _)) => EndpointKind::ConstUint(*b),
        _ => return None,
    };
    let same_value = |arg: &Operand| match (arg, &endpoint) {
        (Operand::Copy(a) | Operand::Move(a), EndpointKind::Local(b_local)) => {
            a.projections.is_empty() && a.local == *b_local
        }
        (Operand::Constant(ConstValue::Uint(a, _)), EndpointKind::ConstUint(b)) => a == b,
        _ => false,
    };
    let mut tests = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        let [recv, arg] = args.as_slice() else { continue };
        if !dest.projections.is_empty()
            || !same_value(arg)
            || !callee_is_std_str_is_char_boundary(callee)
        {
            continue;
        }
        let result = dest.local;
        if !crate::local_defs::is_single_static_assignment(func, result)
            || !matches!(
                crate::local_defs::unique_value_call(func, result),
                Some(Terminator::Call { func: c, .. }) if std::ptr::eq(c, callee)
            )
            || !charindices_shared_slice_root(func, recv)
                .is_some_and(|r| receiver_roots.contains(&r) && !local_written_in_a_cycle(func, r))
        {
            continue;
        }
        tests.push(Formula::var_owned(
            crate::place_to_var_name(func, &Place::local(result)),
            Sort::Bool,
        ));
    }
    match tests.len() {
        0 => None,
        1 => tests.pop(),
        _ => Some(Formula::Or(tests)),
    }
}

/// True unless `local` provably holds ONE value for the whole run: a parameter, or a
/// local whose single defining block ([`crate::local_defs::unique_defining_block`],
/// which sees every write channel and declines on a partial, escaping or unlocatable
/// one) lies on no CFG cycle. A relation between two single-assignment locals — a
/// test result and the value it tested — holds everywhere only when neither side is
/// rewritten after the other: inside a loop, a later iteration can redefine the
/// tested value while the result still holds the previous one. Fail-closed: a local
/// with no unique defining block answers `true`.
fn local_written_in_a_cycle(func: &VerifiableFunction, local: usize) -> bool {
    if crate::local_defs::is_parameter(func, local) {
        return !crate::local_defs::holds_one_value(func, local);
    }
    let Some(def) = crate::local_defs::unique_defining_block(func, local) else { return true };
    let push_successors = |id: BlockId, work: &mut Vec<BlockId>| {
        if let Some(b) = func.body.blocks.get(id.0).filter(|b| b.id == id) {
            super::loop_bounds::for_each_terminator_succ(&b.terminator, |t| work.push(BlockId(t)));
        }
    };
    let def = BlockId(def);
    let mut seen: FxHashSet<BlockId> = FxHashSet::default();
    let mut work = Vec::new();
    push_successors(def, &mut work);
    while let Some(next) = work.pop() {
        if next == def {
            return true;
        }
        if seen.insert(next) {
            push_successors(next, &mut work);
        }
    }
    false
}

/// std's `<Option<T> as Try>::branch`, the `?` desugar: `Some(v)` becomes
/// `ControlFlow::Continue(v)`. The self type and the trait are both read from the
/// qualified spelling; an unauthenticated crate stamp anywhere refuses.
fn callee_is_std_option_try_branch(callee: &str) -> bool {
    callee.starts_with('<')
        && super::method_tail(callee) == "branch"
        && callee.contains("Option")
        && !trust_types::path_has_unauthenticated_crate_stamp(callee)
        && ParsedQualifier::parse(callee).is_some_and(|q| {
            // The extractor stamps the method `branch::<__trust_try_total>`.
            vc_strip_generics_cow(q.self_ty) == "core::option::Option"
                && q.trait_path.is_some_and(|trait_path| {
                    vc_strip_generics_cow(q.method) == "branch"
                        && matches!(
                            vc_strip_generics_cow(trait_path).as_ref(),
                            "core::ops::try_trait::Try" | "core::ops::Try"
                        )
                })
        })
}

/// std's `<Result<T, E> as Try>::branch`, the `?` desugar on a `Result`: `Ok(v)`
/// becomes `ControlFlow::Continue(v)`. Read exactly as
/// [`callee_is_std_option_try_branch`].
fn callee_is_std_result_try_branch(callee: &str) -> bool {
    callee.starts_with('<')
        && super::method_tail(callee) == "branch"
        && callee.contains("Result")
        && !trust_types::path_has_unauthenticated_crate_stamp(callee)
        && ParsedQualifier::parse(callee).is_some_and(|q| {
            vc_strip_generics_cow(q.self_ty) == "core::result::Result"
                && q.trait_path.is_some_and(|trait_path| {
                    vc_strip_generics_cow(q.method) == "branch"
                        && matches!(
                            vc_strip_generics_cow(trait_path).as_ref(),
                            "core::ops::try_trait::Try" | "core::ops::Try"
                        )
                })
        })
}

/// The call-result local and the variant index whose field 0 the place `src`
/// reads: `(r as V).0` directly (`V` = 1 for `Some`, 0 for `Ok`; which one applies
/// is settled by the callee's own summary), or `(c as Continue).0` where `c`'s only
/// write is std's `Option`/`Result` `Try::branch(r)`, which moves `r`'s `Some` / `Ok`
/// payload into `Continue` unchanged.
fn payload_read_of_call_result(func: &VerifiableFunction, src: &Place) -> Vec<(usize, usize)> {
    use trust_types::Projection::{Downcast, Field};
    let mut out = Vec::new();
    match src.projections.as_slice() {
        [Downcast(1), Field(0)] => out.push((src.local, 1)),
        [Downcast(0), Field(0)] => {
            out.push((src.local, 0));
            if let Some((callee, args)) = call_dest_hop(func, src.local)
                && let [Operand::Copy(r) | Operand::Move(r)] = args
                && r.projections.is_empty()
            {
                if callee_is_std_option_try_branch(callee) {
                    out.push((r.local, 1));
                } else if callee_is_std_result_try_branch(callee) {
                    out.push((r.local, 0));
                }
            }
        }
        _ => {}
    }
    out
}

/// Trust (2026-10-01): the per-block map of payload-interval facts. For each
/// payload `x = (r as Some).0` / `(r as Ok).0`, or `x = (c as Continue).0` under
/// `c = Try::branch(r)` (the `?` desugar), where `r`'s one value is a call reaching
/// a summarized local body ([`crate::call_reaches_summarized_body`]) whose payload
/// return interval was recorded for the SAME variant, `lo <= x <= hi`. The summary
/// holds for every completed call ([`crate::compute_return_payload_interval_summaries`]);
/// `x` passes [`payload_carries_global_fact`], so the fact is about its one value.
/// Sweep A6: `let h = digit(hi)?; let l = digit(lo)?; h * 10 + l` with `digit`
/// returning `Some(c)` under `c <= 9` was refuted with `h = 26`.
pub(crate) fn build_payload_interval_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return FxHashMap::default();
    }
    let Some(summaries) = crate::current_callee_summaries()
        .filter(crate::CalleeSummaryContext::has_any_return_payload_interval)
    else {
        return FxHashMap::default();
    };
    let mut interval_call_locals: FxHashSet<usize> = FxHashSet::default();
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, dest, .. } = &block.terminator
            && dest.projections.is_empty()
            && summaries.return_payload_interval(callee).is_some()
            && summaries.call_reaches_summarized_body(&block.terminator)
        {
            interval_call_locals.insert(dest.local);
        }
    }
    if interval_call_locals.is_empty() {
        return FxHashMap::default();
    }
    let mut payloads: Vec<(usize, Vec<Formula>)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            match src.projections.as_slice() {
                [trust_types::Projection::Downcast(1), trust_types::Projection::Field(0)] => {
                    if !interval_call_locals.contains(&src.local) {
                        continue;
                    }
                }
                [trust_types::Projection::Downcast(0), trust_types::Projection::Field(0)] => {}
                _ => continue,
            }
            for (result, variant) in payload_read_of_call_result(func, src) {
                if !interval_call_locals.contains(&result) {
                    continue;
                }
                let Some(term @ Terminator::Call { func: callee, dest: call_dest, .. }) =
                    crate::local_defs::unique_value_call(func, result)
                else {
                    continue;
                };
                if !call_dest.projections.is_empty() {
                    continue;
                }
                let Some((v, lo, hi)) = summaries.return_payload_interval(callee) else {
                    continue;
                };
                if v != variant || !summaries.call_reaches_summarized_body(term) {
                    continue;
                }
                if !payload_carries_global_fact(func, dest.local) {
                    break;
                }
                let x = Formula::var_owned(
                    place_to_var_name(func, &Place::local(dest.local)),
                    Sort::Int,
                );
                let facts = match (lo, hi) {
                    (Some(lo), Some(hi)) => vec![
                        Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(lo))),
                        Formula::Le(Box::new(x), Box::new(Formula::Int(hi))),
                    ],
                    (Some(lo), None) => vec![Formula::Ge(Box::new(x), Box::new(Formula::Int(lo)))],
                    (None, Some(hi)) => vec![Formula::Le(Box::new(x), Box::new(Formula::Int(hi)))],
                    (None, None) => Vec::new(),
                };
                payloads.push((dest.local, facts));
                break;
            }
        }
    }
    attach_payload_facts(func, payloads)
}

/// The `Option` local whose `Some` payload the place `src` reads: `(o as Some).0`,
/// or `(c as Continue).0` where `c`'s only write is std's `<Option<T> as
/// Try>::branch(o)` — the `?` desugar, which moves the payload into `Continue`
/// unchanged (`let i = s.rfind('.')?`).
pub(super) fn option_payload_source(func: &VerifiableFunction, src: &Place) -> Option<usize> {
    if is_some_payload_projection(&src.projections) {
        return Some(src.local);
    }
    if !matches!(
        src.projections.as_slice(),
        [trust_types::Projection::Downcast(0), trust_types::Projection::Field(0)]
    ) {
        return None;
    }
    let (callee, args) = call_dest_hop(func, src.local)?;
    if !callee_is_std_option_try_branch(callee) {
        return None;
    }
    let [Operand::Copy(o) | Operand::Move(o)] = args else { return None };
    o.projections.is_empty().then_some(o.local)
}

/// The `str::find` / `str::rfind` call whose result is the `Option` local
/// `option`: its receiver's stable shared root ([`charindices_shared_slice_root`])
/// and whether the pattern is a `char` (a match of one is at least a byte long).
/// The call must be the local's only write ([`call_dest_hop`]).
pub(super) fn str_find_call(func: &VerifiableFunction, option: usize) -> Option<(usize, bool)> {
    let (callee, args) = call_dest_hop(func, option)?;
    if !callee_is_std_str_find(callee) {
        return None;
    }
    let root = charindices_shared_slice_root(func, args.first()?)?;
    Some((root, callee.ends_with("::<char>")))
}

/// The receiver root of the `str::find` / `str::rfind` whose `Some` payload the
/// place `src` reads ([`option_payload_source`], [`str_find_call`]).
pub(super) fn str_find_payload_receiver_root(
    func: &VerifiableFunction,
    src: &Place,
) -> Option<usize> {
    str_find_call(func, option_payload_source(func, src)?).map(|(root, _)| root)
}

/// `(o, d)` when `local`'s only write is std's `Option::unwrap_or(o, d)` with `o` a
/// projection-free local: its value is `o`'s `Some` payload, or `d`.
pub(super) fn option_unwrap_or_parts(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(usize, &Operand)> {
    let Some(Terminator::Call { func: callee, args, dest, .. }) =
        crate::local_defs::unique_value_call(func, local)
    else {
        return None;
    };
    let [Operand::Copy(o) | Operand::Move(o), default] = args.as_slice() else { return None };
    if !dest.projections.is_empty()
        || !o.projections.is_empty()
        || !callee.contains("::option::Option")
        || !is_std_unwrap_or_call(callee)
    {
        return None;
    }
    Some((o.local, default))
}

/// True iff `d` is a char boundary of every string rooted at `root`: the constant 0,
/// or a single-valued copy of the root's own length (`PtrMetadata`, which `s.len()`
/// is extracted as). A string's length is a boundary of it.
fn operand_is_zero_or_len_of_root(func: &VerifiableFunction, d: &Operand, root: usize) -> bool {
    match d {
        Operand::Constant(ConstValue::Uint(0, _)) => true,
        Operand::Copy(q) | Operand::Move(q) if q.projections.is_empty() => matches!(
            crate::local_defs::unique_value_def(func, q.local),
            Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner))
                if charindices_shared_slice_root(func, inner) == Some(root)
        ),
        _ => false,
    }
}

/// True iff `op` IS (a single-def Use-copy of) the `Some` payload of std's
/// `str::find` / `str::rfind` on a string whose root is in `receiver_roots`.
///
/// Trust (2026-09-29). The payload is the byte offset of a match START in the
/// receiver, whatever the pattern: `find` and `rfind` return the start their
/// `Searcher` reported, and `core::str::pattern::Searcher` is an `unsafe trait`
/// because the indices it returns "are required to lie on valid utf8 boundaries in
/// the haystack". So the payload is a char boundary of the receiver, at most its
/// length, and `&s[..i]` / `&s[i..]` at it cannot panic on the boundary check. Its
/// bounds half is a global fact (`container_len::build_str_find_guard_map`); this is
/// the boundary half, which no formula term carries. The gates on the copy are the
/// `char_indices` lane's above. A DERIVED offset (`i + 1`) is not a payload and gets
/// nothing: it can land inside a multi-byte char.
pub(super) fn operand_is_str_find_payload_of(
    func: &VerifiableFunction,
    op: &Operand,
    receiver_roots: &FxHashSet<usize>,
) -> bool {
    if receiver_roots.is_empty() {
        return false;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, p.local) {
        let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
            return false;
        };
        if !str_find_payload_receiver_root(func, src)
            .is_some_and(|root| receiver_roots.contains(&root))
        {
            return false;
        }
        return crate::local_defs::has_one_explicit_def(func, p.local)
            && !guards::local_is_mutably_borrowed(func, p.local)
            && !local_has_projected_write(func, p.local);
    }
    // `s.find(p).unwrap_or(d)`: the payload or `d`, so a boundary when `d` is one —
    // 0 or `s.len()` (`&s[..s.find(',').unwrap_or(s.len())]`).
    if let Some((o, d)) = option_unwrap_or_parts(func, p.local) {
        if (!matches!(d, Operand::Constant(ConstValue::Uint(0, _)))
            && !matches!(d, Operand::Copy(q) | Operand::Move(q) if q.projections.is_empty()))
            || !crate::local_defs::has_one_explicit_def(func, p.local)
            || guards::local_is_mutably_borrowed(func, p.local)
            || local_has_projected_write(func, p.local)
        {
            return false;
        }
        return str_find_call(func, o).is_some_and(|(root, _)| {
            receiver_roots.contains(&root) && operand_is_zero_or_len_of_root(func, d, root)
        });
    }
    false
}

#[cfg(test)]
mod qualifier_and_generics_perf_tests {
    use std::borrow::Cow;

    use super::{
        ParsedQualifier, vc_qualified_self_ty, vc_qualified_trait_method, vc_qualifier_group,
        vc_strip_generics_cow,
    };

    fn reference_strip_generics(input: &str) -> String {
        if !input.contains(['<', '>']) && !input.contains(":::") {
            return input.trim_matches(':').to_string();
        }
        let mut without_generics = String::with_capacity(input.len());
        let mut depth = 0usize;
        let mut prev = '\0';
        for c in input.chars() {
            match c {
                '<' => depth += 1,
                '>' if prev == '-' => {
                    if depth == 0 {
                        without_generics.push(c);
                    }
                }
                '>' => depth = depth.saturating_sub(1),
                _ if depth == 0 => without_generics.push(c),
                _ => {}
            }
            prev = c;
        }
        if !without_generics.contains(":::")
            && !without_generics.starts_with(':')
            && !without_generics.ends_with(':')
        {
            return without_generics;
        }
        let mut out = String::with_capacity(without_generics.len());
        for seg in without_generics.split("::").filter(|seg| !seg.is_empty()) {
            if !out.is_empty() {
                out.push_str("::");
            }
            out.push_str(seg);
        }
        out
    }

    #[test]
    fn strip_generics_cow_borrows_trailing_generics_and_matches_reference() {
        let borrow_cases = [
            "core::ops::arith::Add<u32>",
            "core::ops::index::Index<core::ops::range::Range<usize>>",
            "core::ops::function::FnOnce<(u32, fn(&str) -> bool)>",
            "alloc::vec::from_elem::<u8>",
            "alloc::vec::from_elem::<fn() -> u8>::<__trust_elem_bytes@8>",
            "core::iter::traits::iterator::Iterator::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>",
            "core::num::nonzero::NonZero<i32>",
            "core::cmp::Ord",
        ];
        for sample in borrow_cases {
            let got = vc_strip_generics_cow(sample);
            assert!(
                matches!(got, Cow::Borrowed(_)),
                "expected zero-alloc Cow::Borrowed for `{sample}`, got {got:?}"
            );
            assert_eq!(got.as_ref(), reference_strip_generics(sample), "mismatch on `{sample}`");
        }

        let tricky_cases = [
            "",
            ":::",
            ":<T>::<U>",
            "a:b:<T>",
            "a:b::<T>",
            "a::::b<T>",
            "foo->bar<T>",
            "foo>bar<T>",
            "<T>",
            "foo<unclosed",
            "alloc::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes@1>",
            "<Map<I, for<'a> fn(&'a str) -> String {f}> as core::iter::Iterator>::collect::<Vec<String>>",
            "λ_utf8::αβγ::<fn(&str) -> usize>::δ",
            "λ_utf8::αβγ::<fn(&str) -> usize>",
        ];
        for sample in tricky_cases {
            let got = vc_strip_generics_cow(sample);
            assert_eq!(got.as_ref(), reference_strip_generics(sample), "mismatch on `{sample}`");
        }
    }

    #[test]
    fn parsed_qualifier_handles_arrows_nested_as_and_utf8_in_single_pass() {
        let map_sum = "<core::iter::Map<I, fn(u8) -> <u32 as core::ops::Not>::Output {f}> as \
                       core::iter::traits::iterator::Iterator>::sum::<u32>";
        let q = ParsedQualifier::parse(map_sum);
        assert_eq!(
            q,
            Some(ParsedQualifier {
                inner: "core::iter::Map<I, fn(u8) -> <u32 as core::ops::Not>::Output {f}> as \
                        core::iter::traits::iterator::Iterator",
                self_ty: "core::iter::Map<I, fn(u8) -> <u32 as core::ops::Not>::Output {f}>",
                trait_path: Some("core::iter::traits::iterator::Iterator"),
                method: "sum::<u32>",
            })
        );
        assert_eq!(
            vc_qualified_trait_method(map_sum),
            Some(("core::iter::traits::iterator::Iterator", "sum::<u32>"))
        );
        assert_eq!(
            vc_qualified_self_ty(map_sum),
            Some("core::iter::Map<I, fn(u8) -> <u32 as core::ops::Not>::Output {f}>")
        );

        let inherent = "<[u8]>::iter";
        assert_eq!(vc_qualifier_group(inherent), Some(("[u8]", "iter")));
        assert_eq!(vc_qualified_trait_method(inherent), None);
        assert_eq!(vc_qualified_self_ty(inherent), Some("[u8]"));

        let double_as = "<Foo as as Bar>::baz";
        assert_eq!(vc_qualified_self_ty(double_as), Some("Foo as"));
        assert_eq!(vc_qualified_trait_method(double_as), Some(("Bar", "baz")));
    }
}
