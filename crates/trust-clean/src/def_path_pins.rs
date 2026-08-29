//! Pinned std/core/alloc def-path spellings — BOTH renderings the extractor has
//! shipped, and why accepting both is not a widening.
//!
//! # The drift
//!
//! `trust_mir_extract::safe_def_path_str` renders every name it stamps into a
//! dump as
//!
//! ```text
//! with_resolve_crate_name!(with_no_visible_paths!(with_no_trimmed_paths!(
//!     tcx.def_path_str(def_id)
//! )))
//! ```
//!
//! since `bd2d6ed1fc` (2026-07-13, "canonicalize extractor fixture identities"),
//! whose own doc comment states the requirement: the string "must neither omit
//! the local crate nor select a context-dependent visible re-export". Before
//! that commit only `with_no_trimmed_paths!` was applied, so rustc's
//! `try_print_visible_def_path` fired first and every std item reached a dump
//! under the path a *user* would type. After it, the same item reaches a dump
//! under its DEFINITION-SITE path:
//!
//! | pre-2026-07-13 (visible re-export) | post-2026-07-13 (definition site) |
//! |---|---|
//! | `std::sync::Arc`            | `alloc::sync::Arc` |
//! | `std::boxed::Box`           | `alloc::boxed::Box` |
//! | `std::ptr::NonNull`         | `core::ptr::non_null::NonNull` |
//! | `std::ptr::Unique`          | `core::ptr::unique::Unique` |
//! | `std::collections::HashSet` | `std::collections::hash::set::HashSet` |
//! | `std::ops::Deref::deref`    | `<alloc::sync::Arc<E> as core::ops::deref::Deref>::deref` |
//!
//! The last row is the same cause, not a second one: with visible paths off,
//! rustc's `print_def_path` cannot shortcut a trait method to its re-export and
//! falls through to the QUALIFIED impl form, which additionally names the `Self`
//! type.
//!
//! Every fixture dumped before 2026-07-13 carries the left column; every fixture
//! dumped after it carries the right column. The shipped corpora contain both
//! (78 `std::ops::Deref::deref` occurrences across the older corpora against 39
//! qualified ones in the freshly regenerated `structural-fold-corpus`), so a
//! recognizer that pins ONE spelling is wrong against half the tree no matter
//! which one it picks.
//!
//! # Why accepting both is not a widening
//!
//! For every row above the two strings are two RENDERINGS OF ONE `DefId`:
//! `std::sync::Arc` is literally `pub use alloc::sync::Arc`, so the set of
//! rustc types the pin admits is unchanged — it is still exactly one type. The
//! pin's soundness argument never depended on the spelling being unique-in-the-
//! universe (a def path is user-spellable either way; that is why the recognizer
//! also checks the STRUCTURE at every use site), it depended on the spelling
//! naming the intended item. Both spellings name it.
//!
//! What would be a widening — and is deliberately NOT done here — is accepting a
//! prefix, a suffix, or a "contains", any of which would admit a genuinely
//! different item. Every predicate below is an exact match against a closed
//! two-element table, except [`is_arc_deref_callee`] and
//! [`is_hashset_insert_callee`], which parse the two structured renderings and
//! are TIGHTER than the flat string they replace (see their own docs).
//!
//! # The SECOND drift: a callee carries its INSTANTIATION, a dump does not
//!
//! Since `938bfd12e9` (2026-07-13) a `Terminator::Call.func` is stamped by
//! `trust_mir_extract::convert::func_operand_name`, which renders
//! `safe_def_path_str_with_args(def_id, args)` and then appends
//! `disambiguate_generic_call_path`'s fixed-format generic-argument
//! disambiguator. A DUMP's `def_path` is still stamped by the args-FREE
//! `safe_def_path_str(def_id)` (`trust-mir-extract/src/lib.rs:1408`). So ONE
//! generic body is reached by MANY call-site spellings:
//!
//! ```text
//! dump def_path  extract_foldmemo::expr::stack_safe
//! callee (A)     extract_foldmemo::expr::stack_safe::<bool, {closure@src/level/mod.rs:1285:20: 1285:22}>::<__trust_args@8a2184a4…>
//! callee (B)     extract_foldmemo::expr::stack_safe::<(),   {closure@src/level/mod.rs:1349:42: 1349:44}>::<__trust_args@96bdbe4e…>
//! ```
//!
//! [`without_args_disambiguator`] and [`turbofish_head`] are the two EXACT
//! inverses of those two producer decorations. Neither searches the path text:
//! the disambiguator is a FIXED-WIDTH suffix located by arithmetic, and the
//! turbofish is found by a single structural left-to-right scan that tracks
//! angle-bracket depth. Both fail closed — a path that does not parse is
//! returned/reported unchanged, never partially matched.

/// `std::sync::Arc`, both renderings.
pub(crate) const ARC: [&str; 2] = ["std::sync::Arc", "alloc::sync::Arc"];

/// `std::boxed::Box`, both renderings.
pub(crate) const BOX: [&str; 2] = ["std::boxed::Box", "alloc::boxed::Box"];

/// `std::ptr::NonNull`, both renderings.
pub(crate) const NON_NULL: [&str; 2] = ["std::ptr::NonNull", "core::ptr::non_null::NonNull"];

/// `std::ptr::Unique`, both renderings.
pub(crate) const UNIQUE: [&str; 2] = ["std::ptr::Unique", "core::ptr::unique::Unique"];

/// `std::collections::HashSet`, both renderings.
pub(crate) const HASH_SET: [&str; 2] =
    ["std::collections::HashSet", "std::collections::hash::set::HashSet"];

/// `core::ops::Deref`, both renderings — the TRAIT, as it appears inside a
/// qualified `<Self as Trait>::method` callee path.
const DEREF_TRAIT: [&str; 2] = ["std::ops::Deref", "core::ops::deref::Deref"];

/// The flat (pre-2026-07-13) rendering of the `Deref::deref` callee.
const DEREF_CALLEE_FLAT: [&str; 2] = ["std::ops::Deref::deref", "core::ops::deref::Deref::deref"];

/// `stacker::maybe_grow` — the P-STACK trampoline primitive. One spelling: it
/// is a plain free function in a third-party crate, so neither the
/// visible-path flip nor the qualified-impl rendering applies to it.
const STACKER_MAYBE_GROW: [&str; 1] = ["stacker::maybe_grow"];

/// Exact membership in a closed spelling table. Never a prefix/suffix test.
#[must_use]
pub(crate) fn is(name: &str, pins: &[&str]) -> bool {
    pins.contains(&name)
}

// ---------------------------------------------------------------------------
// The producer's two call-path decorations, parsed by their EXACT format
// ---------------------------------------------------------------------------

/// The literal opener of the generic-argument disambiguator, byte-for-byte as
/// `trust_mir_extract::convert::disambiguate_generic_call_path` writes it:
/// `format!("{path}::<__trust_args@{lo:016x}{hi:016x}>")`.
const ARGS_MARKER_OPEN: &str = "::<__trust_args@";

/// `Fingerprint::split()` gives two `u64` halves, each rendered `{:016x}`.
/// FIXED width is the producer's own injectivity argument (`Fingerprint::to_hex`
/// is not fixed-width and is deliberately not used).
const ARGS_MARKER_HEX_LEN: usize = 32;

/// `"::<__trust_args@" + 32 hex + ">"` — a constant, so the marker is located
/// by ARITHMETIC from the end of the string, never by searching its text.
const ARGS_MARKER_LEN: usize = ARGS_MARKER_OPEN.len() + ARGS_MARKER_HEX_LEN + 1;

/// `path` with the trailing generic-argument disambiguator removed, or `path`
/// unchanged when it carries none.
///
/// # The grammar, and why it cannot over-match
///
/// The ONLY accepted suffix is, exactly:
///
/// ```text
/// "::<__trust_args@" <hex> <hex> … <hex> ">"      (exactly 32 lowercase hex digits)
/// ```
///
/// anchored at the END of the string, at a fixed offset of
/// [`ARGS_MARKER_LEN`] bytes. There is no `find`/`rfind`/`contains`: the
/// candidate window is computed by subtraction and then compared literally, so
/// a `__trust_args`-looking fragment ANYWHERE else in the path is invisible to
/// this function.
///
/// The suffix is not writable in Rust source: `@` is not an identifier
/// character and does not occur in any rustc-rendered path segment outside a
/// `{closure@…}` / `{coroutine@…}` display form, and those render inside braces
/// and end with `}`, never `>`. A user type genuinely NAMED `__trust_args`
/// spells `f::<__trust_args>` — no `@`, no hex — and is rejected. A wrong hex
/// length, an uppercase digit, or an unbalanced `<`/`>` all fall to the
/// unchanged-path branch, i.e. the caller then declines exactly as it does
/// today.
///
/// The head is required to be non-empty: the marker is a SUFFIX of a real call
/// path, never a whole path.
#[must_use]
pub(crate) fn without_args_disambiguator(path: &str) -> &str {
    let Some(head_len) = path.len().checked_sub(ARGS_MARKER_LEN) else { return path };
    if head_len == 0 || !path.is_char_boundary(head_len) {
        return path;
    }
    let (head, marker) = path.split_at(head_len);
    let Some(rest) = marker.strip_prefix(ARGS_MARKER_OPEN) else { return path };
    let Some(hex) = rest.strip_suffix('>') else { return path };
    // LOWERCASE only: `{:016x}` never emits `A`..`F`, so an uppercase run is a
    // string this producer did not write.
    if hex.len() == ARGS_MARKER_HEX_LEN
        && hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
    {
        head
    } else {
        path
    }
}

/// The head of a VALUE path with its ONE trailing turbofish argument list
/// removed — `f::<A, B>` → `f`. `None` when the path does not END in a
/// top-level `::<…>` group, or when its angle brackets are not balanced.
///
/// # Why this is not [`instantiation_head`]
///
/// [`instantiation_head`] splits a TYPE path at its FIRST `<`
/// (`alloc::sync::Arc<Level>` → `alloc::sync::Arc`). A callee is a VALUE path,
/// where rustc's `print_path_with_generic_args` writes `::` before the
/// delimiters (`FmtPrinter::in_value`), the group may be preceded by OTHER,
/// non-trailing groups (`core::slice::<impl [Level]>::iter::<…>`), and the
/// whole path may itself OPEN with `<` (`<Arc<Level> as Deref>::deref`). A
/// first-`<` split is wrong on every one of those, so this is a distinct
/// parser, not a laxer copy.
///
/// # The scan, and why it cannot over-match
///
/// One left-to-right pass tracking angle-bracket depth:
///
/// * a `<` at depth 0 opens a candidate ONLY when the two bytes before it are
///   `::` — i.e. only a real turbofish. A `<` that opens a qualified path
///   (`<SELF as TRAIT>::m`) CLEARS the candidate instead of setting one.
/// * `->` is a return arrow in a rendered function/closure type
///   (`stacker::maybe_grow::<R, impl FnOnce() -> R>`), never a closing
///   delimiter, so a `>` immediately preceded by `-` is skipped. Without this
///   the depth counter goes negative on the shipped `maybe_grow` spelling.
/// * the split is returned ONLY if the LAST byte of the path closes the
///   candidate group back to depth 0. A group that closes earlier is discarded
///   and the scan continues, so `Option::<&Level>::and_then::<Level, {closure@…}>`
///   splits at `and_then`, not at `Option`.
/// * depth going negative, an unclosed group, or an EMPTY argument list (which
///   the producer never emits — `print_path_with_generic_args` writes nothing
///   for empty args) all return `None`.
///
/// Argument text is never inspected: `{closure@src/level/mod.rs:1285:20: 1285:22}`
/// carries `:`, spaces and a file path, and nested groups
/// (`Zip<Iter<'_, Name>, Iter<'_, Level>>`) carry `,` and `<`/`>` — all of which
/// a substring search would trip over and the depth scan does not.
#[must_use]
pub(crate) fn turbofish_head(path: &str) -> Option<&str> {
    let bytes = path.as_bytes();
    let mut depth: usize = 0;
    // Byte index of the first `:` of the `::<` that opened the current
    // depth-0 group, i.e. exactly where the head ends.
    let mut head_end: Option<usize> = None;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'<' => {
                if depth == 0 {
                    head_end =
                        (i >= 2 && bytes[i - 1] == b':' && bytes[i - 2] == b':').then(|| i - 2);
                }
                depth += 1;
            }
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    if i + 1 == bytes.len() {
                        // A group that opened at `head_end` spans `::<` .. `>`;
                        // require at least one argument byte between them.
                        return head_end
                            .filter(|&s| i > s + 3)
                            // FAIL CLOSED on a SEMANTIC marker. This slot is not
                            // reserved for instantiations: `convert.rs` states
                            // "synthetic identity/semantic markers are
                            // deliberately stacked in this position" and puts at
                            // least four there, each of which CHANGES HOW THE
                            // CALL IS MODELLED rather than naming which instance
                            // is called — `__trust_spawn_namesafe` (model the
                            // call panic-free, marked soundness-critical),
                            // `__trust_try_total`, `__trust_elem_bytes@N` (the
                            // authoritative element size behind the hunt-11
                            // capacity-overflow fix; `@`-spelled since the
                            // batch-6 D1 fix — older artifacts may still carry
                            // the retired `__trust_elem_bytes_N`, and BOTH
                            // spellings share the `__trust_` group prefix this
                            // check keys on) and `__trust_str_index`.
                            // Stripping one would silently ERASE it and hand the
                            // caller a key naming the undecorated item, so a
                            // marked callee would join an unmarked body. The
                            // `__trust_args@` disambiguator is not affected: it
                            // is removed beforehand, by exact fixed-width
                            // arithmetic, in `without_args_disambiguator`.
                            .filter(|&s| !path[s + 3..i].starts_with("__trust_"))
                            .map(|s| &path[..s]);
                    }
                    head_end = None;
                }
            }
            _ => {}
        }
    }
    None
}

/// The DUMP key a possibly-INSTANTIATED callee names, or `None` when the callee
/// is already args-free (so the caller's exact lookup has already been tried and
/// there is nothing further to try).
///
/// Removes at most TWO producer decorations, in the order the producer applies
/// them: the fixed-format [`without_args_disambiguator`] suffix, then ONE
/// [`turbofish_head`] group. Never a loop — `def_path_str_with_args` appends the
/// item's OWN arguments as exactly one trailing group
/// (`rustc_middle::ty::print::default_print_def_path` →
/// `print_path_with_generic_args(|p| p.print_def_path(def_id, parent_args), own_args)`),
/// so a second strip would cut into the path proper and could name a DIFFERENT
/// item.
#[must_use]
pub(crate) fn instantiated_callee_body_key(callee: &str) -> Option<&str> {
    let bare = without_args_disambiguator(callee);
    match turbofish_head(bare) {
        Some(head) => Some(head),
        None if bare.len() != callee.len() => Some(bare),
        None => None,
    }
}

/// The GENERIC HEAD of a type path: the path with a well-formed trailing
/// turbofish argument list removed, or the path itself when it carries none.
///
/// `None` — i.e. fail-closed — for a path with an unbalanced/absent closing
/// `>`, which is not a spelling the extractor emits and must therefore never be
/// silently accepted as its own head.
///
/// This exists because R0 made instantiated spellings REACHABLE at type
/// positions, not just in callee text. A canonical cut point is keyed by the
/// name the type actually carries, and an instantiated recursive root carries
/// its arguments (`alloc::sync::Arc<extract_foldmemo::level::Level>`), so a pin
/// that compares the whole string against `alloc::sync::Arc` declines a type it
/// is supposed to admit. Splitting the head is the ONLY relaxation; the head is
/// still matched by exact membership in a closed table, never by a prefix,
/// suffix or `contains`.
///
/// The argument list is deliberately NOT inspected: every recognizer that
/// consumes this already pins the argument structurally, from the dump's own
/// type info, so re-deriving it from display text would be a second, weaker
/// source of the same fact.
#[must_use]
pub(crate) fn instantiation_head(ty_path: &str) -> Option<&str> {
    match ty_path.split_once('<') {
        Some((head, args)) => args.ends_with('>').then_some(head),
        None => Some(ty_path),
    }
}

/// Whether `ty_path` spells one of `pins`, with or without a trailing turbofish
/// argument list (`alloc::sync::Arc` and `alloc::sync::Arc<SOURCE::Tree>` both
/// name the pinned `Arc`).
#[must_use]
pub(crate) fn is_instantiation_of(ty_path: &str, pins: &[&str]) -> bool {
    instantiation_head(ty_path).is_some_and(|head| pins.contains(&head))
}

/// Whether `callee` is the pinned `Deref::deref` on a pinned `Arc<..>`
/// (P-ARC-DEREF), under either rendering.
///
/// STRICTLY TIGHTER on the new spelling, not looser. The flat rendering
/// (`std::ops::Deref::deref`) carries no `Self` type at all, so the old pin
/// admitted `Deref::deref` on ANY receiver and left the `Arc` check entirely to
/// the caller's separate type test. The qualified rendering names `Self`, and
/// this predicate REQUIRES it to be a pinned `Arc` — so a `<Vec<u8> as
/// Deref>::deref` that the flat pin would have admitted is rejected here.
///
/// The generic-argument disambiguator is removed first (by its exact fixed
/// format), because the post-2026-07-13 producer spells this callee
/// `<alloc::sync::Arc<…> as core::ops::deref::Deref>::deref::<__trust_args@…>`.
/// That marker is a rendering of the SAME `DefId` under the SAME `Self` type —
/// the `Self` type is still named in the path proper and is still required to
/// be a pinned `Arc` — so admitting it widens nothing.
#[must_use]
pub(crate) fn is_arc_deref_callee(callee: &str) -> bool {
    let callee = without_args_disambiguator(callee);
    if is(callee, &DEREF_CALLEE_FLAT) {
        return true;
    }
    let Some(qualified) = callee.strip_prefix('<') else { return false };
    let Some((self_ty, tail)) = qualified.split_once(" as ") else { return false };
    let Some(trait_path) = tail.strip_suffix(">::deref") else { return false };
    is(trait_path, &DEREF_TRAIT) && is_instantiation_of(self_ty, &ARC)
}

/// Whether `callee` is the pinned `HashSet::insert` (rung B, design §4), under
/// either rendering.
///
/// The two shipped spellings differ in the TYPE path *and* in the turbofish:
/// `std::collections::HashSet::<T, S, A>::insert` (generic parameters, the
/// pre-2026-07-13 visible-path rendering) against
/// `std::collections::hash::set::HashSet::<i64>::insert` (the call-site
/// instantiation). Pinning either literal would reject the other, so what is
/// pinned is the thing the premise P-ACC-OPAQUE is actually about: `insert` on
/// std's `HashSet`. The turbofish is not inspected — the element type is
/// re-derived structurally at the call site (`as_int` on the inserted operand
/// declines anything that is not a modeled `Int`), which is a stronger check
/// than reading it out of display text.
///
/// As for [`is_arc_deref_callee`], the fixed-format generic-argument
/// disambiguator is removed first: the shipped post-2026-07-13 spelling is
/// `std::collections::hash::set::HashSet::<…>::insert::<__trust_args@…>`.
#[must_use]
pub(crate) fn is_hashset_insert_callee(callee: &str) -> bool {
    let callee = without_args_disambiguator(callee);
    let Some(receiver) = callee.strip_suffix("::insert") else { return false };
    match receiver.split_once("::<") {
        Some((path, args)) => args.ends_with('>') && is(path, &HASH_SET),
        None => is(receiver, &HASH_SET),
    }
}

/// Whether `callee` is the pinned `stacker::maybe_grow`, at ANY instantiation.
///
/// The shipped spelling is
/// `stacker::maybe_grow::<R, impl FnOnce() -> R>::<__trust_args@…>` — the
/// generic body's own call, still carrying `stack_safe`'s parameters. Both
/// producer decorations are removed by their exact format and the ITEM is then
/// matched by exact table membership, never a prefix/suffix/`contains`.
///
/// Erasing the arguments loses nothing the premise depends on: P-STACK is
/// `maybe_grow(red_zone, growth, f) = f()`, which is uniform in `R` and `F`,
/// and the two literals plus the "forward parameter 1, return the result"
/// shape are pinned byte-exactly by the caller. A `maybe_grow` from a SECOND
/// crate also named `stacker` would carry `disambiguate_direct_call_path`'s
/// `__trust_crate@…::` prefix (that prefix is emitted in exactly the
/// duplicate-crate-name compilations where `__trust_args` is emitted), which
/// this predicate retains and the table rejects.
#[must_use]
pub(crate) fn is_stacker_maybe_grow_callee(callee: &str) -> bool {
    let bare = without_args_disambiguator(callee);
    is(turbofish_head(bare).unwrap_or(bare), &STACKER_MAYBE_GROW)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Both renderings of one `DefId` are admitted, and near-misses are not.
    #[test]
    fn both_renderings_of_one_defid_are_admitted_and_neighbours_are_not() {
        for (pins, old, new) in [
            (&ARC[..], "std::sync::Arc", "alloc::sync::Arc"),
            (&BOX[..], "std::boxed::Box", "alloc::boxed::Box"),
            (&NON_NULL[..], "std::ptr::NonNull", "core::ptr::non_null::NonNull"),
            (&UNIQUE[..], "std::ptr::Unique", "core::ptr::unique::Unique"),
            (&HASH_SET[..], "std::collections::HashSet", "std::collections::hash::set::HashSet"),
        ] {
            assert!(is(old, pins), "{old} is the pre-2026-07-13 rendering");
            assert!(is(new, pins), "{new} is the post-2026-07-13 rendering");
        }
        // A user type whose path merely LOOKS like one of the pins, a prefix,
        // and a suffix all decline — the table is an exact match, never a
        // `starts_with` / `ends_with` / `contains`.
        for impostor in [
            "mycrate::sync::Arc",
            "alloc::sync::Arc2",
            "sync::Arc",
            "alloc::sync",
            "alloc::rc::Rc",
            "hashbrown::set::HashSet",
            "std::collections::HashMap",
            "std::collections::hash::map::HashMap",
        ] {
            assert!(
                !is(impostor, &ARC)
                    && !is(impostor, &BOX)
                    && !is(impostor, &NON_NULL)
                    && !is(impostor, &UNIQUE)
                    && !is(impostor, &HASH_SET),
                "{impostor} must not satisfy any pin",
            );
        }
    }

    /// The qualified `Deref` callee is admitted only for a pinned `Arc` `Self`,
    /// which is STRICTLY tighter than the flat spelling it succeeds.
    #[test]
    fn qualified_deref_callee_pins_the_arc_self_type() {
        assert!(is_arc_deref_callee("std::ops::Deref::deref"));
        assert!(is_arc_deref_callee(
            "<alloc::sync::Arc<SOURCE::Tree> as core::ops::deref::Deref>::deref"
        ));
        assert!(is_arc_deref_callee("<std::sync::Arc<Tree> as std::ops::Deref>::deref"));
        for wrong in [
            // Not an Arc receiver — the flat pin could not see this at all.
            "<alloc::vec::Vec<u8> as core::ops::deref::Deref>::deref",
            "<alloc::boxed::Box<Tree> as core::ops::deref::Deref>::deref",
            // Not `Deref`.
            "<alloc::sync::Arc<Tree> as core::ops::deref::DerefMut>::deref_mut",
            "<alloc::sync::Arc<Tree> as core::borrow::Borrow>::borrow",
            // Not the method.
            "<alloc::sync::Arc<Tree> as core::ops::deref::Deref>::deref_mut",
            // A user item that merely contains the text.
            "mycrate::std::ops::Deref::deref",
            "std::ops::Deref::deref_mut",
        ] {
            assert!(!is_arc_deref_callee(wrong), "{wrong} must decline");
        }
    }

    /// The head split is the ONLY relaxation an instantiated cut-point name
    /// gets: the head is still matched by exact table membership, an
    /// unbalanced turbofish declines, and neighbours of a pin stay out.
    #[test]
    fn instantiation_head_splits_only_a_well_formed_turbofish() {
        assert_eq!(instantiation_head("alloc::sync::Arc"), Some("alloc::sync::Arc"));
        assert_eq!(
            instantiation_head("alloc::sync::Arc<extract_foldmemo::level::Level>"),
            Some("alloc::sync::Arc"),
        );
        // Nested arguments still terminate the list.
        assert_eq!(
            instantiation_head("alloc::boxed::Box<alloc::vec::Vec<u8>>"),
            Some("alloc::boxed::Box"),
        );
        // Unbalanced / empty argument lists are not spellings the extractor
        // emits and must never be accepted as their own head.
        assert_eq!(instantiation_head("alloc::sync::Arc<Level"), None);
        assert_eq!(instantiation_head("alloc::sync::Arc<"), None);

        for pinned in ["alloc::sync::Arc", "alloc::sync::Arc<extract_foldmemo::level::Level>"] {
            assert!(is_instantiation_of(pinned, &ARC), "{pinned} names the pinned Arc");
        }
        for impostor in [
            "alloc::sync::Arc2<Level>",
            "mycrate::alloc::sync::Arc<Level>",
            "alloc::rc::Rc<Level>",
            "alloc::sync::Arc<Level",
            "sync::Arc<Level>",
        ] {
            assert!(!is_instantiation_of(impostor, &ARC), "{impostor} must decline");
        }
    }

    /// One REAL shipped callee, byte-for-byte out of
    /// `fixtures/level-fold-corpus/level__Level__has_params.json`.
    const REAL_STACK_SAFE_CALLEE: &str = "extract_foldmemo::expr::stack_safe::<bool, \
         {closure@src/level/mod.rs:1285:20: 1285:22}>::\
         <__trust_args@8a2184a43a70782505085d99a82ff886>";

    /// The generic-args disambiguator is parsed by its EXACT fixed format:
    /// every real spelling is stripped, and every near-miss is left alone (so
    /// the caller declines exactly as it would have).
    #[test]
    fn args_disambiguator_is_parsed_by_its_exact_fixed_format() {
        // Every shape the shipped corpora actually carry.
        for (decorated, bare) in [
            (
                REAL_STACK_SAFE_CALLEE,
                "extract_foldmemo::expr::stack_safe::<bool, \
                 {closure@src/level/mod.rs:1285:20: 1285:22}>",
            ),
            (
                "<alloc::sync::Arc<extract_foldmemo::level::Level> as \
                 core::ops::deref::Deref>::deref::\
                 <__trust_args@c8fc53ba8aefa57cd564f1781115c41c>",
                "<alloc::sync::Arc<extract_foldmemo::level::Level> as \
                 core::ops::deref::Deref>::deref",
            ),
            (
                "stacker::maybe_grow::<R, impl FnOnce() -> R>::\
                 <__trust_args@be746c8a0e7ceac68f9944f3ff2f085f>",
                "stacker::maybe_grow::<R, impl FnOnce() -> R>",
            ),
            (
                "alloc::vec::Vec::<extract_foldmemo::name::Name>::push::\
                 <__trust_args@864c6c2ecd8337c601f7da93ac534a07>",
                "alloc::vec::Vec::<extract_foldmemo::name::Name>::push",
            ),
            (
                "0123456789abcdef::f::<__trust_args@0123456789abcdef0123456789abcdef>",
                "0123456789abcdef::f",
            ),
        ] {
            assert_eq!(without_args_disambiguator(decorated), bare, "{decorated}");
            // Idempotent: the producer appends at most one, and a bare path is
            // never mistaken for a decorated one.
            assert_eq!(without_args_disambiguator(bare), bare, "{bare}");
        }

        // NEAR-MISSES — each returns the path UNCHANGED, so the caller's exact
        // lookup/table match then declines.
        for near_miss in [
            // 31 hex digits, and 33.
            "f::<__trust_args@8a2184a43a70782505085d99a82ff88>",
            "f::<__trust_args@8a2184a43a70782505085d99a82ff8866>",
            // Uppercase is not what `{:016x}` emits.
            "f::<__trust_args@8A2184A43A70782505085D99A82FF886>",
            // A non-hex digit inside an otherwise 32-long run.
            "f::<__trust_args@8a2184a43a70782505085d99a82ff88g>",
            // No `@`.
            "f::<__trust_args8a2184a43a70782505085d99a82ff8861>",
            // No `::` before the turbofish.
            "f<__trust_args@8a2184a43a70782505085d99a82ff886>",
            // Unbalanced / missing close.
            "f::<__trust_args@8a2184a43a70782505085d99a82ff886",
            // A user TYPE literally named `__trust_args` — writable Rust, and
            // it carries neither `@` nor the fingerprint.
            "mycrate::f::<__trust_args>",
            "mycrate::f::<mycrate::__trust_args>",
            "mycrate::__trust_args::f",
            // The marker text NOT in the suffix position (there is no search).
            "f::<__trust_args@8a2184a43a70782505085d99a82ff886>::g",
            // Marker-only: the head must be non-empty.
            "::<__trust_args@8a2184a43a70782505085d99a82ff886>",
        ] {
            assert_eq!(
                without_args_disambiguator(near_miss),
                near_miss,
                "{near_miss} must be left unchanged",
            );
        }
    }

    /// The trailing-turbofish scan: balanced, `->`-aware, anchored at the END,
    /// and `None` on anything malformed.
    #[test]
    fn turbofish_head_is_a_balanced_scan_anchored_at_the_end() {
        for (path, head) in [
            ("f::<A>", "f"),
            ("m::f::<u8, i64>", "m::f"),
            // Nested arguments, and arguments carrying `::`.
            ("m::f::<alloc::vec::Vec<u8>, Foo<Bar<T>>>", "m::f"),
            // Closure display text: colons, spaces and a file path inside.
            (
                "extract_foldmemo::expr::stack_safe::<bool, \
                 {closure@src/level/mod.rs:1285:20: 1285:22}>",
                "extract_foldmemo::expr::stack_safe",
            ),
            // A `->` return arrow is NOT a closing delimiter.
            ("stacker::maybe_grow::<R, impl FnOnce() -> R>", "stacker::maybe_grow"),
            ("m::f::<fn(u8) -> fn(u8) -> u8>", "m::f"),
            // A NON-trailing group is skipped; the split is the LAST one.
            (
                "core::slice::<impl [extract_foldmemo::level::Level]>::iter::<u8>",
                "core::slice::<impl [extract_foldmemo::level::Level]>::iter",
            ),
            (
                "core::option::Option::<&Level>::and_then::<Level, {closure@a.rs:1:1: 1:2}>",
                "core::option::Option::<&Level>::and_then",
            ),
            // A path that OPENS with `<` (qualified trait form) still splits at
            // its own trailing turbofish, not at the qualifier.
            (
                "<alloc::sync::Arc<Level> as core::ops::deref::Deref>::deref::<u8>",
                "<alloc::sync::Arc<Level> as core::ops::deref::Deref>::deref",
            ),
        ] {
            assert_eq!(turbofish_head(path), Some(head), "{path}");
        }

        for none in [
            // No trailing group at all.
            "m::f",
            "core::slice::<impl [Level]>::iter",
            "<alloc::sync::Arc<Level> as core::ops::deref::Deref>::deref",
            // A TYPE path's argument list is not a turbofish (no `::`), which is
            // `instantiation_head`'s job, not this one.
            "alloc::sync::Arc<extract_foldmemo::level::Level>",
            "alloc::boxed::Box<alloc::vec::Vec<u8>>",
            // Unbalanced in either direction.
            "m::f::<u8",
            "m::f::<Vec<u8>",
            "m::f::u8>",
            "m::f::<u8>>",
            // Empty argument list — never emitted by
            // `print_path_with_generic_args`, so never accepted.
            "m::f::<>",
            // The group closes before the end.
            "m::f::<u8>::g",
        ] {
            assert_eq!(turbofish_head(none), None, "{none} must decline");
        }
    }

    /// The composed derivation: at most ONE disambiguator + ONE turbofish, and
    /// `None` for an already-args-free callee (so the caller's exact lookup is
    /// the only thing that ran).
    #[test]
    fn instantiated_callee_body_key_strips_exactly_the_two_producer_decorations() {
        assert_eq!(
            instantiated_callee_body_key(REAL_STACK_SAFE_CALLEE),
            Some("extract_foldmemo::expr::stack_safe"),
        );
        // Marker only, no instantiation turbofish.
        assert_eq!(
            instantiated_callee_body_key(
                "<alloc::sync::Arc<Level> as core::ops::deref::Deref>::deref::\
                 <__trust_args@c8fc53ba8aefa57cd564f1781115c41c>",
            ),
            Some("<alloc::sync::Arc<Level> as core::ops::deref::Deref>::deref"),
        );
        // Instantiation turbofish only, no marker (the ordinary crate graph).
        assert_eq!(instantiated_callee_body_key("m::f::<u8>"), Some("m::f"));
        // NOT a loop: a middle turbofish belongs to the PARENT and is retained,
        // so `Vec::<Name>::push` never collapses to `alloc::vec::Vec`.
        assert_eq!(
            instantiated_callee_body_key(
                "alloc::vec::Vec::<extract_foldmemo::name::Name>::push::<X>",
            ),
            Some("alloc::vec::Vec::<extract_foldmemo::name::Name>::push"),
        );
        assert_eq!(
            instantiated_callee_body_key("alloc::vec::Vec::<extract_foldmemo::name::Name>::push"),
            None,
        );
        // Nothing to derive ⇒ `None` ⇒ the caller declines on its exact lookup.
        for bare in [
            "extract_foldmemo::expr::stack_safe",
            "extract_foldmemo::level::Level::has_params_impl",
            "alloc::sync::Arc<extract_foldmemo::level::Level>",
            "m::f::<u8",
            "mycrate::f::<__trust_args>x",
        ] {
            assert_eq!(instantiated_callee_body_key(bare), None, "{bare}");
        }
    }

    /// `stacker::maybe_grow` is pinned at every instantiation, and only there.
    #[test]
    fn maybe_grow_callee_is_pinned_at_every_instantiation() {
        for ok in [
            "stacker::maybe_grow",
            "stacker::maybe_grow::<R, impl FnOnce() -> R>",
            "stacker::maybe_grow::<R, impl FnOnce() -> R>::\
             <__trust_args@be746c8a0e7ceac68f9944f3ff2f085f>",
            "stacker::maybe_grow::<bool, {closure@src/expr/mod.rs:60:9: 60:11}>",
        ] {
            assert!(is_stacker_maybe_grow_callee(ok), "{ok} is the pinned maybe_grow");
        }
        for wrong in [
            // A different item in the same crate, and a same-named item elsewhere.
            "stacker::grow",
            "stacker::maybe_grow_unchecked::<R>",
            "mycrate::stacker::maybe_grow::<R>",
            "maybe_grow",
            "stacker2::maybe_grow::<R>",
            // A SECOND crate also named `stacker`: the producer prefixes the
            // callee with its stable crate id, which is not the pinned item.
            "__trust_crate@0123456789abcdef::stacker::maybe_grow::<R>",
            // Malformed decorations leave a string the table rejects.
            "stacker::maybe_grow::<R",
            "stacker::maybe_grow::<R>::<__trust_args@be746c8a0e7ceac68f9944f3ff2f085>",
        ] {
            assert!(!is_stacker_maybe_grow_callee(wrong), "{wrong} must decline");
        }
    }

    /// The two structured callee pins see through the disambiguator, and are no
    /// looser for it: the `Self` type / container is still pinned exactly.
    #[test]
    fn structured_callee_pins_see_through_the_args_disambiguator() {
        assert!(is_arc_deref_callee(
            "<alloc::sync::Arc<extract_foldmemo::level::Level> as \
             core::ops::deref::Deref>::deref::\
             <__trust_args@c8fc53ba8aefa57cd564f1781115c41c>"
        ));
        assert!(is_hashset_insert_callee(
            "std::collections::hash::set::HashSet::<extract_foldmemo::name::Name>::insert::\
             <__trust_args@6fa949a0cca84d08b7c78e5acfb97aca>"
        ));
        for wrong in [
            // Right marker, WRONG receiver — the `Self` pin still binds.
            "<alloc::vec::Vec<u8> as core::ops::deref::Deref>::deref::\
             <__trust_args@c8fc53ba8aefa57cd564f1781115c41c>",
            // Right receiver, MALFORMED marker — declines rather than
            // half-matching.
            "<alloc::sync::Arc<extract_foldmemo::level::Level> as \
             core::ops::deref::Deref>::deref::\
             <__trust_args@c8fc53ba8aefa57cd564f1781115c41>",
        ] {
            assert!(!is_arc_deref_callee(wrong), "{wrong} must decline");
        }
        for wrong in [
            "std::collections::hash::map::HashMap::<K, V>::insert::\
             <__trust_args@6fa949a0cca84d08b7c78e5acfb97aca>",
            "hashbrown::set::HashSet::<Name>::insert::\
             <__trust_args@6fa949a0cca84d08b7c78e5acfb97aca>",
        ] {
            assert!(!is_hashset_insert_callee(wrong), "{wrong} must decline");
        }
    }

    /// `HashSet::insert` is admitted under both type-path spellings and with or
    /// without a turbofish; a different container or a different method is not.
    #[test]
    fn hashset_insert_callee_pins_the_container_and_the_method() {
        assert!(is_hashset_insert_callee("std::collections::HashSet::<T, S, A>::insert"));
        assert!(is_hashset_insert_callee("std::collections::hash::set::HashSet::<i64>::insert"));
        assert!(is_hashset_insert_callee("std::collections::HashSet::insert"));
        for wrong in [
            "std::collections::HashMap::<K, V, S, A>::insert",
            "hashbrown::set::HashSet::<i64>::insert",
            "std::collections::hash::set::HashSet::<i64>::remove",
            "std::collections::hash::set::HashSet::<i64>::new",
            "mycrate::insert",
            "insert",
        ] {
            assert!(!is_hashset_insert_callee(wrong), "{wrong} must decline");
        }
    }
}
