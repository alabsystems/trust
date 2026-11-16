// Panic-freedom for the `Option`/`Result` unwrap family. The obligation is
// discharged by pinning the receiver's discriminant tag: trace the value back
// to the call or construction that fixed it, and refute the panicking variant.
// Also the catalogue of std methods that panic on out-of-range arguments.

use super::*;

/// Trust (reliability E1): a call to a std slice/`Vec` method that PANICS on an
/// out-of-range argument (`> len`) but is NOT in `is_known_panicking_method`
/// (Option/Result unwrap family) nor `slice_method_panic` (the precisely-modeled
/// `split_at`/`chunks`/`swap`/range-index lane). These have a normal-return target
/// (the rotated/split slice) but an unmodeled internal panic path:
///   * `<[T]>::rotate_left(mid)` / `rotate_right(mid)` — panic when `mid > len`.
///   * `Vec`/`String`/`VecDeque`::`split_off(at)` — panic when `at > len`.
///   * `Vec`/`String`/`VecDeque`::`drain(range)` — panic when `start > end` or
///     `end > len` (`v.drain(0..99)` on a shorter Vec panics at runtime). The no-arg
///     `HashMap`/`HashSet`/`BinaryHeap::drain()` are TOTAL (drain everything, never
///     panic) — discriminated below by arg count (a range-taking drain has arg 1;
///     a total drain has only the receiver).
///   * `<[T]>::copy_within(src, dest)` — panic when the source range is out of range
///     or `dest + src.len() > len`.
///   * `<[T]>::select_nth_unstable(i)` / `_by` / `_by_key` — panic when `i >= len`.
/// They are surfaced as an UnsupportedMir → Unknown obligation, which can only make
/// the default headline MORE conservative (Unknown, never Proved) — so an
/// over-match is honest-but-imprecise, never unsound.
///
/// SOUNDNESS of the slice/`Vec` discrimination — `rotate_left`/`rotate_right` ALSO
/// name TOTAL integer methods (`u32::rotate_left`, never panics); flagging those
/// would only be over-conservative (Unknown, not a false proof), but we exclude
/// them anyway to keep the default headline clean. The receiver must be a confirmed
/// slice/`Vec`, established by EITHER (a) a modeled slice length on arg 0
/// (`slice_len_formula`/`param_slice_len`, true for `&[T]`/`&mut [T]` receivers),
/// OR (b) a callee path that names the slice/`Vec` container (`slice` / `vec::Vec`
/// / `[T]`) and is NOT an integer-`num` method. An integer rotate renders as
/// `core::num::<impl u32>::rotate_left` (matches neither (a) nor (b)) and is
/// EXCLUDED; an owned `Vec::split_off` (whose `&Vec` receiver has no modeled
/// slice length) is caught by (b).
pub(super) fn is_bounds_panicking_slice_mutator(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> bool {
    let tail = method_tail(callee);
    if !matches!(
        tail,
        "rotate_left"
            | "rotate_right"
            | "split_off"
            | "drain"
            // Slice-only bounds-panicking methods (no total same-name method exists,
            // so no name-collision exclusion is needed like the integer-`rotate` case):
            //   * `<[T]>::copy_within(src, dest)` — panics if `src` is out of range or
            //     `dest + src.len() > len`.
            //   * `<[T]>::select_nth_unstable(i)` / `_by` / `_by_key` — panic if `i >= len`.
            | "copy_within"
            | "select_nth_unstable"
            | "select_nth_unstable_by"
            | "select_nth_unstable_by_key"
            // `Vec::extend_from_within(range)` (T: Copy) — panics on an out-of-range
            // `range` (`start > end` / `end > len`). Unique name (no total same-name
            // method), `Vec` receiver. It ALSO has a capacity-overflow panic path on
            // reallocation; the whole-call fail-honest Unknown covers BOTH soundly
            // (never Proved), so no separate overflow model is needed here.
            | "extend_from_within"
    ) {
        return false;
    }
    // `drain` DISCRIMINATION: only the range-taking drains (`Vec`/`String`/`VecDeque`,
    // whose call carries the receiver PLUS a range arg) panic on a bad range. The no-arg
    // `HashMap`/`HashSet`/`BinaryHeap::drain()` drain everything and are TOTAL — their
    // call has ONLY the receiver (args.len() == 1). Excluding them avoids an unnecessary
    // (still sound: Unknown, non-fatal) over-refusal of a total method. rotate/split_off
    // both take a scalar arg, so they naturally have args.len() == 2 and are unaffected.
    if tail == "drain" && args.len() < 2 {
        return false;
    }
    // Trust (cap vec-drain, 2026-10-03): std's `Vec`/`VecDeque::drain` over `..`,
    // `0..`, `..0` or `0..0` cannot fail its one range check; see the recognizer.
    if super::collection_range::std_vec_drain_range_cannot_panic(func, callee, args) {
        return false;
    }
    // Trust (2026-09-29): `drain(..)` and `drain(0..)` on a std `Vec`, `VecDeque` or
    // `String` drain `0..len`, which is always in range (and `0`/`len` are always char
    // boundaries), so they cannot panic. The row was the only thing refusing
    // `v.drain(..)`, `for x in v.drain(..)` and `d.drain(..)` on the ordinary-Rust
    // sweep; a range that is not provably whole keeps it. (Upstream's recognizer
    // above covers `Vec`/`VecDeque`; this one also covers `String`.)
    if tail == "drain"
        && callee_is_std_growable_container_method(callee)
        && drain_range_is_whole(func, callee, &args[1])
    {
        return false;
    }
    // (b) Path-based fallback for owned `Vec`/`String`/`VecDeque` receivers (no
    // modeled slice length). EXCLUDE integer methods, which render as
    // `core::num::<impl u32>::rotate_left` — `num`/`<impl u`/`<impl i` markers.
    //
    // Trust (W4 fix round 2, 2026-09-26): the EXCLUSION reads the receiver spine
    // (turbofish groups removed), never a generic ARGUMENT. It used to read the whole
    // callee, so a container whose ELEMENT type names an integer method — a sysroot
    // fn item, `Vec::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::split_off`
    // — or any type under a `num` module was excluded as an "integer method":
    // measured on `0.10.0+g6a3460983`, an unguarded `split_off`/`drain`/
    // `extend_from_within` on such a `Vec` (and `split_off`/`drain`/`rotate_*` on
    // such a `VecDeque`) built rc=0 and panicked. The integer rotate keeps its
    // marker: `core::num::<impl u32>::rotate_left` has spine
    // `core::num::::rotate_left`, which still carries `::num::`. The POSITIVE test
    // below still reads the whole callee — an over-match there only adds a row.
    if callee.contains("slice")
        || callee.contains("vec::Vec")
        || callee.contains("Vec::")
        || callee.contains("[T]")
        || callee.contains("collections::")
    {
        let spine = callee_without_turbofish_args(callee);
        let is_integer_method =
            spine.contains("::num::") || spine.contains("<impl u") || spine.contains("<impl i");
        if !is_integer_method {
            return true;
        }
    }
    // (a) A modeled slice length on the receiver (arg 0) proves a slice receiver.
    args.first().is_some_and(|recv| {
        param_slice_len(func, recv, 8).is_some() || crate::slice_len_formula(func, recv).is_some()
    })
}

/// An inherent method of the std `Vec`, `VecDeque` or `String`, by an anchored path
/// with no qualified (`as`) spelling and no unauthenticated crate stamp.
fn callee_is_std_growable_container_method(callee: &str) -> bool {
    if callee.contains(" as ") || trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return false;
    }
    let owner = super::iterator_yield::vc_strip_generics_cow(callee);
    let owner = owner.rsplit_once("::").map_or("", |(owner, _)| owner);
    matches!(
        owner,
        "alloc::vec::Vec"
            | "std::vec::Vec"
            | "alloc::collections::vec_deque::VecDeque"
            | "std::collections::VecDeque"
            | "std::collections::vec_deque::VecDeque"
            | "alloc::string::String"
            | "std::string::String"
    )
}

/// `drain`'s range argument covers the whole receiver: a `RangeFull` (`..`), or a
/// `RangeFrom` whose one value starts at the constant `0` (`0..`).
///
/// A `RangeFull` is a field-less unit struct, which the extractor lowers to the bare
/// `Constant(Unit)` with no type, so it is read from the std `drain`'s own generic
/// argument — the instance's `R`, which rustc fixes from the argument's type — and the
/// operand must be that unit constant.
fn drain_range_is_whole(func: &VerifiableFunction, callee: &str, range: &Operand) -> bool {
    if callee.ends_with("::drain::<core::ops::range::RangeFull>")
        && matches!(range, Operand::Constant(ConstValue::Unit))
    {
        return true;
    }
    let Some(ty) = crate::operand_ty_cow(func, range) else {
        return false;
    };
    let Ty::Adt { name, .. } = ty.as_ref() else {
        return false;
    };
    if !name.starts_with("core::ops::range::") {
        return false;
    }
    let head = name.split('<').next().unwrap_or(name);
    match head {
        "core::ops::range::RangeFull" => true,
        "core::ops::range::RangeFrom" => {
            let (Operand::Copy(p) | Operand::Move(p)) = range else { return false };
            p.projections.is_empty()
                && !crate::local_defs::is_parameter(func, p.local)
                && matches!(
                    crate::local_defs::unique_value_def(func, p.local),
                    Some(Rvalue::Aggregate(_, ops))
                        if matches!(ops.as_slice(), [Operand::Constant(ConstValue::Uint(0, _))])
                )
        }
        _ => false,
    }
}

/// Trust (2026-09-19): `char::encode_utf8` / `char::encode_utf8_raw` PANIC when
/// the destination buffer is shorter than the encoding
/// (`library/core/src/char/methods.rs:2482`, "need {len} bytes to encode
/// U+{code:04X} but buffer has just {dst_len}"). That is a Rust SAFETY
/// obligation about the CALLER's own buffer, exactly like an out-of-range index
/// — not std's own defined behaviour reacting to the environment — so it belongs
/// in the same `panic-freedom-unverified` family as the container mutators and
/// NOT in the vanilla-sysroot tolerance.
///
/// WHY IT IS NEEDED NOW. Before the absent-callee ledger covered callees reached
/// through a bundled member, `encode_utf8_raw` was refused only because it was
/// NOT IN THE LEDGER — an accident, measured:
///
/// ```text
/// [VANILLA_ROW] tolerated=false NOT-IN-LEDGER callee=`core::char::methods::encode_utf8_raw`
/// ```
///
/// With the ledger widened that accident disappears and the call would become a
/// policy-B conditional pass. This recogniser replaces the accident with the
/// reason, so `c.encode_utf8(&mut [0u8; 1])` stays a build error rather than
/// becoming a warning.
///
/// EXACT-METHOD gated, like its siblings: only these two names, and only in
/// `core`'s own `char` module, so a user method called `encode_utf8` is not
/// matched.
///
/// Trust (merge 2026-10-14): NOT the UTF-16 twins. Local main's review round 90
/// (`067e015c50c`) added `encode_utf16`/`encode_utf16_raw` here; `origin/main`'s
/// UTF8-ENCODE-UTF16-SHORTBUF-1 (`a40dc084865`) closed the same hole with
/// [`is_buffer_panicking_char_utf16_encoder`], asked of ROOT call sites only, and
/// recorded adding them here as REJECTED (docs/DECISION_QUEUE.md): the bundle walk
/// asks this predicate too (through [`super::callee_is_known_caller_value_panic`]),
/// and core's `EncodeUtf16::next` and `wtf8` call them with a two-unit buffer of
/// their own, so the total `s.encode_utf16().count()` would be refused. Every root
/// call stays refused twice (the row `unsupported.rs` mints and the compiler's
/// root-call tolerance).
pub fn is_buffer_panicking_char_encoder(callee: &str) -> bool {
    matches!(method_tail(callee), "encode_utf8" | "encode_utf8_raw")
        && callee.contains("char")
        && (callee.starts_with("core::") || callee.starts_with("<core::"))
}

/// Trust (UTF8-ENCODE-UTF16-SHORTBUF-1, 2026-10-05): `char::encode_utf16` and
/// `core::char::methods::encode_utf16_raw`, the UTF-16 twins of the encoders above.
/// They PANIC when the destination is shorter than the character's UTF-16 length
/// (`library/core/src/char/methods.rs`, `encode_utf16_raw`: "encode_utf16: need
/// {len} bytes to encode U+{code:04X} but buffer has just {dst_len}"): one unit for
/// a BMP character, two for a supplementary-plane one. The buffer is the caller's
/// own, so this is the same family and the same row as `encode_utf8`.
///
/// THE DEFECT, measured on the stage 1 of `dc15b882f6` (main plus wave 16):
/// `pub fn f(c: char, buf: &mut [u16]) { c.encode_utf16(buf); }` built rc=0 under
/// the default policy at `-O0` and `-O3`, its only row a runtime-checked
/// panic-freedom row citing the bundled `encode_utf16_raw`, and a verify-off driver
/// calling `f('\u{1F600}', &mut [0u16; 1])` panicked. The `encode_utf8` twin is
/// refused by the row below. Nothing named this method, so the compiler's
/// vanilla-sysroot tolerance admitted the call as std's own defined behaviour.
///
/// WHY A SEPARATE RECOGNIZER, NOT A WIDER [`is_buffer_panicking_char_encoder`].
/// The bundle walk asks that one (through
/// [`super::callee_is_known_caller_value_panic`]) of std-internal call sites too,
/// and core calls `encode_utf16` with its OWN two-unit buffer:
/// `EncodeUtf16::next` (`library/core/src/str/iter.rs`, `ch.encode_utf16(&mut buf)`
/// with `buf = [0; 2]`) and `wtf8`'s `encode_utf16_raw(.., &mut buf)`. Asked
/// there, it would refuse the TOTAL `s.encode_utf16().count()` and `.collect()`,
/// the `VecDeque::swap_remove_back` lesson
/// ([`super::callee_is_root_call_caller_value_panic`]). This recognizer is asked of
/// ROOT call sites only: by `unsupported.rs` on the caller's own MIR, and by the
/// compiler's root-call tolerance through
/// [`super::callee_is_root_call_caller_value_panic`].
///
/// EXACT-PATH gated: core's two definitional spellings (the extractor prints
/// definitional paths), optionally followed by a turbofish. A user
/// `encode_utf16`, the total `core::str::<impl str>::encode_utf16` iterator
/// constructor, `len_utf16`, and a stamped impersonator crate named `core` are not
/// matched.
pub fn is_buffer_panicking_char_utf16_encoder(callee: &str) -> bool {
    const CORE_CHAR_UTF16_ENCODERS: [&str; 2] =
        ["core::char::methods::<impl char>::encode_utf16", "core::char::methods::encode_utf16_raw"];
    let callee = callee.trim();
    CORE_CHAR_UTF16_ENCODERS.iter().any(|path| {
        callee.strip_prefix(path).is_some_and(|rest| {
            // Anything after the path must be trailing turbofish groups only, so
            // the method tail of the whole spelling is still the encoder's.
            rest.is_empty() || (rest.starts_with("::<") && method_tail(callee) == method_tail(path))
        })
    })
}

/// Trust (W4 fix round 1, 2026-09-25): the std `VecDeque` members that PANIC on a
/// CALLER-SUPPLIED index, count or range — the same family as the `Vec`/`String`
/// mutators below, which [`is_index_panicking_container_mutator`] deliberately
/// never matches (it excludes `collections::` wholesale, to keep the TOTAL
/// `VecDeque::remove` and the map/set methods out) — AND that no call-site lane
/// charges.
///
/// THE DEFECT THIS CLOSES, measured on stage 1 `0.10.0+gc2e3daed7`:
/// `pub fn f(d: &mut VecDeque<u32>, i: usize) { d.insert(i, 0); }` built rc=0 with
/// one runtime-checked row and panics "index out of bounds" at `f(&mut [1], 5)`:
/// the callee is a sysroot routine at foundational types, so the vanilla-sysroot
/// tolerance admitted it as "std's own defined behaviour", which a panic on the
/// caller's own index is not. `split_off`, `rotate_left`/`rotate_right` and
/// `drain` were already refused, by `is_bounds_panicking_slice_mutator`'s
/// `collections::` fallback; they are listed here too so the COMPILER's
/// root-call-site tolerance (`callee_is_root_call_caller_value_panic`) withholds
/// the tolerance for them as well. That consumer asks this of the ROOT body's own
/// call sites only, never the bundle walk — see its doc for the measured
/// over-refusal the bundle walk caused.
///
/// RECONCILED with `origin/main` 92e7829ca5 (2026-09-28, W4 salvage). Main's
/// `collection_range` charges `swap`, `range`, `range_mut`, `insert_mut` and the
/// `Index`/`IndexMut` scalar index AT THE CALL SITE (`slice_method_panic` ->
/// `collection_method_panic` / `deque_scalar_index_body`): PRECISELY over a stable
/// deque length (`deque_receiver_len`), so the GUARDED forms prove, and fail-honest
/// otherwise. Round 1 had them here too, which withheld the tolerance by NAME at
/// every root call and minted an undischargeable row, refusing exactly the guarded
/// programs main proves (`tests/ui/trust/policy_b/std_index_range_panics_charged.rs`).
/// They are therefore NOT in this list: the charge row is their refusal, and a
/// guard discharges it. [`is_deque_scalar_index_call`] keeps the `Index` spelling for
/// the one fail-closed backstop vcgen still mints (a deque index main's lane cannot
/// read — see `unsupported.rs`). What stays here is what main neither charges nor
/// models: `insert` (no call-site row on main; its KNOWN_HAZARDS table left it to this
/// branch) and the members whose refusal was already the slice-mutator row.
///
/// AUDITED against `library/alloc/src/collections/vec_deque/mod.rs` in this tree,
/// every `pub fn` with a `# Panics` section that is not a capacity overflow (the
/// growth class `push_back` shares, recorded in docs/TCB.md and deliberately
/// untouched): `swap` (either index `>= len`), `range`/`range_mut`/`drain`/`splice`/
/// `extract_if`/`extend_from_within`/`prepend_from_within` (a bad range),
/// `insert`/`insert_mut` (`index > len`), `split_off` (`at > len`),
/// `rotate_left`/`rotate_right` (`n > len`), plus the undocumented
/// `Index::index`/`IndexMut::index_mut` (`self.get(index).expect("Out of bounds
/// access")`). TOTAL and deliberately NOT matched: `remove`,
/// `swap_remove_back`/`swap_remove_front`, `get`/`get_mut` (`Option`), `truncate`.
/// Charged by main's `collection_range` and so NOT matched whenever its recognizer
/// names the call: `swap`, `range`, `range_mut`, `insert_mut` (and `Index`/`IndexMut`,
/// by receiver type — see [`is_deque_scalar_index_call`]).
/// `vecdeque_members_main_charges_are_left_to_its_rows` pins that each of them IS
/// recognized there, fn-item element types included;
/// `a_deque_member_main_declines_keeps_the_carve_out` pins the fall-back.
///
/// EXACT-PATH gated: the receiver path, turbofish groups stripped, must be std's
/// own `collections::vec_deque::VecDeque`; a ` as `-qualified spelling (a user
/// trait that happens to have an `insert` method implemented for `VecDeque`) is
/// not matched.
pub fn is_caller_value_panicking_deque_method(callee: &str) -> bool {
    let tail = method_tail(callee);
    if callee.starts_with('<') {
        return false;
    }
    if !matches!(
        tail,
        "drain"
            | "splice"
            | "extract_if"
            | "extend_from_within"
            | "prepend_from_within"
            | "insert"
            | "split_off"
            | "rotate_left"
            | "rotate_right"
            | "swap"
            | "range"
            | "range_mut"
            | "insert_mut"
    ) {
        return false;
    }
    // The members main's `collection_range` charges leave this list EXACTLY when its
    // recognizer names the call. Its identity test is stricter than this one (an
    // authenticated sysroot root and no unauthenticated-crate stamp ANYWHERE in the
    // rendered name), so a spelling it declines — e.g. an element type that is a
    // stamped impersonator crate's tuple-struct constructor, which the compiler still
    // counts as foundational — gets no charge row and falls to the slice `swap` arm,
    // which emits nothing for a deque. Such a call keeps this carve-out's refusal.
    if matches!(tail, "swap" | "range" | "range_mut" | "insert_mut")
        && super::collection_range::collection_method_panic(callee).is_some()
    {
        return false;
    }
    // `callee_without_turbofish_args` removes each `<..>` group but keeps the `::`
    // around it (`VecDeque::<u32>::insert::<__trust_args@..>` becomes
    // `VecDeque::::insert::`), so the method segment is what remains after the
    // receiver path with the colons trimmed — and it must be the WHOLE remainder.
    let spine = callee_without_turbofish_args(callee);
    STD_VECDEQUE_PATHS.iter().any(|path| {
        spine
            .strip_prefix(path)
            .is_some_and(|rest| rest.starts_with("::") && rest.trim_matches(':') == tail)
    })
}

/// std's own `VecDeque`, as a callee's receiver path spells it.
const STD_VECDEQUE_PATHS: [&str; 2] =
    ["alloc::collections::vec_deque::VecDeque", "std::collections::vec_deque::VecDeque"];

/// Trust (W4 salvage, 2026-09-28): `<VecDeque<T> as Index<usize>>::index` /
/// `IndexMut<usize>>::index_mut` — the scalar deque index, which panics ("Out of
/// bounds access") at `i >= len`. Main's `collection_range::deque_scalar_index_body`
/// charges it at the call site; this spelling test lets `unsupported.rs` keep a
/// fail-closed row for the one case that lane cannot read (it answers `None` when
/// the receiver or the index operand carries no readable type), so moving the index
/// out of [`is_caller_value_panicking_deque_method`] opens no silent path.
///
/// The split is at the first ` as ` at DEPTH 0 inside the qualification: the element
/// type can carry its own (`fn(u32) -> <u32 as Not>::Output {<u32 as Not>::not}`).
pub(super) fn is_deque_scalar_index_call(callee: &str) -> bool {
    if !callee.starts_with('<') {
        return false;
    }
    let tail = method_tail(callee);
    if !matches!(tail, "index" | "index_mut") {
        return false;
    }
    let Some((self_ty, rest)) = split_qualified_callee_at_top_level_as(callee) else {
        return false;
    };
    let self_path = self_ty.split('<').next().unwrap_or(self_ty);
    let index_trait = matches!(
        (tail, rest.split('<').next()),
        ("index", Some("core::ops::index::Index" | "core::ops::Index"))
            | ("index_mut", Some("core::ops::index::IndexMut" | "core::ops::IndexMut"))
    );
    index_trait
        && STD_VECDEQUE_PATHS.contains(&self_path)
        && rest.split_once('>').is_some_and(|(arg, _)| arg.ends_with("<usize"))
}

/// The trait half of std's scalar `Index<usize>::index`, as a qualified callee
/// spells it after its top-level ` as `. The extractor renders the trait by its
/// defining path (`core::ops::index::Index`, measured on stage1-w10 for `[u32]`,
/// `[u32; 4]` and `alloc::vec::Vec<u32>` receivers); the two re-export spellings
/// are accepted because they name the same trait.
const STD_SCALAR_INDEX_TRAIT_METHOD: [&str; 3] = [
    "core::ops::index::Index<usize>>::index",
    "core::ops::Index<usize>>::index",
    "std::ops::Index<usize>>::index",
];

/// std's own `Vec`, as a callee's qualified self type or a `Ty::Adt` name spells it.
use trust_types::interior_mutability::STD_VEC_PATHS;
/// Trust (IDX-TIE-1, 2026-10-03): is the `Ty::Adt` name `name` std's own `Vec`, by
/// its exact path? `is_owned_slice_container_name` tests only the LAST segment, so
/// a user type named `Vec` passes it. The producer stamps a type name whose crate
/// impersonates `alloc`/`std` (`impersonates_sysroot_crate`), so an exact
/// `alloc::vec::Vec`/`std::vec::Vec` path is std's.
///
/// `pub(crate)` since DEREF-ANCHOR-1 (2026-10-04): `guards::std_container_deref_self`
/// (the callee's self type) and `guards::deref_receiver_is_std_container` (the receiver's
/// MIR type) ask it too, so the deref length hop and the index ties agree on "std's `Vec`".
pub(crate) use trust_types::interior_mutability::is_std_vec_adt_name;

/// Trust (IDX-TIE-1, 2026-10-03): is `callee` std's OWN scalar
/// `<S as Index<usize>>::index` on a slice `[T]`, an array `[T; N]` or a `Vec<T>`?
///
/// A fact that reads `index`'s RESULT — "equal indices into one unchanged container
/// read the same element", or "the element read is one of the rows pushed" — is a
/// theorem about std's impls and about nothing else. Matching the method NAME
/// (`method_tail == "index"`) handed it to every user method called `index`: a user
/// trait on `[u32]` (`<[u32] as x::Lo>::index`), or a user `impl Index<Key> for
/// [u32]` with a local key type (`<[u32] as core::ops::index::Index<x::A>>::index`).
/// Both were measured accepted under certify with an overflow check removed.
///
/// Why each condition names std's impl:
///  * the trait-and-method half must EQUAL one of
///    [`STD_SCALAR_INDEX_TRAIT_METHOD`]. Equality, not a prefix, so the split point
///    is the LAST qualification of the string and the method has no suffix. The
///    trait argument is exactly `usize`: an `ends_with("<usize")` test (the deque
///    helper's) also admits a user key such as `Index<x::K<usize>>`.
///  * the self type starts with `[` (a slice or an array, both primitive), or its
///    path is std's `Vec`. The orphan rule forbids a downstream
///    `impl Index<usize>` on `[T]`, `[T; N]` or `Vec<T>` (none of them is local, and
///    `usize` is not local), so with the trait argument fixed to `usize` the impl
///    can only be core's or alloc's.
///  * the callee opens with `<`. The producer prefixes a callee whose defining
///    crate impersonates a sysroot name with `__trust_crate@…::`, so a forged
///    `core` never reaches this test.
///
/// Fail closed: every other spelling answers false, and the caller emits no fact.
pub(super) fn is_std_scalar_index_call(callee: &str) -> bool {
    if !callee.starts_with('<') || method_tail(callee) != "index" {
        return false;
    }
    let Some((self_ty, rest)) = split_qualified_callee_at_top_level_as(callee) else {
        return false;
    };
    if !STD_SCALAR_INDEX_TRAIT_METHOD.contains(&rest) {
        return false;
    }
    if self_ty.starts_with('[') {
        return true;
    }
    STD_VEC_PATHS
        .iter()
        .any(|path| self_ty.strip_prefix(path).is_some_and(|args| args.starts_with('<')))
}

/// The trait paths of std's `Index` and `IndexMut`, as the qualified half of a callee
/// spells them after its top-level ` as ` (the extractor renders the defining path,
/// `core::ops::index::…`; the two re-export spellings name the same traits).
const STD_INDEX_TRAITS: [&str; 3] =
    ["core::ops::index::Index", "core::ops::Index", "std::ops::Index"];
const STD_INDEX_MUT_TRAITS: [&str; 3] =
    ["core::ops::index::IndexMut", "core::ops::IndexMut", "std::ops::IndexMut"];

/// std's range index types, as the extractor renders the trait argument of an
/// `Index`/`IndexMut` call (measured on stage1-w11fix, 2026-10-04: `v[0..2]`,
/// `v[1..]`, `v[..2]`, `v[..]`, `v[0..=1]`, `v[..=1]` on a `Vec<u32>`, and the same
/// family on `[u32]`, `[u32; 4]` and `String`).
const STD_RANGE_INDEX_ARGS: [&str; 6] = [
    "core::ops::range::Range<usize>",
    "core::ops::range::RangeFrom<usize>",
    "core::ops::range::RangeTo<usize>",
    "core::ops::range::RangeFull",
    "core::ops::range::RangeInclusive<usize>",
    "core::ops::range::RangeToInclusive<usize>",
];

/// Trust (STD-RECEIVER-ANCHOR-1, 2026-10-04): is `callee` std's OWN `Index::index`
/// or `IndexMut::index_mut` on a std container — the call that hands out a
/// reference INTO the container and never changes its length?
///
/// `guards::local_mut_borrows_may_resize` counts a `&mut v` consumed by such a call
/// as length-benign, so the `.len()` tie and the index-bound recovery survive the
/// `v[i] = x` write idiom. That is a theorem about std's impls only. It was decided
/// on the TRAIT path (`callee_is_std_ops_method`), which a downstream impl of std's
/// trait on std's `Vec` also carries: `impl<T> IndexMut<K<T>> for Vec<u32>` (a
/// generic local impl the producer does not rename to its impl path) or a
/// dependency's `impl IndexMut<dep::K> for Vec<u32>` renders
/// `<alloc::vec::Vec<u32> as core::ops::index::IndexMut<dep::K>>::index_mut`. If
/// that body truncates the `Vec`, two `v.len()` around `v[K] = 1` were still tied to
/// one length: `if v.len() == 0 { return 0; } v[K] = 1; v.len() - 1` read
/// `overflow:sub proved` (Certified) under every policy, the check was removed, and
/// the advisory build returned `usize::MAX` for `vec![7]` where vanilla Rust panics.
///
/// Why each condition names std's impl:
///  * the trait-and-method half must EQUAL `{trait}<{arg}>>::{method}` with the
///    trait one of std's `Index`/`IndexMut` paths matching the method, and `arg`
///    EXACTLY `usize` or one of [`STD_RANGE_INDEX_ARGS`] — never a prefix or a
///    suffix test, so `Index<x::K<usize>>` and `Index<Range<x::K>>` answer false.
///  * the self type is a primitive slice or array (`[`), std's `Vec<…>`, std's
///    `String` (range arguments only: `String` is not `Index<usize>`) or std's
///    `VecDeque<…>` (`usize` only: its one `Index` impl). The orphan rule forbids a
///    downstream `impl Index<A> for S` when neither `S` nor `A` is local, and none of
///    these `S`/`A` is local to any crate but `core`/`alloc` (a slice, an array, a
///    `Vec`, a `String` or a `VecDeque` of a user element type is still not local),
///    so the impl that runs is std's.
///  * the callee opens with `<`: a callee whose defining crate impersonates a
///    sysroot name is stamped `__trust_crate@…::` by the producer.
///
/// Fail closed: every other spelling answers false, which the caller reads as "may
/// resize" and declines the tie.
pub(crate) fn is_std_container_index_call(callee: &str) -> bool {
    if !callee.starts_with('<') {
        return false;
    }
    let method = method_tail(callee);
    let traits: &[&str] = match method {
        "index" => &STD_INDEX_TRAITS,
        "index_mut" => &STD_INDEX_MUT_TRAITS,
        _ => return false,
    };
    let Some((self_ty, rest)) = split_qualified_callee_at_top_level_as(callee) else {
        return false;
    };
    // `rest` is `{trait}<{arg}>>::{method}`; the trait paths carry no `<`, so the
    // first `<` separates the trait from its argument.
    let Some(trait_and_arg) = rest.strip_suffix(method).and_then(|r| r.strip_suffix(">>::")) else {
        return false;
    };
    let Some((trait_path, arg)) = trait_and_arg.split_once('<') else { return false };
    if !traits.contains(&trait_path) {
        return false;
    }
    let scalar = arg == "usize";
    let range = STD_RANGE_INDEX_ARGS.contains(&arg);
    let generic_std = |paths: &[&str]| {
        paths
            .iter()
            .any(|path| self_ty.strip_prefix(path).is_some_and(|args| args.starts_with('<')))
    };
    if self_ty.starts_with('[') || generic_std(&STD_VEC_PATHS) {
        scalar || range
    } else if super::collection_range::STRING_OWNERS.contains(&self_ty) {
        range
    } else if generic_std(&STD_VECDEQUE_PATHS) {
        scalar
    } else {
        false
    }
}

/// Trust (falsification gate, `absent_callee_call_only_mono`): a call to a std
/// container method that PANICS on an out-of-range index and whose body is not
/// modeled — `Vec::{remove, insert, swap_remove}` (panic: `index >= len`, resp.
/// `index > len` for `insert`) and `String::{remove, insert, insert_str}`
/// (panic: out of bounds or not a char boundary). Surfaced as the same
/// `panic-freedom-unverified` UnsupportedMir row as the slice-mutator lane, which
/// STRICT policy counts as `failed` — the honest verdict for an unguarded call
/// whose panic set is known and input-reachable.
///
/// EXACT-PATH gated, deliberately STRICTER than
/// `is_bounds_panicking_slice_mutator`'s path fallback (which accepts
/// `collections::`): `HashMap`/`BTreeMap`/`HashSet::remove`/`insert` and
/// `VecDeque::remove` are TOTAL (they return `Option`/`bool`) and render under
/// `collections::` — matching them here would reject valid programs under
/// strict policy (this lane's rows count as FAILED, not Unknown, so an
/// over-match is not merely conservative). Only the real `alloc::vec::Vec` /
/// `alloc::string::String` paths qualify, and `collections::` is excluded
/// outright.
pub fn is_index_panicking_container_mutator(callee: &str) -> bool {
    if !matches!(method_tail(callee), "remove" | "insert" | "swap_remove" | "insert_str") {
        return false;
    }
    // SOUNDNESS/precision (R20 Front A, measured on ny-cert gate R19): the
    // receiver test must read the RECEIVER path, never a TURBOFISH generic
    // ARGUMENT. `serde_json::Map::<std::string::String, serde_json::Value>::insert`
    // is a TOTAL map insert (it returns `Option<Value>`; it has no index
    // argument and no char-boundary), yet it carries the substring
    // `string::String` inside its FIRST GENERIC ARGUMENT — so the raw
    // `contains` matched it and stamped a fail-closed
    // `Call::insert::panic-freedom-unverified` row that STRICT policy counts as
    // FAILED. That single mis-recognition was 41 of ny-cert's 92 unknown
    // obligations across 8 JSON-serializer functions: a rejection of valid code,
    // exactly the over-match this lane's `collections::` exclusion already
    // warns about.
    //
    // Stripping turbofish groups CANNOT lose a true positive: a turbofish holds
    // generic ARGUMENTS, and the receiver type's own path head always PRECEDES
    // it (`std::vec::Vec::<T, A>::insert` -> `std::vec::Vec::insert`,
    // `std::string::String::insert` unchanged). A qualified-path spelling
    // (`<std::vec::Vec<u8> as Ext>::insert`) opens its `<` after a path segment
    // rather than after `::`, so it is left intact and still matches.
    let spine = callee_without_turbofish_args(callee);
    // Total map/set/deque methods live under `collections::` — never match.
    if spine.contains("collections::") {
        return false;
    }
    spine.contains("vec::Vec") || spine.contains("string::String")
}

/// The callee path with every TURBOFISH generic-argument group (`::<…>`, which
/// includes the trailing `::<__trust_args@HASH>` monomorph tag) removed, so a
/// receiver-path test cannot be satisfied by text that only appears in a
/// generic ARGUMENT. Balanced-aware, so nested groups
/// (`::<Vec<Option<u8>>, u32>`) are removed whole; an UNBALANCED `<` is left
/// as-is (fail-closed: the recognizer then sees the original text and keeps
/// its fail-closed row rather than silently dropping one).
///
/// Deliberately does NOT touch a `<…>` that is not introduced by `::` — that
/// is a QUALIFIED PATH (`<Recv as Trait>::m`) whose receiver lives inside the
/// brackets, and removing it would blind every receiver test to it.
pub(super) fn callee_without_turbofish_args(callee: &str) -> std::borrow::Cow<'_, str> {
    if !callee.contains("::<") {
        return std::borrow::Cow::Borrowed(callee);
    }
    let bytes = callee.as_bytes();
    let mut out = String::with_capacity(callee.len());
    let mut copy_from = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        // A turbofish opens at `::<`.
        if bytes[i] == b'<' && i >= 2 && bytes[i - 1] == b':' && bytes[i - 2] == b':' {
            let mut depth = 0i32;
            let mut j = i;
            let mut closed = None;
            while j < bytes.len() {
                // Trust (W4 fix round 2, 2026-09-26): the `>` of a fn-signature
                // ARROW is not a bracket. A fn-item or fn-pointer element type
                // carries one (`VecDeque::<fn(u32) -> u32 {…count_ones}>::insert`);
                // counting it closed the group at the arrow, the spine came back as
                // `VecDeque:: u32 {…}>::insert`, and every receiver test on it
                // missed — the deque caller-value carve-out (vcgen row AND the
                // compiler's root-call carve-out) and the `collections::` exclusion
                // of `is_index_panicking_container_mutator` alike. Measured on
                // `0.10.0+g6a3460983`: an unguarded `insert`/`swap`/`range`/
                // `range_mut`/`rotate_right`/`split_off`/`drain` on a `VecDeque` of
                // sysroot fn items built rc=0 and panicked. `alloc_bounds::method_tail`
                // has always carried the same rule.
                if is_arrow_gt(bytes, j) {
                    j += 1;
                    continue;
                }
                match bytes[j] {
                    b'<' => depth += 1,
                    b'>' => {
                        depth -= 1;
                        if depth == 0 {
                            closed = Some(j);
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            match closed {
                // Skip the whole balanced group; `i` and `end + 1` are ASCII boundaries.
                Some(end) => {
                    out.push_str(&callee[copy_from..i]);
                    i = end + 1;
                    copy_from = i;
                    continue;
                }
                // Unbalanced: keep the remainder verbatim (fail-closed).
                None => {
                    out.push_str(&callee[copy_from..]);
                    return std::borrow::Cow::Owned(out);
                }
            }
        }
        i += 1;
    }
    if copy_from < bytes.len() {
        out.push_str(&callee[copy_from..]);
    }
    std::borrow::Cow::Owned(out)
}

/// Is `bytes[j]` the `>` of a fn-signature arrow (`->`) rather than a closing
/// angle bracket?
fn is_arrow_gt(bytes: &[u8], j: usize) -> bool {
    bytes[j] == b'>' && j > 0 && bytes[j - 1] == b'-'
}

/// Split a qualified-path callee (`<SELF as TRAIT>::item`) into `SELF` and
/// `TRAIT>::item` at the first ` as ` found at angle-bracket DEPTH 1 — depth 0 once
/// the opening `<` is stripped — counting depth with the same arrow rule as
/// [`callee_without_turbofish_args`]. `None` for a callee that does not open with
/// `<`, has no such ` as `, or whose brackets close below that depth.
///
/// Trust (W4 fix round 2, 2026-09-26): the SELF type can itself carry ` as `. A
/// `VecDeque` whose element is a trait-method fn item renders its `Index` call as
/// `<VecDeque<fn(u32) -> <u32 as core::ops::bit::Not>::Output {<u32 as
/// core::ops::bit::Not>::not}> as core::ops::index::Index<usize>>::index`; a plain
/// `split_once(" as ")` split inside the element type, the recognizer read the
/// self type as `…VecDeque<fn(u32) -> <u32` and the trait as `core::ops::bit::Not`,
/// and an unguarded `d[i]` / `d[i] = x` built rc=0 and panicked (measured on
/// `0.10.0+g6a3460983`).
///
/// `pub(crate)` since DEREF-ANCHOR-1 (2026-10-04): `guards::std_container_deref_self`
/// splits std's `Deref::deref` with it. A fn-item type argument can carry its own
/// ` as core::ops::deref::Deref>::deref` (measured), so a `contains` test is forgeable.
pub(crate) fn split_qualified_callee_at_top_level_as(callee: &str) -> Option<(&str, &str)> {
    let qualified = callee.strip_prefix('<')?;
    let bytes = qualified.as_bytes();
    let mut depth = 0i32;
    for (j, &byte) in bytes.iter().enumerate() {
        match byte {
            b'>' if is_arrow_gt(bytes, j) => {}
            b'<' => depth += 1,
            b'>' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            // `b' '` is ASCII, so `j` is a char boundary.
            b' ' if depth == 0 && qualified[j..].starts_with(" as ") => {
                return Some((&qualified[..j], &qualified[j + 4..]));
            }
            _ => {}
        }
    }
    None
}

/// Trust (hunt-15 Class D): a call to a std method that PANICS on its failure
/// variant — `Option`/`Result` `unwrap`/`expect`/`unwrap_err`/`expect_err`. These
/// have a normal-return target (the success value) but an unmodeled internal panic
/// path, so the canonical pipeline surfaces them as Unknown to keep the headline from
/// over-crediting. `unwrap_unchecked`/`unwrap_or*` are EXCLUDED: the former is UB
/// (a different obligation class), the latter are total (no panic). The
/// `Option`/`Result` path guard avoids an unrelated user `unwrap`/`expect`; an
/// over-match would only be over-conservative (Unknown), never unsound.
pub(super) fn is_known_panicking_method(callee: &str) -> bool {
    matches!(method_tail(callee), "unwrap" | "expect" | "unwrap_err" | "expect_err")
        && (callee.contains("Option") || callee.contains("Result"))
}

/// Trust (signed `iN::abs` panic-freedom, 2026-07-06): the std inherent
/// `i8/i16/i32/i64/i128/isize::abs` PANICS (debug) / wraps (release) when its
/// receiver is `iN::MIN` — the exact same overflow as `-x` (there is no positive
/// representation of `MIN`). `-x` is caught by `v2_build_negation_raw_vc`, but
/// `x.abs()` lowers to an OPAQUE `Call` to `core::num::<impl iN>::abs`, so without
/// this recognizer the panic path is unmodeled and a genuinely-unsafe `x.abs()`
/// compiles clean — a hole in panic-freedom and an inconsistency with the caught
/// `-x`. Anchored to the std `core::num`/`std::num` inherent-impl path and the exact
/// `abs` method tail, so `wrapping_abs`/`unsigned_abs`/`checked_abs`/
/// `overflowing_abs` (which do NOT panic) and any user `.abs()` are excluded; the
/// body additionally gates on a SIGNED-INT receiver, so a float `abs` (total) is
/// never matched.
///
/// Trust (2026-10-06, ABS-NAME-1): the "anchor" above was not one. It was
/// `method_tail == "abs"` plus a SUBSTRING test for `core::num::` / `std::num::`
/// anywhere in the rendered path, so a user `mycore::num::abs`, and a user
/// `G::<core::num::Wrapping<i32>>::abs` whose generic argument merely mentions
/// core's module, minted `NegationOverflow { x == iN::MIN }` over the user
/// function's argument. Measured on the stage 1 of `9e11546767`: `fn abs(x: i32)
/// -> i32 { x ^ 1 }` called that way was refuted at `x = -2147483648` and reported
/// as a "guaranteed Level 0 safety violation" of a function that cannot panic, and
/// `memory-safe` added the false note that rustc inserts a runtime check. It now
/// takes exactly `numeric_panic::int_inherent`'s authenticated
/// `core::num::<impl iN>::abs` (or `std::num::`), with a SIGNED primitive owner — the
/// identity `pow` and `strict_pow` already use. `pub` because it is also trust-clean's
/// negation-subject recognizer (re-exported at the crate root), so the consumer can
/// no longer drift from the emitter. `callee_has_call_site_panic_family` keeps the old
/// view ([`is_signed_abs_call_name_only`]).
///
/// Trust (wave-19 review, 2026-10-09): the EMITTER now asks [`is_signed_abs_mint`],
/// which also reads core's spelling behind one leading extractor stamp (a graph that
/// stamps the genuine core). This predicate stays authenticated: it is what trust-clean
/// admits, so the admitted subjects are a SUBSET of the charged ones (equal on every
/// unstamped spelling), and a row minted for a stamped spelling is never clean-certified.
pub fn is_signed_abs_call(callee: &str) -> bool {
    matches!(numeric_panic::int_inherent(callee), Some((_, true, "abs")))
}

/// The MINTING view of [`is_signed_abs_call`]: also core's signed `abs` behind one
/// leading extractor identity stamp (`numeric_panic::int_inherent_minting`).
///
/// Trust (wave-19 review, 2026-10-09): the extractor stamps the GENUINE core when the
/// graph holds a second crate named `core`, or under `-Zbuild-std`, and
/// [`is_signed_abs_call`] refuses every stamp. MEASURED (the stage 1 of `46e9afaf95`):
/// beside a verify-off `--crate-name core` dependency, `x.abs()` lost its `negation`
/// row (refuted at `x = i32::MIN` on the stage 1 of `f39efe05ca`), the default build
/// exited 0 on a `runtime_checked` row, and the binary panicked "attempt to negate
/// with overflow". The row only ADDS an obligation, and only a crate using rustc's
/// internal coherence attributes can define `<impl i32>::abs`, so reading the stamped
/// spelling here can at worst charge a forgery a row it does not owe. trust-clean's
/// negation-subject admission keeps [`is_signed_abs_call`]: the subjects it admits stay
/// a subset of the ones charged, and a row minted for a stamped spelling is never
/// clean-certified.
pub(super) fn is_signed_abs_mint(callee: &str) -> bool {
    matches!(numeric_panic::int_inherent_minting(callee), Some((_, true, "abs")))
}

/// The pre-ABS-NAME-1 view of [`is_signed_abs_call`]: the `abs` method tail plus a
/// `core::num::` / `std::num::` SUBSTRING, with no anchor and no owner check.
///
/// Trust (2026-10-06, ABS-NAME-1): only `callee_has_call_site_panic_family` reads
/// this. There a `true` only WITHHOLDS the vanilla admission of a real-sysroot fn
/// item the compiler has already authenticated, so keeping the wider match leaves
/// that gate's answer byte-identical: `Wrapping::<iN>::abs`, `Saturating::<iN>::abs`
/// and `NonZero::<iN>::abs` handed over as items stay withheld as before rather than
/// becoming newly admitted by a change nobody measured. It must never mint a row —
/// the same split as `alloc_bounds::overflow_arith_call_name_only`.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn is_signed_abs_call_name_only(callee: &str) -> bool {
    method_tail(callee) == "abs"
        && (callee.contains("core::num::") || callee.contains("std::num::"))
}

/// What the `abs` arm mints for one signed `iN::abs` call ([`signed_abs_panic_body`]).
#[derive(Debug)]
pub(super) enum SignedAbsRow {
    /// The panic-freedom VIOLATION formula, and the signed-int type of `Self` at the
    /// width the row is built at.
    Modeled(Formula, Ty),
    /// A fail-closed `UnsupportedMir` row (`pointer-width-unresolved`): the formula
    /// and the kind, minted with no guard assembly, as the numeric family does.
    Refused(Formula, VcKind),
}

/// The panic-freedom VIOLATION formula (and the receiver's signed-int type) for a
/// signed `iN::abs` call: SAT iff the receiver can be `iN::MIN` (its sole panic
/// input). Mirrors the negation-overflow obligation (`v2_build_negation_raw_vc`)
/// exactly, so a bounded/guarded receiver (`if x != iN::MIN { x.abs() }`, `(x &
/// 0x7f).abs()`) proves and an unconstrained one stays refutable. The type is
/// returned so the emitted obligation carries `VcKind::NegationOverflow { ty }` —
/// abs-at-MIN IS a negation overflow, and that kind routes identically to `-x`
/// (BV-capable discharge), where a plain `Assertion` panic-freedom kind does NOT
/// discharge the BV bound and would FALSE-refute `(x & 0x7f).abs()`. `None` when
/// `callee` is not core's signed `abs` (a float `abs` is total — no panic).
///
/// Trust (ABS-LIT-WIDTH-1, 2026-10-11): the width is the OWNER's, never the
/// receiver's `crate::operand_ty`. That function types a width-less signed literal
/// (`ConstValue::Int`) as i64, so for `i32::MIN.abs()` (and for `let m = i32::MIN;
/// m.abs()` or `const M: i32 = i32::MIN; M.abs()`, which reach the call as the same
/// constant operand) the row asked whether `-2^31 == i64::MIN`. That is UNSAT, and the
/// row was published `proved` with clean-kernel `Certified` evidence for a call that
/// panics "attempt to negate with overflow"; `i16::MIN.abs()` and `(-128i8).abs()`
/// the same. The width now comes from, in order:
///   1. the owner, `core::num::<impl iN>` ([`numeric_panic::int_inherent_minting`]):
///      a fixed-width `iN` is its own width;
///   2. for `isize`, the receiver's DECLARED pointer width
///      ([`numeric_panic::resolve_owner_width`]); a signed literal declares none;
///   3. for `isize`, the declared pointer width of the call's destination: `abs`
///      returns `Self`, so `dest` is `Ty::Int { 64 }` on the host and
///      `Ty::Int { 32 }` on i686 and wasm32.
///
/// If none of them fixes an `isize` width (a faithful `PtrSizedInt` receiver and
/// destination), the row is REFUSED with `pointer-width-unresolved`
/// ([`SignedAbsRow::Refused`]), never built at an assumed width and never dropped:
/// `abs` has no other row, so dropping it would accept the call silently. For a
/// place receiver of a fixed-width owner nothing moves: its declared width is the
/// owner's.
pub(super) fn signed_abs_panic_body(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
) -> Option<SignedAbsRow> {
    let (owner, true, "abs") = numeric_panic::int_inherent_minting(callee)? else {
        return None;
    };
    let arg = args.first()?;
    // The receiver must still be a signed integer, as before: only the WIDTH is no
    // longer read from it. An operand with no integer type (an `Unsupported` one
    // mints its own fail-closed row) gets no `abs` row here, as before.
    if !crate::operand_ty_cow(func, arg).is_some_and(|t| t.is_signed()) {
        return None;
    }
    let width = match owner {
        numeric_panic::IntWidth::Fixed(w) => w,
        numeric_panic::IntWidth::Pointer => {
            match numeric_panic::resolve_owner_width(func, owner, true, Some(arg), true).or_else(
                || {
                    let dest_op = Operand::Copy(if dest.projections.is_empty() {
                        Place::local(dest.local)
                    } else {
                        dest.clone()
                    });
                    numeric_panic::declared_pointer_width(func, &dest_op, true)
                },
            ) {
                Some(w) => w,
                None => {
                    let (formula, kind) = numeric_panic::pointer_width_unresolved("abs")?;
                    return Some(SignedAbsRow::Refused(formula, kind));
                }
            }
        }
    };
    let ty = Ty::Int { width, signed: true };
    let value = operand_to_formula(func, arg);
    let int_min = crate::range::type_min_formula(width, true);
    let body = Formula::And(vec![
        crate::range::input_range_constraint(&value, width, true),
        Formula::Eq(Box::new(value), Box::new(int_min)),
    ]);
    Some(SignedAbsRow::Modeled(body, ty))
}

/// Trust (unwrap panic-freedom, dominated-safe): the std enum def-paths, the
/// expected variant-name pair, and the PANIC-variant name for a std
/// `Option`/`Result` `unwrap`-family call. `None` for anything else — in
/// particular a USER extension-trait `unwrap`/`expect` (whose panic semantics
/// are arbitrary; modeling them could mint a false panic-freedom proof) never
/// matches: the caller additionally anchors the callee path on the std enum
/// def-path prefix, which a user item can never carry under `safe_def_path_str`.
pub(super) fn std_unwrap_family_panic_variant(
    callee: &str,
) -> Option<(&'static [&'static str], &'static [&'static str], &'static str)> {
    const OPTION_PATHS: &[&str] = &["core::option::Option", "std::option::Option"];
    const OPTION_VARIANTS: &[&str] = &["None", "Some"];
    const RESULT_PATHS: &[&str] = &["core::result::Result", "std::result::Result"];
    const RESULT_VARIANTS: &[&str] = &["Ok", "Err"];
    // Anchor on the callee PREFIX (the method's self type), never a substring:
    // `Result::<Option<T>, E>::unwrap` mentions BOTH enums in its generic args,
    // but only the prefix names the receiver.
    match method_tail(callee) {
        // `unwrap`/`expect` panic on the FAILURE variant.
        "unwrap" | "expect" => {
            if OPTION_PATHS.iter().any(|p| callee.starts_with(p)) {
                Some((OPTION_PATHS, OPTION_VARIANTS, "None"))
            } else if RESULT_PATHS.iter().any(|p| callee.starts_with(p)) {
                Some((RESULT_PATHS, RESULT_VARIANTS, "Err"))
            } else {
                None
            }
        }
        // `unwrap_err`/`expect_err` (Result-only) panic on the SUCCESS variant.
        "unwrap_err" | "expect_err" if RESULT_PATHS.iter().any(|p| callee.starts_with(p)) => {
            Some((RESULT_PATHS, RESULT_VARIANTS, "Ok"))
        }
        _ => None,
    }
}

/// Trust (tag-transparent hop): a std `Option`/`Result` `as_ref` call — its
/// result's discriminant EQUALS its receiver's discriminant by definition, so
/// tag-origin resolution may hop through it. `as_mut` is deliberately excluded:
/// its `&mut self` borrow already unpins the receiver, so the chain fails
/// closed anyway, and a mutable reborrow could feed a `SetDiscriminant`.
pub(super) fn std_as_ref_call(callee: &str) -> bool {
    const OPTION_PATHS: [&str; 2] = ["core::option::Option", "std::option::Option"];
    const RESULT_PATHS: [&str; 2] = ["core::result::Result", "std::result::Result"];
    method_tail(callee) == "as_ref"
        && (OPTION_PATHS.iter().any(|p| callee.starts_with(p))
            || RESULT_PATHS.iter().any(|p| callee.starts_with(p)))
}

/// Trust (tag-transparent hop): [`unwrap_receiver_origin`] extended THROUGH std
/// `as_ref` calls — for `o.as_ref().is_some()` / `o.as_ref().unwrap()` the tag
/// origin resolves to `o` itself, because `as_ref` preserves the discriminant
/// exactly. Each hop requires the full probe borrow shape (the call's single
/// argument is a Copy/Move of a bare local whose unique def is a SHARED borrow
/// of a bare local) and re-runs the pinned-origin resolution on the referent,
/// so an unpinned link still fails closed. Depth-capped like the base resolver.
pub(super) fn unwrap_tag_origin(func: &VerifiableFunction, local: usize) -> Option<usize> {
    let mut cur = unwrap_receiver_origin(func, local)?;
    // PERF-COMPILER-VCGEN-727: `unwrap_origin_call_def` requires a bare-dest Call
    // terminator, and a pinned parameter (`unwrap_receiver_origin` already verified
    // `unwrap_receiver_local_is_pinned(func, cur)`) has `never_explicitly_reseated`, so
    // it never has a `Call` write. Short-circuit both before scanning terminators.
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Some(cur);
    }
    for _ in 0..4 {
        if crate::local_defs::is_parameter(func, cur) {
            return Some(cur);
        }
        let Some((callee, args, _)) = unwrap_origin_call_def(func, cur) else {
            return Some(cur);
        };
        if !std_as_ref_call(callee) {
            return Some(cur);
        }
        let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else {
            return Some(cur);
        };
        // SOUNDNESS (aliased reseat, audit r4): the as_ref receiver temp `p`
        // must be PINNED before its `&referent` def is trusted — a reseated `p`
        // has a stale borrow def, so the hop would resolve to the wrong origin.
        // Stop the hop (keep the current pinned origin) on an unpinned link.
        if !p.projections.is_empty()
            || crate::local_defs::is_parameter(func, p.local)
            || !unwrap_receiver_local_is_pinned(func, p.local)
        {
            return Some(cur);
        }
        let Some(Rvalue::Ref { mutable: false, place: referent }) =
            crate::local_defs::unique_value_def(func, p.local)
        else {
            return Some(cur);
        };
        if !referent.projections.is_empty() {
            return Some(cur);
        }
        cur = unwrap_receiver_origin(func, referent.local)?;
    }
    Some(cur)
}

/// Trust (tag-transparent hop, observer-gate contract): does this block's
/// terminator define an `as_ref` result whose tag-origin resolution CONNECTS
/// back to `origin`? Only then is the as_ref call a connected (whitelisted)
/// observer — the fires-only discipline every modeled channel follows.
pub(super) fn as_ref_hop_connected(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    origin: usize,
) -> bool {
    let Terminator::Call { func: callee, dest, .. } = &block.terminator else {
        return false;
    };
    std_as_ref_call(callee)
        && dest.projections.is_empty()
        && unwrap_tag_origin(func, dest.local) == Some(origin)
}

/// Trust (probe-call model): the std enum def-paths and the PROBED variant name
/// for a std `Option`/`Result` state probe (`is_some`/`is_none`/`is_ok`/`is_err`).
/// `None` for anything else — a USER extension-trait probe never matches (the
/// caller additionally anchors the receiver type on the std enum def-path, which
/// a user item can never carry under `safe_def_path_str`). The probe's return
/// value is EXACTLY `receiver.__tag == probe_tag`, which is what
/// [`probe_call_definitions`] records.
pub(super) fn std_option_result_probe_variant(
    callee: &str,
) -> Option<(&'static [&'static str], &'static str)> {
    const OPTION_PATHS: &[&str] = &["core::option::Option", "std::option::Option"];
    const RESULT_PATHS: &[&str] = &["core::result::Result", "std::result::Result"];
    match method_tail(callee) {
        "is_some" if OPTION_PATHS.iter().any(|p| callee.starts_with(p)) => {
            Some((OPTION_PATHS, "Some"))
        }
        "is_none" if OPTION_PATHS.iter().any(|p| callee.starts_with(p)) => {
            Some((OPTION_PATHS, "None"))
        }
        "is_ok" if RESULT_PATHS.iter().any(|p| callee.starts_with(p)) => {
            Some((RESULT_PATHS, "Ok"))
        }
        "is_err" if RESULT_PATHS.iter().any(|p| callee.starts_with(p)) => {
            Some((RESULT_PATHS, "Err"))
        }
        _ => None,
    }
}

/// Trust (probe-call model): the PATH-DEFINITION facts a modeled std probe call
/// terminator establishes on its success edge — for `_g = o.is_some()` (MIR:
/// `_b = &o; _g = is_some(move _b)`), the exact result semantics
///   `(_g ∧ tag == PROBE) ∨ (¬_g ∧ tag ≠ PROBE)`
/// plus the variant-range fact `tag ∈ {variant tags}` over the SAME tag term, so
/// a two-variant complement (`is_err() == false ⇒ tag == Ok`) also discharges.
/// The tag term is the SHARED one the unwrap lane cites
/// ([`receiver_tag_term_any`]): a dominating `if o.is_some()` guard (`_g`, via
/// the bool path guard) then pins the very variable the unwrap VC's body tests,
/// turning the un-inlined probe idiom from a fail-closed UNKNOWN into a PROVED
/// obligation — and an `if o.is_none()`-guarded unwrap into a refutation.
///
/// Fail-closed (`Vec::new()`) on every unrecognized shape: non-probe callee,
/// projected/non-SSA bool dest, a receiver that is not a shared borrow of a
/// pinned bare local, a non-modeled enum layout, or no derivable tag term.
/// SOUNDNESS: `is_*` are TOTAL and return exactly the discriminant test of the
/// receiver AT THE CALL; the receiver origin is pinned
/// (`unwrap_receiver_origin`), so its tag at the call equals the recorded term
/// (a construction tag, a prior read's dest, or the free entry-tag field of a
/// pinned parameter). The fact is threaded only to the call's successor (the
/// path-definition fixpoint pushes terminator outflow to `ClauseTarget::Block`
/// targets), never before the call.
pub(super) fn probe_call_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator else {
        return Vec::new();
    };
    if args.is_empty()
        || !dest.projections.is_empty()
        || !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool))
    {
        return Vec::new();
    }
    let Some(probe) = std_option_result_probe_variant(callee) else {
        return Vec::new();
    };
    if !is_single_static_assignment(func, dest.local) {
        return Vec::new();
    }
    let whole = probe_call_definitions_whole_local(func, block, probe);
    if !whole.is_empty() {
        return whole;
    }
    // Trust (2026-10-03, unwrap-from-facts): the probe's receiver is not a
    // borrow of a bare enum local but a SUBJECT place — the pointee of a shared
    // `&Enum` parameter (`fn f(x: &Option<u32>) { if x.is_some() { … } }`,
    // MIR `is_some(copy _1)`) or a field of one (`&(*s).0`). See
    // [`probe_subject_model`].
    probe_subject_model_resolved(func, block, probe).map(|(_, facts)| facts).unwrap_or_default()
}

/// The whole-local half of [`probe_call_definitions`] (the receiver borrows a
/// bare, pinned enum local).
fn probe_call_definitions_whole_local(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    (enum_paths, probe_variant): (&'static [&'static str], &'static str),
) -> Vec<Formula> {
    let Terminator::Call { args, dest, target: Some(_), .. } = &block.terminator else {
        return Vec::new();
    };
    // PERF-COMPILER-VCGEN-727: caller (`probe_call_definitions`) has already verified
    // `dest.projections.is_empty()`, `Ty::Bool`, and `is_single_static_assignment(dest.local)`.
    // Receiver: probes take `&self` — a Copy/Move of a bare local whose unique
    // def is a shared borrow of a bare local (the `is_ok`-call shape).
    let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else {
        return Vec::new();
    };
    // SOUNDNESS (aliased reseat, audit r4): pin `recv` before trusting its
    // `&referent` def — a reseated probe receiver has a stale borrow def, so the
    // fact would be minted over the wrong subject while the probe reads another.
    if !recv.projections.is_empty()
        || crate::local_defs::is_parameter(func, recv.local)
        || !unwrap_receiver_local_is_pinned(func, recv.local)
    {
        return Vec::new();
    }
    let Some(Rvalue::Ref { mutable: false, place: referent }) =
        crate::local_defs::unique_value_def(func, recv.local)
    else {
        return Vec::new();
    };
    if !referent.projections.is_empty() {
        return Vec::new();
    }
    // Tag-transparent: `o.as_ref().is_some()` probes the as_ref RESULT, whose
    // discriminant equals `o`'s — resolve the origin THROUGH the hop so the
    // fact cites `o`'s own tag term (the one the unwrap obligation tests).
    let Some(origin) = unwrap_tag_origin(func, referent.local) else {
        return Vec::new();
    };
    let Some(ty) = crate::local_ty_ref(func, origin) else {
        return Vec::new();
    };
    let Some((name, variants)) = modeled_std_enum_shape(ty) else {
        return Vec::new();
    };
    if !enum_paths.contains(&name) {
        return Vec::new();
    }
    let Some(probe_tag) = variants.iter().find(|v| v.name == probe_variant).map(|v| v.discriminant)
    else {
        return Vec::new();
    };
    let Some(tag) = receiver_tag_term_any(func, origin, variants) else {
        return Vec::new();
    };
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(probe_tag)));
    let semantics = Formula::Or(vec![
        Formula::And(vec![guard.clone(), probed.clone()]),
        Formula::And(vec![Formula::Not(Box::new(guard)), Formula::Not(Box::new(probed))]),
    ]);
    let range = Formula::Or(
        variants
            .iter()
            .map(|v| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(v.discriminant))))
            .collect(),
    );
    vec![semantics, range]
}

/// Trust (eq-guard channel): the std-spelled UNRESOLVED `PartialEq` trait
/// method — `Some(negated)`. Exact match, no turbofish (the unresolved trait
/// method's def-path carries none): the extractor keeps this spelling for
/// `Option`/`Result` receivers (`std_enum_partial_eq_keeps_name` pre-empts the
/// total-clone sentinel exactly for them), so the name arrives here for both
/// the concrete-total and the generic case. Anything else — including the
/// ambiguous `__trust_total_clone` sentinel, which also covers `lt`/`le`/
/// `gt`/`ge` — never matches (attaching equality semantics to the sentinel
/// would be UNSOUND: `o < None` is not `o == None`).
pub(super) fn std_partial_eq_callee(callee: &str) -> Option<bool> {
    if !callee.ends_with("::eq") && !callee.ends_with("::ne") {
        return None;
    }
    if trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return None;
    }
    let tail = if let Some((_self_ty, rest)) = split_qualified_callee_at_top_level_as(callee) {
        rest
    } else {
        callee
    };
    match tail {
        "std::cmp::PartialEq::eq"
        | "core::cmp::PartialEq::eq"
        | "std::cmp::PartialEq>::eq"
        | "core::cmp::PartialEq>::eq" => Some(false),
        "std::cmp::PartialEq::ne"
        | "core::cmp::PartialEq::ne"
        | "std::cmp::PartialEq>::ne"
        | "core::cmp::PartialEq>::ne" => Some(true),
        _ => None,
    }
}

/// Trust (eq-guard channel): classify one `PartialEq::{eq,ne}` argument as the
/// RECEIVER side — byte-for-byte the probe receiver shape: a Copy/Move of a
/// bare local whose unique def is a SHARED borrow of a bare local, resolved
/// through the pinned/tag-transparent origin chain.
pub(super) fn eq_side_receiver(func: &VerifiableFunction, arg: &Operand) -> Option<usize> {
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return None;
    };
    // SOUNDNESS (aliased reseat, audit r4): pin the eq receiver before trusting
    // its `&referent` def — a reseated receiver has a stale borrow def.
    // PERF-COMPILER-VCGEN-728: parameters never have `unique_value_def == Some(..)`;
    // reject parameters and unpinned locals before querying `unique_value_def`.
    if !place.projections.is_empty()
        || crate::local_defs::is_parameter(func, place.local)
        || !unwrap_receiver_local_is_pinned(func, place.local)
    {
        return None;
    }
    let Some(Rvalue::Ref { mutable: false, place: referent }) =
        crate::local_defs::unique_value_def(func, place.local)
    else {
        return None;
    };
    if !referent.projections.is_empty() {
        return None;
    }
    unwrap_tag_origin(func, referent.local)
}

/// Trust (eq-guard channel): classify one `PartialEq::{eq,ne}` argument as the
/// PINNED PAYLOAD-LESS-VARIANT side — `(enum def-path, variant index)`. Three
/// recognized shapes, every one immutable by construction:
///   * the promoted literal (`o == None`): the argument IS the
///     [`trust_types::ConstValue::UnitVariantRef`] constant the extractor
///     recovers from the promoted `&Option<T>::None`;
///   * the const-copied local (`_4 = const promoted[0]`): a bare local whose
///     unique def is a `Use` of that constant;
///   * the let-bound construction (`let n = None; o == n` → `_5 = &n`): a bare
///     local whose unique def is a shared borrow of a PINNED bare local whose
///     unique def is a ZERO-OPERAND ADT aggregate (`ops.is_empty()` — the
///     payload-less gate; a `Some(x)` construction never matches).
pub(super) fn eq_side_pinned_unit<'a>(
    func: &'a VerifiableFunction,
    arg: &'a Operand,
) -> Option<(&'a str, usize)> {
    if let Operand::Constant(trust_types::ConstValue::UnitVariantRef {
        enum_name, variant, ..
    }) = arg
    {
        return Some((enum_name.as_str(), *variant));
    }
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return None;
    };
    // SOUNDNESS (aliased reseat, audit r4): pin `place` before trusting its
    // const/`&referent` def — a reseated unit-variant side would compare against
    // a DIFFERENT variant than the recorded one (false fact).
    // PERF-COMPILER-VCGEN-728: reject parameters and unpinned locals before querying
    // `unique_value_def`.
    if !place.projections.is_empty()
        || crate::local_defs::is_parameter(func, place.local)
        || !unwrap_receiver_local_is_pinned(func, place.local)
    {
        return None;
    }
    match crate::local_defs::unique_value_def(func, place.local)? {
        Rvalue::Use(Operand::Constant(trust_types::ConstValue::UnitVariantRef {
            enum_name,
            variant,
            ..
        })) => Some((enum_name.as_str(), *variant)),
        Rvalue::Ref { mutable: false, place: referent }
            if referent.projections.is_empty()
                && !crate::local_defs::is_parameter(func, referent.local)
                && unwrap_receiver_local_is_pinned(func, referent.local) =>
        {
            match crate::local_defs::unique_value_def(func, referent.local)? {
                Rvalue::Aggregate(
                    AggregateKind::Adt { name, variant, active_field: None, .. },
                    ops,
                ) if ops.is_empty() => Some((name.as_str(), *variant)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Trust (eq-guard channel): the PATH-DEFINITION facts a modeled
/// `Option`/`Result` `PartialEq::{eq,ne}`-against-a-payload-less-variant call
/// establishes — for `_g = (o == None)`:
///   `(_g ∧ tag == UNIT_TAG) ∨ (¬_g ∧ tag ≠ UNIT_TAG)`    (polarity flipped for `ne`)
/// plus the variant-range fact over the SAME shared tag term, exactly the probe
/// channel's pair — so `if o == None { 0 } else { o.unwrap() }` PROVES and
/// `if o == None { o.unwrap() }` REFUTES.
///
/// SOUNDNESS: the callee is the unresolved std trait method and the receiver
/// TYPE is anchored to the std enum def-path; coherence (orphan rule — Option/
/// Result are foreign, non-fundamental) forbids any user impl, and core's impl
/// against a payload-less variant returns EXACTLY the discriminant test (the
/// `(Some, Some)` payload arm is unreachable, no user code runs). Payload-
/// carrying comparisons NEVER model: the pinned side requires a zero-operand
/// construction / unit-variant const AND `vd.fields.is_empty()` — `o == Some(x)`
/// and `o == p` fail closed (and keep the observer gate shut).
pub(super) fn eq_unit_call_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return Vec::new();
    };
    if args.len() != 2
        || !dest.projections.is_empty()
        || !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool))
    {
        return Vec::new();
    }
    let Some(negated) = std_partial_eq_callee(callee) else {
        return Vec::new();
    };
    if !is_single_static_assignment(func, dest.local) {
        return Vec::new();
    }
    // Exactly one receiver + one pinned unit, either order.
    let classified = [(0usize, 1usize), (1, 0)].into_iter().find_map(|(r, u)| {
        let origin = eq_side_receiver(func, &args[r])?;
        let (enum_name, variant) = eq_side_pinned_unit(func, &args[u])?;
        Some((origin, enum_name, variant))
    });
    let Some((origin, unit_enum, variant)) = classified else {
        return Vec::new();
    };
    let Some(ty) = crate::local_ty_ref(func, origin) else {
        return Vec::new();
    };
    let Some((name, variants)) = modeled_std_enum_shape(ty) else {
        return Vec::new();
    };
    // Same std flavor on both sides (Option-vs-Option or Result-vs-Result).
    const OPTION_PATHS: [&str; 2] = ["core::option::Option", "std::option::Option"];
    const RESULT_PATHS: [&str; 2] = ["core::result::Result", "std::result::Result"];
    let same_flavor = (OPTION_PATHS.contains(&name) && OPTION_PATHS.contains(&unit_enum))
        || (RESULT_PATHS.contains(&name) && RESULT_PATHS.contains(&unit_enum));
    if !same_flavor {
        return Vec::new();
    }
    let Some(vd) = variants.get(variant) else {
        return Vec::new();
    };
    // The load-bearing payload-less gate: equality against a variant WITH a
    // payload is never a pure tag test.
    if !vd.fields.is_empty() {
        return Vec::new();
    }
    let unit_tag = vd.discriminant;
    let Some(tag) = receiver_tag_term_any(func, origin, variants) else {
        return Vec::new();
    };
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(unit_tag)));
    let (pos, neg) = if negated {
        (Formula::Not(Box::new(probed.clone())), probed)
    } else {
        (probed.clone(), Formula::Not(Box::new(probed)))
    };
    let semantics = Formula::Or(vec![
        Formula::And(vec![guard.clone(), pos]),
        Formula::And(vec![Formula::Not(Box::new(guard)), neg]),
    ]);
    let range = Formula::Or(
        variants
            .iter()
            .map(|v| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(v.discriminant))))
            .collect(),
    );
    vec![semantics, range]
}

/// The SMT variable for a FIELD place's discriminant tag — the `__tag` field of
/// the flattened std enum at `(*base).field`, named via `place_to_var_name` so
/// the unwrap refutation and the guard's injected fact cite the SAME term.
/// Fail-closed when the layout carries no Int tag (niche/bool tag).
pub(super) fn field_tag_var(func: &VerifiableFunction, field_place: &Place) -> Option<Formula> {
    let explicit = crate::explicit_discriminant_field_for_place(func, field_place).ok()?;
    if !matches!(explicit.ty, Ty::Int { .. }) {
        return None;
    }
    Some(Formula::Var(place_to_var_name(func, &explicit.place), Sort::Int))
}

/// A field subject `(*base).field` has a FREE entry tag (⇒ refutable when
/// unguarded, pinnable by a guard) exactly when `base` is a pinned PARAMETER:
/// its pointee's field is initialized at entry and — via
/// [`unwrap_receiver_local_is_pinned`]'s `place_source_is_stable` (no rebind,
/// no `&mut`/`&raw mut`, no projected store) — cannot be reseated or mutated in
/// the body, so its tag is a single free value on every execution.
///
/// SOUNDNESS (raw-pointer / `&mut`-cast alias, audit r2): for a Deref-rooted
/// field (`(*base).f`) the pointee must be IMMUTABLE, i.e. `base` must be a
/// SHARED `&T`. A `&mut`/`*mut`/`*const` base admits a mutation alias the
/// syntactic pinning gate cannot see (`p = copy base; SetDiscriminant((*p).f)`
/// or `p = base as *mut _; …` sets `(*base).f` through a DIFFERENT local, so
/// `place_source_is_stable(base)` — which only inspects writes rooted at `base`
/// — still reports pinned). A by-value field (`base.f`, no Deref) carries no
/// such indirection: the field is part of the pinned value.
pub(super) fn field_subject_is_pinned(func: &VerifiableFunction, field_place: &Place) -> bool {
    let base = field_place.local;
    if !((1..=func.body.arg_count).contains(&base) && unwrap_receiver_local_is_pinned(func, base)) {
        return false;
    }
    if field_place.projections.first() == Some(&trust_types::Projection::Deref) {
        // Deref-rooted field: the base must be a shared reference so the pointee
        // (and thus the field) cannot be mutated through any pointer alias.
        //
        // Trust (2026-10-03, unwrap-from-facts): and the pointee a `Field` hop
        // steps into must not be an interior-mutability wrapper — a shared `&`
        // does not freeze an `UnsafeCell`'s contents (the same rule
        // `guards::ty_is_interior_mut_wrapper` enforces for field-place keys).
        // Safe code cannot name such a field, but the gate must not rely on it.
        match crate::local_ty_ref(func, base) {
            Some(Ty::Ref { mutable: false, inner }) => {
                field_place.projections.len() == 1
                    || !crate::guards::ty_is_interior_mut_wrapper(inner.as_ref())
            }
            _ => false,
        }
    } else {
        // By-value field of a pinned aggregate param — no indirection. Not
        // through an interior-mutability wrapper (2026-10-03): a shared borrow
        // of the param handed to a callee could write it.
        crate::local_ty_ref(func, base)
            .is_some_and(|ty| !crate::guards::ty_is_interior_mut_wrapper(ty))
    }
}

/// Trust (2026-10-03, unwrap-from-facts): the projections a pinnable SUBJECT
/// place may carry — a by-value field of a parameter (`[Field]`), the pointee
/// of a shared-reference parameter (`[Deref]`), or a field of that pointee
/// (`[Deref, Field]`). Exactly the shapes [`field_subject_is_pinned`] can
/// decide: the base local is `place.local`, and nothing between it and the
/// enum can be re-pointed.
pub(super) fn is_pinnable_subject_projection(projs: &[trust_types::Projection]) -> bool {
    matches!(
        projs,
        [trust_types::Projection::Field(_)]
            | [trust_types::Projection::Deref]
            | [trust_types::Projection::Deref, trust_types::Projection::Field(_)]
    )
}

/// Trust (2026-10-03, unwrap-from-facts): the ONE tag term every channel cites
/// for a pinned SUBJECT place (see [`field_subject_is_pinned`]) — the unwrap
/// refutation body, a std probe's result semantics, an inferred guard-helper
/// contract. Sharing the term is what links a guard to the unwrap it dominates.
///
///   * READ-pinned: a `_d = Discriminant(subject)` statement whose dest `_d` is a
///     bare, non-parameter, stable local with exactly that read as its one
///     definition (the `match *x { Some(_) => x.unwrap(), … }` / `if let` shape).
///     The term is `_d`'s variable, so the switch guard on `_d` pins it.
///     The FIRST such read in block order is chosen (deterministic); any other
///     read of the subject stays an opaque observer in
///     [`field_tag_observed_elsewhere`], which keeps that shape fail-closed.
///   * otherwise the subject's free entry tag ([`field_tag_var`]).
///
/// SOUNDNESS: a pinned subject is immutable for the whole body (a shared
/// reference PARAMETER's pointee is protected for the call; a by-value param
/// field is never written — [`field_subject_is_pinned`]), so `_d` equals the
/// subject's tag after the read on every execution, and a path that never ran
/// the read leaves `_d` free (under-constrained ⇒ SAT ⇒ the row stays failed).
pub(super) fn subject_tag_term(func: &VerifiableFunction, subject: &Place) -> Option<Formula> {
    subject_read_pinned_dest(func, subject)
        .map(|dest| Formula::Var(place_to_var_name(func, &dest), Sort::Int))
        .or_else(|| field_tag_var(func, subject))
}

/// The dest of the read that pins [`subject_tag_term`], if any.
fn subject_read_pinned_dest(func: &VerifiableFunction, subject: &Place) -> Option<Place> {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            if src != subject || !dest.projections.is_empty() {
                continue;
            }
            if (1..=func.body.arg_count).contains(&dest.local)
                || !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Int { .. }))
                || !matches!(
                    crate::local_defs::unique_value_def(func, dest.local),
                    Some(Rvalue::Discriminant(read)) if read == subject
                )
                || !crate::place_source_is_stable(func, dest.local)
            {
                continue;
            }
            return Some(dest.clone());
        }
    }
    None
}

/// Trust (2026-10-03, unwrap-from-facts): the SUBJECT place a shared `&Enum`
/// operand denotes, for the subject lane:
///   (a) a pinned bare temp whose unique definition is a SHARED borrow of a
///       place with a NON-empty pinnable projection (`_3 = &((*_1).0)`,
///       `_3 = &(*_1)`, `_3 = &(_1.0)`) — a borrow of a bare local is the
///       whole-local lane's, never this one's;
///   (b) a pinned shared-reference PARAMETER passed directly (`is_some(copy _1)`
///       for `x: &Option<u32>`): the subject is `*_1`.
/// `None` on anything else (fail-closed). The caller still has to ask
/// [`field_subject_is_pinned`] of the result.
pub(super) fn shared_ref_operand_subject(func: &VerifiableFunction, op: &Operand) -> Option<Place> {
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    if (1..=func.body.arg_count).contains(&place.local) {
        return (matches!(
            crate::local_ty_ref(func, place.local),
            Some(Ty::Ref { mutable: false, .. })
        ) && unwrap_receiver_local_is_pinned(func, place.local))
        .then(|| Place { local: place.local, projections: vec![trust_types::Projection::Deref] });
    }
    match crate::local_defs::unique_value_def(func, place.local) {
        Some(Rvalue::Ref { mutable: false, place: referent })
            if !referent.projections.is_empty()
                && is_pinnable_subject_projection(&referent.projections)
                && unwrap_receiver_local_is_pinned(func, place.local) =>
        {
            Some(referent.clone())
        }
        _ => None,
    }
}

/// Trust (2026-10-03, unwrap-from-facts): the probe model for a SUBJECT
/// receiver — the subject twin of [`probe_call_definitions`]' whole-local
/// model, emitting the same fact pair
///   `(_g ∧ tag == PROBE) ∨ (¬_g ∧ tag ≠ PROBE)`   +   `tag ∈ {variant tags}`
/// over [`subject_tag_term`]. Returns the subject so the observer gate can
/// require place equality (fires-only, never a blanket exemption).
///
/// SOUNDNESS: `is_some`/`is_none`/`is_ok`/`is_err` are TOTAL and return exactly
/// the discriminant test of their receiver at the call; the subject is pinned
/// (immutable for the body), so its tag at the call is the term's value.
pub(super) fn probe_subject_model(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(Place, Vec<Formula>)> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return None;
    };
    if args.len() != 1
        || !dest.projections.is_empty()
        || !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool))
    {
        return None;
    }
    let probe = std_option_result_probe_variant(callee)?;
    if !is_single_static_assignment(func, dest.local) {
        return None;
    }
    probe_subject_model_resolved(func, block, probe)
}

fn probe_subject_model_resolved(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    (enum_paths, probe_variant): (&'static [&'static str], &'static str),
) -> Option<(Place, Vec<Formula>)> {
    let Terminator::Call { args, dest, target: Some(_), .. } = &block.terminator else {
        return None;
    };
    // PERF-COMPILER-VCGEN-727: both callers (`probe_call_definitions` and
    // `probe_subject_model`) have already verified `dest.projections.is_empty()`,
    // `Ty::Bool`, and `is_single_static_assignment(dest.local)`.
    if args.len() != 1 {
        return None;
    }
    let subject = shared_ref_operand_subject(func, args.first()?)?;
    if !field_subject_is_pinned(func, &subject) {
        return None;
    }
    let ty = crate::place_ty_cow(func, &subject)?;
    let (name, variants) = modeled_std_enum_shape(ty.as_ref())?;
    if !enum_paths.contains(&name) {
        return None;
    }
    let probe_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    let tag = subject_tag_term(func, &subject)?;
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(probe_tag)));
    let semantics = Formula::Or(vec![
        Formula::And(vec![guard.clone(), probed.clone()]),
        Formula::And(vec![Formula::Not(Box::new(guard)), Formula::Not(Box::new(probed))]),
    ]);
    let range = Formula::Or(
        variants
            .iter()
            .map(|v| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(v.discriminant))))
            .collect(),
    );
    Some((subject, vec![semantics, range]))
}

/// Trust (2026-10-03, unwrap-from-facts): the SUBJECT a std `as_ref` call
/// borrows, when its result is a tag-transparent view of that subject consumed
/// ONLY by unwrap-family calls — `x.as_ref().unwrap()` for `x: &Option<String>`
/// (MIR `_3 = Option::as_ref(copy _1); unwrap(move _3)`), the idiom for a
/// non-`Copy` payload. `as_ref` preserves the discriminant exactly.
///
/// The use gate is what keeps the lane fires-only: the result local must be
/// pinned, bare, and appear nowhere but its defining call, storage markers,
/// and the FIRST argument of unwrap-family calls — so no opaque consumer of the
/// view can be the guard this lane cannot see.
pub(super) fn as_ref_result_subject(func: &VerifiableFunction, local: usize) -> Option<Place> {
    if crate::local_defs::is_parameter(func, local)
        || !super::terminator_presence_for(func).has_bare_dest_call
    {
        return None;
    }
    let (callee, args, _) = unwrap_origin_call_def(func, local)?;
    if args.len() != 1 || !std_as_ref_call(callee) || !unwrap_receiver_local_is_pinned(func, local)
    {
        return None;
    }
    let subject = shared_ref_operand_subject(func, &args[0])?;
    as_ref_view_only_unwrapped(func, local).then_some(subject)
}

/// The USE gate of [`as_ref_result_subject`]: `local` is mentioned nowhere but
/// in storage markers, its defining std `as_ref` call (found, under pinning, by
/// [`unwrap_origin_call_def`]) and as the BARE first argument of unwrap-family
/// calls. Not a definition scan: every other mention — including any construct
/// `contracts::{statement,terminator}_mentions_local_anywhere` has not audited,
/// which they answer `true` for — DECLINES, so a channel this misses can only
/// keep the row fail-closed.
fn as_ref_view_only_unwrapped(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().all(|block| {
        let stmts_ok = block.stmts.iter().all(|stmt| match stmt {
            Statement::StorageLive(_) | Statement::StorageDead(_) => true,
            other => !crate::contracts::statement_mentions_local_anywhere(other, local),
        });
        let term_ok = match &block.terminator {
            Terminator::Call { func: c, args: a, dest, .. }
                if dest.local == local && dest.projections.is_empty() && std_as_ref_call(c) =>
            {
                !a.iter()
                    .any(|op| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == local))
            }
            Terminator::Call { func: c, args: a, dest, .. }
                if std_unwrap_family_panic_variant(c).is_some() =>
            {
                // Only as the bare receiver; never written, never another arg.
                dest.local != local
                    && a.iter().enumerate().all(|(i, op)| match op {
                        Operand::Copy(p) | Operand::Move(p) if p.local == local => {
                            i == 0 && p.projections.is_empty()
                        }
                        _ => true,
                    })
            }
            other => !crate::contracts::terminator_mentions_local_anywhere(other, local),
        };
        stmts_ok && term_ok
    })
}

/// The SUBJECT place a field guard's receiver borrows: `self` inside a
/// `&self` helper is `*receiver`, so the caller subject is the reborrow's
/// referent (`_r = &(subj); is_ready(move _r)`) or, for a directly-passed
/// `&Struct` receiver, its deref (`*x`). Bare copy hops are followed.
/// Fail-closed (`None`) on a projected pred actual or a too-deep chain.
///
/// SOUNDNESS (aliased reseat, audit r3): EVERY hop local must be PINNED before
/// its `unique_value_def` is trusted — exactly as [`unwrap_receiver_origin`]
/// does for the whole-pointee lane. Without it, a reference local reseated
/// through an ALIAS (`let mut r=o; mem::swap(&mut r, &mut r2); check(r)`) has a
/// stale `Use(Copy(o))` def (the `&mut r` write is invisible to
/// `unique_value_def`), so the guard subject would mis-resolve to `*o`
/// while `r` points at `r2` at the call — threading the guard's fact onto the
/// WRONG subject and discharging a genuinely-panicking `o.slot.unwrap()` (a safe
/// -code FALSE PROVE). A `&mut`/alias-reseated `cur` fails `place_source_is_stable`.
pub(super) fn guard_receiver_subject(func: &VerifiableFunction, recv: &Place) -> Option<Place> {
    if !recv.projections.is_empty() {
        return None;
    }
    let mut cur = recv.local;
    for _ in 0..4 {
        if !unwrap_receiver_local_is_pinned(func, cur) {
            return None;
        }
        // PERF-COMPILER-VCGEN-585: parameters have an implicit entry definition,
        // so `unique_value_def(func, cur)` always returns `None` after an O(blocks * stmts)
        // `local_write` scan. Short-circuit parameters directly to the deref arm.
        if crate::local_defs::is_parameter(func, cur) {
            return Some(Place {
                local: cur,
                projections: vec![trust_types::Projection::Deref],
            });
        }
        match crate::local_defs::unique_value_def(func, cur) {
            Some(Rvalue::Ref { mutable: false, place: referent }) => {
                return Some(referent.clone());
            }
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != cur =>
            {
                cur = p.local;
            }
            // No reborrow def: `cur` is a directly-passed `&Struct` value — the
            // subject is its deref (`place_ty_cow` fails closed if not a ref).
            _ => {
                return Some(Place {
                    local: cur,
                    projections: vec![trust_types::Projection::Deref],
                });
            }
        }
    }
    None
}

/// Trust (inferred contract, call-site consumer): the guard-helper twin of
/// [`probe_call_definitions`] — for `_g = my_check(&o)` where `my_check` has an
/// INFERRED [`ReturnBoolPredSummary`], emit the probe-shaped fact pair
///   `(_g ∧ tag REL T) ∨ (¬_g ∧ ¬(tag REL T))`   +   `tag ∈ {variant tags}`
/// over the CALLER's shared tag term. Returns the resolved pred ORIGIN too, so
/// the observer gate can require origin equality (a future multi-arg
/// summarized call must not exempt an unrelated Option passed elsewhere).
///
/// SOUNDNESS: the summary was derived from the callee BODY by a fail-closed
/// whole-CFG proof over an entry-pinned shared-ref param (see
/// `function_return_bool_pred_summary`); the use-site cross-checks re-anchor
/// the enum (def-path + variant tags must MATCH the summary — never applied
/// across enums or instantiating layouts), and the receiver resolution is the
/// probe channel's own pinned borrow discipline.
pub(super) fn inferred_pred_call_model(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(InferredSubject, Vec<Formula>)> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return None;
    };
    if args.is_empty()
        || !dest.projections.is_empty()
        || !crate::local_ty_ref(func, dest.local).is_some_and(|t| matches!(t, Ty::Bool))
    {
        return None;
    }
    let summary = crate::callee_return_bool_pred(callee)?;
    if args.len() != summary.params.len() || !crate::call_reaches_summarized_body(&block.terminator)
    {
        return None;
    }
    if !is_single_static_assignment(func, dest.local) {
        return None;
    }
    // The pred actual: a borrow temp / directly-passed shared ref.
    let arg = args.get(summary.pred_param.checked_sub(1)?)?;
    let (Operand::Copy(recv) | Operand::Move(recv)) = arg else {
        return None;
    };
    if !recv.projections.is_empty() {
        return None;
    }
    // Resolve the subject whose tag the contract constrains, and the tag term
    // over it — whole pointee (`&Enum` param) or a field (`&Struct` param,
    // `pred_field`). Both re-anchor the summary's enum at the use site.
    let (subject, tag) = match summary.pred_field {
        None => {
            // The guard actual is either a shared BORROW of the enum (`check(&o)`,
            // or `check(o)` where `o: &Enum` — recv resolves to `&(caller local)`)
            // or the enum passed BY VALUE (`check(o)` where `o: Enum` is Copy —
            // recv IS the caller's enum local). Resolve the pinned origin in both;
            // the enum cross-check below rejects any non-enum misresolution.
            // SOUNDNESS (aliased reseat, audit r4): the Ref arm may trust
            // `recv`'s `&referent` def ONLY when `recv` is PINNED — a reseated
            // `recv` (`let mut b=&o; let m=&mut b; *m=&o2`) has a stale `&o` def
            // while it points at `o2` at the call, so the fact would be minted
            // over the WRONG subject. An unpinned recv falls to the `_` arm,
            // whose `unwrap_tag_origin` pin-checks and returns None (fail-closed).
            // PERF-COMPILER-VCGEN-585: check `unwrap_receiver_local_is_pinned` first
            // (required by both arms since `unwrap_tag_origin` checks it on entry) and
            // skip `unique_value_def` on parameters (which never have a unique statement def).
            if !unwrap_receiver_local_is_pinned(func, recv.local) {
                return None;
            }
            let origin = if !crate::local_defs::is_parameter(func, recv.local)
                && let Some(Rvalue::Ref { mutable: false, place: referent }) =
                    crate::local_defs::unique_value_def(func, recv.local)
                && referent.projections.is_empty()
            {
                unwrap_tag_origin(func, referent.local)?
            } else {
                unwrap_tag_origin(func, recv.local)?
            };
            let ty = crate::local_ty_ref(func, origin)?;
            let (name, variants) = modeled_std_enum_shape(ty)?;
            if name != summary.enum_name
                || variants.len() != summary.variants.len()
                || !variants.iter().zip(&summary.variants).all(|(v, &t)| v.discriminant == t)
            {
                return None;
            }
            let tag = receiver_tag_term_any(func, origin, variants)?;
            (InferredSubject::Local(origin), tag)
        }
        Some(field_idx) => {
            let mut field_place = guard_receiver_subject(func, recv)?;
            field_place.projections.push(trust_types::Projection::Field(field_idx));
            if !field_subject_is_pinned(func, &field_place) {
                return None;
            }
            let field_ty = crate::place_ty_cow(func, &field_place)?;
            let (name, variants) = modeled_std_enum_shape(field_ty.as_ref())?;
            if name != summary.enum_name
                || variants.len() != summary.variants.len()
                || !variants.iter().zip(&summary.variants).all(|(v, &t)| v.discriminant == t)
            {
                return None;
            }
            let tag = subject_tag_term(func, &field_place)?;
            (InferredSubject::Field(field_place), tag)
        }
    };
    if !summary.variants.contains(&summary.pred_tag) {
        return None;
    }
    let guard = Formula::Var(place_to_var_name(func, dest), Sort::Bool);
    let mut probed = Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(summary.pred_tag)));
    if !summary.pred_is_eq {
        probed = Formula::Not(Box::new(probed));
    }
    // Emit the fact at the summary's STRENGTH:
    //   Iff         `(g ∧ probed) ∨ (¬g ∧ ¬probed)`  — proves + refutes both guards
    //   ImpliesTrue `g ⇒ probed`  = `¬g ∨ probed`     — proves `if g {unwrap}`, ¬g inconclusive
    //   ImpliesFalse`¬g ⇒ probed` = `g ∨ probed`      — proves `if g {} else {unwrap}`
    // The weaker forms are SOUND: they assert strictly less than the iff, so a
    // wrong-polarity guard simply stays fail-closed (never a spurious discharge).
    let semantics = match summary.kind {
        ReturnBoolPredKind::Iff => {
            let not_g = Formula::Not(Box::new(guard.clone()));
            Formula::Or(vec![
                Formula::And(vec![guard, probed.clone()]),
                Formula::And(vec![not_g, Formula::Not(Box::new(probed))]),
            ])
        }
        ReturnBoolPredKind::ImpliesTrue => {
            Formula::Or(vec![Formula::Not(Box::new(guard)), probed])
        }
        ReturnBoolPredKind::ImpliesFalse => Formula::Or(vec![guard, probed]),
    };
    let range = Formula::Or(
        summary
            .variants
            .iter()
            .map(|t| Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(*t))))
            .collect(),
    );
    Some((subject, vec![semantics, range]))
}

/// The path-definition facts of a modeled guard-helper call (empty when the
/// model does not fire).
pub(super) fn inferred_pred_call_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    inferred_pred_call_model(func, block).map(|(_, facts)| facts).unwrap_or_default()
}

/// Observer-gate connectedness for a WHOLE-pointee guard-helper call: fires-only
/// AND origin-equal (see [`inferred_pred_call_model`]).
pub(super) fn inferred_pred_call_connects(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    origin: usize,
) -> bool {
    matches!(
        inferred_pred_call_model(func, block),
        Some((InferredSubject::Local(o), _)) if o == origin
    )
}

/// Observer-gate connectedness for a FIELD guard-helper call: fires-only AND
/// field-place-equal, so `if x.is_ready() { x.slot.unwrap() }` connects only to
/// the `x.slot` unwrap and never an unrelated field or Option.
pub(super) fn inferred_pred_call_connects_field(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    field_place: &Place,
) -> bool {
    matches!(
        inferred_pred_call_model(func, block),
        Some((InferredSubject::Field(fp), _)) if &fp == field_place
    )
}

/// Trust (unwrap/probe shared tag term): the ONE variable both the unwrap
/// refutation body and the probe result semantics cite for a pinned receiver —
/// the recognized pinning shapes first ([`unwrap_receiver_tag_term`]:
/// construction- or read-pinned), else the FREE entry-tag field of a pinned
/// PARAMETER ([`receiver_entry_tag_var`]). Sharing this term is the proof
/// mechanism: the probe fact links the guard bool to the tag, the path guard
/// pins the bool, and the unwrap body tests the same tag ⇒ UNSAT ⇒ PROVED.
pub(super) fn receiver_tag_term_any(
    func: &VerifiableFunction,
    origin: usize,
    variants: &[trust_types::VariantDef],
) -> Option<Formula> {
    unwrap_receiver_tag_term(func, origin, variants).or_else(|| {
        if (1..=func.body.arg_count).contains(&origin) || call_pinned_origin(func, origin) {
            receiver_entry_tag_var(func, origin)
        } else {
            None
        }
    })
}

/// The receiver local's discriminant TAG cannot change after initialization:
/// [`crate::place_source_is_stable`] (at most one whole-local store, no projected
/// store, no `&mut`/`&raw` borrow, no `SetDiscriminant`/`Deinit`, no
/// projected call-dest) PLUS the parameter refinement — a PARAMETER is
/// initialized at entry WITHOUT any `Assign`, so a `mut` param with one body
/// store has TWO values and must NOT count as pinned (`place_source_is_stable`
/// alone would admit it).
pub(super) fn unwrap_receiver_local_is_pinned(func: &VerifiableFunction, local: usize) -> bool {
    if !crate::place_source_is_stable(func, local) {
        return false;
    }
    !crate::local_defs::is_parameter(func, local)
        || crate::local_defs::never_explicitly_reseated(func, local)
}

/// Follow value-preserving whole-local move/copy hops (`_5 = move _2`, the
/// compiler-inserted receiver temp) from the unwrap receiver back to its ORIGIN
/// local. Every hop local AND the origin must be pinned (see above), so the
/// receiver's tag at the call IS the origin's tag on every execution. `None`
/// (fail-closed) on any unpinned link or a cyclic/deep chain.
pub(super) fn unwrap_receiver_origin(func: &VerifiableFunction, local: usize) -> Option<usize> {
    let mut cur = local;
    for _ in 0..8 {
        if !unwrap_receiver_local_is_pinned(func, cur) {
            return None;
        }
        // PERF-COMPILER-VCGEN-585: parameters have an implicit entry definition,
        // so `unique_value_def(func, cur)` always returns `None` after an O(blocks * stmts)
        // `local_write` scan. Return `Some(cur)` in O(1) for pinned parameters.
        if crate::local_defs::is_parameter(func, cur) {
            return Some(cur);
        }
        match crate::local_defs::unique_value_def(func, cur) {
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != cur =>
            {
                cur = p.local;
            }
            _ => return Some(cur),
        }
    }
    None
}

/// `src` — the operand place of a `Discriminant` read — denotes the pinned
/// origin's value: the origin local itself (bare), or a deref of a single-def
/// SHARED borrow of it (`_b = &_r; _d = discriminant(*_b)`, the `is_ok`-inlined
/// shape). A shared borrow cannot mutate its referent, and the pinned-origin
/// gates already exclude any `&mut`/raw alias of the origin.
pub(super) fn discriminant_src_is_pinned_origin(
    func: &VerifiableFunction,
    src: &Place,
    origin: usize,
) -> bool {
    if src.local == origin && src.projections.is_empty() {
        return true;
    }
    // SOUNDNESS (aliased reseat, audit r5): use the PARAM-refined pin (not raw
    // `place_source_is_stable`) — a reference PARAMETER reseated once in the body
    // (`_3 = &a` on one branch) is "stable" by the raw check but its `*_3` at the
    // read denotes the ENTRY pointee on the other branch, not `a`. The legit
    // compiler-temp shape (`_b = &origin; discr(*_b)`) has `_b` a non-param, so
    // the wrapper is identical there and nothing regresses.
    matches!(src.projections.as_slice(), [trust_types::Projection::Deref])
        // PERF-COMPILER-VCGEN-585: parameters never have `unique_value_def == Some(..)`.
        && !crate::local_defs::is_parameter(func, src.local)
        && unwrap_receiver_local_is_pinned(func, src.local)
        && matches!(
            crate::local_defs::unique_value_def(func, src.local),
            Some(Rvalue::Ref { mutable: false, place })
                if place.local == origin && place.projections.is_empty()
        )
}

/// The SMT term denoting the pinned receiver's discriminant tag at the call.
/// Two recognized pinning shapes, mirroring the ny-cert instances:
///   (b) CONSTRUCTION-pinned: the origin's unique whole-local def is an ADT
///       aggregate (`let x = Ok(v); … x.unwrap()`). The tag is the GROUND
///       constant of that variant — identical on EVERY execution of the single
///       def (loops included: re-executing `x = Ok(v)` never changes the tag),
///       so the term is exact, not merely path-pinned.
///   (a) READ-pinned: a discriminant read `_d = Discriminant(origin)` (directly
///       or through a single-def shared borrow) whose dest `_d` is a bare,
///       non-parameter, pinned local with EXACTLY that read as its one
///       definition. The term is `_d`'s variable: a dominating `match`/`if`
///       switch guard pins it (`_d == OK_TAG`) on every guarded path, and the
///       S2c version machinery keeps a multi-write `_d` name-disjoint
///       (fail-closed) instead of stale.
/// `None` (fail-closed) when neither shape applies.
pub(super) fn unwrap_receiver_tag_term(
    func: &VerifiableFunction,
    origin: usize,
    variants: &[trust_types::VariantDef],
) -> Option<Formula> {
    if !crate::local_defs::is_parameter(func, origin)
        && let Some(Rvalue::Aggregate(kind, _)) = crate::local_defs::unique_value_def(func, origin)
        && let AggregateKind::Adt { variant, active_field: None, .. } = kind
    {
        let tag = variants.get(*variant)?.discriminant;
        return Some(Formula::Int(tag));
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            // `_d` itself must be single-valued: a bare non-param local whose ONE
            // whole-local definition is exactly this read (a second write would
            // leave the term stale vs. the tag; `unique_value_def` returns
            // `None` on any second def, so the `Discriminant` match below implies
            // THIS statement is the sole def).
            // PERF-COMPILER-VCGEN-730: reject projected or parameter `dest` in O(1)
            // before calling `discriminant_src_is_pinned_origin`.
            if !dest.projections.is_empty()
                || (1..=func.body.arg_count).contains(&dest.local)
                || !discriminant_src_is_pinned_origin(func, src, origin)
                || !matches!(
                    crate::local_defs::unique_value_def(func, dest.local),
                    Some(Rvalue::Discriminant(_))
                )
                || !crate::place_source_is_stable(func, dest.local)
            {
                continue;
            }
            return Some(Formula::Var(place_to_var_name(func, dest), Sort::Int));
        }
    }
    None
}

/// Trust (unwrap panic-freedom, dominated-safe): the SOLVABLE refutation body
/// for a std `Option`/`Result` `unwrap`-family call whose receiver's
/// discriminant is PINNED by real dataflow — `receiver_tag == PANIC_TAG` in the
/// same "SAT ⇒ violation / UNSAT ⇒ proved" convention as the UnboundedAllocation
/// lane. `None` (⇒ keep the fail-closed `Call::…::panic-freedom-unverified`
/// UnsupportedMir row) for EVERY case outside the recognized shape:
///   * a non-std callee path (user extension-trait `unwrap`),
///   * a projected / non-place receiver,
///   * a receiver type that is not the MODELED flattened std enum from
///     `lower_enum_adt` (std def-path name + explicit `__tag` slot + both
///     variant defs with their real discriminant tags),
///   * an unpinned receiver (reassigned, `&mut`-borrowed, `SetDiscriminant`,
///     projected store, `mut` parameter with a body store),
///   * no recognizable tag pinning (neither construction- nor read-pinned).
/// SOUNDNESS: the body may only UNDER-constrain (a free tag var is trivially
/// SAT ⇒ the row FAILS closed); the conjoined context (block defs, path guards,
/// preconditions, discriminant range facts) consists exclusively of the same
/// unconditionally-true facts every other v2 lane threads.
pub(crate) fn unwrap_panic_freedom_body(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> Option<Formula> {
    let (enum_paths, variant_names, panic_variant) = std_unwrap_family_panic_variant(callee)?;
    let (Operand::Copy(recv) | Operand::Move(recv)) = args.first()? else {
        return None;
    };
    // Whole-LOCAL receiver first (the bare-enum-local shapes a–d); then the
    // FIELD receiver path (`x.slot.unwrap()`), which the whole-local path
    // fails closed on.
    unwrap_whole_local_tag_refutation(func, recv, enum_paths, variant_names, panic_variant)
        .or_else(|| unwrap_field_tag_refutation(func, recv, enum_paths, panic_variant))
}

/// Whole-LOCAL receiver refutation (shapes a–d): the receiver is a bare enum
/// local. Fail-closed on a projected/field receiver — see
/// [`unwrap_field_tag_refutation`].
pub(super) fn unwrap_whole_local_tag_refutation(
    func: &VerifiableFunction,
    recv: &Place,
    enum_paths: &'static [&'static str],
    variant_names: &'static [&'static str],
    panic_variant: &'static str,
) -> Option<Formula> {
    // Receiver: a bare local. Projections are not traced — fail closed.
    if !recv.projections.is_empty() {
        return None;
    }
    // Receiver type: the MODELED flattened std enum (`lower_enum_adt` shape —
    // the shared `modeled_std_enum_shape` gate), additionally anchored to the
    // callee flavor's def-paths (an Option method never models a Result
    // receiver and vice versa).
    let ty = crate::local_ty_ref(func, recv.local)?;
    let (name, variants) = modeled_std_enum_shape(ty)?;
    debug_assert!(variant_names.iter().all(|v| variants.iter().any(|vd| vd.name == *v)));
    if !enum_paths.contains(&name) {
        return None;
    }
    let panic_tag = variants.iter().find(|vd| vd.name == panic_variant)?.discriminant;
    // Tag-transparent: `o.as_ref().unwrap()` unwraps the as_ref RESULT, whose
    // discriminant equals `o`'s — resolve through the hop so the obligation
    // tests the guard-connected origin tag.
    let origin = unwrap_tag_origin(func, recv.local)?;
    if let Some(tag_term) = unwrap_receiver_tag_term(func, origin, variants) {
        return Some(Formula::Eq(Box::new(tag_term), Box::new(Formula::Int(panic_tag))));
    }
    // (c) SUMMARY-pinned: the pinned origin's unique def is a Call to a LOCAL
    // callee with a return-discriminant summary (`compute_return_disc_summaries`,
    // threaded per crate like the const-return bounds). The refutation body
    // becomes `tag_expr(actual args) == PANIC_TAG` — ground for constant
    // arguments (`Rat::new(1, 2).unwrap()` proves outright); for pinned
    // symbolic arguments the VC keeps the caller's context, so a dominating
    // `if d != 0` guard proves it and an unguarded call stays SAT (failed).
    // (Falls through on any miss so shape (d) below can still fire.)
    if let Some((call_callee, call_args, reaches_body)) = unwrap_origin_call_def(func, origin)
        && reaches_body
        && let Some(summary) = crate::callee_return_disc_summary(call_callee)
        && summary.enum_name == name
        && let Some(tag_expr) = return_disc_tag_expr(func, &summary, call_args)
    {
        return Some(Formula::Eq(Box::new(tag_expr), Box::new(Formula::Int(panic_tag))));
    }
    // (d) PARAM-pinned fallback: the origin is a pinned PARAMETER (a `mut` param
    // with a body store was already rejected by `unwrap_receiver_local_is_pinned`
    // inside `unwrap_receiver_origin`), and the body contains NO other channel
    // that could observe its tag (`origin_tag_observed_elsewhere` — a
    // discriminant read, a copy that is matched on, or ANY call receiving the
    // origin / a borrow of it, all of which could dominate the unwrap with a
    // guard this lane cannot see). With no observer, the tag is a FREE entry
    // value: SAT with model `tag == PANIC_TAG` is a GENUINE `None`/`Err`
    // argument reaching the unwrap — a real refutation with a real witness, not
    // a coverage gap. This is what turns the bare `f(o: Option<u32>) ->
    // { o.unwrap() }` from a fail-closed UNKNOWN into FAILED(o = None).
    // SOUNDNESS: under-constraining only (a free tag is trivially SAT ⇒ fails
    // closed); the observer gate exists for PRECISION (never mint a spurious
    // ground counterexample on a guarded-but-unrecognized shape — those keep
    // today's fail-closed UnsupportedMir row).
    // (e) CALL-pinned (2026-10-03, unwrap-from-facts): the pinned origin's one
    // definition is an opaque CALL (`let r = x.ok_or(e); if r.is_ok() {
    // r.unwrap() }`). Pinned means that call is its only write and nothing can
    // re-point or mutate it, so the tag is a single unknown value from the
    // return on: the same free tag variable a parameter gets, cited by the
    // probe/eq channels through `receiver_tag_term_any`. The same observer gate
    // as (d). A loop that re-runs the call kills every fact over the old value
    // (the terminator kill of the path-definition fixpoint covers `origin.*`).
    if ((1..=func.body.arg_count).contains(&origin) || call_pinned_origin(func, origin))
        && let Some(tag_var) = receiver_entry_tag_var(func, origin)
        && !origin_tag_observed_elsewhere(func, origin)
    {
        return Some(Formula::Eq(Box::new(tag_var), Box::new(Formula::Int(panic_tag))));
    }
    None
}

/// Trust (2026-10-03, unwrap-from-facts): shape (e)'s gate — a pinned,
/// NON-parameter origin whose one definition is a normally-returning call with
/// the origin as its bare destination. A std `as_ref` call is excluded: its
/// result's tag IS its receiver's, so a free variable would cut the link to a
/// guard on the receiver; the subject lane (`as_ref_result_subject`) and the
/// whole-local hop (`unwrap_tag_origin`) own that shape.
pub(super) fn call_pinned_origin(func: &VerifiableFunction, origin: usize) -> bool {
    !(1..=func.body.arg_count).contains(&origin)
        && origin != 0
        // PERF-COMPILER-VCGEN-585: `unwrap_origin_call_def` requires a bare-dest Call
        // terminator; reject bodies without one in O(1) via `terminator_presence_for(func)`.
        && super::terminator_presence_for(func).has_bare_dest_call
        && crate::local_defs::unique_value_def(func, origin).is_none()
        && unwrap_origin_call_def(func, origin)
            .is_some_and(|(callee, _, _)| !std_as_ref_call(callee))
        && unwrap_receiver_local_is_pinned(func, origin)
}

/// FIELD receiver refutation: `x.slot.unwrap()` where `slot` is a modeled-enum
/// field of a PINNED param base. Mints the tag term over the field place — the
/// SAME var an inferred field-guard contract (`if x.is_ready() { … }`,
/// `pred_field`) cites — so a dominating field guard proves the unwrap and an
/// unguarded field unwrap refutes with a field-`None`/`Err` witness. The field
/// path is the exact analogue of the whole-local shape (d): free entry tag,
/// fires-only observer gate. Fail-closed on any deviation.
pub(super) fn unwrap_field_tag_refutation(
    func: &VerifiableFunction,
    recv: &Place,
    enum_paths: &'static [&'static str],
    panic_variant: &'static str,
) -> Option<Formula> {
    let field_place = unwrap_field_place(func, recv)?;
    if !field_subject_is_pinned(func, &field_place) {
        return None;
    }
    let field_ty = crate::place_ty_cow(func, &field_place)?;
    let (name, variants) = modeled_std_enum_shape(field_ty.as_ref())?;
    if !enum_paths.contains(&name) {
        return None;
    }
    let panic_tag = variants.iter().find(|vd| vd.name == panic_variant)?.discriminant;
    let tag_var = subject_tag_term(func, &field_place)?;
    // Fires-only: with NO OPAQUE observer of the field the tag is a free entry
    // value ⇒ refute. A CONNECTED field guard is exempt (shape (d) still fires,
    // and its threaded fact discharges the obligation).
    if field_tag_observed_elsewhere(func, &field_place) {
        return None;
    }
    Some(Formula::Eq(Box::new(tag_var), Box::new(Formula::Int(panic_tag))))
}

/// The FIELD place an unwrap receiver consumes: the receiver is the projected
/// field operand directly (`recv` = `(*base).field`), or a bare temp whose
/// unique def copies from such a field place. Restricted to a SIMPLE field of
/// the param pointee — `[Field]` (by-value base) or `[Deref, Field]` (`&Struct`
/// base) — or, since 2026-10-03, the whole pointee `[Deref]` (`&Enum` base) and
/// the result of a std `as_ref` over one of these
/// ([`as_ref_result_subject`]), so the base local is exactly
/// `field_place.local` and its stability is decidable. Fail-closed otherwise.
pub(super) fn unwrap_field_place(func: &VerifiableFunction, recv: &Place) -> Option<Place> {
    // Trust (2026-10-03, unwrap-from-facts): `[Deref]` too — the whole pointee
    // of a shared `&Enum` parameter (`x.unwrap()` for `x: &Option<u32>` copies
    // `*x`), decided by the same `field_subject_is_pinned`.
    let is_simple_field = is_pinnable_subject_projection;
    if is_simple_field(&recv.projections) {
        return Some(recv.clone());
    }
    // Bare temp copied from a field place. SOUNDNESS (aliased reseat, audit r3):
    // the temp must be PINNED before its copy def is trusted — a `&mut`-reseated
    // temp (`_t = copy((*x).f); m = &mut _t; *m = None; _t.unwrap()`) has a stale
    // `Use(Copy((*x).f))` def while the unwrap operates on the mutated value, so
    // a guard on `(*x).f` would falsely discharge it. Fail-closed on an unpinned
    // temp (mirrors `guard_receiver_subject` / `unwrap_receiver_origin`).
    // PERF-COMPILER-VCGEN-585: both bare-temp arms below require a non-parameter
    // `recv.local` (`unique_value_def` and `as_ref_result_subject` are always `None`
    // for parameters).
    if recv.projections.is_empty() && !crate::local_defs::is_parameter(func, recv.local) {
        if let Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) =
            crate::local_defs::unique_value_def(func, recv.local)
            && is_simple_field(&p.projections)
            && unwrap_receiver_local_is_pinned(func, recv.local)
        {
            return Some(p.clone());
        }
        // Trust (2026-10-03, unwrap-from-facts): the receiver is the result of a
        // std `as_ref` over a subject, used only by unwrap-family calls.
        return as_ref_result_subject(func, recv.local);
    }
    None
}

/// FIELD observer gate (the whole-local [`origin_tag_observed_elsewhere`]
/// analogue): does the body contain an OPAQUE channel through which the field's
/// discriminant could be observed and guarded — a `Discriminant` read touching
/// the base, or ANY non-unwrap call receiving the base struct / a borrow or
/// copy of it (all of which could read the field and dominate the unwrap with a
/// guard this lane cannot see)? A CONNECTED field guard
/// ([`inferred_pred_call_connects_field`]) is exempt. Conservative (broad) so a
/// missed observer can only SUPPRESS a refutation (fail-closed), never mint a
/// spurious one.
pub(super) fn field_tag_observed_elsewhere(func: &VerifiableFunction, field_place: &Place) -> bool {
    let base = field_place.local;
    let touches_base = |place: &Place| -> bool {
        if place.local == base {
            return true;
        }
        // PERF-COMPILER-VCGEN-729: parameters != `base` have `unique_value_def == None`
        // and `unwrap_receiver_origin` at most `Some(place.local) != Some(base)`. For
        // non-parameters, inspect `unique_value_def(func, place.local)` once.
        if crate::local_defs::is_parameter(func, place.local) {
            return false;
        }
        match crate::local_defs::unique_value_def(func, place.local) {
            // A borrow whose referent roots at the base.
            Some(Rvalue::Ref { place: r, .. }) => {
                r.local == base || unwrap_receiver_origin(func, r.local) == Some(base)
            }
            // A MULTI-HOP copy/move alias of the base — matches the whole-local
            // twin's `unwrap_tag_origin` reach (a one-hop check would let a 2-hop
            // `_a = copy base; _b = copy _a; observe(_b)` slip past the gate and
            // spuriously refute a possibly-guarded field unwrap).
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != place.local =>
            {
                unwrap_receiver_origin(func, place.local) == Some(base)
            }
            _ => false,
        }
    };
    // Trust (2026-10-03, unwrap-from-facts): the read [`subject_tag_term`]
    // chose IS the term, so it is a connected observer; any other read is not.
    let mut pinning_read: Option<Option<Place>> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
                && touches_base(src)
                && !(src == field_place
                    && pinning_read
                        .get_or_insert_with(|| subject_read_pinned_dest(func, field_place))
                        .as_ref()
                        == Some(dest))
            {
                return true;
            }
        }
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && std_unwrap_family_panic_variant(callee).is_none()
            && args.iter().any(|arg| {
                matches!(arg, Operand::Copy(place) | Operand::Move(place) if touches_base(place))
            })
            // A std `as_ref` view of THIS subject whose result only unwraps.
            && !(std_as_ref_call(callee)
                && dest.projections.is_empty()
                && as_ref_result_subject(func, dest.local).as_ref() == Some(field_place))
            // A modeled std probe of THIS subject (fires-only, place-equal).
            && !matches!(probe_subject_model(func, block), Some((p, _)) if &p == field_place)
            && !inferred_pred_call_connects_field(func, block, field_place)
        {
            return true;
        }
    }
    false
}

/// Trust (unwrap panic-freedom, shape (d)): the SMT variable denoting a pinned
/// PARAMETER receiver's discriminant tag at function entry — the explicit
/// `__tag`/`discriminant` field of the flattened std-enum layout, named exactly
/// as `set_discriminant_definitions` / the aggregate-field lane write it, so a
/// (rare) explicit tag consumer cites the same term. Fail-closed (`None`) when
/// the layout carries no Int tag field (e.g. a bool-tag or niche layout).
pub(super) fn receiver_entry_tag_var(func: &VerifiableFunction, origin: usize) -> Option<Formula> {
    let bare = Place::local(origin);
    let explicit = crate::explicit_discriminant_field_for_place(func, &bare).ok()?;
    if !matches!(explicit.ty, Ty::Int { .. }) {
        return None;
    }
    Some(Formula::Var(place_to_var_name(func, &explicit.place), Sort::Int))
}

/// Trust (unwrap panic-freedom, shape (d) observer gate): does the body contain
/// ANY channel other than the unwrap-family calls themselves through which the
/// pinned parameter `origin`'s discriminant could be observed — and therefore a
/// guard this lane cannot connect to the free entry-tag variable?
///   * a `Discriminant` read of the origin (direct, through a single-def shared
///     borrow, or of a pinned COPY of the origin — `let c = o; match c { … }`);
///   * ANY call receiving the origin, a shared borrow of it, or a pinned copy
///     of it as an argument (an `is_some`-style probe, a `PartialEq` against
///     `None`, an `as_ref` chain, a user helper — all could return tag
///     information that dominates the unwrap).
/// `true` ⇒ the caller keeps today's fail-closed UnsupportedMir row instead of
/// minting a possibly-spurious refutation. Unwrap-family calls are exempt: they
/// CONSUME the tag (their own VCs refute or prove per-site) and never produce a
/// guard value.
pub(super) fn origin_tag_observed_elsewhere(func: &VerifiableFunction, origin: usize) -> bool {
    let is_origin_alias = |place: &Place| -> bool {
        if !place.projections.is_empty() {
            return false;
        }
        if place.local == origin {
            return true;
        }
        // A pinned copy of the origin (`let c = o;`), a tag-transparent
        // `as_ref` RESULT of it, or a single-def shared borrow of it (or of a
        // tag-transparent-connected local — `_e = &(o.as_ref())`) — all carry
        // the same tag onward, so an unmodeled consumer of any of them is an
        // opaque guard channel. Following the referent through `unwrap_tag_origin`
        // closes the as_ref-then-shared-borrow leak (a borrow of the as_ref
        // RESULT is a real observer the literal `referent.local == origin` check
        // missed).
        //
        // A DECLINE FROM THE RESOLVER ANSWERS YES HERE, NOT NO. This gate asks
        // "could this place carry the origin's tag to a consumer this lane cannot
        // model?", so the safe answer when the seam cannot say what the place holds
        // is that it could: reading a decline as "not an alias" would drop the
        // observer and mint a refutation over a tag the guard may have pinned. The
        // last disjunct is that reading — a local that is BOTH unpinned and
        // unresolvable — so a pinned local with an ordinary opaque def (a call dest)
        // is not swept in. `whole_pointee_guard_through_reseat_does_not_connect` is
        // the row.
        //
        // THE ALIAS SHAPE (`_b = &o; _m = &mut _b; *_m = &o2; check(_b)`) DOES NOT
        // REACH THAT DISJUNCT, because `local_defs::unique_value_def` does not
        // decline on a `&mut` escape — the seam's open defect, stated in its `Escape`
        // arm. Here it happens not to matter: `_b`'s stale def is still `&o`, so the
        // middle disjunct connects the observer anyway. It is not a general argument,
        // and it stops being needed when that defect is repaired.
        //
        // PERF-COMPILER-VCGEN-729: for a parameter != `origin`, `unique_value_def` is
        // `None` and `unwrap_tag_origin` is at most `Some(place.local) != Some(origin)`,
        // so the three disjuncts reduce to `!unwrap_receiver_local_is_pinned(place.local)`.
        // For a non-parameter, query `unique_value_def(func, place.local)` once instead
        // of up to three times.
        if crate::local_defs::is_parameter(func, place.local) {
            return !unwrap_receiver_local_is_pinned(func, place.local);
        }
        match crate::local_defs::unique_value_def(func, place.local) {
            Some(Rvalue::Ref { mutable: false, place: referent }) => {
                referent.projections.is_empty()
                    && (referent.local == origin
                        || unwrap_tag_origin(func, referent.local) == Some(origin))
            }
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != place.local =>
            {
                unwrap_tag_origin(func, place.local) == Some(origin)
            }
            Some(_) => false,
            None => {
                !unwrap_receiver_local_is_pinned(func, place.local)
                    || (super::terminator_presence_for(func).has_bare_dest_call
                        && unwrap_tag_origin(func, place.local) == Some(origin))
            }
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Discriminant(src), .. } = stmt
                && (discriminant_src_is_pinned_origin(func, src, origin) || is_origin_alias(src))
            {
                return true;
            }
        }
        if let Terminator::Call { func: callee, args, .. } = &block.terminator
            && std_unwrap_family_panic_variant(callee).is_none()
            && args.iter().any(|arg| {
                matches!(arg, Operand::Copy(place) | Operand::Move(place) if is_origin_alias(place))
            })
            // A tag-transparent `as_ref` whose result CONNECTS back to this
            // origin (`unwrap_tag_origin(dest) == origin` — the exact hop the
            // probe/unwrap models resolve) is a CONNECTED observer, not an
            // opaque one: every downstream consumer of its result is itself
            // alias-tracked by `is_origin_alias`, so a dangerous consumer still
            // trips this gate. An as_ref whose hop does NOT connect (e.g. a
            // reassigned dest) stays an opaque observer — fires-only, never a
            // blanket name exemption (a blanket exemption would let shape (d)
            // mint a spurious refutation for a guarded-but-unconnected chain).
            && !as_ref_hop_connected(func, block, origin)
            // A MODELED probe call (`is_some`-family whose result semantics
            // `probe_call_definitions` records over the SHARED tag term) is a
            // CONNECTED observer, not an opaque one: its guard constrains the
            // same free entry-tag variable shape (d) cites, so a dominating
            // `if o.is_some()` proves the unwrap and an unguarded one still
            // refutes. An UNmodeled probe (failed gates) stays an opaque
            // observer and keeps the fail-closed row.
            && probe_call_definitions(func, block).is_empty()
            // Same fires-only contract for a MODELED `o == None` / `o != None`
            // equality guard; `o == Some(x)` / `o == p` never model and stay
            // opaque observers.
            && eq_unit_call_definitions(func, block).is_empty()
            // And for a guard-helper call with an INFERRED contract — fires-only
            // AND origin-equal, so a summarized call constraining THIS origin's
            // tag is connected, while the same callee taking an unrelated
            // Option (or failing any gate) stays an opaque observer.
            && !inferred_pred_call_connects(func, block, origin)
        {
            return true;
        }
    }
    false
}

/// The unique `Call` that defines the PINNED unwrap-receiver origin (bare
/// dest, normally returning). Pinnedness (`unwrap_receiver_origin`'s
/// `place_source_is_stable` chain) already guarantees AT MOST one whole-local
/// store of the origin across statements AND call dests, so the first match is
/// THE defining call on every execution that reaches the unwrap.
pub(super) fn unwrap_origin_call_def<'a>(
    func: &'a VerifiableFunction,
    origin: usize,
) -> Option<(&'a str, &'a [Operand], bool)> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    crate::find_local_write_term(func, &func.body.blocks, origin, |_block, term| {
        if let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = term
            && dest.local == origin
            && dest.projections.is_empty()
        {
            // The third component: whether this call reaches the summarized body
            // (`crate::call_reaches_summarized_body`), which a body-derived summary needs.
            return Some((
                callee.as_str(),
                args.as_slice(),
                crate::call_reaches_summarized_body(term),
            ));
        }
        None
    })
}

/// Trust (return-discriminant summary, use site): the summarized callee's
/// returned TAG as a term over THIS call's actual arguments.
///   * Unconditional: the ground variant tag (argument-independent).
///   * Guard-conditioned: `ite(cond[formals := actuals], then_tag, else_tag)`,
///     via the capture-avoiding [`substitute_summary_params`]. Every actual
///     must itself resolve through [`entry_stable_operand_formula`] (a
///     constant, or a pinned caller parameter/const-defined local): the
///     substituted term must still denote the CALL-TIME argument value at the
///     downstream unwrap block, and a reassignable actual could go stale in
///     between (the S2c class) — refused, fail-closed. Arity and
///     free-vars ⊆ formals are re-checked so a malformed summary can never
///     leave an unbound callee symbol to capture a caller local.
pub(super) fn return_disc_tag_expr(
    func: &VerifiableFunction,
    summary: &ReturnDiscSummary,
    args: &[Operand],
) -> Option<Formula> {
    match &summary.cases {
        ReturnDiscCases::Unconditional { tag } => Some(Formula::Int(*tag)),
        ReturnDiscCases::GuardConditioned { cond, then_tag, else_tag } => {
            if summary.params.len() != args.len()
                || !trust_types::all_free_variable_names(cond, &mut |v| {
                    summary.params.iter().any(|p| p == v)
                })
            {
                return None;
            }
            let mut replacements: Vec<(String, Formula)> = Vec::with_capacity(args.len());
            for (formal, actual) in summary.params.iter().zip(args) {
                replacements.push((formal.clone(), entry_stable_operand_formula(func, actual)?));
            }
            let cond = substitute_summary_params(cond, &replacements);
            Some(Formula::Ite(
                Box::new(cond),
                Box::new(Formula::Int(*then_tag)),
                Box::new(Formula::Int(*else_tag)),
            ))
        }
    }
}

/// Shared bridge for [`collect_terminator_unsupported`] and the dominated-success
/// recognizer, so every known-panicking call keeps exactly one obligation.
pub(super) fn unwrap_panic_freedom_modeled(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
) -> bool {
    unwrap_panic_freedom_body(func, callee, args).is_some()
}

/// Trust (unwrap panic-freedom, dominated-safe): one solvable VC per recognized
/// `unwrap`/`expect` call, replacing that call's fail-closed
/// `Call::…::panic-freedom-unverified` UnsupportedMir row (the suppression in
/// [`collect_terminator_unsupported`] keys on the SAME
/// [`unwrap_panic_freedom_body`] recognizer, so the two can never drift — every
/// call gets exactly one of {solvable VC, UnsupportedMir row}).
///
/// The body `receiver_tag == PANIC_TAG` is conjoined with the SAME discharge
/// context the UnboundedAllocation lane assembles — same-block defs, live
/// path-definition facts, arg/local/datatype type ranges, versioned
/// preconditions, dominating path guards (S2c-exempt), assert-passed semantic
/// guards, global invariant facts (which carry the discriminant variant-range
/// and CSE facts), and the final SSA version-token collapse. Verdict
/// convention: SAT ⇒ the panic variant's tag is reachable at the call ⇒ the row
/// stays failed; UNSAT ⇒ the discriminant is pinned to the success variant on
/// every path ⇒ panic-freedom PROVED.
pub(super) fn unwrap_panic_freedom_vcs_with_blocks(
    func: &VerifiableFunction,
) -> Vec<(BlockId, VerificationCondition)> {
    if func.body.blocks.is_empty() || !super::terminator_presence_for(func).has_call {
        return Vec::new();
    }
    // Trust (slice ARM 2): the trailing `Option<(Formula, u32)>` carries the abs
    // receiver as SUBJECT and its `int_width()` as WIDTH — the payload the
    // authenticated-obligation recorder cross-checks against MIR. `None` for the
    // unwrap family (payload-free panic-freedom, not in the slice).
    #[allow(clippy::type_complexity)]
    let mut sites: Vec<(
        &trust_types::BasicBlock,
        &str,
        &SourceSpan,
        Formula,
        Option<VcKind>,
        Option<(Formula, u32)>,
    )> = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, target, span, .. } = &block.terminator
        else {
            continue;
        };
        // A normally-returning known-panicking std call. Two independent sources:
        //   * Option/Result unwrap-family (`is_known_panicking_method`), unless the
        //     slice->array recognizer already proved it infallible (row suppressed);
        //   * signed `iN::abs` (`is_signed_abs_mint`) — panics at `iN::MIN`, never
        //     flagged by the UnsupportedMir arm, so it is added ONLY here (no
        //     double-flag). Both flow through the SAME guard-aware assembly below,
        //     so a dominating guard proves the obligation and an unguarded call
        //     stays refutable.
        if target.is_none() {
            continue;
        }
        // `(body, kind_override)`: abs carries an explicit `NegationOverflow { ty }`
        // kind (routes like `-x`, BV-capable discharge); unwrap uses the default
        // `Assertion` panic-freedom kind computed at the tail (`None`).
        let (body, kind_override, subj_width): (
            Option<Formula>,
            Option<VcKind>,
            Option<(Formula, u32)>,
        ) = if is_signed_abs_mint(callee) {
            match signed_abs_panic_body(func, callee, args, dest) {
                Some(SignedAbsRow::Modeled(body, ty)) => {
                    // Seed SUBJECT = the abs receiver, WIDTH = the width the row is
                    // built at (the owner's, ABS-LIT-WIDTH-1), at the point the
                    // emitter KNOWS them (before `ty` is moved into the kind). `None`
                    // if either is unavailable → no obligation.
                    let width = ty.int_width();
                    let subject = args.first().map(|a| operand_to_formula(func, a));
                    let sw = match (subject, width) {
                        (Some(s), Some(w)) => Some((s, w)),
                        _ => None,
                    };
                    (Some(body), Some(VcKind::NegationOverflow { ty }), sw)
                }
                // Trust (ABS-LIT-WIDTH-1): an `isize` receiver whose width nothing
                // fixes. The `UnsupportedMir` kind rides through `sites` and is
                // pushed as-is below, with no guard assembly.
                Some(SignedAbsRow::Refused(formula, kind)) => (Some(formula), Some(kind), None),
                None => (None, None, None),
            }
        } else if is_known_panicking_method(callee)
                && !unwrap_is_infallible_slice_to_array(func, callee, args, dest)
                // Trust (countdown-loop piece, B0): const-int conversion `expect`s
                // that provably succeed carry no panic path — no VC (see the
                // UnsupportedMir twin's suppression for the rationale).
                && expect_infallible_const_int_conversion(func, callee, args, dest).is_none()
        {
            (unwrap_panic_freedom_body(func, callee, args), None, None)
        } else {
            (None, None, None)
        };
        let Some(body) = body else {
            continue;
        };
        sites.push((block, callee, span, body, kind_override, subj_width));
    }
    if sites.is_empty() {
        return Vec::new();
    }
    let fn_sym: trust_types::Symbol = func.name.as_str().into();
    if sites.iter().all(|(_, _, _, _, kind_override, _)| {
        matches!(kind_override, Some(VcKind::UnsupportedMir { .. }))
    }) {
        return sites
            .into_iter()
            .filter_map(|(block, _, span, body, kind_override, _)| {
                let Some(kind @ VcKind::UnsupportedMir { .. }) = kind_override else {
                    return None;
                };
                Some((
                    block.id,
                    VerificationCondition {
                        kind,
                        function: fn_sym,
                        location: span.clone(),
                        formula: body,
                        contract_metadata: None,
                        obligation: None,
                    },
                ))
            })
            .collect();
    }
    let guard_paths_map = super::guard_map_for(func);
    let semantic_guards = super::semantic_guard_map_for(func, None);
    // (No per-block may-reassigned KILL set: `conjoin_preconditions_versioned_recorded`
    // ignores it — the version rename kills staleness — and materialising it was a
    // Θ(blocks × names) whole-CFG fixpoint.)
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = super::stmt_versions_for(func);
    let path_definition_map = super::path_definition_map_for(func);
    // Each row takes the set less the element-read congruences it cannot use
    // (`RowGlobalFacts::for_row`).
    let global_facts = build_global_invariant_facts(func);
    let filtered_preconditions: Vec<Formula> = if func.preconditions.is_empty() {
        Vec::new()
    } else {
        func.preconditions
            .iter()
            .filter(|pre| !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre))
            .cloned()
            .collect()
    };
    let mut vcs = Vec::new();
    for (block, callee, span, body, kind_override, subj_width) in sites {
        // Trust (ABS-LIT-WIDTH-1): a refused `abs` row is a fail-closed
        // `UnsupportedMir` row. It takes no facts and records no obligation, the
        // same as `numeric_panic`'s refusals in `safety.rs`.
        if let Some(kind @ VcKind::UnsupportedMir { .. }) = kind_override {
            vcs.push((
                block.id,
                VerificationCondition {
                    kind,
                    function: fn_sym,
                    location: span.clone(),
                    formula: body,
                    contract_metadata: None,
                    obligation: None,
                },
            ));
            continue;
        }
        let m = method_tail(callee);
        // Trust (2026-10-03, unwrap-from-facts): the message comes from
        // `trust_types::l0_refutation`, whose classifier publishes an UNPROVED
        // instance of it `failed` — the mint and the classifier share one table.
        // `sites` holds only `is_known_panicking_method` calls, whose tail is one
        // of the four the table names; anything else keeps the old spelling and
        // is (deliberately) not classified.
        let kind = kind_override.unwrap_or_else(|| VcKind::Assertion {
            message: trust_types::l0_refutation::unwrap_family_panic_freedom_message(m)
                .map_or_else(|| format!("Call::{m}::panic-freedom"), str::to_string),
        });

        // Step 1 (block-defs): record the terminal-versioned body + kept defs so the
        // obligation reconstructs. Seed the record ONLY for the slice kind (abs →
        // NegationOverflow, carrying SUBJECT/WIDTH); the unwrap family stays None.
        let (formula0, obligation) = if matches!(kind, VcKind::NegationOverflow { .. }) {
            let (formula0, ob_body, kept) =
                v2_formula_with_block_defs_at_point_recorded(func, block, block.stmts.len(), body);
            // Trust (slice ARM 2, abs lane — ATOMIC-CORE recording, 2026-07-31).
            // `ob_body` is the renamed composite `And([range_r, Eq_r])`
            // (`signed_abs_panic_body` builds the raw as `And([input_range,
            // Eq(v, MIN)])`, renamed STRUCTURALLY by the block-def recorder). The
            // consumer's negation `is_core` accepts ONLY the ATOMIC `Eq(v, MIN)`, so
            // seed the record with that atom as `body` and demote the input-range
            // constraint to a `ConjoinFactsLast` FACT — exactly as the raw-`Neg`
            // path in `checked_vcs.rs` does. Two seed wrappers reconstruct `formula0`
            // BIT-FOR-BIT: the INNER conjoins the range onto the atom
            // (→ `And([range_r, Eq_r])`), the OUTER conjoins the kept block-defs
            // around it (→ `And([kept.., And([range_r, Eq_r])])`, the combine's
            // nesting — it pushes the whole body `And` as one conjunct). The
            // downstream `ob_record_*` mirror helpers then wrap this atomic body
            // identically to the composite it replaced (both `version_rename_at` and
            // `normalize_ssa_version_tokens` are per-variable maps that distribute
            // over `And`), so the fully-assembled record still reconstructs to
            // `vc.formula`. `formula0` — what the lane VERIFIES — is UNCHANGED.
            let obligation = subj_width.and_then(|(subject, width)| {
                let Formula::And(mut cs) = ob_body else { return None };
                let atomic_core = (cs.len() == 2).then(|| cs.pop()).flatten()?;
                let mut wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: cs }];
                if !kept.is_empty() {
                    wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
                }
                Some(ObligationRecord {
                    body: atomic_core,
                    wrappers,
                    subject: Some(subject),
                    width: Some(width),
                })
            });
            (formula0, obligation)
        } else {
            (v2_formula_with_block_defs_at_point(func, block, block.stmts.len(), body), None)
        };
        let mut vc = VerificationCondition {
            kind,
            function: fn_sym,
            location: span.clone(),
            formula: formula0,
            contract_metadata: None,
            obligation,
        };

        // Live path-definition facts (the safety-lane channel): predecessor
        // definitions that made the path reachable (e.g. the bool `is_ok` temp).
        if let Some(path_defs) = path_definition_map.get(&block.id)
            && !path_defs.is_empty()
        {
            let live = v2_live_path_defs(func, block, path_defs);
            if !live.is_empty() {
                ob_record_conjoin(&mut vc, &live);
                let mut conjuncts = live;
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
        }
        {
            let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
            let mut ob = vc.obligation.as_mut();
            vc.formula =
                conjoin_arg_local_field_type_ranges_recorded(func, formula, &mut |before, after| {
                    if let Some(ob) = ob.as_deref_mut()
                        && let Some(facts) = extract_conjoined_facts(before, after)
                        && !facts.is_empty()
                    {
                        ob.wrappers
                            .push(ObligationWrapper::ConjoinFactsLast { facts: facts.to_vec() });
                    }
                });
        }
        // Trust S2c: whole-VC version rename FIRST; the threaded facts below
        // (path guards, semantic guards, global facts) are conjoined AFTER,
        // EXEMPT from the rename — same discipline as the allocation lane.
        let record_ob = vc.obligation.is_some();
        let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
        let (nf, conjoined) = conjoin_preconditions_versioned_at_point_inner(
            func,
            &sv,
            block.id,
            usize::MAX,
            &filtered_preconditions,
            formula,
            record_ob,
            true,
        );
        vc.formula = nf;
        if record_ob {
            ob_record_rename_at(&mut vc, &sv, func, block.id, block.stmts.len());
            ob_record_conjoin_owned(&mut vc, conjoined);
        }
        if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
            let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
            if vc.obligation.is_some() {
                let (nf, path_terms) = v2_formula_with_path_guards_recorded(
                    func,
                    &sv,
                    block.id,
                    block_guard_paths,
                    formula,
                );
                vc.formula = nf;
                if let Some(ob) = vc.obligation.as_mut() {
                    ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
                }
            } else {
                vc.formula = v2_formula_with_path_guards(
                    func,
                    &sv,
                    block.id,
                    block_guard_paths,
                    formula,
                );
            }
        }
        if let Some(sem_guards) = semantic_guards.get(&block.id)
            && !sem_guards.is_empty()
        {
            ob_record_conjoin(&mut vc, sem_guards);
            let mut conjuncts = Vec::with_capacity(sem_guards.len() + 1);
            conjuncts.extend(sem_guards.iter().cloned());
            conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
            vc.formula = Formula::And(conjuncts);
        }
        // Function-wide invariant facts — notably the discriminant variant-range
        // fact `d ∈ {variant tags}` (a true type invariant: it deletes phantom-tag
        // counterexamples but can never exclude the real panic tag, which is a
        // member of the set — the refutation stays reachable).
        let row_facts = global_facts.for_row(&vc.formula);
        if !row_facts.is_empty() {
            ob_record_conjoin(&mut vc, &row_facts);
            let mut conjuncts = row_facts;
            conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
            vc.formula = Formula::And(conjuncts);
        }
        vc.formula = normalize_ssa_version_tokens_owned(
            func,
            std::mem::replace(&mut vc.formula, Formula::Bool(true)),
        );
        ob_record_normalize(&mut vc, func);
        vcs.push((block.id, vc));
    }
    vcs
}

pub(super) fn generate_unwrap_panic_freedom_vcs(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let cached = super::unwrap_panic_vcs_for(func);
    match std::rc::Rc::try_unwrap(cached) {
        Ok(vec) => vec.into_iter().map(|(_, vc)| vc).collect(),
        Err(rc) => rc.iter().map(|(_, vc)| vc.clone()).collect(),
    }
}

/// Trust (hardened PanicBoundary twin consistency): the fully-assembled
/// panic-freedom refutation formulas for all recognized pinned `unwrap`/`expect`
/// calls in `func`, keyed by block ordinal. The hardened lane swaps its
/// fail-closed `Bool(true)` PanicBoundary twin for this formula so BOTH rows
/// keyed to the same call are decided by the SAME solvable obligation (UNSAT ⇒
/// both prove; SAT ⇒ both stay failed) instead of the twin wedging at Unknown
/// after the primary row proves.
pub(crate) fn unwrap_panic_freedom_formulas_by_block(
    func: &VerifiableFunction,
) -> FxHashMap<usize, Formula> {
    let cached = super::unwrap_panic_vcs_for(func);
    match std::rc::Rc::try_unwrap(cached) {
        Ok(vec) => vec.into_iter().map(|(id, vc)| (id.0, vc.formula)).collect(),
        Err(rc) => rc.iter().map(|(id, vc)| (id.0, vc.formula.clone())).collect(),
    }
}

/// Trust (Problem B): recognize the INFALLIBLE `Result::unwrap` whose receiver is
/// the success-by-construction of a slice -> ARRAY `TryInto`/`TryFrom` conversion
/// on a slice of STATICALLY-KNOWN length `N` equal to the target array length `N`.
/// The standard-library impl `<&[T] as TryFrom<&[T; N]>>` (and the `TryInto`
/// mirror) returns `Ok` IFF `slice.len() == N`; when the slice length is
/// statically `N`, the conversion CANNOT return `Err`, so the `unwrap` CANNOT
/// panic. Returning `true` SUPPRESSES the `Call::unwrap::panic-freedom-unverified`
/// UnsupportedMir obligation for exactly these provably-infallible unwraps.
///
/// SOUNDNESS — the suppression is sound ONLY because every gate below is a HARD
/// requirement; ANY ambiguity returns `false` (keep the obligation as Unknown):
///   * The unwrapped value is a `Result` (`unwrap` on `Result`), so the only
///     panic path is the `Err` arm — there is no `None` arm to reason about.
///   * The receiver `args[0]` is a BARE LOCAL `_r` (no projections): we trace a
///     whole-local value, never a field/element of an aggregate.
///   * `_r` is defined by EXACTLY ONE `Call` terminator (a single, unambiguous
///     def) whose callee is a slice->array `try_into`/`try_from` conversion.
///   * The TARGET array length `N` is read from the conversion's RESULT type — the
///     `[T; N]` inside `Result<[T; N], _>` — and the unwrap's own destination type
///     `[T; N]`; BOTH must agree on `N`. (`array_len_of_result` / `array_len_of`.)
///   * The conversion's slice ARGUMENT has a STATICALLY-KNOWN length that is
///     EXACTLY `N` — established only from a constant `Subslice { from, to,
///     from_end: false }` projection (length `to - from`) or a chain that ends in
///     one. A runtime-variable range (`bytes[len-8..]`, `bytes[off..off+8]`) does
///     NOT lower to a constant `Subslice` (it is a separate `slice::index` Call
///     whose result length is not statically `N`), so `slice_static_len` returns
///     `None` and the obligation is KEPT — we never assume the dynamic length
///     equals `N`. A genuinely-wrong-length conversion (e.g. `bytes[0..7]` into
///     `[u8; 8]`) has `to - from != N`, so the equality check fails and the
///     obligation is KEPT. An arbitrary `Result::unwrap` (not a slice->array
///     conversion) never matches and is STILL flagged.
/// Trust (Part B): `true` IFF the `Call` terminator in block `ordinal` is a
/// `Result::unwrap` that is PROVABLY INFALLIBLE — the success-by-construction of a
/// slice->array `try_into`/`try_from` whose slice length provably equals the array
/// length (the SAME [`unwrap_is_infallible_slice_to_array`] predicate the
/// `Call::unwrap::panic-freedom` per-statement suppression uses). The hardened
/// `PanicBoundary` lane calls this to SUPPRESS the `Result::unwrap` twin for exactly
/// these infallible unwraps; a genuinely-fallible unwrap (unknown length, user Index
/// impl, non-`try_into` Result) does NOT match and the twin is still emitted
/// (fail-closed). Any other terminator / a non-unwrap call returns `false`.
pub(crate) fn unwrap_call_at_block_is_infallible(
    func: &VerifiableFunction,
    ordinal: usize,
) -> bool {
    let block = func
        .body
        .blocks
        .get(ordinal)
        .filter(|block| block.id.0 == ordinal)
        .or_else(|| func.body.blocks.iter().find(|block| block.id.0 == ordinal));
    block.is_some_and(|block| {
        matches!(
            &block.terminator,
            Terminator::Call { func: callee, args, dest, .. }
                if unwrap_is_infallible_slice_to_array(func, callee, args, dest)
                    // Trust (countdown-loop piece, B0): the const-int
                    // conversion `expect` twin — success-by-construction.
                    || expect_infallible_const_int_conversion(func, callee, args, dest)
                        .is_some()
        )
    })
}
