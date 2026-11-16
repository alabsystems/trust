// Element and byte ceilings for allocation-size reasoning, and the spelled-type
// parsing that turns a MIR type name back into an element width.

use super::*;

/// Byte size of a Rust type as written in monomorphized `safe_def_path_str` /
/// turbofish spelling — the cases recoverable from the spelling ALONE: primitives,
/// fixed arrays `[T; N]`, and unit. Returns `None` for a named ADT, enum, generic
/// parameter or nonempty tuple: its field padding requires actual layout evidence.
/// Counted allocations retain a visible Unknown when this layout is unavailable.
/// Recursion depth is bounded by the spelling length.
pub(super) fn parse_spelled_type_byte_size(s: &str) -> Option<i128> {
    let s = s.trim();
    // Fixed array `[T; N]` — size(T) * N. The byte size that makes `with_capacity`
    // capacity-overflow is exactly this shape (`[u8; huge]`).
    if let Some(inner) = s.strip_prefix('[').and_then(|x| x.strip_suffix(']')) {
        let (elem, len) = inner.rsplit_once(';')?;
        // Accept the complete decimal literal, with separators or a usize suffix.
        // A leading run alone would misread `1 << 40` as 1 and `0x100` as 0.
        let n = parse_decimal_array_len_i128(len.trim())?;
        return parse_spelled_type_byte_size(elem)?.checked_mul(n);
    }
    // Summing tuple field sizes can UNDERESTIMATE the actual stride. That weakens
    // the failure predicate and can falsely prove a capacity-overflowing request.
    // Unit is exact; every other tuple needs the extractor's actual layout token.
    if let Some(inner) = s.strip_prefix('(').and_then(|x| x.strip_suffix(')')) {
        if inner.trim().is_empty() {
            return Some(0); // unit `()`
        }
        return None;
    }
    // Primitives (and `char` = 4, `bool` = 1). Anything else is a named type.
    Some(match s {
        "u8" | "i8" | "bool" => 1,
        "u16" | "i16" => 2,
        "u32" | "i32" | "f32" | "char" => 4,
        "u64" | "i64" | "f64" | "usize" | "isize" => 8,
        "u128" | "i128" => 16,
        _ => return None,
    })
}

fn parse_decimal_array_len_i128(s: &str) -> Option<i128> {
    let s = s.strip_suffix("usize").unwrap_or(s);
    if !s.as_bytes().first().is_some_and(u8::is_ascii_digit)
        || !s.bytes().all(|b| b.is_ascii_digit() || b == b'_')
    {
        return None;
    }
    let mut n: i128 = 0;
    let mut has_digit = false;
    for b in s.bytes() {
        if b != b'_' {
            has_digit = true;
            n = n.checked_mul(10)?.checked_add(i128::from(b - b'0'))?;
        }
    }
    has_digit.then_some(n)
}

fn first_top_level_comma_item(s: &str) -> &str {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '<' | '[' | '(' => depth += 1,
            '>' | ']' | ')' => depth -= 1,
            ',' if depth == 0 => return &s[..i],
            _ => {}
        }
    }
    s
}

pub(super) fn try_for_each_top_level_comma_item<'a, E>(
    s: &'a str,
    mut f: impl FnMut(&'a str) -> Result<(), E>,
) -> Result<(), E> {
    let (mut depth, mut start) = (0i32, 0usize);
    for (i, c) in s.char_indices() {
        match c {
            '<' | '[' | '(' => depth += 1,
            '>' | ']' | ')' => depth -= 1,
            ',' if depth == 0 => {
                f(&s[start..i])?;
                start = i + 1;
            }
            _ => {}
        }
    }
    f(&s[start..])
}

pub(super) fn find_top_level_comma_item<'a>(
    s: &'a str,
    mut pred: impl FnMut(&'a str) -> bool,
) -> Option<&'a str> {
    let mut found = None;
    let _ = try_for_each_top_level_comma_item(s, |item| {
        if pred(item) {
            found = Some(item);
            Err(())
        } else {
            Ok(())
        }
    });
    found
}

/// Split a top-level comma list (tuple / turbofish args), not descending into
/// nested `<…>`, `[…]`, `(…)`. Used to peel the ELEMENT type out of a possibly
/// multi-arg turbofish (`Vec::<T, A>` → `T`).
#[cfg(test)]
pub(super) fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let _ = try_for_each_top_level_comma_item::<()>(s, |item| {
        out.push(item);
        Ok(())
    });
    out
}

/// The ELEMENT-type spelling of a monomorphized `Vec::<T, …>::method` callee path
/// (`std::vec::Vec::<[u8; 1099511627776]>::with_capacity` → `[u8; 1099511627776]`).
/// The element `T` is the first turbofish argument (a trailing allocator `A` is
/// dropped). `None` if the path carries no `Vec::<…>` turbofish (e.g. fully erased
/// in optimized MIR) — the caller then emits no capacity term.
pub(super) fn vec_element_spelling(callee: &str) -> Option<&str> {
    let lt = callee.find("Vec::<")? + "Vec::".len(); // index of the '<'
    let bytes = callee.as_bytes();
    let mut depth = 0i32;
    for i in lt..bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' => {
                depth -= 1;
                if depth == 0 {
                    let inner = callee.get(lt + 1..i)?.trim();
                    return Some(first_top_level_comma_item(inner).trim());
                }
            }
            _ => {}
        }
    }
    None
}

/// The element BYTE size of a recognized bulk-allocation call, for the
/// capacity-overflow (`count * size_of::<T>() < isize::MAX`) obligation. Recovered
/// from the element-value operand (`vec![x; n]` / `from_elem`) or, for the
/// element-erasing `Vec` methods (`with_capacity`/`reserve`/`resize`, whose
/// `RawVec<T>` lowers `T` to `u8`), from the monomorphized callee turbofish. `None`
/// when the element layout is not recoverable from the spelling — the obligation
/// then keeps only the count ceiling (a documented, contrived residual: a `>= 32 GiB`
/// element whose size is not spelled, e.g. a named struct wrapping a giant array;
/// full closure needs extraction-time `tcx.layout_of`).
///
/// Trust (ALLOC-WIDTH-1, 2026-10-08): returns the size AS RECOVERED, zero and
/// one included. The caller decides which strides carry a capacity term (every
/// stride above one, and a one-byte stride only where the element ceiling does
/// not already exclude its line — a live receiver on a target without the
/// live-address-space bound). The spelled fallbacks size `usize`/`isize` and
/// pointers at 8 bytes, the 64-bit layout; on a narrower target that is an
/// over-estimate, which only adds failures.
pub(super) fn alloc_element_byte_size(
    func: &VerifiableFunction,
    display: &str,
    callee: &str,
    args: &[Operand],
) -> Option<i128> {
    // AUTHORITATIVE: the exact `tcx.layout_of` element size the extractor carried in a
    // trailing `::<__trust_elem_bytes@N>` token — sizes EVERY concrete element (incl. a
    // named struct/enum the turbofish spelling cannot size).
    let raw = parse_elem_bytes_token(callee).or_else(|| match display {
        // Fallbacks (older callees / robustness): the from_elem element operand, or the
        // callee turbofish spelling (exact primitives / arrays / unit; nonempty
        // tuples need an authoritative layout token).
        //
        // `Box::new`/`Rc::new`/`Arc::new` size the SINGLE allocated value `T` from
        // the value operand (arg 0) exactly like `from_elem` — the byte size of `T`
        // IS the allocation, with an implicit count of 1.
        "vec::from_elem" | "Box::new" | "Rc::new" | "Arc::new" => args
            .first()
            .and_then(|e| crate::operand_ty_cow(func, e))
            .and_then(|t| allocation_operand_byte_size(t.as_ref())),
        "Vec::with_capacity" | "Vec::reserve" | "<[T]>::resize" => {
            vec_element_spelling(callee).and_then(parse_spelled_type_byte_size)
        }
        _ => None,
    });
    raw.filter(|&s| s >= 0)
}

/// Exact byte sizes available from an allocation operand without a layout token.
/// Keep this separate from the separation engine's abstract size estimates: a
/// tuple field sum and a logical bit-vector width are not physical Rust layouts.
fn allocation_operand_byte_size(ty: &Ty) -> Option<i128> {
    match ty {
        Ty::Unit => Some(0),
        Ty::Bool => Some(1),
        Ty::Int { width, .. } if matches!(*width, 8 | 16 | 32 | 64 | 128) => {
            Some(i128::from(*width) / 8)
        }
        Ty::Float { width } if matches!(*width, 16 | 32 | 64 | 128) => {
            Some(i128::from(*width) / 8)
        }
        Ty::Array { elem, len } => allocation_operand_byte_size(elem)?.checked_mul(i128::from(*len)),
        Ty::Tuple(elems) if elems.is_empty() => Some(0),
        _ => None,
    }
}

/// Trust (ALLOC-WIDTH-1, 2026-10-08): the target an allocation row is judged for —
/// the largest object it can hold, and whether a LIVE receiver's existing length is
/// bounded.
///
/// THE OBJECT LIMIT is `isize::MAX` at the compilation target's pointer width:
/// `Layout`, RawVec ("capacity overflow") and hashbrown ("Hash table capacity
/// overflow") all refuse a larger allocation, and it is the same line trust-ir's
/// `alloc_bound::max_object_bytes(pointer_bits)` judges against. The width is the
/// compiler's session fact (`VcgenContext::with_target_pointer_bits`). Without it —
/// every non-compiler caller — the row is judged at 32 bits, the narrowest width
/// this lane models: a LOWER line only adds failures. Before 2026-10-08 the line was
/// the 64-bit value on every target, and the deleted 256 MiB atom was the only thing
/// refusing a 32-bit target's `Vec::<[u8; 65536]>::with_capacity(n as usize)` over a
/// `u16` `n`, which panics from `n = 32768`.
///
/// A 16-bit target is NOT modeled ([`AllocTarget::for_session`] answers its width as
/// an error, and the caller makes every row a visible Unknown): the 2^28 element
/// ceiling is far above its object limit, so a one-byte element's line and
/// hashbrown's `count * 8` overflow would need terms this lane does not emit.
///
/// THE LIVE RECEIVER. `reserve(additional)` (and `extend`, `collect_into`) asks for
/// `len + additional` slots of a receiver that may already hold `len`. On a 64-bit
/// target `len` is bounded by the `MAX_LIVE_USER_ADDRESS_SPACE_BYTES` modeled-fact
/// axiom (docs/TCB.md), exactly as `bounded_source_fits_sink` bounds it; on any
/// other target that axiom bounds nothing below the object limit, so the receiver
/// may already be full and the row fails closed. Either way only for a receiver
/// whose elements OCCUPY that memory: a zero-sized element's length is bounded by
/// nothing, and the lane asks `live_receiver_length_is_bounded` before it charges
/// a receiver at all (ALLOC-RECEIVER-ZST-1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct AllocTarget {
    /// `isize::MAX` in bytes at the judged pointer width.
    pub(super) object_limit: i128,
    /// The judged pointer width, for diagnostics; `None` when no width was supplied.
    pub(super) pointer_bits: Option<u32>,
    /// `true` exactly on a 64-bit target: the live-address-space axiom bounds a
    /// live receiver (and a live source) far below the object limit.
    pub(super) live_axiom: bool,
}

impl AllocTarget {
    /// The narrowest pointer width this lane models, used when none is supplied.
    pub(super) const NARROWEST_MODELED_POINTER_BITS: u32 = 32;

    /// The target of the current generation: the compiler's session fact, or the
    /// narrowest modeled width when there is none. `Err(bits)` for a pointer width
    /// this lane does not model.
    pub(super) fn for_session() -> Result<Self, u32> {
        Self::at_pointer_bits(crate::session_target_pointer_bits())
    }

    /// The target for a supplied (`Some`) or unsupplied (`None`) pointer width.
    pub(super) fn at_pointer_bits(bits: Option<u32>) -> Result<Self, u32> {
        match bits {
            Some(64) => Ok(Self {
                object_limit: ALLOC_CAPACITY_OVERFLOW_BYTES,
                pointer_bits: Some(64),
                live_axiom: true,
            }),
            Some(32) => {
                Ok(Self { object_limit: (1 << 31) - 1, pointer_bits: Some(32), live_axiom: false })
            }
            None => Ok(Self {
                object_limit: (1i128 << (Self::NARROWEST_MODELED_POINTER_BITS - 1)) - 1,
                pointer_bits: None,
                live_axiom: false,
            }),
            Some(other) => Err(other),
        }
    }

    /// A strict upper bound on the items a live receiver of `stride`-byte elements
    /// may ALREADY hold (its `len`; for a hash table, its buckets, which hashbrown's
    /// `reserve_rehash` resizes past). Under the axiom it is
    /// `trust_types::live_source_bound::live_receiver_items`; otherwise the
    /// receiver is one object of at most `object_limit` bytes, so it may hold
    /// `object_limit / per_item` items and an additional-count row can never be
    /// shown to fit.
    pub(super) fn live_receiver_items(self, stride: i128, hash_table: bool) -> i128 {
        if self.live_axiom {
            let stride = u128::try_from(stride).unwrap_or(0);
            let held = trust_types::live_source_bound::live_receiver_items(stride, hash_table);
            i128::try_from(held).unwrap_or(i128::MAX)
        } else {
            let per_item = if hash_table { stride.saturating_add(1) } else { stride.max(1) };
            self.object_limit / per_item.max(1) + 1
        }
    }
}

/// Parse the TRAILING `::<__trust_elem_bytes@N>` element-size token the
/// extractor appends to a bulk-allocation sink callee
/// (`…::with_capacity::<__trust_elem_bytes@4096>`). Delegates to the ONE
/// shared grammar (`trust_types::parse_trailing_elem_bytes_token`, also used
/// by trust-ir-bridge's `vec_alloc_elem_bytes_token`): the non-identifier `@`
/// spelling plus the trailing-position requirement mean a user-spellable
/// lookalike (`Vec::<__trust_elem_bytes_1>::with_capacity` — a legal
/// type/param name that survives in the rendered path exactly when the
/// extractor omits the real token) can never feed the OOM ceiling a forged
/// stride (batch-6 adversarial review D1; the old loose substring parse here
/// accepted it).
pub(super) fn parse_elem_bytes_token(callee: &str) -> Option<i128> {
    trust_types::parse_trailing_elem_bytes_token(callee)
}

/// Recognize a std bulk heap-allocation / grow call by its `safe_def_path_str`
/// callee, returning `(display_name, size_arg_index)`. Matched on the method
/// tail (mirrors `ord_method`) so generic/path noise does not defeat the match;
/// the size-arg index accounts for the implicit `&mut self` receiver on the
/// grow methods.
/// Final path segment (method / free-fn name) of a `safe_def_path_str` callee,
/// robust to monomorphization noise. Two turbofish shapes occur and BOTH must
/// reduce to the bare name:
///   * middle turbofish — methods: `std::vec::Vec::<u8>::with_capacity`
///     (`rsplit("::")` already yields `with_capacity`); and
///   * **trailing** turbofish — monomorphized free fns:
///     `std::vec::from_elem::<Option<u8>>`, where a naive `rsplit("::").next()`
///     returns the generic-args group `<Option<u8>>` instead of `from_elem`.
///
/// The trailing case is not academic: `vec![x; n]` lowers to exactly
/// `from_elem::<T>` and `xs.collect::<Vec<_>>()` to `collect::<…>` — the two
/// dominant ways an unbounded `Vec` is materialized. Missing it is why the
/// 2026-06-16 interpreter OOM slipped past the UnboundedAllocation gate (the
/// obligation degraded to an SMT timeout the warning lane tolerated) and panicked
/// the host. We strip a *trailing* balanced `<…>` group (only when the path ends
/// in `>`, so a middle turbofish is untouched), then take the last `::` segment.
///
/// KNOWN RESIDUAL, MEASURED 2026-09-20, DELIBERATELY NOT FIXED HERE. The reverse
/// depth scan below is the MIRROR IMAGE of the `->` defect closed in
/// `sep_engine::strip_turbofish_args`: scanning right-to-left, the `>` of an ARROW
/// increments `depth`, so a TRAILING turbofish containing a function pointer never
/// balances, `open` stays `None`, the loop `break`s, and the leaf that comes back is
/// garbage. `alloc::vec::from_elem::<fn() -> u8>` — what `vec![f; n]` lowers to for a
/// `Vec<fn() -> u8>` — yields `""`, and every recognizer keyed on the leaf misses.
///
/// It is NOT a regression of this branch (the SEAL has it) and it is NOT this
/// commit's to fix: `method_tail` backs ~30 call sites across the panic-freedom,
/// guards and slice-conversion lanes, and correcting it moves rows in all of them.
/// It IS a live LOST OBLIGATION, so it is written down rather than implied. MEASURED
/// on the sealed `trustc ff538f905` (`$TMPDIR/rc6/mtail.rs`):
///
///   vec![0u8; n]              `unbounded allocation in vec::from_elem`  PRESENT
///   vec![nop as fn(); n]                                                PRESENT
///   vec![f as fn() -> u8; n]                                            ABSENT
///
/// The fix is the same one line (do not count a `>` preceded by `-`) plus a
/// re-measure of every lane that consumes the leaf.
pub(crate) fn method_tail(callee: &str) -> &str {
    let mut base = callee.trim();
    // SOUNDNESS (P0 false proof, 2026-06-17 hunt-15 Class A): strip ALL trailing
    // balanced turbofish groups, not just one. A FREE-FUNCTION bulk-alloc sink rendered
    // with the hunt-11 byte-size token carries TWO trailing turbofishes —
    // `std::vec::from_elem::<u8>::<__trust_elem_bytes@1>` (element type AND byte token),
    // likewise `collect::<Vec<u8>>::<__trust_elem_bytes@N>`. Stripping only the outer one
    // left `from_elem::<u8>`, whose last `::` segment is `<u8>` (not `from_elem`), so
    // `bulk_alloc_call`/`is_collect_sink` returned None and `vec![x; n]` / `(0..n).collect()`
    // emitted NO UnboundedAllocation obligation at all — a capacity-overflow then sailed
    // through as a default-mode headline OVER-CREDIT ("1 proved out of 1" crediting only an
    // unrelated safe op, while the alloc panics). A METHOD call keeps its type turbofish in
    // the MIDDLE (`Vec::<u8>::with_capacity::<…>`), so it needs a single strip — the loop is
    // a no-op past the first iteration for that shape, and `break` on an unbalanced `<…>`
    // prevents any spin.
    while base.ends_with('>') {
        let bytes = base.as_bytes();
        let mut depth = 0i32;
        let mut open = None;
        for (i, &b) in bytes.iter().enumerate().rev() {
            // A `>` that closes an ARROW is not a bracket. A fn-pointer or
            // `Fn`-trait type inside a turbofish carries one, and rustc renders
            // monomorphized `str::split` with exactly that:
            //
            //   core::str::<impl str>::split::<fn(char) -> bool {…is_whitespace}>
            //
            // Counting the arrow's `>` left the group permanently unbalanced, so
            // the loop hit its `None` break, nothing was stripped, and the tail
            // came back as the fn item's own last segment instead of `split`.
            //
            // This is the same failure this loop was written to fix, one type
            // shape over, and it fails in the same direction: a missed tail
            // means `is_collect_sink`/`bulk_alloc_call` do not recognize the
            // call, so NO allocation obligation is emitted at all — the
            // over-credit the note above records, not a visible Unknown.
            if b == b'>' && i > 0 && bytes[i - 1] == b'-' {
                continue;
            }
            match b {
                b'>' => depth += 1,
                b'<' => {
                    depth -= 1;
                    if depth == 0 {
                        open = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        match open {
            Some(i) => base = base[..i].trim_end_matches(':'),
            None => break, // unbalanced `<…>` — avoid an infinite loop
        }
    }
    let tail = base.rsplit("::").next().unwrap_or(base);
    // A middle turbofish leaves the name clean already; this final strip is a
    // belt-and-braces no-op for `with_capacity` and trims any residue.
    tail.split('<').next().unwrap_or(tail).trim()
}

pub(super) struct AllocCallDispatch;

impl AllocCallDispatch {
    #[inline]
    pub(super) fn bulk_with_tail(tail: &str) -> Option<(&'static str, usize)> {
        match tail {
            "with_capacity"
            | "with_capacity_in"
            | "with_capacity_and_hasher"
            | "with_capacity_and_hasher_in" => Some(("Vec::with_capacity", 0)),
            "reserve" | "reserve_exact" | "extend_reserve" => Some(("Vec::reserve", 1)),
            "resize" | "resize_with" => Some(("<[T]>::resize", 1)),
            "from_elem" => Some(("vec::from_elem", 1)),
            "new_uninit_slice" | "new_uninit_slice_in" => Some(("Box/Rc/Arc::new_uninit_slice", 0)),
            "new_zeroed_slice" | "new_zeroed_slice_in" => Some(("Box/Rc/Arc::new_zeroed_slice", 0)),
            _ => None,
        }
    }

    #[inline]
    pub(super) fn single_value_with_tail(callee: &str, tail: &str) -> Option<&'static str> {
        if !matches!(tail, "new" | "pin") {
            return None;
        }
        if callee.contains("Box")
            && (callee.contains("boxed::Box")
                || callee.contains("Box::<")
                || callee.starts_with("Box::"))
        {
            Some("Box::new")
        } else if callee.contains("Rc")
            && (callee.contains("rc::Rc")
                || callee.contains("Rc::<")
                || callee.starts_with("Rc::"))
        {
            Some("Rc::new")
        } else if callee.contains("Arc")
            && (callee.contains("sync::Arc")
                || callee.contains("Arc::<")
                || callee.starts_with("Arc::"))
        {
            Some("Arc::new")
        } else {
            None
        }
    }

    #[inline]
    pub(super) fn raw_with_tail(callee: &str, tail: &str) -> Option<&'static str> {
        match tail {
            "alloc" | "alloc_zeroed"
                if callee.contains("alloc::alloc") || callee.contains("::alloc::") =>
            {
                Some("alloc::alloc")
            }
            "allocate" if callee.contains("Allocator") => Some("Allocator::allocate"),
            _ => None,
        }
    }
}

pub(super) fn bulk_alloc_call(callee: &str) -> Option<(&'static str, usize)> {
    AllocCallDispatch::bulk_with_tail(method_tail(callee))
}

/// Recognize a SINGLE-VALUE heap allocation — `Box::new` / `Rc::new` / `Arc::new`
/// (and the pinning `Box::pin` / `Rc::pin` / `Arc::pin` forms) — returning a
/// display name. Unlike the [`bulk_alloc_call`] sinks, these have NO element-count
/// argument: they heap-allocate exactly ONE value of type `T`, so the hazard is a
/// single OVERSIZED `T` (`Box::new([0u8; 1 << 40])` — a 1 TiB box that OOMs / panics
/// "capacity overflow"), not an unbounded count. The element byte size of `T` is the
/// value operand (arg 0); the caller models count = 1 and emits a CAPACITY-OVERFLOW
/// byte obligation when `size_of::<T>()` is recoverable and reaches the budget,
/// degrading to NOTHING (drop-in) for an ordinary small `Box::new(x)` and never a
/// false PROVE in the other direction.
///
/// `Box::from`/`Rc::from`/`Arc::from` and the slice/`str` `From` shims are NOT here:
/// their size is the SOURCE length (already covered where it is a recognized sink),
/// and a blanket match would false-flag the ubiquitous `Box::from(&small)` shim.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn single_value_alloc_call(callee: &str) -> Option<&'static str> {
    AllocCallDispatch::single_value_with_tail(callee, method_tail(callee))
}

/// Recognize a RAW allocator call — `alloc::alloc` / `alloc_zeroed` / the
/// `GlobalAlloc::alloc` / `Allocator::allocate` trait methods — whose size is
/// carried INSIDE a `Layout` value, not a plain integer operand the obligation can
/// range-bound. There is no sound count/byte formula to recover from the optimized
/// MIR (the `Layout` is an opaque ADT), so flagging it with a count ceiling would be
/// meaningless and a silent skip would wave a genuine unbounded `alloc(layout)` —
/// AY's exact raw-buffer growth — straight through. The caller therefore emits a
/// VISIBLE `UnsupportedMir` obligation (preclassified to Unknown, NEVER a false
/// PROVE), making the raw-allocation hazard surface for review rather than vanish.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn raw_alloc_call(callee: &str) -> Option<&'static str> {
    AllocCallDispatch::raw_with_tail(callee, method_tail(callee))
}

/// Arithmetic performed INSIDE a library/intrinsic call that can overflow but
/// produces NO caller-visible `Rvalue::BinaryOp` / `Assert(Overflow)` — so the
/// `generate_v2_safety_vcs` BinaryOp/Assert arms never see it and the operation
/// is reported vacuously safe. This recognizer maps such a `Terminator::Call`
/// to the overflow obligation its hidden arithmetic owes, mirroring
/// `bulk_alloc_call`'s tail-match style:
///
///   * `i32::pow` / `u64::pow` / `usize::pow` (`base.pow(exp)`): `base^exp` can
///     leave the type. Modeled EXACTLY by `v2_overflow_call_body` (Trust,
///     POW-SYMEXP-1, 2026-10-05): a negative base, and an exponent bounded below
///     the width, are charged like any other overflowing pair; only a guard that
///     excludes every overflowing `(base, exp)` discharges.
///   * the `unchecked_add` / `unchecked_sub` / `unchecked_mul` intrinsics: these
///     are *undefined behavior* on overflow (no wrap, no panic), so an unguarded
///     one MUST be checked — they reduce to the corresponding `+`/`-`/`*`
///     overflow obligation on their two operands.
///
/// `next_power_of_two` and `Iterator::sum`/`product` are deliberately NOT here:
/// `sum`/`product` fold over a runtime-length slice with no operand the caller
/// can range-bound (modeling them soundly needs an accumulation invariant we do
/// not have), and a clean conservative model is not available — flagging them
/// unconditionally would false-FAIL ordinary bounded sums. Keeping this set to
/// `pow` + the `unchecked_*` intrinsics keeps every emitted obligation cleanly
/// dischargeable by a dominating guard / precondition.
///
/// Trust (2026-10-06, POW-SYMEXP-1 integration review): the `pow` arm MINTS core's
/// overflow row, so it answers only for core's own primitive-integer `pow` —
/// `core::num::<impl iN/uN>::pow` (or the `std::num::` spelling) under an
/// AUTHENTICATED sysroot root, the recognizer `strict_pow` already takes
/// (`numeric_panic::int_inherent`). It used to match the last path segment
/// alone, so a USER free function or method named `pow` that returns an integer
/// (`fn pow(b: i32, e: u32) -> i32 { b ^ e as i32 }`, `impl M { fn pow(&self, e:
/// u32) -> u32 }`) was charged std's overflow row over its own arguments and
/// refuted with a counterexample for an overflow that cannot happen — MEASURED
/// on the stage 1 of `9e11546767`: `if e < 40 { pow(-2, e) }` failed at `e = 32`,
/// `if e < 32 { m.pow(e) }` at `e = 2, m = 65536`, and the unguarded `m.pow(e)`
/// was already refuted on the stage 1 of `dc15b882f6`, before the exact body. A
/// user `pow` mints no row here; whatever it does is in its own body, which is
/// verified as its own function.
/// [`overflow_arith_call_name_only`] keeps the name-only view for the deny-list
/// union that only WITHHOLDS an admission.
///
/// Trust (2026-10-06, UNCHECKED-NAME-1): the `unchecked_{add,sub,mul}` arms take
/// the same discipline. They too were decided by the last path segment alone, so a
/// USER function or method merely named `unchecked_add` (`fn unchecked_add(a: u32,
/// b: u32) -> u32 { a ^ b }`, a trait method `<u32 as T>::unchecked_mul`) was
/// charged `UncheckedArithmeticOverflow` over its own arguments: an unguarded
/// caller was refused with an `unknown` row, and a guarded one read `proved |
/// clean-kernel-certified | unchecked arithmetic overflow (Add)` — a Certified row
/// about an addition the program never performs (measured on the stage 1 of
/// `9e11546767`). An arm now mints only for
///   * core's own primitive-integer method, `core::num::<impl iN/uN>::unchecked_*`
///     (or the `std::num::` spelling), through `numeric_panic::int_inherent`, whose
///     leaf must be the arm's own operation; or
///   * the intrinsic itself, `core::intrinsics::unchecked_*` (or `std::`), by EXACT
///     path with generics stripped, under an authenticated sysroot root. MIR lowers a
///     real intrinsic call to `BinOp::{Add,Sub,Mul}Unchecked` before `TrustVerify`
///     runs (`LowerIntrinsics`), so this spelling reaches the arm only from a direct
///     `VerifiableFunction` (the unit fixtures build exactly it); it is kept rather
///     than dropped because dropping it could only lose a row.
///
/// Trust (wave-19 review, 2026-10-09): the `pow` arm and the core-method half of the
/// `unchecked_*` arms read core's spelling through `numeric_panic::int_inherent_minting`,
/// which also accepts it behind ONE leading `__trust_crate@<id>::` stamp. The extractor
/// stamps the GENUINE core when a second crate named `core` is in the graph or under
/// `-Zbuild-std`, and refusing the stamp lost these rows for genuine calls (measured on
/// the stage 1 of `46e9afaf95`: beside a `--crate-name core` dependency,
/// `unsafe { a.unchecked_add(b) }` lost its `unchecked_overflow` row and `a.pow(e)` was
/// charged nothing but its absent-callee row). An inherent method on a primitive needs
/// rustc's internal coherence attributes, so the stamped spelling is core's or a
/// forgery whose worst outcome here is a row it does not owe (a false red). A stamp
/// anywhere else, or one in front of any other text, is refused. The intrinsic half
/// stays authenticated-only: a real intrinsic call never reaches this arm.
pub(super) fn overflow_arith_call(callee: &str) -> Option<OverflowCall> {
    match overflow_arith_call_name_only(callee)? {
        OverflowCall::Pow => {
            matches!(numeric_panic::int_inherent_minting(callee), Some((_, _, "pow")))
                .then_some(OverflowCall::Pow)
        }
        kind @ OverflowCall::Unchecked(op) => {
            let leaf = match op {
                BinOp::Add => "unchecked_add",
                BinOp::Sub => "unchecked_sub",
                BinOp::Mul => "unchecked_mul",
                _ => return None,
            };
            let core_int_method =
                matches!(numeric_panic::int_inherent_minting(callee), Some((_, _, l)) if l == leaf);
            let core_intrinsic = !core_int_method
                && (callee.starts_with("core::intrinsics::")
                    || callee.starts_with("std::intrinsics::"))
                && trust_types::path_root_is_authenticated_sysroot_crate(callee)
                && {
                    let bare = vc_strip_generics_cow(callee);
                    bare.strip_prefix("core::intrinsics::")
                        .or_else(|| bare.strip_prefix("std::intrinsics::"))
                        == Some(leaf)
                };
            (core_int_method || core_intrinsic).then_some(kind)
        }
    }
}

/// The method-tail view of [`overflow_arith_call`], with no sysroot
/// authentication: `pow` names `OverflowCall::Pow` and `unchecked_{add,sub,mul}`
/// name `OverflowCall::Unchecked` whatever their owner (since UNCHECKED-NAME-1,
/// 2026-10-06, the minting view authenticates both).
///
/// Trust (2026-10-06, POW-SYMEXP-1 integration review): only
/// `callee_has_call_site_panic_family` reads this, and there a `Some` only
/// WITHHOLDS the vanilla admission of a real-sysroot fn item the compiler has
/// already authenticated (`foreign_fn_item_type_arg_is_accounted`). Keeping the
/// wider name-only match there leaves that gate's answer byte-identical: the
/// sysroot `Wrapping::<T>::pow` / `Saturating::<T>::pow` items stay withheld as
/// before rather than becoming newly admitted by a change nobody measured. It
/// must never mint a row.
pub(super) fn overflow_arith_call_name_only(callee: &str) -> Option<OverflowCall> {
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    match tail {
        // `base.pow(exp)` — the receiver lowers to the first MIR arg.
        "pow" => Some(OverflowCall::Pow),
        // UB-on-overflow intrinsics: `core::intrinsics::unchecked_{add,sub,mul}(a, b)`.
        "unchecked_add" => Some(OverflowCall::Unchecked(BinOp::Add)),
        "unchecked_sub" => Some(OverflowCall::Unchecked(BinOp::Sub)),
        "unchecked_mul" => Some(OverflowCall::Unchecked(BinOp::Mul)),
        _ => None,
    }
}

/// Trust (iterator-fold overflow — the sum/product SILENT false-accept): true iff
/// `callee` is `Iterator::sum` / `Iterator::product`. These fold accumulation
/// arithmetic INSIDE the library impl, so no caller-visible `Rvalue::BinaryOp`
/// exists and `overflow_arith_call` deliberately skips them (a bounded `vec.sum()`
/// has no operand the caller can range-bound, so a REFUTABLE overflow VC would
/// false-FAIL it). But skipping ENTIRELY made a genuinely-overflowing
/// `(1..=n).product::<i32>()` compile CLEAN with zero obligations — a silent
/// false-accept. Instead, mint an UnsupportedMir obligation (→ Unknown →
/// runtime-checked in the default lane, exactly like `m[&k]`), so the overflow is
/// HONESTLY accounted and delegated to the runtime overflow check, never silently
/// verified and never false-FAILED. Gated to the GENERIC trait path
/// `…::Iterator::{sum,product}` rustc renders (optional trailing `::<S>` turbofish
/// stripped) so a user method named `sum`/`product` on a non-`Iterator` receiver
/// never matches. `count` is excluded (its `usize` result cannot overflow — that
/// would need more than `usize::MAX` elements in memory).
///
/// Trust (2026-09-25, F4): THIS RECOGNIZER NEVER FIRED. rustc renders the call
/// fully qualified — `<core::slice::iter::Iter<'_, u32> as
/// core::iter::traits::iterator::Iterator>::sum::<u32>` — whose last two segments
/// are `sum` and `Iterator>`, never `Iterator`, so `v.iter().sum::<u32>()` built
/// exit 0 with ZERO rows and panicked on `[u32::MAX, 1]`. The unit fixtures were
/// dumped when the bare `std::iter::Iterator::sum` spelling was still emitted.
/// Authentication is now [`vc_callee_is_std_iter_trait_method`] — both spellings,
/// anchored to the `core::iter::`/`std::iter::` trait path — and the direct
/// `Sum::sum(iter)` / `Product::product(iter)` forms are recognized too. The
/// iterator is argument 0 in all four.
/// `(IteratorFold, is_direct_sum_or_product_trait)` for `Iterator::sum`/`product`
/// and `Sum::sum`/`Product::product`.
fn iterator_integer_fold_call_detail(callee: &str) -> Option<(IteratorFold, bool)> {
    if !(callee.contains("sum") || callee.contains("product"))
        || !(callee.contains("core::iter::") || callee.contains("std::iter::"))
    {
        return None;
    }
    if vc_callee_is_std_iter_trait_method(callee, "Iterator", "sum") {
        Some((IteratorFold::Sum, false))
    } else if vc_callee_is_std_iter_trait_method(callee, "Sum", "sum") {
        Some((IteratorFold::Sum, true))
    } else if vc_callee_is_std_iter_trait_method(callee, "Iterator", "product") {
        Some((IteratorFold::Product, false))
    } else if vc_callee_is_std_iter_trait_method(callee, "Product", "product") {
        Some((IteratorFold::Product, true))
    } else {
        None
    }
}

pub(super) fn iterator_integer_fold_call(callee: &str) -> Option<IteratorFold> {
    iterator_integer_fold_call_detail(callee).map(|(fold, _)| fold)
}

/// Trust (W4 ITER-HOF fix round 4, 2026-10-02): NAME-ONLY, for the compiler's
/// admission of a sysroot fn ITEM handed over as a type argument (through
/// `callee_has_call_site_panic_family`): is `callee` an
/// [`iterator_integer_fold_call`] whose accumulator may overflow? A DIRECT call is
/// charged its `iterator-fold-overflow` row; the item spelling
/// (`v.iter().map(|w| w.iter()).map(Iterator::sum::<u32>)`) runs the same fold
/// inside the HOF, where no call-site recognizer looks. MEASURED on stage 1 of
/// origin/main `a3be88bbde`: `.map(Iterator::sum::<u32>).last()` and
/// `Option::map(Iterator::sum::<u32>)` built rc=0 (a `runtime_checked` row only) and
/// panicked "attempt to add with overflow" on `[u32::MAX, 1]`; with W4 ITER-HOF the
/// `.collect()` consumer of the same `map` built rc=0 too (main refused it only for
/// its collect count). Conservative: only an accumulator that cannot overflow is
/// excluded — a float, or a `Wrapping`/`Saturating` integer — read from the method's
/// turbofish (`Iterator::sum::<S>`) or, for `Sum::sum`/`Product::product`, the
/// qualified `Self`; an integer, an `Option`/`Result` of one, or an unreadable
/// spelling answers `true`.
pub(super) fn iterator_fold_item_may_overflow(callee: &str) -> bool {
    let Some((_, is_direct_trait)) = iterator_integer_fold_call_detail(callee) else {
        return false;
    };
    let accumulator = if is_direct_trait {
        vc_qualified_self_ty(callee)
    } else {
        // The duplicate-crate-name fingerprint `::<__trust_args@HEX>` is an identity
        // tag, not the accumulator turbofish (ARGS-FINGERPRINT-READ-1).
        trust_types::strip_trailing_args_fingerprint(callee.trim())
            .rsplit_once("::<")
            .map(|(_, t)| t.strip_suffix('>').unwrap_or(t))
    };
    // Trust (ARGS-FINGERPRINT-READ-1 round 2, 2026-10-07): a float is a primitive no
    // crate can spell; `Wrapping`/`Saturating` are TYPE PATHS, and on a tagged callee
    // (an argument — the qualified `Self` included, it is the trait's first argument —
    // names a crate whose name does not identify it) `core::num::wrapping::Wrapping`
    // may be a crate built `--crate-name core`, whose `Sum` impl may overflow.
    let type_paths_identify = !trust_types::args_display_may_name_a_same_named_crate(callee);
    !accumulator.map(str::trim).is_some_and(|t| {
        matches!(t, "f16" | "f32" | "f64" | "f128")
            || type_paths_identify
                && [
                    "core::num::wrapping::Wrapping<",
                    "core::num::saturating::Saturating<",
                    "std::num::Wrapping<",
                    "std::num::Saturating<",
                ]
                .iter()
                .any(|p| t.starts_with(*p))
    })
}

/// Which integer fold [`iterator_integer_fold_call`] recognized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IteratorFold {
    Sum,
    Product,
}

/// Trust (2026-09-25, F4): the INTEGER type an integer fold accumulates in, read
/// from the call's destination: the destination itself, or the payload of a std
/// `Option`/`Result` destination (`Sum<Option<U>> for Option<T>` and its `Result`
/// twin run `T`'s own overflowing fold inside `try_process`). `char` has no `Sum`
/// and a float saturates, so both answer `None`, as does `Wrapping`/`Saturating`
/// (an ADT that is neither).
pub(super) fn fold_accumulator_int_ty(ty: &Ty) -> Option<Ty> {
    match ty {
        Ty::Int { .. } | Ty::PtrSizedInt { .. } => Some(ty.clone()),
        Ty::Adt { name, variants, .. }
            if name.starts_with("core::") || name.starts_with("std::") =>
        {
            let payload = match name.split('<').next().unwrap_or(name) {
                "core::option::Option" | "std::option::Option" => "Some",
                "core::result::Result" | "std::result::Result" => "Ok",
                _ => return None,
            };
            let variant = variants.iter().find(|v| v.name == payload)?;
            match &variant.fields.first()?.1 {
                t @ (Ty::Int { .. } | Ty::PtrSizedInt { .. }) => Some(t.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Trust (str capacity overflow — sibling of the sum/product silent FA): true iff
/// `callee` is `str::repeat` (`std::str::<impl str>::repeat`). `s.repeat(n)`
/// computes its result capacity `s.len() * n` INSIDE the library impl, which
/// overflow-panics ("capacity overflow") for large `n` — no caller-visible
/// `Rvalue::BinaryOp`, so it was SILENTLY accepted (0 obligations). Same
/// default-lane runtime-checked demotion as sum/product. Gated to the `str`
/// inherent impl specifically: `slice`/`Vec::repeat` (`<impl [T]>::repeat`)
/// already mint a runtime-checked obligation via the bulk-alloc capacity path, so
/// matching them here would double-count (and a broad `repeat` tail-match could
/// catch a user method named `repeat`).
pub(super) fn str_repeat_capacity_overflow_call(callee: &str) -> bool {
    callee.ends_with("<impl str>::repeat")
}

#[cfg(test)]
mod fn_item_callee_tests {
    use super::*;

    // Review round 29 (2026-10-01): the `>` of a fn-item type's `->` inside the
    // qualifier closed it early, the fold recognizer missed the call, and its
    // overflow row was never minted while the compiler granted the call.
    #[test]
    fn a_fold_over_a_fn_item_callable_is_still_recognized() {
        let sum = "<core::iter::adapters::map::Map<core::iter::adapters::copied::Copied<\
                   core::slice::iter::Iter<'_, u8>>, fn(u8) -> u32 {big}> as \
                   core::iter::traits::iterator::Iterator>::sum::<u32>";
        assert_eq!(iterator_integer_fold_call(sum), Some(IteratorFold::Sum));
        let product = "<core::iter::adapters::filter::Filter<core::ops::range::Range<u32>, \
                       for<'a> fn(&'a u32) -> bool {keep}> as \
                       core::iter::traits::iterator::Iterator>::product::<u32>";
        assert_eq!(iterator_integer_fold_call(product), Some(IteratorFold::Product));
    }
}
