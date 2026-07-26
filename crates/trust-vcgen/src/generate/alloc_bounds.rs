// Element and byte ceilings for allocation-size reasoning, and the spelled-type
// parsing that turns a MIR type name back into an element width.

use super::*;

/// Byte size of a Rust type as written in monomorphized `safe_def_path_str` /
/// turbofish spelling — the cases recoverable from the spelling ALONE: primitives,
/// fixed arrays `[T; N]`, and tuples `(A, B, …)`. Returns `None` for any type whose
/// layout is not derivable from its name (a named ADT / enum / generic param); the
/// caller treats `None` conservatively (no capacity term emitted, never a false
/// PROVE in the other direction). Recursion depth is bounded by the spelling length.
pub(super) fn parse_spelled_type_byte_size(s: &str) -> Option<i128> {
    let s = s.trim();
    // Fixed array `[T; N]` — size(T) * N. The byte size that makes `with_capacity`
    // capacity-overflow is exactly this shape (`[u8; huge]`).
    if let Some(inner) = s.strip_prefix('[').and_then(|x| x.strip_suffix(']')) {
        let (elem, len) = inner.rsplit_once(';')?;
        // The length const renders as a decimal that MAY carry digit separators or a
        // type suffix (`1099511627776`, `1_099_511_627_776`, `1099511627776usize`);
        // take the leading digit run.
        let digits: String =
            len.trim().chars().take_while(|c| c.is_ascii_digit() || *c == '_').collect();
        let n: i128 = digits.replace('_', "").parse().ok()?;
        return parse_spelled_type_byte_size(elem)?.checked_mul(n);
    }
    // Tuple `(A, B, …)` — sum of field sizes (ignores layout padding; an
    // UNDER-estimate of the true size, which is the SOUND direction for a failure
    // threshold: we may miss a padding-only overflow, never invent one).
    if let Some(inner) = s.strip_prefix('(').and_then(|x| x.strip_suffix(')')) {
        if inner.trim().is_empty() {
            return Some(0); // unit `()`
        }
        let mut total: i128 = 0;
        for part in split_top_level_commas(inner) {
            total = total.checked_add(parse_spelled_type_byte_size(part.trim())?)?;
        }
        return Some(total);
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

/// Split a top-level comma list (tuple / turbofish args), not descending into
/// nested `<…>`, `[…]`, `(…)`. Used to peel the ELEMENT type out of a possibly
/// multi-arg turbofish (`Vec::<T, A>` → `T`).
pub(super) fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut depth, mut start) = (0i32, 0usize);
    for (i, c) in s.char_indices() {
        match c {
            '<' | '[' | '(' => depth += 1,
            '>' | ']' | ')' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
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
            b'>' => {
                depth -= 1;
                if depth == 0 {
                    let inner = callee.get(lt + 1..i)?.trim();
                    return split_top_level_commas(inner).into_iter().next().map(str::trim);
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
pub(super) fn alloc_element_byte_size(
    func: &VerifiableFunction,
    display: &str,
    callee: &str,
    args: &[Operand],
) -> Option<i128> {
    // AUTHORITATIVE: the exact `tcx.layout_of` element size the extractor carried in a
    // trailing `::<__trust_elem_bytes_N>` token — sizes EVERY concrete element (incl. a
    // named struct/enum the turbofish spelling cannot size).
    let raw = parse_elem_bytes_token(callee).or_else(|| match display {
        // Fallbacks (older callees / robustness): the from_elem element operand, or the
        // callee turbofish spelling (primitives / arrays / tuples).
        //
        // `Box::new`/`Rc::new`/`Arc::new` size the SINGLE allocated value `T` from
        // the value operand (arg 0) exactly like `from_elem` — the byte size of `T`
        // IS the allocation, with an implicit count of 1.
        "vec::from_elem" | "Box::new" | "Rc::new" | "Arc::new" => args
            .first()
            .and_then(|e| crate::operand_ty_cow(func, e))
            .and_then(|t| sep_engine::ty_byte_size(t.as_ref())),
        "Vec::with_capacity" | "Vec::reserve" | "<[T]>::resize" => {
            vec_element_spelling(callee).and_then(parse_spelled_type_byte_size)
        }
        _ => None,
    });
    raw.filter(|&s| s > 1)
}

/// Parse the `__trust_elem_bytes_N` element-size token the extractor appends to a
/// bulk-allocation sink callee (`…::with_capacity::<__trust_elem_bytes_4096>`).
pub(super) fn parse_elem_bytes_token(callee: &str) -> Option<i128> {
    let after = callee.rsplit_once("__trust_elem_bytes_")?.1;
    let digits: String = after.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
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
pub(crate) fn method_tail(callee: &str) -> &str {
    let mut base = callee.trim();
    // SOUNDNESS (P0 false proof, 2026-06-17 hunt-15 Class A): strip ALL trailing
    // balanced turbofish groups, not just one. A FREE-FUNCTION bulk-alloc sink rendered
    // with the hunt-11 byte-size token carries TWO trailing turbofishes —
    // `std::vec::from_elem::<u8>::<__trust_elem_bytes_1>` (element type AND byte token),
    // likewise `collect::<Vec<u8>>::<__trust_elem_bytes_N>`. Stripping only the outer one
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

pub(super) fn bulk_alloc_call(callee: &str) -> Option<(&'static str, usize)> {
    match method_tail(callee) {
        "with_capacity" | "with_capacity_in" => Some(("Vec::with_capacity", 0)),
        "reserve" | "reserve_exact" => Some(("Vec::reserve", 1)),
        "resize" | "resize_with" => Some(("<[T]>::resize", 1)),
        "from_elem" => Some(("vec::from_elem", 1)), // `vec![x; n]` lowers to from_elem(x, n)
        _ => None,
    }
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
pub(super) fn single_value_alloc_call(callee: &str) -> Option<&'static str> {
    // The `T` of `Box::<T>::new` is a MIDDLE turbofish, so `method_tail` (which
    // strips a TRAILING turbofish then `rsplit("::")`) still yields `new`/`pin`;
    // gate on the owning type so an unrelated `Foo::new` is not swallowed.
    let tail = method_tail(callee);
    if !matches!(tail, "new" | "pin") {
        return None;
    }
    if callee.contains("boxed::Box") || callee.contains("Box::<") || callee.starts_with("Box::") {
        Some("Box::new")
    } else if callee.contains("rc::Rc") || callee.contains("Rc::<") || callee.starts_with("Rc::") {
        Some("Rc::new")
    } else if callee.contains("sync::Arc")
        || callee.contains("Arc::<")
        || callee.starts_with("Arc::")
    {
        Some("Arc::new")
    } else {
        None
    }
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
pub(super) fn raw_alloc_call(callee: &str) -> Option<&'static str> {
    match method_tail(callee) {
        // Free fns `alloc::alloc(layout)` / `alloc::alloc_zeroed(layout)`. Gate on
        // the `alloc` path so an unrelated `*::alloc` field/method is not caught.
        "alloc" | "alloc_zeroed"
            if callee.contains("alloc::alloc") || callee.contains("::alloc::") =>
        {
            Some("alloc::alloc")
        }
        // `GlobalAlloc::alloc` / `Allocator::allocate` trait dispatch.
        "allocate" if callee.contains("Allocator") => Some("Allocator::allocate"),
        _ => None,
    }
}

/// Arithmetic performed INSIDE a library/intrinsic call that can overflow but
/// produces NO caller-visible `Rvalue::BinaryOp` / `Assert(Overflow)` — so the
/// `generate_v2_safety_vcs` BinaryOp/Assert arms never see it and the operation
/// is reported vacuously safe. This recognizer maps such a `Terminator::Call`
/// to the overflow obligation its hidden arithmetic owes, mirroring
/// `bulk_alloc_call`'s tail-match style:
///
///   * `i32::pow` / `u64::pow` / `usize::pow` (`base.pow(exp)`): `base^exp` can
///     exceed the type max. Modeled conservatively below (flag when the base can
///     be `>= 2` and the exponent is large/unbounded; a small constant base or a
///     bounded exponent discharges).
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
pub(super) fn overflow_arith_call(callee: &str) -> Option<OverflowCall> {
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
pub(super) fn iterator_integer_fold_call(callee: &str) -> bool {
    let base = callee.split("::<").next().unwrap_or(callee);
    matches!(
        base.rsplit("::").take(2).collect::<Vec<_>>().as_slice(),
        ["sum", "Iterator"] | ["product", "Iterator"]
    )
}

/// Trust (str capacity overflow — sibling of the sum/product silent FA): true iff
/// `callee` is `str::repeat` (`std::str::<impl str>::repeat`). `s.repeat(n)`
/// computes its result capacity `s.len() * n` INSIDE the library impl, which
/// overflow-panics ("capacity overflow") for large `n` — no caller-visible
/// `Rvalue::BinaryOp`, so it was SILENTLY accepted (0 obligations). Same
/// owner-decided runtime-checked demotion as sum/product. Gated to the `str`
/// inherent impl specifically: `slice`/`Vec::repeat` (`<impl [T]>::repeat`)
/// already mint a runtime-checked obligation via the bulk-alloc capacity path, so
/// matching them here would double-count (and a broad `repeat` tail-match could
/// catch a user method named `repeat`).
pub(super) fn str_repeat_capacity_overflow_call(callee: &str) -> bool {
    callee.ends_with("<impl str>::repeat")
}
