// W4 STR-OFFSET (2026-09-25): value facts for the RESULTS of the std str searches
// — `str::find`/`str::rfind` (`Some(i)`) and `str::starts_with`/`str::ends_with`
// (`true`) — keyed on the compiler-minted callee identity (`CalleeKey::
// sysroot_item`), never on a rendered path.
//
// THE THEOREMS, all from `core::str`'s own contract:
//
//  * `s.find(p) == Some(i)` / `s.rfind(p) == Some(i)`: `i` is the byte index at
//    which a match of `p` STARTS, so `s[i..i + m]` is the match, where `m` is the
//    match's byte length. Hence `i + m <= s.len()`, and both `i` and `i + m` are
//    UTF-8 char boundaries of `s` (the match of a `char` is that char's whole
//    encoding; the match of a `&str` is a whole, valid-UTF-8 substring). For a
//    `char` pattern `m == c.len_utf8() >= 1`; for a `&str` literal `m` is its
//    byte length (possibly 0).
//  * `s.starts_with(p) == true` / `s.ends_with(p) == true` for a pattern whose
//    match length is `m`: `s.len() >= m`.
//
// WHAT THE PATTERN MAY BE. Only the shapes whose match length this lane can
// state exactly, or bound below: a `char` CONSTANT (`m = len_utf8(c)`), a
// `&str` LITERAL (`m = bytes.len()`), and a `char`-typed LOCAL (`m >= 1`, the
// match END is then not creditable). Everything else — a closure, a `[char; N]`
// set, a `&String`, a `&str` variable — declines: no fact, never a guessed one.
// A `char` constant reaches the MIR as `ConstValue::Uint(c, 32)`, the same
// spelling as a `u32` constant; that is unambiguous HERE because the callee is
// the authenticated `str::find` and `u32` implements no `Pattern` (the orphan
// rule forbids anyone else adding one).
//
// WHY THE BOUNDARY HALF IS STRUCTURAL. `str` is extracted as `[u8]`, so a
// range-slice obligation models only the byte bounds; the char-boundary panic
// is not a formula term and `panic_calls::slice_method_panic_body` fails a str
// range CLOSED unless every explicit endpoint is PROVABLY a boundary. The
// CharIndices yield lane is the precedent: a bound that IS a yielded offset of
// the SAME string is credited structurally, VC-locally. This lane adds exactly
// two more credited shapes — the search payload `i` itself, and `i + K` where
// `K` is the CONSTANT equal to the exact match length — and nothing derived
// (`i + 1` after a two-byte `'é'` match, `i - 1`, `i + n`) is credited, because
// those are exactly the offsets that fall mid-char.
//
// THE `?`/`ok_or` HOPS. `let at = s.find('@').ok_or(E)?;` reads the payload out
// of `ControlFlow::Continue`, two calls away from the search. Each hop is keyed
// on its DefId (`Option::ok_or`/`ok_or_else`: `Some(v) -> Ok(v)`;
// `core::ops::Try::branch`: `Some(v)`/`Ok(v) -> Continue(v)`), and the
// `Try::branch` hop — a TRAIT method, whose key names no impl — is admitted only
// when its receiver is the unique result of a `str::find`/`rfind` (so `Self =
// Option<usize>`) or of `Option::ok_or`/`ok_or_else` (so `Self = Result<_, _>`):
// both are `core` types and `Try` is a `core` trait, so coherence leaves `core`'s
// own impl as the only one that can run.
//
// SOUNDNESS GATES, each one a channel a real false proof used against a sibling:
//  * every hop's local is the UNIQUE value of one call (`local_defs::
//    unique_value_call`): no second definition, no projected write, no `&mut`
//    alias, no parameter entry value;
//  * the payload read is `(x as Downcast(v)).Field(0)` with `v` the value-bearing
//    variant of the type the producing call's DefId fixes (`Option::Some` = 1,
//    `Result::Ok` = 0, `ControlFlow::Continue` = 0 — declaration order in `core`);
//  * the searched string's root is gated exactly as the CharIndices root is
//    (`charindices_shared_slice_root`: a shared `&str`, one value, never mutably
//    borrowed or projection-written), so the string the payload indexes IS the
//    string that is sliced or whose length the fact names;
//  * a per-block fact is keyed on a payload that passes
//    `payload_carries_global_fact` (single static assignment), states the length
//    of a root only through `licensed_slice_len_formula`, and is attached only to
//    blocks that READ the payload — reached, by MIR definite initialization,
//    only after the search returned its value on this iteration.

use super::*;

/// The byte length of a search pattern's match, as far as it is known.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StrMatchLen {
    /// Exactly this many bytes (a `char` constant's UTF-8 width, or a `&str`
    /// literal's byte length).
    Exact(i128),
    /// A `char`-typed local: between 1 and 4 bytes, value unknown.
    AtLeastOne,
}

impl StrMatchLen {
    /// The largest `k` for which `offset + k <= len` is a theorem.
    fn lower_bound(self) -> i128 {
        match self {
            StrMatchLen::Exact(k) => k,
            StrMatchLen::AtLeastOne => 1,
        }
    }
}

/// The UTF-8 width of the Unicode scalar value `c`, or `None` if `c` is not one
/// (a surrogate or above `char::MAX`) — then it was never a `char` and the
/// caller declines.
fn char_utf8_width(c: u128) -> Option<i128> {
    let c = u32::try_from(c).ok()?;
    char::from_u32(c).map(|ch| ch.len_utf8() as i128)
}

/// The match length of the PATTERN operand of an authenticated `str` search or
/// affix test. See the module banner for the admitted shapes.
pub(crate) fn str_pattern_match_len(
    func: &VerifiableFunction,
    pat: &Operand,
) -> Option<StrMatchLen> {
    match pat {
        Operand::Constant(ConstValue::Uint(c, 32)) => char_utf8_width(*c).map(StrMatchLen::Exact),
        Operand::Constant(ConstValue::Str { bytes }) => {
            // A `&str` literal is valid UTF-8 by construction; a byte-array
            // constant that reused this carrier is not a `Pattern` at all, and
            // the check keeps it from ever being read as one.
            std::str::from_utf8(bytes).ok()?;
            Some(StrMatchLen::Exact(bytes.len() as i128))
        }
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            // The verifier's extraction spells `char` as `Int { 32, unsigned }`
            // (`Ty::Char` is the faithful lane's); `u32` is not a `Pattern`, so
            // on an authenticated `str` search either spelling is a `char`.
            match crate::local_ty_ref(func, p.local) {
                Some(Ty::Char | Ty::Int { width: 32, signed: false }) => {
                    Some(StrMatchLen::AtLeastOne)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The authenticated `SysrootItem` of a call terminator, when its callee is in
/// the compiler's own sysroot.
fn call_item(term: &Terminator) -> Option<(trust_types::SysrootItem, &[Operand])> {
    let Terminator::Call { callee_key: Some(key), args, .. } = term else { return None };
    if !key.krate_is_real_sysroot {
        return None;
    }
    Some((key.sysroot_item?, args.as_slice()))
}

#[inline]
pub(super) fn terminator_is_str_search_call(term: &Terminator) -> bool {
    use trust_types::SysrootItem as S;
    matches!(call_item(term), Some((S::StrFind | S::StrRfind | S::IteratorPosition, _)))
}

fn whole_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// Where a search result came from: the ROOT local of the searched string and
/// the match length of the pattern.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StrSearchOrigin {
    pub(crate) root: usize,
    pub(crate) match_len: StrMatchLen,
}

/// `x` is the unique result of a call whose value-bearing variant `v` carries
/// (through the admitted hops) the `Some(i)` of an authenticated
/// `str::find`/`rfind`.
fn wrapped_search_origin(
    func: &VerifiableFunction,
    x: usize,
    v: usize,
    fuel: u32,
) -> Option<StrSearchOrigin> {
    use trust_types::SysrootItem as S;
    let fuel = fuel.checked_sub(1)?;
    if crate::local_defs::is_parameter(func, x)
        || !super::terminator_presence_for(func).has_str_search_item_call
    {
        return None;
    }
    let (item, args) = call_item(crate::local_defs::unique_value_call(func, x)?)?;
    match item {
        S::StrFind | S::StrRfind if v == 1 && args.len() == 2 => {
            let root = charindices_shared_slice_root(func, &args[0])?;
            let match_len = str_pattern_match_len(func, &args[1])?;
            Some(StrSearchOrigin { root, match_len })
        }
        // STR_BYTE_POSITION: only at the top level (no `ok_or` / `?` hop between
        // the `position` call and the payload read).
        S::IteratorPosition if args.len() == 2 => bytes_position_origin(func, x, v),
        // `Option::ok_or(o, e)` / `ok_or_else(o, f)`: `Some(v) -> Ok(v)`.
        S::OptionOkOr | S::OptionOkOrElse if v == 0 => {
            let inner = whole_local(args.first()?)?;
            let (inner_item, _) = call_item(crate::local_defs::unique_value_call(func, inner)?)?;
            if inner_item == S::IteratorPosition {
                return None;
            }
            wrapped_search_origin(func, inner, 1, fuel)
        }
        // `Try::branch(r)`: `Some(v)`/`Ok(v) -> Continue(v)`, with `Self` fixed by
        // the DefId of the call that produced the receiver (module banner).
        S::TryBranch if v == 0 && args.len() == 1 => {
            let y = whole_local(&args[0])?;
            let (inner, _) = call_item(crate::local_defs::unique_value_call(func, y)?)?;
            match inner {
                S::StrFind | S::StrRfind => wrapped_search_origin(func, y, 1, fuel),
                S::OptionOkOr | S::OptionOkOrElse => wrapped_search_origin(func, y, 0, fuel),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The search origin of a PAYLOAD local — the `usize` a program binds out of a
/// search result — with the spelling it was bound by.
///
/// Two spellings: the pattern-match read `p = (x as Downcast(v)).0` (a `match`,
/// `if let`, `while let`, or the `?` operator's `Continue` arm), and the
/// panicking extractors `p = Option::unwrap(x)` / `expect` / `Result::unwrap`
/// / `expect`, whose result exists only once the call has RETURNED.
pub(crate) fn str_search_payload_origin(
    func: &VerifiableFunction,
    payload: usize,
) -> Option<(StrSearchOrigin, PayloadSpelling)> {
    use trust_types::SysrootItem as S;
    const FUEL: u32 = 6;
    if crate::local_defs::is_parameter(func, payload)
        || !super::terminator_presence_for(func).has_str_search_item_call
    {
        return None;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, payload) {
        let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
            return None;
        };
        let [trust_types::Projection::Downcast(v), trust_types::Projection::Field(0)] =
            src.projections.as_slice()
        else {
            return None;
        };
        return wrapped_search_origin(func, src.local, *v, FUEL)
            .map(|o| (o, PayloadSpelling::DowncastRead));
    }
    let (item, args) = call_item(crate::local_defs::unique_value_call(func, payload)?)?;
    let v = match item {
        S::OptionUnwrap | S::OptionExpect => 1,
        S::ResultUnwrap | S::ResultExpect => 0,
        _ => return None,
    };
    wrapped_search_origin(func, whole_local(args.first()?)?, v, FUEL)
        .map(|o| (o, PayloadSpelling::ExtractorCall))
}

/// How a payload local was bound — it decides which blocks may carry its fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PayloadSpelling {
    /// `p = (x as V).0`, read in the arm the variant switch sends the value to.
    DowncastRead,
    /// `p = unwrap(x)`: `p` exists only AFTER the call returns, so the call's
    /// own block (whose rows include the extractor's panic row, where the
    /// search may have returned `None`) must not carry the fact.
    ExtractorCall,
}

/// A str range-slice ENDPOINT that is provably a char boundary of the string
/// rooted at one of `roots`, and the linear facts that hold of its value.
///
/// Credited shapes, traced through whole-local `Use` copies (every hop the
/// unique value of its local):
///  * the search payload `i` itself — a match start;
///  * `i + K` (`CheckedBinaryOp(Add)`'s `.0`, or a wrapping `BinaryOp(Add)`),
///    with `K` a CONSTANT equal to the pattern's EXACT match length — the match
///    end.
///
/// The facts are stated on `endpoint_f`, the formula the violation itself reads
/// for this endpoint: `0 <= e` and `e + slack <= len`, where `slack` is the
/// match length still ahead of a match START (`0` for a match end).
pub(crate) fn str_search_endpoint_facts(
    func: &VerifiableFunction,
    endpoint: &Operand,
    roots: &FxHashSet<usize>,
    endpoint_f: &Formula,
    len: &Formula,
) -> Option<Vec<Formula>> {
    if roots.is_empty() || !super::terminator_presence_for(func).has_str_search_item_call {
        return None;
    }
    let mut local = whole_local(endpoint)?;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local) {
            return None;
        }
        match crate::local_defs::unique_value_def(func, local) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                local = q.local;
            }
            // `e = (t).0` with `t = CheckedBinaryOp(Add, a, b)`.
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
                if q.projections.as_slice() == [trust_types::Projection::Field(0)] =>
            {
                let Rvalue::CheckedBinaryOp(BinOp::Add, a, b) =
                    crate::local_defs::unique_value_def(func, q.local)?
                else {
                    return None;
                };
                return match_end_facts(func, a, b, roots, endpoint_f, len);
            }
            Some(Rvalue::BinaryOp(BinOp::Add, a, b)) => {
                return match_end_facts(func, a, b, roots, endpoint_f, len);
            }
            Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src)))
                if matches!(
                    src.projections.as_slice(),
                    [trust_types::Projection::Downcast(_), trust_types::Projection::Field(0)]
                ) =>
            {
                let (origin, _) = str_search_payload_origin(func, local)?;
                return roots
                    .contains(&origin.root)
                    .then(|| endpoint_facts(endpoint_f, len, origin.match_len.lower_bound()));
            }
            Some(_) => return None,
            None => {
                let (origin, _) = str_search_payload_origin(func, local)?;
                return roots
                    .contains(&origin.root)
                    .then(|| endpoint_facts(endpoint_f, len, origin.match_len.lower_bound()));
            }
        }
    }
    None
}

/// `a + b` is a match END: one addend is a search payload over one of `roots`
/// whose EXACT match length is the other addend, a constant.
fn match_end_facts(
    func: &VerifiableFunction,
    a: &Operand,
    b: &Operand,
    roots: &FxHashSet<usize>,
    endpoint_f: &Formula,
    len: &Formula,
) -> Option<Vec<Formula>> {
    let (payload_op, k) = match (a, b) {
        (_, Operand::Constant(ConstValue::Uint(k, _))) => (a, *k),
        (Operand::Constant(ConstValue::Uint(k, _)), _) => (b, *k),
        _ => return None,
    };
    // The addend may reach the payload through whole-local `Use` copies.
    let mut payload = whole_local(payload_op)?;
    let mut origin = None;
    for _ in 0..8 {
        match crate::local_defs::unique_value_def(func, payload) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                payload = q.local;
            }
            Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src)))
                if matches!(
                    src.projections.as_slice(),
                    [trust_types::Projection::Downcast(_), trust_types::Projection::Field(0)]
                ) =>
            {
                origin = str_search_payload_origin(func, payload).map(|(o, _)| o);
                break;
            }
            Some(_) => return None,
            None => {
                origin = str_search_payload_origin(func, payload).map(|(o, _)| o);
                break;
            }
        }
    }
    let origin = origin?;
    if !roots.contains(&origin.root) {
        return None;
    }
    // ONLY the exact match length. `i + 1` after a multi-byte match is the
    // canonical mid-char offset and must stay uncredited.
    let StrMatchLen::Exact(m) = origin.match_len else { return None };
    if i128::try_from(k).ok()? != m {
        return None;
    }
    Some(endpoint_facts(endpoint_f, len, 0))
}

fn endpoint_facts(endpoint_f: &Formula, len: &Formula, slack: i128) -> Vec<Formula> {
    let upper = if slack == 0 {
        endpoint_f.clone()
    } else {
        Formula::Add(Box::new(endpoint_f.clone()), Box::new(Formula::Int(slack)))
    };
    vec![
        Formula::Ge(Box::new(endpoint_f.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(upper), Box::new(len.clone())),
    ]
}

/// Per-block facts for every search payload: `0 <= i`, `i + m <= len(root)`
/// and `len(root) <= isize::MAX` (a live `&str`'s byte length), attached to the
/// blocks that READ `i`. This is what bounds arithmetic on the payload (`i + 1`
/// in `&s[i + 1..]`), which the VC-local endpoint credit cannot reach because
/// the add is its own `Assert` row.
pub(crate) fn build_str_search_payload_fact_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    use trust_types::SysrootItem as S;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !super::terminator_presence_for(func).has_str_search_item_call {
        return map;
    }
    let mut candidates: Vec<usize> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } = stmt
                && place.projections.is_empty()
                && matches!(
                    src.projections.as_slice(),
                    [trust_types::Projection::Downcast(_), trust_types::Projection::Field(0)]
                )
            {
                candidates.push(place.local);
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.projections.is_empty()
            && matches!(
                call_item(&block.terminator),
                Some((S::OptionUnwrap | S::OptionExpect | S::ResultUnwrap | S::ResultExpect, _))
            )
        {
            candidates.push(dest.local);
        }
    }
    if candidates.is_empty() {
        return map;
    }
    if candidates.len() > 1 {
        candidates.sort_unstable();
        candidates.dedup();
    }
    for payload in candidates {
        if !payload_carries_global_fact(func, payload) {
            continue;
        }
        let Some((origin, spelling)) = str_search_payload_origin(func, payload) else { continue };
        let root_op = Operand::Copy(Place::local(origin.root));
        let Some(len) = licensed_slice_len_formula(func, &root_op, 8) else { continue };
        // The root is a shared `&str` (`charindices_shared_slice_root`): its
        // elements are bytes, so its length is at most `isize::MAX`.
        let root_is_byte_slice = matches!(
            crate::local_ty_ref(func, origin.root),
            Some(Ty::Ref { inner, .. })
                if matches!(inner.as_ref(), Ty::Slice { elem } if matches!(elem.as_ref(), Ty::Int { width: 8, .. }))
        );
        let p = Formula::Var(place_to_var_name(func, &Place::local(payload)), Sort::Int);
        let m = origin.match_len.lower_bound();
        let mut facts = vec![
            Formula::Ge(Box::new(p.clone()), Box::new(Formula::Int(0))),
            Formula::Le(
                Box::new(if m == 0 {
                    p
                } else {
                    Formula::Add(Box::new(p), Box::new(Formula::Int(m)))
                }),
                Box::new(len.clone()),
            ),
        ];
        if root_is_byte_slice {
            facts.push(Formula::Le(Box::new(len), Box::new(Formula::Int(i64::MAX as i128))));
        }
        // An extractor call's own block runs BEFORE the value exists (its rows
        // include the extractor's panic row, on the path where the search
        // returned `None`): exclude it, and decline if it cannot be located.
        let def_block = match spelling {
            PayloadSpelling::ExtractorCall => {
                match crate::local_defs::unique_defining_block(func, payload) {
                    Some(index) => Some(index),
                    None => continue,
                }
            }
            PayloadSpelling::DowncastRead => None,
        };
        for (index, block) in func.body.blocks.iter().enumerate() {
            if Some(index) == def_block || !block_mentions_local(block, payload) {
                continue;
            }
            map.entry(block.id).or_default().extend(facts.iter().cloned());
        }
    }
    map
}

/// `true`-branch semantics of an authenticated `str::starts_with` /
/// `str::ends_with` whose result is the switch discriminant `discr`:
/// `len(receiver) >= m` for the pattern's match length `m`. `None` when the
/// discriminant is not such a result or the pattern is not an admitted shape.
pub(crate) fn str_affix_true_len_fact(
    func: &VerifiableFunction,
    discr: &Operand,
) -> Option<Formula> {
    use trust_types::SysrootItem as S;
    let local = whole_local(discr)?;
    if crate::local_defs::is_parameter(func, local)
        || !super::terminator_presence_for(func).has_bare_dest_call
    {
        return None;
    }
    let (item, args) = call_item(crate::local_defs::unique_value_call(func, local)?)?;
    if !matches!(item, S::StrStartsWith | S::StrEndsWith) || args.len() != 2 {
        return None;
    }
    let m = str_pattern_match_len(func, &args[1])?.lower_bound();
    // The receiver's length through the A6–A8 LICENCE, never the bare name:
    // `guards.rs` conjoins this fact at the switch AFTER the version rename, so a
    // bare `{s}__slice_len` would be rebound to whichever version of `s` is
    // terminal there. Adversarial round 1 (probe s91, `-Copt-level=1`):
    // `let b = s.starts_with("abc"); s = t; if b { s.as_bytes()[2] }` — the MIR
    // is `_3 = starts_with(move _1, ..); _1 = copy _2; switchInt(_3)`, the fact
    // `_1__slice_len >= 3` landed on `t`'s length, and both bounds rows were
    // PROVED and kernel-certified while `k("abc", "")` panics.
    let len = licensed_slice_len_formula(func, &args[0], 8)?;
    Some(Formula::Ge(Box::new(len), Box::new(Formula::Int(m))))
}

/// W4 round 3 (2026-09-29): `op` IS (through whole-local `Use` copies, each the
/// unique value of its local) the result of an authenticated `str::len` call — or,
/// since 2026-10-15, the `PtrMetadata` the str-length rewrite turns it into —
/// whose receiver roots to one of `roots` — so its value is the byte length of
/// that string, which is always a char boundary of it. The STRUCTURAL half of the
/// `str::split_at(s.len())` credit (`panic_calls::str_split_at_panic_body`); the
/// `mid <= len` half is the ordinary bounds row, discharged by
/// [`build_str_len_call_tie_facts`]. `roots` must come from
/// `charindices_shared_slice_root` (a shared, single-valued, never mutably
/// borrowed root), so the string measured IS the string split.
pub(crate) fn operand_is_str_len_of_root(
    func: &VerifiableFunction,
    op: &Operand,
    roots: &FxHashSet<usize>,
) -> bool {
    use trust_types::SysrootItem as S;
    if roots.is_empty() {
        return false;
    }
    let Some(mut local) = whole_local(op) else { return false };
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local) {
            return false;
        }
        match crate::local_defs::unique_value_def(func, local) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                local = q.local;
            }
            // Trust (2026-10-15): the str-length rewrite (`rewrite_str_len_calls`) lowers
            // `s.len()` to `PtrMetadata(s)` (a `&str` is extracted as `&[u8]`, whose
            // metadata is its byte length), so the call this arm reads above no longer
            // exists, and `s.split_at(s.len())` was refused as an unmodeled boundary
            // (measured on the stage 1 of the 2026-10-14 merge,
            // `tests/ui/trust/str_split_at_char_boundary.rs#zero_and_len`). The metadata
            // of the same shared, single-valued root IS that string's byte length.
            Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, operand)) => {
                return charindices_shared_slice_root(func, operand)
                    .is_some_and(|r| roots.contains(&r));
            }
            Some(_) => return false,
            None => {
                if super::terminator_presence_for(func).has_bare_dest_call
                    && let Some(term) = crate::local_defs::unique_value_call(func, local)
                {
                    let Some((item, args)) = call_item(term) else { return false };
                    return item == S::StrLen
                        && args.len() == 1
                        && charindices_shared_slice_root(func, &args[0])
                            .is_some_and(|r| roots.contains(&r));
                }
                return false;
            }
        }
    }
    false
}

/// `dest == len(s)` for an authenticated `str::len` / `<[T]>::len` CALL — the
/// definitional tie between the call's result and the receiver's modeled
/// length metadata (`s.len()` IS `s`'s length). A slice `len()` usually lowers
/// to `PtrMetadata` and is tied by the block encoder already; `str::len` stays a
/// call, and without this its result floated free of `s__slice_len`, so a
/// `!s.is_empty()` / `s.starts_with(p)` / `s.find(c)` fact about the length
/// never reached `s.len() - 1`.
///
/// A global fact, sound because the destination is a single static assignment
/// (so the equation constrains only a name that holds exactly this call's
/// value, and is satisfiable by that value everywhere else) and the length is
/// stated through `licensed_slice_len_formula` (the receiver's length name
/// holds one value). Keyed on `SysrootItem::StrLen`/`SliceLen`.
pub(crate) fn build_str_len_call_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use trust_types::SysrootItem as S;
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { dest, args, .. } = &block.terminator else { continue };
        if !dest.projections.is_empty() || args.len() != 1 {
            continue;
        }
        let Some((item, _)) = call_item(&block.terminator) else { continue };
        if !matches!(item, S::StrLen | S::SliceLen)
            || !crate::local_defs::is_single_static_assignment(func, dest.local)
        {
            continue;
        }
        let Some(len) = licensed_slice_len_formula(func, &args[0], 8) else { continue };
        facts.push(Formula::Eq(
            Box::new(Formula::Var(place_to_var_name(func, dest), Sort::Int)),
            Box::new(len),
        ));
    }
    facts
}

/// STR_BYTES_POSITION_BOUND (2026-10-04): the receiver ROOT of an authenticated
/// `Iterator::position` call whose `Self` is pinned to a `str::Bytes` built by an
/// authenticated `str::bytes(root)`.
///
/// `IteratorPosition` names no impl, so `Self` is pinned from the receiver: arg 0 is
/// a whole local `c` whose one value is `&mut it`, `it` was initialised by
/// `str::bytes(s)`, and every `&mut`/`&raw` borrow of `it` is a conduit that feeds
/// ONLY this call's argument 0 ([`super::iterator_yield::iter_mut_borrows_only_feed`]
/// with an admit for this one terminator). So nothing consumed or reseated `it`
/// before `position` (a prior `next()` declines: precision only), and the items it
/// scans are a suffix of `s.as_bytes()`.
fn bytes_position_root(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<usize> {
    position_root_and_iter(func, block).map(|(root, _, _, _)| root)
}

/// [`position_root_and_iter`] restricted to `str::bytes(s).position(..)` — the one
/// shape STR_BYTE_POSITION (the char-boundary credit) may use.
fn bytes_position_root_and_iter(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(usize, usize, usize)> {
    use trust_types::SysrootItem as S;
    match position_root_and_iter(func, block)? {
        (root, it, init_block, (S::StrBytes, S::IteratorPosition)) => Some((root, it, init_block)),
        _ => None,
    }
}

/// [`bytes_position_root`], also answering the iterator local `it` and the index
/// of the block whose call initialised it.
///
/// Widened 2026-10-04: the iterator may also be core's `<[T]>::iter(s)` over a shared
/// slice, and the search `Iterator::rposition`. Every pairing bounds `Some(i)` by
/// `len(s)`: `slice::Iter` overrides both searches with an `i < n` assertion on the
/// remaining length, and `str::Bytes` forwards both to `Copied<slice::Iter<u8>>`,
/// whose default `position` counts consumed items and default `rposition` counts down
/// from the remaining `len()`. Answers
/// `(root, it, init_block, (constructor, search))`.
fn position_root_and_iter(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(usize, usize, usize, (trust_types::SysrootItem, trust_types::SysrootItem))> {
    use trust_types::SysrootItem as S;
    let (search @ (S::IteratorPosition | S::IteratorRposition), [receiver, _]) =
        call_item(&block.terminator)?
    else {
        return None;
    };
    let c = whole_local(receiver)?;
    if crate::local_defs::is_parameter(func, c) {
        return None;
    }
    let Some(Rvalue::Ref { mutable: true, place: it }) =
        crate::local_defs::unique_value_def(func, c)
    else {
        return None;
    };
    if !it.projections.is_empty() || crate::local_defs::is_parameter(func, it.local) {
        return None;
    }
    // `unique_initializing_call` admits a mutable alias of `it`; the conduit gate
    // below is the argument that makes it safe (see its doc's second caller).
    let init = crate::local_defs::unique_initializing_call(func, it.local)?;
    let (constructor @ (S::StrBytes | S::SliceIter), [s_op]) = call_item(init)? else {
        return None;
    };
    let init_block = func.body.blocks.iter().position(|b| std::ptr::eq(&b.terminator, init))?;
    let this = &block.terminator;
    if !super::iterator_yield::iter_mut_borrows_only_feed(func, it.local, |_, term, arg_ix| {
        arg_ix == 0 && std::ptr::eq(term, this)
    }) {
        return None;
    }
    let root = super::iterator_yield::charindices_shared_slice_root(func, s_op)?;
    Some((root, it.local, init_block, (constructor, search)))
}

/// STR_BYTE_POSITION (docs/TCB.md): the search origin of `x = Iterator::position(&mut
/// it, |b| b == K)` — an exact one-byte match of the ASCII byte `K` — or `None`.
///
/// `s.as_bytes()[i] == K < 0x80` makes `i` a char boundary, and `i + 1` either
/// `len(s)` or the start of the next char (a `&str` is valid UTF-8), so `s[i..i + 1]`
/// is a match of exact length 1 and the audited endpoint consumers credit exactly
/// `i` and `i + 1`. Gates, every miss `None`:
///  * the COMPILER certified this very call block (`ascii_eq_bytes_position_call_for`,
///    owner-checked): core's `Iterator::position` on `str::Bytes` with a capture-free
///    closure whose whole body is `item == K`; `K < 0x80` is re-checked here;
///  * `x` is the call's destination, a modeled core `Option<usize>`, read at its
///    `Some` variant `v`;
///  * Fact A's receiver chain ([`bytes_position_root_and_iter`]): `Self` pinned by
///    `&mut it` with `it = str::bytes(s)`, conduits feeding only this call, a shared
///    single-valued root;
///  * the iterator is FRESH and consumed by ONE dynamic execution of the call
///    ([`super::iterator_yield::iter_consumed_once_by`]), so the index is absolute.
fn bytes_position_origin(func: &VerifiableFunction, x: usize, v: usize) -> Option<StrSearchOrigin> {
    let call = crate::local_defs::unique_value_call(func, x)?;
    let call_block = crate::local_defs::unique_defining_block(func, x)?;
    let block = func.body.blocks.get(call_block)?;
    if !std::ptr::eq(&block.terminator, call) {
        return None;
    }
    let k = crate::ascii_eq_bytes_position_call_for(&func.def_path, block.id)?;
    if k >= 0x80 {
        return None;
    }
    let (some_index, _) = core_option_of_usize_some(func, x)?;
    if some_index != v {
        return None;
    }
    let (root, it, init_block) = bytes_position_root_and_iter(func, block)?;
    if !super::iterator_yield::iter_consumed_once_by(func, it, call_block, init_block) {
        return None;
    }
    Some(StrSearchOrigin { root, match_len: StrMatchLen::Exact(1) })
}

/// The `Some` variant index and discriminant of a local typed as the modeled core
/// `Option<usize>` (a 64-bit unsigned payload), or `None`.
fn core_option_of_usize_some(func: &VerifiableFunction, local: usize) -> Option<(usize, i128)> {
    let ty = crate::local_ty_ref(func, local)?;
    let (name, variants) = super::callee_summaries::modeled_std_enum_shape(ty)?;
    if name != "core::option::Option" {
        return None;
    }
    let index = variants.iter().position(|v| v.name == "Some")?;
    let some = &variants[index];
    match some.fields.as_slice() {
        [(_, Ty::Int { width: 64, signed: false })] => Some((index, some.discriminant)),
        _ => None,
    }
}

/// STR_BYTES_POSITION_BOUND (docs/TCB.md): for `dest = Iterator::position(&mut it, p)`
/// (or `rposition`) with `it = str::bytes(s)` or `it = <[T]>::iter(s)` (gated by
/// [`bytes_position_root`]), the fact
///
/// ```text
///   discr(dest) != Some  ∨  (0 <= i ∧ i + 1 <= len(s) [∧ len(s) <= isize::MAX])
/// ```
///
/// where `i` is the `Some` payload pinned to this call's post-call token `s{b}_t`.
/// `str::Bytes::position` forwards to `Copied<slice::Iter<u8>>`, which runs the
/// default `Iterator::position` (a `try_fold` that counts consumed items), so
/// `Some(i)` implies `i < items remaining <= len(s)` for ANY predicate and any
/// prior consumption. In a loop that re-runs the call the index is relative to the
/// remaining suffix and the bound still holds; the guard map's join weakening drops
/// the fact at the loop header in any case. It says nothing about char boundaries:
/// this producer never feeds the str search origin (`str_search_payload_origin`),
/// where a byte position would earn a false boundary credit
/// (`position(|b| b == 0xA9)` on `"é"`).
///
/// It rides only the call's success edge, as a semantic guard. The disjunction is
/// load-bearing: on the `None` arm of `s = ""` an unguarded `i + 1 <= len(s)` is false.
/// Every gate failure emits nothing.
pub(crate) fn str_bytes_position_dest_facts(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    str_bytes_position_dest_fact(sv, func, block).into_iter().collect()
}

fn str_bytes_position_dest_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Formula> {
    let Terminator::Call { args, dest, target: Some(target), .. } = &block.terminator else {
        return None;
    };
    if !dest.projections.is_empty()
        || !matches!(
            call_item(&block.terminator),
            Some((
                trust_types::SysrootItem::IteratorPosition
                    | trust_types::SysrootItem::IteratorRposition,
                [_, _]
            ))
        )
    {
        return None;
    }
    let (some_index, some_discr) = core_option_of_usize_some(func, dest.local)?;
    let root = bytes_position_root(func, block)?;
    if !crate::local_defs::is_single_static_assignment(func, dest.local)
        || !crate::local_defs::dest_fact_is_version_pinnable(func, dest.local)
        || crate::guards::local_is_mutably_borrowed(func, dest.local)
        || super::iterator_yield::local_has_projected_write(func, dest.local)
    {
        return None;
    }
    let dest_name = place_to_var_name(func, dest);
    if super::block_defs::terminator_args_read_name(func, args, &dest_name) {
        return None;
    }
    // The discriminant is read BARE. For a call-written dest it is never versioned
    // (the single-assignment and no-projected-write gates above are what keep it
    // tied to this call); this check is a fail-closed backstop for a body that
    // versions it anyway, and answers true after a budget trip.
    let discr = crate::discriminant_formula_var_name(&dest_name);
    if sv.ever_versioned(func, &discr) {
        return None;
    }
    let payload = place_to_var_name(
        func,
        &Place {
            local: dest.local,
            projections: vec![
                trust_types::Projection::Downcast(some_index),
                trust_types::Projection::Field(0),
            ],
        },
    );
    let Some(tok) = sv.version_token_at(func, *target, 0, &payload) else {
        return None;
    };
    if tok
        .strip_prefix('s')
        .and_then(|s| s.strip_suffix("_t"))
        .and_then(|n| n.parse::<usize>().ok())
        != Some(block.id.0)
    {
        return None;
    }
    let len = licensed_slice_len_formula(func, &Operand::Copy(Place::local(root)), 8)?;
    let len = version_rename_at(&len, sv, func, block.id, block.stmts.len());
    let root_is_byte_slice = matches!(
        crate::local_ty_ref(func, root),
        Some(Ty::Ref { inner, .. })
            if matches!(inner.as_ref(), Ty::Slice { elem } if matches!(elem.as_ref(), Ty::Int { width: 8, .. }))
    );
    // The default lane switches on a LOCAL `d = discriminant(dest)`, not on the
    // canonical symbol (which only the CHC lane reads), and no block def ties the
    // two for a data-carrying enum. So the guard is stated over the canonical
    // symbol AND over every whole local whose one value is `dest`'s discriminant:
    // `dest` is single-assignment and never partially written, so its tag is
    // fixed from the call on, and `d` (single-assignment on every write channel,
    // never borrowed) can only ever hold that tag. `d` IS versioned at its own
    // definition (`d#s{b}_0`), so no never-versioned gate applies to it: every
    // post-definition token of a single-assignment local names that one value, and
    // a re-stamp onto a pre-definition phantom only unconstrains the guard.
    let mut discriminants = vec![discr];
    for b in &func.body.blocks {
        for st in &b.stmts {
            if let Statement::Assign { place: d, rvalue: Rvalue::Discriminant(src), .. } = st
                && src.local == dest.local
                && src.projections.is_empty()
                && d.projections.is_empty()
                && crate::local_defs::is_single_static_assignment(func, d.local)
                && !crate::guards::local_is_mutably_borrowed(func, d.local)
            {
                let name = place_to_var_name(func, d);
                if !discriminants.contains(&name) {
                    discriminants.push(name);
                }
            }
        }
    }
    let p = Formula::Var(format!("{payload}#{tok}"), Sort::Int);
    let mut bound = vec![
        Formula::Ge(Box::new(p.clone()), Box::new(Formula::Int(0))),
        Formula::Le(
            Box::new(Formula::Add(Box::new(p), Box::new(Formula::Int(1)))),
            Box::new(len.clone()),
        ),
    ];
    // A byte slice's length is at most `isize::MAX`; any slice's length is a `usize`.
    let len_max = if root_is_byte_slice { i128::from(i64::MAX) } else { i128::from(u64::MAX) };
    bound.push(Formula::Le(Box::new(len), Box::new(Formula::Int(len_max))));
    let bound = Formula::And(bound);
    Some(Formula::And(
        discriminants
            .into_iter()
            .map(|d| {
                Formula::Or(vec![
                    Formula::Not(Box::new(Formula::Eq(
                        Box::new(Formula::Var(d, Sort::Int)),
                        Box::new(Formula::Int(some_discr)),
                    ))),
                    bound.clone(),
                ])
            })
            .collect(),
    ))
}
