// Integer `TryFrom`/`try_into` conversions and the `unwrap_or` that usually
// follows them. A conversion whose source range provably fits the target is
// infallible, so the `Result` never takes its `Err` arm and the fallback
// constant is dead -- proving that is what keeps the downstream index or
// arithmetic obligation dischargeable.

use super::*;

/// The std fallible conversion `TryFrom::try_from` / `TryInto::try_into`
/// (`u32::try_from(x)`, `x.try_into()`). For the primitive integer -> integer
/// impls it returns `Ok(v as T)` IFF the source value is representable in the
/// target (`MIN_T <= v <= MAX_T`) and `Err(TryFromIntError)` otherwise.
///
/// `safe_def_path_str` resolves such a call to the TRAIT-method spelling
/// `core/std::convert::TryFrom::try_from` (the same behavior `is_bool_from_call`
/// documents for `From::from`); the `TryInto` dual and the fully-qualified impl
/// spellings (`<u32 as core::convert::TryFrom<i64>>::try_from`, or the trimmed
/// `<u32 as TryFrom<i64>>::try_from`) are also accepted. EXACT method tail, so
/// e.g. a hypothetical `try_from_exact` never matches. A user `mymod::try_from`
/// (or a user trait *named* `TryFrom`, which renders with its own crate path)
/// matches none of these anchors and is (soundly) never modeled.
///
/// The CALLER pins the impl family further — an `Int`-sorted final destination
/// plus the `TryFromIntError` Result anchor (`is_int_try_from_result_ty`)
/// restrict to the std primitive-int impls, whose success condition is exactly
/// the range check above (see `int_try_from_unwrap_or_facts` for why each gate
/// is load-bearing).
pub(super) fn is_int_try_from_callee(callee: &str) -> bool {
    matches!(method_tail(callee), "try_from" | "try_into")
        && (callee.contains("core::convert::")
            || callee.contains("std::convert::")
            || callee.contains("as TryFrom<")
            || callee.contains("as TryInto<"))
}

/// The std TOTAL `unwrap_or` (`Result::unwrap_or(default)` /
/// `Option::unwrap_or(default)`): returns the success payload or the passed
/// default — it never panics and runs no user code. EXACT method tail, so
/// `unwrap_or_else` / `unwrap_or_default` (whose defaults run user code the
/// model cannot see) do not match; anchored on the std `Result`/`Option` path
/// (`core::result::Result::<T, E>::unwrap_or` is the `safe_def_path_str`
/// spelling, mirroring the `Result::unwrap` fixtures) so a user
/// `mymod::Thing::unwrap_or` is never modeled.
pub(super) fn is_std_unwrap_or_call(callee: &str) -> bool {
    method_tail(callee) == "unwrap_or"
        && (callee.contains("core::result::Result")
            || callee.contains("std::result::Result")
            || callee.contains("core::option::Option")
            || callee.contains("std::option::Option"))
}

/// `true` iff `ty` (transitively) contains an ADT named
/// `core/std::num::TryFromIntError` — the error type of exactly the std
/// primitive-int `TryFrom` impl family. Fuel-bounded; a compacted/degraded type
/// simply misses (fail-closed).
pub(super) fn ty_mentions_try_from_int_error(ty: &Ty, fuel: u32) -> bool {
    if fuel == 0 {
        return false;
    }
    match ty {
        Ty::Adt { name, fields, variants, .. } => {
            name.ends_with("num::TryFromIntError")
                || fields.iter().any(|(_, t)| ty_mentions_try_from_int_error(t, fuel - 1))
                || variants.iter().any(|v| {
                    v.fields.iter().any(|(_, t)| ty_mentions_try_from_int_error(t, fuel - 1))
                })
        }
        Ty::Datatype { name, variants } => {
            name.ends_with("num::TryFromIntError")
                || variants.iter().any(|(_, fields)| {
                    fields.iter().any(|(_, t)| ty_mentions_try_from_int_error(t, fuel - 1))
                })
        }
        _ => false,
    }
}

/// The Result-type ANCHOR for the composed try_from idiom: the intermediate
/// local's declared type must be the std `Result` (a user enum can never render
/// as `core::result::Result` under `safe_def_path_str`) whose Err side is
/// `TryFromIntError`. This is the discriminating gate for the primitive-int
/// impl family: `char::try_from(u32)` — whose target `char` is MODELED as
/// `Int{32,unsigned}` and so passes the int-dest gate — carries
/// `CharTryFromError` and is rejected here (its success set, the char
/// scalar-value range with the surrogate gap, is NOT the interval
/// `[MIN, MAX]`, so the payload facts would be FALSE for it). The `NonZero*`
/// targets — whose `TryFrom` also uses `TryFromIntError` — are excluded by the
/// caller's int-dest gate instead (`NonZero` lowers to a `core::num::NonZero`
/// `Ty::Adt`, never `Ty::Int`).
pub(super) fn is_int_try_from_result_ty(ty: &Ty) -> bool {
    match ty {
        Ty::Adt { name, .. } | Ty::Datatype { name, .. }
            if name == "core::result::Result" || name == "std::result::Result" =>
        {
            ty_mentions_try_from_int_error(ty, 4)
        }
        _ => false,
    }
}

/// Number of times `local` is READ anywhere in the function — as a whole or
/// projected operand, an observed place (`Ref`/`AddressOf`/`Len`/
/// `Discriminant`/`CopyForDeref`/`SetDiscriminant`/`Drop`), an `Index` inside
/// any place's projections (including a write destination's), a call argument,
/// a `SwitchInt` discriminant, or an `Assert` condition. Assignments TO `local`
/// are not counted. Unknown statement/terminator variants are not counted —
/// the sole consumer requires `== 1` and treats anything else as ambiguous, so
/// an over-count only skips (fail-closed) and an exotic-variant under-count can
/// only relax the SCOPING gate, never a soundness gate (see
/// `int_try_from_unwrap_or_facts`).
pub(super) fn local_operand_use_count(func: &VerifiableFunction, local: usize) -> usize {
    fn place_reads(p: &Place, local: usize) -> usize {
        usize::from(p.local == local)
            + p.projections
                .iter()
                .filter(|proj| matches!(proj, trust_types::Projection::Index(i) if *i == local))
                .count()
    }
    fn op_reads(op: &Operand, local: usize) -> usize {
        match op {
            Operand::Copy(p) | Operand::Move(p) => place_reads(p, local),
            _ => 0,
        }
    }
    // An `Index` projection inside a WRITE destination still reads `local`.
    fn dest_reads(p: &Place, local: usize) -> usize {
        p.projections
            .iter()
            .filter(|proj| matches!(proj, trust_types::Projection::Index(i) if *i == local))
            .count()
    }
    let mut uses = 0usize;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    uses += dest_reads(place, local);
                    uses += match rvalue {
                        Rvalue::Use(op)
                        | Rvalue::UnaryOp(_, op)
                        | Rvalue::Cast(op, _)
                        | Rvalue::Repeat(op, _) => op_reads(op, local),
                        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                            op_reads(a, local) + op_reads(b, local)
                        }
                        Rvalue::Ref { place: p, .. }
                        | Rvalue::AddressOf(_, p)
                        | Rvalue::Discriminant(p)
                        | Rvalue::Len(p)
                        | Rvalue::CopyForDeref(p) => place_reads(p, local),
                        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
                            ops.iter().map(|op| op_reads(op, local)).sum()
                        }
                        _ => 0,
                    };
                }
                Statement::SetDiscriminant { place, .. } => uses += place_reads(place, local),
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                uses += args.iter().map(|op| op_reads(op, local)).sum::<usize>();
                uses += dest_reads(dest, local);
            }
            Terminator::SwitchInt { discr, .. } => uses += op_reads(discr, local),
            Terminator::Assert { cond, .. } => uses += op_reads(cond, local),
            Terminator::Drop { place, .. } => uses += place_reads(place, local),
            _ => {}
        }
    }
    uses
}

/// `true` iff `local`'s VALUE cannot change over the function body: no
/// projected store into it, no `&mut`/`AddressOf` borrow (the same mutation
/// channels `is_single_static_assignment` rejects), and at most one definition
/// COUNTING the implicit entry definition — i.e. ZERO body defs for a
/// PARAMETER (`1..=arg_count`, whose entry value is a def: a parameter with one
/// body store has TWO values, and the emitted fact — versioned at the consuming
/// `unwrap_or` block's terminal — would bind the post-store value, a staleness
/// FALSE fact the `reassigned_source_gets_no_payload_facts` lock pins), and at
/// most one body def for any other local. Used for the try_from SOURCE operand:
/// it must still hold, at the `unwrap_or` block, the value the conversion read.
pub(super) fn local_value_is_stable(func: &VerifiableFunction, local: usize) -> bool {
    let is_param = (1..=func.body.arg_count).contains(&local);
    let mut defs = if is_param { 1u32 } else { 0u32 };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if let Rvalue::Ref { mutable: true, place: borrowed }
                | Rvalue::AddressOf(_, borrowed) = rvalue
                    && borrowed.local == local
                {
                    return false;
                }
                if place.local != local {
                    continue;
                }
                // A store through `Deref` writes the POINTEE, not this local.
                if place.projections.first() == Some(&trust_types::Projection::Deref) {
                    continue;
                }
                if !place.projections.is_empty() {
                    return false;
                }
                defs += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            if !dest.projections.is_empty() {
                return false;
            }
            defs += 1;
        }
    }
    defs <= 1
}

/// Resolve `local` — the receiver of a std `unwrap_or` call — to the unique std
/// `try_from`/`try_into` conversion `Call` that defines it, following at most
/// `fuel` whole-local `Use(Copy|Move)` hops (elaborated MIR inserts
/// `_t = move _r` between the conversion and the consuming call). Every local on
/// the chain must be single-static-assignment and read EXACTLY ONCE (its read
/// being the hop/receiver we arrived through), so the Result value is a pure
/// conduit from the conversion to the `unwrap_or`. Returns the conversion's
/// source operand and the local its `Result` is stored in; `None` on ANY
/// ambiguity (fail-closed havoc, exactly as today).
pub(super) fn int_try_from_def(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<(&Operand, usize)> {
    if fuel == 0 {
        return None;
    }
    if !is_single_static_assignment(func, local) || local_operand_use_count(func, local) != 1 {
        return None;
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if place.local != local || !place.projections.is_empty() {
                continue;
            }
            // THE unique whole-local def (uniqueness guaranteed by the SSA gate
            // above): a whole-local copy/move hop is followed; anything else is
            // not the composed idiom.
            let Rvalue::Use(Operand::Copy(hop) | Operand::Move(hop)) = rvalue else {
                return None;
            };
            if !hop.projections.is_empty() {
                return None;
            }
            return int_try_from_def(func, hop.local, fuel - 1);
        }
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            if is_int_try_from_callee(callee) && args.len() == 1 {
                return Some((&args[0], local));
            }
            return None;
        }
    }
    None
}

/// The try_from SOURCE operand as a formula: an integer constant, or a bare,
/// never-reassigned (and never mut-borrowed) integer local. The stability gate
/// is LOAD-BEARING: the emitted facts are versioned at the consuming
/// `unwrap_or` block's terminal (`version_terminator_dest_fact`), so the source
/// read there must still be the value the conversion consumed (MIR
/// init-before-use guarantees the conversion — the receiver chain's unique def
/// — executed on every path reaching the `unwrap_or`, and a stable local cannot
/// have changed in between).
pub(super) fn int_try_from_source_formula(func: &VerifiableFunction, src: &Operand) -> Option<Formula> {
    match src {
        Operand::Constant(trust_types::ConstValue::Int(_) | trust_types::ConstValue::Uint(..)) => {
            Some(crate::operand_to_formula(func, src))
        }
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            let decl = func.body.locals.iter().find(|d| d.index == p.local)?;
            if !decl.ty.is_integer() || !local_value_is_stable(func, p.local) {
                return None;
            }
            Some(crate::operand_to_formula(func, src))
        }
        _ => None,
    }
}

/// Trust (countdown-loop piece, B0): the composed std idiom
/// `_r = T::try_from(CONST); _d = Result::expect(move _r, msg)` (or `unwrap`)
/// where the conversion SOURCE is an integer CONSTANT that provably fits the
/// target integer type — success-by-construction, so the `expect` CANNOT panic
/// and its result is exactly the constant. This is what the itoa macro fns do
/// for every guard constant and divisor
/// (`999.try_into().expect(..)`, `let scale: Self = 1_00_00.try_into().expect(..)`),
/// leaving them opaque call results without this recognizer. Returns
/// `Some(value)` — used to (a) SUPPRESS the `Call::expect::panic-freedom`
/// obligation, (b) pin the dest's VALUE via the versioned call-dest fact lane,
/// and (c) resolve loop-guard/divisor constants in `build_countdown_trip_facts`.
///
/// SOUNDNESS GATES (ALL hard; any miss -> `None`, keeping the obligation and
/// emitting no fact):
///   * callee tail is exactly `expect`/`unwrap` on the std `Result` path — a
///     user `mymod::Thing::expect` never matches;
///   * the receiver resolves through [`int_try_from_def`]: a bare-local,
///     single-static-assignment, read-exactly-once conduit whose unique def is a
///     std-anchored `try_from`/`try_into` Call (`is_int_try_from_callee` — a
///     user trait named `TryFrom` renders with its own crate path and never
///     matches);
///   * the intermediate Result carries the `TryFromIntError` anchor
///     (`is_int_try_from_result_ty`) — this pins the PRIMITIVE-INT impl family,
///     whose success condition is exactly the target range check
///     (`char::try_from` carries `CharTryFromError` and is rejected; `NonZero*`
///     targets fail the Int-dest gate below);
///   * the `expect` destination is a bare local of a primitive `Ty::Int` — the
///     conversion TARGET type, read from the monomorphized locals table;
///   * the source is an integer CONSTANT evaluated at the exact target width
///     with i128 arithmetic (the i128-const-width lesson: `ConstValue::Int`
///     carries the mathematical value, never a truncation) and the conversion
///     SUCCEEDS. `999 -> u8` FAILS the range check and stays flagged — that
///     `expect` genuinely panics if reached.
pub(super) fn expect_infallible_const_int_conversion(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
) -> Option<i128> {
    if !matches!(method_tail(callee), "expect" | "unwrap") {
        return None;
    }
    if !(callee.contains("core::result::Result") || callee.contains("std::result::Result")) {
        return None;
    }
    if !dest.projections.is_empty() {
        return None;
    }
    let Some(Ty::Int { width, signed }) = func.body.locals.get(dest.local).map(|d| &d.ty).cloned()
    else {
        return None;
    };
    // Receiver: bare local conduit to the unique std try_from/try_into Call.
    let recv = args.first()?;
    let (Operand::Copy(rp) | Operand::Move(rp)) = recv else { return None };
    if !rp.projections.is_empty() {
        return None;
    }
    let (src, r_local) = int_try_from_def(func, rp.local, 4)?;
    if !func.body.locals.get(r_local).is_some_and(|d| is_int_try_from_result_ty(&d.ty)) {
        return None;
    }
    let val: i128 = match src {
        Operand::Constant(trust_types::ConstValue::Int(v)) => *v,
        Operand::Constant(trust_types::ConstValue::Uint(v, _)) => i128::try_from(*v).ok()?,
        _ => return None,
    };
    // Width-exact evaluation of the actual monomorphized conversion.
    let fits = if signed {
        width == 128 || (val >= -(1i128 << (width - 1)) && val <= (1i128 << (width - 1)) - 1)
    } else {
        val >= 0 && (width == 128 || (val as u128) <= (u128::MAX >> (128 - width)))
    };
    fits.then_some(val)
}

/// Trust (countdown-loop piece, B0): whole-function map `expect-dest local ->
/// constant value` for every [`expect_infallible_const_int_conversion`] site
/// whose dest is single-static-assignment (so the local holds the constant on
/// every path after its unique def — the same SSA gate the versioned call-dest
/// fact lane uses). Consumed by `build_countdown_trip_facts` to resolve loop
/// guard constants and divisors through the `try_into().expect()` idiom.
pub(super) fn expect_infallible_const_map(func: &VerifiableFunction) -> FxHashMap<usize, i128> {
    let mut map = FxHashMap::default();
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && let Some(v) = expect_infallible_const_int_conversion(func, callee, args, dest)
            && is_single_static_assignment(func, dest.local)
        {
            map.insert(dest.local, v);
        }
    }
    map
}

/// Precise, SOUND result modeling for the composed std idiom
/// `_r = T::try_from(_x); _d = Result::unwrap_or(move _r, _def)` (integer ->
/// integer). The intermediate `_r` is a `Result<T, TryFromIntError>` ADT the
/// guard-map formula language cannot state payload facts about (a Call dest
/// gets no discriminant/payload pinning — only `Rvalue::Discriminant`
/// STATEMENT reads are modeled), so a LONE `try_from` stays havoc'd
/// (fail-closed) and only the composition — whose final destination `_d` IS
/// Int-sorted — is modeled.
///
/// Emitted facts (theorems of the std impls; the orphan rule forbids any other
/// `TryFrom` impl between primitive ints), in the clamp arm's
/// `Or[¬cond, consequence]` encoding:
///   * in-range:      `MIN_T <= _x <= MAX_T  ->  _d == _x`
///     (`Ok` path: `unwrap_or` yields the payload `_x as T`, value-preserving
///     exactly when in range) as `Or[_x < MIN_T, _x > MAX_T, _d == _x]`;
///   * out-of-range: `!(MIN_T <= _x <= MAX_T) ->  _d == _def`
///     (`Err` path: `unwrap_or` yields the default) as
///     `Or[MIN_T <= _x <= MAX_T, _d == _def]`.
///
/// SOUNDNESS GATES (any miss -> `None`, i.e. today's fail-closed havoc):
///   * callees std-anchored: `is_std_unwrap_or_call` (checked by the CALLER) +
///     `is_int_try_from_callee` — a user `mymod::try_from` never matches;
///   * `_d` is a bare, single-static-assignment local (the CALLER's shared
///     min/max/clamp gate) of type `Ty::Int` with width < 128 (the CALLER's
///     128-bit fail-closed gate, see the emission site);
///   * `_r`'s declared type passes `is_int_try_from_result_ty` — the
///     `TryFromIntError` anchor pinning the primitive-int impl family (this is
///     what excludes `char::try_from`, whose modeled dest type u32 the int-dest
///     gate cannot distinguish);
///   * `_x` is an integer constant or a stable bare local
///     (`int_try_from_source_formula`);
///   * `_r` (and each `_t = move _r` hop temp) is SSA and read exactly once
///     (`int_try_from_def`). The single-use requirement is a SCOPING
///     simplification, NOT a soundness one — the facts are theorems about
///     `_x`/`_d` regardless of other observers of `_r` — it just keeps the
///     modeled Result temp a pure conduit.
pub(super) fn int_try_from_unwrap_or_facts(
    func: &VerifiableFunction,
    args: &[Operand],
    dest_var: &Formula,
    width: u32,
    signed: bool,
) -> Option<[Formula; 2]> {
    let [recv, default] = args else { return None };
    let (Operand::Copy(recv_place) | Operand::Move(recv_place)) = recv else {
        return None;
    };
    if !recv_place.projections.is_empty() {
        return None;
    }
    // The default is typed `T` by rustc; re-check int-ness anyway so a
    // malformed/synthetic IR can never wire a non-integer formula into the
    // equality (fail-closed).
    if !crate::operand_ty_cow(func, default).is_some_and(|t| t.is_integer()) {
        return None;
    }
    let (src, result_local) = int_try_from_def(func, recv_place.local, 4)?;
    let result_decl = func.body.locals.iter().find(|d| d.index == result_local)?;
    if !is_int_try_from_result_ty(&result_decl.ty) {
        return None;
    }
    let src_f = int_try_from_source_formula(func, src)?;
    let default_f = crate::operand_to_formula(func, default);
    let min = crate::range::type_min_formula(width, signed);
    let max = crate::range::type_max_formula(width, signed);
    Some([
        Formula::Or(vec![
            Formula::Lt(Box::new(src_f.clone()), Box::new(min)),
            Formula::Gt(Box::new(src_f.clone()), Box::new(max)),
            Formula::Eq(Box::new(dest_var.clone()), Box::new(src_f.clone())),
        ]),
        Formula::Or(vec![
            crate::range::input_range_constraint(&src_f, width, signed),
            Formula::Eq(Box::new(dest_var.clone()), Box::new(default_f)),
        ]),
    ])
}
