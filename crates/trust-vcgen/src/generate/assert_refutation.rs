// Refutation of the assertion terminators rustc inserts, and of explicit
// `panic!` calls. The message text matters: a panic whose message matches a
// declared contract annotation is a contract obligation, not a stray panic.

use super::*;

/// Trust: locals whose value along any path is an UNCONSTRAINED function input,
/// so leaving them free in a path-feasibility formula is sound (no spurious SAT).
/// A local qualifies iff it is a PARAMETER, or it is assigned EXACTLY ONCE by a
/// pure leaf read — a `Use`/`Copy`/`Move`/`CopyForDeref` of an input-free place
/// (any projection: a field/element/deref of a free aggregate is itself free) or
/// a `Discriminant` of one. A local assigned more than once (a control-flow MERGE,
/// e.g. a clamp `if c {a} else {b}`), via a `Call` terminator, or by any
/// computation (BinaryOp/UnaryOp/Cast/Aggregate) is EXCLUDED: its value is
/// functionally constrained, but that definition is NOT in the path-guard formula,
/// so treating it free would over-approximate and could false-refute.
pub(super) fn v2_input_free_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    // assignment count per BARE local + the sole rvalue (when assigned exactly once)
    let mut assign_count: FxHashMap<usize, usize> = FxHashMap::default();
    let mut sole_rvalue: FxHashMap<usize, &Rvalue> = FxHashMap::default();
    // Read-count per local across EVERY operand/place position, to gate the
    // Call-result-free admission: an argument read ONLY in the allowlisted call
    // cannot decouple the call result from any other constraint.
    let mut read_count: FxHashMap<usize, usize> = FxHashMap::default();
    // An `Opaque`/`Resume` (or any future) terminator may hide reads we cannot
    // see; if one is present we refuse all Call-result admission (conservative —
    // never undercount, which would be unsound).
    let mut unanalyzable = false;
    // Locals taken by `&mut` / `&raw` are NOT input-free: their value can be
    // reassigned through the borrow (`mem::swap(&mut a, ..)`, a setter, `*p = ..`)
    // WITHOUT a direct `Assign`, so the single-assignment leaf-read rule would
    // model a STALE pre-mutation value and could false-refute (the `&mut`/AddressOf
    // staleness class — see the hunt-5/7/8 lessons). Exclude their base locals.
    let mut mut_borrowed: FxHashSet<usize> = FxHashSet::default();
    // Allowlisted "free-payload extractor" calls: (dest.local, arg locals). The
    // result of `Try::branch(r)` (the `?` operator) / `<[T]>::get(s, i)` is an
    // unconstrained projection of its input-free receiver, so its payload ranges
    // freely with the inputs.
    let mut payload_calls: Vec<(usize, Vec<usize>)> = Vec::new();
    let bump = |local: usize, rc: &mut FxHashMap<usize, usize>| {
        *rc.entry(local).or_insert(0) += 1;
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if place.projections.is_empty() {
                    *assign_count.entry(place.local).or_insert(0) += 1;
                    sole_rvalue.insert(place.local, rvalue);
                } else {
                    // a projected store (`a.0 = ..`, `*a = ..`) mutates the base
                    // local's value WITHOUT a direct assign — exclude it from
                    // input-free outright (covers even a parameter, which the
                    // single-assignment rule would otherwise admit) so the
                    // post-mutation value is never modelled as a free leaf.
                    *assign_count.entry(place.local).or_insert(0) += 2;
                    mut_borrowed.insert(place.local);
                }
                match rvalue {
                    // single operand or single place read (one local).
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::UnaryOp(_, Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::Cast(Operand::Copy(p) | Operand::Move(p), _)
                    | Rvalue::Repeat(Operand::Copy(p) | Operand::Move(p), _)
                    | Rvalue::Ref { mutable: false, place: p }
                    | Rvalue::Discriminant(p)
                    | Rvalue::Len(p)
                    | Rvalue::CopyForDeref(p) => bump(p.local, &mut read_count),
                    // a `&mut` / raw `&raw` borrow READS and may MUTATE the base
                    // local through the borrow — exclude it from input-free.
                    Rvalue::Ref { mutable: true, place: p } | Rvalue::AddressOf(_, p) => {
                        bump(p.local, &mut read_count);
                        mut_borrowed.insert(p.local);
                    }
                    Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                        for op in [a, b] {
                            if let Operand::Copy(p) | Operand::Move(p) = op {
                                bump(p.local, &mut read_count);
                            }
                        }
                    }
                    Rvalue::Aggregate(_, ops) => {
                        for op in ops {
                            if let Operand::Copy(p) | Operand::Move(p) = op {
                                bump(p.local, &mut read_count);
                            }
                        }
                    }
                    // Constant/Symbolic/Unsupported operands read no tracked local.
                    _ => {}
                }
            }
        }
        match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } => {
                // a Call result is a COMPUTED value; never input-free by the
                // leaf-read rule (admitted only by the allowlist pass below).
                *assign_count.entry(dest.local).or_insert(0) += 2;
                for op in args {
                    if let Operand::Copy(p) | Operand::Move(p) = op {
                        bump(p.local, &mut read_count);
                    }
                }
                // `?`-operator desugar (`<R as Try>::branch`) and slice `get`. Use
                // `method_tail` so the `<.. as Try>::` / turbofish qualifier does not
                // defeat the match; the `Try` / `slice` guard keeps it specific.
                let tail = method_tail(callee);
                let is_extractor = (tail == "branch" && callee.contains("Try"))
                    || (tail == "get" && callee.contains("slice"));
                if is_extractor && dest.projections.is_empty() {
                    let arg_locals: Vec<usize> = args
                        .iter()
                        .filter_map(|a| match a {
                            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                            _ => None,
                        })
                        .collect();
                    payload_calls.push((dest.local, arg_locals));
                }
            }
            Terminator::SwitchInt { discr, .. } => {
                if let Operand::Copy(p) | Operand::Move(p) = discr {
                    bump(p.local, &mut read_count);
                }
            }
            Terminator::Assert { cond, .. } => {
                if let Operand::Copy(p) | Operand::Move(p) = cond {
                    bump(p.local, &mut read_count);
                }
            }
            Terminator::Drop { place, .. } => bump(place.local, &mut read_count),
            Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => {}
            _ => unanalyzable = true,
        }
    }
    // Parameters (locals 1..=arg_count) are the base input-free set — EXCEPT any
    // that are `&mut`-borrowed (reassignable through the borrow). Grow to a
    // fixpoint over single-assignment leaf reads of input-free places, plus
    // allowlisted Call-result payloads; a `&mut`-borrowed local is never admitted.
    let mut safe: FxHashSet<usize> =
        (1..=func.body.arg_count).filter(|l| !mut_borrowed.contains(l)).collect();
    loop {
        let mut changed = false;
        for (&local, &count) in &assign_count {
            if safe.contains(&local) || count != 1 || mut_borrowed.contains(&local) {
                continue;
            }
            let leaf = match sole_rvalue.get(&local) {
                // a pure read: copy/move of an input-free place (ANY projection —
                // a field/element/deref of a free aggregate is itself free), a
                // constant, or a discriminant of an input-free place.
                Some(Rvalue::Use(Operand::Constant(_))) => true,
                Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                | Some(Rvalue::Discriminant(p))
                | Some(Rvalue::CopyForDeref(p)) => safe.contains(&p.local),
                // BinaryOp/UnaryOp/Cast/Aggregate/Ref/Len/… constrain the value.
                _ => false,
            };
            if leaf {
                safe.insert(local);
                changed = true;
            }
        }
        // Call-result-free admission: an allowlisted payload extractor whose every
        // arg is an input-free PARAMETER read ONLY in this call (so the result's
        // value is unconstrained elsewhere — no decoupling).
        if !unanalyzable {
            for (dest, arg_locals) in &payload_calls {
                if safe.contains(dest) || mut_borrowed.contains(dest) {
                    continue;
                }
                let ok = !arg_locals.is_empty()
                    && arg_locals.iter().all(|&a| {
                        (1..=func.body.arg_count).contains(&a)
                            && safe.contains(&a)
                            && read_count.get(&a).copied().unwrap_or(0) <= 1
                    });
                if ok {
                    safe.insert(*dest);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    safe
}

/// Trust: `-full`-only, refute-only path-feasibility VCs for user `assert!` /
/// `panic!` failure sites.
///
/// For each panic-call terminator block, build the path-feasibility formula — the
/// conjunction of branch guards reaching that block, which (since the block is
/// entered exactly when the assertion FAILS) IS the violation condition. Emit it
/// ONLY when every free variable is INPUT-FREE (`v2_input_free_locals`): a
/// parameter, or a single-assignment leaf read of an input (an enum/struct
/// payload field, a pinned discriminant). Then an ay SAT verdict is a genuine
/// counterexample (a real input drives execution to the panic). A panic site
/// whose reachability depends on a COMPUTED intermediate (e.g. a `clamp` value
/// merged across blocks, or a `s.get(i)` call result) is EXCLUDED — its defining
/// computation is not threaded here, so leaving it free could be spuriously SAT
/// and false-refute a guarded-safe assert. Excluding it is sound (the obligation
/// simply stays runtime-checked), never a false refutation.
///
/// Returned SEPARATELY from `generate_vcs` and consumed ONLY by the strict
/// `-full` path (see `refute_full_assert_obligations`), so DEFAULT mode never
/// sees these: a reachable `assert!` panic is valid, drop-in Rust and must stay
/// runtime-checked by default. Refute-only: the caller acts on an ay `Failed`
/// (SAT) and discards everything else, so it can never turn into a proof.
/// Trust: model a defined-behavior `wrapping_{add,sub}` method Call as an EXACT
/// modular DEFINITION of its destination, so an `assert!` whose condition compares
/// the result can GROUND and be decided (otherwise the result temp — a
/// `Terminator::Call` dest, invisible to the statement-based block-definition
/// extractor — stays an unconstrained free var and the obligation is dropped as
/// ungrounded, falling back to runtime-checked).
///
/// Unlike `overflow_arith_call` (UB-on-overflow intrinsics that carry an
/// obligation), `wrapping_*` wraps by definition and needs no obligation. The
/// model is the single-`Ite` modular reduction at the operand width, kept in
/// Int/LIA so ay decides it directly:
///   `wrapping_add(a,b) == ite(a+b >= 2^w, a+b - 2^w, a+b)`
///   `wrapping_sub(a,b) == ite(a-b <  0,   a-b + 2^w, a-b)`
/// This is FAITHFUL: the unsound unbounded `a+b` would false-PROVE
/// `assert!(a.wrapping_add(1) > a)` at `a == MAX` (where the real result wraps to
/// 0). Returns `(Eq(dest, ite), operand-range facts)`; the caller conjoins the
/// ranges only when the def is used, so the refute direction cannot pick an
/// out-of-range operand and spuriously fail a valid assert. add/sub at width <= 64
/// (u8..=u64 / i8..=i64 / usize / isize), BOTH unsigned (single-Ite reduction) and
/// signed (two's-complement two-sided wrap); `mul` (full nonlinear mod) and wider
/// types (u128/i128) return `None`, leaving such asserts ungrounded (sound:
/// dropped, never mis-decided).
/// The bitvector op and carrier carried by an authenticated
/// `wrapping_{add,sub}` marker. Raw method suffixes are deliberately rejected:
/// they are source-spellable and therefore cannot establish call identity.
fn authenticated_wrapping_call(
    callee: &str,
) -> Option<(BinOp, trust_types::RustcWrappingRefutationCarrier)> {
    if callee.starts_with(trust_types::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX) {
        return match trust_types::RustcTotalPrimitiveMethod::classify(callee)? {
            trust_types::RustcTotalPrimitiveMethod::WrappingAdd(width) => Some((
                BinOp::Add,
                trust_types::RustcWrappingRefutationCarrier::Fixed { width, signed: false },
            )),
            trust_types::RustcTotalPrimitiveMethod::WrappingSub(width) => Some((
                BinOp::Sub,
                trust_types::RustcWrappingRefutationCarrier::Fixed { width, signed: false },
            )),
            trust_types::RustcTotalPrimitiveMethod::WrappingMul(_) => None,
        };
    }
    let method = trust_types::RustcWrappingRefutationMethod::classify(callee)?;
    let op = match method.op {
        trust_types::RustcWrappingRefutationOp::Add => BinOp::Add,
        trust_types::RustcWrappingRefutationOp::Sub => BinOp::Sub,
    };
    Some((op, method.carrier))
}

pub(super) fn wrapping_call_tail_op(callee: &str) -> Option<BinOp> {
    authenticated_wrapping_call(callee).map(|(op, _)| op)
}

fn wrapping_carrier_destination(
    carrier: trust_types::RustcWrappingRefutationCarrier,
    destination: &Ty,
) -> Option<(u32, bool)> {
    match (carrier, destination) {
        (
            trust_types::RustcWrappingRefutationCarrier::Fixed {
                width: expected_width,
                signed: expected_signed,
            },
            Ty::Int { width, signed },
        ) if *width == expected_width && *signed == expected_signed => Some((*width, *signed)),
        (
            trust_types::RustcWrappingRefutationCarrier::PointerSized {
                signed: expected_signed,
            },
            Ty::PtrSizedInt { signed },
        ) if *signed == expected_signed => Some((destination.int_width()?, *signed)),
        // The production verifier extraction lane still carries usize/isize as
        // its pinned 64-bit `Ty::Int` representation. The compiler-authenticated
        // marker retains the lost pointer-sized identity; accepting that one
        // legacy spelling preserves existing source precision. Fixed u64/i64
        // and pointer-sized arithmetic have identical modular semantics at this
        // width. Faithful serialized IR uses `PtrSizedInt` and is checked by the
        // exact arm above.
        (
            trust_types::RustcWrappingRefutationCarrier::PointerSized {
                signed: expected_signed,
            },
            Ty::Int { width: 64, signed },
        ) if *signed == expected_signed => Some((64, *signed)),
        _ => None,
    }
}

fn signed_constant_fits_width(value: i128, width: u32) -> bool {
    if width == 128 {
        return true;
    }
    if !(1..128).contains(&width) {
        return false;
    }
    let bound = 1i128 << (width - 1);
    (-bound..bound).contains(&value)
}

fn unsigned_constant_fits_width(value: u128, width: u32) -> bool {
    (1..=128).contains(&width) && (width == 128 || value < (1u128 << width))
}

fn wrapping_operand_matches_destination(
    func: &VerifiableFunction,
    operand: &Operand,
    destination: &Ty,
    width: u32,
    signed: bool,
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            crate::place_ty_cow(func, place).is_some_and(|actual| actual.as_ref() == destination)
        }
        // MIR integer constants retain their value but signed constants do not
        // retain their narrow width, and legacy usize constants retain only the
        // pinned target width. Validate representability against the
        // authenticated destination rather than fabricating i64/u64 identity.
        Operand::Constant(ConstValue::Int(value)) if signed => {
            signed_constant_fits_width(*value, width)
        }
        Operand::Constant(ConstValue::Uint(value, encoded_width)) if !signed => {
            *encoded_width == width && unsigned_constant_fits_width(*value, width)
        }
        // Typed opaque/const-param values still carry exact type metadata.
        _ => crate::operand_ty_cow(func, operand)
            .is_some_and(|actual| actual.as_ref() == destination),
    }
}

pub(super) fn wrapping_call_assert_model(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    dest: &Place,
    has_normal_return_target: bool,
    has_atomic_metadata: bool,
    is_foreign: bool,
    is_unsafe_sig: bool,
) -> Option<(Formula, Vec<Formula>)> {
    // The marker authenticates the selected DefId, not independently mutable
    // call-site metadata. A modular destination definition is valid only for
    // the ordinary safe Rust call shape that the compiler actually extracted.
    // `unwind` is deliberately not a gate: the authenticated method is total,
    // and this refutation CFG follows only the normal-return target; rustc may
    // retain an unreachable `Continue`/cleanup annotation on such a call.
    if !has_normal_return_target || has_atomic_metadata || is_foreign || is_unsafe_sig {
        return None;
    }
    let (op, carrier) = authenticated_wrapping_call(callee)?;
    if args.len() != 2 {
        return None;
    }
    let lhs = args.first()?;
    let rhs = args.get(1)?;
    let dest_ty = crate::place_ty_cow(func, dest)?;
    let (width, signed) = wrapping_carrier_destination(carrier, dest_ty.as_ref())?;
    if !wrapping_operand_matches_destination(func, lhs, dest_ty.as_ref(), width, signed)
        || !wrapping_operand_matches_destination(func, rhs, dest_ty.as_ref(), width, signed)
    {
        return None;
    }
    // width <= 64 covers u8..=u64 / i8..=i64 / usize / isize. The cap keeps the
    // modulus `1i128 << width` (= 2^width) within i128 (it overflows near width 127);
    // u128/i128 wrapping stays unhandled (returns None -> dropped, sound).
    if width > 64 {
        return None;
    }
    let modulus = Formula::Int(1i128 << width);
    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
    let s = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        _ => return None,
    };
    let ite = if signed {
        // Two's-complement wrap into [min, max]: the sum/difference of two in-range
        // signed values lands in [2*min, 2*max] (add) / [min-max, max-min] (sub),
        // so it wraps AT MOST ONCE past either bound. `ite(s>max, s-2^w, ite(s<min,
        // s+2^w, s))` is faithful; range facts (signed) keep both operands in band.
        let max = crate::range::type_max_formula(width, true);
        let min = crate::range::type_min_formula(width, true);
        Formula::Ite(
            Box::new(Formula::Gt(Box::new(s.clone()), Box::new(max))),
            Box::new(Formula::Sub(Box::new(s.clone()), Box::new(modulus.clone()))),
            Box::new(Formula::Ite(
                Box::new(Formula::Lt(Box::new(s.clone()), Box::new(min))),
                Box::new(Formula::Add(Box::new(s.clone()), Box::new(modulus))),
                Box::new(s),
            )),
        )
    } else {
        // Unsigned single-Ite reduction at the operand width.
        match op {
            BinOp::Add => Formula::Ite(
                Box::new(Formula::Ge(Box::new(s.clone()), Box::new(modulus.clone()))),
                Box::new(Formula::Sub(Box::new(s.clone()), Box::new(modulus))),
                Box::new(s),
            ),
            // wrapping_sub unsigned: borrow when the difference goes negative.
            _ => Formula::Ite(
                Box::new(Formula::Lt(Box::new(s.clone()), Box::new(Formula::Int(0)))),
                Box::new(Formula::Add(Box::new(s.clone()), Box::new(modulus))),
                Box::new(s),
            ),
        }
    };
    let def = Formula::Eq(Box::new(dest_var), Box::new(ite));
    let ranges = vec![
        crate::range::input_range_constraint(&lhs_f, width, signed),
        crate::range::input_range_constraint(&rhs_f, width, signed),
    ];
    Some((def, ranges))
}

fn wrapping_result_local_is_stable(
    func: &VerifiableFunction,
    dest: &Place,
    call_def_count: usize,
) -> bool {
    dest.projections.is_empty()
        && call_def_count == 1
        // Counting call destinations alone is insufficient: a statement write
        // on another path or mutation through `&mut` can give the assertion's
        // reaching version a value unrelated to this wrapping call. The model
        // is renamed at the assertion use point, so admitting such a local can
        // manufacture a modular equation for the competing definition and a
        // false SAT counterexample.
        && !crate::guards::value_local_is_unstable(func, dest.local)
}

pub fn generate_full_assert_refutation_vcs(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    generate_full_assert_refutation_vcs_with_context(func, &context)
}

/// Generate full-mode assertion-refutation VCs under explicit function policy.
/// Contract-panic annotations are consumed only when `context` owns `func`.
pub fn generate_full_assert_refutation_vcs_with_context(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> Vec<VerificationCondition> {
    crate::with_function_vcgen_context(&func.def_path, context, || {
        generate_full_assert_refutation_vcs_impl(func)
    })
}

pub(super) fn generate_full_assert_refutation_vcs_impl(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    if let Err(error) = crate::validate_function(func) {
        return vec![malformed_trust_ir_vc(func, &error)];
    }

    // verifier-perf: hold the mid-generation work-meter scope; this path materializes
    // declared types via owned place-type queries too (`place_to_var_name`, path
    // defs). Resets on the outermost entry. SOUNDNESS: DROP-ONLY (see the trip
    // check before the return).
    let _gen_work_scope = crate::gen_work_scope();
    // verifier-perf (whole-function gate): an over-budget recursive-datatype function
    // explodes `StmtVersionCtx::build` / path-def machinery below. Emit NO refutation
    // claims for it. SOUNDNESS: withholding a refutation is the fail-closed direction (it
    // can only DROP a refutation, never manufacture one) — DROP-ONLY.
    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    // This public lane can be invoked independently of `generate_vcs_impl`, so
    // sanitize its direct precondition consumption at its own boundary too.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    let sv = StmtVersionCtx::build(func);
    let guard_paths_map = v2_build_path_guard_map(func);
    // The formula var names whose value is an UNCONSTRAINED function input, so it
    // is sound to leave them free in a path-feasibility formula (no spurious SAT):
    // parameters and single-assignment leaf reads of inputs (e.g. an enum/struct
    // payload field `o.0` or a `Discriminant(o)`). A computed/merged intermediate
    // (e.g. a clamp `if c {a} else {b}` or a `s.get(i)` call result) is excluded —
    // its constraining definition is absent from the path-guard formula.
    let input_free = v2_input_free_locals(func);
    let safe_names: FxHashSet<String> = (0..func.body.locals.len())
        .filter(|local| input_free.contains(local))
        .map(|local| crate::place_to_var_name(func, &Place { local, projections: Vec::new() }))
        .collect();
    // Per-block path-definition facts (branch-merge `x == Ite(..)` invariants,
    // enum/struct-payload definitions, `?`-Try payloads). Conjoining a relevant
    // one PINS an otherwise-free computed/merged value to an input-free expression,
    // so it is resolved rather than spuriously free. Monotone-sound (true equalities
    // only shrink the model set).
    let path_defs = v2_build_path_definition_map(func);
    // Trust: wrapping-call result DEFINITIONS — `(Eq(dest, modular-ite), operand
    // range facts)` for each `wrapping_{add,sub}` whose result temp is a
    // `Terminator::Call` dest (invisible to the statement/path-def extractors, so
    // without this the comparing assert is dropped as ungrounded). Sound ONLY when
    // the dest local is SINGLE-assignment (one Call def — else its value is
    // path-dependent) and every operand is an input-free leaf (so the modular
    // identity `dest == wrap(op(a,b))` holds at every reaching-def version). The
    // range facts are conjoined by the resolution loop only when the def is used,
    // keeping the refute direction from picking an out-of-range operand.
    let wrap_call_def_count: FxHashMap<usize, usize> = {
        let mut c: FxHashMap<usize, usize> = FxHashMap::default();
        for b in &func.body.blocks {
            if let Terminator::Call { dest, .. } = &b.terminator {
                *c.entry(dest.local).or_default() += 1;
            }
        }
        c
    };
    // Locals that are SINGLE-assignment `wrapping_{add,sub}` results. A wrap result
    // is defined once, so its value is fixed — it is a SAFE operand for an OUTER
    // wrapping op (CHAINED wrapping, e.g. `a.wrapping_add(b).wrapping_add(c)` or
    // `head.wrapping_add(n).wrapping_sub(n)`). The resolution fixpoint grounds the
    // inner model first, then the outer, bottoming out in input-free leaves; if a
    // chain does not bottom out the grounding check fails and the assert is dropped
    // (sound). The inner result's u32 range is conjoined by the outer model's
    // operand-range facts, so the single-Ite modular reduction stays faithful.
    let wrap_dest_locals: FxHashSet<usize> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| {
            let Terminator::Call {
                func: callee,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } = &b.terminator
            else {
                return None;
            };
            (wrapping_result_local_is_stable(
                func,
                dest,
                wrap_call_def_count.get(&dest.local).copied().unwrap_or(0),
            )
                && target.is_some()
                && atomic.is_none()
                && !*is_foreign
                && !*is_unsafe_sig
                && wrapping_call_tail_op(callee).is_some())
            .then_some(dest.local)
        })
        .collect();
    let wrap_models: Vec<(Formula, Vec<Formula>)> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| {
            let Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } = &b.terminator
            else {
                return None;
            };
            if !wrapping_result_local_is_stable(
                func,
                dest,
                wrap_call_def_count.get(&dest.local).copied().unwrap_or(0),
            ) {
                return None;
            }
            let operands_ok = args.iter().take(2).all(|a| match a {
                Operand::Constant(_) => true,
                // An operand is a SAFE (stable) leaf when it is an input-free read OR
                // itself a single-assignment wrapping result (chained wrapping).
                Operand::Copy(p) | Operand::Move(p) => {
                    p.projections.is_empty()
                        && (input_free.contains(&p.local) || wrap_dest_locals.contains(&p.local))
                }
                // `Operand` is #[non_exhaustive]: an unrecognized operand is treated
                // as unsafe, so the model is skipped (fail-closed).
                _ => false,
            });
            if !operands_ok {
                return None;
            }
            wrapping_call_assert_model(
                func,
                callee,
                args,
                dest,
                target.is_some(),
                atomic.is_some(),
                *is_foreign,
                *is_unsafe_sig,
            )
        })
        .collect();
    // STRAIGHT-LINE definition grounding (XOR / cast / checked-arith assert path).
    // The path-feasibility formula for a user `assert!` over computed bool/integer
    // intermediates (e.g. `r == (((a as u8) + ..) % 2 == 1)`) has free vars that are
    // NOT branch-merge Ites / enum payloads / wrapping-call models — they are the
    // ordinary straight-line statement results: bool `BitXor`/`Cast` defs and the
    // `CheckedBinaryOp` overflow flag `_N.1`. The checked result `_N.0` is
    // edge-sensitive: its unbounded mathematical equation is true only after the
    // no-overflow Assert succeeds, so it comes exclusively from `path_defs` above.
    // Without pinning the remaining straight-line values the
    // assert is dropped as ungrounded and the typed CHC/PDR route returns Unsupported
    // -> UNKNOWN. Collect each block's statement definitions (`extract_block_definitions`,
    // which already lowers bool `BitXor` to `dest == (l != r)` and bool->int casts to
    // `dest == Ite(b, 1, 0)`) PLUS the checked-add flag semantics
    // (`extract_overflow_flag_semantics` — the `.1` overflow-flag def the statement
    // extractor deliberately skips), gated to function-wide SINGLE-ASSIGNMENT vars.
    //
    // SOUNDNESS: each def is conjoined only after `version_rename_at` at the assert
    // use-point (below). For a var defined exactly once in the whole function its
    // reaching-def version is unique at EVERY program point, so the use-point-versioned
    // equality equals the def-point equality — a genuine function-wide true fact
    // (monotone: only shrinks the model set, so it can manufacture neither a spurious
    // UNSAT/false-prove nor a spurious SAT/false-refute). A def any of whose vars is NOT
    // single-assignment-or-input is DROPPED (fail-closed), so a value a later
    // reassignment could falsify never enters the conjunction. The relevance slice below
    // still conjoins only fv-reachable defs; the terminal discharge stays in
    // `refute_full_assert_obligations` -> `InProcessAyBackend` (Proved only on a
    // strict-checked ay UNSAT-of-negation artifact). This is the same soundness argument
    // as `wrap_models` / path-defs, restricted further by the single-assignment gate.
    let single_assign_names: FxHashSet<String> = {
        let mut count: FxHashMap<usize, usize> = FxHashMap::default();
        for b in &func.body.blocks {
            for stmt in &b.stmts {
                if let Statement::Assign { place, .. } = stmt
                    && place.projections.is_empty()
                {
                    *count.entry(place.local).or_default() += 1;
                }
            }
            if let Terminator::Call { dest, .. } = &b.terminator
                && dest.projections.is_empty()
            {
                *count.entry(dest.local).or_default() += 1;
            }
        }
        count
            .into_iter()
            // Trust (P0 call-arg &mut staleness, assert-refute lane): a local with a
            // single DIRECT store can still be MUTATED through a `&mut`/`&raw mut`
            // borrow that escapes into a call (`set(&mut a, v)`, `mem::swap`), so its
            // single-assignment `Eq(a, init)` fact is STALE after the call. Treating
            // it as stable let the assert-refute grounder pin `a` to its pre-call
            // value (`let mut a = x; set(&mut a, v); assert!(a == v)` GROUNDED `a` to
            // `x`, refuting the always-true `a == v` — a false REFUTATION of valid
            // Rust). Exclude mutably-borrowed locals; `value_local_is_unstable` is the
            // SAME predicate the bounds/upper-bound staleness gates use, so the
            // refute lane and the proof lane agree on what is reassignable. SOUND:
            // dropping a fact only DROPS a refutation (fail-closed) — it can never
            // manufacture a refutation or a proof.
            .filter(|(local, c)| *c == 1 && !crate::guards::value_local_is_unstable(func, *local))
            .map(|(local, _)| {
                crate::place_to_var_name(func, &Place { local, projections: Vec::new() })
            })
            .collect()
    };
    // The base place name of a (possibly versioned / field-projected) formula var:
    // strip the `#sN_M` reaching-def token and any trailing numeric `.k` field
    // projection (a tuple field `_N.0` / `_N.1` is stable iff its base tuple local `_N`
    // is single-assignment).
    fn def_base_name(v: &str) -> &str {
        let mut s = v.split('#').next().unwrap_or(v);
        while let Some(dot) = s.rfind('.') {
            if dot + 1 < s.len() && s[dot + 1..].bytes().all(|b| b.is_ascii_digit()) {
                s = &s[..dot];
            } else {
                break;
            }
        }
        s
    }
    let var_stable = |v: &str| {
        safe_names.contains(v)
            || safe_names.contains(def_base_name(v))
            || single_assign_names.contains(def_base_name(v))
    };
    let def_stable = |d: &Formula| d.free_variables().iter().all(|v| var_stable(v));
    // `(Eq-def, range-facts)` candidates, UNVERSIONED here (renamed per assert site).
    let mut stmt_defs: Vec<(Formula, Vec<Formula>)> = Vec::new();
    for b in &func.body.blocks {
        for d in guards::extract_block_definitions(func, b) {
            if matches!(&d, Formula::Eq(..)) && def_stable(&d) {
                stmt_defs.push((d, Vec::new()));
            }
        }
        // `extract_overflow_flag_semantics` = `[_N.1 <=> overflow, lhs_range,
        // rhs_range]`. Keep the flag Eq, attaching the operand range facts so
        // they ride along when it is used. The success-only `_N.0 == lhs OP rhs`
        // equation must come from this assert site's edge-sensitive `path_defs`.
        let ofs = guards::extract_overflow_flag_semantics(func, b);
        let (eqs, ranges): (Vec<&Formula>, Vec<&Formula>) =
            ofs.iter().partition(|f| matches!(f, Formula::Eq(..)));
        let ranges: Vec<Formula> = ranges.into_iter().filter(|r| def_stable(r)).cloned().collect();
        for d in eqs {
            if def_stable(d) {
                stmt_defs.push((d.clone(), ranges.clone()));
            }
        }
    }
    // Trust (derived trivial-setter summary — the COMPLETENESS half of the P0
    // staleness fix documented on `single_assign_names` above): that fix
    // correctly excludes a mut-borrowed local from the stable-def channels, so
    // after `set(&mut a, v)` the grounder no longer pins `a` to its STALE
    // pre-call value — but it then knows NOTHING about `a`, so the always-true
    // `assert!(a == v)` stays ungrounded and demotes to runtime-checked. When
    // the callee is a RECOGNIZED trivial setter, the post-call value is exact:
    // conjoin `a#s{b}_t == v` (`trivial_setter_callsite_fact` — versioned at
    // the call terminator, name-disjoint from every pre-call/stale read), plus
    // the copy-chain links `dst == a` for whole-local copies OF THE SETTER
    // TARGET, each versioned at ITS OWN establish point
    // (`version_block_def_at_establish`: reads at the def's read-point, subject
    // at the def's write-point) so each is a TRUE per-snapshot fact — a copy
    // reading the PRE-call value names `a#<pre>` and stays name-disjoint from
    // the setter fact (inert), never falsely connected. Both polarities stay
    // sound: true facts cannot exclude a genuine counterexample snapshot (a
    // real refutation stays SAT) and UNSAT still means no execution reaches
    // the panic. Fail-closed: no recognized setter call ⇒ empty ⇒ unchanged.
    // UNVERSIONED derived-setter facts + copy-chain links. Each is versioned at the
    // ASSERT use-point below (via `version_rename_at`, exactly like `stmt_defs`), so
    // the target's token unifies with the assert formula's own reaching-def token by
    // construction — robust to the trust-ir flip's re-versioning (the pre-pinned
    // terminator token did not survive it). Staleness stays caught: a pre-call read
    // versions to a different reaching-def token and the fact stays inert.
    let setter_defs: Vec<Formula> = {
        let mut defs: Vec<Formula> = Vec::new();
        let mut targets: FxHashSet<usize> = FxHashSet::default();
        for b in &func.body.blocks {
            if let Some((target, fact)) = trivial_setter_callsite_fact_unversioned(func, b) {
                defs.push(fact);
                targets.insert(target);
            }
        }
        for target in targets {
            for cb in &func.body.blocks {
                for stmt in &cb.stmts {
                    let Statement::Assign {
                        place,
                        rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                        ..
                    } = stmt
                    else {
                        continue;
                    };
                    if !place.projections.is_empty()
                        || !src.projections.is_empty()
                        || src.local != target
                    {
                        continue;
                    }
                    // Unversioned copy-chain link `dst == target`; use-point-versioned
                    // with the setter fact below so `dst`, `target` get the assert's
                    // tokens (a copy reading the PRE-call value versions `target` to a
                    // different reaching def and stays disjoint — inert, sound).
                    defs.push(Formula::Eq(
                        Box::new(Formula::Var(crate::place_to_var_name(func, place), Sort::Int)),
                        Box::new(Formula::Var(crate::place_to_var_name(func, src), Sort::Int)),
                    ));
                }
            }
        }
        defs
    };
    let debug = std::env::var("TRUST_ASSERT_DEBUG").is_ok();
    let mut out = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, span, .. } = &block.terminator else {
            continue;
        };
        // A user `assert!`/`panic!` failure site. Exclude the `unreachable!()`
        // sentinel ("entered unreachable code"): that is intentional dead-code
        // scaffolding handled by the Unreachable VC, not a refutable assert.
        let is_assert_panic = (v2_is_assertion_panic_call(callee) || callee.ends_with("::panic"))
            && !v2_is_unreachable_sentinel_panic(callee, args);
        if !is_assert_panic {
            continue;
        }
        let Some(paths) = guard_paths_map.get(&block.id) else { continue };
        let mut formula = v2_formula_with_path_guards(func, &sv, paths, Formula::Bool(true));
        let mut fv = formula.free_variables();
        // A formula var is INPUT-FREE iff its base local (strip the `#sN_M`
        // reaching-def version) is input-free.
        let is_free = |v: &str| safe_names.contains(v.split('#').next().unwrap_or(v));
        // Resolve computed/merged vars by PINNING them to input-free expressions
        // via this block's path-definition facts: select each `Eq(Var v, rhs)`
        // whose rhs is already resolved (fixpoint), marking `v` resolved and
        // conjoining the def. We only ever ADD defs whose rhs is resolved, so the
        // augmented formula introduces no new unresolved var.
        let mut resolved: FxHashSet<String> = FxHashSet::default();
        // For each resolved var, the def that grounded it + its range facts + the
        // def's rhs free vars — so the conjunction can keep ONLY the relevance slice
        // transitively reachable from the formula's free vars (see below).
        let mut resolved_def: FxHashMap<String, (Formula, Vec<Formula>, Vec<String>)> =
            FxHashMap::default();
        let end = block.stmts.len();
        // Candidate definitions to resolve computed temps: this block's propagated
        // path-defs (branch-merge `_7 == Ite(..)`, enum/struct payloads) PLUS the
        // function's wrapping-call result models — each versioned at this block's use
        // point so its `#sN_M` reaching-def tokens unify with the path-guard formula's
        // (otherwise the def is name-disjoint and inert). Each candidate carries any
        // range facts to conjoin when (and only when) the def is actually used.
        let mut cand: Vec<(String, Vec<String>, Formula, Vec<Formula>)> = Vec::new();
        if let Some(block_defs) = path_defs.get(&block.id) {
            for d in block_defs {
                let vd = version_rename_at(d, &sv, func, block.id, end);
                if let Formula::Eq(a, b) = &vd {
                    if let Some(v) = a.var_name() {
                        cand.push((
                            v.to_string(),
                            b.free_variables().into_iter().collect(),
                            vd.clone(),
                            Vec::new(),
                        ));
                    } else if let Some(v) = b.var_name() {
                        cand.push((
                            v.to_string(),
                            a.free_variables().into_iter().collect(),
                            vd.clone(),
                            Vec::new(),
                        ));
                    }
                }
            }
        }
        for (def, ranges) in &wrap_models {
            let vd = version_rename_at(def, &sv, func, block.id, end);
            let vranges: Vec<Formula> =
                ranges.iter().map(|r| version_rename_at(r, &sv, func, block.id, end)).collect();
            // The model is `Eq(dest_var, modular-ite)`: dest is the lhs, the rhs is
            // the modular expression whose free vars are the (input-free) operands.
            if let Formula::Eq(dest, rhs) = &vd
                && let Some(v) = dest.var_name()
            {
                cand.push((
                    v.to_string(),
                    rhs.free_variables().into_iter().collect(),
                    vd.clone(),
                    vranges,
                ));
            }
        }
        // Straight-line statement / checked-arith defs (collected + soundness-gated
        // above), versioned at THIS assert's use-point. For a single-assignment var the
        // use-point version equals the def-point version, so the renamed equality is a
        // true fact (see the soundness note at the `stmt_defs` construction).
        for (def, ranges) in &stmt_defs {
            let vd = version_rename_at(def, &sv, func, block.id, end);
            let vranges: Vec<Formula> =
                ranges.iter().map(|r| version_rename_at(r, &sv, func, block.id, end)).collect();
            if let Formula::Eq(a, b) = &vd {
                if let Some(v) = a.var_name() {
                    cand.push((
                        v.to_string(),
                        b.free_variables().into_iter().collect(),
                        vd.clone(),
                        vranges,
                    ));
                } else if let Some(v) = b.var_name() {
                    cand.push((
                        v.to_string(),
                        a.free_variables().into_iter().collect(),
                        vd.clone(),
                        vranges,
                    ));
                }
            }
        }
        // Trust (derived trivial-setter summary): the setter post-call facts and
        // their copy-chain links (see the `setter_defs` construction above). Emitted
        // UNVERSIONED and version-renamed HERE at the assert use-point — the same
        // reaching-def use-point versioning `stmt_defs` use above — so the target's
        // token unifies with the assert formula's own token by construction (robust
        // to the flip; a stale/pre-call read versions to a different token and the
        // def stays inert).
        for raw in &setter_defs {
            let vd = version_rename_at(raw, &sv, func, block.id, end);
            if let Formula::Eq(a, b) = &vd {
                if let Some(v) = a.var_name() {
                    cand.push((
                        v.to_string(),
                        b.free_variables().into_iter().collect(),
                        vd.clone(),
                        Vec::new(),
                    ));
                } else if let Some(v) = b.var_name() {
                    cand.push((
                        v.to_string(),
                        a.free_variables().into_iter().collect(),
                        vd.clone(),
                        Vec::new(),
                    ));
                }
            }
        }
        loop {
            let mut changed = false;
            for (v, rhs, df, ranges) in &cand {
                if is_free(v) || resolved.contains(v) {
                    continue;
                }
                if rhs.iter().all(|r| is_free(r) || resolved.contains(r)) {
                    resolved.insert(v.clone());
                    resolved_def.insert(v.clone(), (df.clone(), ranges.clone(), rhs.clone()));
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // GROUNDED-CONJUNCT SLICE: a path-feasibility formula can be ungrounded ONLY
        // because a reachability-guard conjunct carries a loop-carried / unresolvable
        // var (e.g. a `for _ in 0..n` counter `_8` pinned to `Eq(_8, 1)`), while the
        // assert's OWN fail-condition is already grounded on inputs (e.g. `x == x`'s
        // `Not(Eq(x, x))` over param `x`). When the top-level violation is an `And`,
        // slice it to the conjuncts whose vars are ALL grounded and refute THAT.
        // SOUND: dropping a conjunct WEAKENS the violation, so a refutation of the
        // slice (weaker) refutes the full violation (stronger) — weaker-UNSAT implies
        // stronger-UNSAT. FAIL-CLOSED: if the assert's own fail-condition needs the
        // ungroundable var, the slice loses the contradiction and stays SAT -> the VC
        // is simply not refuted (never a false refutation). Only fires when we actually
        // drop an ungroundable conjunct AND the slice keeps a non-trivial atom.
        let full_grounded = !fv.is_empty() && fv.iter().all(|v| is_free(v) || resolved.contains(v));
        if !full_grounded && let Formula::And(conjuncts) = &formula {
            let grounded_conjs: Vec<Formula> = conjuncts
                .iter()
                .filter(|c| c.free_variables().iter().all(|v| is_free(v) || resolved.contains(v)))
                .cloned()
                .collect();
            if grounded_conjs.len() < conjuncts.len()
                && grounded_conjs.iter().any(|c| !matches!(c, Formula::Bool(_)))
            {
                formula = Formula::And(grounded_conjs);
                fv = formula.free_variables();
            }
        }
        // Grounded iff non-trivial AND every free var is input-free or pinned.
        let grounded = !fv.is_empty() && fv.iter().all(|v| is_free(v) || resolved.contains(v));
        // RELEVANCE SLICE: conjoin ONLY the defs transitively reachable from the
        // formula's free vars. Walk fv -> its grounding def -> that def's rhs vars to
        // a fixpoint, keeping each visited var's def + range facts. An irrelevant
        // resolvable path-def (e.g. a leftover `_3 == (_4 == _5)` whose Bool subject
        // is not free) is EXCLUDED: a def of a var unreachable from fv cannot
        // constrain the path-feasibility formula, so dropping it is sound in BOTH
        // directions — yet conjoining it empirically trips ay's proof production
        // (UNSAT but no strict-checked artifact -> falls back to runtime-checked
        // instead of Proved).
        let mut used_defs: Vec<Formula> = Vec::new();
        if grounded {
            let mut needed: Vec<String> = fv.iter().cloned().collect();
            let mut seen: FxHashSet<String> = needed.iter().cloned().collect();
            let mut qi = 0;
            while qi < needed.len() {
                let v = needed[qi].clone();
                qi += 1;
                if let Some((df, ranges, rhs)) = resolved_def.get(&v) {
                    used_defs.push(df.clone());
                    used_defs.extend(ranges.iter().cloned());
                    for r in rhs {
                        if seen.insert(r.clone()) {
                            needed.push(r.clone());
                        }
                    }
                }
            }
        }
        if debug {
            let mut fvs: Vec<&String> = fv.iter().collect();
            fvs.sort();
            eprintln!(
                "[ASSERT_REFUTE] block={:?} grounded={grounded} pinned={} free={fvs:?}\n  formula={formula:?}",
                block.id,
                used_defs.len(),
            );
        }
        if !grounded {
            continue;
        }
        if !used_defs.is_empty() {
            used_defs.push(formula);
            formula = Formula::And(used_defs);
        }
        // Contract consumption (assume-at-entry): conjoin the function's
        // DECLARED, extraction-GATED preconditions (`func.preconditions` — the
        // gated set only; never re-parse contracts here) into the panic-path
        // feasibility formula. Without this, the refute lane freely violates
        // `#[trust::requires]` in its counterexamples (e.g. picking lo > hi
        // against requires(lo <= hi)) and REFUTES guards the contract already
        // excludes. SOUNDNESS, refute direction: SAT-with-requires is a
        // strictly STRONGER counterexample claim (the model also honors the
        // contract); conjoining can only turn SAT into UNSAT — i.e. drop
        // refutations of contract-violating inputs, exactly the intent.
        // UNSAT direction: "unreachable under the assumed requires" is sound
        // because every Trust-verified caller carries a `VcKind::Precondition`
        // PROVE obligation for the callee's full declared predicate (the
        // assume/prove pairing; see generate_callsite_precondition_vcs) — an
        // assumption is never free. Preconditions carry bare ENTRY-parameter
        // debug names (the S2c exemption keeps entry reads bare), so they bind
        // exactly the entry values; a precondition over a reassigned place is
        // name-disjoint from versioned reads and inert.
        let safe_preconditions: Vec<Formula> = func
            .preconditions
            .iter()
            .filter(|pre| {
                !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre)
            })
            .cloned()
            .collect();
        if !safe_preconditions.is_empty() {
            let mut cs = safe_preconditions;
            cs.push(formula);
            formula = Formula::And(cs);
        }
        out.push(VerificationCondition {
            kind: VcKind::Assertion { message: v2_panic_call_vc_message(func, callee, args) },
            function: func.name.clone().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
        });
    }
    // verifier-perf (mid-generation work-bound): a function whose VC-gen tripped the work
    // budget gets NO refutation claims — emit an empty set so it can never produce a
    // SPURIOUS guaranteed-violation from leaf-degraded types. SOUNDNESS: withholding a
    // refutation is the fail-closed direction (it can only DROP a refutation, never
    // manufacture one). (The T9 unused-annotation rows below are also withheld here —
    // a budget-tripped function keeps unresolved obligations, so it can never reach a
    // green gate that an unused annotation would need to poison.)
    if crate::gen_work_tripped() {
        return Vec::new();
    }
    // FINAL pass: collapse SSA locals' version tokens to the bare name (see
    // `normalize_ssa_version_tokens`). In THIS lane SAT = refuted, and the
    // collapse only ADDS true identities — it removes spurious SAT (a model
    // assigning `h#s6_t` and bare `h` different values despite one write),
    // never a genuine refutation (real traces satisfy the identity).
    for vc in &mut out {
        vc.formula = normalize_ssa_version_tokens(func, &vc.formula);
    }
    // Trust (T9 contract-panic): unused-annotation enforcement, end of per-fn VC
    // generation for the refute lane. A `contract_panic` annotation that matched
    // NO panic call in this function mints an always-SAT (`Bool(true)`) Assertion
    // VC — in THIS lane SAT = refuted, so it surfaces as a guaranteed FAILED row.
    // An annotation on panic-free code is an ERROR: it must never sit dormant
    // waiting to mask a panic a future edit introduces.
    out.extend(contract_panic_unused_vcs(func));
    out
}

pub(super) fn v2_is_assertion_panic_call(callee: &str) -> bool {
    callee.contains("begin_panic")
        || callee.contains("panic_fmt")
        || callee.contains("panic_display")
        || callee.contains("assert_failed")
}

/// The bare panic intrinsic `core::panicking::panic` is the lowering of BOTH
/// `unreachable!()` and `assert!(cond)` / `panic!("static str")`, distinguished
/// only by the static message argument. We must emit a VC ONLY for the
/// `unreachable!()` sentinel: an `assert!`/`panic!` panic site is already covered
/// by the existing obligation path, and emitting a second (dataflow-starved)
/// terminator VC for it false-FAILs a provable assert (e.g. cursor_clamp_assert,
/// whose merged clamp definition does not reach a raw panic-terminator VC). The
/// `unreachable!()` panic, by contrast, has NO prior VC, so its modulo/path-guard
/// facts had no goal to discharge (modulo_unreachable fell back to runtime-checked).
/// Match the well-known sentinel "entered unreachable code"; if the wording ever
/// drifts this fails CLOSED (reverts to runtime-checked, never a false-prove).
pub(super) fn v2_is_unreachable_sentinel_panic(callee: &str, args: &[Operand]) -> bool {
    if !callee.ends_with("::panic") {
        return false;
    }
    args.iter()
        .any(|a| operand_str_constant(a).is_some_and(|s| s.contains("entered unreachable code")))
}

/// The UTF-8 contents of a `&str` constant operand, if `op` is one.
pub(super) fn operand_str_constant(op: &Operand) -> Option<String> {
    match op {
        Operand::Constant(ConstValue::Str { bytes }) => {
            Some(String::from_utf8_lossy(bytes).into_owned())
        }
        _ => None,
    }
}

/// The raw BYTES of a `&str`/byte-array constant operand, if `op` is one.
/// T7 (fmt-template): unlike `operand_str_constant`, no lossy UTF-8
/// conversion — the `format_args!` TEMPLATE carries non-UTF-8 control bytes
/// (placeholder heads like `0xC0`) that must survive for the decoder to walk.
pub(super) fn operand_str_bytes(op: &Operand) -> Option<&[u8]> {
    match op {
        Operand::Constant(ConstValue::Str { bytes }) => Some(bytes),
        _ => None,
    }
}

/// T7 (fmt-template): is `callee` the template-based
/// `core::fmt::Arguments::new::<N, M>` ctor (spelled with the turbofish, e.g.
/// `core::fmt::Arguments::<'_>::new::<10, 1>`, or bare `…Arguments::new` in
/// synthetic MIR)? The `::new::<` / trailing-`::new` boundary check keeps the
/// sibling ctors from matching: `new_const`/`from_str` (const-message ctors,
/// harvested by their own arm) and `rt::Argument::new_display`/`new_debug`/…
/// (per-ARGUMENT ctors — also excluded by the `Arguments` [plural] substring).
/// Same name-shape laxness as the existing `from_str`/`new_const` gate.
pub(crate) fn is_arguments_template_new_call(callee: &str) -> bool {
    callee.contains("Arguments") && (callee.contains("::new::<") || callee.ends_with("::new"))
}

/// T7 (fmt-template): every `&str`/byte-array constant that can define `op` —
/// the operand itself, or (the real post-lowering shape,
/// `_9 = const b"…"; Arguments::new(move _9, copy _10)`) each whole-body
/// bare-local `Use` def of it. Mirrors the enclosing Arguments-ctor chase:
/// whole-body scan, bare locals only (a projected def is skipped, fail-closed),
/// and EVERY matching def is harvested rather than guessing which one flows.
pub(super) fn template_const_bytes_candidates<'f>(
    func: &'f VerifiableFunction,
    op: &'f Operand,
) -> Vec<&'f [u8]> {
    if let Some(bytes) = operand_str_bytes(op) {
        return vec![bytes];
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return Vec::new() };
    if !p.projections.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place: dest, rvalue: Rvalue::Use(inner), .. } = stmt
                && dest.local == p.local
                && dest.projections.is_empty()
                && let Some(bytes) = operand_str_bytes(inner)
            {
                out.push(bytes);
            }
        }
    }
    out
}

/// T7 (contract-panic through panic_fmt): the concatenated LITERAL string
/// pieces of a `format_args!` TEMPLATE byte sequence, or `None` when `bytes`
/// is not a well-formed template.
///
/// The encoding is the one defined in library/core/src/fmt/mod.rs ("Internal
/// representation", representation 2 — this repo's vendored core is the source
/// of truth), decoded defensively:
///   * `0x00` — end of template. It must be the FINAL byte here: the template
///     constant is exactly the `[u8; N]` array `format_args!` emits, so
///     trailing bytes mean the shape is not what we think it is — fail closed;
///   * `0x01..=0x7F` — short literal piece: that many UTF-8 bytes follow;
///   * `0x80` — long literal piece: u16 LE length, then that many bytes;
///   * `0xC0..=0xFF` — placeholder: the head byte's low bits say which option
///     fields follow (flags 4B if bit0, width 2B if bit1, precision 2B if
///     bit2, arg_index 2B if bit3 — the exact skip arithmetic of
///     `Arguments::estimated_capacity`); the runtime VALUE is never in the
///     template, so a placeholder contributes NOTHING to the harvest;
///   * `0x81..=0xBF` — not a valid part start: fail closed.
/// EVERY malformed case returns `None` — the caller then records no message,
/// so a `contract_panic` annotation can only FAIL to match (surfacing the
/// original FAILED row / the unused-annotation error), never falsely match: a
/// decoder that guessed wrong could otherwise harvest option/length bytes as
/// "text" and message-match a payload the real literal pieces don't contain.
///
/// CONCATENATION semantics (the T7 task shape): pieces on both sides of a
/// placeholder are joined, so `message_contains = "expected got"` does match
/// `panic!("expected {} got {}", a, b)`'s pieces even though the formatted
/// message interleaves runtime values. This errs toward matching the
/// annotation — acceptable because the contract-panic marker only reclassifies
/// a FAILED row in an explicit survey lane (the strict default never
/// rewrites) — and keeps the unused-annotation check from
/// false-ERRORING on payloads that span a placeholder-split piece boundary.
pub(crate) fn fmt_template_literal_pieces(bytes: &[u8]) -> Option<String> {
    let mut out = String::new();
    let mut i = 0usize;
    loop {
        let head = *bytes.get(i)?;
        i += 1;
        match head {
            0 => {
                // End marker: must close the template exactly (see above).
                return (i == bytes.len()).then_some(out);
            }
            1..=0x7F => {
                let len = head as usize;
                out.push_str(core::str::from_utf8(bytes.get(i..i + len)?).ok()?);
                i += len;
            }
            0x80 => {
                let len = usize::from(u16::from_le_bytes([*bytes.get(i)?, *bytes.get(i + 1)?]));
                i += 2;
                out.push_str(core::str::from_utf8(bytes.get(i..i + len)?).ok()?);
                i += len;
            }
            0xC0..=0xFF => {
                let skip = usize::from(head & 1 != 0) * 4
                    + usize::from(head & 2 != 0) * 2
                    + usize::from(head & 4 != 0) * 2
                    + usize::from(head & 8 != 0) * 2;
                // The option fields must actually be present.
                bytes.get(i..i + skip)?;
                i += skip;
            }
            0x81..=0xBF => return None,
        }
    }
}

/// Trust (T9 contract-panic): the compile-time-constant `&str` messages of a
/// panic call with the given `args` — the shared message harvest for the
/// site+message matcher and the unused-annotation check, so the two can never
/// drift.
///
/// Three shapes are recognized:
///   * a direct `&str` constant argument (`core::panicking::panic("msg")`,
///     `assert!`'s generated message) — `operand_str_constant`, the same
///     `ConstValue::Str` extraction `v2_is_unreachable_sentinel_panic` uses;
///   * the POST-INLINE lowering of `panic!("static msg")`, where the constant
///     sits one call behind the panic entry:
///     `_a = fmt::Arguments::from_str("static msg"); panic_fmt(move _a)` —
///     a bare `Move`/`Copy` argument local is chased (one level, whole-body)
///     to its defining `fmt::Arguments` `from_str`/`new_const` constructor
///     call and THAT call's `&str` constants are harvested;
///   * T7: the FORMATTED lowering `panic!("prefix {}", x)`, where the same
///     chase lands on the template-based ctor
///     `_a = fmt::Arguments::new::<N, M>(move _t, …)` with
///     `_t = const b"\x07prefix \xc0\x00"` one `Use` def further back
///     (`template_const_bytes_candidates`) — the template's literal pieces
///     are decoded (`fmt_template_literal_pieces`, fail-closed on any
///     malformed byte) and their CONCATENATION is one harvested message.
///     Previously formatted messages never matched at all, forcing
///     const-message rewrites in user code (the aterm-alloc evidence).
///
/// The runtime VALUES of a formatted message are never in the template, so
/// `message_contains` text that only occurs in a runtime value still cannot
/// match — fail-closed (the T9 annotation-surface contract). On OLDER
/// toolchains whose `format_args!` lowers to `Arguments::new_v1` with a
/// `&[&str; N]` pieces array, extraction lowers that pieces constant to the
/// content-free `OpaqueConst`, so those messages (soundly) remain unmatched.
pub(super) fn panic_call_const_str_messages(func: &VerifiableFunction, args: &[Operand]) -> Vec<String> {
    let mut msgs: Vec<String> = args.iter().filter_map(operand_str_constant).collect();
    for arg in args {
        let (Operand::Copy(p) | Operand::Move(p)) = arg else { continue };
        if !p.projections.is_empty() {
            continue;
        }
        for block in &func.body.blocks {
            if let Terminator::Call { func: callee, args: ctor_args, dest, .. } = &block.terminator
                && dest.local == p.local
                && dest.projections.is_empty()
                && callee.contains("Arguments")
            {
                if callee.contains("from_str") || callee.contains("new_const") {
                    msgs.extend(ctor_args.iter().filter_map(operand_str_constant));
                } else if is_arguments_template_new_call(callee)
                    && let Some(template_op) = ctor_args.first()
                {
                    for bytes in template_const_bytes_candidates(func, template_op) {
                        if let Some(concat) = fmt_template_literal_pieces(bytes) {
                            msgs.push(concat);
                        } else if let Ok(s) = std::str::from_utf8(bytes) {
                            // THIS toolchain's `Arguments::new(&[&str] pieces, args)` template: the
                            // extractor concatenates the literal pieces into a plain-UTF-8 `Str`
                            // (not the `\x07`-length byte-template `fmt_template_literal_pieces`
                            // decodes), so use the raw pieces string directly. This is what lets
                            // contract_panic see a FORMATTED panic's message.
                            msgs.push(s.to_string());
                        }
                    }
                }
            }
        }
    }
    msgs
}

/// Trust (T9 contract-panic): does any of the enclosing fn's
/// `contract_panic(message_contains = "...")` payloads occur as a substring of a
/// compile-time-constant `&str` message of this panic call
/// (`panic_call_const_str_messages`)? This is the site+message match: the
/// payload set is pinned to `func.def_path` (see
/// `contract_panic_annotations_for` — never a stale cross-function hint), and
/// a runtime-formatted message can never be message-matched, fail-closed.
/// Empty payloads never match (extraction already rejects them; belt+braces).
pub(super) fn contract_panic_annotation_matches(func: &VerifiableFunction, args: &[Operand]) -> bool {
    let payloads = crate::contract_panic_annotations_for(&func.def_path);
    if payloads.is_empty() {
        return false;
    }
    panic_call_const_str_messages(func, args)
        .iter()
        .any(|msg| payloads.iter().any(|p| !p.trim().is_empty() && msg.contains(p.as_str())))
}

/// Trust (T9 contract-panic): the Assertion message for a panic-call VC. When a
/// contract-panic annotation message-matches this exact call site, the message
/// is prefixed with `CONTRACT_PANIC_VC_MARKER`; the VC is still SOLVED normally
/// (the marker never changes a verdict). The compiler's verify pass reclassifies
/// a resulting FAILED transport row — in a survey lane only — into a visible
/// `contract-panic:` row; an Unknown/Proved row is left untouched, and the
/// strict default never rewrites at all.
pub(super) fn v2_panic_call_vc_message(func: &VerifiableFunction, callee: &str, args: &[Operand]) -> String {
    if contract_panic_annotation_matches(func, args) {
        format!("{}panic call: {callee}", trust_types::assumption::CONTRACT_PANIC_VC_MARKER)
    } else {
        format!("panic call: {callee}")
    }
}

/// Does `func` participate in a nested-body (closure/coroutine) relationship — i.e.
/// could a `contract_panic` annotation it holds legitimately match a panic that is not
/// visible in this body? True when `func` IS a synthetic nested body (its def_path names
/// a `{closure`/`{coroutine`, so it inherited the annotation from a parent) OR when it
/// CREATES one (an `Aggregate(Closure/Coroutine/CoroutineClosure)` rvalue, whose child
/// body may carry the matching panic). A leaf that does neither cannot host the panic
/// elsewhere, so a panic-free leaf's annotation is genuinely stale.
pub(super) fn func_participates_in_nested_body(func: &VerifiableFunction) -> bool {
    if func.def_path.contains("{closure") || func.def_path.contains("{coroutine") {
        return true;
    }
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Closure { .. }
                            | AggregateKind::Coroutine { .. }
                            | AggregateKind::CoroutineClosure { .. },
                        _,
                    ),
                    ..
                }
            )
        })
    })
}

/// Trust (T9 contract-panic): one always-refuted VC per `contract_panic`
/// annotation that matched NO panic call in `func` — the unused-annotation
/// ERROR. USED means: some `Terminator::Call` whose callee is a recognized
/// panic entry point (`v2_is_assertion_panic_call` or the bare `::panic`
/// intrinsic — the same recognizer set as the panic-call VC mint sites) carries
/// a `&str` constant argument containing the payload. The check is SYNTACTIC
/// over the body (not over which lane happened to mint/solve a VC), so a
/// guarded-but-provably-unreachable panic still counts as used while a function
/// with no matching panic text at all always errors. The minted VC's formula is
/// `Bool(true)`: in the refute lane SAT = refuted, so it lands as a guaranteed
/// FAILED row (kind rewritten to `contract-panic-unused` by the verify pass —
/// which deliberately does NOT start with the `contract-panic:` prefix, so
/// targo counts it as a genuine failure, never a conditional pass).
pub(super) fn contract_panic_unused_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let payloads = crate::contract_panic_annotations_for(&func.def_path);
    if payloads.is_empty() {
        return Vec::new();
    }
    // Inheritance-aware gate (fixes the G1 contract_panic-inheritance interaction):
    // a `#[trust::contract_panic]` on a fn now propagates to that fn's nested bodies
    // (closures/coroutines) so their panics are excused. But the unused check runs
    // per-body and can only see THIS body's panic calls, so a body that HOLDS an
    // (inherited or declared) annotation whose matching panic lives in a DIFFERENT
    // body would be spuriously flagged "unused" — e.g. `successors` declares
    // `contract_panic("no action")` matched in its own body, yet its closure inherits
    // the annotation and, having no such panic, false-fails; and `require`'s panic
    // lives inside its `unwrap_or_else(|| panic!(...))` closure, so `require` itself
    // has no direct match.
    //
    // The excuse applies ONLY when this body participates in a nested-body
    // relationship — it either IS a synthetic nested body (its def_path names a
    // `{closure`/`{coroutine`, so it inherited the annotation from a parent whose
    // panic it need not carry) or it CREATES one (an `Aggregate(Closure/Coroutine/…)`
    // rvalue, so a matching panic may live in the child it spawned). A genuine LEAF
    // with no panic call and no nested body cannot host the matching panic anywhere,
    // so its annotation IS stale and must still mint the unused-marker VC (annotation
    // hygiene on panic-free code). Narrowing to this relationship — rather than
    // skipping every panic-call-free body — restores that stale-leaf signal while
    // keeping the G1 excuse. Soundness is unaffected either way: skipping the unused
    // check never manufactures a PROVE; an unexcused reachable panic in any body still
    // refutes at that body.
    let has_direct_panic_call = func.body.blocks.iter().any(|b| {
        matches!(&b.terminator,
            Terminator::Call { func: callee, .. }
                if v2_is_assertion_panic_call(callee) || callee.ends_with("::panic"))
    });
    if !has_direct_panic_call && func_participates_in_nested_body(func) {
        return Vec::new();
    }
    let payload_used = |payload: &str| {
        !payload.trim().is_empty()
            && func.body.blocks.iter().any(|b| match &b.terminator {
                Terminator::Call { func: callee, args, .. }
                    if v2_is_assertion_panic_call(callee) || callee.ends_with("::panic") =>
                {
                    // Same message harvest as the site matcher
                    // (`panic_call_const_str_messages`): direct `&str`
                    // constants PLUS the post-inline
                    // `Arguments::from_str("static msg")` chase, so an
                    // inlined `panic!("static msg")` still counts as used.
                    panic_call_const_str_messages(func, args)
                        .iter()
                        .any(|msg| msg.contains(payload))
                }
                _ => false,
            })
    };
    payloads
        .iter()
        .filter(|p| !payload_used(p))
        .map(|payload| VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "{}contract_panic(message_contains = \"{payload}\") matched no panic call in this function",
                    trust_types::assumption::CONTRACT_PANIC_UNUSED_VC_MARKER
                ),
            },
            function: func.name.clone().into(),
            location: func.span.clone(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        })
        .collect()
}

pub(super) fn v2_is_unreachable_panic_call(callee: &str) -> bool {
    callee.contains("unreachable_display")
}

pub(super) fn v2_is_unreachable_panic_chain(func: &VerifiableFunction, block_id: BlockId) -> bool {
    fn dfs(
        func: &VerifiableFunction,
        block_id: BlockId,
        seen: &mut std::collections::HashSet<BlockId>,
    ) -> bool {
        if !seen.insert(block_id) {
            return false;
        }

        for pred in func
            .body
            .blocks
            .iter()
            .filter(|bb| v2_terminator_targets(&bb.terminator).contains(&block_id))
        {
            match &pred.terminator {
                Terminator::Call { func: callee, .. }
                    if callee.contains("from_str_nonconst")
                        || callee.contains("unreachable_display") =>
                {
                    return true;
                }
                Terminator::Call { target: Some(_), .. }
                | Terminator::Goto(_)
                | Terminator::Drop { .. }
                | Terminator::Opaque { .. }
                    if dfs(func, pred.id, seen) =>
                {
                    return true;
                }
                _ => {}
            }
        }

        false
    }

    dfs(func, block_id, &mut std::collections::HashSet::new())
}

// Trust: ungated — also used by the (ungated) `v2_may_reassigned_per_block`,
// which the hardened profile relies on for its precondition-staleness kill.
pub(crate) fn v2_terminator_targets(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut blocks = targets.iter().map(|(_, target)| *target).collect::<Vec<_>>();
            blocks.push(*otherwise);
            blocks
        }
        Terminator::Call { target: Some(target), .. } => vec![*target],
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::Return | Terminator::Call { target: None, .. } | Terminator::Unreachable => {
            vec![]
        }
        _ => vec![],
    }
}

#[cfg(test)]
mod wrapping_identity_tests {
    use trust_types::{
        BasicBlock, LocalDecl, SourceSpan, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn binary_func(ty: Ty) -> VerifiableFunction {
        let return_ty = ty.clone();
        VerifiableFunction {
            name: "wrap".into(),
            def_path: "crate::wrap".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty, name: Some("b".into()) },
                ],
                blocks: Vec::new(),
                arg_count: 2,
                return_ty,
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    fn model(
        func: &VerifiableFunction,
        callee: &str,
        args: &[Operand],
        dest: &Place,
    ) -> Option<(Formula, Vec<Formula>)> {
        wrapping_call_assert_model(func, callee, args, dest, true, false, false, false)
    }

    #[test]
    fn wrapping_refutation_model_requires_closed_identity_and_exact_call_shape() {
        let func = binary_func(Ty::u64());
        let args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        let marker = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
        assert!(model(&func, marker, &args, &Place::local(0)).is_some());

        assert!(
            model(&func, "attacker::wrapping_add", &args, &Place::local(0)).is_none(),
            "a source-spellable suffix must not receive modular semantics"
        );

        let mut extra_arg = args.clone();
        extra_arg.push(Operand::Copy(Place::local(1)));
        assert!(
            model(&func, marker, &extra_arg, &Place::local(0)).is_none(),
            "the authenticated method has exactly two operands"
        );
        for (has_target, has_atomic, is_foreign, is_unsafe_sig, label) in [
            (false, false, false, false, "missing normal-return target"),
            (true, true, false, false, "atomic metadata"),
            (true, false, true, false, "foreign metadata"),
            (true, false, false, true, "unsafe-signature metadata"),
        ] {
            assert!(
                wrapping_call_assert_model(
                    &func,
                    marker,
                    &args,
                    &Place::local(0),
                    has_target,
                    has_atomic,
                    is_foreign,
                    is_unsafe_sig,
                )
                .is_none(),
                "{label} must not inherit the authenticated modular call model"
            );
        }

        let signed = binary_func(Ty::Int { width: 32, signed: true });
        let signed_args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        let signed_marker =
            "@trust-rustc-wrapping-refutation-method::core::num::<impl i32>::wrapping_sub";
        assert!(
            model(&signed, signed_marker, &signed_args, &Place::local(0)).is_some(),
            "the sealed refutation marker retains the prior signed lane"
        );
        let signed_literal_args =
            vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Int(1))];
        assert!(
            model(&signed, signed_marker, &signed_literal_args, &Place::local(0)).is_some(),
            "a narrow signed literal is checked against the authenticated destination width"
        );
        assert!(
            model(&signed, marker, &signed_args, &Place::local(0)).is_none(),
            "marker carrier and extracted operand/destination types must agree"
        );

        let pointer = binary_func(Ty::PtrSizedInt { signed: false });
        let pointer_args = vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        ];
        let pointer_marker =
            "@trust-rustc-wrapping-refutation-method::core::num::<impl usize>::wrapping_add";
        assert!(
            model(&pointer, pointer_marker, &pointer_args, &Place::local(0)).is_some(),
            "a pointer-sized literal is checked against its authenticated destination carrier"
        );
        let legacy_pointer = binary_func(Ty::usize());
        let legacy_pointer_args = vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        ];
        assert!(
            model(&legacy_pointer, pointer_marker, &legacy_pointer_args, &Place::local(0)).is_some(),
            "the authenticated pointer marker restores identity lost by legacy verifier extraction"
        );
        assert!(
            model(&pointer, marker, &pointer_args, &Place::local(0)).is_none(),
            "a fixed-width marker must not authorize a faithful pointer-sized destination"
        );

        let fixed_u32 = binary_func(Ty::u32());
        let fixed_u32_args =
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))];
        assert!(
            model(&fixed_u32, pointer_marker, &fixed_u32_args, &Place::local(0)).is_none(),
            "a pointer-sized marker must not authorize an arbitrary fixed-width destination"
        );
    }

    #[test]
    fn wrapping_result_model_requires_a_whole_function_stable_destination() {
        let marker =
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
        let mut func = binary_func(Ty::u64());
        func.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Call {
                    func: marker.into(),
                    args: vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: trust_types::UnwindEdge::Continue,
                },
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ];
        assert!(
            wrapping_result_local_is_stable(&func, &Place::local(0), 1),
            "an exact single call destination remains modelable even when rustc retains an \
             unreachable unwind annotation"
        );

        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
            span: SourceSpan::default(),
        });
        assert!(
            !wrapping_result_local_is_stable(&func, &Place::local(0), 1),
            "a competing statement definition must prevent use-point renaming from assigning \
             the wrapping equation to another reaching value"
        );
    }
}
