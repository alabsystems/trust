//! Shared interior-mutable byte and own-storage escape classification.
//! These are model queries, not proof authority. Unknown shapes retain the
//! existing conservative answer; a pointer slot and its pointee remain distinct.

use crate::place_ty::place_ty_step;
use crate::{Projection, Rvalue, Statement, Ty};

/// Conservative name backup for unrecorded cell wrappers. A name mismatch
/// never establishes frozen bytes; grants require the structural walk below.
pub fn type_name_is_interior_mutable(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    let tail = base.rsplit("::").next().unwrap_or(base).trim();
    tail.contains("Cell")
        || tail.starts_with("Atomic")
        || matches!(tail, "Mutex" | "RwLock" | "OnceLock" | "LazyLock" | "Condvar" | "Once")
}

pub fn type_name_is_std(name: &str) -> bool {
    let base = name.trim_start_matches('<');
    base.starts_with("core::") || base.starts_with("alloc::") || base.starts_with("std::")
}

pub fn type_name_is_zero_sized_std_marker(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name).trim();
    matches!(
        base,
        "core::marker::PhantomData"
            | "std::marker::PhantomData"
            | "core::marker::PhantomPinned"
            | "std::marker::PhantomPinned"
            | "alloc::alloc::Global"
            | "std::alloc::Global"
    )
}

pub fn union_cover_len(
    defs: &crate::DatatypeDefs,
    base: Option<&Ty>,
    place: &crate::Place,
) -> Option<usize> {
    let first_field = |from: usize| {
        place.projections[from..].iter().position(is_field_projection).map(|k| from + k)
    };
    first_field(0)?;
    let Some(base) = base else {
        return first_field(0);
    };
    let mut ty: std::borrow::Cow<'_, Ty> = std::borrow::Cow::Borrowed(base);
    let mut pending_variant: Option<usize> = None;
    for (i, proj) in place.projections.iter().enumerate() {
        if is_field_projection(proj) && field_base_may_overlap_siblings(defs, &ty) {
            return Some(i);
        }
        match place_ty_step(defs, ty, proj, &mut pending_variant) {
            Some(next) => ty = next,
            None => return first_field(i),
        }
    }
    None
}

fn is_field_projection(proj: &crate::Projection) -> bool {
    matches!(proj, crate::Projection::Field(_))
}

pub fn field_base_may_overlap_siblings(defs: &crate::DatatypeDefs, ty: &Ty) -> bool {
    let resolved;
    let ty = match ty {
        Ty::Datatype { variants, .. } if variants.is_empty() => {
            match crate::datatype_marker_definition(defs, ty) {
                Some(definition) => {
                    resolved = definition;
                    resolved
                }
                None => return true,
            }
        }
        _ => ty,
    };
    match ty {
        Ty::Adt { adt_kind: Some(kind), .. } => matches!(kind, crate::AdtKind::Union),
        Ty::Adt { adt_kind: None, variants, .. } => variants.is_empty(),
        Ty::Tuple(_) | Ty::Closure { .. } | Ty::Coroutine { .. } => false,
        Ty::Datatype { variants, .. } => variants.is_empty(),
        _ => true,
    }
}

/// Whether `ty` may hold an `UnsafeCell` at an INLINE position — the bytes a `&ty`
/// covers, so not behind a reference, a raw pointer or a `Box` (whose storage is a
/// pointer). That is `!Freeze` re-derived structurally, FAIL-CLOSED: an ADT whose
/// name is an `UnsafeCell` or a std wrapper built on one
/// ([`type_name_is_interior_mutable`]: `Cell`, `RefCell`, `Mutex`, `Atomic*`, ...),
/// an ADT with neither a recorded field nor a recorded variant (a std zero-sized
/// marker aside), a by-name datatype marker the body's table does not define, a `Vec`
/// (`Ty::Seq` drops its allocator parameter), every unclassified type, and a type
/// deeper than the fuel all answer `true`. A marker already being walked answers
/// `false` for the cycle, which adds no new part.
pub fn ty_may_hold_inline_unsafe_cell(
    defs: &crate::DatatypeDefs,
    ty: &Ty,
    seen: &mut Vec<String>,
    fuel: u32,
) -> bool {
    ty_may_hold_cell_bytes(defs, ty, CellBytes::Any, seen, fuel)
}

/// Which bytes of a value a [`ty_may_hold_cell_bytes`] walk asks about.
///
/// Trust: 2026-10-15 (INTERIOR-MUT-CHANNEL-1 follow-up, G2-OPTSTRING-1).
#[derive(Clone, Copy, PartialEq, Eq)]
enum CellBytes {
    /// Every inline byte: `!Freeze` ([`ty_may_hold_unsafe_cell`]).
    Any,
    /// Only the bytes some modelled place name denotes
    /// ([`ty_may_hold_named_unsafe_cell`]): the same walk, except that std's `Vec`
    /// answers `false` wherever the walk reaches it.
    Named,
}

/// The walk behind [`ty_may_hold_inline_unsafe_cell`] and
/// [`ty_may_hold_named_unsafe_cell`]. The two questions differ ONLY at std's `Vec`
/// (`Ty::Seq`, or a field-less ADT at its exact path,
/// [`is_std_vec_adt_name`]): `CellBytes::Any` answers `true`
/// (its allocator is not in hand), `CellBytes::Named` answers `false`. A cell wrapper is
/// refused by name BEFORE the walk descends, so a `Vec` inside one (`RefCell<Vec<u8>>`)
/// is never reached and the wrapper answers `true` under both (since CELL-NAME-TAIL-1 the
/// named question takes a NON-std ADT with recorded parts by its fields instead,
/// [`cell_name_decided_by_fields`]: a user `TrailCell { row, col }` holds no cell byte); and below a union (or a
/// variant-less ADT of unrecorded kind) the walk asks `CellBytes::Any`, because the
/// union's other fields name the `Vec`'s bytes.
fn ty_may_hold_cell_bytes(
    defs: &crate::DatatypeDefs,
    ty: &Ty,
    bytes: CellBytes,
    seen: &mut Vec<String>,
    fuel: u32,
) -> bool {
    let Some(fuel) = fuel.checked_sub(1) else {
        return true;
    };
    let walk = |t: &Ty, seen: &mut Vec<String>| ty_may_hold_cell_bytes(defs, t, bytes, seen, fuel);
    match ty {
        Ty::Bool
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Char
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Str
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::FnDef { .. }
        | Ty::FnPtr { .. } => false,
        // std's `Vec`: see [`ty_may_hold_named_unsafe_cell`] for why no name denotes its
        // cell bytes. The raw question cannot see its allocator, so it refuses.
        Ty::Seq { .. } => bytes == CellBytes::Any,
        Ty::Adt { name, fields, variants, .. }
            if bytes == CellBytes::Named
                && fields.is_empty()
                && variants.is_empty()
                && is_std_vec_adt_name(name) =>
        {
            false
        }
        // A `Box` is walked like any ADT: its pointer field is `Freeze`, and its
        // allocator field is inline (a `Box` rendered without fields is refused).
        Ty::Adt { name, fields, variants, adt_kind, .. } => {
            // Under a UNION every field's names denote every byte (`u.n` reads the bytes of
            // a `ManuallyDrop<Vec<u8, A>>` sibling, `A`'s cells included), so the byte
            // question decides its fields. A variant-less ADT whose kind was not recorded
            // may be one.
            let bytes = if variants.is_empty()
                && !matches!(adt_kind, Some(crate::AdtKind::Struct | crate::AdtKind::Enum))
            {
                CellBytes::Any
            } else {
                bytes
            };
            let walk =
                |t: &Ty, seen: &mut Vec<String>| ty_may_hold_cell_bytes(defs, t, bytes, seen, fuel);
            // CELL-NAME-TAIL-1: for the NAMED question, a user ADT with its parts recorded
            // is decided by its fields alone ([`cell_name_decided_by_fields`]).
            let decided_by_fields = bytes == CellBytes::Named
                && cell_name_decided_by_fields(
                    name,
                    adt_kind,
                    !fields.is_empty() || !variants.is_empty(),
                );
            (type_name_is_interior_mutable(name) && !decided_by_fields)
                || (fields.is_empty()
                    && variants.is_empty()
                    && !type_name_is_zero_sized_std_marker(name))
                || fields.iter().any(|(_, t)| walk(t, seen))
                || variants.iter().any(|v| v.fields.iter().any(|(_, t)| walk(t, seen)))
        }
        Ty::Datatype { name, variants } if variants.is_empty() => {
            if seen.contains(name) {
                return false;
            }
            seen.push(name.clone());
            match crate::datatype_marker_definition(defs, ty) {
                Some(definition) => walk(definition, seen),
                None => true,
            }
        }
        Ty::Datatype { name, variants } => {
            type_name_is_interior_mutable(name)
                || variants.iter().any(|(_, fields)| fields.iter().any(|(_, t)| walk(t, seen)))
        }
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => walk(elem, seen),
        Ty::Tuple(elems) => elems.iter().any(|t| walk(t, seen)),
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(|t| walk(t, seen))
        }
        _ => true,
    }
}

/// Trust: 2026-10-15 (INTERIOR-MUT-CHANNEL-1) — THE ONE STRUCTURAL interior-mutability
/// predicate over BYTES: whether a value of `ty` may hold an `UnsafeCell` byte at an
/// inline position ([`ty_may_hold_inline_unsafe_cell`]: `!Freeze` re-derived field by
/// field, a by-name marker resolved through `defs`, fail-closed on every shape whose
/// parts are not in hand, a `Vec` included, the [`type_name_is_interior_mutable`] tails
/// as a REFUSING backup). A local walk that granted on `!name.contains("UnsafeCell")`
/// passed a `Cell` the extractor rendered without its fields, and a struct holding one.
///
/// Every "these bytes are `Freeze`" GRANT asks it. Trust: 2026-10-15 (G2-OPTSTRING-1),
/// each caller checked against [`ty_may_hold_named_unsafe_cell`], which differs only at
/// std's `Vec`, and kept on this one:
///  * `sep_engine`'s box-temp reborrow containment asks whether a pointer derived from
///    a shared reborrow can WRITE (deallocate) the bytes: a memory-model question about
///    every byte, whatever names them;
///  * `value_facts`' protected shared parameter (the discriminant CSE across barriers)
///    refused a `Vec` before G2 as well; the named question would be a NEW grant there,
///    not a G2 casualty restored;
///  * `local_defs`' read-path freeze is asked about the leaf of a `Copy` read (a
///    bound), which never holds a `Vec`, so the two questions agree on all of its reads;
///  * `trust_vcgen::generate::interior_mutable_shared_borrow` (`laundered_alias_roots`, through
///    [`ty_may_hold_inline_unsafe_cell`]) asks which storage a raw pointer derived
///    through a cell may reach: bytes, not names.
pub fn ty_may_hold_unsafe_cell(defs: &crate::DatatypeDefs, ty: &Ty) -> bool {
    ty_may_hold_cell_bytes(defs, ty, CellBytes::Any, &mut Vec::new(), UNRETAGGED_POINTER_TY_FUEL)
}

/// Trust: 2026-10-15 (INTERIOR-MUT-CHANNEL-1 follow-up, G2-OPTSTRING-1) — whether a value
/// of `ty` may hold an `UnsafeCell` byte that a modelled place NAME denotes: THE question
/// of [`unsafe_cell_places`], which decides what both halves of the write channel and
/// every stability scan name. It is [`ty_may_hold_unsafe_cell`] with one difference:
/// std's `Vec` (`Ty::Seq`, or a field-less ADT at std's exact `Vec` path) answers `false`
/// wherever the walk reaches it, i.e. wherever no cell wrapper encloses it.
///
/// Why a `Vec` holds no named cell byte. `Vec<T, A>` is `{ buf: { ptr, cap, alloc: A },
/// len }`; only `A` can hold `UnsafeCell` bytes (the byte question refuses a `Seq`
/// because `Ty::Seq` drops `A`). No name denotes them:
///  * place typing has no projection into a `Seq` (`crate::project_ty_cow` types no
///    `Field`, `Index` or `Deref` of one), so no place name lies under a `Vec` place;
///  * its elements live behind `ptr`, not inline, and are reached only through call
///    results (`index`, `deref`, `iter`, `get`), which are fresh names with their own
///    channel (a retagged shared reference's pointee is named by
///    `trust_vcgen::generate::stored_ref_pointee_names`); `A` likewise only through `Vec::allocator`'s result;
///  * the names that DO reach into a `Vec`'s bytes are its length (`guards::coll_len_var`,
///    `vec_region`'s symbols) — the private `len`, outside every cell, written only
///    through `&mut Vec` — and, when the `Vec` is an enum's payload, that enum's
///    discriminant, which may sit in a niche of `ptr` or `cap` but never in `A`'s cell
///    bytes: `UnsafeCell` disables niche optimizations (`library/core/src/cell.rs`,
///    "Memory layout"). Another variant's fields share the place but are read only
///    while the enum IS that variant, when no `Vec` is there;
///  * a UNION is the exception: its other fields name every byte of a `Vec` field
///    (`u.n` beside `u.v: ManuallyDrop<Vec<u8, A>>`), so below a union (or a variant-less
///    ADT whose kind was not recorded) the walk asks the byte question.
///
/// So `Option<String>` (`String` renders `{ vec: Seq<u8> }`), `(u32, Vec<u8>)`, an enum
/// over a `Vec` and a `Vec<Cell<u32>>` hold no named cell byte, while `Option<Cell<u32>>`,
/// an enum with a `Cell` payload, a `Vec`-holding struct with a `Cell` sibling, a
/// `RefCell<Vec<u8>>` (whose holder can resize the `Vec` through `&`), a union with a
/// `Vec` field, and a user type named like std's `Vec` or `String` that holds a `Cell`
/// still do.
pub fn ty_may_hold_named_unsafe_cell(defs: &crate::DatatypeDefs, ty: &Ty) -> bool {
    ty_may_hold_cell_bytes(defs, ty, CellBytes::Named, &mut Vec::new(), UNRETAGGED_POINTER_TY_FUEL)
}

/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1, G2 of the verifier-gaps design) — the
/// places under `place` (of type `ty`) whose BYTES may be `UnsafeCell` bytes, each at the
/// finest granularity a place name can denote. THE ONE STATEMENT of "what a shared
/// reference does not freeze", asked by both halves of the interior-mutable write
/// channel (`trust_vcgen::generate::stored_ref_pointee_names`) and by every stability scan of a local's own
/// storage (`trust_vcgen::generate::shared_borrowed_cell_places`).
///
/// A shared reference freezes its pointee's bytes OUTSIDE an `UnsafeCell` (a write to
/// them while the reference is live is UB under Stacked Borrows and Tree Borrows alike);
/// the bytes INSIDE one are writable through any copy of it, and through any pointer a
/// holder derives from it, in a defined execution (`Cell::set`, `RefCell::borrow_mut`,
/// an atomic store, `*UnsafeCell::get() = v`). So every name of those bytes must be
/// havocked wherever unseen code can run while such a reference exists.
///
/// The walk asks the structural predicate of NAMED cell bytes,
/// [`ty_may_hold_named_unsafe_cell`] (`!Freeze` re-derived field by field, fail-closed on
/// every unrecorded shape, with the interior-mutability name tails as a REFUSING backup),
/// and descends only where a NAME can split the bytes: a stamped struct that is not
/// itself a cell wrapper, field by field, and a tuple, field by field. Every other
/// cell-holding shape — a cell wrapper, an enum (its variant fields share the place), a
/// union, an array or slice of cell-holding elements (an element name `a[_i]` cannot tell
/// `a[_j]` apart), a closure, a by-name datatype, an unresolved type — is named WHOLE. So
/// `st.1` for `st: S { n, c: Cell }` and never `st.0`: every GRANT (a sibling not named)
/// is the predicate finding no cell in that sibling, never a name failing to match.
///
/// A std `Vec` (`Ty::Seq`, or a field-less ADT at std's exact `Vec` path) names nothing
/// here, and holds no named cell byte for an enclosing shape either: the only names that
/// reach into its bytes are its LENGTH (`guards::coll_len_var`, a private `usize` std
/// writes only through `&mut Vec`) and an enclosing enum's discriminant, neither of them
/// in a cell; its elements are reached only through call results, which are fresh names;
/// an allocator cell a holder of `&Vec` can write has no name to kill
/// ([`ty_may_hold_named_unsafe_cell`] states the argument). Below a UNION the other
/// fields name the `Vec`'s bytes, so there the byte question decides and the union is
/// named whole. Trust: 2026-10-15
/// (G2-OPTSTRING-1): this arm used to sit here, below a predicate that refused every
/// `Vec`, so an enum, array or closure over one was named WHOLE: `x: &Option<String>`
/// lost its tag fact at every call (`x.is_some()` then `x.as_ref().unwrap()`).
pub fn unsafe_cell_places(
    defs: &crate::DatatypeDefs,
    place: &crate::Place,
    ty: &Ty,
    out: &mut Vec<crate::Place>,
) {
    fn walk(
        defs: &crate::DatatypeDefs,
        place: &mut crate::Place,
        ty: &Ty,
        fuel: u32,
        out: &mut Vec<crate::Place>,
    ) {
        let Some(fuel) = fuel.checked_sub(1) else {
            if !out.contains(place) {
                out.push(place.clone());
            }
            return;
        };
        match ty {
            Ty::Tuple(elems) => {
                for (i, t) in elems.iter().enumerate() {
                    if !ty_may_hold_named_unsafe_cell(defs, t) {
                        continue;
                    }
                    place.projections.push(Projection::Field(i));
                    walk(defs, place, t, fuel, out);
                    place.projections.pop();
                }
            }
            Ty::Adt {
                name,
                fields,
                variants,
                adt_kind: adt_kind @ Some(crate::AdtKind::Struct),
                ..
            } if variants.is_empty()
                && !fields.is_empty()
                && (!type_name_is_interior_mutable(name)
                    || cell_name_decided_by_fields(name, adt_kind, true)) =>
            {
                for (i, (_, t)) in fields.iter().enumerate() {
                    if !ty_may_hold_named_unsafe_cell(defs, t) {
                        continue;
                    }
                    place.projections.push(Projection::Field(i));
                    walk(defs, place, t, fuel, out);
                    place.projections.pop();
                }
            }
            _ => {
                if !out.contains(place) {
                    out.push(place.clone());
                }
            }
        }
    }
    if !ty_may_hold_named_unsafe_cell(defs, ty) {
        return;
    }
    let mut place = place.clone();
    walk(defs, &mut place, ty, UNSAFE_CELL_PLACE_FUEL, out);
}

/// Trust (2026-10-18, CELL-NAME-TAIL-1; candidate-gate RCA precision D2): whether the
/// NAMED cell question ([`ty_may_hold_named_unsafe_cell`], [`unsafe_cell_places`]) decides
/// an ADT whose name matches [`type_name_is_interior_mutable`] by its FIELDS instead of
/// refusing it by name: a NON-std ADT (not under `core::`, `alloc::`, `std::`) that the
/// extractor stamped as a struct or an enum, with its parts (fields or variants) recorded.
///
/// The name tail is `contains("Cell")`, so every user type named like aterm's
/// `TrailCell`, `aterm_grid::Cell` or a `GridCell` was refused as a cell wrapper, and a
/// retagged `&TrailCell` lost every fact about its pointee at every call
/// (INTERIOR-MUT-CHANNEL-1's pointee half named it whole): aterm-render `lib.rs:17913`.
/// The name is a REFUSING BACKUP for what the walk cannot see: `UnsafeCell` itself (a
/// lang item whose only field is the plain `T`, so its NAME is all there is) and the std
/// wrappers on it. For a user ADT it adds nothing: interior mutability is an `UnsafeCell`
/// at an inline position, every `UnsafeCell` is `core::cell::UnsafeCell` (a std name the
/// walk still refuses), and the extractor renders a stamped ADT's `all_fields()` —
/// private fields and other crates' types included — compacting an oversized field to a
/// by-name marker that the walk resolves through `datatype_defs` or refuses. So the walk
/// reaches every inline byte of such a type. A std name, a by-name `Datatype`, an ADT of
/// unrecorded kind (a union is never stamped `Struct`/`Enum`) and a part-less rendering
/// keep the name refusal. The byte question ([`ty_may_hold_unsafe_cell`]) is unchanged.
fn cell_name_decided_by_fields(
    name: &str,
    adt_kind: &Option<crate::AdtKind>,
    has_parts: bool,
) -> bool {
    has_parts
        && !type_name_is_std(name)
        && matches!(adt_kind, Some(crate::AdtKind::Struct | crate::AdtKind::Enum))
}

/// Depth bound of [`unsafe_cell_places`]' descent; running out names the place whole.
const UNSAFE_CELL_PLACE_FUEL: u32 = 24;

fn body_local_ty(body: &crate::VerifiableBody, local: usize) -> Option<&Ty> {
    if let Some(decl) = body.locals.get(local)
        && decl.index == local
    {
        return Some(&decl.ty);
    }
    body.locals.iter().find(|d| d.index == local).map(|d| &d.ty)
}

/// The type of `projections` from `root`, by the body's own place typing (`place_ty_step`,
/// which widens a by-name datatype marker through `body.datatype_defs` at every step).
/// `None` when a step cannot be typed. Body-level, for the `local_defs` questions that
/// hold no `VerifiableFunction`.
fn body_place_ty_from_root<'a>(
    defs: &'a crate::DatatypeDefs,
    root: Option<&'a Ty>,
    projections: &[Projection],
) -> Option<std::borrow::Cow<'a, Ty>> {
    let mut ty: std::borrow::Cow<'a, Ty> = std::borrow::Cow::Borrowed(root?);
    let mut pending_variant: Option<usize> = None;
    for proj in projections {
        ty = place_ty_step(defs, ty, proj, &mut pending_variant)?;
    }
    Some(ty)
}

/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1) — the SLOT HALF of the interior-mutable
/// write channel for one statement: when `stmt` is a SHARED borrow `_ = &P` of the body's
/// OWN storage (`P` has no `Deref`), the root local of `P` and the [`unsafe_cell_places`]
/// under `P`. `None` for every other statement, and for a shared borrow whose place holds
/// no cell. A place whose type cannot be resolved is named whole (fail-closed).
///
/// A shared borrow of `Freeze` bytes hands out no write channel (a write through it is UB),
/// which is why `crate::Statement::escapes_local` and the slot-write rule
/// (`trust_vcgen::generate::own_storage_write_borrow`) leave it off. A shared borrow of `UnsafeCell` bytes DOES:
/// `poke(&c)` sets `c` through `Cell::set`, defined under both aliasing models. A borrow
/// through a `Deref` reaches the POINTEE, which the pointer's own channel covers (a
/// `&mut`, raw or `Box` root's base name is on `trust_vcgen::generate::mutable_pointer_local_names`; the cells
/// behind a retagged shared reference are named by `trust_vcgen::generate::stored_ref_pointee_names`; a
/// reference loaded from memory has its whole pointee named there).
///
/// Trust: 2026-10-16 (INTERIOR-MUT-CHANNEL-2) — A BORROW BELOW A UNION FIELD names the union
/// cover. When `P` projects through a field of a value that may be a union (the cut of
/// `trust_vcgen::generate::union_write_cover_name`, the cover UNION-SIBLING-WRITE-2 gives `&mut u.b`), the
/// union's other fields name the same bytes: `poke(&u.c)` for
/// `union U { c: ManuallyDrop<Cell<u32>>, n: u32 }` rewrites `u.n`, which the name algebra
/// keeps apart from `u.0`. So there the BYTE question ([`ty_may_hold_unsafe_cell`]) is
/// asked of `P`'s own type, and the cover (`u`, or `w.1` for `&w.u.c`) is named whole,
/// which rebinds every overlapping sibling by prefix. The byte question, not the named
/// one: a `Vec` field's allocator cell bytes (`&u.v` with `u.v: ManuallyDrop<Vec<u8, A>>`)
/// are named by the sibling `u.n` although no name below `u.v` denotes them. Until this
/// arm the walk started AT `P`, saw no union, and named only `u.0`'s cells: measured
/// 2026-10-16 on real MIR (`tests/union_cell_channel_realmir.rs`), `u.n + 1` after
/// `poke(&u.c)` and `s[u.n]` after `poke(&u.c)` or `poke(&w.u.c)` were PROVED on
/// programs that panic, as were `s[u.n[k]]` after `poke(&u.v)` over a `Vec` with a cell
/// allocator. A borrow of a `Freeze` field (`&u.n`) still hands out nothing.
pub fn shared_borrow_cell_places(
    body: &crate::VerifiableBody,
    stmt: &Statement,
) -> Option<(usize, Vec<crate::Place>)> {
    let place = own_storage_shared_borrow(stmt)?;
    let defs = &body.datatype_defs;
    let mut cells = Vec::new();
    let root = body_local_ty(body, place.local);
    let ty = body_place_ty_from_root(defs, root, &place.projections);
    if let Some(cut) = union_cover_len(defs, root, place) {
        if ty.as_deref().is_none_or(|t| ty_may_hold_unsafe_cell(defs, t)) {
            cells.push(crate::Place {
                local: place.local,
                projections: place.projections[..cut].to_vec(),
            });
        }
    } else {
        match ty {
            Some(ty) => unsafe_cell_places(defs, place, &ty, &mut cells),
            None => cells.push(place.clone()),
        }
    }
    (!cells.is_empty()).then_some((place.local, cells))
}

/// The place a SHARED borrow of the body's OWN storage borrows: `Some(P)` exactly when
/// `stmt` is `_ = &P` and `P` has no `Deref` — the only statements
/// [`shared_borrow_cell_places`] can answer `Some` for, and the root it then answers is
/// `P.local`. No type is read.
///
/// Trust: 2026-10-17 (gate-rca deadline, G2 cost) — the escape question asks about ONE
/// local (`crate::body_stmt_escapes_local(body, stmt, local)`), once per statement per
/// asked local, inside the path-definition fixpoint and the write walks. It used to run
/// the cell walk ([`unsafe_cell_places`], [`ty_may_hold_unsafe_cell`], the interior-
/// mutable type-name match) for EVERY shared borrow in the body and only then compare
/// the root, so a borrow of any other local paid the whole type walk to answer `false`.
/// Measured on the candidate gate's `aterm_conformance::measure::scan::scan_frames`:
/// 45 % of a 2.5-minute native bundle construction in this walk. The callers now test
/// the root here first; the answer is the same predicate.
pub fn own_storage_shared_borrow(stmt: &Statement) -> Option<&crate::Place> {
    let Statement::Assign { rvalue: Rvalue::Ref { mutable: false, place }, .. } = stmt else {
        return None;
    };
    (!place.projections.iter().any(|p| matches!(p, Projection::Deref))).then_some(place)
}

/// Whether `stmt` is a shared borrow of `local`'s OWN storage that covers an
/// `UnsafeCell` byte: exactly `shared_borrow_cell_places(body, stmt)` answering
/// `Some((local, _))`, with the cell walk run only for a borrow rooted at `local`
/// (see [`own_storage_shared_borrow`]).
pub fn shared_borrow_of_local_covers_cell(
    body: &crate::VerifiableBody,
    stmt: &Statement,
    local: usize,
) -> bool {
    let Some(place) = own_storage_shared_borrow(stmt).filter(|place| place.local == local) else {
        return false;
    };
    let defs = &body.datatype_defs;
    let root = body_local_ty(body, local);
    let ty = body_place_ty_from_root(defs, root, &place.projections);
    if union_cover_len(defs, root, place).is_some() {
        ty.as_deref().is_none_or(|t| ty_may_hold_unsafe_cell(defs, t))
    } else {
        ty.as_deref().is_none_or(|t| ty_may_hold_named_unsafe_cell(defs, t))
    }
}

const UNRETAGGED_POINTER_TY_FUEL: u32 = 64;

pub const STD_VEC_PATHS: [&str; 2] = ["alloc::vec::Vec", "std::vec::Vec"];

/// Exact std paths only: a user type called Vec retains its field semantics.
pub fn is_std_vec_adt_name(name: &str) -> bool {
    let path = name.split('<').next().unwrap_or(name);
    STD_VEC_PATHS.contains(&path)
}
