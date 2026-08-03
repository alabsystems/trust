//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-EF): an enum with a SHARED `&str` payload REGISTERS first-class, so its other
//! variants construct and match instead of collapsing to the wave-EL opaque lane.
//!
//! `enum_variant_field_admissible` walled `Ty::FatPtr(FatPtrKind::Str)` out with every other
//! aggregate spelling. One `&'static str` variant field therefore declined the WHOLE enum, and
//! with it every body that touched it — including bodies that only ever construct the enum's
//! scalar variants. The measured shape is clean-kernel's `flat/db.rs::get_name`, whose return
//! type is `Result<&str, FlatError>`: `FlatError` itself is `u32`/`u8`/`String` only, the sole
//! blocker is the enclosing `Result`'s `Ok(&str)` field, and the body constructs only `Err`.
//!
//! What changed, and what did NOT:
//!  * REGISTRATION widens — the `&str` field satisfies requirement (1), layout sizability
//!    (trust-ir images it as two pointer lanes, and the gate CHECKS that against rustc's own
//!    layout rather than assuming it), and requirement (3), table-freedom (`FatPtrKind::Str` is
//!    id-less; only `Slice(TyId)` names the module `types` table).
//!  * CONSTRUCTION of a `&str`-carrying variant stays FAIL-CLOSED. Requirement (2), seedability,
//!    is variant-0-only and enforced at the seed, by an EXPLICIT wall
//!    (`enum_ctor_fat_seed_reject` → `EnumCtor(fat field seed)`) checked before
//!    `seed_constant_ty` is consulted. The wall is a predicate rather than an absence on
//!    purpose: trust-ir has no fat-pointer `Constant` today, so the refusal would happen anyway
//!    — but as a property of another crate's enum, which a future pointer-valued `Constant`
//!    would delete silently. That is a tag SUBSTITUTION for those sites, not an unlock.
//!    `Constant::PhantomData` would be accepted by the interpreter for any type and is refused
//!    on purpose — a zero-lane phantom in a 16-byte slot is safe only while somebody happens to
//!    overwrite it first, which is the wave-UB safety-by-reachability defect.
//!  * The `?` LANE has the twin walls, newly load-bearing because `Result<_, &'static str>` and
//!    `Result<&'static str, _>` never registered first-class before this change:
//!    `Try(fat err field)` (`try_err_fat_seed_reject`, fired before the caller-supplied seeder)
//!    then `Try(err field not seedable)` on the Err slot, and `Try(non-scalar success payload)`
//!    on the Ok slot. Same posture: tag substitution, never an unlock.
//!  * The gate keys on the GROUND-TRUTH rustc field type (`ty::Ref(_, str, Not)` plus a proven
//!    16/8 layout), never on the mapped spelling. `map_ty`'s shared-`&str` arm is today the only
//!    site minting `FatPtr(Str)`; keying on that would be safety-by-single-producer.
//!  * A layout disagreement between the trust-ir fat image and rustc's own would produce an
//!    interpreter TRAP (`type_error` out of `enum_layout`, interpret.rs:2650-2665), NOT a
//!    value divergence. The size/align equality gate makes that trap unreachable.
//!
//! FLIP EXPOSURE — this is NOT "clean-rate only". A first-class registration gives these bodies
//! a `Ty::Enum(eid)` signature spelling, and the derived-MIR shim admits `Ty::Enum` as a RETURN
//! (to_mir.rs:1663) and as a PARAM (to_mir.rs:1697), both gated on `enum_flip_direct_only`
//! (to_mir.rs:1407) — which admits the `Direct` tag encoding these error enums carry. So a
//! `&str`-carrying enum with otherwise-scalar variants becomes flip-ELIGIBLE where it
//! previously had no first-class spelling at all. `enum_flip_direct_only` is additionally
//! fail-OPEN on a MISSING layout descriptor (`None => true`), failing closed only on an
//! unresolvable def; `register_enum` fills descriptors absent-fill, so that state is reachable.

// ---------------------------------------------------------------- positives

pub enum E {
    A(u32),
    B(&'static str),
}

// A scalar variant of a `&str`-carrying enum CONSTRUCTS. Pre-wave this recorded
// `EnumCtor(non-enum mapped ty)` because the whole def had declined.
pub fn make_a(x: u32) -> E {
    E::A(x)
}

// ... and MATCHES first-class (a real `Switch` on the registered def's discriminants, not the
// opaque lane). The `&str` payload is not bound here; binding it is a separate capability.
pub fn tag(e: E) -> u32 {
    match e {
        E::A(_) => 0,
        E::B(_) => 1,
    }
}

// The real clean-kernel shape: `Result<&str, ErrEnum>`, constructing only `Err`. `FlatLike`
// mirrors `FlatError`'s admissible field set (u32 / u8 / String) and its variant 0 is fieldless,
// so the nested `seed_constant_ty` recursion bottoms out.
pub enum FlatLike {
    InvalidMagic,
    IndexOutOfBounds(u32),
    InvalidTag(u8),
}

pub fn get_name(idx: u32, count: u32) -> Result<&'static str, FlatLike> {
    if idx >= count {
        return Err(FlatLike::IndexOutOfBounds(idx));
    }
    read_indexed(idx)
}

pub fn read_indexed(_idx: u32) -> Result<&'static str, FlatLike> {
    Err(FlatLike::InvalidMagic)
}

// The `Ok(&str)` construction stays CLOSED (`EnumCtor(fat field seed)`). Present so the
// refusal is exercised in the same crate as the accept, not merely asserted in prose.
pub fn ok_str() -> Result<&'static str, FlatLike> {
    Ok("x")
}

// A `&str`-carrying variant that is NOT variant 0 — pins that sizability is per-variant while
// seedability is variant-0-only (the same split `trust_ir_lower_struct_payload_enum.rs` pins for
// struct payloads).
pub enum Late {
    Zero,
    One(&'static str),
}
pub fn late(l: Late) -> u32 {
    match l {
        Late::Zero => 0,
        Late::One(_) => 1,
    }
}

// ------------------------------------------------------- negative controls
//
// Each control is stated against the MAPPED NODE TYPE, not the surface syntax — a control that
// does not actually reach the arm it claims to test is not a control.

// CONTROL: `&[u8]` maps to `Ty::FatPtr(FatPtrKind::Slice(tid))`, which names the module `types`
// table and fails requirement (3). Still declines.
pub enum SliceE {
    A(u32),
    B(&'static [u8]),
}
pub fn slice_e(e: SliceE) -> u32 {
    match e {
        SliceE::A(_) => 0,
        SliceE::B(_) => 1,
    }
}

// CONTROL: `&dyn Trait` maps to `Ty::FatPtr(FatPtrKind::TraitObject { .. })`, which IS table-free
// — so this is the control proving table-freedom was never the admission criterion. Its value is
// a (data, vtable) pair this producer cannot construct or reason about. Still declines.
pub trait Marker {}
pub enum DynE {
    A(u32),
    B(&'static dyn Marker),
}
pub fn dyn_e(e: DynE) -> u32 {
    match e {
        DynE::A(_) => 0,
        DynE::B(_) => 1,
    }
}

// CONTROL: `*const str` maps to the ANONYMOUS fat pair `Ty::Tuple([Ptr, I64])`, not to
// `FatPtr(Str)`. Same 16 bytes, different spelling, and the new arm matches on the spelling
// AND the rustc type — so an aggregate spelling stays out. Still declines.
pub enum RawStrE {
    A(u32),
    B(*const str),
}
pub fn raw_str_e(e: RawStrE) -> u32 {
    match e {
        RawStrE::A(_) => 0,
        RawStrE::B(_) => 1,
    }
}

// CONTROL: a bare generic payload maps to the opaque `Ty::Unit` placeholder (wave-PO
// `param_opaque`), which is deliberately not admitted — pins that the `ty::Param` route, the
// LARGEST class hiding behind `EnumCtor(non-enum mapped ty)` (167 of 236 root bodies in the
// clean-kernel census, all `symbolic`), is untouched by this change.
pub enum GenE<T> {
    A(u32),
    B(T),
}
pub fn gen_e<T>(e: GenE<T>) -> u32 {
    match e {
        GenE::A(_) => 0,
        GenE::B(_) => 1,
    }
}

// NOT A CONTROL — a NO-CHANGE WITNESS, recorded because the obvious reading of it is wrong.
// `&mut str` does NOT map to `FatPtr(Str)`: `map_ty`'s shared-`&str` arm requires
// `Mutability::Not`, and the generic ref arm below it spells a pointee that IS the DST
// (`Slice`/`Str`/`Dynamic`) as a THIN `Ty::Ptr` — a named, deliberately unfaithful posture with
// an oracle-side twin. `Ty::Ptr` has been admitted since wave-EP, so this enum ALREADY
// registered before this change and still does. It is included so nobody re-derives it as a
// decline control; the refusal the gate really owes here (a `FatPtr(Str)` spelling over a
// non-shared rustc ref) has no reachable witness and is pinned by the gate's rustc-type
// conjunct, not by this file.
pub enum MutStrE {
    A(u32),
    B(&'static mut str),
}
pub fn mut_str_e(e: MutStrE) -> u32 {
    match e {
        MutStrE::A(_) => 0,
        MutStrE::B(_) => 1,
    }
}

fn main() {}
