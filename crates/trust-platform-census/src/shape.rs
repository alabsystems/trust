//! trust-ir types as the census sees them: the leaf layout of a value
//! (design §2.3: aggregates are flattened to per-field variables) and
//! whether a type holds a descriptor carrier.

use trust_ir::{Module, Ty};

/// A scalar's integer type (values are kept in the type's natural range:
/// `i32` values are signed, `u32` values unsigned).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IntTy {
    pub bits: u32,
    pub signed: bool,
}

impl IntTy {
    pub const I32: IntTy = IntTy { bits: 32, signed: true };
    pub const BOOL: IntTy = IntTy { bits: 1, signed: false };

    #[must_use]
    pub fn min(self) -> i64 {
        if self.signed { -(1i64 << (self.bits.min(64) - 1)) } else { 0 }
    }

    #[must_use]
    pub fn max(self) -> i64 {
        match (self.bits, self.signed) {
            (64, true) => i64::MAX,
            // u64 values above i64::MAX are not representable: the census
            // keeps u64 values only while they fit (wrap checks cut the rest).
            (64, false) => i64::MAX,
            (b, true) => (1i64 << (b - 1)) - 1,
            (b, false) => (1i64 << b) - 1,
        }
    }

    #[must_use]
    pub fn contains(self, v: i64) -> bool {
        v >= self.min() && v <= self.max()
    }

    #[must_use]
    pub fn name(self) -> String {
        if self.bits == 1 {
            "bool".to_string()
        } else {
            format!("{}{}", if self.signed { 'i' } else { 'u' }, self.bits)
        }
    }
}

/// The integer type of a trust-ir scalar type, if it is one.
#[must_use]
pub fn int_ty(ty: &Ty) -> Option<IntTy> {
    Some(match ty {
        Ty::Bool => IntTy::BOOL,
        Ty::I8 => IntTy { bits: 8, signed: true },
        Ty::I16 => IntTy { bits: 16, signed: true },
        Ty::I32 => IntTy::I32,
        Ty::I64 | Ty::Isize => IntTy { bits: 64, signed: true },
        Ty::U8 => IntTy { bits: 8, signed: false },
        Ty::U16 => IntTy { bits: 16, signed: false },
        Ty::U32 | Ty::Char => IntTy { bits: 32, signed: false },
        Ty::U64 | Ty::Usize => IntTy { bits: 64, signed: false },
        _ => return None,
    })
}

/// The leaf layout of a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Shape {
    /// One integer (or bool) leaf.
    Int(IntTy),
    /// One pointer leaf.
    Ptr,
    /// No leaves (`()`, `PhantomData`, never).
    Unit,
    /// Fields in order. An enum is `[tag, lane 1, lane 2, …]` (trust-ir's
    /// tagged union: lane `i >= 1` is field `i - 1` of the active variant).
    Agg(Vec<Shape>),
    /// A value the census does not lay out (floats, wide integers, large
    /// arrays, variants whose lanes disagree): one untracked leaf.
    Blob,
}

const MAX_DEPTH: usize = 12;
const MAX_ARRAY: u64 = 8;

/// The shape of `ty`.
#[must_use]
pub fn shape_of(m: &Module, ty: &Ty) -> Shape {
    shape_at(m, ty, 0)
}

fn shape_at(m: &Module, ty: &Ty, depth: usize) -> Shape {
    if depth > MAX_DEPTH {
        return Shape::Blob;
    }
    if let Some(i) = int_ty(ty) {
        return Shape::Int(i);
    }
    match ty {
        Ty::Ptr
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Func(_) => Shape::Ptr,
        // (data, metadata)
        Ty::FatPtr(_) => {
            Shape::Agg(vec![Shape::Ptr, Shape::Int(IntTy { bits: 64, signed: false })])
        }
        Ty::Unit | Ty::Never => Shape::Unit,
        Ty::Tuple(tys) => Shape::Agg(tys.iter().map(|t| shape_at(m, t, depth + 1)).collect()),
        Ty::Struct(id) => match m.structs.iter().find(|s| s.id == *id) {
            Some(s) if s.fields.is_empty() => Shape::Unit,
            Some(s) => Shape::Agg(s.fields.iter().map(|f| shape_at(m, &f.ty, depth + 1)).collect()),
            None => Shape::Blob,
        },
        Ty::Enum(id) => match m.enums.iter().find(|e| e.id == *id) {
            Some(e) => {
                let lanes = e.variants.iter().map(|v| v.fields.len()).max().unwrap_or(0);
                let mut out = vec![Shape::Int(IntTy { bits: 64, signed: true })];
                for lane in 0..lanes {
                    let mut common: Option<Shape> = None;
                    let mut agree = true;
                    for v in &e.variants {
                        if let Some(t) = v.fields.get(lane) {
                            let s = shape_at(m, t, depth + 1);
                            match &common {
                                None => common = Some(s),
                                Some(c) if *c == s => {}
                                Some(_) => agree = false,
                            }
                        }
                    }
                    out.push(if agree { common.unwrap_or(Shape::Unit) } else { Shape::Blob });
                }
                Shape::Agg(out)
            }
            None => Shape::Blob,
        },
        Ty::Array(elem, n) if *n <= MAX_ARRAY => match m.types.get(elem.as_usize()) {
            Some(t) => {
                let s = shape_at(m, t, depth + 1);
                Shape::Agg((0..*n).map(|_| s.clone()).collect())
            }
            None => Shape::Blob,
        },
        Ty::Closure(id) => match m.closure_types.get(id.as_usize()) {
            Some(c) => Shape::Agg(c.captures.iter().map(|t| shape_at(m, t, depth + 1)).collect()),
            None => Shape::Blob,
        },
        _ => Shape::Blob,
    }
}

impl Shape {
    /// Number of leaves (Int, Ptr and Blob are one each).
    #[must_use]
    pub fn leaf_count(&self) -> usize {
        match self {
            Shape::Int(_) | Shape::Ptr | Shape::Blob => 1,
            Shape::Unit => 0,
            Shape::Agg(v) => v.iter().map(Shape::leaf_count).sum(),
        }
    }
}

/// Struct names that own an open descriptor (their drop is a `close`).
/// Matched against the struct's name with generic arguments removed, so
/// `Vec<OwnedFd>`'s `PhantomData<OwnedFd>` marker is not a carrier but a
/// `std::vec::Vec<std::os::fd::OwnedFd>` is found through its name.
pub const FD_CARRIERS: &[&str] = &[
    "std::os::fd::OwnedFd",
    "std::os::fd::owned::OwnedFd",
    "std::fs::File",
    "std::os::unix::net::UnixStream",
    "std::os::unix::net::UnixListener",
    "std::os::unix::net::UnixDatagram",
    "std::net::TcpStream",
    "std::net::TcpListener",
    "std::net::UdpSocket",
    "std::process::ChildStdin",
    "std::process::ChildStdout",
    "std::process::ChildStderr",
    "std::io::PipeReader",
    "std::io::PipeWriter",
    "std::sys::fd::unix::FileDesc",
];

fn base_name(name: &str) -> &str {
    name.split('<').next().unwrap_or(name)
}

fn is_marker(name: &str) -> bool {
    let b = base_name(name);
    b.ends_with("PhantomData") || b.ends_with("BorrowedFd")
}

fn has_fd_carrier_arg(name: &str) -> bool {
    if !name.contains('<') {
        return false;
    }
    FD_CARRIERS.iter().any(|c| {
        name.match_indices(c).any(|(idx, _)| {
            idx > 0
                && name.as_bytes()[idx - 1] == b'<'
                && name.as_bytes().get(idx + c.len()) == Some(&b'>')
        })
    })
}

/// The first descriptor-carrier type `ty` holds by value, if any (through
/// struct fields, tuple and enum lanes, arrays and closure captures; a
/// pointer holds nothing by value).
#[must_use]
pub fn fd_carrier_in(m: &Module, ty: &Ty) -> Option<String> {
    carrier_at(m, ty, 0)
}

fn carrier_at(m: &Module, ty: &Ty, depth: usize) -> Option<String> {
    if depth > MAX_DEPTH {
        return None;
    }
    match ty {
        Ty::Struct(id) => {
            let s = m.structs.iter().find(|s| s.id == *id)?;
            if is_marker(&s.name) {
                return None;
            }
            if FD_CARRIERS.contains(&base_name(&s.name)) || has_fd_carrier_arg(&s.name) {
                return Some(s.name.clone());
            }
            s.fields.iter().find_map(|f| carrier_at(m, &f.ty, depth + 1))
        }
        Ty::Enum(id) => {
            let e = m.enums.iter().find(|e| e.id == *id)?;
            e.variants
                .iter()
                .flat_map(|v| v.fields.iter())
                .find_map(|t| carrier_at(m, t, depth + 1))
        }
        Ty::Tuple(tys) => tys.iter().find_map(|t| carrier_at(m, t, depth + 1)),
        Ty::Array(elem, _) => {
            m.types.get(elem.as_usize()).and_then(|t| carrier_at(m, t, depth + 1))
        }
        Ty::Closure(id) => m
            .closure_types
            .get(id.as_usize())
            .and_then(|c| c.captures.iter().find_map(|t| carrier_at(m, t, depth + 1))),
        _ => None,
    }
}

/// std composites that own descriptors through fields but are not one
/// carrier (`trust_platform::symbols`' drop gaps): their drop closes
/// several, or some.
const OWNING_COMPOSITES: &[&str] =
    &["std::process::Child", "std::process::Command", "std::process::Stdio"];

/// The types (base names, generic arguments removed) whose `Drop` impl is in
/// the module: `<T as std::ops::Drop>::drop` (or `core::ops::Drop`), as a
/// body or a declaration. Their drop glue runs that impl — user code.
#[must_use]
pub fn drop_impl_types(m: &Module) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    for f in &m.functions {
        let raw = f.display_path.as_deref().unwrap_or(&f.name);
        if !raw.contains("Drop>::drop") {
            continue;
        }
        let owned = crate::stub::instance_path(raw);
        let name = owned.as_deref().unwrap_or(raw);
        let Some(inner) = name.strip_prefix('<') else { continue };
        for tr in [" as std::ops::Drop>::drop", " as core::ops::Drop>::drop"] {
            if let Some(ty) = inner.strip_suffix(tr) {
                out.insert(base_name(ty).to_string());
            }
        }
    }
    out
}

/// The first type `ty` holds BY VALUE whose drop glue may have a platform
/// effect (Critique C-2, widened by the review's F2): an fd carrier (its
/// drop closes), a type with a `Drop` impl in `impls` (user code), or a std
/// composite that owns descriptors. Through struct fields, tuple and enum
/// lanes, arrays and closure captures; a pointer holds nothing by value.
#[must_use]
pub fn effectful_drop(
    m: &Module,
    ty: &Ty,
    impls: &std::collections::BTreeSet<String>,
) -> Option<String> {
    effectful_at(m, ty, impls, 0)
}

fn effectful_at(
    m: &Module,
    ty: &Ty,
    impls: &std::collections::BTreeSet<String>,
    depth: usize,
) -> Option<String> {
    if depth > MAX_DEPTH {
        return None;
    }
    match ty {
        Ty::Struct(id) => {
            let s = m.structs.iter().find(|s| s.id == *id)?;
            if is_marker(&s.name) {
                return None;
            }
            let base = base_name(&s.name);
            if FD_CARRIERS.contains(&base)
                || has_fd_carrier_arg(&s.name)
                || OWNING_COMPOSITES.contains(&base)
                || impls.contains(base)
            {
                return Some(s.name.clone());
            }
            s.fields.iter().find_map(|f| effectful_at(m, &f.ty, impls, depth + 1))
        }
        Ty::Enum(id) => {
            let e = m.enums.iter().find(|e| e.id == *id)?;
            if impls.contains(base_name(&e.name)) {
                return Some(e.name.clone());
            }
            e.variants
                .iter()
                .flat_map(|v| v.fields.iter())
                .find_map(|t| effectful_at(m, t, impls, depth + 1))
        }
        Ty::Tuple(tys) => tys.iter().find_map(|t| effectful_at(m, t, impls, depth + 1)),
        Ty::Array(elem, _) => {
            m.types.get(elem.as_usize()).and_then(|t| effectful_at(m, t, impls, depth + 1))
        }
        Ty::Closure(id) => m
            .closure_types
            .get(id.as_usize())
            .and_then(|c| c.captures.iter().find_map(|t| effectful_at(m, t, impls, depth + 1))),
        _ => None,
    }
}

/// Whether `ty`'s drop glue is certainly empty: integers, bools, pointers,
/// references, unit, and tuples/arrays of those (no struct, enum or closure
/// by value, whose glue the census cannot see).
#[must_use]
pub fn trivially_dropped(m: &Module, ty: &Ty) -> bool {
    match ty {
        Ty::Tuple(tys) => tys.iter().all(|t| trivially_dropped(m, t)),
        Ty::Array(elem, _) => m.types.get(elem.as_usize()).is_some_and(|t| trivially_dropped(m, t)),
        Ty::Ptr
        | Ty::FatPtr(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Func(_)
        | Ty::Unit
        | Ty::Never
        | Ty::F16
        | Ty::F32
        | Ty::F64 => true,
        _ => int_ty(ty).is_some(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEXT: &str = r#"; TrustIr text format v1
module "m"
struct @"core::num::niche_types::I32NotAllOnes" { 0: i32 @0 } size=4 align=4 repr=transparent id=0
struct @"std::os::fd::OwnedFd" { fd: struct.0 @0 } size=4 align=4 repr=transparent id=1
struct @"std::marker::PhantomData<std::os::fd::OwnedFd>" {  } size=0 align=1 id=2
struct @Holder { a: i32 @0, f: struct.1 @4 } size=8 align=4 id=3
struct @"std::os::fd::BorrowedFd<'_>" { fd: struct.0 @0, _p: struct.2 } size=4 align=4 id=4
"#;

    #[test]
    fn carriers_are_found_through_fields_and_markers_are_not_carriers() {
        let m = trust_ir::parser::parse_module(TEXT).expect("parses");
        let s = |i| Ty::Struct(trust_ir::StructId::new(i));
        assert_eq!(fd_carrier_in(&m, &s(1)).as_deref(), Some("std::os::fd::OwnedFd"));
        assert_eq!(fd_carrier_in(&m, &s(3)).as_deref(), Some("std::os::fd::OwnedFd"));
        assert_eq!(fd_carrier_in(&m, &s(2)), None, "PhantomData owns nothing");
        assert_eq!(fd_carrier_in(&m, &s(4)), None, "a BorrowedFd is not dropped");
        assert_eq!(fd_carrier_in(&m, &Ty::Ptr), None, "a pointer holds nothing by value");
        // OwnedFd is one i32 leaf (through I32NotAllOnes).
        assert_eq!(shape_of(&m, &s(1)).leaf_count(), 1);
        assert_eq!(shape_of(&m, &s(3)).leaf_count(), 2);
    }

    #[test]
    fn int_ranges() {
        assert_eq!(IntTy::I32.max(), i64::from(i32::MAX));
        assert_eq!(IntTy::I32.min(), i64::from(i32::MIN));
        let u32t = IntTy { bits: 32, signed: false };
        assert_eq!(u32t.max(), i64::from(u32::MAX));
        assert!(!u32t.contains(-1));
    }
}
