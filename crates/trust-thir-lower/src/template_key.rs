//! Stable, lossless host terms for level-S template instantiation.
//!
//! These keys contain no session-local DefId, debug spelling, type address or
//! runtime placeholder. In particular a closure and a function item retain
//! their defining entity and every positional argument. Regions are erased;
//! their positions remain explicit so reconstruction can check every kind.
//! The S artifact owns parameters. No parameter key is a level-R IR type.

use trust_ir::template::HostKey;

pub mod rustc;

pub const KEY_NAMESPACE: &str = "rust";
pub const KEY_SCHEMA: u32 = 1;
const MAGIC: &[u8; 8] = b"TRSTKEY\0";
const MAX_BYTES: usize = 1 << 20;
const MAX_NODES: usize = 1 << 16;
const MAX_DEPTH: usize = 128;

/// DefPathHash's stable crate identity and definition-local hash.
pub type StableDef = (u64, u64);

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum HoleKey {
    Type(KeyTy),
    Const(KeyConstItem),
    Callee { item: StableDef, args: Vec<KeyArg> },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum KeyConstItem {
    Assoc { item: StableDef, args: Vec<KeyArg> },
    FieldOffset { adt: Box<KeyTy>, variant: u32, field: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum KeyTy {
    Bool,
    Char,
    /// Bits; zero is the target-sized signed/unsigned integer.
    Int(u8),
    Uint(u8),
    Float(u8),
    Str,
    Never,
    Param(u32),
    Adt(StableDef, Vec<KeyArg>),
    Ref { mutable: bool, pointee: Box<KeyTy> },
    RawPtr { mutable: bool, pointee: Box<KeyTy> },
    Slice(Box<KeyTy>),
    Array(Box<KeyTy>, KeyConst),
    Tuple(Vec<KeyTy>),
    FnDef(StableDef, Vec<KeyArg>),
    FnPtr {
        inputs_and_output: Vec<KeyTy>,
        abi: String,
        safe: bool,
        c_variadic: bool,
        splatted: Option<u8>,
    },
    Closure(StableDef, Vec<KeyArg>),
    Projection { item: StableDef, args: Vec<KeyArg>, rigid: bool },
    Foreign(StableDef),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum KeyConst {
    Param(u32),
    /// The width is part of ScalarInt's identity, including on usize/isize.
    Value { bits: u128, bytes: u8, ty: Box<KeyTy> },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum KeyArg {
    Type(KeyTy),
    Const(KeyConst),
    ErasedRegion,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyError(pub &'static str);

impl std::fmt::Display for KeyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str(self.0) }
}
impl std::error::Error for KeyError {}

type Result<T> = std::result::Result<T, KeyError>;

/// Every dependency in first-occurrence order. Lifetimes contribute no value.
pub fn parameters(key: &HoleKey) -> Result<Vec<u32>> {
    encode(key)?;
    type Dependencies = (Vec<u32>, std::collections::BTreeSet<u32>);
    fn add(out: &mut Dependencies, p: u32) { if out.1.insert(p) { out.0.push(p); } }
    fn args(out: &mut Dependencies, values: &[KeyArg]) {
        for a in values { match a {
            KeyArg::Type(t) => ty(out, t),
            KeyArg::Const(c) => konst(out, c),
            KeyArg::ErasedRegion => {}
        }}
    }
    fn konst(out: &mut Dependencies, value: &KeyConst) { match value {
        KeyConst::Param(p) => add(out, *p),
        KeyConst::Value { ty: t, .. } => ty(out, t),
    }}
    fn ty(out: &mut Dependencies, t: &KeyTy) { match t {
        KeyTy::Param(p) => add(out, *p),
        KeyTy::Adt(_, a) | KeyTy::FnDef(_, a) | KeyTy::Closure(_, a)
            | KeyTy::Projection { args: a, .. } => args(out, a),
        KeyTy::Ref { pointee, .. } | KeyTy::RawPtr { pointee, .. }
            | KeyTy::Slice(pointee) => ty(out, pointee),
        KeyTy::Array(t, n) => { ty(out, t); konst(out, n); }
        KeyTy::Tuple(ts) | KeyTy::FnPtr { inputs_and_output: ts, .. } => {
            for t in ts { ty(out, t); }
        }
        KeyTy::Bool | KeyTy::Char | KeyTy::Int(_) | KeyTy::Uint(_) | KeyTy::Float(_)
            | KeyTy::Str | KeyTy::Never | KeyTy::Foreign(_) => {}
    }}
    let mut out = (Vec::new(), std::collections::BTreeSet::new());
    match key {
        HoleKey::Type(t) => ty(&mut out, t),
        HoleKey::Callee { args: a, .. } | HoleKey::Const(KeyConstItem::Assoc { args: a, .. }) => args(&mut out, a),
        HoleKey::Const(KeyConstItem::FieldOffset { adt, .. }) => ty(&mut out, adt),
    }
    Ok(out.0)
}

pub fn encode(key: &HoleKey) -> Result<HostKey> {
    let mut w = Writer { bytes: MAGIC.to_vec(), nodes: 0 };
    w.u32(KEY_SCHEMA);
    match key {
        HoleKey::Type(t) => { w.byte(0); w.ty(t, 0)?; }
        HoleKey::Const(KeyConstItem::Assoc { item, args }) => {
            w.byte(1); w.def(*item); w.args(args, 0)?;
        }
        HoleKey::Const(KeyConstItem::FieldOffset { adt, variant, field }) => {
            w.byte(2); w.ty(adt, 0)?; w.u32(*variant); w.u32(*field);
        }
        HoleKey::Callee { item, args } => { w.byte(3); w.def(*item); w.args(args, 0)?; }
    }
    if w.bytes.len() > MAX_BYTES { return Err(KeyError("template key byte budget")); }
    Ok(HostKey::new(KEY_NAMESPACE, w.bytes))
}

/// Validate a borrowed type before reconstruction; do not clone an untrusted tree.
pub fn encode_type(ty: &KeyTy) -> Result<HostKey> {
    let mut w = Writer { bytes: MAGIC.to_vec(), nodes: 0 };
    w.u32(KEY_SCHEMA);
    w.byte(0);
    w.ty(ty, 0)?;
    if w.bytes.len() > MAX_BYTES { return Err(KeyError("template key byte budget")); }
    Ok(HostKey::new(KEY_NAMESPACE, w.bytes))
}

pub fn decode(key: &HostKey) -> Result<HoleKey> {
    if key.namespace != KEY_NAMESPACE { return Err(KeyError("template key namespace")); }
    if key.bytes.len() > MAX_BYTES { return Err(KeyError("template key byte budget")); }
    let mut r = Reader { bytes: &key.bytes, cursor: 0, nodes: 0, reserved: 0 };
    if r.take(8)? != MAGIC { return Err(KeyError("template key magic")); }
    if r.u32()? != KEY_SCHEMA { return Err(KeyError("template key schema")); }
    let value = match r.byte()? {
        0 => HoleKey::Type(r.ty(0)?),
        1 => HoleKey::Const(KeyConstItem::Assoc { item: r.def()?, args: r.args(0)? }),
        2 => HoleKey::Const(KeyConstItem::FieldOffset { adt: Box::new(r.ty(0)?), variant: r.u32()?, field: r.u32()? }),
        3 => HoleKey::Callee { item: r.def()?, args: r.args(0)? },
        _ => return Err(KeyError("unknown template key kind")),
    };
    if r.cursor != r.bytes.len() { return Err(KeyError("template key trailing bytes")); }
    // One canonical spelling, also checked for programmatically built keys.
    if encode(&value)? != *key { return Err(KeyError("noncanonical template key")); }
    Ok(value)
}

fn width(bits: u8, float: bool) -> Result<()> {
    if if float { matches!(bits, 16 | 32 | 64 | 128) }
        else { matches!(bits, 0 | 8 | 16 | 32 | 64 | 128) }
    { Ok(()) } else { Err(KeyError("template key scalar width")) }
}

fn scalar(bits: u128, bytes: u8, ty: &KeyTy) -> Result<()> {
    let size = match ty {
        KeyTy::Bool => 1,
        KeyTy::Char => 4,
        KeyTy::Int(0) | KeyTy::Uint(0) if matches!(bytes, 4 | 8) => bytes,
        KeyTy::Int(n) | KeyTy::Uint(n) => { width(*n, false)?; *n / 8 }
        KeyTy::Float(n) => { width(*n, true)?; *n / 8 }
        _ => return Err(KeyError("template key constant is not scalar")),
    };
    if !matches!(bytes, 1 | 2 | 4 | 8 | 16) || size != bytes
        || (bytes < 16 && bits >= (1_u128 << (u32::from(bytes) * 8)))
    { return Err(KeyError("template key scalar bits/width disagree")); }
    if matches!(ty, KeyTy::Bool) && bits > 1 { return Err(KeyError("template key invalid bool")); }
    if matches!(ty, KeyTy::Char) && u32::try_from(bits).ok().and_then(char::from_u32).is_none() {
        return Err(KeyError("template key invalid char"));
    }
    Ok(())
}

struct Writer { bytes: Vec<u8>, nodes: usize }
impl Writer {
    fn byte(&mut self, v: u8) { self.bytes.push(v); }
    fn u32(&mut self, v: u32) { self.bytes.extend_from_slice(&v.to_le_bytes()); }
    fn def(&mut self, v: StableDef) {
        self.bytes.extend_from_slice(&v.0.to_le_bytes());
        self.bytes.extend_from_slice(&v.1.to_le_bytes());
    }
    fn node(&mut self, depth: usize) -> Result<()> {
        self.nodes += 1;
        if depth > MAX_DEPTH || self.nodes > MAX_NODES || self.bytes.len() > MAX_BYTES {
            Err(KeyError("template key tree budget"))
        } else { Ok(()) }
    }
    fn len(&mut self, n: usize) -> Result<()> {
        if n > MAX_NODES { return Err(KeyError("template key list budget")); }
        self.u32(n as u32); Ok(())
    }
    fn args(&mut self, args: &[KeyArg], depth: usize) -> Result<()> {
        self.len(args.len())?;
        for a in args { self.node(depth)?; match a {
            KeyArg::Type(t) => { self.byte(0); self.ty(t, depth + 1)?; }
            KeyArg::Const(c) => { self.byte(1); self.konst(c, depth + 1)?; }
            KeyArg::ErasedRegion => self.byte(2),
        }}
        Ok(())
    }
    fn konst(&mut self, c: &KeyConst, depth: usize) -> Result<()> {
        self.node(depth)?;
        match c {
            KeyConst::Param(p) => { self.byte(0); self.u32(*p); }
            KeyConst::Value { bits, bytes, ty } => {
                scalar(*bits, *bytes, ty)?; self.byte(1); self.byte(*bytes);
                self.bytes.extend_from_slice(&bits.to_le_bytes()); self.ty(ty, depth + 1)?;
            }
        }
        Ok(())
    }
    fn ty(&mut self, t: &KeyTy, depth: usize) -> Result<()> {
        self.node(depth)?;
        match t {
            KeyTy::Bool => self.byte(0), KeyTy::Char => self.byte(1),
            KeyTy::Int(n) => { width(*n, false)?; self.byte(2); self.byte(*n); }
            KeyTy::Uint(n) => { width(*n, false)?; self.byte(3); self.byte(*n); }
            KeyTy::Float(n) => { width(*n, true)?; self.byte(4); self.byte(*n); }
            KeyTy::Str => self.byte(5), KeyTy::Never => self.byte(6),
            KeyTy::Param(p) => { self.byte(7); self.u32(*p); }
            KeyTy::Adt(d, a) | KeyTy::FnDef(d, a) | KeyTy::Closure(d, a) => {
                self.byte(match t { KeyTy::Adt(..) => 8, KeyTy::FnDef(..) => 14, _ => 16 });
                self.def(*d); self.args(a, depth + 1)?;
            }
            KeyTy::Ref { mutable, pointee } | KeyTy::RawPtr { mutable, pointee } => {
                self.byte(if matches!(t, KeyTy::Ref { .. }) { 9 } else { 10 });
                self.byte(u8::from(*mutable)); self.ty(pointee, depth + 1)?;
            }
            KeyTy::Slice(t) => { self.byte(11); self.ty(t, depth + 1)?; }
            KeyTy::Array(t, n) => { self.byte(12); self.ty(t, depth + 1)?; self.konst(n, depth + 1)?; }
            KeyTy::Tuple(ts) => {
                self.byte(13); self.len(ts.len())?;
                for t in ts { self.ty(t, depth + 1)?; }
            }
            KeyTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted } => {
                if inputs_and_output.is_empty() || abi.is_empty() || abi.len() > 64 || !abi.is_ascii() {
                    return Err(KeyError("template key function signature"));
                }
                self.byte(15); self.len(inputs_and_output.len())?;
                for t in inputs_and_output { self.ty(t, depth + 1)?; }
                self.byte(abi.len() as u8); self.bytes.extend_from_slice(abi.as_bytes());
                self.byte(u8::from(*safe)); self.byte(u8::from(*c_variadic));
                match splatted { None => self.byte(0), Some(n) => { self.byte(1); self.byte(*n); } }
            }
            KeyTy::Projection { item, args, rigid } => {
                self.byte(17); self.def(*item); self.args(args, depth + 1)?; self.byte(u8::from(*rigid));
            }
            KeyTy::Foreign(d) => { self.byte(18); self.def(*d); }
        }
        Ok(())
    }
}

struct Reader<'a> { bytes: &'a [u8], cursor: usize, nodes: usize, reserved: usize }
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.cursor.checked_add(n).ok_or(KeyError("template key size overflow"))?;
        let value = self.bytes.get(self.cursor..end).ok_or(KeyError("truncated template key"))?;
        self.cursor = end; Ok(value)
    }
    fn byte(&mut self) -> Result<u8> { Ok(self.take(1)?[0]) }
    fn boolean(&mut self) -> Result<bool> { match self.byte()? {
        0 => Ok(false), 1 => Ok(true), _ => Err(KeyError("template key noncanonical bool")),
    }}
    fn u32(&mut self) -> Result<u32> { Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap())) }
    fn def(&mut self) -> Result<StableDef> {
        Ok((u64::from_le_bytes(self.take(8)?.try_into().unwrap()),
            u64::from_le_bytes(self.take(8)?.try_into().unwrap())))
    }
    fn node(&mut self, depth: usize) -> Result<()> {
        self.nodes += 1;
        if depth > MAX_DEPTH || self.nodes > MAX_NODES { Err(KeyError("template key tree budget")) }
        else { Ok(()) }
    }
    fn len(&mut self) -> Result<usize> {
        let n = self.u32()? as usize;
        self.reserved = self.reserved.checked_add(n).ok_or(KeyError("template key list budget"))?;
        if self.reserved > MAX_NODES || n > self.bytes.len() - self.cursor {
            Err(KeyError("template key list budget"))
        } else { Ok(n) }
    }
    fn args(&mut self, depth: usize) -> Result<Vec<KeyArg>> {
        let n = self.len()?; let mut out = Vec::with_capacity(n);
        for _ in 0..n { self.node(depth)?; out.push(match self.byte()? {
            0 => KeyArg::Type(self.ty(depth + 1)?),
            1 => KeyArg::Const(self.konst(depth + 1)?),
            2 => KeyArg::ErasedRegion,
            _ => return Err(KeyError("unknown template key argument kind")),
        }); }
        Ok(out)
    }
    fn konst(&mut self, depth: usize) -> Result<KeyConst> {
        self.node(depth)?;
        match self.byte()? {
            0 => Ok(KeyConst::Param(self.u32()?)),
            1 => { let bytes = self.byte()?; let bits = u128::from_le_bytes(self.take(16)?.try_into().unwrap());
                let ty = Box::new(self.ty(depth + 1)?); scalar(bits, bytes, &ty)?;
                Ok(KeyConst::Value { bits, bytes, ty }) }
            _ => Err(KeyError("unknown template key constant kind")),
        }
    }
    fn ty(&mut self, depth: usize) -> Result<KeyTy> {
        self.node(depth)?;
        Ok(match self.byte()? {
            0 => KeyTy::Bool, 1 => KeyTy::Char,
            2 => { let n = self.byte()?; width(n, false)?; KeyTy::Int(n) }
            3 => { let n = self.byte()?; width(n, false)?; KeyTy::Uint(n) }
            4 => { let n = self.byte()?; width(n, true)?; KeyTy::Float(n) }
            5 => KeyTy::Str, 6 => KeyTy::Never, 7 => KeyTy::Param(self.u32()?),
            tag @ (8 | 14 | 16) => { let d = self.def()?; let a = self.args(depth + 1)?;
                match tag { 8 => KeyTy::Adt(d, a), 14 => KeyTy::FnDef(d, a), _ => KeyTy::Closure(d, a) } }
            tag @ (9 | 10) => { let mutable = self.boolean()?; let pointee = Box::new(self.ty(depth + 1)?);
                if tag == 9 { KeyTy::Ref { mutable, pointee } } else { KeyTy::RawPtr { mutable, pointee } } }
            11 => KeyTy::Slice(Box::new(self.ty(depth + 1)?)),
            12 => KeyTy::Array(Box::new(self.ty(depth + 1)?), self.konst(depth + 1)?),
            13 => { let n = self.len()?; let mut ts = Vec::with_capacity(n);
                for _ in 0..n { ts.push(self.ty(depth + 1)?); } KeyTy::Tuple(ts) }
            15 => { let n = self.len()?; let mut inputs_and_output = Vec::with_capacity(n);
                for _ in 0..n { inputs_and_output.push(self.ty(depth + 1)?); }
                let n = usize::from(self.byte()?);
                let abi = std::str::from_utf8(self.take(n)?).map_err(|_| KeyError("template key ABI encoding"))?.to_owned();
                let safe = self.boolean()?; let c_variadic = self.boolean()?;
                let splatted = match self.byte()? { 0 => None, 1 => Some(self.byte()?), _ => return Err(KeyError("template key function kind")) };
                KeyTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted } }
            17 => KeyTy::Projection { item: self.def()?, args: self.args(depth + 1)?, rigid: self.boolean()? },
            18 => KeyTy::Foreign(self.def()?),
            _ => return Err(KeyError("unknown template key type kind")),
        })
    }
}

#[cfg(test)]
mod tests;
