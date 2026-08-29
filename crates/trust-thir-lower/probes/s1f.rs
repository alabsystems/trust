// LANE S1F — the S1 FORWARDER tranche: the 32 single-call `call ret` bodies the CF plan refuses.
// Each body reproduces, shape for shape, one of the census's receiver classes on custom types,
// with the REAL derive expansions where the census body is a derive.
#![allow(dead_code, clippy::all)]
use std::collections::HashMap;

// (a) FIELD-RECEIVER autoref, `&HashMap` / `&Vec` (== cache::TypeCheckCache::len, Cofib::is_bot)
pub struct Cache {
    results: HashMap<u64, u64>,
}
impl Cache {
    pub fn a1_len(&self) -> usize {
        self.results.len()
    }
    pub fn a2_is_empty(&self) -> bool {
        self.results.is_empty()
    }
    // mixed: field receiver + bare ref param  (== SimpExtState::contains)
    pub fn a3_contains(&self, name: &u64) -> bool {
        self.results.contains_key(name)
    }
}
pub struct Cofib {
    disjuncts: Vec<u32>,
}
impl Cofib {
    pub fn a4_is_bot(&self) -> bool {
        self.disjuncts.is_empty()
    }
}

// (e) DERIVED Ord on a newtype, `&u64` (== <FVarId as Ord>::cmp); derived PartialEq on a
//     Vec-field struct, `&Vec` (== <VcBatch as PartialEq>::eq)
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FVarId(pub u64);
#[derive(Clone, PartialEq, Eq)]
pub struct VcBatch {
    pub obligations: Vec<u32>,
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoryValue(pub u8);
// the SAME two shapes, hand-written, to separate "derive" from "spelling"
impl FVarId {
    pub fn e1_cmp_hand(&self, other: &FVarId) -> std::cmp::Ordering {
        Ord::cmp(&self.0, &other.0)
    }
}
impl VcBatch {
    pub fn e2_eq_hand(&self, other: &VcBatch) -> bool {
        self.obligations == other.obligations
    }
}

// (b) UNIT STATEMENT CALL (== TrustedEnvExt::init_quot, TypeChecker::pop_binder_local)
pub struct Env {
    n: u64,
}
impl Env {
    #[inline(never)]
    pub fn init_quot_inner(&mut self) {
        self.n += 1;
    }
    pub fn b1_init_quot(&mut self) {
        Env::init_quot_inner(self);
    }
    #[inline(never)]
    pub fn ctx_pop(&self) {
        let _ = self.n;
    }
    pub fn b2_pop_binder_local(&self) {
        self.ctx_pop();
    }
}

// (c) REBORROWED RETURN (== <PooledBuilder as Deref>::deref)
pub struct Res {
    x: u64,
}
pub struct Pooled {
    resources: Option<Res>,
}
impl Pooled {
    pub fn resources(&self) -> &Res {
        self.resources.as_ref().expect("inv")
    }
}
impl std::ops::Deref for Pooled {
    type Target = Res;
    fn deref(&self) -> &Self::Target {
        self.resources()
    }
}

// (d) OVERLOADED-DEREF COERCION of `self` (== <LevelArc as AsRef<Level>>::as_ref)
pub struct Level {
    v: u64,
}
pub struct LevelArc(Option<std::sync::Arc<Level>>);
impl std::ops::Deref for LevelArc {
    type Target = Level;
    fn deref(&self) -> &Level {
        self.0.as_deref().expect("live")
    }
}
impl AsRef<Level> for LevelArc {
    fn as_ref(&self) -> &Level {
        self
    }
}
