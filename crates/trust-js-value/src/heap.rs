// The heap: object and environment arenas. No unsafe, no GC — totality is
// enforced by the interpreter's resource caps, and arena handles are plain
// indices.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::env::EnvFrame;
use crate::object::JsObject;
use crate::units::Units;
use crate::value::{EnvId, ObjId, SymId};

#[derive(Debug, Default)]
pub struct Heap {
    pub objects: Vec<JsObject>,
    pub envs: Vec<EnvFrame>,
    /// User-symbol descriptions ([[Description]]); indexed by `SymId::User`.
    pub symbols: Vec<Option<Units>>,
}

impl Heap {
    #[must_use]
    pub fn new() -> Heap {
        Heap::default()
    }

    #[must_use]
    pub fn obj(&self, id: ObjId) -> &JsObject {
        &self.objects[id.0 as usize]
    }

    pub fn obj_mut(&mut self, id: ObjId) -> &mut JsObject {
        &mut self.objects[id.0 as usize]
    }

    pub fn alloc(&mut self, o: JsObject) -> ObjId {
        let id = ObjId(u32::try_from(self.objects.len()).expect("heap bounded by interpreter caps"));
        self.objects.push(o);
        id
    }

    #[must_use]
    pub fn env(&self, id: EnvId) -> &EnvFrame {
        &self.envs[id.0 as usize]
    }

    pub fn env_mut(&mut self, id: EnvId) -> &mut EnvFrame {
        &mut self.envs[id.0 as usize]
    }

    pub fn alloc_env(&mut self, frame: EnvFrame) -> EnvId {
        let id = EnvId(u32::try_from(self.envs.len()).expect("envs bounded by interpreter caps"));
        self.envs.push(frame);
        id
    }

    /// Allocate a fresh user symbol with the given [[Description]].
    pub fn alloc_symbol(&mut self, desc: Option<Units>) -> SymId {
        let id =
            u32::try_from(self.symbols.len()).expect("symbols bounded by interpreter caps");
        self.symbols.push(desc);
        SymId::User(id)
    }

    /// The [[Description]] of a symbol (well-known symbols carry their
    /// projection name).
    #[must_use]
    pub fn sym_description(&self, s: SymId) -> Option<Units> {
        match s {
            SymId::WellKnown(wk) => Some(crate::units::units_from_str(wk.projection_name())),
            SymId::User(i) => self.symbols.get(i as usize).cloned().flatten(),
        }
    }
}
