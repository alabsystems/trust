// Environment records: declarative frames with TDZ-aware bindings, and the
// function-environment extras (`this`, `new.target`) resolved lexically so
// arrows inherit them for free.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::value::{EnvId, JsValue, ObjId};
use std::collections::HashMap;

/// One declarative binding.
#[derive(Debug, Clone)]
pub struct Binding {
    pub value: JsValue,
    pub mutable: bool,
    /// false = TDZ (declared, not yet initialized).
    pub initialized: bool,
    /// For immutable bindings: CreateImmutableBinding's [[Strict]] flag.
    /// `true` (const) throws on any write; `false` (the named function
    /// expression self-binding, the `arguments` binding of strict functions)
    /// makes sloppy writes a silent no-op and strict writes a TypeError.
    pub strict_immutable: bool,
    /// CreateMutableBinding's `canBeDeleted` flag. Only the var/function
    /// bindings a sloppy `eval` introduces into a function scope set this; a
    /// `delete name` targeting one removes it (all other declarative bindings
    /// are non-deletable — `delete` returns false).
    pub deletable: bool,
}

impl Binding {
    /// An ordinary initialized mutable binding.
    #[must_use]
    pub fn var(value: JsValue) -> Binding {
        Binding {
            value,
            mutable: true,
            initialized: true,
            strict_immutable: false,
            deletable: false,
        }
    }

    /// A deletable mutable binding: the var/function binding a sloppy `eval`
    /// introduces into a function variable environment (CreateMutableBinding
    /// with canBeDeleted = true).
    #[must_use]
    pub fn var_deletable(value: JsValue) -> Binding {
        Binding {
            value,
            mutable: true,
            initialized: true,
            strict_immutable: false,
            deletable: true,
        }
    }

    /// An uninitialized (TDZ) binding; `mutable` = let vs const.
    #[must_use]
    pub fn tdz(mutable: bool) -> Binding {
        Binding {
            value: JsValue::Undefined,
            mutable,
            initialized: false,
            strict_immutable: !mutable,
            deletable: false,
        }
    }
}

/// One environment frame. `this_val`/`new_target` are `Some` only on
/// function environments (and the script root); arrows allocate frames
/// without them, so lexical `this` resolution is a parent walk.
/// `this_uninit` marks a derived-class-constructor frame whose `this` is in
/// TDZ until `super()` binds it. `home_object` carries the [[HomeObject]]
/// for `super.x` resolution; `active_fn` the running function object (for
/// GetSuperConstructor).
#[derive(Debug)]
pub struct EnvFrame {
    pub parent: Option<EnvId>,
    pub bindings: HashMap<String, Binding>,
    pub this_val: Option<JsValue>,
    pub this_uninit: bool,
    pub new_target: Option<JsValue>,
    pub home_object: Option<ObjId>,
    pub active_fn: Option<ObjId>,
    /// True on a function's VARIABLE environment (the frame `var`-scoped
    /// names hoist into). A sloppy direct `eval` finds the caller's variable
    /// environment by walking to the nearest frame with this flag set; the
    /// absence of one means the variable environment is the global object.
    pub var_scope: bool,
}

impl EnvFrame {
    #[must_use]
    pub fn new(parent: Option<EnvId>) -> EnvFrame {
        EnvFrame {
            parent,
            bindings: HashMap::new(),
            this_val: None,
            this_uninit: false,
            new_target: None,
            home_object: None,
            active_fn: None,
            var_scope: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tdz_binding_states() {
        let b = Binding::tdz(true);
        assert!(!b.initialized && b.mutable && !b.strict_immutable);
        let c = Binding::tdz(false);
        assert!(!c.initialized && !c.mutable && c.strict_immutable);
        let v = Binding::var(JsValue::Num(1.0));
        assert!(v.initialized && v.mutable);
    }
}
