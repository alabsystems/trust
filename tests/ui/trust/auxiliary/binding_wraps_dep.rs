//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency's generic code that writes through the pointer it is given
//! where its own body does not show it: after wrapping the pointer, or in a
//! blanket impl its trait-method call resolves to at the instance called.

pub fn reset_opt<T: Default>(slot: Option<&mut T>) {
    if let Some(slot) = slot {
        *slot = T::default();
    }
}

pub fn reset_via_opt<T: Default>(slot: &mut T) {
    reset_opt(Some(slot))
}

pub fn take_via_map<T: Default>(slot: &mut T) {
    let _ = Some(slot).map(std::mem::take);
}

pub trait Wipe {
    fn wipe(&mut self);
}

impl<T: Default> Wipe for T {
    fn wipe(&mut self) {
        *self = T::default();
    }
}

pub fn wipe_it<T: Wipe>(slot: &mut T) {
    slot.wipe()
}

/// Hands the pointer to the caller's closure: what is written is in there.
pub fn with<T>(slot: &mut T, f: impl FnOnce(&mut T)) {
    f(slot)
}

/// A run loop: it is given the handler and the receiver, wraps the handler in
/// a closure for its own driver, and writes nothing itself.
pub trait Handler<T> {
    fn user_event(&mut self, event: T);
}

fn drive<F: FnMut() -> bool>(mut step: F) {
    while step() {}
}

pub fn run_app<T, H: Handler<T>>(app: &mut H, rx: std::sync::mpsc::Receiver<T>) {
    drive(|| match rx.recv() {
        Ok(event) => {
            app.user_event(event);
            true
        }
        Err(_) => false,
    });
}

/// A type of the dependency's own, with a setter whose body comes with the
/// crate.
#[derive(Default)]
pub struct Cfg {
    pub level: u8,
    pub theme: u8,
}

impl Cfg {
    #[inline]
    pub fn set_level(&mut self, level: u8) {
        self.level = level;
    }
}
