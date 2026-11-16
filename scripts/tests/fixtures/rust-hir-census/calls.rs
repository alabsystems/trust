// Trust: λ makes raw byte positions differ from character positions.
#![allow(dead_code)]
pub fn leaf() {}
use leaf as alias;
pub struct Concrete;
impl Concrete { pub fn inherent(&self) {} }
pub trait Action { fn action(&self); }
impl Action for Concrete { fn action(&self) {} }
pub fn direct() { leaf(); }
pub fn method(x: &Concrete) { x.inherent(); }
pub fn trait_method(x: &Concrete) { x.action(); }
pub fn through_alias() { alias(); }
pub fn generic<T: Action>(x: &T) { x.action(); }
pub fn dynamic(x: &dyn Action) { x.action(); }
pub fn pointer(f: fn()) { f(); }
pub fn closure() { let f = || {}; f(); }
pub fn empty() {}
#[cfg(any())]
pub fn excluded() { leaf(); }
macro_rules! invoke { () => { leaf() }; }
pub fn expanded() { invoke!(); invoke!(); }
pub fn nested() { let _f = || leaf(); }
pub const VALUE: () = { const fn local() {} local() };
pub async fn asynchronous() { leaf(); }
