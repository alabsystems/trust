//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_dyn_closure.rs` and its `_holds` twin:
#![forbid(unsafe_code)]
//! A dependency whose fns pass a fn item BY NAME to std's `Iterator::map` (`.map(tag)`), and twins
//! that pass a closure calling it (`.map(|t| tag(t))`). Safe, and sound: nothing is put over anything.
fn tag<T>(t: T) -> (u8, T) { (0, t) }
pub fn tag_all_item<T>(v: Vec<T>) -> Vec<(u8, T)> { v.into_iter().map(tag).collect() }
pub fn tag_all_closure<T>(v: Vec<T>) -> Vec<(u8, T)> { v.into_iter().map(|t| tag(t)).collect() }
pub fn wrap_all_item<T>(v: Vec<T>) -> Vec<Option<T>> { v.into_iter().map(Some).collect() }
pub fn wrap_all_closure<T>(v: Vec<T>) -> Vec<Option<T>> { v.into_iter().map(|t| Some(t)).collect() }
fn touch<T>(t: &mut T) -> usize { let _ = t; 1 }
pub fn each_dyn<T>(v: &mut [T]) -> usize { let f: &dyn Fn(&mut T) -> usize = &|t| touch(t); let mut n = 0; for x in v.iter_mut() { n += f(x) } n }
pub fn each_closure<T>(v: &mut [T]) -> usize { let f = |t: &mut T| touch(t); let mut n = 0; for x in v.iter_mut() { n += f(x) } n }
pub fn each_ptr<T>(v: &mut [T]) -> usize { let f: fn(&mut T) -> usize = touch::<T>; let mut n = 0; for x in v.iter_mut() { n += f(x) } n }
