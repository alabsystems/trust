#![feature(no_core, lang_items, auto_traits)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub auto trait Freeze {}
impl Copy for u64 {}
#[unsafe(no_mangle)]
pub extern "C" fn trust_bootstrap_native_object() -> u64 { 42u64 }
