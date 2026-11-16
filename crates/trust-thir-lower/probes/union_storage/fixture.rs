#![allow(dead_code, improper_ctypes)]
use std::mem::ManuallyDrop;

#[repr(C)]
union Plain { inline: ManuallyDrop<[u64; 2]>, heap: (*mut u8, usize) }
#[repr(C)]
struct Parent { head: u64, storage: Plain, tail: u64 }
fn case_union_tail(x: &Parent) -> &u64 { &x.tail }
fn case_union_read(x: &Parent) -> u64 { x.tail }
fn case_union_identity(x: Plain) -> Plain { x }
fn case_parent_identity(x: Parent) -> Parent { x }
unsafe fn case_union_load(x: *const Plain) -> Plain { unsafe { x.read() } }
unsafe fn case_union_store(x: *mut Plain, value: Plain) { unsafe { x.write(value) } }
unsafe extern "C" { fn sink(value: Plain); fn produce() -> Plain; }
fn case_union_arg(value: Plain) { unsafe { sink(value) } }
fn case_union_result() -> Plain { unsafe { produce() } }

// Same geometry, genuinely distinct nominal destructors. Neither is licensed
// by a geometry witness or selected by matching the byte count.
#[repr(C)]
union DropA { words: [u64; 2] }
impl Drop for DropA { fn drop(&mut self) { self.words = [11, 11]; } }
#[repr(C)]
union DropB { words: [u64; 2] }
impl Drop for DropB { fn drop(&mut self) { self.words = [29, 29]; } }
#[repr(C)]
struct DropParentA { head: u64, storage: DropA, tail: u64 }
#[repr(C)]
struct DropParentB { head: u64, storage: DropB, tail: u64 }
fn case_drop_a_ref(x: &DropParentA) -> &u64 { &x.tail }
fn case_drop_b_ref(x: &DropParentB) -> &u64 { &x.tail }
fn case_drop_a_identity(x: DropA) -> DropA { x }
fn case_drop_b_identity(x: DropB) -> DropB { x }
fn case_drop_a_explicit(x: DropA) { drop(x) }

#[repr(C)]
struct SameStruct { words: [u64; 2] }
enum SameEnum { Words([u64; 2]) }
fn case_struct_identity(x: &SameStruct) { let _ = x; }
fn case_enum_identity(x: &SameEnum) { let _ = x; }
#[repr(C)]
union Generic<T> { payload: ManuallyDrop<T>, other: u64 }
fn case_generic_u64(x: &Generic<u64>) { let _ = x; }
fn case_generic_array(x: &Generic<[u64; 3]>) { let _ = x; }
#[repr(C, packed)]
struct PackedParent { head: u8, storage: Plain, tail: u64 }
fn case_packed_read(x: &PackedParent) -> u64 { x.tail }
fn main() {}
