#![allow(dead_code, private_interfaces)]
use std::mem::{ManuallyDrop, MaybeUninit};

struct Payload(u64);
impl Drop for Payload {
    fn drop(&mut self) {}
}

#[repr(C)]
struct Parent {
    head: u64,
    storage: MaybeUninit<[Payload; 2]>,
    tail: u64,
}
impl Drop for Parent {
    fn drop(&mut self) {}
}

// Address-only access to initialized siblings does not read the union or
// require the payload's Drop implementation to run.
fn case_head(parent: &Parent) -> &u64 {
    &parent.head
}
fn case_tail(parent: &Parent) -> &u64 {
    &parent.tail
}
fn case_read_tail(parent: &Parent) -> u64 {
    parent.tail
}

// This mirrors the representation boundary in the original SmallVec sibling:
// an enum payload holds actual MaybeUninit, while another variant holds a
// pointer and length. No active variant is selected or read here.
enum Buffer {
    Inline(MaybeUninit<[Payload; 2]>),
    Heap { ptr: std::ptr::NonNull<Payload>, len: usize },
}
#[repr(C)]
struct EnumParent {
    head: u64,
    buffer: Buffer,
    tail: u64,
}
impl Drop for EnumParent {
    fn drop(&mut self) {}
}
fn case_enum_tail(parent: &EnumParent) -> &u64 {
    &parent.tail
}
fn case_enum_identity(buffer: Buffer) -> Buffer {
    buffer
}

// These are valid Rust, but remain outside the storage-only IR contract.
fn case_value_identity(storage: MaybeUninit<u64>) -> MaybeUninit<u64> {
    storage
}
fn case_parent_identity(parent: Parent) -> Parent {
    parent
}

// Matching size, alignment and field spelling do not make a union the
// compiler's actual MaybeUninit lang item.
union Lookalike {
    unit: (),
    value: ManuallyDrop<[Payload; 2]>,
}
#[repr(C)]
struct LookalikeParent {
    head: u64,
    storage: Lookalike,
    tail: u64,
}
fn case_lookalike(parent: &LookalikeParent) -> &u64 {
    &parent.tail
}

fn main() {}
