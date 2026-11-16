//@ check-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! The owning run-make test checks the actual emitted addresses and coverage.
//! This UI compilation alone is neither a lowering nor a codegen acceptance claim.

#![crate_type = "lib"]

use std::cell::{Cell, RefCell};

pub fn touch_cell(c: &Cell<u32>) {
    c.set(7);
}

pub fn read_cell(c: &Cell<u32>) -> u32 {
    c.get()
}

pub fn cell_parameter(c: Cell<u32>) -> u32 {
    touch_cell(&c);
    touch_cell(&c);
    read_cell(&c)
}

pub fn cell_local(c: Cell<u32>) -> u32 {
    let local = c;
    touch_cell(&local);
    read_cell(&local)
}

// Source-level restoration of the bug: mutate a fresh object initialized with
// the original's value, then read the original. This intentionally has two homes.
pub fn cell_copy_mutant(c: Cell<u32>) -> u32 {
    let copied = Cell::new(read_cell(&c));
    touch_cell(&copied);
    read_cell(&c)
}

#[repr(C)]
pub struct CellField {
    pub prefix: u32,
    pub cell: Cell<u32>,
}

pub fn cell_field_parameter(c: CellField) -> u32 {
    touch_cell(&c.cell);
    read_cell(&c.cell)
}

pub fn cell_field_local(value: u32) -> u32 {
    let local = CellField { prefix: 19, cell: Cell::new(value) };
    touch_cell(&local.cell);
    read_cell(&local.cell)
}

// The value-producing block moves the aggregate into a temporary. A field
// borrowed from it cannot be substituted with the original parameter's home.
pub fn nonfreeze_field_copy(c: CellField) -> u32 {
    read_cell(&{ c }.cell)
}

pub fn cell_field_raw_tail_escape(value: u32) -> *const Cell<u32> {
    let local = CellField { prefix: 19, cell: Cell::new(value) };
    &raw const local.cell
}

pub fn cell_field_raw_return_escape(value: u32) -> *const Cell<u32> {
    let local = CellField { prefix: 19, cell: Cell::new(value) };
    return &raw const local.cell;
}

pub fn touch_refcell(c: &RefCell<u32>) {
    c.replace(7);
}

pub fn read_refcell(c: &RefCell<u32>) -> u32 {
    // A scalar result without introducing a borrowed Ref's drop into the caller.
    c.replace(7)
}

pub fn refcell_local(c: RefCell<u32>) -> u32 {
    let local = c;
    touch_refcell(&local);
    read_refcell(&local)
}

pub struct Nested {
    pub cell: Cell<u32>,
    pub tag: u32,
}

pub fn touch_nested(c: &Nested) {
    c.cell.set(7);
}

pub fn read_nested(c: &Nested) -> u32 {
    c.cell.get()
}

pub fn nested_local(c: Nested) -> u32 {
    let local = c;
    touch_nested(&local);
    read_nested(&local)
}

pub fn forwarded_cell(c: &Cell<u32>) -> u32 {
    touch_cell(c);
    read_cell(c)
}

pub fn write_scalar(x: &mut u32) {
    *x = 7;
}

pub fn read_scalar(x: &u32) -> u32 {
    *x
}

pub fn freeze_promoted(mut x: u32) -> u32 {
    write_scalar(&mut x);
    read_scalar(&x)
}

pub fn freeze_neighbor(x: u32) -> u32 {
    read_scalar(&x)
}

pub struct Frozen {
    pub a: u32,
    pub b: u32,
}

pub fn read_frozen(x: &Frozen) -> u32 {
    x.a
}

pub fn freeze_aggregate(x: Frozen) -> u32 {
    read_frozen(&x)
}

pub fn freeze_temporary(x: Frozen) -> u32 {
    read_frozen(&{ x })
}

pub fn freeze_field(x: Frozen) -> u32 {
    read_scalar(&x.b)
}

pub struct DropCell(pub Cell<u32>);

impl Drop for DropCell {
    fn drop(&mut self) {
        self.0.set(13);
    }
}

pub fn touch_drop(c: &DropCell) {
    c.0.set(7);
}

pub fn drop_home(c: DropCell) {
    touch_drop(&c);
}

pub struct DropFrozen(pub u32);

impl Drop for DropFrozen {
    fn drop(&mut self) {}
}

pub fn read_drop_frozen(c: &DropFrozen) -> u32 {
    c.0
}

// This originally had no promoted home. Whole-local storage now carries both
// the shared call and the destructor; the run-make test checks their identity.
pub fn unsupported_drop_home(c: DropFrozen) -> u32 {
    read_drop_frozen(&c)
}

pub struct DropFloat(pub f32);

impl Drop for DropFloat {
    fn drop(&mut self) {}
}

pub fn read_drop_float(c: &DropFloat) -> f32 {
    c.0
}

// Aggregate float storage still has no qualified whole-local promotion. Keep
// the destructor-bearing shape as a real refusal, not an erased drop.
pub fn unrepresented_drop_home(c: DropFloat) -> f32 {
    read_drop_float(&c)
}

// There is no existing named home for these fresh temporary copies. Until the
// producer models their real temporary homes, they must be named refusals.
pub fn nonfreeze_temporary(c: Cell<u32>) -> u32 {
    read_cell(&{ c })
}

pub fn nonfreeze_refcell_temporary(c: RefCell<u32>) -> u32 {
    read_refcell(&{ c })
}

pub fn nonfreeze_nested_temporary(c: Nested) -> u32 {
    read_nested(&{ c })
}

pub fn touch_float(c: &Cell<f32>) {
    c.set(7.0);
}

// The existing whole-lifetime promotion gate has scalar integer leaves. A
// representable value snapshot with float leaves is not permission to copy Cell.
pub fn nonfreeze_unpromotable(c: Cell<f32>) {
    touch_float(&c);
}

pub fn unknown_snapshot<T>(value: T) {
    let _reference = &value;
}
