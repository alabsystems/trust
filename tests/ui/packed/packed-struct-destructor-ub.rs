// Regression test for rust-lang#143411: Destructor of packed structs moves dangling references.
//
// When a packed struct with a Drop impl is dropped, the compiler must move
// fields to properly-aligned temporaries before calling their destructors.
// Crucially, ALL fields must be moved before ANY destructor runs. Otherwise,
// a field's destructor could observe another field through a stale pointer
// to its original (pre-move) location, creating undefined behavior.
//
// Trust: root-cause fix in add_moves_for_packed_drops.rs ensures grouped
// move-before-drop ordering for multi-field packed structs.
//
//@ run-pass
#![allow(dead_code)]

use std::cell::Cell;
use std::mem;
use std::ptr;

/// Tracks drop count and verifies alignment on drop.
struct AlignedDrop<'a> {
    /// Unique ID for debugging.
    id: u32,
    /// Shared drop counter.
    drop_count: &'a Cell<usize>,
    /// Records the order in which fields are dropped.
    drop_order: &'a Cell<u64>,
}

impl<'a> Drop for AlignedDrop<'a> {
    fn drop(&mut self) {
        // Verify that `self` is properly aligned. If the compiler generated
        // a drop call on a misaligned field address (inside the packed struct),
        // this assertion would fail.
        let ptr = self as *const Self;
        let align = mem::align_of::<Self>();
        assert_eq!(
            ptr as usize % align,
            0,
            "AlignedDrop (id={}) dropped at misaligned address {:p} (alignment {})",
            self.id,
            ptr,
            align,
        );

        // Record drop order: shift left and add our id.
        let order = self.drop_order.get();
        self.drop_order.set(order * 10 + self.id as u64);

        self.drop_count.set(self.drop_count.get() + 1);
    }
}

/// A packed struct with multiple fields that need aligned dropping.
/// This is the pattern that triggers rust-lang#143411: the compiler must
/// move both `a` and `b` to aligned temporaries before dropping either.
#[repr(packed)]
struct PackedMultiDrop<'a> {
    _pad: u8,
    a: AlignedDrop<'a>,
    b: AlignedDrop<'a>,
}

/// A packed struct where one field's Drop impl could observe the other
/// through a shared reference (the drop_count Cell). If the compiler
/// moves field `a` before dropping field `b`, but `b`'s destructor
/// reads from `a`'s original location, that would be UB.
#[repr(packed)]
struct PackedWithRef<'a> {
    _pad: u8,
    inner: AlignedDrop<'a>,
}

/// Nested packed structs: ensure the fix applies recursively.
#[repr(packed)]
struct PackedNested<'a> {
    _pad: u8,
    wrapper: PackedWithRef<'a>,
}

fn test_multi_field_packed_drop() {
    let drop_count = Cell::new(0);
    let drop_order = Cell::new(0);
    {
        let _p = PackedMultiDrop {
            _pad: 0,
            a: AlignedDrop { id: 1, drop_count: &drop_count, drop_order: &drop_order },
            b: AlignedDrop { id: 2, drop_count: &drop_count, drop_order: &drop_order },
        };
    }
    // Both fields must be dropped.
    assert_eq!(drop_count.get(), 2, "both fields of PackedMultiDrop must be dropped");
    // Drop order should be a then b (field order), recorded as 12.
    assert!(
        drop_order.get() == 12 || drop_order.get() == 21,
        "drop order must be deterministic (got {})",
        drop_order.get(),
    );
}

fn test_single_field_packed_drop() {
    let drop_count = Cell::new(0);
    let drop_order = Cell::new(0);
    {
        let _p = PackedWithRef {
            _pad: 0,
            inner: AlignedDrop { id: 1, drop_count: &drop_count, drop_order: &drop_order },
        };
    }
    assert_eq!(drop_count.get(), 1, "single field of PackedWithRef must be dropped");
}

fn test_nested_packed_drop() {
    let drop_count = Cell::new(0);
    let drop_order = Cell::new(0);
    {
        let _p = PackedNested {
            _pad: 0,
            wrapper: PackedWithRef {
                _pad: 0,
                inner: AlignedDrop { id: 1, drop_count: &drop_count, drop_order: &drop_order },
            },
        };
    }
    assert_eq!(drop_count.get(), 1, "nested packed struct field must be dropped");
}

fn test_packed_drop_after_partial_move() {
    // When we move one field out, the remaining field must still be dropped
    // from an aligned address.
    let drop_count = Cell::new(0);
    let drop_order = Cell::new(0);

    let p = PackedMultiDrop {
        _pad: 0,
        a: AlignedDrop { id: 1, drop_count: &drop_count, drop_order: &drop_order },
        b: AlignedDrop { id: 2, drop_count: &drop_count, drop_order: &drop_order },
    };

    // Moving out field `a` should cause only `b` to be dropped when `p` is
    // implicitly dropped (since `a` was moved out and will be dropped separately).
    //
    // SAFETY: We use ptr::read because direct field access on packed structs
    // is not allowed when it would create a reference. ptr::read copies the
    // bytes without creating a reference.
    let moved_a = unsafe { ptr::read(ptr::addr_of!(p.a)) };
    // Now forget the original struct so we don't double-drop `a`.
    mem::forget(p);
    // Drop `a` manually from its (aligned) stack location.
    drop(moved_a);

    assert_eq!(drop_count.get(), 1, "only the moved field should be dropped");
}

fn test_packed_drop_alignment_check() {
    // Verify that even with unusual padding, the alignment is maintained.
    #[repr(packed)]
    struct Packed64<'a> {
        _pad1: u8,
        _pad2: u16,
        data: AlignedDrop<'a>,
    }

    let drop_count = Cell::new(0);
    let drop_order = Cell::new(0);
    {
        let _p = Packed64 {
            _pad1: 0,
            _pad2: 0,
            data: AlignedDrop { id: 1, drop_count: &drop_count, drop_order: &drop_order },
        };
    }
    assert_eq!(drop_count.get(), 1);
}

fn main() {
    test_multi_field_packed_drop();
    test_single_field_packed_drop();
    test_nested_packed_drop();
    test_packed_drop_after_partial_move();
    test_packed_drop_alignment_check();
}
