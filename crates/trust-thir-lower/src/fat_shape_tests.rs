use std::cell::Cell;

use super::{FatShape, agg_or_opaque, is_pure_value_shape};

fn shape(tag: usize) -> FatShape {
    match tag {
        0 => FatShape::Scalar,
        1 => FatShape::Thin,
        2 => FatShape::Fat,
        3 => FatShape::Opaque,
        4 => FatShape::Agg(vec![]),
        5 => FatShape::Agg(vec![FatShape::Scalar, FatShape::Thin]),
        // The helper must preserve this shape as given. Recursive callers
        // collapse their own Opaque children before yielding to their parent.
        6 => FatShape::Agg(vec![FatShape::Opaque]),
        _ => unreachable!(),
    }
}

#[test]
fn empty_order_and_nested_shape_are_preserved() {
    assert_eq!(agg_or_opaque([]), FatShape::Agg(vec![]));
    assert_eq!(
        agg_or_opaque([shape(1), shape(5), shape(0)]),
        FatShape::Agg(vec![FatShape::Thin, shape(5), FatShape::Scalar]),
    );
    assert_eq!(agg_or_opaque([shape(6)]), FatShape::Agg(vec![shape(6)]));
    assert!(is_pure_value_shape(&agg_or_opaque([shape(0), shape(4)])));
    assert!(!is_pure_value_shape(&agg_or_opaque([shape(0), shape(2)])));
}

#[test]
fn stops_after_the_first_opaque_at_every_position() {
    for first_opaque in 0..16 {
        let consumed = Cell::new(0);
        let result = agg_or_opaque((0..16).map(|index| {
            consumed.set(consumed.get() + 1);
            if index == first_opaque { FatShape::Opaque } else { FatShape::Scalar }
        }));
        assert_eq!(result, FatShape::Opaque);
        assert_eq!(consumed.get(), first_opaque + 1, "first Opaque at {first_opaque}");
    }
}

#[test]
fn never_evaluates_a_tail_after_opaque() {
    let children = std::iter::once(FatShape::Opaque)
        .chain(std::iter::once_with(|| panic!("irrelevant child was evaluated")));
    assert_eq!(agg_or_opaque(children), FatShape::Opaque);
}

#[test]
fn nonopaque_children_are_evaluated_once_and_in_order() {
    let next = Cell::new(0);
    let result = agg_or_opaque((0..32).map(|index| {
        assert_eq!(next.get(), index);
        next.set(index + 1);
        shape(index % 3)
    }));
    assert_eq!(next.get(), 32);
    assert_eq!(result, FatShape::Agg((0..32).map(|index| shape(index % 3)).collect()));
}

#[test]
fn exhaustive_bounded_output_equivalence() {
    let mut cases = 0;
    for len in 0..=5 {
        for mut encoded in 0..7usize.pow(len as u32) {
            let mut tags = Vec::new();
            for _ in 0..len {
                tags.push(encoded % 7);
                encoded /= 7;
            }
            let expected = if tags.contains(&3) {
                FatShape::Opaque
            } else {
                FatShape::Agg(tags.iter().map(|&tag| shape(tag)).collect())
            };
            assert_eq!(agg_or_opaque(tags.iter().map(|&tag| shape(tag))), expected, "{tags:?}");
            cases += 1;
        }
    }
    assert_eq!(cases, 19608);
}

#[test]
fn bounded_child_evaluation_counts() {
    for count in [1, 8, 64, 1024] {
        for first_opaque in [Some(0), Some(count / 2), Some(count - 1), None] {
            let consumed = Cell::new(0);
            let result = agg_or_opaque((0..count).map(|index| {
                consumed.set(consumed.get() + 1);
                if first_opaque == Some(index) { FatShape::Opaque } else { FatShape::Scalar }
            }));
            assert_eq!(matches!(result, FatShape::Opaque), first_opaque.is_some());
            eprintln!(
                "FAT_SHAPE_WORK count={count} first_opaque={first_opaque:?} consumed={}",
                consumed.get()
            );
        }
    }
}
