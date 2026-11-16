//! Ordered-registry equivalence and work counts, independent of rustc queries.
//! Native producer tests separately cover layouts, refusals and taint propagation.

use std::cell::Cell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use trust_types::fx::FxIndexMap;

use super::{declared_struct_field_offset, pending_struct_row};

thread_local! {
    static PENDING_ROW_COMPARISONS: Cell<u64> = const { Cell::new(0) };
}

pub(super) fn record_pending_row_comparison() {
    PENDING_ROW_COMPARISONS.with(|count| count.set(count.get() + 1));
}

fn pending_row(id: u32) -> trust_ir::StructDef {
    trust_ir::StructDef {
        id: trust_ir::StructId::new(id),
        name: format!("row_{id}"),
        fields: vec![trust_ir::FieldDef {
            name: "field".into(),
            ty: if id == 0 {
                trust_ir::Ty::U64
            } else {
                trust_ir::Ty::Struct(trust_ir::StructId::new(id - 1))
            },
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: trust_ir::StructRepr::C,
        origin: None,
    }
}

#[test]
fn pending_rows_keep_exact_identity_through_append_snapshot_and_take() {
    let mut rows = Vec::new();
    for id in 0..64 {
        let mut row = pending_row(id);
        // Anonymous rows occupy the same physical table even though they have
        // no entry in the DefId/GenericArgs registration ledger.
        if id % 7 == 0 {
            row.name = format!("anonymous_{id}");
        }
        rows.push(row);
        for query in (0..=id + 1).rev() {
            let sid = trust_ir::StructId::new(query);
            let old = rows.iter().find(|row| row.id == sid);
            let new = pending_struct_row(&rows, sid);
            assert_eq!(new, old);
            if let (Some(old), Some(new)) = (old, new) {
                assert!(std::ptr::eq(old, new), "lookup must return the stored row");
            }
        }
    }
    let snapshot = rows.clone();
    let flushed = std::mem::take(&mut rows);
    assert!(pending_struct_row(&rows, trust_ir::StructId::new(0)).is_none());
    for table in [&snapshot, &flushed] {
        for id in (0..64).rev() {
            assert_eq!(
                pending_struct_row(table, trust_ir::StructId::new(id)),
                table.get(id as usize)
            );
        }
        assert!(pending_struct_row(table, trust_ir::StructId::new(u32::MAX)).is_none());
    }
}

#[test]
fn pending_rows_refuse_misnumbered_slots_without_changing_arbitrary_tables() {
    let mut misplaced = pending_row(0);
    misplaced.fields[0].offset = Some(24);
    let rows = vec![pending_row(9), misplaced, pending_row(2)];
    assert!(pending_struct_row(&rows, trust_ir::StructId::new(0)).is_none());
    assert!(pending_struct_row(&rows, trust_ir::StructId::new(1)).is_none());
    assert_eq!(pending_struct_row(&rows, trust_ir::StructId::new(2)), rows.get(2));
    // This public helper accepts arbitrary declaration slices and stays by-id.
    assert_eq!(declared_struct_field_offset(&rows, trust_ir::StructId::new(0), 0), Some(24));
}

#[test]
fn pending_rows_avoid_prefix_scans_on_many_nested_rows() {
    use std::hint::black_box;
    use std::time::Instant;

    for count in [32_u32, 128, 512, 2048] {
        let rows: Vec<_> = (0..count).map(pending_row).collect();
        let rounds = 8_u64;
        let mut linear_comparisons = 0_u64;
        let old_start = Instant::now();
        for _ in 0..rounds {
            for id in (0..count).rev() {
                let sid = black_box(trust_ir::StructId::new(id));
                let row = rows.iter().find(|row| {
                    linear_comparisons += 1;
                    row.id == sid
                });
                assert_eq!(black_box(row).map(|row| row.id), Some(sid));
            }
        }
        let old_elapsed = old_start.elapsed();
        PENDING_ROW_COMPARISONS.with(|value| value.set(0));
        let new_start = Instant::now();
        for _ in 0..rounds {
            for id in (0..count).rev() {
                let sid = black_box(trust_ir::StructId::new(id));
                let row = pending_struct_row(&rows, sid);
                assert_eq!(black_box(row).map(|row| row.id), Some(sid));
            }
        }
        let new_elapsed = new_start.elapsed();
        let indexed_comparisons = PENDING_ROW_COMPARISONS.with(Cell::get);
        assert_eq!(linear_comparisons, rounds * u64::from(count) * u64::from(count + 1) / 2);
        assert_eq!(indexed_comparisons, rounds * u64::from(count));
        eprintln!(
            "pending rows count={count} rounds={rounds} linear_comparisons={linear_comparisons} indexed_comparisons={indexed_comparisons} linear_ns={} indexed_ns={}",
            old_elapsed.as_nanos(),
            new_elapsed.as_nanos(),
        );
    }
}

fn linear_register<K: Clone + Eq>(rows: &mut Vec<(K, u32)>, key: K, next: &mut u32) -> u32 {
    if let Some((_, id)) = rows.iter().find(|(existing, _)| existing == &key) {
        return *id;
    }
    let id = *next;
    *next += 1;
    rows.push((key, id));
    id
}

fn indexed_register<K: Eq + Hash>(rows: &mut FxIndexMap<K, u32>, key: K, next: &mut u32) -> u32 {
    if let Some(id) = rows.get(&key) {
        return *id;
    }
    let id = *next;
    *next += 1;
    assert!(rows.insert(key, id).is_none());
    id
}

#[test]
fn registry_keeps_instantiations_order_and_anonymous_id_gaps() {
    // Distinct GenericArgs for one definition must not alias. IDs come from the
    // declaration table, which can contain anonymous rows absent from this index.
    let keys = [(7, 1), (7, 2), (8, 1), (7, 1), (7, 3), (8, 1)];
    let mut old = Vec::new();
    let mut new = FxIndexMap::default();
    let (mut old_next, mut new_next) = (1, 1);
    let mut ids = Vec::new();
    for (position, key) in keys.into_iter().enumerate() {
        if position == 2 {
            old_next += 1;
            new_next += 1;
        }
        let expected = linear_register(&mut old, key, &mut old_next);
        assert_eq!(indexed_register(&mut new, key, &mut new_next), expected);
        assert_eq!(new_next, old_next);
        assert_eq!(new.iter().map(|(key, id)| (*key, *id)).collect::<Vec<_>>(), old);
        ids.push(expected);
    }
    assert_eq!(ids, [1, 2, 4, 1, 5, 4]);
    assert_eq!(new.get(&(7, 0)), None);
    assert_eq!(new.keys().copied().collect::<Vec<_>>(), [(7, 1), (7, 2), (8, 1), (7, 3)]);
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CollisionKey(u32, u32);

impl Hash for CollisionKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0_u8.hash(state);
    }
}

#[test]
fn registry_checks_exact_keys_even_with_all_hashes_colliding() {
    let mut old = Vec::new();
    let mut new = FxIndexMap::default();
    let (mut old_next, mut new_next) = (0, 0);
    for i in 0..256 {
        let key = CollisionKey(i % 8, i / 8);
        assert_eq!(
            indexed_register(&mut new, key, &mut new_next),
            linear_register(&mut old, key, &mut old_next),
        );
    }
    for (key, expected) in old.iter().rev() {
        assert_eq!(new.get(key), Some(expected));
        assert_eq!(indexed_register(&mut new, *key, &mut new_next), *expected);
    }
    assert_eq!(new.get(&CollisionKey(8, 0)), None);
    assert_eq!(new_next, old_next);
    assert_eq!(new.iter().map(|(key, id)| (*key, *id)).collect::<Vec<_>>(), old);
}

#[test]
fn registry_matches_linear_lookup_and_order_over_repeated_traces() {
    for seed in 0..128_u64 {
        let mut state = seed + 1;
        let mut old = Vec::new();
        let mut new = FxIndexMap::default();
        let (mut old_next, mut new_next) = (0, 0);
        for step in 0..512 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = ((state >> 32) as u32 % 16, (state >> 8) as u32 % 32);
            if step % 7 == 0 {
                old_next += 1;
                new_next += 1;
            }
            let expected = old.iter().find(|(row, _)| row == &key).map(|(_, id)| *id);
            assert_eq!(new.get(&key).copied(), expected);
            assert_eq!(
                indexed_register(&mut new, key, &mut new_next),
                linear_register(&mut old, key, &mut old_next),
            );
        }
        assert_eq!(new_next, old_next);
        assert_eq!(new.iter().map(|(key, id)| (*key, *id)).collect::<Vec<_>>(), old);
    }
}

#[derive(Clone)]
struct CountedKey {
    value: u32,
    equalities: Rc<Cell<u64>>,
    hashes: Rc<Cell<u64>>,
}

impl PartialEq for CountedKey {
    fn eq(&self, other: &Self) -> bool {
        self.equalities.set(self.equalities.get() + 1);
        self.value == other.value
    }
}

impl Eq for CountedKey {}

impl Hash for CountedKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hashes.set(self.hashes.get() + 1);
        self.value.hash(state);
    }
}

#[test]
fn registry_prefix_replay_avoids_repeated_linear_key_comparisons() {
    // A accepted, distinct one-field structs followed by R rejected structs.
    // Each rejection discards its scratch; the next reconstructs A registrations.
    // The mapper, field/layout work and final live replay are intentionally not
    // modelled here: only the exact registry lookup/insertion operations are counted.
    for accepted in [16_u32, 64, 128] {
        let rejected = accepted / 4;
        let old_eq = Rc::new(Cell::new(0));
        let old_hash = Rc::new(Cell::new(0));
        let new_eq = Rc::new(Cell::new(0));
        let new_hash = Rc::new(Cell::new(0));
        for rejection in 0..rejected {
            let mut old = Vec::new();
            let mut new = FxIndexMap::default();
            let (mut old_next, mut new_next) = (0, 0);
            for value in (0..accepted).chain([accepted + rejection]) {
                let old_key = CountedKey {
                    value,
                    equalities: Rc::clone(&old_eq),
                    hashes: Rc::clone(&old_hash),
                };
                let new_key = CountedKey {
                    value,
                    equalities: Rc::clone(&new_eq),
                    hashes: Rc::clone(&new_hash),
                };
                assert_eq!(
                    indexed_register(&mut new, new_key, &mut new_next),
                    linear_register(&mut old, old_key, &mut old_next),
                );
            }
            assert_eq!(
                new.iter().map(|(key, id)| (key.value, *id)).collect::<Vec<_>>(),
                old.iter().map(|(key, id)| (key.value, *id)).collect::<Vec<_>>(),
            );
        }
        assert_eq!(old_eq.get(), u64::from(rejected) * u64::from(accepted * (accepted + 1) / 2));
        assert!(new_eq.get() < old_eq.get());
        // Hash work is counted too; fewer comparisons do not mean zero work.
        assert!(new_hash.get() >= u64::from(rejected * (accepted + 1)));
        eprintln!(
            "registry accepted={accepted} rejected={rejected} linear_equalities={} indexed_equalities={} indexed_hashes={}",
            old_eq.get(),
            new_eq.get(),
            new_hash.get(),
        );
    }
}
