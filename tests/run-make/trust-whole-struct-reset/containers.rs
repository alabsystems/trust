//! Whole replacement after a scalar read must use the same complete struct type.

use std::collections::HashMap;

#[derive(Default)]
pub struct VecCache {
    pub values: Vec<u32>,
    pub epoch: u64,
}

#[derive(Default)]
pub struct MapCache {
    pub values: HashMap<u32, u32>,
    pub epoch: u64,
}

pub fn vec_reset(cache: &mut VecCache) -> u64 {
    let epoch = cache.epoch;
    *cache = VecCache::default();
    cache.epoch = epoch + 1;
    cache.epoch
}

pub fn vec_reset_only(cache: &mut VecCache) {
    *cache = VecCache::default();
}

pub fn vec_write_after(cache: &mut VecCache) {
    *cache = VecCache::default();
    cache.epoch = 1;
}

pub fn vec_field_only(cache: &mut VecCache) {
    cache.epoch += 1;
}

pub fn map_reset(cache: &mut MapCache) -> u64 {
    let epoch = cache.epoch;
    *cache = MapCache::default();
    cache.epoch = epoch + 1;
    cache.epoch
}

pub fn map_reset_only(cache: &mut MapCache) {
    *cache = MapCache::default();
}
