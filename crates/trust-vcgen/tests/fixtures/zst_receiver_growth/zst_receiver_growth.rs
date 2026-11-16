// Source of the `zst_receiver_growth` fixtures (`tests/zst_receiver_growth_realmir.rs`).
// One JSON per function, named by the function, dumped by
//
//     trustc --edition 2021 --crate-type lib -Ztrust-verify=on \
//            -Ztrust-dump=mir:<dir> zst_receiver_growth.rs
//
// on stage 1 of `5184affbb97`.
#![feature(iter_collect_into)]
#![feature(extend_one)]
#![allow(dead_code)]
use std::collections::{BTreeSet, BinaryHeap, VecDeque};

// ---- a zero-sized receiver: one more element overflows a full one ----

pub fn ci_vec_zst_counted(v: &mut Vec<()>, n: usize) {
    if n < 100 {
        (0..n).map(|_| ()).collect_into(v);
    }
}

pub fn ci_vec_zst_repeat(v: &mut Vec<()>, n: usize) {
    if n < 100 {
        std::iter::repeat(()).take(n).collect_into(v);
    }
}

pub fn ci_vec_zst_bounded(v: &mut Vec<()>, s: &[u8]) {
    s.iter().map(|_| ()).collect_into(v);
}

pub fn ci_vec_zst_option(v: &mut Vec<()>) {
    Some(()).into_iter().collect_into(v);
}

pub fn ci_deque_zst_bounded(v: &mut VecDeque<()>, s: &[u8]) {
    s.iter().map(|_| ()).collect_into(v);
}

pub fn ext_vec_zst(v: &mut Vec<()>) {
    v.extend(Some(()));
}

pub fn ext_deque_zst(v: &mut VecDeque<()>) {
    v.extend(Some(()));
}

pub fn ext_heap_zst(h: &mut BinaryHeap<()>) {
    h.extend(Some(()));
}

pub fn ext_tuple_zst(v: &mut (Vec<()>, Vec<u8>)) {
    v.extend(Some(((), 1u8)));
}

pub fn reserve_vec_zst(v: &mut Vec<()>, n: usize) {
    if n < 100 {
        v.reserve(n);
    }
}

pub fn reserve_vec_zst_const(v: &mut Vec<()>) {
    v.reserve(5);
}

pub fn reserve_deque_zst(v: &mut VecDeque<()>, n: usize) {
    if n < 100 {
        v.reserve(n);
    }
}

pub fn extend_reserve_vec_zst(v: &mut Vec<()>, n: usize) {
    if n < 100 {
        <Vec<()> as Extend<()>>::extend_reserve(v, n);
    }
}

// ---- controls: a receiver whose length memory bounds ----

pub fn ci_vec_u64_counted(v: &mut Vec<u64>, n: usize) {
    if n < 100 {
        (0..n).map(|i| i as u64).collect_into(v);
    }
}

pub fn ci_deque_u64_counted(v: &mut VecDeque<u64>, n: usize) {
    if n < 100 {
        std::iter::repeat(1u64).take(n).collect_into(v);
    }
}

pub fn ci_btree_zst_bounded(s: &mut BTreeSet<()>, v: &[u8]) {
    v.iter().map(|_| ()).collect_into(s);
}

pub fn reserve_vec_u64(v: &mut Vec<u64>, n: usize) {
    if n < 100 {
        v.reserve(n);
    }
}

pub fn reserve_deque_u64(v: &mut VecDeque<u64>, n: usize) {
    if n < 100 {
        v.reserve(n);
    }
}

pub fn reserve_string(s: &mut String, n: usize) {
    if n < 100 {
        s.reserve(n);
    }
}
