// ki1015-subslice-len: a sub-slice's length under its parent's guard (TRUST-KI-1015-1).
// Every SAFE function's Sub must not be FAILED (proved, or at worst unknown); every UNSAFE
// one's must stay FAILED or at least not PROVED. a15 is copied verbatim from
// ~/salvage-2026-09-28/records/regr-codec-inflate911-review1/adv/src/lib.rs.

// a15 SAFE (the reported shape): guard on len, Sub on (len - 2) - 4.
pub fn a15_subslice_ok(input: &[u8]) -> Option<(usize, u8, u8)> {
    if input.len() < 6 {
        return None;
    }
    let a = input[0];
    let b = input[1];
    let rest = &input[2..];
    Some((rest.len() - 4, a, b))
}

// a14 UNSAFE: (len - 2) - 5 at len 6 underflows.
pub fn a14_subslice(input: &[u8]) -> Option<(usize, u8, u8)> {
    if input.len() < 6 {
        return None;
    }
    let a = input[0];
    let b = input[1];
    let rest = &input[2..];
    Some((rest.len() - 5, a, b))
}

// b1 SAFE: RangeFrom without the byte reads.
pub fn b1_from_ok(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    Some(rest.len() - 4)
}

// b1x UNSAFE: guard off by one (len >= 5).
pub fn b1x_from_offby1(input: &[u8]) -> Option<usize> {
    if input.len() < 5 {
        return None;
    }
    let rest = &input[2..];
    Some(rest.len() - 4)
}

// b1y UNSAFE: guard removed (the slice itself only gives len >= 2).
pub fn b1y_from_noguard(input: &[u8]) -> usize {
    let rest = &input[2..];
    rest.len() - 4
}

// b1z UNSAFE: the sub-slice is of the wrong offset (3.. instead of 2..).
pub fn b1z_from_wrong_offset(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[3..];
    Some(rest.len() - 4)
}

// b2 SAFE: Range a..b with constant bounds: rest.len() == 3, under len >= 6.
pub fn b2_range_ok(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..5];
    Some(rest.len() - 3)
}

// b2x UNSAFE: Range of length 3, Sub of 4.
pub fn b2x_range_wrong(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..5];
    Some(rest.len() - 4)
}

// b3 SAFE: Range a..b with a symbolic end: rest.len() == len - 1 - 2.
pub fn b3_range_sym_ok(input: &[u8]) -> Option<usize> {
    if input.len() < 7 {
        return None;
    }
    let rest = &input[2..input.len() - 1];
    Some(rest.len() - 4)
}

// b3x UNSAFE: same, guard off by one (len >= 6 gives rest.len() == 3).
pub fn b3x_range_sym_offby1(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..input.len() - 1];
    Some(rest.len() - 4)
}

// b4 SAFE: RangeTo ..b: rest.len() == 5.
pub fn b4_to_ok(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[..5];
    Some(rest.len() - 5)
}

// b4x UNSAFE: RangeTo ..5, Sub of 6.
pub fn b4x_to_wrong(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[..5];
    Some(rest.len() - 6)
}

// b5 SAFE: split_at(2): tail.len() == len - 2.
pub fn b5_split_at_ok(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let (_head, tail) = input.split_at(2);
    Some(tail.len() - 4)
}

// b5x UNSAFE: split_at(2), Sub of 5.
pub fn b5x_split_at_wrong(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let (_head, tail) = input.split_at(2);
    Some(tail.len() - 5)
}

// b6 SAFE: a sub-slice of a sub-slice: (len - 2) - 1 - 3 under len >= 6.
pub fn b6_nested_ok(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    let rest2 = &rest[1..];
    Some(rest2.len() - 3)
}

// b6x UNSAFE: a sub-slice of a sub-slice, Sub of 4.
pub fn b6x_nested_wrong(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    let rest2 = &rest[1..];
    Some(rest2.len() - 4)
}

// b7 SAFE: chunks_exact(2): every chunk has length 2.
pub fn b7_chunks_exact_ok(input: &[u8]) -> usize {
    let mut n = 0usize;
    for c in input.chunks_exact(2) {
        n = n.wrapping_add(c.len() - 2);
    }
    n
}

// b7x UNSAFE: chunks(2): the last chunk may have length 1.
pub fn b7x_chunks_wrong(input: &[u8]) -> usize {
    let mut n = 0usize;
    for c in input.chunks(2) {
        n = n.wrapping_add(c.len() - 2);
    }
    n
}

// b8 SAFE: the guard is on the sub-slice itself (control: no parent relation needed).
pub fn b8_guard_on_rest(input: &[u8]) -> Option<usize> {
    if input.len() < 2 {
        return None;
    }
    let rest = &input[2..];
    if rest.len() < 4 {
        return None;
    }
    Some(rest.len() - 4)
}

// b9 UNSAFE: the sub-slice is of ANOTHER slice than the one guarded.
pub fn b9_other_parent(input: &[u8], other: &[u8]) -> Option<usize> {
    if input.len() < 6 || other.len() < 2 {
        return None;
    }
    let rest = &other[2..];
    Some(rest.len() - 4)
}

// b10 SAFE: a symbolic start: rest.len() == len - k under len >= k + 4.
pub fn b10_from_sym_ok(input: &[u8], k: usize) -> Option<usize> {
    if k > 100 || input.len() < k + 4 {
        return None;
    }
    let rest = &input[k..];
    Some(rest.len() - 4)
}

// b10x UNSAFE: symbolic start, guard one short.
pub fn b10x_from_sym_offby1(input: &[u8], k: usize) -> Option<usize> {
    if k > 100 || input.len() < k + 3 {
        return None;
    }
    let rest = &input[k..];
    Some(rest.len() - 4)
}

// b7y SAFE: chunks(2): every chunk is non-empty.
pub fn b7y_chunks_nonempty_ok(input: &[u8]) -> usize {
    let mut n = 0usize;
    for c in input.chunks(2) {
        n = n.wrapping_add(c.len() - 1);
    }
    n
}

// b11 SAFE: a mutable sub-slice (`IndexMut::index_mut`).
pub fn b11_index_mut_ok(input: &mut [u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &mut input[2..];
    rest[0] = 1;
    Some(rest.len() - 4)
}

// b11x UNSAFE: a mutable sub-slice, Sub of 5.
pub fn b11x_index_mut_wrong(input: &mut [u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &mut input[2..];
    rest[0] = 1;
    Some(rest.len() - 5)
}

// b12 SAFE: the slice re-sliced in place (`s = &s[2..]`).
pub fn b12_reslice_ok(input: &[u8]) -> Option<usize> {
    let mut s = input;
    if s.len() < 6 {
        return None;
    }
    s = &s[2..];
    Some(s.len() - 4)
}

// b12x UNSAFE: re-sliced in place twice under a guard that covers one cut only.
pub fn b12x_reslice_twice_wrong(input: &[u8]) -> Option<usize> {
    let mut s = input;
    if s.len() < 6 {
        return None;
    }
    s = &s[2..];
    s = &s[2..];
    Some(s.len() - 4)
}

// b14 SAFE: an array receiver: (8 - 2) - 6.
pub fn b14_array_ok(arr: &[u8; 8]) -> usize {
    let rest = &arr[2..];
    rest.len() - 6
}

// b14x UNSAFE: an array receiver: (8 - 2) - 7.
pub fn b14x_array_wrong(arr: &[u8; 8]) -> usize {
    let rest = &arr[2..];
    rest.len() - 7
}

// b15 SAFE: a `str` receiver (the index may panic on a char boundary; when it returns,
// the length is len - 2).
pub fn b15_str_ok(s: &str) -> Option<usize> {
    if s.len() < 6 {
        return None;
    }
    let rest = &s[2..];
    Some(rest.len() - 4)
}

// b17 UNSAFE: a loop that cuts two at a time can leave an empty slice.
pub fn b17_loop_cut_wrong(input: &[u8]) -> usize {
    let mut s = input;
    while s.len() >= 2 {
        s = &s[2..];
    }
    s.len() - 1
}

// b18 SAFE: the cut inside the loop, under the loop guard.
pub fn b18_loop_cut_ok(input: &[u8]) -> usize {
    let mut s = input;
    let mut acc = 0usize;
    while s.len() >= 6 {
        s = &s[2..];
        acc = acc.wrapping_add(s.len() - 4);
    }
    acc
}

// b19 UNSAFE: a sub-slice of a sub-slice whose second cut is too deep.
pub fn b19_nested_deep_wrong(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    let rest2 = &rest[3..];
    Some(rest2.len() - 2)
}

// b20 SAFE: Range with a symbolic start and end: rest.len() == e - s.
pub fn b20_range_two_sym_ok(input: &[u8], s: usize, e: usize) -> Option<usize> {
    if s > e || e > input.len() || e - s < 4 {
        return None;
    }
    let rest = &input[s..e];
    Some(rest.len() - 4)
}

// b20x UNSAFE: same, guard one short.
pub fn b20x_range_two_sym_offby1(input: &[u8], s: usize, e: usize) -> Option<usize> {
    if s > e || e > input.len() || e - s < 3 {
        return None;
    }
    let rest = &input[s..e];
    Some(rest.len() - 4)
}

// b11b SAFE: a mutable sub-slice with no element store before the Sub.
pub fn b11b_index_mut_no_store_ok(input: &mut [u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &mut input[2..];
    Some(rest.len() - 4)
}

// b21 SAFE (no sub-slice before the Sub): the loop guard's own length, read in the body.
pub fn b21_loop_guard_len_ok(input: &[u8]) -> usize {
    let mut s = input;
    let mut acc = 0usize;
    while s.len() >= 6 {
        acc = acc.wrapping_add(s.len() - 4);
        s = &s[2..];
    }
    acc
}

// ---- 2026-10-15 (the review's SHOULD-FIX: the gates of the fact, reached by programs) ----

// The OpaqueScalar identity gate (`call_facts::body_mentions_opaque_scalar`): an associated
// constant of a generic parameter is a `ConstValue::OpaqueScalar` keyed by its item.
pub trait Cut {
    const K: usize;
    const J: usize;
}

// g1 SAFE, but no fact: the gate refuses every body that mentions an OpaqueScalar, and every
// other gate passes (`rest.len() == len - K >= 8 - 4`).
pub fn g1_opaque_start_ok<T: Cut>(input: &[u8]) -> usize {
    if T::K > 4 || input.len() < 8 {
        return 0;
    }
    let rest = &input[T::K..];
    rest.len() - 4
}

// g1x UNSAFE: the same constant, guard one wide (`K = 5`, `len = 8`: `3 - 4`).
pub fn g1x_opaque_start_offby1<T: Cut>(input: &[u8]) -> usize {
    if T::K > 5 || input.len() < 8 {
        return 0;
    }
    let rest = &input[T::K..];
    rest.len() - 4
}

// g1y UNSAFE: the guard bounds ANOTHER constant (`J = 0`, `K = 5`, `len = 8`: `3 - 4`).
pub fn g1y_opaque_other_const<T: Cut>(input: &[u8]) -> usize {
    if T::J > 4 || input.len() < 8 {
        return 0;
    }
    let rest = &input[T::K..];
    rest.len() - 4
}

// g3x UNSAFE: a runtime opaque start (`ptr as usize`, a positional OpaqueScalar) re-read in a
// loop; `rest` is the previous iteration's cut, so `rest.len() - d` is `k - k_prev`, which
// underflows for `k = 0` after `k_prev = 4`.
pub fn g3x_opaque_site_loop_wrong(input: &[u8], ps: &[*const u8]) -> usize {
    if input.len() < 8 {
        return 0;
    }
    let mut rest = input;
    let mut acc = 0usize;
    let mut i = 0;
    while i < ps.len() {
        let k = ps[i] as usize;
        if k > 4 {
            return acc;
        }
        let d = input.len() - k;
        acc = acc.wrapping_add(rest.len() - d);
        rest = &input[k..];
        i += 1;
    }
    acc
}
