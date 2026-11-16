// TRUST-KI-1015-1, the `as_chunks` remainder shape (aterm-digest Sha256::update,
// sha256.rs:127:16 at aterm 848d791bd). `s*` are correct programs (no input panics);
// `w*` are their wrong twins, each of which really panics on the input named beside it.

pub fn s1_digest_tail(buf: &mut [u8; 64], data: &[u8]) -> usize {
    let (blocks, rest) = data.as_chunks::<64>();
    let mut acc = 0u8;
    for block in blocks {
        acc ^= block[0];
    }
    buf[..rest.len()].copy_from_slice(rest);
    buf[0] ^= acc;
    rest.len()
}

pub fn s2_no_loop(buf: &mut [u8; 64], data: &[u8]) {
    let (_blocks, rest) = data.as_chunks::<64>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn s3_rchunks(buf: &mut [u8; 16], data: &[u8]) {
    let (rest, _chunks) = data.as_rchunks::<16>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn s4_chunks_mut(buf: &mut [u8; 8], data: &mut [u8]) {
    let (_chunks, rest) = data.as_chunks_mut::<8>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn s5_rchunks_mut(buf: &mut [u8; 8], data: &mut [u8]) {
    let (rest, _chunks) = data.as_rchunks_mut::<8>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn s6_room_left(data: &[u8]) -> usize {
    let (_blocks, rest) = data.as_chunks::<64>();
    63 - rest.len()
}

pub fn s7_whole_part(data: &[u8]) -> usize {
    let (_blocks, rest) = data.as_chunks::<64>();
    data.len() - rest.len()
}

pub fn s8_block_count(data: &[u8]) -> u8 {
    let (blocks, _rest) = data.as_chunks::<4>();
    if data.len() >= 8 { blocks[1][3] } else { 0 }
}

pub fn s9_rblock_count(data: &[u8]) -> u8 {
    let (_rest, chunks) = data.as_rchunks::<4>();
    if data.len() >= 8 { chunks[1][0] } else { 0 }
}

pub fn s10_exact_rest(data: &[u8]) -> usize {
    if data.len() != 70 {
        return 0;
    }
    let (_blocks, rest) = data.as_chunks::<64>();
    6 - rest.len()
}

pub fn s11_words(buf: &mut [u32; 3], data: &[u32]) {
    let (_quads, rest) = data.as_chunks::<4>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn s12_chunks_exact_rem(buf: &mut [u8; 64], data: &[u8]) {
    let rest = data.chunks_exact(64).remainder();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn w1_buf_too_small(buf: &mut [u8; 32], data: &[u8]) {
    // panics: data.len() == 40
    let (_blocks, rest) = data.as_chunks::<64>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn w2_room_off_by_one(data: &[u8]) -> usize {
    // panics: data.len() == 63
    let (_blocks, rest) = data.as_chunks::<64>();
    62 - rest.len()
}

pub fn w3_rest_nonempty(data: &[u8]) -> usize {
    // panics: data.len() == 64
    let (_blocks, rest) = data.as_chunks::<64>();
    rest.len() - 1
}

pub fn w4_rchunks_buf_too_small(buf: &mut [u8; 8], data: &[u8]) {
    // panics: data.len() == 12
    let (rest, _chunks) = data.as_rchunks::<16>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn w5_block_count_off_by_one(data: &[u8]) -> u8 {
    // panics: data.len() == 7
    let (blocks, _rest) = data.as_chunks::<4>();
    if data.len() >= 7 { blocks[1][3] } else { 0 }
}

pub fn w6_chunks_mut_buf_too_small(buf: &mut [u8; 4], data: &mut [u8]) {
    // panics: data.len() == 5
    let (_chunks, rest) = data.as_chunks_mut::<8>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn w7_rblock_count_off_by_one(data: &[u8]) -> u8 {
    // panics: data.len() == 7
    let (_rest, chunks) = data.as_rchunks::<4>();
    if data.len() >= 7 { chunks[1][0] } else { 0 }
}

pub fn w8_exact_rest_off_by_one(data: &[u8]) -> usize {
    // panics: data.len() == 70
    if data.len() != 70 {
        return 0;
    }
    let (_blocks, rest) = data.as_chunks::<64>();
    5 - rest.len()
}

pub fn w9_rest_is_not_the_head(data: &[u8]) -> usize {
    // panics: data.len() == 64 (the remainder of `as_rchunks` is the HEAD, and empty here)
    let (rest, _chunks) = data.as_rchunks::<64>();
    rest.len() - 1
}

pub fn w10_words_buf_too_small(buf: &mut [u32; 2], data: &[u32]) {
    // panics: data.len() == 3
    let (_quads, rest) = data.as_chunks::<4>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn w11_rchunks_mut_buf_too_small(buf: &mut [u8; 4], data: &mut [u8]) {
    // panics: data.len() == 7
    let (rest, _chunks) = data.as_rchunks_mut::<8>();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn w12_chunks_exact_rem_buf_too_small(buf: &mut [u8; 32], data: &[u8]) {
    // panics: data.len() == 40
    let rest = data.chunks_exact(64).remainder();
    buf[..rest.len()].copy_from_slice(rest);
}

pub fn s13_exact_count(data: &[u8]) -> usize {
    let (blocks, _rest) = data.as_chunks::<64>();
    if data.len() == 130 { blocks.len() - 2 } else { 0 }
}

pub fn w13_rest_of_a_whole_block(data: &[u8]) -> usize {
    // panics: data.len() == 64 (the head remainder of `as_rchunks` is empty there; a
    // fact that swapped the halves would call it 64 / 64 == 1 and prove this)
    let (rest, _chunks) = data.as_rchunks::<64>();
    if data.len() == 64 { rest.len() - 1 } else { 0 }
}

pub fn w14_count_off_by_one(data: &[u8]) -> usize {
    // panics: data.len() == 127
    let (blocks, _rest) = data.as_chunks::<64>();
    if data.len() == 127 { blocks.len() - 2 } else { 0 }
}
