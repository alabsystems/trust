// Andrew Yates — source of tests/fixtures/argument_premise_*_mir.json (tests/
// argument_premise_row_identity_realmir.rs). Lines pinned by the test: `mixed` 9 and
// 12, `clip_textured_quad_x` 42-44, `guarded_index` 53 (keep them where they are).
//
// D96: `a` and `n` are `&mut` arguments the compiler installs NOALIAS_MUT_ARGS for;
// `x` is a by-value argument no premise covers.

pub fn mixed(a: &mut u32, n: &mut usize, x: u8) -> u8 {
    let y = (x & 0x7f) + 1;
    if *n < 8 {
        *a = 1;
        *n += 1;
    }
    y
}

// aterm-gpu renderer.rs:19099 at aterm 4df067b345, verbatim: NOALIAS_MUT_ARGS over
// `rect` and `uv`. The bounds rows of `uv[2] *= kept`, `rect[0] = x0` and
// `rect[2] = x1 - x0` carry the definitions of `old_x` and `old_w` across the stores
// through `uv` only under the premise, and need neither.
pub fn clip_textured_quad_x(
    rect: &mut [f32; 4],
    uv: &mut [f32; 4],
    clip_x: Option<(usize, usize)>,
) -> bool {
    let Some((clip_x0, clip_x1)) = clip_x else {
        return rect[2] > 0.0;
    };
    let old_x = rect[0];
    let old_w = rect[2];
    if old_w <= 0.0 {
        return false;
    }
    let x0 = old_x.max(clip_x0 as f32);
    let x1 = (old_x + old_w).min(clip_x1 as f32);
    if x1 <= x0 {
        return false;
    }
    let left = (x0 - old_x) / old_w;
    let kept = (x1 - x0) / old_w;
    uv[0] += uv[2] * left;
    uv[2] *= kept;
    rect[0] = x0;
    rect[2] = x1 - x0;
    true
}

// The ordinary-Rust sweep's m07: the `*n += 1` overflow needs the guard only the
// premise keeps across the store through `a`.
pub fn guarded_index(a: &mut [u32; 8], n: &mut usize) {
    if *n < 8 {
        a[0] = 1;
        *n += 1;
    }
}
