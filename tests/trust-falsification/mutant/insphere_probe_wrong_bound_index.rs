#![crate_type = "lib"]
// MUTANT of proved/insphere_probe_guarded_index.rs: GUARDED ON THE WRONG BOUND.
// `i > 3` admits `i == 3` on a 3-element array — an off-by-one leaving exactly
// one out-of-bounds index reachable. Genuinely unsafe: executed under stock
// rustc with the index swept, exactly 1 of 12 values panics (i == 3). This is
// the shape a decline-to-mint change is most likely to launder, because the row
// still LOOKS guarded. MUST fail (exit 1).
//
// Shape: a3d's `a3d_kernel::insphere_i128` — a 4x4 lifted-paraboloid in-sphere
// determinant over fixed `[i64; 3]` arrays, with the twelve relative-coordinate
// `checked_sub`s INLINE in one body. The inlining is load-bearing, not style:
// the hardened panic-boundary VC for a late statement carries the accumulated
// body-definition conjunction, and that chain is what pushes the derived
// typed-CHC contract past `MAX_CONTRACT_PREDICATE_JSON_DEPTH`. Helper functions
// break the chain and the class is not reached.
//
// NOTE ON COVERAGE: the deep-contract class needs
// `-Ztrust-verify-profile=unix_hardened` (a3d's own gate runs it; the
// falsification gate does not pass it). Under the gate's default flags these
// fixtures still exercise ordinary bounds refutation, which is why they belong
// here; the hardened-profile battery is what pins the decline path itself.

fn det3(r0: [i128; 3], r1: [i128; 3], r2: [i128; 3]) -> Option<i128> {
    let m0 = r1[1].checked_mul(r2[2])?.checked_sub(r1[2].checked_mul(r2[1])?)?;
    let m1 = r1[0].checked_mul(r2[2])?.checked_sub(r1[2].checked_mul(r2[0])?)?;
    let m2 = r1[0].checked_mul(r2[1])?.checked_sub(r1[1].checked_mul(r2[0])?)?;
    let t0 = r0[0].checked_mul(m0)?;
    let t1 = r0[1].checked_mul(m1)?;
    let t2 = r0[2].checked_mul(m2)?;
    t0.checked_sub(t1)?.checked_add(t2)
}

fn lift(v: [i128; 3]) -> Option<i128> {
    v[0].checked_mul(v[0])?
        .checked_add(v[1].checked_mul(v[1])?)?
        .checked_add(v[2].checked_mul(v[2])?)
}

fn insphere_det(a: [i128; 3], b: [i128; 3], c: [i128; 3], d: [i128; 3]) -> Option<i128> {
    let al = lift(a)?;
    let bl = lift(b)?;
    let cl = lift(c)?;
    let dl = lift(d)?;
    let ma = det3(b, c, d)?;
    let mb = det3(a, c, d)?;
    let mc = det3(a, b, d)?;
    let md = det3(a, b, c)?;
    al.checked_mul(ma)?
        .checked_sub(bl.checked_mul(mb)?)?
        .checked_add(cl.checked_mul(mc)?)?
        .checked_sub(dl.checked_mul(md)?)
}

pub fn insphere_probe(
    a: [i64; 3],
    b: [i64; 3],
    c: [i64; 3],
    d: [i64; 3],
    e: [i64; 3],
    i: usize,
) -> Option<i128> {
    if i > 3 {
        return None;
    }
    let probe = a[i] as i128;
    let aex = (a[0] as i128).checked_sub(e[0] as i128)?;
    let aey = (a[1] as i128).checked_sub(e[1] as i128)?;
    let aez = (a[2] as i128).checked_sub(e[2] as i128)?;
    let bex = (b[0] as i128).checked_sub(e[0] as i128)?;
    let bey = (b[1] as i128).checked_sub(e[1] as i128)?;
    let bez = (b[2] as i128).checked_sub(e[2] as i128)?;
    let cex = (c[0] as i128).checked_sub(e[0] as i128)?;
    let cey = (c[1] as i128).checked_sub(e[1] as i128)?;
    let cez = (c[2] as i128).checked_sub(e[2] as i128)?;
    let dex = (d[0] as i128).checked_sub(e[0] as i128)?;
    let dey = (d[1] as i128).checked_sub(e[1] as i128)?;
    let dez = (d[2] as i128).checked_sub(e[2] as i128)?;
    let det = insphere_det([aex, aey, aez], [bex, bey, bez], [cex, cey, cez], [dex, dey, dez])?;
    det.checked_add(probe)
}
