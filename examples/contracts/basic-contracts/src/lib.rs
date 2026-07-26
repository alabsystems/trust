#![allow(dead_code)]

/// Tier 2 public contract corpus using compiler-owned signature clauses.

pub fn divide_exact(numerator: i32, denominator: i32) -> i32
    requires denominator != 0
    ensures result * denominator == numerator
{
    numerator / denominator
}

pub fn abs_total(x: i32) -> i32
    ensures result >= 0
{
    if x == i32::MIN {
        i32::MAX
    } else if x < 0 {
        -x
    } else {
        x
    }
}

pub fn get_at(values: &[i32], index: usize) -> i32
    requires index < values.len()
    ensures result == values[index]
{
    values[index]
}

/// Deliberately UNSPECIFIED public API (no `requires`/`ensures`) — the
/// standalone inventory lane pins it as such, so do not add a contract here.
///
/// The accumulation is `saturating_add` rather than `+=`: over a `&[u32]`
/// the type permits ~2^32 elements, so a plain `+=` can genuinely overflow
/// `u64` and the verifier REFUTES it (correctly — an unbounded accumulation
/// with no length premise). Saturation makes the arithmetic total, which is
/// the honest repair for an example whose point is the contract surface, not
/// overflow behavior. `wrapping_add` would also silence the verifier, but by
/// converting a detected overflow into silent wraparound — teaching exactly
/// the anti-pattern this corpus exists to catch.
pub fn running_total(values: &[u32]) -> u64 {
    let mut total = 0_u64;
    for value in values {
        total = total.saturating_add(u64::from(*value));
    }
    total
}

pub fn midpoint_checked(low: usize, high: usize) -> Option<usize> {
    if low > high {
        return None;
    }
    Some(low + (high - low) / 2)
}
