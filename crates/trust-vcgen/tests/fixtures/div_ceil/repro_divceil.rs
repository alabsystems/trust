// Is `usize::div_ceil` modelled? A dominating bound on `n` should bound `n.div_ceil(8)`.
pub const MAX: usize = 1 << 16;
pub fn via_div_ceil(n: usize) -> Option<Vec<u8>> {
    if n > MAX {
        return None;
    }
    Some(vec![0u8; n.div_ceil(8)])
}
// Control: the same size spelled with Add/Div.
pub fn via_add_div(n: usize) -> Option<Vec<u8>> {
    if n > MAX {
        return None;
    }
    Some(vec![0u8; (n + 7) / 8])
}
// Control: a dominating bound on the count itself.
pub fn direct(n: usize) -> Option<Vec<u8>> {
    if n > MAX {
        return None;
    }
    Some(vec![0u8; n])
}
