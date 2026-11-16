//! Source of the `d5_downcast_*_mir.json` fixtures
//! (tests/call_dest_downcast_try_hop_realmir.rs). D5-A-DOWNCAST-1 / D5-A-TRY-HOP-1:
//! astream-agent `fork.rs` (`cog_fork_swap`, `try_cog_fork_swap`) in miniature.
#[derive(Clone)]
pub struct R(pub u64);

fn index_in(records: &[R], at: u64) -> Option<usize> {
    usize::try_from(at).ok().filter(|&i| i < records.len())
}

pub fn swap(records: &[R], at: u64, replacement: R) -> Vec<R> {
    let mut out = records.to_vec();
    if let Some(i) = index_in(records, at) {
        out[i] = replacement;
    }
    out
}

pub fn try_swap(records: &[R], at: u64, replacement: R) -> Option<Vec<R>> {
    let i = index_in(records, at)?;
    let mut out = records.to_vec();
    out[i] = replacement;
    Some(out)
}

// Control: direct guard, no helper.
pub fn swap_direct(records: &[R], i: usize, replacement: R) -> Vec<R> {
    let mut out = records.to_vec();
    if i < records.len() {
        out[i] = replacement;
    }
    out
}

// Real bug control: no guard at all -> must stay refuted.
pub fn swap_bad(records: &[R], i: usize, replacement: R) -> Vec<R> {
    let mut out = records.to_vec();
    out[i] = replacement;
    out
}
