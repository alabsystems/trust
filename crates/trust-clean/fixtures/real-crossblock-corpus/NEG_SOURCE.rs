// xblock_neg — reconstructed generating source for
// fixtures/real-crossblock-corpus/double_bump.json (commit a4ea5c0876).
// Negative control: TWO checked-increment commit sites for the same counter
// (one per if-arm) — the fail-closed fallback must DECLINE (ambiguous).
pub fn double_bump(n: u32, flag: bool) -> u32 {
    let mut i: u32 = 0;
    while i < n {
        if flag {
            i += 1;
        } else {
            i += 1;
        }
    }
    i
}
