#![crate_type = "lib"]
// MUTANT (soundness regression guard, adversarial-audit 2026-06-16): the discriminant
// `cond` is a bounds comparison on ONE path and the constant `true` on the other, so on
// the `k != 0` path `s[i]` runs UNGUARDED. The bounds obligation is SAT (real OOB when
// i >= len) and MUST be refused (exit 1). Threading the `i < s.len()` comparison as a
// dominating guard — without checking it is the discriminant's UNIQUE (path-dominating)
// definition — would FALSELY prove it (the hole `resolve_bool_comparison_def`; closed by
// the single-assignment requirement).
pub fn nondominating_bool_guard(s: &[u32], i: usize, k: usize) -> u32 {
    let cond = if k == 0 { i < s.len() } else { true };
    if cond { s[i] } else { 0 }
}
