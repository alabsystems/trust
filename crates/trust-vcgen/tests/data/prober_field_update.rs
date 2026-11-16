// Authored, unexecuted diagnostic input. Not a Trust/AY source repair.
// The body and four accessed fields mirror AY 94bf24d0 Prober::ensure_num_vars.
// Unused Prober fields/derives are omitted; visibility and crate identity differ.
pub struct Prober {
    num_vars: usize,
    bin_occs: Vec<u32>,
    propfixed: Vec<i64>,
    uip_seen: Vec<bool>,
}

impl Prober {
    pub fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        self.num_vars = num_vars;
        let num_lits = num_vars.saturating_mul(2);
        if self.bin_occs.len() < num_lits {
            self.bin_occs.resize(num_lits, 0);
        }
        if self.propfixed.len() < num_lits {
            self.propfixed.resize(num_lits, -1);
        }
        if self.uip_seen.len() < num_vars {
            self.uip_seen.resize(num_vars, false);
        }
    }
}
