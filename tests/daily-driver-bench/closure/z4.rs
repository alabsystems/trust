pub fn f(v: &[u32]) -> Vec<u32> { let mut w = v.to_vec(); w.sort_by(|a,b| a.cmp(b)); w }
