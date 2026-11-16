pub fn f(v: &[u32]) -> usize { v.iter().enumerate().filter(|(i,_)| i % 2 == 0).count() }
