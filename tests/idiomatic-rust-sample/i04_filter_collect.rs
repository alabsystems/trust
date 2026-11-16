pub fn evens(v: &[u32]) -> Vec<u32> { v.iter().copied().filter(|x| x % 2 == 0).collect() }
