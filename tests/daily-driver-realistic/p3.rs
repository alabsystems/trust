pub fn parse_pairs(s: &str) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    for line in s.lines() {
        let mut it = line.split(',');
        if let (Some(a), Some(b)) = (it.next(), it.next())
            && let (Ok(x), Ok(y)) = (a.trim().parse::<u32>(), b.trim().parse::<u32>())
        {
            out.push((x, y));
        }
    }
    out
}
