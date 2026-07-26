pub fn midpoint(a: u64, b: u64) -> u64 
    requires a <= u64::MAX - b
{
    (a.checked_add(b).expect("midpoint addition overflow")) / 2
}
