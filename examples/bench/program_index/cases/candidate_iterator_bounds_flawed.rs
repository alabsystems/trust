// Candidate proof fixture: flawed iterator-adjacent off-by-one index guard.

fn find_by_index_off_by_one(data: &[u32], target: usize) -> Option<u32> {
    let mut seen = 0;
    for _ in data.iter() {
        seen += 1;
    }

    if target <= seen { Some(data[target]) } else { None }
}

fn main() {
    let data = [10, 20, 30];
    assert_eq!(find_by_index_off_by_one(&data, 1), Some(20));
}
