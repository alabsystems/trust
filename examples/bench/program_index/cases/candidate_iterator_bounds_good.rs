// Candidate proof fixture: iterator search avoids direct index bounds obligations.

fn find_by_index(data: &[u32], target: usize) -> Option<u32> {
    for (idx, value) in data.iter().enumerate() {
        if idx == target {
            return Some(*value);
        }
    }
    None
}

fn main() {
    let data = [10, 20, 30];
    assert_eq!(find_by_index(&data, 1), Some(20));
    assert_eq!(find_by_index(&data, 4), None);
}
