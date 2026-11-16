use std::collections::HashMap;
pub fn word_counts(text: &str) -> HashMap<&str, usize> {
    let mut m: HashMap<&str, usize> = HashMap::new();
    for w in text.split_whitespace() {
        *m.entry(w).or_insert(0) += 1;
    }
    m
}
pub fn most_common(text: &str) -> Option<usize> {
    word_counts(text).values().copied().max()
}
