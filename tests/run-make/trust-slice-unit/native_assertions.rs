fn main() {
    // The native oracle checks the same Rust subject, with Trust-IR lowering off.
    std::panic::set_hook(Box::new(|_| {}));
    let storage = [[(); 0]; 5];
    let cases = [
        (0, 0), (0, usize::MAX), (1, 0), (1, 1), (1, usize::MAX),
        (5, 0), (5, 4), (5, 5), (5, usize::MAX),
    ];
    for (length, index) in cases {
        let result = std::panic::catch_unwind(|| read_nonunit_zst(&storage[..length], index));
        assert_eq!(result.is_ok(), index < length, "length={length}, index={index}");
        if let Ok(value) = result {
            assert_eq!(value, []);
        }
    }
    assert_eq!(cases.len(), 9);
}
