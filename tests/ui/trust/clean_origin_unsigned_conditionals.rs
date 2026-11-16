//@ needs-trust-verify
//@ run-pass
//@ revisions: O0 O2
//@ compile-flags: -Z trust-verify=off
//@ [O0] compile-flags: -Copt-level=0
//@ [O2] compile-flags: -Copt-level=2
//@ dont-check-compiler-stderr
// Trust: the kernel faithfulness gate remains active in the unverified lane.
// Both native execution and CTFE cover every input of the original classifier
// shapes. This consumer is ordinary Rust; there is no allocator-name dispatch.

clean {
    def low_range (x : UInt8) : UInt8 :=
        if x < 19 then 0 else if x < 30 then 1 else 0
    def high_range (x : UInt8) : UInt8 :=
        if x < 8 then 0 else if x < 16 then 1 else 0
    def forked (a b : UInt64) : UInt64 :=
        if a < b then (if a < 3 then a else b) else (if b < 7 then 9 else a)
    def literal_relations (a : UInt8) : UInt8 :=
        if a <= 10 then (if a = 7 then 1 else 2) else 3
}

const fn classified() -> [[u8; 256]; 2] {
    let mut rows = [[0; 256]; 2];
    let mut index = 0;
    while index < 256 {
        rows[0][index] = low_range(index as u8);
        rows[1][index] = high_range(index as u8);
        index += 1;
    }
    rows
}

const ROWS: [[u8; 256]; 2] = classified();

const fn literal_classified() -> [u8; 256] {
    let mut row = [0; 256];
    let mut index = 0;
    while index < 256 {
        row[index] = literal_relations(index as u8);
        index += 1;
    }
    row
}

const LITERAL_ROW: [u8; 256] = literal_classified();

fn main() {
    for index in 0..=255u8 {
        let actual_input = std::hint::black_box(index);
        let expected = [u8::from((19..30).contains(&index)), u8::from((8..16).contains(&index))];
        let expected_literal = if index <= 10 { if index == 7 { 1 } else { 2 } } else { 3 };
        assert_eq!(low_range(actual_input), expected[0]);
        assert_eq!(high_range(actual_input), expected[1]);
        assert_eq!(literal_relations(actual_input), expected_literal);
        assert_eq!(ROWS[0][usize::from(index)], expected[0]);
        assert_eq!(ROWS[1][usize::from(index)], expected[1]);
        assert_eq!(LITERAL_ROW[usize::from(index)], expected_literal);
    }
    for a in [0, 2, 3, 6, 7, u64::MAX] {
        for b in [0, 2, 3, 6, 7, u64::MAX] {
            let expected = if a < b { if a < 3 { a } else { b } } else { if b < 7 { 9 } else { a } };
            assert_eq!(forked(std::hint::black_box(a), std::hint::black_box(b)), expected);
        }
    }
}
