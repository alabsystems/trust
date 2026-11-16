use super::*;

#[test]
fn test_lookup_line() {
    let source = "abcdefghijklm\nabcdefghij\n...".to_owned();
    let mut sf = SourceFile::new(
        FileName::Anon(Hash64::ZERO),
        source,
        SourceFileHashAlgorithm::Sha256,
        Some(SourceFileHashAlgorithm::Sha256),
    )
    .unwrap();
    sf.start_pos = BytePos(3);
    assert_eq!(sf.lines(), &[RelativeBytePos(0), RelativeBytePos(14), RelativeBytePos(25)]);

    assert_eq!(sf.lookup_line(RelativeBytePos(0)), Some(0));
    assert_eq!(sf.lookup_line(RelativeBytePos(1)), Some(0));

    assert_eq!(sf.lookup_line(RelativeBytePos(13)), Some(0));
    assert_eq!(sf.lookup_line(RelativeBytePos(14)), Some(1));
    assert_eq!(sf.lookup_line(RelativeBytePos(15)), Some(1));

    assert_eq!(sf.lookup_line(RelativeBytePos(25)), Some(2));
    assert_eq!(sf.lookup_line(RelativeBytePos(26)), Some(2));
}

#[test]
fn test_normalize_newlines() {
    fn check(before: &str, after: &str, expected_positions: &[u32]) {
        let mut actual = before.to_string();
        let mut actual_positions = vec![];
        normalize_newlines(&mut actual, &mut actual_positions);
        let actual_positions: Vec<_> = actual_positions.into_iter().map(|nc| nc.pos.0).collect();
        assert_eq!(actual.as_str(), after);
        assert_eq!(actual_positions, expected_positions);
    }
    check("", "", &[]);
    check("\n", "\n", &[]);
    check("\r", "\r", &[]);
    check("\r\r", "\r\r", &[]);
    check("\r\n", "\n", &[1]);
    check("hello world", "hello world", &[]);
    check("hello\nworld", "hello\nworld", &[]);
    check("hello\r\nworld", "hello\nworld", &[6]);
    check("\r\nhello\r\nworld\r\n", "\nhello\nworld\n", &[1, 7, 13]);
    check("\r\r\n", "\r\n", &[2]);
    check("hello\rworld", "hello\rworld", &[]);
}

#[test]
fn test_trim() {
    let span = |lo: usize, hi: usize| {
        Span::new(BytePos::from_usize(lo), BytePos::from_usize(hi), SyntaxContext::root(), None)
    };

    // Various positions, named for their relation to `start` and `end`.
    let well_before = 1;
    let before = 3;
    let start = 5;
    let mid = 7;
    let end = 9;
    let after = 11;
    let well_after = 13;

    // The resulting span's context should be that of `self`, not `other`.
    let other = span(start, end).with_ctxt(SyntaxContext::from_u32(999));

    // Test cases for `trim_end`.

    assert_eq!(span(well_before, before).trim_end(other), Some(span(well_before, before)));
    assert_eq!(span(well_before, start).trim_end(other), Some(span(well_before, start)));
    assert_eq!(span(well_before, mid).trim_end(other), Some(span(well_before, start)));
    assert_eq!(span(well_before, end).trim_end(other), Some(span(well_before, start)));
    assert_eq!(span(well_before, after).trim_end(other), Some(span(well_before, start)));

    assert_eq!(span(start, mid).trim_end(other), None);
    assert_eq!(span(start, end).trim_end(other), None);
    assert_eq!(span(start, after).trim_end(other), None);

    assert_eq!(span(mid, end).trim_end(other), None);
    assert_eq!(span(mid, after).trim_end(other), None);

    assert_eq!(span(end, after).trim_end(other), None);

    assert_eq!(span(after, well_after).trim_end(other), None);

    // Test cases for `trim_start`.

    assert_eq!(span(after, well_after).trim_start(other), Some(span(after, well_after)));
    assert_eq!(span(end, well_after).trim_start(other), Some(span(end, well_after)));
    assert_eq!(span(mid, well_after).trim_start(other), Some(span(end, well_after)));
    assert_eq!(span(start, well_after).trim_start(other), Some(span(end, well_after)));
    assert_eq!(span(before, well_after).trim_start(other), Some(span(end, well_after)));

    assert_eq!(span(mid, end).trim_start(other), None);
    assert_eq!(span(start, end).trim_start(other), None);
    assert_eq!(span(before, end).trim_start(other), None);

    assert_eq!(span(start, mid).trim_start(other), None);
    assert_eq!(span(before, mid).trim_start(other), None);

    assert_eq!(span(before, start).trim_start(other), None);

    assert_eq!(span(well_before, before).trim_start(other), None);
}

#[test]
fn test_unnormalized_source_length() {
    let source = "\u{feff}hello\r\nferries\r\n".to_owned();
    let sf = SourceFile::new(
        FileName::Anon(Hash64::ZERO),
        source,
        SourceFileHashAlgorithm::Sha256,
        Some(SourceFileHashAlgorithm::Sha256),
    )
    .unwrap();
    assert_eq!(sf.unnormalized_source_len, 19);
    assert_eq!(sf.normalized_source_len.0, 14);
}

#[test]
fn test_span_niche_and_four_encoding_formats_roundtrip() {
    use crate::def_id::{DefIndex, LocalDefId};
    use crate::edition::Edition;

    assert_eq!(std::mem::size_of::<Span>(), 8);
    assert_eq!(std::mem::size_of::<Option<Span>>(), 8);
    assert!(DUMMY_SP.is_dummy());

    create_session_globals_then(Edition::Edition2024, &[], None, || {
        // 1. InlineCtxt (`0` prefix): parent = None, small len & ctxt
        let s_ctxt = Span::new(BytePos(100), BytePos(120), SyntaxContext::from_u32(7), None);
        assert!(!s_ctxt.is_dummy());
        assert_eq!(s_ctxt.lo_hi(), (BytePos(100), BytePos(120)));
        assert_eq!(s_ctxt.ctxt(), SyntaxContext::from_u32(7));
        assert_eq!(s_ctxt.parent(), None);

        // 2. InlineParent (`110` prefix): ctxt = root (0), parent = Some(small)
        let p_small = LocalDefId { local_def_index: DefIndex::from_u32(42) };
        let s_parent = Span::new(BytePos(500), BytePos(550), SyntaxContext::root(), Some(p_small));
        assert_eq!(s_parent.lo_hi(), (BytePos(500), BytePos(550)));
        assert_eq!(s_parent.ctxt(), SyntaxContext::root());
        assert_eq!(s_parent.parent(), Some(p_small));

        // 3. InlinePair (`10` prefix): non-root ctxt + parent within 16 bits, small lo & len
        let s_pair =
            Span::new(BytePos(200), BytePos(210), SyntaxContext::from_u32(3), Some(p_small));
        assert_eq!(s_pair.lo_hi(), (BytePos(200), BytePos(210)));
        assert_eq!(s_pair.ctxt(), SyntaxContext::from_u32(3));
        assert_eq!(s_pair.parent(), Some(p_small));

        // 4. Interned (`111` prefix, non-MAX): large length triggers interning
        let s_interned =
            Span::new(BytePos(1000), BytePos(100_000), SyntaxContext::from_u32(9), Some(p_small));
        assert_eq!(s_interned.lo_hi(), (BytePos(1000), BytePos(100_000)));
        assert_eq!(s_interned.ctxt(), SyntaxContext::from_u32(9));
        assert_eq!(s_interned.parent(), Some(p_small));
    });
}
