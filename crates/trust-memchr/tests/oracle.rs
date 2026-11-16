//! Correctness tests for the first-party memchr.
//!
//! Two independent sources of truth, neither of which is this crate's own
//! search code:
//!
//! 1. **A naive oracle** written here from the *definition* of each routine.
//!    It shares no code with `src/`, so a bug in the scan core cannot hide in
//!    the expectation.
//! 2. **Upstream's own documented examples**, copied verbatim from the memchr
//!    2.8 rustdoc, which pin the exact values callers were promised.
//!
//! The corpus is exhaustive over short strings — where every empty-needle,
//! overlap and boundary case lives — plus a seeded pseudorandom sweep over
//! longer inputs and wider alphabets.
//!
//! This suite is the in-tree half. The other half is a differential harness
//! that runs every API against the registry `memchr` crate on the same corpus;
//! it cannot live here, because depending on upstream memchr is exactly what
//! this crate exists to stop doing.

use memchr::arch::all::{is_equal, is_prefix, is_suffix};
use memchr::{
    Memchr, Memchr2, Memchr3, memchr, memchr_iter, memchr2, memchr2_iter, memchr3, memchr3_iter,
    memmem, memrchr, memrchr_iter, memrchr2, memrchr2_iter, memrchr3, memrchr3_iter,
};

// ---------------------------------------------------------------- oracle ---

fn oracle_positions(h: &[u8], needles: &[u8]) -> Vec<usize> {
    let mut out = Vec::new();
    for (i, b) in h.iter().enumerate() {
        if needles.contains(b) {
            out.push(i);
        }
    }
    out
}

/// Every offset where `n` occurs in `h`, overlapping matches included. An empty
/// needle occurs at every offset from `0` through `h.len()`.
fn oracle_all_substring(h: &[u8], n: &[u8]) -> Vec<usize> {
    let mut out = Vec::new();
    if n.is_empty() {
        for i in 0..=h.len() {
            out.push(i);
        }
        return out;
    }
    if n.len() > h.len() {
        return out;
    }
    for i in 0..=(h.len() - n.len()) {
        if &h[i..i + n.len()] == n {
            out.push(i);
        }
    }
    out
}

/// Forward, non-overlapping iteration: take a match, then skip
/// `max(needle.len(), 1)` bytes.
fn oracle_find_iter(h: &[u8], n: &[u8]) -> Vec<usize> {
    let all = oracle_all_substring(h, n);
    let step = if n.is_empty() { 1 } else { n.len() };
    let mut out: Vec<usize> = Vec::new();
    let mut next_allowed = 0usize;
    for &i in &all {
        if i >= next_allowed {
            out.push(i);
            next_allowed = i + step;
        }
    }
    out
}

/// Reverse, non-overlapping iteration: each match must end at or before the
/// start of the previous one. An empty needle walks `len, len-1, …, 0`.
fn oracle_rfind_iter(h: &[u8], n: &[u8]) -> Vec<usize> {
    if n.is_empty() {
        return (0..=h.len()).rev().collect();
    }
    let all = oracle_all_substring(h, n);
    let mut out = Vec::new();
    let mut limit = h.len();
    for &i in all.iter().rev() {
        if i + n.len() <= limit {
            out.push(i);
            limit = i;
        }
    }
    out
}

// ------------------------------------------------------------- the checks ---

fn check_bytes(h: &[u8], n1: u8, n2: u8, n3: u8) {
    let p1 = oracle_positions(h, &[n1]);
    let p2 = oracle_positions(h, &[n1, n2]);
    let p3 = oracle_positions(h, &[n1, n2, n3]);

    assert_eq!(memchr(n1, h), p1.first().copied(), "memchr {h:?} {n1}");
    assert_eq!(memrchr(n1, h), p1.last().copied(), "memrchr {h:?} {n1}");
    assert_eq!(memchr2(n1, n2, h), p2.first().copied(), "memchr2 {h:?}");
    assert_eq!(memrchr2(n1, n2, h), p2.last().copied(), "memrchr2 {h:?}");
    assert_eq!(memchr3(n1, n2, n3, h), p3.first().copied(), "memchr3 {h:?}");
    assert_eq!(memrchr3(n1, n2, n3, h), p3.last().copied(), "memrchr3 {h:?}");

    assert_eq!(memchr_iter(n1, h).collect::<Vec<_>>(), p1, "memchr_iter {h:?}");
    assert_eq!(memchr2_iter(n1, n2, h).collect::<Vec<_>>(), p2);
    assert_eq!(memchr3_iter(n1, n2, n3, h).collect::<Vec<_>>(), p3);

    let r1: Vec<usize> = p1.iter().rev().copied().collect();
    let r2: Vec<usize> = p2.iter().rev().copied().collect();
    let r3: Vec<usize> = p3.iter().rev().copied().collect();
    assert_eq!(memrchr_iter(n1, h).collect::<Vec<_>>(), r1, "memrchr_iter {h:?}");
    assert_eq!(memrchr2_iter(n1, n2, h).collect::<Vec<_>>(), r2);
    assert_eq!(memrchr3_iter(n1, n2, n3, h).collect::<Vec<_>>(), r3);

    assert_eq!(memchr_iter(n1, h).count(), p1.len(), "count {h:?}");

    // Double-ended: alternating next/next_back must peel the same positions
    // from the two ends of `p1` and meet exactly once.
    let mut it = Memchr::new(n1, h);
    let mut lo = 0usize;
    let mut hi = p1.len();
    let mut front = true;
    loop {
        let (_, upper) = it.size_hint();
        assert!(upper.unwrap() >= hi - lo, "size_hint upper bound too small");
        let got = if front { it.next() } else { it.next_back() };
        if lo == hi {
            assert_eq!(got, None, "exhausted iterator must fuse");
            assert_eq!(it.next(), None);
            assert_eq!(it.next_back(), None);
            break;
        }
        if front {
            assert_eq!(got, Some(p1[lo]));
            lo += 1;
        } else {
            hi -= 1;
            assert_eq!(got, Some(p1[hi]));
        }
        front = !front;
    }

    // The same walk through the `arch::all` searchers.
    {
        use memchr::arch::all::memchr as a;
        let one = a::One::new(n1);
        assert_eq!(one.find(h), p1.first().copied());
        assert_eq!(one.rfind(h), p1.last().copied());
        assert_eq!(one.count(h), p1.len());
        assert_eq!(one.iter(h).collect::<Vec<_>>(), p1);
        assert_eq!(one.iter(h).rev().collect::<Vec<_>>(), r1);
        let two = a::Two::new(n1, n2);
        assert_eq!(two.find(h), p2.first().copied());
        assert_eq!(two.rfind(h), p2.last().copied());
        assert_eq!(two.iter(h).collect::<Vec<_>>(), p2);
        assert_eq!(two.iter(h).rev().collect::<Vec<_>>(), r2);
        let three = a::Three::new(n1, n2, n3);
        assert_eq!(three.find(h), p3.first().copied());
        assert_eq!(three.rfind(h), p3.last().copied());
        assert_eq!(three.iter(h).collect::<Vec<_>>(), p3);
        assert_eq!(three.iter(h).rev().collect::<Vec<_>>(), r3);
    }

    // Memchr2/Memchr3 double-ended, collected from both ends at once.
    assert_eq!(Memchr2::new(n1, n2, h).rev().collect::<Vec<_>>(), r2);
    assert_eq!(Memchr3::new(n1, n2, n3, h).rev().collect::<Vec<_>>(), r3);
}

fn check_substring(h: &[u8], n: &[u8]) {
    let all = oracle_all_substring(h, n);
    let fwd = oracle_find_iter(h, n);
    let rev = oracle_rfind_iter(h, n);

    assert_eq!(memmem::find(h, n), all.first().copied(), "find {h:?} {n:?}");
    assert_eq!(memmem::rfind(h, n), all.last().copied(), "rfind {h:?} {n:?}");
    assert_eq!(memmem::find_iter(h, n).collect::<Vec<_>>(), fwd, "find_iter");
    assert_eq!(memmem::rfind_iter(h, n).collect::<Vec<_>>(), rev, "rfind_iter");

    let f = memmem::Finder::new(n);
    assert_eq!(f.find(h), all.first().copied());
    assert_eq!(f.needle(), n);
    assert_eq!(f.find_iter(h).collect::<Vec<_>>(), fwd);
    assert_eq!(f.as_ref().find(h), all.first().copied());
    assert_eq!(f.clone().into_owned().find(h), all.first().copied());

    let r = memmem::FinderRev::new(n);
    assert_eq!(r.rfind(h), all.last().copied());
    assert_eq!(r.needle(), n);
    assert_eq!(r.rfind_iter(h).collect::<Vec<_>>(), rev);
    assert_eq!(r.clone().into_owned().rfind(h), all.last().copied());

    // `size_hint` must bound the number of matches actually produced, and the
    // empty-needle lower bound must be exact.
    let mut it = memmem::find_iter(h, n);
    let (lo, hi) = it.size_hint();
    assert!(hi.unwrap() >= fwd.len(), "find_iter upper bound too small");
    if n.is_empty() {
        assert_eq!(lo, h.len() + 1);
    }
    for &expect in &fwd {
        assert_eq!(it.next(), Some(expect));
    }
    assert_eq!(it.next(), None);

    let mut builder = memmem::FinderBuilder::new();
    builder.prefilter(memmem::Prefilter::None);
    assert_eq!(builder.build_forward(n).find(h), all.first().copied());
    assert_eq!(builder.build_reverse(n).rfind(h), all.last().copied());
    assert_eq!(builder.build_forward_owned(n.to_vec()).find(h), all.first().copied());
    assert_eq!(builder.build_reverse_owned(n.to_vec()).rfind(h), all.last().copied());

    assert_eq!(is_prefix(h, n), h.len() >= n.len() && &h[..n.len()] == n);
    assert_eq!(is_suffix(h, n), h.len() >= n.len() && &h[h.len() - n.len()..] == n);
    assert_eq!(is_equal(h, n), h == n);
}

fn enumerate(alphabet: &[u8], max_len: usize) -> Vec<Vec<u8>> {
    let mut out = vec![Vec::new()];
    let mut level = vec![Vec::new()];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for base in &level {
            for &b in alphabet {
                let mut v = base.clone();
                v.push(b);
                next.push(v);
            }
        }
        out.extend(next.iter().cloned());
        level = next;
    }
    out
}

// -------------------------------------------------------------- the tests ---

#[test]
fn exhaustive_short_binary_alphabet() {
    for h in enumerate(b"ab", 10) {
        check_bytes(&h, b'a', b'b', b'c');
    }
    for h in enumerate(b"ab", 7) {
        for n in enumerate(b"ab", 3) {
            check_substring(&h, &n);
        }
    }
}

#[test]
fn exhaustive_short_ternary_alphabet() {
    for h in enumerate(b"abc", 6) {
        check_bytes(&h, b'a', b'b', b'c');
    }
    for h in enumerate(b"abc", 4) {
        for n in enumerate(b"abc", 3) {
            check_substring(&h, &n);
        }
    }
}

#[test]
fn adversarial() {
    let lens = [0usize, 1, 2, 3, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 1024];
    for len in lens {
        let run = vec![b'a'; len];
        check_bytes(&run, b'a', b'b', b'c');
        check_bytes(&run, b'z', b'y', b'x');
        check_substring(&run, b"");
        check_substring(&run, b"a");
        check_substring(&run, &run);
        check_substring(&run, &vec![b'a'; len + 1]);
        check_substring(&run, b"z");

        // Needle planted at every offset that a vectorised implementation
        // would treat as a chunk boundary.
        for off in [0usize, 1, 14, 15, 16, 30, 31, 32, 62, 63, 64] {
            if off + 3 <= len {
                let mut v = run.clone();
                v[off..off + 3].copy_from_slice(b"xyz");
                check_substring(&v, b"xyz");
                check_bytes(&v, b'x', b'y', b'z');
            }
        }

        // Every byte value, so nothing depends on the needle being ASCII.
        let full: Vec<u8> = (0..len).map(|i| (i % 256) as u8).collect();
        check_bytes(&full, 0, 128, 255);
        check_substring(&full, &[0, 1, 2]);
        check_substring(&full, &[253, 254, 255]);

        // Periodic input: the worst case for a naive substring scan, and the
        // shape where a shift-table algorithm is most likely to disagree.
        let per: Vec<u8> = (0..len).map(|i| if i % 2 == 0 { b'a' } else { b'b' }).collect();
        check_substring(&per, b"ab");
        check_substring(&per, b"ba");
        check_substring(&per, b"aab");
        check_substring(&per, b"aaa");
    }
}

#[test]
fn randomized() {
    // xorshift64; a fixed seed keeps failures reproducible.
    let mut state: u64 = 0x5eed_1234_dead_beef;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut below = |n: usize| if n == 0 { 0 } else { (next() % n as u64) as usize };

    for _ in 0..4_000 {
        let alpha = [2usize, 3, 4, 16, 64, 256][below(6)];
        let hlen = match below(3) {
            0 => below(8),
            1 => below(70),
            _ => below(600),
        };
        let mut h: Vec<u8> = (0..hlen).map(|_| below(alpha) as u8).collect();
        let nlen = match below(3) {
            0 => below(3),
            1 => below(6),
            _ => below(hlen + 2),
        };
        let mut n: Vec<u8> = (0..nlen).map(|_| below(alpha) as u8).collect();
        // Half the time force a hit; a quarter of the time take the needle out
        // of the haystack itself.
        if !n.is_empty() && n.len() <= h.len() && below(2) == 0 {
            let at = below(h.len() - n.len() + 1);
            h[at..at + n.len()].copy_from_slice(&n);
        }
        if !h.is_empty() && below(4) == 0 {
            let at = below(h.len());
            let end = (at + 1 + below(8)).min(h.len());
            n = h[at..end].to_vec();
        }
        check_substring(&h, &n);
        check_bytes(&h, below(alpha) as u8, below(alpha) as u8, below(alpha) as u8);
    }
}

/// The examples in the upstream rustdoc, verbatim. These are the values
/// callers were promised by name.
#[test]
fn upstream_documented_examples() {
    assert_eq!(Some(10), memchr(b'z', b"foo bar baz quuz"));
    assert_eq!(memchr(b'k', b"the quick brown fox"), Some(8));
    assert_eq!(memrchr(b'o', b"the quick brown fox"), Some(17));
    assert_eq!(memchr2(b'k', b'q', b"the quick brown fox"), Some(4));
    assert_eq!(memrchr2(b'k', b'o', b"the quick brown fox"), Some(17));
    assert_eq!(memchr3(b'k', b'q', b'u', b"the quick brown fox"), Some(4));
    assert_eq!(memrchr3(b'k', b'o', b'n', b"the quick brown fox"), Some(17));

    let mut it = memchr3_iter(b'a', b'b', b'c', b"xyzaxyzbxyzc").rev();
    assert_eq!(Some(11), it.next());
    assert_eq!(Some(7), it.next());
    assert_eq!(Some(3), it.next());
    assert_eq!(None, it.next());

    let haystack = b"foo bar foo baz foo";
    let mut it = memmem::find_iter(haystack, "foo");
    assert_eq!(Some(0), it.next());
    assert_eq!(Some(8), it.next());
    assert_eq!(Some(16), it.next());
    assert_eq!(None, it.next());

    let mut it = memmem::rfind_iter(haystack, "foo");
    assert_eq!(Some(16), it.next());
    assert_eq!(Some(8), it.next());
    assert_eq!(Some(0), it.next());
    assert_eq!(None, it.next());

    let finder = memmem::Finder::new("foo");
    assert_eq!(Some(4), finder.find(b"baz foo quux"));
    assert_eq!(None, finder.find(b"quux baz bar"));

    assert_eq!(Some(0), memmem::find(b"foo bar baz", b"foo"));
    assert_eq!(Some(4), memmem::find(b"foo bar baz", b"bar"));
    assert_eq!(None, memmem::find(b"foo bar baz", b"quux"));
    assert_eq!(Some(0), memmem::rfind(b"foo bar baz", b"foo"));
    assert_eq!(Some(4), memmem::rfind(b"foo bar baz", b"bar"));
    assert_eq!(Some(8), memmem::rfind(b"foo bar baz", b"ba"));
    assert_eq!(None, memmem::rfind(b"foo bar baz", b"quux"));

    assert_eq!(Some(0), memmem::Finder::new("foo").find(b"foo bar baz"));
    assert_eq!(Some(0), memmem::FinderRev::new("foo").rfind(b"foo bar baz"));
    assert_eq!(None, memmem::FinderRev::new("quux").rfind(b"foo bar baz"));
}

/// The iterators were regressed once upstream by losing `Send`/`Sync` (memchr
/// issue 133). Same guard here.
#[test]
fn iterators_stay_send_and_sync() {
    use core::panic::{RefUnwindSafe, UnwindSafe};
    fn assert_send_sync<T: Send + Sync + UnwindSafe + RefUnwindSafe>() {}
    assert_send_sync::<Memchr>();
    assert_send_sync::<Memchr2>();
    assert_send_sync::<Memchr3>();
    assert_send_sync::<memmem::Finder<'static>>();
    assert_send_sync::<memmem::FinderRev<'static>>();
}

/// `Finder<'static>` inside a `Clone + Debug` prefilter is exactly how
/// aho-corasick and regex-automata hold it; if either bound were lost those
/// crates would stop compiling against this one.
#[test]
fn finder_is_clone_and_debug_at_static() {
    #[derive(Clone, Debug)]
    #[allow(dead_code)]
    struct Prefilter(memmem::Finder<'static>, memmem::FinderRev<'static>);

    let p = Prefilter(
        memmem::Finder::new(b"needle").into_owned(),
        memmem::FinderRev::new(b"needle").into_owned(),
    );
    let q = p.clone();
    assert_eq!(q.0.find(b"a needle here"), Some(2));
    assert!(format!("{p:?}").contains("Prefilter"));
}

/// Upstream's default prefilter is `Auto`, and `FinderBuilder::default()`
/// starts from it exactly as `FinderBuilder::new()` does. The derive's
/// `#[default]` marker is what decides this, so a moved marker fails here.
#[test]
fn prefilter_defaults_to_auto() {
    assert!(matches!(memmem::Prefilter::default(), memmem::Prefilter::Auto));
    assert_eq!(
        format!("{:?}", memmem::FinderBuilder::default()),
        format!("{:?}", memmem::FinderBuilder::new()),
    );
}

/// The lint expectations in Rust source `text`: each `expect(` outside a
/// string in an outer `#[..]` or inner `#![..]` attribute, so an `expect`
/// attribute and each `expect` a `cfg_attr(..)` applies, nested or not, however
/// it is spaced, and commented too unless the comment has an unbalanced quote
/// or bracket. Too high a count only asks for Rust 1.81 where it was not
/// needed; too low a one lets `rust-version` name a compiler that rejects the
/// crate.
fn lint_expectations(text: &str) -> usize {
    let text: String = text.chars().filter(|character| !character.is_whitespace()).collect();
    let mut found = 0;
    let mut rest = text.as_str();
    while let Some(at) = rest.find('#') {
        rest = &rest[at + 1..];
        let inner = rest.strip_prefix('!').unwrap_or(rest);
        if let Some(attribute) = inner.strip_prefix('[') {
            found += attribute_expectations(attribute);
        }
    }
    found
}

/// Each `expect(` outside a string in the attribute at the start of
/// `attribute`, up to the bracket that closes it. With whitespace gone, a
/// comment before an applied `expect` runs into it (`all(),//alwaysexpect(`),
/// so this counts the text wherever it starts, not only after a comma.
fn attribute_expectations(attribute: &str) -> usize {
    let (mut found, mut depth, mut string, mut escaped) = (0, 0usize, false, false);
    for (at, character) in attribute.char_indices() {
        match character {
            _ if escaped => escaped = false,
            '\\' if string => escaped = true,
            '"' => string = !string,
            _ if string => {}
            'e' if attribute[at..].starts_with("expect(") => found += 1,
            '(' | '[' => depth += 1,
            ')' | ']' if depth == 0 => break,
            ')' | ']' => depth -= 1,
            _ => {}
        }
    }
    found
}

/// The `(major, minor)` a `rust-version` names, spelled as Cargo accepts it:
/// `MAJOR[.MINOR[.PATCH]]`, each part a `u32` in decimal digits.
fn rust_version(declared: &str) -> Result<(u32, u32), String> {
    if declared.is_empty() {
        return Err("Cargo.toml declares no rust-version (CARGO_PKG_RUST_VERSION is empty), \
                    so nothing says which compiler this crate's #[expect] needs (Rust 1.81)"
            .to_owned());
    }
    let refused = || {
        format!(
            "Cargo.toml's rust-version {declared:?} is not MAJOR[.MINOR[.PATCH]], each a u32 in \
             decimal digits, so it cannot be compared with the Rust 1.81 that #[expect] needs"
        )
    };
    let mut parts = Vec::new();
    for part in declared.split('.') {
        if part.is_empty() || !part.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(refused());
        }
        parts.push(part.parse::<u32>().map_err(|_| refused())?);
    }
    match parts[..] {
        [major] => Ok((major, 0)),
        [major, minor] | [major, minor, _] => Ok((major, minor)),
        _ => Err(refused()),
    }
}

/// The spellings `src/` does not carry today: an inner `#![expect]`, an
/// `expect` that a `cfg_attr` applies (nested, spaced, commented, beside
/// others), and what is no expectation, an `expect(` in a string included; and
/// a `rust-version` that is empty or no version refused with what it is, not a
/// parse panic.
#[test]
fn lint_expectations_and_rust_version_are_read_in_every_spelling() {
    for (text, count) in [
        ("#[expect(dead_code)]", 1),
        ("#![expect(dead_code, reason = \"crate-wide\")]", 1),
        ("# ! [ expect ( dead_code ) ]", 1),
        ("#[cfg_attr(test, expect(dead_code))]", 1),
        ("#![cfg_attr(test, expect(dead_code))]", 1),
        ("#[cfg_attr(all(test, unix), allow(unused), expect(dead_code))]", 1),
        ("#[cfg_attr(test, cfg_attr(unix, expect(dead_code)))]", 1),
        ("#[cfg_attr(feature = \"a,)\\\"\", expect(dead_code))]", 1),
        ("#[cfg_attr(\n    all(), // always\n    expect(dead_code),\n)]", 1),
        ("#[cfg_attr(test, /* why */ expect(dead_code))]", 1),
        ("#[/* why */ expect(dead_code)]", 1),
        ("#[expect(a)] fn f() {} #![expect(b)] #[cfg_attr(test, expect(c))]", 3),
        ("#[allow(dead_code)] fn f(x: Option<u8>) -> u8 { x.expect(\"a byte\") }", 0),
        ("#[cfg_attr(test, allow(dead_code))] #[cfg_attr(expect, allow(x))] #[must_use]", 0),
        ("#[doc = \"expect(x)\"] #[must_use = \"a\\\"expect(\"]", 0),
    ] {
        assert_eq!(lint_expectations(text), count, "{text}");
    }
    for (declared, major_minor) in [("1", (1, 0)), ("1.81", (1, 81)), ("1.81.0", (1, 81))] {
        assert_eq!(rust_version(declared), Ok(major_minor), "{declared}");
    }
    let empty = rust_version("").expect_err("an empty rust-version");
    assert!(empty.contains("declares no rust-version"), "{empty}");
    let malformed = ["1.x", "1..0", ".81", "1.81.", "+1.81", "1.81-beta", " 1.81", "1.81.0.0"];
    let past_u32 = "4294967296.0";
    for declared in malformed.into_iter().chain([past_u32]) {
        let refused = rust_version(declared).expect_err(declared);
        assert!(refused.contains(&format!("rust-version {declared:?} is not")), "{refused}");
    }
}

/// `#[expect]` and its `reason` need Rust 1.81. While `src/` carries one, in
/// any spelling, the manifest's `rust-version` must not name an older compiler.
#[test]
fn declared_rust_version_covers_lint_expectations() {
    fn expectations(dir: &std::path::Path) -> usize {
        let mut found = 0;
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                found += expectations(&path);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                found += lint_expectations(&std::fs::read_to_string(&path).unwrap());
            }
        }
        found
    }
    let declared = env!("CARGO_PKG_RUST_VERSION");
    let major_minor = rust_version(declared).unwrap_or_else(|refused| panic!("{refused}"));
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let found = expectations(&source);
    if found > 0 {
        assert!(
            major_minor >= (1, 81),
            "src/ has {found} #[expect]; rust-version {declared} predates them (Rust 1.81)"
        );
    }
}
