//! TINV design §5 P1 (the json `Parser` reduction), verbatim from
//! `tests/ui/trust/tinv/tinv_p1_json_parser.rs` without the UI annotations.
#![forbid(unsafe_code)]

struct P<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.i += 1;
        Some(c)
    }

    fn literal(&mut self, w: &'static [u8]) -> bool {
        if self.b.len() >= self.i + w.len() && &self.b[self.i..self.i + w.len()] == w {
            self.i += w.len();
            true
        } else {
            false
        }
    }
}

pub fn parse(b: &[u8]) -> bool {
    let mut p = P { b, i: 0 };
    p.bump();
    p.literal(b"null")
}
