// n-queens (bitmask recursion) + a tiny expression tokenizer/evaluator over bytes.
#[derive(Clone, Copy, PartialEq)]
enum Tok { Num(u64), Plus, Star, LParen, RParen, End }

struct Lexer<'a> { src: &'a [u8], pos: usize }

impl<'a> Lexer<'a> {
    fn new(src: &'a [u8]) -> Self { Lexer { src, pos: 0 } }
    fn next(&mut self) -> Tok {
        while self.pos < self.src.len() && self.src[self.pos] == b' ' { self.pos += 1; }
        if self.pos >= self.src.len() { return Tok::End; }
        let c = self.src[self.pos];
        if c >= b'0' && c <= b'9' {
            let mut v = 0u64;
            while self.pos < self.src.len() {
                let d = self.src[self.pos];
                if d < b'0' || d > b'9' { break; }
                v = v * 10 + (d - b'0') as u64;
                self.pos += 1;
            }
            return Tok::Num(v);
        }
        self.pos += 1;
        match c { b'+' => Tok::Plus, b'*' => Tok::Star, b'(' => Tok::LParen, b')' => Tok::RParen, _ => Tok::End }
    }
}

struct Parser<'a> { lx: Lexer<'a>, cur: Tok }

impl<'a> Parser<'a> {
    fn new(src: &'a [u8]) -> Self { let mut lx = Lexer::new(src); let cur = lx.next(); Parser { lx, cur } }
    fn bump(&mut self) { self.cur = self.lx.next(); }
    fn atom(&mut self) -> u64 {
        match self.cur {
            Tok::Num(v) => { self.bump(); v }
            Tok::LParen => { self.bump(); let v = self.expr(); if self.cur == Tok::RParen { self.bump(); } v }
            _ => 0,
        }
    }
    fn term(&mut self) -> u64 {
        let mut v = self.atom();
        while self.cur == Tok::Star { self.bump(); v = v * self.atom(); }
        v
    }
    fn expr(&mut self) -> u64 {
        let mut v = self.term();
        while self.cur == Tok::Plus { self.bump(); v = v + self.term(); }
        v
    }
}

fn queens(n: u32, row: u32, cols: u32, d1: u32, d2: u32) -> u64 {
    if row == n { return 1; }
    let full = (1u32 << n) - 1;
    let mut avail = full & !(cols | d1 | d2);
    let mut count = 0u64;
    while avail != 0 {
        let bit = avail & (!avail + 1);
        avail &= avail - 1;
        count += queens(n, row + 1, cols | bit, ((d1 | bit) << 1) & full, (d2 | bit) >> 1);
    }
    count
}

fn digits(mut x: u64, buf: &mut [u8; 24]) -> usize {
    let mut tmp = [0u8; 24];
    let mut n = 0;
    if x == 0 { tmp[0] = b'0'; n = 1; }
    while x > 0 { tmp[n] = b'0' + (x % 10) as u8; x /= 10; n += 1; }
    let mut i = 0;
    while i < n { buf[i] = tmp[n - 1 - i]; i += 1; }
    n
}

#[no_mangle]
pub extern "C" fn rung(x: u64) -> u64 {
    // expression: "(<x> + 3) * 2 + 4 * (1 + <x>)"
    let mut src = [b' '; 96];
    let mut p = 0usize;
    let mut num = [0u8; 24];
    let n = digits(x % 100000, &mut num);
    let pre: &[u8] = b"(";
    let mid: &[u8] = b" + 3) * 2 + 4 * (1 + ";
    let post: &[u8] = b")";
    let mut i = 0; while i < pre.len() { src[p] = pre[i]; p += 1; i += 1; }
    i = 0; while i < n { src[p] = num[i]; p += 1; i += 1; }
    i = 0; while i < mid.len() { src[p] = mid[i]; p += 1; i += 1; }
    i = 0; while i < n { src[p] = num[i]; p += 1; i += 1; }
    i = 0; while i < post.len() { src[p] = post[i]; p += 1; i += 1; }
    let mut ps = Parser::new(&src[..p]);
    let e = ps.expr();
    let qn = if x >= 1000000 { (x - 1000000) as u32 } else { (x % 8) as u32 + 1 };
    e + queens(qn, 0, 0, 0, 0) * 1000003
}
