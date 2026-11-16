#![forbid(unsafe_code)]

#[derive(Clone)]
pub enum Json {
    Null,
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

struct P<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn bump(&mut self) -> Option<u8> {
        let c = *self.b.get(self.i)?;
        self.i += 1;
        Some(c)
    }
}

pub fn parse(b: &[u8]) -> Option<u8> {
    let mut p = P { b, i: 0 };
    p.bump()
}
