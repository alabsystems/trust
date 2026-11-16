pub struct P {
    pub x: i32,
    pub y: i32,
}
impl P {
    pub fn new(x: i32, y: i32) -> P {
        P { x, y }
    }
    pub fn manhattan(&self) -> i32 {
        self.x.abs().saturating_add(self.y.abs())
    }
}
