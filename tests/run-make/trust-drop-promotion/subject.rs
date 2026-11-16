pub struct Bomb {
    pub value: u32,
}
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("drop ran");
    }
}
pub const BOMB: Bomb = Bomb { value: 7 };

pub fn literal_temp() -> u32 {
    let r = &Bomb { value: 7 };
    r.value
}
pub fn named_temp() -> u32 {
    let r = &BOMB;
    r.value
}
pub fn array_temp() -> u32 {
    let r = &[Bomb { value: 7 }];
    r[0].value
}
pub fn projected_temp() -> u32 {
    let r = &(Bomb { value: 7 }, 3u32).0;
    r.value
}
pub fn tuple_temp() -> u32 {
    let r = &(Bomb { value: 7 },);
    r.0.value
}
pub struct Wrapper {
    pub prefix: u64,
    pub bomb: Bomb,
}
pub fn projected_runtime(value: u32) -> u32 {
    let r = &(Bomb { value }, 3u32).0;
    r.value
}
pub fn scalar_runtime(value: u32) -> u32 {
    let r = &(Bomb { value }, 3u32).1;
    *r
}
pub fn struct_runtime(value: u32) -> u32 {
    let r = &Wrapper {
        prefix: 99,
        bomb: Bomb { value },
    }
    .bomb;
    r.value
}
pub fn nested_runtime(value: u32) -> u32 {
    let r = &(
        0u8,
        Wrapper {
            prefix: 99,
            bomb: Bomb { value },
        },
    )
        .1
        .bomb;
    r.value
}
pub fn scoped_runtime(value: u32) -> u32 {
    let r = &({
        let marker = 3u32;
        (Bomb { value }, marker)
    })
    .0;
    r.value
}
pub fn read_bomb(value: &Bomb) -> u32 {
    value.value
}
pub fn call_runtime(value: u32) -> u32 {
    read_bomb(&(Bomb { value }, 3u32).0)
}
pub fn safe_literal() -> u32 {
    *&7u32
}
pub fn safe_tuple() -> u32 {
    (&(5u32, 7u32)).1
}
