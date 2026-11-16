pub trait Values { const SIGNED:i8; const FLAG:bool; const WIDE:u128; const FLOAT:f32; }
impl Values for u8 { const SIGNED:i8=-7; const FLAG:bool=true; const WIDE:u128=u128::MAX; const FLOAT:f32=-0.0; }
impl Values for u16 { const SIGNED:i8=42; const FLAG:bool=false; const WIDE:u128=7; const FLOAT:f32=1.5; }
#[repr(C)] pub struct Layout<T>{prefix:u8,value:T,tail:u8}
pub const EXPECT_U8:usize=core::mem::offset_of!(Layout<u8>,value);
pub const EXPECT_U16:usize=core::mem::offset_of!(Layout<u16>,value);
pub fn owner<'a:'a,T:Values,const N:u32>(_:&'a ()){let _=N;}
