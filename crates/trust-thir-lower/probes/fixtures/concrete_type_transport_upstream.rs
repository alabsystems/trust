pub struct NeedsGlue<T>{pub value:u64,pub marker:core::marker::PhantomData<T>}
impl<T> Drop for NeedsGlue<T>{fn drop(&mut self){self.value=0;}}
#[derive(Clone,Copy)] #[repr(C)] pub struct HostPair<T>{pub first:T,pub second:u64}
pub fn host_owner<'a:'a,T:Copy,const N:usize>(x:u64)->u64{x}
use core::marker::PhantomData;
#[derive(Clone,Copy)] #[repr(C)] pub struct Inner<T>{pub tag:u8,pub value:T,pub zst:PhantomData<()>}
#[derive(Clone,Copy)] #[repr(C)] pub struct Packet<T>{pub prefix:u32,pub inner:Inner<T>,pub tail:[u16;2]}
#[derive(Clone,Copy)] pub struct Pair<T>{pub first:u8,pub second:T}
pub union Overlap{pub wide:u64,pub bytes:[u8;8]}
pub struct UnionHolder{pub union:Overlap}
pub struct Fat<'a>{pub prefix:u64,pub tail:&'a mut [u8]}
pub fn owner<'a:'a,T:Copy,const N:usize>(_:&'a(),_:Packet<T>,_:[T;N],_:(u8,T),_:Pair<T>){}
pub fn bad_union(_:UnionHolder){}
pub fn bad_fat(_:Fat<'static>){}
pub fn bad_callable(_:fn(u8)->u8){}
