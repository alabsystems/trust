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
pub fn concrete_u8(_: &(),x:Packet<u8>,_:[u8;3],_:(u8,u8),_:Pair<u8>){let _=x;}
pub fn concrete_u16(_: &(),x:Packet<u16>,_:[u16;5],_:(u8,u16),_:Pair<u16>){let _=x;}
fn main(){host_owner::<*const u8,7>(3);host_owner::<u8,3>(1);host_owner::<u16,5>(2);let p8=Packet{prefix:1,inner:Inner{tag:2,value:3u8,zst:core::marker::PhantomData},tail:[4,5]};let p16=Packet{prefix:1,inner:Inner{tag:2,value:3u16,zst:core::marker::PhantomData},tail:[4,5]};owner::<u8,3>(&(),p8,[1;3],(1,2),Pair{first:1,second:2});owner::<u16,5>(&(),p16,[1;5],(1,2),Pair{first:1,second:2});}
