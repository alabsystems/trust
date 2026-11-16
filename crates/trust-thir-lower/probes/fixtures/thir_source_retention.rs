#![allow(dead_code,unused_assignments)]
pub fn leaf<'a:'a,T:Copy,const N:usize>(x:u64)->u64{x}
pub fn root<'a:'a,T:Copy,const N:usize>(x:u64)->u64{leaf::<T,N>(x)}
pub fn source_chain<'a:'a,T:Copy,const N:usize>(x:u64)->u64{let a=root::<T,N>(x);let b=root::<T,N>(a);b}
pub fn source_diamond<'a:'a,T:Copy,const N:usize>(x:u64)->u64{let a=source_chain::<T,N>(x);root::<T,N>(a)}
pub fn source_ground<T:Copy>(x:u64)->u64{leaf::<u8,3>(x)}
pub unsafe fn source_store<T:Copy>(p:*mut T,x:T){unsafe{*p=x;}}
pub unsafe fn source_alias_store<T:Copy>(p:*mut T,x:T){let q=p;unsafe{*q=x;}}
pub unsafe fn source_reassigned_pointer<T:Copy>(mut p:*mut T,q:*mut T,x:T){p=q;unsafe{*p=x;}}
pub unsafe fn source_reassigned_value<T:Copy>(p:*mut T,mut x:T,y:T){x=y;unsafe{*p=x;}}
pub fn source_private(mut x:u64)->u64{x=3;x}
pub fn source_array<'a:'a,T:Copy,const N:usize>(x:[T;N])->[T;N]{x}
pub fn source_bad_borrow<T>(x:&mut T){let _r=&mut *x;}
pub fn source_bad_index<T:Copy,const N:usize>(x:[T;N])->T{x[0]}
pub fn source_bad_branch<T:Copy>(x:u64)->u64{if x==0{leaf::<T,3>(x)}else{x}}
pub fn source_bad_arithmetic<T>(x:u64)->u64{x+1}
pub fn source_bad_closure<T>(x:u64)->u64{let f=|a|a;f(x)}
pub struct NeedsGlue<T>{value:T}
impl<T> Drop for NeedsGlue<T>{fn drop(&mut self){}}
pub fn source_pending_drop<T>(x:NeedsGlue<T>)->u64{let _y=x;1}
#[derive(Clone,Copy)]
pub enum Flat { A(u8), B(u16) }
#[derive(Clone,Copy)]
pub struct Packet {pub hi:u64,pub lo:u16}
pub fn source_identity<T:Copy>(value:T)->T{value}
pub fn source_const_array<'a:'a,T:Copy,const N:usize>(value:[T;N])->[T;N]{value}
pub fn source_typed_relay<T:Copy>(prefix:[u8;2],value:T)->T{let _=prefix;source_identity(value)}
pub fn source_value_chain<T:Copy>(value:T)->T{let first=source_identity(value);source_identity(first)}
fn main(){let _=source_identity(());let _=source_typed_relay([1,2],());let _=source_value_chain(());let _=source_identity(13u64);let _=source_identity([1u8,2,3]);let _=source_identity([0u8;0]);
let _=source_identity(Packet{hi:5,lo:2});let referenced=23u64;let _=source_identity(&referenced);
let _=source_const_array::<u8,3>([1,2,3]);let _=source_const_array::<u16,5>([1,2,3,4,5]);
let _=source_typed_relay([1,2],[3u64,4,5]);let mut x=3u8;unsafe{source_store(&mut x,4);source_alias_store(&mut x,5);source_reassigned_pointer(&mut x,&mut x,6);source_reassigned_value(&mut x,7,8);let mut e=Flat::A(1);source_store(&mut e,Flat::B(2));}let _=source_ground::<u16>(1);let _=root::<u8,3>(1);let _=root::<u16,5>(2);let _=source_chain::<u8,3>(4);let _=source_diamond::<u8,3>(4);let _=source_array::<u8,3>([0;3]);let _=source_array::<u16,5>([0;5]);let _=source_pending_drop(NeedsGlue{value:1u8});}
