use template_type_transport_source::*;
pub fn concrete_u8(_: &(),x:Packet<u8>,_:[u8;3],_:(u8,u8),_:Pair<u8>){let _=x;}
pub fn concrete_u16(_: &(),x:Packet<u16>,_:[u16;5],_:(u8,u16),_:Pair<u16>){let _=x;}
fn main(){host_owner::<*const u8,7>(3);host_owner::<u8,3>(1);host_owner::<u16,5>(2);let p8=Packet{prefix:1,inner:Inner{tag:2,value:3u8,zst:core::marker::PhantomData},tail:[4,5]};let p16=Packet{prefix:1,inner:Inner{tag:2,value:3u16,zst:core::marker::PhantomData},tail:[4,5]};owner::<u8,3>(&(),p8,[1;3],(1,2),Pair{first:1,second:2});owner::<u16,5>(&(),p16,[1;5],(1,2),Pair{first:1,second:2});}
