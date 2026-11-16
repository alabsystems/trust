#![allow(unreachable_code, unused_assignments, unused_variables, unconditional_panic, arithmetic_overflow)]
#[derive(Clone, Copy)] pub struct Pair { pub x:u32, pub y:u32 }
pub union U { pub byte:u8, pub flag:bool }
pub fn union_write()->u32 { (U{byte:2}).flag=true; 7 }
pub fn union_copy_write()->u32 { (U{byte:2} as U).flag=true; 7 }
pub struct Bomb;
impl Drop for Bomb { fn drop(&mut self) { panic!("drop ran"); } }
pub fn hidden_drop()->u32 { ({let _bomb=Bomb; Pair{x:1,y:2}}).x=4; 7 }
pub fn hidden_drop_copy()->u32 { ({let _bomb=Bomb; Pair{x:1,y:2}} as Pair).x=4; 7 }
pub struct Borrowed<'a> { pub p:&'a Bomb, pub x:u32 }
pub fn borrowed_drop_temporary()->u32 { (Borrowed{p:&Bomb,x:1}).x=4; 7 }
pub fn borrowed_drop_copy()->u32 { (Borrowed{p:&Bomb,x:1} as Borrowed<'_>).x=4; 7 }
pub struct Link<'a> { pub p:&'a mut Pair }
pub fn nested_reference_compound()->u32 { let mut p=Pair{x:1,y:2}; (Link{p:&mut p}).p.x+=3; p.x }
pub fn copied_deref_block()->u32 { let mut p=Pair{x:1,y:2};let r=&mut p;({*r}).x+=3;p.x }
pub fn copied_deref_value()->u32 { let mut p=Pair{x:1,y:2};let r=&mut p;(*r as Pair).x+=3;p.x }
pub fn rhs_returns()->u32 { [0u32;1][1]={return 7}; 9 }
pub fn base_returns()->u32 { (if true {return 7} else {[0u32;1]})[1]=4; 9 }
pub fn index_returns()->u32 { [u32::MAX][{return 7; 0usize}]+=1; 9 }
pub fn read_index_returns()->u32 { let a=[u32::MAX]; a[{return 7; 0usize}]; 9 }
pub fn index_conditionally_returns(flag:bool)->u32 { [u32::MAX][if flag {return 7} else {0usize}]+=1; 9 }
pub fn mixed_branch_returns(flag:bool)->u32 { (if flag {return 7} else {Pair{x:1,y:2}}).x+=3; 1 }
pub fn if_overflow()->u32 { (if true {Pair{x:u32::MAX,y:0}} else {Pair{x:1,y:0}}).x+=1; 9 }
pub fn match_overflow()->u32 { (match 1 {0=>Pair{x:1,y:0},_=>Pair{x:u32::MAX,y:0}}).x+=1; 9 }
pub fn loop_overflow()->u32 { (loop {break Pair{x:u32::MAX,y:0}}).x+=1; 9 }
pub fn make_max()->Pair { Pair{x:u32::MAX,y:0} }
pub fn call_overflow()->u32 { make_max().x+=1; 9 }
pub fn literal_array_order()->u32 { let mut n=0;[{n=n*10+2;1u32},2][{n=n*10+3;0}]={n=n*10+1;4};n }
