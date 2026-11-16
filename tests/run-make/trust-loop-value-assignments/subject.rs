#![allow(dead_code, unused_variables, unused_assignments, unused_mut)]

struct Wrap { value: u32 }
struct Pair { first: u32, second: u32 }

pub fn direct() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _={ k+=1; k }; if n==3 { break k; } } }
pub fn tuple() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _=({ k+=1; k },); if n==3 { break k; } } }
pub fn array() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _=[{ k+=1; k }]; if n==3 { break k; } } }
pub fn repeat() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _=[{ k+=1; k }; 2]; if n==3 { break k; } } }
pub fn adt() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _=Wrap { value: { k+=1; k } }; if n==3 { break k; } } }
pub fn borrow() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _=&{ k+=1; 42 }; if n==3 { break k; } } }
pub fn deref() -> u32 { let mut n=0; let mut k=0; loop { n+=1; let _=*{ k+=1; &42 }; if n==3 { break k; } } }
pub fn iflet() -> u32 { let mut n=0; let mut k=0; loop { n+=1; if let Some(_) = Some({ k+=1; k }) {} if n==3 { break k; } } }
pub fn guarded_match() -> u32 { let mut n=0; let mut k=0; loop { n+=1; match 0u32 { 0 if { k+=1; true } => (), _ => () } if n==3 { break k; } } }

pub fn tuple_local() -> u32 {
    let mut n=0; let mut sum=0;
    loop { n+=1; let t=({let mut v=1;v+=1;v},);sum+=t.0;if n==3 {break sum;} }
}
pub fn array_predeclared_local() -> u32 {
    let mut n=0;let mut sum=0;
    loop {n+=1;let mut v=1;let a=[{v+=1;v}];sum+=a[0];if n==3 {break sum;} }
}
pub fn shadowed_names() -> u32 {
    let mut n=0;let mut k=0;
    loop {n+=1;let _=({k+=1;let mut k=3;k+=7;k},);if n==3 {break k;} }
}
pub fn nested_field_loop() -> u32 {
    let mut n=0;let mut k=0;
    loop {n+=1;let _=(loop {k+=1;break 0;},);if n==3 {break k;} }
}
pub fn fru_base_effect() -> u32 {
    let mut n=0;let mut k=0;
    loop {n+=1;let _=Pair {first:9,..{k+=1;Pair {first:1,second:2}}};if n==3 {break k;} }
}
pub fn field_effect_order() -> u32 {
    let mut n=0;let mut k=0;
    loop {n+=1;let _=({k+=1;k},{k*=2;k});if n==3 {break k;} }
}
pub fn repeat_evaluates_once() -> u32 {
    let mut n=0;let mut k=0;
    loop {n+=1;let _=[{k+=1;k};4];if n==3 {break k;} }
}
pub fn condition_tuple_field() -> u32 {
    let mut n=0;let mut k=0;
    loop {n+=1;if ({k+=1;true},).0 {} if n==3 {break k;} }
}
pub fn uninitialized_external_tuple() -> u32 {
    let mut k;let t=loop {break ({k=7;11},);};k+t.0
}
