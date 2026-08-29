use std::collections::HashMap;
use std::hint::black_box;
use std::panic::catch_unwind;

#[inline(never)] pub fn vec_range_index_with_ensures(v: Vec<u32>, end: usize) -> u32 { let _s=&black_box(&v)[..end]; black_box(7) }
#[inline(never)] pub fn a1_min_div(a: u32, b: u32) -> u32 { black_box(a) / black_box(b).min(3) }
#[inline(never)] pub fn a2_min_sub(a: u32, b: u32) -> u32 { black_box(a).min(4) - black_box(b) }
#[inline(never)] pub fn a3_char_idx(s: &str, i: usize) -> u8 { black_box(s).as_bytes()[i] }
#[inline(never)] pub fn a7_max_mul(a: u32, b: u32) -> u32 { black_box(a).max(2) * black_box(b) }
#[inline(never)] pub fn e3_branch_div(a: u32, b: u32, c: bool) -> u32 { if black_box(c) { black_box(a)/black_box(b) } else { black_box(a)/(black_box(b)+1) } }
#[inline(never)] pub fn e5_straight_idx(v: Vec<u32>, i: usize) -> u32 { black_box(&v)[i] }
#[inline(never)] pub fn p1_vec_range_sum(v: Vec<u32>, end: usize) -> u32 { let s=&black_box(&v)[..end]; s.len() as u32 }
#[inline(never)] pub fn opaque_divisor(x: u32) -> u32 { black_box(x).wrapping_sub(1) }
#[inline(never)] pub fn p2_opaque_callee_div(a: u32, x: u32) -> u32 { black_box(a) / opaque_divisor(x) }
#[inline(never)] pub fn p3_map_index(m: HashMap<u32,u32>, k: u32) -> u32 { black_box(&m)[&black_box(k)] }
#[inline(never)] pub fn safe_div(a: u32, b: u32) -> u32 { black_box(a) / black_box(b) }
#[inline(never)] pub fn safe_add(a: u32, b: u32) -> u32 { black_box(a) + black_box(b) }

fn report(name: &str, panics: usize, total: usize, first: Option<String>) {
    println!("{name}: {panics}/{total} panicked first={first:?}");
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let smalls: Vec<u32> = vec![0,1,2,3,4,5,7,255,1000,65535,0x7fff_ffff,0xffff_ffff];

    // vec_range_index_with_ensures + p1
    for (name, f) in [("vec_range_index_with_ensures", vec_range_index_with_ensures as fn(Vec<u32>,usize)->u32), ("p1_vec_range_sum", p1_vec_range_sum)] {
        let (mut p, mut t, mut first) = (0,0,None);
        for len in 0usize..9 { for end in 0usize..12 {
            t+=1; let v: Vec<u32>=(0..len as u32).collect();
            if catch_unwind(move || f(v, end)).is_err() { p+=1; if first.is_none(){first=Some(format!("(len={len},end={end})"));} }
        }}
        report(name,p,t,first);
    }
    // e5_straight_idx
    { let (mut p,mut t,mut first)=(0,0,None);
      for len in 0usize..9 { for i in 0usize..12 { t+=1; let v:Vec<u32>=(0..len as u32).collect();
        if catch_unwind(move || e5_straight_idx(v,i)).is_err(){p+=1; if first.is_none(){first=Some(format!("(len={len},i={i})"));}} }}
      report("e5_straight_idx",p,t,first); }
    // a1,a2,a7,safe_div,safe_add over pairs
    for (name, f) in [("a1_min_div", a1_min_div as fn(u32,u32)->u32), ("a2_min_sub", a2_min_sub), ("a7_max_mul", a7_max_mul), ("safe_div", safe_div), ("safe_add", safe_add)] {
        let (mut p, mut t, mut first)=(0,0,None);
        for &a in &smalls { for &b in &smalls { t+=1;
            if catch_unwind(|| f(a,b)).is_err(){p+=1; if first.is_none(){first=Some(format!("(a={a},b={b})"));}} }}
        report(name,p,t,first);
    }
    // safe_div/safe_add under their DECLARED preconditions
    { let (mut p,mut t)=(0,0); for &a in &smalls { for &b in &smalls { if b==0 {continue;} t+=1;
        if catch_unwind(|| safe_div(a,b)).is_err(){p+=1;} }} println!("safe_div|requires b!=0: {p}/{t} panicked"); }
    { let (mut p,mut t)=(0,0); for a in 0u32..1000 { for b in 0u32..1000 { t+=1;
        if catch_unwind(|| safe_add(a,b)).is_err(){p+=1;} }} println!("safe_add|requires a<1000,b<1000: {p}/{t} panicked"); }
    // e3_branch_div
    { let (mut p,mut t,mut first)=(0,0,None);
      for &a in &smalls { for &b in &smalls { for c in [true,false] { t+=1;
        if catch_unwind(|| e3_branch_div(a,b,c)).is_err(){p+=1; if first.is_none(){first=Some(format!("(a={a},b={b},c={c})"));}} }}}
      report("e3_branch_div",p,t,first); }
    // a3_char_idx
    { let (mut p,mut t,mut first)=(0,0,None);
      for s in ["", "a", "abc", "hello world"] { for i in 0usize..14 { t+=1;
        if catch_unwind(|| a3_char_idx(s,i)).is_err(){p+=1; if first.is_none(){first=Some(format!("(s={s:?},i={i})"));}} }}
      report("a3_char_idx",p,t,first); }
    // p2
    { let (mut p,mut t,mut first)=(0,0,None);
      for &a in &smalls { for &x in &smalls { t+=1;
        if catch_unwind(|| p2_opaque_callee_div(a,x)).is_err(){p+=1; if first.is_none(){first=Some(format!("(a={a},x={x})"));}} }}
      report("p2_opaque_callee_div",p,t,first); }
    // p3
    { let (mut p,mut t,mut first)=(0,0,None);
      for nkeys in 0u32..4 { for k in 0u32..6 { t+=1;
        let m: HashMap<u32,u32> = (0..nkeys).map(|i|(i,i*10)).collect();
        if catch_unwind(move || p3_map_index(m,k)).is_err(){p+=1; if first.is_none(){first=Some(format!("(nkeys={nkeys},k={k})"));}} }}
      report("p3_map_index",p,t,first); }
}
