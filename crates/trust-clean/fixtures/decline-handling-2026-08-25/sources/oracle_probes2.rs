use std::collections::BTreeMap;
use std::hint::black_box;
use std::panic::catch_unwind;

#[inline(never)] pub fn q1_str_range(s: &str, i: usize) -> usize { let t=&black_box(s)[i..]; t.len() }
#[inline(never)] pub fn q2_btree_index(m: BTreeMap<u32,u32>, k: u32) -> u32 { black_box(&m)[&black_box(k)] }
#[inline(never)] pub fn q3_vec_range2(v: Vec<u8>, a: usize, b: usize) -> usize { let s=&black_box(&v)[a..b]; s.len() }
#[inline(never)] pub fn q4_string_range(s: String, end: usize) -> usize { let t=&black_box(&s)[..end]; t.len() }
#[inline(never)] pub fn q5_dyn_range(v: Vec<u8>, f: &dyn Fn()->usize) -> usize { let s=&black_box(&v)[..f()]; s.len() }
#[inline(never)] pub fn q6_vec_range_ensures(v: Vec<u8>, end: usize) -> u32 { let _s=&black_box(&v)[..end]; black_box(3) }
#[inline(never)] pub fn q7_boxslice_range(v: Box<[u8]>, end: usize) -> usize { let s=&black_box(&v)[..end]; s.len() }

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    { let (mut p,mut t,mut f)=(0,0,None);
      for s in ["", "a", "abc", "héllo"] { for i in 0usize..8 { t+=1;
        if catch_unwind(|| q1_str_range(s,i)).is_err(){p+=1; if f.is_none(){f=Some(format!("(s={s:?},i={i})"));}} }}
      println!("q1_str_range: {p}/{t} first={f:?}"); }
    { let (mut p,mut t,mut f)=(0,0,None);
      for n in 0u32..4 { for k in 0u32..6 { t+=1; let m: BTreeMap<u32,u32>=(0..n).map(|i|(i,i)).collect();
        if catch_unwind(move || q2_btree_index(m,k)).is_err(){p+=1; if f.is_none(){f=Some(format!("(n={n},k={k})"));}} }}
      println!("q2_btree_index: {p}/{t} first={f:?}"); }
    { let (mut p,mut t,mut f)=(0,0,None);
      for len in 0usize..6 { for a in 0usize..8 { for b in 0usize..8 { t+=1; let v: Vec<u8>=vec![0;len];
        if catch_unwind(move || q3_vec_range2(v,a,b)).is_err(){p+=1; if f.is_none(){f=Some(format!("(len={len},a={a},b={b})"));}} }}}
      println!("q3_vec_range2: {p}/{t} first={f:?}"); }
    { let (mut p,mut t,mut f)=(0,0,None);
      for len in 0usize..6 { for e in 0usize..8 { t+=1; let s: String = "a".repeat(len);
        if catch_unwind(move || q4_string_range(s,e)).is_err(){p+=1; if f.is_none(){f=Some(format!("(len={len},end={e})"));}} }}
      println!("q4_string_range: {p}/{t} first={f:?}"); }
    { let (mut p,mut t,mut f)=(0,0,None);
      for len in 0usize..6 { for e in 0usize..8 { t+=1; let v: Vec<u8>=vec![0;len]; let g=move||e;
        if catch_unwind(move || q5_dyn_range(v,&g)).is_err(){p+=1; if f.is_none(){f=Some(format!("(len={len},e={e})"));}} }}
      println!("q5_dyn_range: {p}/{t} first={f:?}"); }
    { let (mut p,mut t,mut f)=(0,0,None);
      for len in 0usize..6 { for e in 0usize..8 { t+=1; let v: Vec<u8>=vec![0;len];
        if catch_unwind(move || q6_vec_range_ensures(v,e)).is_err(){p+=1; if f.is_none(){f=Some(format!("(len={len},end={e})"));}} }}
      println!("q6_vec_range_ensures: {p}/{t} first={f:?}"); }
    { let (mut p,mut t,mut f)=(0,0,None);
      for len in 0usize..6 { for e in 0usize..8 { t+=1; let v: Box<[u8]> = vec![0u8;len].into_boxed_slice();
        if catch_unwind(move || q7_boxslice_range(v,e)).is_err(){p+=1; if f.is_none(){f=Some(format!("(len={len},end={e})"));}} }}
      println!("q7_boxslice_range: {p}/{t} first={f:?}"); }
}
