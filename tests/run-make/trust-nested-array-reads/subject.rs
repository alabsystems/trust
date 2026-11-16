#![allow(unreachable_code, unused_must_use, unused_assignments, unconditional_panic)]
pub fn nested_const() -> u32 { [[1u32, 2], [3, 4]][1][0] }
pub fn nested_dynamic(i: usize, j: usize) -> u32 { [[1u32, 2], [3, 4]][i][j] }
pub fn nested_row(i: usize) -> [u32; 2] { [[1u32, 2], [3, 4]][i] }
pub fn nested_param(a: [[u32; 2]; 2], i: usize, j: usize) -> u32 { a[i][j] }
pub fn nested_slice(a: &[[u32; 2]], i: usize, j: usize) -> u32 { a[i][j] }
pub fn nested_index_returns() -> u32 { [[1u32, 2]][{ return 7; 0usize }]; 9 }
pub fn nested_base_returns() -> u32 { ({ return 7; [[1u32, 2]] })[0]; 9 }
pub fn nested_unit(i: usize, j: usize) -> u32 { [[(); 2]; 2][i][j]; 7 }

pub fn copied_row(i: usize, j: usize) -> u32 {
    let a=[[1u32,2],[3,4]];
    let mut row=a[i]; row[j]=99;
    a[i][j]
}
pub fn changed_place(i: usize, j: usize) -> u32 {
    let mut a=[[1u32,2],[3,4]];
    a[{a=[[5,6],[7,8]];i}][j]
}
pub fn captured_value(i: usize, j: usize) -> u32 {
    let mut a=[[1u32,2],[3,4]];
    ({a})[{a=[[5,6],[7,8]];i}][j]
}
pub fn changed_slice(i: usize, j: usize) -> u32 {
    let a=[[1u32,2],[3,4]];let b=[[5u32,6],[7,8]];
    let mut s:&[[u32;2]]=&a;
    s[{s=&b;i}][j]
}
pub fn captured_slice(i: usize, j: usize) -> u32 {
    let a=[[1u32,2],[3,4]];let b=[[5u32,6],[7,8]];
    let mut s:&[[u32;2]]=&a;
    (s as &[[u32;2]])[{s=&b;i}][j]
}
pub fn reference_row(a:&[[u32;2];2], i:usize, j:usize)->u32 { a[i][j] }
pub fn pointer_leaf_refused() -> u32 { let x=3u32; let a=[[&x]]; *a[0][0] }
pub fn generic_length<const N:usize>(a:[[u32;N];1])->u32 { a[0][0] }
pub struct Bomb { pub value:u32 }
impl Drop for Bomb { fn drop(&mut self) { panic!("drop ran"); } }
pub fn drop_leaf_refused()->u32 { [ [Bomb{value:3}] ][0][0].value }
pub fn empty_rows(i:usize)->u32 { let a:[[u32;0];2]=[[],[]]; let row=a[i]; row.len() as u32 }
pub fn empty_inner(i:usize)->u32 { let a:[[u32;0];2]=[[],[]]; a[i][0] }
pub fn large_zst_row(i:usize)->u32 { let a=[[();1_048_576];2]; let row=a[i]; row.len() as u32 }

pub fn param_values(i:usize,j:usize)->u32 { nested_param([[1,2],[3,4]],i,j) }
pub fn slice_values(i:usize,j:usize)->u32 { nested_slice(&[[1,2],[3,4]],i,j) }
pub fn reference_values(i:usize,j:usize)->u32 { reference_row(&[[1,2],[3,4]],i,j) }
pub fn row_value(i:usize,j:usize)->u32 { nested_row(i)[j] }
pub fn nested_float(i:usize,j:usize)->u32 { [[1.0f32,2.0],[3.0,4.0]][i][j] as u32 }
pub fn nested_double(i:usize,j:usize)->u32 { [[1.0f64,2.0],[3.0,4.0]][i][j] as u32 }
pub fn nested_char(i:usize)->u32 { [['a','β'],['🙂','z']][i][0] as u32 }
pub fn nested_bool(i:usize,j:usize)->u32 { if [[false,true],[true,false]][i][j] {1}else{0} }
pub fn deep(i:usize,j:usize,k:usize)->u32 { [[[1u32,2],[3,4]],[[5,6],[7,8]]][i][j][k] }

pub fn empty_slice()->u32 { nested_slice(&[],0,0) }

pub fn rectangular(i:usize,j:usize)->u32 { [[1u32,2,3],[4,5,6]][i][j] }
pub fn rectangular_slice(i:usize,j:usize)->u32 {
    let a=[[1u32,2,3],[4,5,6]]; let s:&[[u32;3]]=&a; s[i][j]
}
pub fn zst_slice_rows(s:&[[();2]],i:usize,j:usize)->u32 { s[i][j]; 7 }
pub fn zst_slice_values(i:usize,j:usize)->u32 { zst_slice_rows(&[[();2];2],i,j) }
pub fn zero_len_slice(s:&[[u32;0]],i:usize)->u32 { let row=s[i]; row.len() as u32 }
pub fn zero_len_values(i:usize)->u32 { zero_len_slice(&[[],[]],i) }

#[derive(Clone, Copy)]
pub struct Plain { pub tag: u8, pub value: u32 }
pub fn direct_adt(i: usize) -> u32 {
    [Plain { tag: 1, value: 13 }, Plain { tag: 2, value: 29 }][i].value
}
pub fn direct_adt_slice(i: usize) -> u32 {
    let a = [Plain { tag: 1, value: 13 }, Plain { tag: 2, value: 29 }];
    let s: &[Plain] = &a;
    s[i].value
}
pub fn nested_adt_refused() -> u32 { [[Plain { tag: 1, value: 13 }]][0][0].value }
