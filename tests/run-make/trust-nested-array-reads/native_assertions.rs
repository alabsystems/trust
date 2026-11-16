fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("outer-oob")=>{nested_dynamic(99,0);return;}
        Some("inner-oob")=>{nested_dynamic(0,17);return;}
        Some("slice-oob")=>{empty_slice();return;}
        Some("unit-outer-oob")=>{nested_unit(2,0);return;}
        Some("unit-inner-oob")=>{nested_unit(0,2);return;}
        Some("empty-outer")=>{empty_rows(2);return;}
        Some("empty-inner")=>{empty_inner(0);return;}
        Some("large-outer")=>{large_zst_row(2);return;}
        Some("zst-slice-outer")=>{zst_slice_values(2,0);return;}
        Some("zst-slice-inner")=>{zst_slice_values(0,2);return;}
        Some("zero-len-outer")=>{zero_len_values(2);return;}
        Some("direct-adt-oob")=>{direct_adt(2);return;}
        Some("direct-adt-slice-oob")=>{direct_adt_slice(2);return;}
        Some("drop")=>{drop_leaf_refused();return;}
        _=>{}
    }
    assert_eq!(nested_const(),3);
    assert_eq!(nested_adt_refused(),13);
    for (i, value) in [(0,13),(1,29)] {
        assert_eq!(direct_adt(i),value);
        assert_eq!(direct_adt_slice(i),value);
    }
    assert_eq!(nested_index_returns(),7);
    assert_eq!(nested_base_returns(),7);
    assert_eq!(pointer_leaf_refused(),3);
    assert_eq!(generic_length([[1u32,2]]),1);
    assert_eq!(nested_char(0),'a' as u32);
    assert_eq!(nested_char(1),'🙂' as u32);
    for i in 0..2 {
        assert_eq!(nested_row(i),[[1,2],[3,4]][i]);
        assert_eq!(empty_rows(i),0);
        assert_eq!(zero_len_values(i),0);
        for j in 0..3 {
            assert_eq!(rectangular(i,j),1+(3*i+j) as u32);
            assert_eq!(rectangular_slice(i,j),1+(3*i+j) as u32);
        }
        assert_eq!(large_zst_row(i),1_048_576);
        for j in 0..2 {
            let value=1+(2*i+j) as u32;
            assert_eq!(nested_dynamic(i,j),value);
            assert_eq!(nested_param([[1,2],[3,4]],i,j),value);
            assert_eq!(nested_slice(&[[1,2],[3,4]],i,j),value);
            assert_eq!(nested_unit(i,j),7);
            assert_eq!(zst_slice_values(i,j),7);
            // Valid zero-sized slices need alignment and a non-null pointer,
            // but no backing allocation; mirror this input in the IR test.
            let zst = unsafe { std::slice::from_raw_parts(
                std::ptr::NonNull::<[();2]>::dangling().as_ptr(),2) };
            assert_eq!(zst_slice_rows(zst,i,j),7);
            let empty_rows = unsafe { std::slice::from_raw_parts(
                std::ptr::NonNull::<[u32;0]>::dangling().as_ptr(),2) };
            assert_eq!(zero_len_slice(empty_rows,i),0);
            assert_eq!(copied_row(i,j),value);
            assert_eq!(changed_place(i,j),value+4);
            assert_eq!(captured_value(i,j),value);
            assert_eq!(changed_slice(i,j),value+4);
            assert_eq!(captured_slice(i,j),value);
            assert_eq!(reference_row(&[[1,2],[3,4]],i,j),value);
            assert_eq!(param_values(i,j),value);
            assert_eq!(slice_values(i,j),value);
            assert_eq!(reference_values(i,j),value);
            assert_eq!(row_value(i,j),value);
            assert_eq!(nested_float(i,j),value);
            assert_eq!(nested_double(i,j),value);
            assert_eq!(nested_bool(i,j),u32::from(i!=j));
            for k in 0..2 { assert_eq!(deep(i,j,k),1+(4*i+2*j+k) as u32); }
        }
    }
}
