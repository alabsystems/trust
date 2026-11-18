mod fields;

fn main() {
    let tuples = [(String::from("first"), 1), (String::from("second"), 2)];
    let fields = [fields::SliceField { name: String::from("field"), sort: 3 }];
    assert_eq!(fields::direct_tuple_slice_len(&tuples), 2);
    assert_eq!(fields::direct_field_slice_len(&fields), 1);
    // Valid Rust still executes through the ordinary retained route. This does
    // not assert faithful native proof support for opaque enum payloads.
    assert_eq!(fields::slice_payload_len(fields::SlicePayload::Tuples(&tuples)), 2);
    assert_eq!(fields::slice_payload_len(fields::SlicePayload::Datatype(&fields)), 1);
}
