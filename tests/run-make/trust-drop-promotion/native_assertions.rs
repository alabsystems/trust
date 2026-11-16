fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("literal") => {
            literal_temp();
        }
        Some("named") => {
            named_temp();
        }
        Some("array") => {
            array_temp();
        }
        Some("projected") => {
            projected_temp();
        }
        Some("tuple") => {
            tuple_temp();
        }
        Some("projected-runtime") => {
            projected_runtime(7);
        }
        Some("scalar-runtime") => {
            scalar_runtime(7);
        }
        Some("struct-runtime") => {
            struct_runtime(7);
        }
        Some("nested-runtime") => {
            nested_runtime(7);
        }
        Some("scoped-runtime") => {
            scoped_runtime(7);
        }
        Some("call-runtime") => {
            call_runtime(7);
        }
        _ => {
            assert_eq!(safe_literal(), 7);
            assert_eq!(safe_tuple(), 7);
        }
    }
}
