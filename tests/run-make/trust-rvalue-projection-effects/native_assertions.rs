fn main() {
match std::env::args().nth(1).as_deref() {
 Some("hidden-drop") => {hidden_drop();return;},
 Some("hidden-drop-copy") => {hidden_drop_copy();return;},
 Some("borrowed-drop") => {borrowed_drop_temporary();return;},
 Some("borrowed-drop-copy") => {borrowed_drop_copy();return;},
 Some("if-overflow") => {if_overflow();return;},
 Some("match-overflow") => {match_overflow();return;},
 Some("loop-overflow") => {loop_overflow();return;},
 Some("call-overflow") => {call_overflow();return;},
 Some("index-overflow") => {index_conditionally_returns(false);return;},
 _ => {}
}
assert_eq!(union_write(),7);assert_eq!(union_copy_write(),7);
assert_eq!(nested_reference_compound(),4);assert_eq!(copied_deref_block(),1);assert_eq!(copied_deref_value(),1);
assert_eq!(rhs_returns(),7);assert_eq!(base_returns(),7);assert_eq!(index_returns(),7);
assert_eq!(read_index_returns(),7);assert_eq!(index_conditionally_returns(true),7);
assert_eq!(mixed_branch_returns(true),7);assert_eq!(mixed_branch_returns(false),1);
assert_eq!(literal_array_order(),123);
}
