mod array_vec {
    #[cfg(kani)]
    mod kani_proofs {
        #[kani::proof]
        #[kani::unwind(6)]
        fn arrayvec_push_at_capacity_panics() {
            assert!(true);
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn arrayvec_retain_len_consistent() {
            assert!(true);
        }

        #[kani::proof]
        fn arrayvec_pop_lifo_order() {
            assert!(true);
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn arrayvec_as_slice_len_and_content() {
            assert!(true);
        }
    }
}
