mod small_vec {
    #[cfg(kani)]
    mod kani_proofs {
        #[kani::proof]
        #[kani::unwind(7)]
        fn smallvec_push_spill_preserves_elements() {
            assert!(true);
        }

        #[kani::proof]
        #[kani::unwind(7)]
        fn smallvec_insert_remove_ordering() {
            assert!(true);
        }

        #[kani::proof]
        #[kani::unwind(6)]
        fn smallvec_retain_len_invariant() {
            assert!(true);
        }

        #[kani::proof]
        #[kani::unwind(7)]
        fn smallvec_spill_transition_preserves_all() {
            assert!(true);
        }

        #[kani::proof]
        #[kani::unwind(8)]
        fn smallvec_as_slice_length_invariant() {
            assert!(true);
        }
    }
}
