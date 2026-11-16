/- The literal index is not the constructor's stored Nat payload. Must refuse. -/
theorem wrong_index_payload (index payload : Nat) :
    @OfNat.ofNat Nat index (@OfNat.mk Nat index payload) = index := by rfl
