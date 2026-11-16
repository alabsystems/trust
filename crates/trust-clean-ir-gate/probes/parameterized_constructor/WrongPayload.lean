/- Replacing the constructor field with another runtime argument must refuse. -/
theorem wrong_payload (index : Nat) (payload other : UInt64) :
    @OfNat.ofNat UInt64 index (@OfNat.mk UInt64 index other) = payload := by rfl
