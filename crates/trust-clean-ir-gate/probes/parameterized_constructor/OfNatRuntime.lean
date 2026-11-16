/- Real source case: kernel-valid, still outside runtime/carrier admission. -/
def ofNatPayload (index : Nat) (payload : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 index (@OfNat.mk UInt64 index payload)
