/- A payload theorem does not permit changing the original dependent result. -/
def wrong_result_index (first second : Nat) (payload : UInt64) : OfNat UInt64 first :=
  @OfNat.mk UInt64 second payload
