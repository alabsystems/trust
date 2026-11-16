/- The type parameter remains exact; UInt64 payload is not a Nat field. -/
def wrong_type_parameter (index : Nat) (payload : UInt64) : OfNat Nat index :=
  @OfNat.mk UInt64 index payload
