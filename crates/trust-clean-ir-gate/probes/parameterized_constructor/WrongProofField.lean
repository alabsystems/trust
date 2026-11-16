/- Erasing a proof field does not authorize a constructor without its premise. -/
def wrong_proof_field (bound payload : Nat) (within : bound < payload) : Fin bound :=
  @Fin.mk bound payload within
