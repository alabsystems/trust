def dbl (a : UInt64) : UInt64 := a + a
theorem dbl_wrong (a : UInt64) : dbl a = a := rfl
