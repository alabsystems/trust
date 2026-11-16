def applyTwice (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f (f x)
def addK (k x : UInt64) : UInt64 := applyTwice (fun y => y + k) x
