namespace ErasedDictionary

def makeLeft (a : UInt64) : UInt64 -> UInt64 :=
  fun x => @HAdd.hAdd UInt64 UInt64 UInt64
    (@HAdd.mk UInt64 UInt64 UInt64 (fun left right => left)) a x

def applyLeft (f : UInt64 -> UInt64) (x : UInt64) : UInt64 := f x

def useLeft (a x : UInt64) : UInt64 :=
  let f := makeLeft a
  applyLeft f x

end ErasedDictionary
