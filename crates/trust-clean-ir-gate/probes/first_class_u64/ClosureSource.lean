/- Original higher-order Lean program. No runtime or carrier annotation. -/
namespace ClosureSource

def makeAffine (a b : UInt64) : UInt64 -> UInt64 := fun x => a * x + b

def apply64 (f : UInt64 -> UInt64) (x : UInt64) : UInt64 := f x

def useAffine (a b x : UInt64) : UInt64 :=
  let f := makeAffine a b
  apply64 f x

end ClosureSource
