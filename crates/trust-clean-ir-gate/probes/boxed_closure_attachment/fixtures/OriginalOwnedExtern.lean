/- Complete source input for closure-conversion proposals.  These definitions
   carry no compiler annotations, runtime names, or representation assumptions. -/
namespace EscapingOriginal

def makeAffine (a b : UInt64) : UInt64 -> UInt64 := fun x => a * x + b

def apply64 (f : UInt64 -> UInt64) (x : UInt64) : UInt64 := f x

def useAffine (a b x : UInt64) : UInt64 :=
  let f := makeAffine a b
  apply64 f x

end EscapingOriginal

@[extern "unowned_probe_identity"]
def ownedForeign (x : UInt64) : UInt64 := x
