class Scale (α : Type) where
  scale : α → α

instance instScaleU64 : Scale UInt64 where
  scale := fun (x : UInt64) => x * 3

def triple (x : UInt64) : UInt64 := @Scale.scale UInt64 instScaleU64 x
