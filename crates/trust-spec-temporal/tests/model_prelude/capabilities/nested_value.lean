-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- Value nested through List and Prod (design 10:71-107, note 10:170); required pass.

namespace Trust
namespace Model

inductive InfKind where
  | nat | int | string | seqOf | fnSet

-- Design 10:71-107: nested through List and Prod.
inductive Value where
  | bool   : Bool → Value
  | int    : Int → Value
  | str    : Nat → Value
  | mv     : Nat → Value
  | tmv    : Nat → Nat → Value
  | set    : List Value → Value
  | fn     : List (Value × Value) → Value
  | infSet : InfKind → List Value → Value

-- A nested inductive's casesOn (and rec) takes one motive per type of the block:
-- Value, List Value, List (Value × Value), Value × Value, then a minor premise for
-- every constructor of each of them.
def Value.sizeF (fuel : Nat) : Value → Nat :=
  @Nat.rec (fun _ => Value → Nat) (fun _ => 0)
    (fun _ go v => @Value.casesOn (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) v
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
      (fun xs => @List.rec Value (fun _ => Nat) 1 (fun x _ acc => go x + acc) xs)
      (fun ps => @List.rec (Prod Value Value) (fun _ => Nat) 1
        (fun p _ acc => go p.1 + go p.2 + acc) ps)
      (fun _ xs => @List.rec Value (fun _ => Nat) 1 (fun x _ acc => go x + acc) xs)
      0 (fun _ _ => 0) 0 (fun _ _ => 0) (fun _ _ => 0))
    fuel

-- The same dispatch through `match` (one motive).
def Value.isSet (v : Value) : Bool :=
  match v with
  | .set _ => true
  | _ => false

def v1 : Value :=
  Value.set [Value.int 3, Value.int (-2), Value.fn [(Value.bool true, Value.str 4)]]

theorem nested_value_door : Nat.beq (Value.sizeF 10 v1) 6 = true := rfl
theorem nested_value_match : Value.isSet v1 = true := rfl

end Model
end Trust
