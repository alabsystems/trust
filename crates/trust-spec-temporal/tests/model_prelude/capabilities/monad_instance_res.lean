-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a Monad instance for a local Res, used through `do`; expected failure.

namespace Trust
namespace Model

inductive Fail where
  | overflow

inductive Res (α : Type) where
  | ok    : α → Res α
  | error : Fail → Res α

def Res.bind {α β : Type} (r : Res α) (f : α → Res β) : Res β :=
  @Res.rec α (fun _ => Res β) f (fun e => Res.error e) r

instance : Monad Res where
  pure := Res.ok
  bind := Res.bind

def addR (a b : Nat) : Res Nat := do
  let x ← Res.ok a
  let y ← Res.ok b
  pure (x + y)

def Res.getD (r : Res Nat) : Nat := @Res.rec Nat (fun _ => Nat) (fun v => v) (fun _ => 0) r

theorem res_door : Nat.beq (Res.getD (addR 3 4)) 7 = true := rfl

end Model
end Trust
