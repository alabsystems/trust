-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- the B1A-D07 block: Nat.rec over fuel, a non-recursive step taking `go`, eta-expanded List.rec with its major premise, fuel 100000 by rfl; required pass.

namespace Trust
namespace Model

inductive Fail where
  | overflow | fuel

inductive Res (α : Type) where
  | ok    : α → Res α
  | error : Fail → Res α

inductive Job where
  | sum : List Nat → Job
  | dbl : Nat → Job

inductive Out where
  | nat  : Nat → Out
  | none : Out

def Out.get (o : Out) : Nat := @Out.casesOn (fun _ => Nat) o (fun n => n) 0

def Tlc.stepL (go : Job → Res Out) (l : List Nat) : Res Out :=
  @List.rec Nat (fun _ => Res Out) (Res.ok (Out.nat 0))
    (fun h _ acc => @Res.rec Out (fun _ => Res Out)
      (fun a => @Res.rec Out (fun _ => Res Out)
        (fun b => Res.ok (Out.nat (Out.get a + Out.get b))) (fun f => Res.error f) (go (Job.dbl h)))
      (fun f => Res.error f) acc) l

def Tlc.step (go : Job → Res Out) (j : Job) : Res Out :=
  @Job.rec (fun _ => Res Out) (fun l => Tlc.stepL go l) (fun n => Res.ok (Out.nat (n + n))) j

def Tlc.run (n : Nat) : Job → Res Out :=
  @Nat.rec (fun _ => Job → Res Out) (fun _ => Res.error Fail.fuel) (fun _ go => Tlc.step go) n

def Res.isOkNat (r : Res Out) (k : Nat) : Bool :=
  @Res.rec Out (fun _ => Bool) (fun o => Nat.beq (Out.get o) k) (fun _ => false) r

def Res.isFuel (r : Res Out) : Bool :=
  @Res.rec Out (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.rec (fun _ => Bool) false true f) r

theorem fuel_block_sum : Res.isOkNat (Tlc.run 5 (Job.sum [1, 2, 3])) 12 = true := rfl
theorem fuel_block_out_of_fuel : Res.isFuel (Tlc.run 1 (Job.sum [1])) = true := rfl
theorem fuel_block_100000 : Res.isOkNat (Tlc.run 100000 (Job.sum [1])) 2 = true := rfl

end Model
end Trust
