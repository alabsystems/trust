-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- A model taken from a real program: aterm, a terminal whose supervisor
-- approves agent dialogs under a policy written in a config file. The policy
-- has ONE writer, the config watcher. This is the scalar model of that
-- protocol (aterm-spec `harness_policy_one_writer_model`, 85 reachable
-- states), as a `ScalarModel` an island can declare.
--
--   disk            the policy the file on disk writes (0: off, 1: on)
--   has_posted, last_posted   the watcher dedupe: what it last posted
--   queued, queued_val        one post in flight to the window
--   in_force        the policy the window runs
--   committed       a seamless successor drops every wake before its Commit
--   forget_pending  the Commit handler asks the watcher to forget its dedupe
--
-- Written with `Trust.Protocol`'s short names (the island imports it).
--
-- `Protocol 0` is the design. `Protocol 1` switches on the mutants: a second
-- writer (an admission that adopts its own policy, the design this replaced)
-- and a Commit that raises no forget. A model that takes a parameter is a
-- function, so only the applied constants below are checked.

namespace HarnessPolicy
open Trust.Protocol

-- another edit is allowed (no subtraction: the model language is over the naturals)
def editsLeft : Trust.Temporal.FiniteModel.ScalarExpr := v "edits" ⊞ n 1 ≼ k "MaxEdits"

def Protocol (buggy : Nat) : Trust.Temporal.FiniteModel.ScalarModel :=
  machine "HarnessPolicyOneWriter" [param "Buggy" buggy, param "MaxEdits" 3]
    [var "disk" 0, var "edits" 0, var "has_posted" 0, var "last_posted" 0, var "queued" 0,
     var "queued_val" 0, var "in_force" 1, var "committed" 0, var "forget_pending" 0]
    [act "WriteOff" (v "disk" ≐ n 1 ⋏ editsLeft) ["disk" ≔ n 0, "edits" ≔ v "edits" ⊞ n 1],
     act "WriteOn" (v "disk" ≐ n 0 ⋏ editsLeft) ["disk" ≔ n 1, "edits" ≔ v "edits" ⊞ n 1],
     act "Poll"
       (v "queued" ≐ n 0 ⋏
         (v "has_posted" ≐ n 0 ⋎ v "last_posted" ≻ v "disk" ⋎ v "disk" ≻ v "last_posted"))
       ["has_posted" ≔ n 1, "last_posted" ≔ v "disk", "queued" ≔ n 1, "queued_val" ≔ v "disk"],
     act "Deliver" (v "queued" ≐ n 1)
       ["in_force" ≔ cond (v "committed" ≐ n 1) (v "queued_val") (v "in_force"),
        "queued" ≔ n 0, "queued_val" ≔ n 0],
     act "AdmitOff" (v "committed" ≐ n 1) ["in_force" ≔ v "in_force"],
     act "AdmitOn" (v "committed" ≐ n 1) ["in_force" ≔ v "in_force"],
     act "Commit" (v "committed" ≐ n 0) ["committed" ≔ n 1, "forget_pending" ≔ n 1],
     act "Forget" (v "forget_pending" ≐ n 1) ["has_posted" ≔ n 0, "forget_pending" ≔ n 0],
     act "SecondWriterOff" (k "Buggy" ≐ n 1 ⋏ v "committed" ≐ n 1) ["in_force" ≔ n 0],
     act "SecondWriterOn" (k "Buggy" ≐ n 1 ⋏ v "committed" ≐ n 1) ["in_force" ≔ n 1],
     act "CommitWithoutForget" (k "Buggy" ≐ n 1 ⋏ v "committed" ≐ n 0) ["committed" ≔ n 1]]
    [inv "Agrees"
       (v "committed" ≐ n 0 ⋎ v "has_posted" ≐ n 0 ⋎ v "queued" ≐ n 1 ⋎
         v "forget_pending" ≐ n 1 ⋎ v "in_force" ≐ v "last_posted")]

def OneWriter : Trust.Temporal.FiniteModel.ScalarModel := Protocol 0

end HarnessPolicy
