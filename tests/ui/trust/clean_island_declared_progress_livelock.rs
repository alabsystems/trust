//@ compile-flags: -Z trust-verify=off
//! Temporal P2, the mutant twin of `clean_island_declared_progress_proved.rs`:
//! over `Protocol 1` (a second writer, and a Commit that raises no forget) a
//! fair run leaves the goal for good. The untrusted search finds the lasso and
//! the KERNEL confirms it: it replays the stem and the loop and evaluates the
//! goal and every fairness condition on the loop. The BUILD FAILS with the run.

clean {
    import Trust.FiniteModelCheck
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
    -- `Protocol 0` is the design. `Protocol 1` switches on the mutants: a second
    -- writer (an admission that adopts its own policy, the design this replaced)
    -- and a Commit that raises no forget. A model that takes a parameter is a
    -- function, so only the applied constants below are checked.

    namespace HarnessPolicy

    def v (name : String) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.var name
    def n (value : Nat) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.int value
    def c (name : String) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.constRef name
    def is (a b : Trust.Temporal.FiniteModel.ScalarExpr) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.eq a b
    def both (a b : Trust.Temporal.FiniteModel.ScalarExpr) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.and a b
    def either (a b : Trust.Temporal.FiniteModel.ScalarExpr) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.or a b
    def above (a b : Trust.Temporal.FiniteModel.ScalarExpr) : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.gt a b
    def set (name : String) (value : Trust.Temporal.FiniteModel.ScalarExpr) :
        Trust.Temporal.FiniteModel.Update :=
      Trust.Temporal.FiniteModel.Update.mk name value
    def act (name : String) (guard : Trust.Temporal.FiniteModel.ScalarExpr)
        (updates : List Trust.Temporal.FiniteModel.Update) : Trust.Temporal.FiniteModel.Action :=
      Trust.Temporal.FiniteModel.Action.mk name (Trust.Temporal.FiniteModel.Guard.when guard) updates

    def editsLeft : Trust.Temporal.FiniteModel.ScalarExpr :=
      Trust.Temporal.FiniteModel.ScalarExpr.le (v "edits")
        (Trust.Temporal.FiniteModel.ScalarExpr.sub (c "MaxEdits") (n 1))

    def Protocol (buggy : Nat) : Trust.Temporal.FiniteModel.ScalarModel :=
      Trust.Temporal.FiniteModel.ScalarModel.mk "HarnessPolicyOneWriter"
        [Trust.Temporal.FiniteModel.Constant.mk "Buggy" buggy,
         Trust.Temporal.FiniteModel.Constant.mk "MaxEdits" 3]
        [Trust.Temporal.FiniteModel.StateVar.mk "disk" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "edits" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "has_posted" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "last_posted" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "queued" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "queued_val" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "in_force" 1,
         Trust.Temporal.FiniteModel.StateVar.mk "committed" 0,
         Trust.Temporal.FiniteModel.StateVar.mk "forget_pending" 0]
        [act "WriteOff" (both (is (v "disk") (n 1)) editsLeft)
           [set "disk" (n 0),
            set "edits" (Trust.Temporal.FiniteModel.ScalarExpr.add (v "edits") (n 1))],
         act "WriteOn" (both (is (v "disk") (n 0)) editsLeft)
           [set "disk" (n 1),
            set "edits" (Trust.Temporal.FiniteModel.ScalarExpr.add (v "edits") (n 1))],
         act "Poll"
           (both (is (v "queued") (n 0))
             (either (is (v "has_posted") (n 0))
               (either (above (v "last_posted") (v "disk")) (above (v "disk") (v "last_posted")))))
           [set "has_posted" (n 1), set "last_posted" (v "disk"),
            set "queued" (n 1), set "queued_val" (v "disk")],
         act "Deliver" (is (v "queued") (n 1))
           [set "in_force"
              (Trust.Temporal.FiniteModel.ScalarExpr.ite (is (v "committed") (n 1))
                (v "queued_val") (v "in_force")),
            set "queued" (n 0), set "queued_val" (n 0)],
         act "AdmitOff" (is (v "committed") (n 1)) [set "in_force" (v "in_force")],
         act "AdmitOn" (is (v "committed") (n 1)) [set "in_force" (v "in_force")],
         act "Commit" (is (v "committed") (n 0))
           [set "committed" (n 1), set "forget_pending" (n 1)],
         act "Forget" (is (v "forget_pending") (n 1))
           [set "has_posted" (n 0), set "forget_pending" (n 0)],
         act "SecondWriterOff" (both (is (c "Buggy") (n 1)) (is (v "committed") (n 1)))
           [set "in_force" (n 0)],
         act "SecondWriterOn" (both (is (c "Buggy") (n 1)) (is (v "committed") (n 1)))
           [set "in_force" (n 1)],
         act "CommitWithoutForget" (both (is (c "Buggy") (n 1)) (is (v "committed") (n 0)))
           [set "committed" (n 1)]]
        [Trust.Temporal.FiniteModel.Invariant.mk "Agrees"
           (either (is (v "committed") (n 0))
             (either (is (v "has_posted") (n 0))
               (either (is (v "queued") (n 1))
                 (either (is (v "forget_pending") (n 1))
                   (is (v "in_force") (v "last_posted"))))))]

    def OneWriter : Trust.Temporal.FiniteModel.ScalarModel := Protocol 0

    end HarnessPolicy

    def HarnessPolicy.MutantCatchesUp : Trust.Temporal.FiniteModel.ScalarProgress :=
      Trust.Temporal.FiniteModel.ScalarProgress.mk (HarnessPolicy.Protocol 1)
        (HarnessPolicy.either (HarnessPolicy.is (HarnessPolicy.v "committed") (HarnessPolicy.n 0))
          (HarnessPolicy.is (HarnessPolicy.v "in_force") (HarnessPolicy.v "disk")))
        ["Poll", "Deliver", "Forget"] []
}
//~^^^^^^ ERROR progress claim `HarnessPolicy.MutantCatchesUp` fails

fn main() {}
