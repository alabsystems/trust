//@ probe-shape: Projection
//@ probe-expect: unproved
//@ probe-note: ITEM 10 PHASE 2, RED — a deferred island suffix must not launder a
//@ probe-note: theorem that does not exist ANYWHERE.
//@ probe-note:
//@ probe-note: The in-walk lane reads `TheoremNotFound` as "not checked yet" only
//@ probe-note: because a deferred suffix exists in this crate. That inference is a
//@ probe-note: scheduling hint, so the presence of ANY deferred island must not turn an
//@ probe-note: absent name into a pass. `absent_thm` is declared by nothing: the body is
//@ probe-note: quarantined in-walk, re-adjudicated post-walk against the complete
//@ probe-note: environment, still not found, and stays unproved — with the ordinary hard
//@ probe-note: "cited theorem is not registered" error from the citation sweep.
//@ probe-note:
//@ probe-note: `present_thm` exists only to give the crate a deferred suffix. It names
//@ probe-note: the kernel-import namespace, which is what triggers deferral, and it is a
//@ probe-note: bare reflexivity so it cannot be the thing under test.
clean {
    theorem present_thm : forall (a : UInt64),
        Eq (trust_import_probe__keep a) (trust_import_probe__keep a) :=
        fun a => rfl
}

pub fn keep(a: u64) -> u64 {
    a
}

pub fn caller(x: u64) -> u64
    ensures keep(x) <= x by absent_thm
{
    x
}
