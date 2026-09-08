//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-UI: a local with NO pre-split binding that EVERY reaching arm binds
// joins the if/match merge — the declared-uninit definite-initialization
// shape. Sound on rustc's own grounds: a DIVERGED arm contributes no join
// predecessor, so "bound in every reaching arm" is exactly "definitely
// initialized on every path that reaches the read", and the join arity is
// total by the same condition. A var only SOME reaching arms bind stays
// uncarried and its post-join reads keep failing closed (`VarRef(unbound)`
// — see `half` below).

// Two reaching arms, both assign: the value merges through a join param.
pub fn both(b: bool) -> i64 {
    let x: i64;
    if b {
        x = 5;
    } else {
        x = 9;
    }
    x
}

// One arm diverges: the single reaching arm's value carries alone
// (use-uninit-match2's `foo`, the match form).
pub enum Opt2<T> {
    N,
    S(T),
}
pub fn one_reaching<T>(o: Opt2<T>) -> isize {
    let x: isize;
    match o {
        Opt2::N => panic!(),
        Opt2::S(_t) => {
            x = 5;
        }
    }
    x
}

// There is NO valid-Rust negative for the some-arms-assign + read shape:
// rustc's own definite-initialization (E0381) rejects it at borrowck, which
// is exactly why the every-reaching-arm condition is sound — the producer's
// check is belt-and-braces against desugars, not a filter real programs can
// fail. An assignment that only some arms make is fine as long as nothing
// reads the var after the join; the merge then carries or skips it with no
// observable difference (nothing can name it).
pub fn assigned_unread(b: bool) {
    let x: i64;
    if b {
        x = 5;
        let _ = x;
    }
}
