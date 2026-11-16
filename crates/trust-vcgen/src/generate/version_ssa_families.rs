//! Generated CFG families for the statement-version oracle's parity and scaling tests.
//!
//! Each builder returns a `VerifiableFunction` in the exact shape the compiler's
//! extraction produces (built through its serde form, so every field defaults the
//! way a dumped body does), parameterised by size:
//!
//!  * [`locals_chain`] — `tests/ui/borrowck/ever-init-many-locals.rs` with `n`
//!    locals, block for block as rustc lowers it at `-C opt-level=0`: per local a
//!    `Box::new` call, the pointer-alignment check, the overflow-checked `sum +=`
//!    with its `Assert`, the `drop` call, a drop FLAG set and cleared, and a
//!    two-block cleanup rung (flag switch + `Drop`) chained into the next rung —
//!    every call and assert UNWINDS into the ladder. 7n + 2 blocks.
//!  * [`grid`] — `n` straight-line writes, a `SwitchInt` fanning out to `m` arms
//!    that each read one name and reassign another, and a join reading two.
//!  * [`diamond_chain`] — `n` sequential diamonds, `x` reassigned in one arm of
//!    each and read at every join.
//!  * [`loop_ladder`] — `n` blocks, each branching forward and BACK (the
//!    `tests/vcgen_entry_version_fixpoint.rs` ladder), with an opaque deref store
//!    and `&mut` borrows putting the whole-function havoc list in effect.
//!  * [`loop_joins`] — `n` sequential loops whose body is a diamond (the
//!    loop-header phi / in-loop join shape), with reassignment BEFORE a read in
//!    the same block.
//!  * [`irreducible`] — an entry switch into every block of an `n`-cycle (the
//!    coroutine-resume shape): an irreducible region.
//!
//! and the shapes the WS-E reviews found super-linear in the first SSA oracle:
//!
//!  * [`loop_diamond_names`] — ONE loop whose body is a chain of `n` diamonds, name
//!    `x_k` written only in diamond `k`'s left arm, every `x_k` read after the loop
//!    (each answer has size 2; resolving it used to walk every join of the body);
//!  * [`diamond_chain_single_read`] — `n` diamonds reassigning one `x`, read ONCE at
//!    the end (one answer of size `n + 1`; the flat token sets stored Θ(n²));
//!  * [`confined_store_blocks`] / [`confined_store_one_block`] — a `&mut self` method
//!    with `n` borrows (a `2n`-name havoc list) and `n` CONFINED field stores
//!    `(*self).f_i = i`, one per block / all in one block;
//!  * [`confined_store_loop`] — `n` confined field stores inside ONE loop, every
//!    other one in one arm of a diamond, with `self` read at each store: a read whose
//!    rebinders (`self` and every field) are defined a few at a time around a cycle;
//!  * [`shared_reborrow_calls`] — the same borrows, then `n` calls `foo(&*self)`,
//!    each REFINED (TRUST-10) to "the havoc list minus `self`";
//!  * [`confined_store_index_havoc`] — a read `(*p).a[j]` whose two havoc rebinders,
//!    `p` and `j`'s index fallback, are defined apart: a confined store through `p`
//!    defines the fallback and not `p` (a group's PART exclusion; fixed size);
//!  * [`nested_loops_names`] — `n` names written in the innermost of `depth` nested
//!    loops and read after the outermost: the residual (minimal SSA needs `depth`
//!    joins per name);
//!  * [`array_stores_block`] — a join-free body of `n` array-theory element stores,
//!    whose `arr$L$vN` definition names are the synthetic names the write index's
//!    exact-prefix fallback exists for;
//!
//! and, for the T3 C08 coverage gate only, [`block_def_divisions`]: `n` divisions in one
//! block, whose rows are block-def combinations nothing rewrites.

use serde_json::{Value, json};
use trust_types::VerifiableFunction;

fn span() -> Value {
    json!({"file": "family.rs", "line_start": 1, "col_start": 0, "line_end": 1, "col_end": 1})
}

fn u(width: u32) -> Value {
    json!({"Int": {"width": width, "signed": false}})
}

fn raw(pointee: Value) -> Value {
    json!({"RawPtr": {"mutable": false, "pointee": pointee}})
}

fn adt(name: &str, fields: Vec<(&str, Value)>) -> Value {
    let fields: Vec<Value> = fields.into_iter().map(|(n, t)| json!([n, t])).collect();
    json!({"Adt": {"name": name, "fields": fields, "variants": [], "disc_index_safe": false,
        "faithful_enum_repr": null, "layout": null, "enum_layout": null, "adt_kind": "Struct"}})
}

/// `Box<u64>` exactly as the extraction spells it: the raw pointer two fields down
/// makes every `Box` local a pointer-carrying local (the whole-function havoc list).
fn box_u64() -> Value {
    let nonnull = adt("core::ptr::non_null::NonNull", vec![("pointer", raw(u(64)))]);
    let marker = adt("core::marker::PhantomData", vec![]);
    let unique = adt("core::ptr::unique::Unique", vec![("pointer", nonnull), ("_marker", marker)]);
    adt("alloc::boxed::Box", vec![("0", unique), ("1", adt("alloc::alloc::Global", vec![]))])
}

fn place(local: usize) -> Value {
    json!({"local": local, "projections": []})
}

fn place_proj(local: usize, projections: Value) -> Value {
    json!({"local": local, "projections": projections})
}

fn copy(p: Value) -> Value {
    json!({"Copy": p})
}

fn mv(p: Value) -> Value {
    json!({"Move": p})
}

fn cu(v: u64, width: u32) -> Value {
    json!({"Constant": {"Uint": [v, width]}})
}

fn cb(b: bool) -> Value {
    json!({"Constant": {"Bool": b}})
}

fn assign(p: Value, rvalue: Value) -> Value {
    json!({"Assign": {"place": p, "rvalue": rvalue, "span": span()}})
}

fn binop(op: &str, a: Value, b: Value) -> Value {
    json!({"BinaryOp": [op, a, b]})
}

fn cast(op: Value, ty: Value) -> Value {
    json!({"Cast": [op, ty]})
}

fn goto(t: usize) -> Value {
    json!({"Goto": t})
}

fn switch(discr: Value, targets: Vec<(u64, usize)>, otherwise: usize) -> Value {
    let targets: Vec<Value> = targets.into_iter().map(|(v, t)| json!([v, t])).collect();
    json!({"SwitchInt": {"discr": discr, "targets": targets, "otherwise": otherwise,
        "exhaustive_enum_unreachable": false, "span": span()}})
}

fn unwind(cleanup: Option<usize>) -> Value {
    match cleanup {
        Some(c) => json!({"Cleanup": c}),
        None => json!("Continue"),
    }
}

fn call(
    fn_path: &str,
    args: Vec<Value>,
    dest: Value,
    target: usize,
    cleanup: Option<usize>,
) -> Value {
    json!({"Call": {"func": fn_path, "args": args, "dest": dest, "target": target, "span": span(),
        "atomic": null, "is_foreign": false, "is_unsafe_sig": false, "unwind": unwind(cleanup)}})
}

fn local(index: usize, ty: Value, name: Option<String>) -> Value {
    json!({"index": index, "ty": ty, "name": name})
}

fn block(id: usize, stmts: Vec<Value>, terminator: Value) -> Value {
    json!({"id": id, "stmts": stmts, "terminator": terminator})
}

fn function(
    name: &str,
    locals: Vec<Value>,
    blocks: Vec<Value>,
    arg_count: usize,
    ret: Value,
) -> VerifiableFunction {
    let v = json!({
        "name": name,
        "def_path": format!("family::{name}"),
        "span": span(),
        "body": {"locals": locals, "blocks": blocks, "arg_count": arg_count, "return_ty": ret},
        "contracts": [], "preconditions": [], "postconditions": [],
        "spec": {"requires": [], "ensures": [], "invariants": []},
    });
    serde_json::from_value(v).expect("a generated family body deserializes")
}

/// `ever-init-many-locals` with `n` locals, as rustc lowers it at `-O0`.
pub(crate) fn locals_chain(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    const PER: usize = 18;
    let base = |i: usize| 2 + PER * i;
    let mut locals = vec![local(0, u(64), None), local(1, u(64), Some("sum".into()))];
    for i in 0..n {
        let b = base(i);
        let unit_ptr = raw(json!("Unit"));
        let tys: [(Value, Option<String>); PER] = [
            (box_u64(), Some(format!("a{i:03}"))),     // a: the boxed local
            (u(64), None),                             // t: `*a`
            (json!({"Tuple": [u(64), "Bool"]}), None), // c: checked sum
            (json!("Unit"), None),                     // u: `drop` result
            (box_u64(), None),                         // m: the moved box
            (json!("Bool"), None),                     // flag: drop flag
            (raw(u(64)), None),                        // p
            (unit_ptr.clone(), None),                  // q
            (u(64), None),                             // x
            (u(64), None),                             // y
            (u(64), None),                             // z
            (json!("Bool"), None),                     // e
            (unit_ptr, None),                          // r
            (u(64), None),                             // s
            (json!("Bool"), None),                     // k1
            (json!("Bool"), None),                     // k2
            (json!("Bool"), None),                     // k3
            (json!("Bool"), None),                     // k4
        ];
        for (off, (ty, name)) in tys.into_iter().enumerate() {
            locals.push(local(b + off, ty, name));
        }
    }
    let (a, t, c, uu, m, flag, p, q, x, y, z, e, r, s, k1, k2, k3, k4) =
        (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
    let bb = |i: usize, off: usize| 7 * i + off;
    let (ret, resume) = (7 * n, 7 * n + 1);
    let mut blocks: Vec<Value> = Vec::with_capacity(7 * n + 2);
    for i in 0..n {
        let l = |off: usize| base(i) + off;
        let next_cleanup = if i == 0 { resume } else { bb(i - 1, 5) };
        // call_i
        let mut stmts = Vec::new();
        if i == 0 {
            for j in 0..n {
                stmts.push(assign(place(base(j) + flag), json!({"Use": cb(false)})));
            }
            stmts.push(assign(place(1), json!({"Use": cu(0, 64)})));
        }
        stmts.push(assign(place(l(flag)), json!({"Use": cb(true)})));
        blocks.push(block(
            bb(i, 0),
            stmts,
            call(
                "alloc::boxed::Box::<u64>::new",
                vec![cu(1, 64)],
                place(l(a)),
                bb(i, 1),
                (i > 0).then(|| bb(i - 1, 5)),
            ),
        ));
        // cast_i: the pointer-alignment check.
        blocks.push(block(
            bb(i, 1),
            vec![
                assign(
                    place(l(p)),
                    cast(copy(place_proj(l(a), json!([{"Field": 0}, {"Field": 0}]))), raw(u(64))),
                ),
                assign(place(l(q)), cast(copy(place(l(p))), raw(json!("Unit")))),
                assign(place(l(x)), cast(copy(place(l(q))), u(64))),
                assign(place(l(y)), binop("Sub", cu(8, 64), cu(1, 64))),
                assign(place(l(z)), binop("BitAnd", copy(place(l(x))), copy(place(l(y))))),
                assign(place(l(e)), binop("Eq", copy(place(l(z))), cu(0, 64))),
            ],
            goto(bb(i, 2)),
        ));
        // chk_i: the null check.
        blocks.push(block(
            bb(i, 2),
            vec![
                assign(place(l(r)), cast(copy(place(l(p))), raw(json!("Unit")))),
                assign(place(l(s)), cast(copy(place(l(r))), u(64))),
                assign(place(l(k1)), binop("Ne", cu(8, 64), cu(0, 64))),
                assign(place(l(k2)), binop("Eq", copy(place(l(s))), cu(0, 64))),
                assign(place(l(k3)), binop("BitAnd", copy(place(l(k2))), copy(place(l(k1))))),
                assign(place(l(k4)), json!({"UnaryOp": ["Not", copy(place(l(k3)))]})),
            ],
            goto(bb(i, 3)),
        ));
        // add_i: `sum += *a`.
        blocks.push(block(
            bb(i, 3),
            vec![
                assign(place(l(t)), json!({"Use": copy(place_proj(l(p), json!(["Deref"])))})),
                assign(
                    place(l(c)),
                    json!({"CheckedBinaryOp": ["Add", copy(place(1)), copy(place(l(t)))]}),
                ),
            ],
            json!({"Assert": {"cond": mv(place_proj(l(c), json!([{"Field": 1}]))),
                "expected": false,
                "msg": {"Overflow": "Add"}, "target": bb(i, 4), "span": span(),
                "unwind": {"Cleanup": bb(i, 5)}}}),
        ));
        // drop_i: `drop(a)`.
        blocks.push(block(
            bb(i, 4),
            vec![
                assign(place(1), json!({"Use": mv(place_proj(l(c), json!([{"Field": 0}])))})),
                assign(place(l(flag)), json!({"Use": cb(false)})),
                assign(place(l(m)), json!({"Use": mv(place(l(a)))})),
            ],
            call(
                "core::mem::drop::<alloc::boxed::Box<u64>>",
                vec![mv(place(l(m)))],
                place(l(uu)),
                if i + 1 < n { bb(i + 1, 0) } else { ret },
                Some(bb(i, 5)),
            ),
        ));
        // The cleanup rung: flag switch, then the drop.
        blocks.push(block(
            bb(i, 5),
            vec![],
            switch(copy(place(l(flag))), vec![(0, next_cleanup)], bb(i, 6)),
        ));
        blocks.push(block(
            bb(i, 6),
            vec![],
            json!({"Drop": {"place": place(l(a)), "target": next_cleanup, "span": span(),
                "unwind": "Terminate"}}),
        ));
    }
    blocks.push(block(
        ret,
        vec![assign(place(0), json!({"Use": copy(place(1))}))],
        json!("Return"),
    ));
    blocks.push(block(resume, vec![], json!("Resume")));
    function(&format!("locals_chain_{n}"), locals, blocks, 0, u(64))
}

/// `n` straight-line writes, a switch over `m` arms, a join.
pub(crate) fn grid(n: usize, m: usize) -> VerifiableFunction {
    assert!(n >= 2 && m >= 2);
    let mut locals = vec![local(0, u(32), None), local(1, u(32), Some("d".into()))];
    for j in 0..n {
        locals.push(local(2 + j, u(32), Some(format!("v{j}"))));
    }
    let v = |j: usize| 2 + (j % n);
    let join = m + 1;
    let mut blocks = Vec::new();
    let writes: Vec<Value> =
        (0..n).map(|j| assign(place(v(j)), json!({"Use": cu(j as u64, 32)}))).collect();
    let targets: Vec<(u64, usize)> = (0..m - 1).map(|k| (k as u64, 1 + k)).collect();
    blocks.push(block(0, writes, switch(copy(place(1)), targets, m)));
    for k in 0..m {
        blocks.push(block(
            1 + k,
            vec![assign(place(v(k)), binop("Add", copy(place(v(k + 1))), cu(1, 32)))],
            goto(join),
        ));
    }
    blocks.push(block(
        join,
        vec![assign(place(0), binop("Add", copy(place(v(0))), copy(place(v(n - 1)))))],
        json!("Return"),
    ));
    function(&format!("grid_{n}_{m}"), locals, blocks, 1, u(32))
}

/// `n` sequential diamonds; `x` reassigned in one arm of each, read at each join.
pub(crate) fn diamond_chain(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let mut locals = vec![
        local(0, u(32), None),
        local(1, u(32), Some("c".into())),
        local(2, u(32), Some("x".into())),
    ];
    for i in 0..n {
        locals.push(local(3 + i, u(32), Some(format!("t{i}"))));
    }
    // bb0; per i: br = 1+4i, a = 2+4i, b = 3+4i, j = 4+4i; ret = 1+4n.
    let ret = 1 + 4 * n;
    let mut blocks = vec![block(0, vec![assign(place(2), json!({"Use": cu(0, 32)}))], goto(1))];
    for i in 0..n {
        let (br, a, b, j) = (1 + 4 * i, 2 + 4 * i, 3 + 4 * i, 4 + 4 * i);
        blocks.push(block(br, vec![], switch(copy(place(1)), vec![(0, a)], b)));
        blocks.push(block(
            a,
            vec![assign(place(2), binop("Add", copy(place(2)), cu(1, 32)))],
            goto(j),
        ));
        blocks.push(block(b, vec![], goto(j)));
        let next = if i + 1 < n { 1 + 4 * (i + 1) } else { ret };
        blocks.push(block(
            j,
            vec![assign(place(3 + i), binop("Add", copy(place(2)), cu(2, 32)))],
            goto(next),
        ));
    }
    blocks.push(block(
        ret,
        vec![assign(place(0), json!({"Use": copy(place(2))}))],
        json!("Return"),
    ));
    function(&format!("diamond_chain_{n}"), locals, blocks, 1, u(32))
}

/// The back-edge ladder of `tests/vcgen_entry_version_fixpoint.rs`.
pub(crate) fn loop_ladder(n: usize, borrows: usize) -> VerifiableFunction {
    assert!(n >= 2);
    let mut locals = vec![
        local(0, u(32), Some("ret".into())),
        local(1, json!({"Ref": {"mutable": true, "inner": u(32)}}), Some("p".into())),
        local(2, u(32), Some("a".into())),
        local(3, u(32), Some("b".into())),
        local(4, u(32), Some("cond".into())),
    ];
    let first_tmp = locals.len();
    for i in 0..n {
        locals.push(local(first_tmp + i, u(32), Some(format!("t{i}"))));
    }
    let first_borrow = locals.len();
    for i in 0..borrows {
        locals.push(local(first_borrow + 2 * i, u(32), Some(format!("v{i}"))));
        locals.push(local(
            first_borrow + 2 * i + 1,
            json!({"Ref": {"mutable": true, "inner": u(32)}}),
            Some(format!("r{i}")),
        ));
    }
    let mut blocks = Vec::new();
    for b in 0..n {
        let mut stmts = Vec::new();
        if b == 0 {
            stmts.push(assign(place_proj(1, json!(["Deref"])), json!({"Use": copy(place(2))})));
            for i in 0..borrows {
                stmts.push(assign(
                    place(first_borrow + 2 * i + 1),
                    json!({"Ref": {"mutable": true, "place": place(first_borrow + 2 * i)}}),
                ));
            }
        }
        stmts.push(assign(place(first_tmp + b), binop("Add", copy(place(2)), copy(place(3)))));
        let term = if b + 1 >= n {
            json!("Return")
        } else {
            switch(copy(place(4)), vec![(0, b + 1)], b.saturating_sub(1))
        };
        blocks.push(block(b, stmts, term));
    }
    function(&format!("loop_ladder_{n}"), locals, blocks, 4, u(32))
}

/// `n` sequential loops, each: header -> diamond (one arm reassigns `k` from a read
/// of itself) -> latch reading `k` -> back to the header or on.
pub(crate) fn loop_joins(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let mut locals = vec![
        local(0, u(32), None),
        local(1, u(32), Some("c".into())),
        local(2, u(32), Some("c2".into())),
        local(3, u(32), Some("k".into())),
        local(4, u(32), Some("t".into())),
    ];
    for i in 0..n {
        locals.push(local(5 + i, u(32), Some(format!("w{i}"))));
    }
    // bb0; per loop i: hdr = 1+4i, arm_a = 2+4i, arm_b = 3+4i, latch = 4+4i; ret = 1+4n.
    let ret = 1 + 4 * n;
    let mut blocks = vec![block(0, vec![assign(place(3), json!({"Use": cu(0, 32)}))], goto(1))];
    for i in 0..n {
        let (hdr, aa, ab, latch) = (1 + 4 * i, 2 + 4 * i, 3 + 4 * i, 4 + 4 * i);
        blocks.push(block(hdr, vec![], switch(copy(place(1)), vec![(0, aa)], ab)));
        blocks.push(block(
            aa,
            vec![
                assign(place(4), json!({"Use": copy(place(3))})),
                assign(place(3), binop("Add", copy(place(4)), cu(1, 32))),
            ],
            goto(latch),
        ));
        blocks.push(block(ab, vec![], goto(latch)));
        let exit = if i + 1 < n { 1 + 4 * (i + 1) } else { ret };
        blocks.push(block(
            latch,
            vec![assign(place(5 + i), binop("Add", copy(place(3)), cu(2, 32)))],
            switch(copy(place(2)), vec![(0, hdr)], exit),
        ));
    }
    blocks.push(block(
        ret,
        vec![assign(place(0), json!({"Use": copy(place(3))}))],
        json!("Return"),
    ));
    function(&format!("loop_joins_{n}"), locals, blocks, 2, u(32))
}

/// An entry switch into every block of an `n`-cycle: an irreducible region.
pub(crate) fn irreducible(n: usize) -> VerifiableFunction {
    assert!(n >= 2);
    let locals = vec![
        local(0, u(32), None),
        local(1, u(32), Some("s".into())),
        local(2, u(32), Some("x".into())),
    ];
    // bb0 = entry switch; L_k = 1 + k; exit = 1 + n.
    let exit = 1 + n;
    let targets: Vec<(u64, usize)> = (0..n - 1).map(|k| (k as u64, 1 + k)).collect();
    let mut blocks = vec![block(0, vec![], switch(copy(place(1)), targets, n))];
    for k in 0..n {
        blocks.push(block(
            1 + k,
            vec![assign(place(2), binop("Add", copy(place(2)), cu(k as u64, 32)))],
            switch(copy(place(1)), vec![(0, exit)], 1 + (k + 1) % n),
        ));
    }
    blocks.push(block(
        exit,
        vec![assign(place(0), json!({"Use": copy(place(2))}))],
        json!("Return"),
    ));
    function(&format!("irreducible_{n}"), locals, blocks, 1, u(32))
}

/// One loop whose body is a chain of `n` diamonds; name `x_k` is written (a constant)
/// ONLY in the left arm of diamond `k`; after the loop, the exit block reads every `x_k`
/// once. Every answer is `{e, s{L_k}_0}`.
pub(crate) fn loop_diamond_names(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let mut locals = vec![local(0, u(32), None), local(1, u(32), Some("c".into()))];
    for k in 0..n {
        locals.push(local(2 + k, u(32), Some(format!("x{k}"))));
    }
    let x = |k: usize| 2 + k;
    // bb0 -> hdr(1); diamond i: br = 2+3i, left = 3+3i, right = 4+3i; latch = 2+3n;
    // exit = 3+3n.
    let hdr = 1;
    let br = |i: usize| 2 + 3 * i;
    let latch = 2 + 3 * n;
    let exit = 3 + 3 * n;
    let mut blocks = vec![block(0, vec![], goto(hdr))];
    blocks.push(block(hdr, vec![], switch(copy(place(1)), vec![(0, exit)], br(0))));
    for i in 0..n {
        let (b, l, r) = (br(i), 3 + 3 * i, 4 + 3 * i);
        let next = if i + 1 < n { br(i + 1) } else { latch };
        blocks.push(block(b, vec![], switch(copy(place(1)), vec![(0, l)], r)));
        blocks.push(block(
            l,
            vec![assign(place(x(i)), json!({"Use": cu(i as u64, 32)}))],
            goto(next),
        ));
        blocks.push(block(r, vec![], goto(next)));
    }
    blocks.push(block(latch, vec![], goto(hdr)));
    let reads: Vec<Value> =
        (0..n).map(|k| assign(place(0), binop("Add", copy(place(x(k))), cu(1, 32)))).collect();
    blocks.push(block(exit, reads, json!("Return")));
    function(&format!("loop_diamond_names_{n}"), locals, blocks, 1, u(32))
}

/// `n` diamonds, `x` written (a constant) in one arm of each, `x` read ONCE, at the
/// return block: one query whose answer has `n + 1` tokens.
pub(crate) fn diamond_chain_single_read(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let locals = vec![
        local(0, u(32), None),
        local(1, u(32), Some("c".into())),
        local(2, u(32), Some("x".into())),
    ];
    let ret = 1 + 3 * n;
    let mut blocks = vec![block(0, vec![assign(place(2), json!({"Use": cu(0, 32)}))], goto(1))];
    for i in 0..n {
        let (br, a, b) = (1 + 3 * i, 2 + 3 * i, 3 + 3 * i);
        let next = if i + 1 < n { 1 + 3 * (i + 1) } else { ret };
        blocks.push(block(br, vec![], switch(copy(place(1)), vec![(0, a)], b)));
        blocks.push(block(
            a,
            vec![assign(place(2), json!({"Use": cu(i as u64 + 1, 32)}))],
            goto(next),
        ));
        blocks.push(block(b, vec![], goto(next)));
    }
    blocks.push(block(
        ret,
        vec![assign(place(0), json!({"Use": copy(place(2))}))],
        json!("Return"),
    ));
    function(&format!("diamond_chain_single_read_{n}"), locals, blocks, 1, u(32))
}

/// A plain struct `S` with `n` `u32` fields, behind `&mut`.
fn mut_self_struct(n: usize) -> Value {
    let fields: Vec<(String, Value)> = (0..n).map(|i| (format!("f{i}"), u(32))).collect();
    let fields: Vec<Value> = fields.into_iter().map(|(n, t)| json!([n, t])).collect();
    json!({"Ref": {"mutable": true, "inner": {"Adt": {"name": "S", "fields": fields,
        "variants": [], "disc_index_safe": false, "faithful_enum_repr": null, "layout": null,
        "enum_layout": null, "adt_kind": "Struct"}}}})
}

/// `fn(&mut self)`: `n` mutable borrows `r_i = &mut v_i` in bb0 (a whole-function havoc
/// list of ~2n names), then `n` blocks each doing ONE CONFINED field store
/// `(*self).f_i = i` and reading `v_i`.
pub(crate) fn confined_store_blocks(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let mut locals = vec![local(0, u(32), None), local(1, mut_self_struct(n), Some("self".into()))];
    let v = |i: usize| 2 + 2 * i;
    let r = |i: usize| 3 + 2 * i;
    for i in 0..n {
        locals.push(local(v(i), u(32), Some(format!("v{i}"))));
        locals.push(local(
            r(i),
            json!({"Ref": {"mutable": true, "inner": u(32)}}),
            Some(format!("r{i}")),
        ));
    }
    let t = 2 + 2 * n;
    locals.push(local(t, u(32), Some("t".into())));
    let mut bb0 = Vec::new();
    for i in 0..n {
        bb0.push(assign(place(v(i)), json!({"Use": cu(0, 32)})));
        bb0.push(assign(place(r(i)), json!({"Ref": {"mutable": true, "place": place(v(i))}})));
    }
    let mut blocks = vec![block(0, bb0, goto(1))];
    for i in 0..n {
        let next = if i + 1 < n { 2 + i } else { 1 + n };
        blocks.push(block(
            1 + i,
            vec![
                assign(
                    place_proj(1, json!(["Deref", {"Field": i}])),
                    json!({"Use": cu(i as u64, 32)}),
                ),
                assign(place(t), json!({"Use": copy(place(v(i)))})),
            ],
            goto(next),
        ));
    }
    blocks.push(block(
        1 + n,
        vec![assign(place(0), json!({"Use": copy(place(t))}))],
        json!("Return"),
    ));
    function(&format!("confined_store_blocks_{n}"), locals, blocks, 1, u(32))
}

/// `fn(&mut self, c)`: ONE loop whose body is `n` confined field stores
/// `(*self).f_i = i`, every odd one in ONE arm of a diamond whose join reads
/// `(*self).f_i`, then `(*self).f_0` read after the loop. Every store reads `self` (a
/// projected destination reads its base), whose rebinders are `self` and every field:
/// the rebinder tree meets blocks that define SOME of a group inside a cycle of joins.
pub(crate) fn confined_store_loop(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let locals = vec![
        local(0, u(32), None),
        local(1, mut_self_struct(n), Some("self".into())),
        local(2, u(32), Some("c".into())),
        local(3, u(32), Some("t".into())),
    ];
    let field = |i: usize| place_proj(1, json!(["Deref", {"Field": i}]));
    let store = |i: usize| assign(field(i), json!({"Use": cu(i as u64, 32)}));
    // bb0 -> hdr (1) -> body ... -> hdr; hdr -> exit. Body ids are allocated in order.
    let body_len: usize = (0..n).map(|i| if i % 2 == 0 { 1 } else { 3 }).sum();
    let exit = 2 + body_len;
    let mut blocks = vec![block(0, vec![], goto(1))];
    blocks.push(block(1, vec![], switch(copy(place(2)), vec![(0, 2)], exit)));
    let mut id = 2;
    for i in 0..n {
        let span_len = if i % 2 == 0 { 1 } else { 3 };
        let next = if i + 1 < n { id + span_len } else { 1 };
        if i % 2 == 0 {
            blocks.push(block(id, vec![store(i)], goto(next)));
        } else {
            let (sw, arm, join) = (id, id + 1, id + 2);
            blocks.push(block(sw, vec![], switch(copy(place(2)), vec![(0, arm)], join)));
            blocks.push(block(arm, vec![store(i)], goto(join)));
            blocks.push(block(
                join,
                vec![assign(place(3), json!({"Use": copy(field(i))}))],
                goto(next),
            ));
        }
        id += span_len;
    }
    blocks.push(block(
        exit,
        vec![assign(place(0), json!({"Use": copy(field(0))}))],
        json!("Return"),
    ));
    function(&format!("confined_store_loop_{n}"), locals, blocks, 2, u(32))
}

/// `fn(&mut self)`: ONE block of `n` confined stores `(*self).f_i = i`, each followed
/// by a read of `(*self).f_0`.
pub(crate) fn confined_store_one_block(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let locals = vec![
        local(0, u(32), None),
        local(1, mut_self_struct(n), Some("self".into())),
        local(2, u(32), Some("t".into())),
    ];
    let mut stmts = Vec::new();
    for i in 0..n {
        stmts.push(assign(
            place_proj(1, json!(["Deref", {"Field": i}])),
            json!({"Use": cu(i as u64, 32)}),
        ));
        stmts.push(assign(
            place(2),
            json!({"Use": copy(place_proj(1, json!(["Deref", {"Field": 0}])))}),
        ));
    }
    stmts.push(assign(place(0), json!({"Use": copy(place(2))})));
    let blocks = vec![block(0, stmts, json!("Return"))];
    function(&format!("confined_store_one_block_{n}"), locals, blocks, 1, u(32))
}

/// `fn(p: &mut S, j: u64, c: u32, q: &mut S)`, `S { a: [u32; 4], b: u32 }`: `r = &mut
/// j` puts `j` and its index fallback `_2` on the havoc list beside the pointers `p`
/// and `q`, and the join of a diamond reads `(*p).a[j]` (`p*.0[_2]`), whose rebinders
/// are `p` and `_2`. Two CONFINED stores define them: `(*q).b = 1` at the end of the
/// entry block (a PART class excluding `q` alone, so it defines both) and `(*p).b = 5`
/// in one arm of the diamond (a class excluding `p` alone, so it defines `_2` and not
/// `p`). `base_first` also borrows `p` itself (`pp = &mut p`) before `j`, which puts
/// `p` ahead of `_2` in the havoc list, and so FIRST in the read's rebinder tree;
/// without it `_2` is first.
pub(crate) fn confined_store_index_havoc(base_first: bool) -> VerifiableFunction {
    let s_ty = adt("S", vec![("a", json!({"Array": {"elem": u(32), "len": 4}})), ("b", u(32))]);
    let s_ref = json!({"Ref": {"mutable": true, "inner": s_ty}});
    let locals = vec![
        local(0, u(32), None),
        local(1, s_ref.clone(), Some("p".into())),
        local(2, u(64), Some("j".into())),
        local(3, u(32), Some("c".into())),
        local(4, s_ref.clone(), Some("q".into())),
        local(5, json!({"Ref": {"mutable": true, "inner": s_ref}}), Some("pp".into())),
        local(6, json!({"Ref": {"mutable": true, "inner": u(64)}}), Some("r".into())),
        local(7, u(32), Some("t".into())),
    ];
    let store_b = |ptr: usize, v: u64| {
        assign(place_proj(ptr, json!(["Deref", {"Field": 1}])), json!({"Use": cu(v, 32)}))
    };
    let mut bb0 = Vec::new();
    if base_first {
        bb0.push(assign(place(5), json!({"Ref": {"mutable": true, "place": place(1)}})));
    }
    bb0.push(assign(place(6), json!({"Ref": {"mutable": true, "place": place(2)}})));
    bb0.push(store_b(4, 1));
    let read = place_proj(1, json!(["Deref", {"Field": 0}, {"Index": 2}]));
    let blocks = vec![
        block(0, bb0, switch(copy(place(3)), vec![(0, 1)], 2)),
        block(1, vec![store_b(1, 5)], goto(2)),
        block(
            2,
            vec![
                assign(place(7), json!({"Use": copy(read)})),
                assign(place(0), json!({"Use": copy(place(7))})),
            ],
            json!("Return"),
        ),
    ];
    let name = if base_first { "base_first" } else { "index_first" };
    function(&format!("confined_store_index_havoc_{name}"), locals, blocks, 4, u(32))
}

/// `fn(&mut self)`: `n` mutable borrows (a ~2n-name havoc list), then `n` blocks each
/// calling `foo(&*self)` — the TRUST-10 shared-reborrow refinement turns each call's
/// havoc into "the list minus `self`, plus `self`'s non-frozen names".
pub(crate) fn shared_reborrow_calls(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let s_ty = {
        let fields: Vec<Value> = (0..2).map(|i| json!([format!("f{i}"), u(32)])).collect();
        json!({"Adt": {"name": "S", "fields": fields, "variants": [], "disc_index_safe": false,
            "faithful_enum_repr": null, "layout": null, "enum_layout": null,
            "adt_kind": "Struct"}})
    };
    let mut locals = vec![
        local(0, json!("Unit"), None),
        local(1, json!({"Ref": {"mutable": true, "inner": s_ty.clone()}}), Some("self".into())),
    ];
    let v = |i: usize| 2 + 4 * i;
    let r = |i: usize| 3 + 4 * i;
    let s = |i: usize| 4 + 4 * i;
    let unit = |i: usize| 5 + 4 * i;
    for i in 0..n {
        locals.push(local(v(i), u(32), Some(format!("v{i}"))));
        locals.push(local(
            r(i),
            json!({"Ref": {"mutable": true, "inner": u(32)}}),
            Some(format!("r{i}")),
        ));
        locals.push(local(s(i), json!({"Ref": {"mutable": false, "inner": s_ty.clone()}}), None));
        locals.push(local(unit(i), json!("Unit"), None));
    }
    let mut bb0 = Vec::new();
    for i in 0..n {
        bb0.push(assign(place(v(i)), json!({"Use": cu(0, 32)})));
        bb0.push(assign(place(r(i)), json!({"Ref": {"mutable": true, "place": place(v(i))}})));
    }
    let mut blocks = vec![block(0, bb0, goto(1))];
    for i in 0..n {
        blocks.push(block(
            1 + i,
            vec![assign(
                place(s(i)),
                json!({"Ref": {"mutable": false, "place": place_proj(1, json!(["Deref"]))}}),
            )],
            call("foo", vec![mv(place(s(i)))], place(unit(i)), 2 + i, None),
        ));
    }
    blocks.push(block(1 + n, vec![], json!("Return")));
    function(&format!("shared_reborrow_calls_{n}"), locals, blocks, 1, json!("Unit"))
}

/// `n` names `x_k`, each written in the innermost body of `depth` nested loops and read
/// after the outermost. Minimal SSA places a join at every one of the `depth` headers
/// for every name, and a resolution of `x_k` after the loops resolves them: Θ(n x
/// depth) joins for answers of size 2 — the documented residual.
pub(crate) fn nested_loops_names(n: usize, depth: usize) -> VerifiableFunction {
    assert!(n >= 1 && depth >= 1);
    let mut locals = vec![local(0, u(32), None), local(1, u(32), Some("c".into()))];
    for k in 0..n {
        locals.push(local(2 + k, u(32), Some(format!("x{k}"))));
    }
    // bb0 -> hdr_0; hdr_d = 1 + 2d, exit_d = 2 + 2d (exit_d latches back to hdr_{d-1});
    // body = 1 + 2*depth; exit block = the outermost exit (2).
    let hdr = |d: usize| 1 + 2 * d;
    let ex = |d: usize| 2 + 2 * d;
    let body = 1 + 2 * depth;
    let mut blocks = vec![block(0, vec![], goto(hdr(0)))];
    for d in 0..depth {
        let inner = if d + 1 < depth { hdr(d + 1) } else { body };
        blocks.push(block(hdr(d), vec![], switch(copy(place(1)), vec![(0, ex(d))], inner)));
        let (stmts, term) = if d == 0 {
            let reads: Vec<Value> = (0..n)
                .map(|k| assign(place(0), binop("Add", copy(place(2 + k)), cu(1, 32))))
                .collect();
            (reads, json!("Return"))
        } else {
            (vec![], goto(hdr(d - 1)))
        };
        blocks.push(block(ex(d), stmts, term));
    }
    let writes: Vec<Value> =
        (0..n).map(|k| assign(place(2 + k), json!({"Use": cu(k as u64, 32)}))).collect();
    blocks.push(block(body, writes, goto(hdr(depth - 1))));
    function(&format!("nested_loops_names_{n}_{depth}"), locals, blocks, 1, u(32))
}

/// A join-free body of `n` array-theory element stores `a[_i] = k` (`a: [u32; 8]`, `i`
/// a stable parameter), each followed by a read `t = a[_i]`. The stores' definitions
/// are `arr$2$v{k+1} == Store(arr$2$v{k}, ..)` — SYNTHETIC names no statement
/// destination spells, which is what the write index's exact-prefix fallback is for.
pub(crate) fn array_stores_block(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let locals = vec![
        local(0, u(32), None),
        local(1, u(64), Some("i".into())),
        local(2, json!({"Array": {"elem": u(32), "len": 8}}), Some("a".into())),
        local(3, u(32), Some("t".into())),
    ];
    let mut stmts = Vec::new();
    for k in 0..n {
        stmts.push(assign(place_proj(2, json!([{"Index": 1}])), json!({"Use": cu(k as u64, 32)})));
        stmts.push(assign(place(3), json!({"Use": copy(place_proj(2, json!([{"Index": 1}])))})));
    }
    stmts.push(assign(place(0), json!({"Use": copy(place(3))})));
    let blocks = vec![block(0, stmts, json!("Return"))];
    function(&format!("array_stores_block_{n}"), locals, blocks, 1, u(32))
}

/// `n` unsigned divisions in ONE block, each by a fresh copy of the divisor parameter
/// (`_d = copy b; _q = Div(copy a, copy _d)`) and with no zero-divisor `Assert`, so each
/// division is a statement-level `DivisionByZero` row (T3 C08). Each row's formula is its
/// block-def combination (`_d == b` and `_d == 0`) with nothing conjoined around it: an
/// entry block has no path definitions, guards or preconditions, the parameters no range
/// facts, and an unsigned division no overflow row. So its rows are the block-def rows the
/// sink joins as Spine rows, the C08 coverage gate's anchor; and their candidate lists
/// extend one another statement by statement, the dense block of plan C08's "sequence
/// growth" risk. Not in [`all_families`]: only the C08 gates read it.
pub(crate) fn block_def_divisions(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let mut locals = vec![
        local(0, u(64), None),
        local(1, u(64), Some("a".into())),
        local(2, u(64), Some("b".into())),
    ];
    let mut stmts = Vec::new();
    for k in 0..n {
        let (divisor, quotient) = (3 + 2 * k, 4 + 2 * k);
        locals.push(local(divisor, u(64), None));
        locals.push(local(quotient, u(64), None));
        stmts.push(assign(place(divisor), json!({"Use": copy(place(2))})));
        stmts.push(assign(place(quotient), binop("Div", copy(place(1)), copy(place(divisor)))));
    }
    stmts.push(assign(place(0), json!({"Use": copy(place(2 + 2 * n))})));
    let blocks = vec![block(0, stmts, json!("Return"))];
    function(&format!("block_def_divisions_{n}"), locals, blocks, 2, u(64))
}

/// Every family at size `n` (the sizes that make sense for each).
pub(crate) fn all_families(n: usize) -> Vec<VerifiableFunction> {
    vec![
        locals_chain(n),
        grid(n.max(2), n.max(2)),
        diamond_chain(n),
        loop_ladder(n.max(2), 3),
        loop_joins(n),
        irreducible(n.max(2)),
        loop_diamond_names(n),
        diamond_chain_single_read(n),
        confined_store_blocks(n),
        confined_store_one_block(n),
        confined_store_loop(n),
        shared_reborrow_calls(n),
        nested_loops_names(n, n.clamp(1, 4)),
        array_stores_block(n),
    ]
}
