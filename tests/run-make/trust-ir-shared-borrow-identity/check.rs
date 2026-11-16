// The source's one local object must keep its address across shared borrows.
// This checks the emitted program, not the lowerer's implementation.
#[derive(Debug)]
struct Function {
    name: String,
    producer: Option<String>,
    body_gate: Option<String>,
    instructions: Vec<String>,
}

fn functions(text: &str) -> Vec<Function> {
    let mut result = Vec::new();
    let mut current: Option<Function> = None;
    for line in text.lines() {
        if line.contains(" fn @") {
            assert!(current.is_none(), "unterminated function");
            current = Some(Function {
                name: String::new(), producer: None, body_gate: None, instructions: Vec::new(),
            });
        } else if let Some(function) = current.as_mut() {
            let line = line.trim();
            if let Some(name) = line.strip_prefix("; #display-path: \"") {
                function.name = name.strip_suffix('"').expect("quoted display path").to_owned();
            } else if let Some(producer) = line.strip_prefix("; #producer: ") {
                assert!(function.producer.replace(producer.to_owned()).is_none(),
                    "duplicate producer metadata");
            } else if let Some(body_gate) = line.strip_prefix("; #body-gate: ") {
                assert!(function.body_gate.replace(body_gate.to_owned()).is_none(),
                    "duplicate body-gate metadata");
            } else if line == "}" {
                result.push(current.take().unwrap());
            } else if !line.starts_with(';') && !line.starts_with("bb") && !line.is_empty() {
                function.instructions.push(line.split(" ;").next().unwrap().trim().to_owned());
            }
        }
    }
    assert!(current.is_none(), "unterminated final function");
    result
}

fn index(functions: &[Function], name: &str) -> usize {
    let found: Vec<_> = functions.iter().enumerate()
        .filter(|(_, function)| function.name == name).map(|(index, _)| index).collect();
    assert_eq!(found.len(), 1, "exactly one emitted function {name}");
    found[0]
}

fn all_call_arguments(function: &Function, callee: usize) -> Vec<(usize, Vec<String>)> {
    let marker = format!("call @func.{callee}(");
    function.instructions.iter().enumerate().filter_map(|(position, line)| {
        line.split_once(&marker).map(|(_, args)| {
            (position, args.strip_suffix(')').expect("call ends after its arguments")
                .split(',').map(|arg| arg.trim().to_owned()).collect::<Vec<_>>())
        })
    }).collect()
}

fn call_arguments(function: &Function, callee: usize) -> Vec<String> {
    let calls = all_call_arguments(function, callee);
    assert_eq!(calls.len(), 1, "exactly one call to {callee}: {function:?}");
    calls.into_iter().next().unwrap().1
}

fn slots(function: &Function) -> Vec<String> {
    function.instructions.iter().filter_map(|line| {
        line.split_once(" = alloca ").map(|(value, _)| value.to_owned())
    }).collect()
}

fn original_mutated_slot(function: &Function, bump: usize) -> String {
    let original = function.instructions.iter().find_map(|line| {
        line.split_once(" = alloca ").map(|(value, _)| value.to_owned())
    }).expect("the local has original storage");
    assert_eq!(call_arguments(function, bump), [original.clone()],
        "bump_scalar must receive the original local: {function:?}");
    original
}

pub fn verify_dump(text: &str) {
    let functions = functions(text);
    // Structural admission is required here; it is not a proof claim.
    for name in [
        "make", "increment", "read_after_write", "bump_scalar", "same_scalar",
        "shared_identity_after_mutation", "copied_value_has_distinct_storage",
        "read_scalar", "frozen_control",
        "bump_cell", "read_cell", "read_after_hidden_write",
        "shared_identity_without_mutation", "copied_value_without_mutation",
        "by_value_cell_parameter", "scalar_reassignment",
        "shared_borrow_in_match_guard",
        "read_f32", "read_f64", "same_f64", "shared_f32_reassignment",
        "shared_f64_reassignment", "shared_f64_identity", "shared_f64_temporary",
        "read_empty_array", "shared_empty_array",
        "same_wide", "shared_wide_parameter", "shared_wide_local",
        "same_unit", "shared_unit_parameter", "read_reference",
        "shared_reference_parameter", "shared_reference_deref",
        "same_reference_address", "shared_payload_reference",
    ] {
        let function = &functions[index(&functions, name)];
        assert_eq!(function.producer.as_deref(), Some("trust"),
            "the checked source function must have the Trust producer: {name}");
        assert_eq!(function.body_gate.as_deref(), Some("gated \"trust-direct-lane-structural\""),
            "the checked source function must retain structural admission: {name}");
    }
    let read = &functions[index(&functions, "read_after_write")];
    let storage: Vec<_> = read.instructions.iter().filter_map(|line| {
        line.split_once(" = alloca ").map(|(value, _)| value.to_owned())
    }).collect();
    let original = storage.first().expect("the original Counter has storage");
    assert_eq!(storage.len(), 1, "no fresh Counter/Cell snapshot: {read:?}");
    let arguments = call_arguments(read, index(&functions, "increment"));
    assert_eq!(arguments, [original.clone()],
        "increment must receive the original Counter, not a copy: {read:?}");
    let call = read.instructions.iter().position(|line| {
        line.contains(&format!("call @func.{}(", index(&functions, "increment")))
    }).unwrap();
    let get = index(&functions, "std::cell::Cell::<T>::get");
    let get_arguments = call_arguments(read, get);
    let field_addresses: Vec<_> = read.instructions.iter().enumerate().filter_map(|(at, line)| {
        let (result, operands) = line.split_once(" = gep inbounds i8, ptr ")?;
        let offset = operands.strip_prefix(&format!("{original}, "))?;
        let zero = format!("{offset} = const i64 0");
        read.instructions[..at].iter().any(|instruction| instruction == &zero)
            .then_some((at, result.to_owned()))
    }).collect();
    assert_eq!(field_addresses.len(), 1, "the Cell must be the Counter's actual field: {read:?}");
    let (field_at, field) = &field_addresses[0];
    assert_eq!(get_arguments, [field.clone()], "get must read the original field: {read:?}");
    let get_at = all_call_arguments(read, get)[0].0;
    assert!(call < *field_at && *field_at < get_at,
        "the original field is read after increment: {read:?}");

    let repeated = &functions[index(&functions, "shared_identity_after_mutation")];
    let arguments = call_arguments(repeated, index(&functions, "same_scalar"));
    assert_eq!(arguments.len(), 2, "two shared borrows");
    let original = original_mutated_slot(repeated, index(&functions, "bump_scalar"));
    assert_eq!(arguments, [original.clone(), original],
        "both shared borrows must address the original local: {repeated:?}");

    let temporary = &functions[index(&functions, "copied_value_has_distinct_storage")];
    let arguments = call_arguments(temporary, index(&functions, "same_scalar"));
    assert_eq!(arguments.len(), 2, "a local and a temporary are borrowed");
    let original = original_mutated_slot(temporary, index(&functions, "bump_scalar"));
    assert_eq!(arguments[0], original,
        "the left borrow must address the original local: {temporary:?}");
    let temporary_slots: Vec<_> = temporary.instructions.iter().filter_map(|line| {
        line.split_once(" = alloca ").map(|(value, _)| value.to_owned())
    }).collect();
    assert!(arguments.iter().all(|argument| temporary_slots.contains(argument)),
        "the local and its value temporary each have their own allocation: {temporary:?}");
    assert_ne!(arguments[0], arguments[1],
        "a value-producing cast must keep its separate temporary: {temporary:?}");

    let control = &functions[index(&functions, "frozen_control")];
    let arguments = call_arguments(control, index(&functions, "read_scalar"));
    assert_eq!(arguments.len(), 1, "the frozen scalar control still lowers");
    assert_eq!(control.instructions.iter().filter(|line| line.contains(" = alloca ")).count(), 1,
        "the scalar control needs one allocation");

    for name in ["read_after_hidden_write", "by_value_cell_parameter"] {
        let function = &functions[index(&functions, name)];
        let storage = slots(function);
        assert_eq!(storage.len(), 1, "one original Cell, no borrow snapshots: {function:?}");
        assert_eq!(call_arguments(function, index(&functions, "bump_cell")), storage,
            "the mutation must reach the original Cell: {function:?}");
        assert_eq!(call_arguments(function, index(&functions, "read_cell")), storage,
            "the subsequent read must reach the same Cell: {function:?}");
        let stores: Vec<_> = function.instructions.iter().enumerate().filter(|(_, line)| {
            line.starts_with("store ") && line.ends_with(&format!(", ptr {}", storage[0]))
        }).collect();
        assert_eq!(stores.len(), 1, "the Cell is initialized once, never restored: {function:?}");
        let bump = all_call_arguments(function, index(&functions, "bump_cell"));
        let read = all_call_arguments(function, index(&functions, "read_cell"));
        assert!(stores[0].0 < bump[0].0 && bump[0].0 < read[0].0,
            "the original Cell is initialized, then mutated, then read: {function:?}");
        if name == "by_value_cell_parameter" {
            assert!(stores[0].1.ends_with(&format!(" %0, ptr {}", storage[0])),
                "the original slot must hold the incoming Cell parameter: {function:?}");
        }
    }

    let shared = &functions[index(&functions, "shared_identity_without_mutation")];
    let storage = slots(shared);
    assert_eq!(storage.len(), 1, "the immutable local has one original slot: {shared:?}");
    assert_eq!(call_arguments(shared, index(&functions, "same_scalar")),
        [storage[0].clone(), storage[0].clone()],
        "shared borrows alone preserve original address identity: {shared:?}");

    let temporary = &functions[index(&functions, "copied_value_without_mutation")];
    let storage = slots(temporary);
    assert_eq!(storage.len(), 2, "one local and one value temporary: {temporary:?}");
    assert_eq!(call_arguments(temporary, index(&functions, "same_scalar")), storage,
        "the cast must borrow its own storage: {temporary:?}");

    let reassigned = &functions[index(&functions, "scalar_reassignment")];
    let storage = slots(reassigned);
    assert_eq!(storage.len(), 1, "reassignment uses one original slot: {reassigned:?}");
    let calls = all_call_arguments(reassigned, index(&functions, "read_scalar"));
    assert_eq!(calls.len(), 2, "read before and after assignment: {reassigned:?}");
    assert!(calls.iter().all(|(_, args)| *args == storage),
        "both reads must address the same local: {reassigned:?}");
    let stores: Vec<_> = reassigned.instructions.iter().enumerate().filter(|(_, line)| {
        line.starts_with("store ") && line.ends_with(&format!(", ptr {}", storage[0]))
    }).collect();
    assert_eq!(stores.len(), 2, "initialization and reassignment: {reassigned:?}");
    assert!(stores[0].0 < calls[0].0 && calls[0].0 < stores[1].0 && stores[1].0 < calls[1].0,
        "the same slot is updated between observations: {reassigned:?}");

    for (name, read, ty) in [
        ("shared_f32_reassignment", "read_f32", "f32"),
        ("shared_f64_reassignment", "read_f64", "f64"),
    ] {
        let function = &functions[index(&functions, name)];
        let storage = slots(function);
        assert_eq!(storage.len(), 1, "one typed floating-point local: {function:?}");
        assert!(function.instructions.iter().any(|line| {
            line == &format!("{} = alloca {ty}", storage[0])
        }), "float storage must keep its own type: {function:?}");
        let calls = all_call_arguments(function, index(&functions, read));
        assert_eq!(calls.len(), 2, "both float observations remain: {function:?}");
        assert!(calls.iter().all(|(_, args)| *args == storage),
            "both float observations use the original slot: {function:?}");
        let stores: Vec<_> = function.instructions.iter().enumerate().filter(|(_, line)| {
            line.starts_with(&format!("store {ty} "))
                && line.ends_with(&format!(", ptr {}", storage[0]))
        }).collect();
        assert_eq!(stores.len(), 2, "initial and replacement float: {function:?}");
        assert!(stores[0].1.contains(" %0,") && stores[1].1.contains(" %1,"),
            "both incoming float values survive unchanged: {function:?}");
        assert!(stores[0].0 < calls[0].0 && calls[0].0 < stores[1].0
            && stores[1].0 < calls[1].0, "float stores and observations stay ordered: {function:?}");
    }
    let identity = &functions[index(&functions, "shared_f64_identity")];
    let storage = slots(identity);
    assert_eq!(storage.len(), 1, "one original f64 allocation: {identity:?}");
    assert_eq!(call_arguments(identity, index(&functions, "same_f64")),
        [storage[0].clone(), storage[0].clone()], "shared float addresses remain identical");

    let temporary = &functions[index(&functions, "shared_f64_temporary")];
    let storage = slots(temporary);
    assert_eq!(storage.len(), 2, "float cast owns separate temporary storage: {temporary:?}");
    assert_eq!(call_arguments(temporary, index(&functions, "same_f64")), storage,
        "the float value-producing cast must not borrow the original local's address");

    let empty = &functions[index(&functions, "shared_empty_array")];
    let storage = slots(empty);
    assert_eq!(storage.len(), 1, "one zero-length array allocation: {empty:?}");
    let calls = all_call_arguments(empty, index(&functions, "read_empty_array"));
    assert_eq!(calls.len(), 2, "both zero-length array observations remain: {empty:?}");
    assert!(calls.iter().all(|(_, args)| *args == storage),
        "the empty array has stable storage: {empty:?}");

    let guarded = &functions[index(&functions, "shared_borrow_in_match_guard")];
    let storage = slots(guarded);
    assert_eq!(storage.len(), 1, "guard-only borrowing still gives the local stable storage");
    assert_eq!(call_arguments(guarded, index(&functions, "read_scalar")), storage,
        "the match guard must read the original slot: {guarded:?}");

    for (name, callee) in [
        ("shared_wide_parameter", "same_wide"),
        ("shared_wide_local", "same_wide"),
        ("shared_unit_parameter", "same_unit"),
    ] {
        let function = &functions[index(&functions, name)];
        let storage = slots(function);
        assert_eq!(storage.len(), 1, "one stable shared-only slot: {function:?}");
        assert_eq!(call_arguments(function, index(&functions, callee)),
            [storage[0].clone(), storage[0].clone()],
            "repeated shared borrows must use the same address: {function:?}");
        let stores: Vec<_> = function.instructions.iter().filter(|line| {
            line.starts_with("store ") && line.ends_with(&format!(", ptr {}", storage[0]))
        }).collect();
        assert_eq!(stores.len(), 1, "immutable shared storage is initialized once: {function:?}");
        if name != "shared_wide_local" {
            assert!(stores[0].contains(" %0,"),
                "shared parameter storage holds the original incoming value: {function:?}");
        }
    }

    let reference = &functions[index(&functions, "shared_reference_parameter")];
    let storage = slots(reference);
    assert_eq!(storage.len(), 1, "one address for the reference parameter: {reference:?}");
    let calls = all_call_arguments(reference, index(&functions, "read_reference"));
    assert_eq!(calls.len(), 2, "both reference observations remain: {reference:?}");
    assert!(calls.iter().all(|(_, args)| *args == storage),
        "both outer borrows use one slot: {reference:?}");
    assert!(reference.instructions.iter().any(|line| {
        line == &format!("store ptr %0, ptr {}", storage[0])
    }), "the slot stores the original pointer: {reference:?}");
    assert!(reference.instructions.iter().any(|line| line.contains(" = load i32, ptr %0")),
        "direct reads retain incoming reference provenance: {reference:?}");

    let deref = &functions[index(&functions, "shared_reference_deref")];
    assert_eq!(slots(deref).len(), 1, "the reference local has one outer slot: {deref:?}");
    assert!(deref.instructions.iter().any(|line| line.contains(" = load i32, ptr %0")),
        "dereferencing the outer slot must reach the original incoming pointer: {deref:?}");
    assert!(!deref.instructions.iter().any(|line| line.contains(" = load ptr,")),
        "immutable pointer slots must forward the original provenance: {deref:?}");

    let payload = &functions[index(&functions, "shared_payload_reference")];
    let args = call_arguments(payload, index(&functions, "same_reference_address"));
    assert_eq!(args.len(), 2, "two borrows of the payload-reference binding");
    assert_eq!(args[0], args[1], "the payload-reference binding has one address: {payload:?}");
    let store = payload.instructions.iter().find(|line| {
        line.starts_with("store ptr ") && line.ends_with(&format!(", ptr {}", args[0]))
    }).expect("the outer slot holds the original payload-reference pointer");
    let inner = store.strip_prefix("store ptr ").unwrap().split(", ptr ").next().unwrap();
    assert_ne!(inner, args[0], "outer storage must not alias the payload's storage");
    assert!(slots(payload).iter().any(|slot| slot == inner),
        "the exact emitted payload pointer is stored: {payload:?}");
    assert!(payload.instructions.iter().any(|line| {
        line.contains(&format!(" = load i32, ptr {inner}"))
    }), "payload reads retain that original pointer: {payload:?}");
}
