//! Trust: `--emit=trust-ir` is a first-class analysis-phase artifact lane —
//! it must write the crate-level trust-ir binary Module at the requested
//! output path, with the canonical-text and coverage.json companions
//! alongside (extension swap on the `.bin`), WITHOUT the `-Z trust-ir-lower`
//! dev flag or the `-Z trust-dump=ir` dev flag, and without running codegen or
//! metadata emission (no `.rmeta`, no object artifacts).
//!
//! The coverage companion is the only published record of what the direct
//! producer could not lower, so this test also pins its HONESTY: the
//! capability/authority header must still read `obligation-bearing-pending-v2` /
//! (the owner-signed tier move, c2ac761224; authority axes still false) /
//! `proof_authority: false`, and a body that failed to lower must carry the
//! leaf-demand histogram that explains why. An empty histogram on a failed body
//! is indistinguishable, to every downstream consumer, from a body that
//! demanded nothing — so "the artifact exists and parses" is deliberately not
//! enough to pass here.
use std::path::Path;

use run_make_support::object::{Object, ObjectSymbol};
use run_make_support::{rfs, rustc};

/// WS5.2: the `(name, display_path)` of the ONE function whose canonical-text
/// block carries `; #display-path: "<def_path>"` — the def path moved out of
/// `Function.name`, which is now the link-time symbol.
fn named_by_display_path<'a>(text: &'a str, def_path: &str) -> &'a str {
    let directive = format!("; #display-path: {def_path:?}\n");
    let mut found = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            let block = &text[offset..];
            let block = &block[..block.find("\n}\n").map_or(block.len(), |end| end + 3)];
            if block.contains(&directive) {
                let name = line
                    .split_once("fn @")
                    .and_then(|(_, tail)| tail.split_once('('))
                    .map(|(name, _)| name)
                    .expect("function header names the function");
                found.push(name);
            }
        }
        offset += line.len();
    }
    assert_eq!(found.len(), 1, "exactly one function displays `{def_path}`: {found:?}\n{text}");
    found[0]
}

/// The text of `"<key>": [ … ]` inside a single coverage row up to the first
/// `]`, or `None` when the row carries no such key. Only emptiness is asserted
/// on the result, so stopping at a nested array's close is fine and keeps this
/// from being a second JSON parser.
fn array_field<'a>(row: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("\"{key}\": [");
    let start = row.find(&needle)? + needle.len();
    let end = start + row[start..].find(']')?;
    Some(row[start..end].trim())
}

/// The coverage row for `def_path`, as raw JSON text. The crate-module coverage
/// writer emits exactly one body per line.
fn body_row<'a>(coverage: &'a str, def_path: &str) -> &'a str {
    let needle = format!("\"def_path\": \"{def_path}\"");
    let start = coverage.find(&needle).unwrap_or_else(|| {
        panic!("coverage.json carries no body row for `{def_path}`:\n{coverage}")
    });
    let rest = &coverage[start..];
    rest.split('\n').next().unwrap_or(rest)
}

fn main() {
    let out_dir = Path::new("emit");
    rfs::create_dir(&out_dir);

    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&out_dir)
        .arg("-Ztrust-verify=off")
        .run();

    // The artifact triple, named from the crate name.
    assert!(out_dir.join("foo.trust-ir.bin").is_file(), "missing trust-ir binary artifact");
    assert!(out_dir.join("foo.trust-ir.txt").is_file(), "missing canonical-text companion");
    assert!(
        out_dir.join("foo.trust-ir.coverage.json").is_file(),
        "missing coverage.json companion"
    );

    // Analysis-only lane: no metadata, no codegen outputs.
    assert!(!out_dir.join("libfoo.rmeta").exists(), "trust-ir emit must not write metadata");
    assert!(!out_dir.join("foo.o").exists(), "trust-ir emit must not run codegen");

    // The binary artifact is non-empty and the coverage companion carries a
    // versioned schema tag. Matched on the stable prefix: a schema revision is a
    // deliberate, reviewable change to the fields asserted below, and pinning
    // the digit alone turns every revision into an unexplained failure that
    // reads as unrelated to whatever it actually broke.
    assert!(rfs::read(out_dir.join("foo.trust-ir.bin")).len() > 0);
    let cov = rfs::read_to_string(out_dir.join("foo.trust-ir.coverage.json"));
    assert!(
        cov.contains("\"schema\": \"trust.thir-lower.crate-module.coverage.v"),
        "coverage.json missing schema tag"
    );

    // The direct producer has no proof and no native-request authority. A
    // published artifact that says otherwise is a soundness event, not a golden
    // to re-bless.
    assert!(
        cov.contains("\"direct_obligation_capability\": \"obligation-bearing-pending-v2\""),
        "coverage.json must publish the direct producer's declared capability"
    );
    assert!(
        cov.contains("\"proof_authority\": false"),
        "the direct THIR producer must never publish proof authority"
    );
    assert!(
        cov.contains("\"native_verification_requests\": false"),
        "the direct THIR producer must never publish native verification requests"
    );

    // WS5.2 (F-087): `Function.name` IS the link-time symbol and the def path is the
    // display path. The spliced `add` is named by exactly the symbol the native object
    // exports for it (`nm`), and carries `add` as its display path.
    let text = rfs::read_to_string(out_dir.join("foo.trust-ir.txt"));
    let add_symbol = named_by_display_path(&text, "add");
    assert!(add_symbol.starts_with("_R"), "a v0 link-time symbol, not a def path: {add_symbol}");
    let native_dir = Path::new("native");
    rfs::create_dir(&native_dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("obj")
        .out_dir(&native_dir)
        .arg("-Ztrust-verify=off")
        .run();
    let object_bytes = rfs::read(native_dir.join("foo.o"));
    let object = run_make_support::object::File::parse(&*object_bytes).expect("native object");
    let exported: Vec<String> =
        object.symbols().filter_map(|symbol| symbol.name().ok().map(str::to_string)).collect();
    assert!(
        exported
            .iter()
            .any(|symbol| { symbol == add_symbol || symbol.strip_prefix('_') == Some(add_symbol) }),
        "the trust-ir name `{add_symbol}` must be the symbol the native object exports for \
         `add`: {exported:?}"
    );
    // MUTATION CONTROL: the def path itself is not a symbol the object exports.
    assert!(!exported.iter().any(|symbol| symbol == "add" || symbol == "_add"));

    // WS5.2 POSITIVE (roadmap `gen.rs`): two items sharing a leaf name in two modules are two
    // distinct v0 symbols, each exactly the native object's, each displaying its own def path.
    // NEGATIVE TWIN: the generic `id<T>` publishes NO definition — the module is monomorphic —
    // and the call at `id::<u32>` is a bodyless declaration; a closure inside a generic item
    // gets no symbol either and stays out of the module, refused by name in coverage.
    // RESIDUAL (WS5.2 NARROWED, docs/DECISION_QUEUE.md D17-DECL-SYMBOL-1): `id::<u32>` is a
    // generic instance of a local fn — the shape the frozen D17 instance lane appends — so its
    // declaration keeps the PRE-WS5.2 name, the bare def path `id`, with no display path and no
    // symbol: the one place `Function.name` is not yet the link-time symbol.
    rfs::write(
        "gen.rs",
        "pub mod a { pub fn same(x: u32) -> u32 { x.wrapping_add(1) } }\n\
         pub mod b { pub fn same(x: u32) -> u32 { x.wrapping_mul(2) } }\n\
         #[inline(never)] pub fn id<T>(x: T) -> T { x }\n\
         pub fn call_id(x: u32) -> u32 { id::<u32>(x) }\n\
         pub fn generic_parent<T>(_t: T) -> u32 { let c = |x: u32| x.wrapping_add(1); c(1) }\n",
    );
    let gen_dir = Path::new("gen-emit");
    rfs::create_dir(&gen_dir);
    rustc()
        .input("gen.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&gen_dir)
        .arg("-Ztrust-verify=off")
        .run();
    rustc()
        .input("gen.rs")
        .crate_type("lib")
        .emit("obj")
        .out_dir(&native_dir)
        .arg("-Ztrust-verify=off")
        .run();
    let gen_text = rfs::read_to_string(gen_dir.join("gen.trust-ir.txt"));
    let gen_bytes = rfs::read(native_dir.join("gen.o"));
    let gen_object = run_make_support::object::File::parse(&*gen_bytes).expect("native gen object");
    let gen_native: Vec<String> = gen_object
        .symbols()
        .filter(|symbol| symbol.is_definition())
        .filter_map(|symbol| symbol.name().ok().map(str::to_string))
        .collect();
    let defines = |name: &str| {
        gen_native.iter().any(|symbol| symbol == name || symbol.strip_prefix('_') == Some(name))
    };
    let a_same = named_by_display_path(&gen_text, "a::same");
    let b_same = named_by_display_path(&gen_text, "b::same");
    assert_ne!(a_same, b_same, "two items sharing a leaf are two link-time symbols");
    for symbol in [a_same, b_same] {
        assert!(defines(symbol), "`{symbol}` must be defined by the native object: {gen_native:?}");
    }
    let id_header = gen_text
        .lines()
        .find(|line| line.contains("fn @id("))
        .expect("the id::<u32> declaration keeps its pre-WS5.2 name `id`");
    let id_block = &gen_text[gen_text.find(id_header).unwrap()..];
    let id_block = &id_block[..id_block.find("\n}\n").unwrap()];
    assert!(
        !id_block.lines().any(|line| line.trim_start().starts_with("bb")),
        "the generic `id<T>` must publish no definition, only the instance's declaration:\n{id_block}"
    );
    assert!(
        !gen_text.contains("; #display-path: \"id\""),
        "the carved-out declaration carries no display path:\n{gen_text}"
    );
    assert!(!defines("id"), "the pre-WS5.2 name is not a symbol: {gen_native:?}");
    let gen_cov = rfs::read_to_string(gen_dir.join("gen.trust-ir.coverage.json"));
    let closure = body_row(&gen_cov, "generic_parent::{closure#0}");
    // Refused either as `symbolic` (its lowering mentions the parent's `T`) or, when it does
    // not, by the WS5.2 backstop `NoLinkTimeSymbol` — either way it is not in the module.
    assert!(closure.contains("\"spliced\": false"), "{closure}");
    assert!(
        closure.contains("\"symbolic\": true")
            || closure.contains("NoLinkTimeSymbol(generic_parent::{closure#0})"),
        "{closure}"
    );
    assert!(!gen_text.contains("; #display-path: \"generic_parent::{closure#0}\""), "{gen_text}");

    // `add` is inside the lowerable fragment: no unsupported shapes, hence no
    // leaf demand to explain.
    let add = body_row(&cov, "add");
    assert_eq!(array_field(add, "unsupported"), Some(""), "`add` must lower cleanly: {add}");
    assert_eq!(array_field(add, "collect_primary"), Some(""));

    // `evens` lowers, but its declared opaque return remains symbolic even
    // when typeck reveals the hidden Filter in the liberated THIR signature.
    // That provenance refuses splicing before the independent ZST-callable
    // check. The concrete-return twin below keeps the latter refusal tested.
    let evens = body_row(&cov, "evens");
    assert_eq!(
        array_field(evens, "unsupported"),
        Some(""),
        "`evens` no longer records unsupported shapes; if that regressed, the coverage \
         win this row pins has been lost: {evens}"
    );
    assert!(
        evens.contains("\"lowered\": true") && evens.contains("\"symbolic\": true"),
        "`evens` must retain its declared opaque return after lowering: {evens}"
    );
    assert!(
        evens.contains("\"spliced\": false")
            && evens.contains("\"splice_refusal\": \"Splice(symbolic body)\""),
        "`evens` must not splice while its declared opaque return is unsubstituted: {evens}"
    );

    // Trust: a call-bearing opaque row is deferred, but its seam entry must still be
    // refused. Its independent ZST-callable refusal must not mask lost declaration provenance.
    assert!(evens.contains("\"deferred_to_seam\": true"), "{evens}");
    assert!(
        evens.contains("\"seam\": { \"state\": \"resolved\", \"verdict\": \"not-run\""),
        "the deferred opaque entry must not gain seam agreement: {evens}"
    );
    assert!(!evens.contains("\"verdict\": \"agreed\""), "{evens}");
    assert!(evens.contains("declares an opaque return"), "{evens}");
    assert!(evens.contains("call args carry a ZST closure value"), "{evens}");

    let even_count = body_row(&cov, "even_count");
    assert_eq!(array_field(even_count, "unsupported"), Some(""), "{even_count}");
    assert!(even_count.contains("\"lowered\": true"), "{even_count}");
    assert!(even_count.contains("\"symbolic\": false"), "{even_count}");
    assert!(even_count.contains("\"spliced\": false"), "{even_count}");
    assert!(even_count.contains("Splice(zst callable stand-in argument)"), "{even_count}");
    assert!(!even_count.contains("declares an opaque return"), "{even_count}");

    // Trust: these opaque returns contain no callable stand-in, so only the declared
    // provenance can explain their classification and exclusion. The scalar/alias twins
    // ensure that concrete signatures are still compared and spliced.
    let opaque_dir = Path::new("opaque-emit");
    rfs::create_dir(&opaque_dir);
    rustc()
        .input("opaque_returns.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&opaque_dir)
        .arg("-Ztrust-verify=off")
        .run();
    let opaque_cov = rfs::read_to_string(opaque_dir.join("opaque_returns.trust-ir.coverage.json"));
    let opaque_text = rfs::read_to_string(opaque_dir.join("opaque_returns.trust-ir.txt"));
    for name in ["opaque_scalar", "opaque_tuple", "Returner::opaque_associated"] {
        let row = body_row(&opaque_cov, name);
        assert!(row.contains("\"lowered\": true"), "{row}");
        assert_eq!(array_field(row, "unsupported"), Some(""), "{row}");
        assert!(row.contains("\"symbolic\": true"), "{row}");
        assert!(row.contains("\"spliced\": false"), "{row}");
        assert!(row.contains("Splice(symbolic body)"), "{row}");
        assert!(row.contains("\"interpreter\": { \"verdict\": \"not-run\""), "{row}");
        assert!(row.contains("\"derived_mir\": { \"verdict\": \"unsupported\""), "{row}");
        assert!(row.contains("declares an opaque return"), "{row}");
        assert!(!row.contains("\"verdict\": \"agreed\""), "{row}");
        assert!(!row.contains("zst callable stand-in"), "{row}");
        assert!(!row.contains("function contains a direct call"), "{row}");
        assert!(!opaque_text.contains(&format!("; #display-path: {name:?}\n")), "{name}");
    }
    for name in ["plain_scalar", "concrete_alias"] {
        let row = body_row(&opaque_cov, name);
        assert!(row.contains("\"lowered\": true"), "{row}");
        assert!(row.contains("\"symbolic\": false"), "{row}");
        assert!(row.contains("\"spliced\": true"), "{row}");
        assert!(row.contains("\"interpreter\": { \"verdict\": \"agreed\""), "{row}");
        assert!(row.contains("\"derived_mir\": { \"verdict\": \"agreed\""), "{row}");
        named_by_display_path(&opaque_text, name);
    }
    // The closure body is a BodyTy::Fn too, but must never be sent to tcx.fn_sig.
    let closure = body_row(&opaque_cov, "closure_control::{closure#0}");
    assert!(closure.contains("\"symbolic\": false"), "{closure}");

    // `dyn_call` is outside the lowerable fragment (no static callee). Its
    // first-fail inventory and its collect-all leaf demand must BOTH be
    // published: the first-fail prefix attributes a whole subtree to one masking
    // tag, which is the entire reason the second histogram exists.
    let dyn_call = body_row(&cov, "dyn_call");
    assert_ne!(
        array_field(dyn_call, "unsupported"),
        Some(""),
        "`dyn_call` must record unsupported shapes: {dyn_call}"
    );
    let primary = array_field(dyn_call, "collect_primary")
        .expect("coverage row must carry a collect_primary field");
    assert!(
        !primary.is_empty(),
        "`dyn_call` failed to lower but published an EMPTY collect_primary histogram — the \
         collect-all measurement pass never ran for a pure `--emit=trust-ir` invocation, so the \
         artifact reports a failed body as demanding no leaf shapes: {dyn_call}"
    );

    // Analysis-only means no code generation; it does not mean deferred
    // verification. The first-class lane must still run borrow checking, and
    // must not publish an artifact for borrow-invalid source: a stale .bin/.txt
    // /.coverage.json left behind by a REJECTED compile is indistinguishable,
    // to every downstream consumer, from the artifact of a body that compiled.
    let rejected_dir = Path::new("borrow-invalid-emit");
    rfs::create_dir(&rejected_dir);
    rustc()
        .input("borrow_invalid.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&rejected_dir)
        .arg("-Ztrust-verify=off")
        .run_fail()
        .assert_stderr_contains("cannot borrow `value` as mutable more than once at a time");
    for name in [
        "borrow_invalid.trust-ir.bin",
        "borrow_invalid.trust-ir.txt",
        "borrow_invalid.trust-ir.coverage.json",
    ] {
        assert!(
            !rejected_dir.join(name).exists(),
            "borrow-invalid analysis published stale artifact `{name}`"
        );
    }
}
