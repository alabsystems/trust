use super::*;
use crate::context::Definition;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;

fn environment(entries: &[(&OsStr, &OsStr)]) -> [u8; 32] {
    let mut encoding = Encoding::new(b"environment-test").unwrap();
    encoding.environment(entries.iter().copied()).unwrap();
    encoding.finish()
}

#[test]
fn non_unicode_environment_bytes_and_empty_values_are_not_dropped() {
    let key = OsString::from_vec(b"NATIVE_\xff".to_vec());
    let before = OsString::from_vec(b"value_\xfe".to_vec());
    let after = OsString::from_vec(b"value_\xff".to_vec());
    let absent = environment(&[]);
    let one = environment(&[(&key, &before)]);
    assert_ne!(absent, one);
    assert_ne!(one, environment(&[(&key, &after)]));
    assert_ne!(
        absent,
        environment(&[(OsStr::new("EMPTY"), OsStr::new(""))])
    );
    let ordinary = (OsStr::new("ORDINARY"), OsStr::new("selected"));
    assert_eq!(
        environment(&[ordinary, (&key, &before)]),
        environment(&[(&key, &before), ordinary])
    );
}

#[test]
fn transport_named_values_are_still_observable_compiler_inputs() {
    assert_ne!(
        environment(&[(
            OsStr::new("CARGO_MAKEFLAGS"),
            OsStr::new("--jobserver-auth=6,7")
        )]),
        environment(&[(
            OsStr::new("CARGO_MAKEFLAGS"),
            OsStr::new("--jobserver-auth=8,9")
        )]),
    );
}

#[test]
fn length_delimiters_and_typed_configuration_preserve_distinct_inputs() {
    let finish = |parts: &[&[u8]]| {
        let mut encoding = Encoding::new(b"parts").unwrap();
        for part in parts {
            encoding.bytes(part).unwrap();
        }
        encoding.finish()
    };
    assert_ne!(finish(&[b"ab", b"c"]), finish(&[b"a", b"bc"]));
    let config = |value| {
        let mut encoding = Encoding::new(b"config").unwrap();
        encoding.value(&value, 0).unwrap();
        encoding.finish()
    };
    assert_ne!(
        config(ConfigValue::String("1".into(), Definition::BuiltIn)),
        config(ConfigValue::Integer(1, Definition::BuiltIn))
    );
    assert_ne!(
        config(ConfigValue::String(
            "relative/tool".into(),
            Definition::Path("/first/.cargo/config.toml".into())
        )),
        config(ConfigValue::String(
            "relative/tool".into(),
            Definition::Path("/second/.cargo/config.toml".into())
        ))
    );
}

#[test]
fn untrusted_configuration_limits_refuse_before_unbounded_population_copy() {
    let mut bytes = Encoding::new(b"limits").unwrap();
    assert!(bytes.bytes(&vec![0; MAX_BYTES]).is_err());
    let entries = (OsStr::new("key"), OsStr::new("value"));
    let mut environment = Encoding::new(b"limits").unwrap();
    assert!(
        environment
            .environment(std::iter::repeat_n(entries, MAX_ENTRIES + 1))
            .is_err()
    );
    let mut value = ConfigValue::Boolean(true, Definition::BuiltIn);
    for _ in 0..MAX_DEPTH {
        value = ConfigValue::List(vec![value], Definition::BuiltIn);
    }
    assert!(Encoding::new(b"limits").unwrap().value(&value, 0).is_ok());
    value = ConfigValue::List(vec![value], Definition::BuiltIn);
    assert!(Encoding::new(b"limits").unwrap().value(&value, 0).is_err());
    let wide = ConfigValue::List(
        vec![ConfigValue::Boolean(true, Definition::BuiltIn); MAX_ENTRIES],
        Definition::BuiltIn,
    );
    assert!(Encoding::new(b"limits").unwrap().value(&wide, 0).is_err());
}

#[test]
fn oversized_feature_name_and_escaped_unit_identity_refuse_without_json_vector() {
    let features = BTreeSet::from(["x".repeat(MAX_BYTES)]);
    assert!(
        Encoding::new(b"features")
            .unwrap()
            .features(Some(&features))
            .is_err()
    );
    let mut absent = Encoding::new(b"features").unwrap();
    absent.features(None).unwrap();
    let mut empty = Encoding::new(b"features").unwrap();
    empty.features(Some(&BTreeSet::new())).unwrap();
    assert_ne!(absent.finish(), empty.finish());
    let mut sink = LimitedSink(16);
    assert!(serde_json::to_writer(&mut sink, &"\n".repeat(16)).is_err());
}

#[test]
fn complete_graph_preflight_refuses_cycles_dangling_edges_depth_and_multiplicity() {
    // Same child reached through multiple parents and parallel edges is valid.
    graph_depth(&[vec![1, 2, 1], vec![3], vec![3], vec![]]).unwrap();
    assert!(graph_depth(&[vec![1], vec![0]]).is_err());
    assert!(graph_depth(&[vec![1]]).is_err());
    assert!(graph_depth(&[vec![0; MAX_EDGES + 1]]).is_err());
    let chain = |length: usize| {
        (0..length)
            .map(|index| {
                if index + 1 < length {
                    vec![index + 1]
                } else {
                    Vec::new()
                }
            })
            .collect::<Vec<_>>()
    };
    graph_depth(&chain(MAX_GRAPH_DEPTH)).unwrap();
    assert!(graph_depth(&chain(MAX_GRAPH_DEPTH + 1)).is_err());
    assert!(graph_depth(&vec![Vec::new(); MAX_UNITS + 1]).is_err());
    // A previously visited short path must not conceal a later longer path.
    assert!(
        graph_depth(&{
            let mut graph = chain(MAX_GRAPH_DEPTH + 1);
            graph.reverse();
            for children in &mut graph {
                for child in children {
                    *child = MAX_GRAPH_DEPTH - *child;
                }
            }
            graph
        })
        .is_err()
    );
}
