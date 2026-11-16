use rustc_span::def_id::DefIndex;

use super::*;

// Trust: both bootstrap and current iterators preserve leaves, namespaces and order.
#[test]
fn use_tree_resolutions_preserve_nested_leaf_order_and_namespaces() {
    fn snapshot(tree: &UseTree<'_>) -> Vec<Vec<Option<Res>>> {
        tree.resolutions().map(|res| res.into_iter().collect()).collect()
    }
    let definition = Res::Def(DefKind::Mod, DefId::local(DefIndex::ZERO));
    let paths = [
        Path {
            span: DUMMY_SP,
            res: PerNS { type_ns: Some(definition), value_ns: None, macro_ns: None },
            segments: &[],
        },
        Path {
            span: DUMMY_SP,
            res: PerNS { type_ns: None, value_ns: Some(definition), macro_ns: Some(Res::Err) },
            segments: &[],
        },
        Path { span: DUMMY_SP, res: PerNS::default(), segments: &[] },
        Path {
            span: DUMMY_SP,
            res: PerNS { type_ns: Some(Res::Err), value_ns: None, macro_ns: Some(definition) },
            segments: &[],
        },
    ];
    let single = UseTree { prefix: &paths[0], kind: UseKind::Single(Ident::dummy()) };
    let glob = UseTree { prefix: &paths[1], kind: UseKind::Glob };
    let empty = UseTree { prefix: &paths[3], kind: UseKind::Nested { items: &[] } };
    assert!(snapshot(&empty).is_empty());
    assert_eq!(snapshot(&single), [paths[0].res.into_iter().collect::<Vec<_>>()]);
    assert_eq!(snapshot(&glob), [paths[1].res.into_iter().collect::<Vec<_>>()]);

    let id = LocalDefId { local_def_index: DefIndex::ZERO };
    let inner = [
        (glob, HirId::INVALID, id),
        (empty, HirId::INVALID, id),
        (UseTree { prefix: &paths[2], kind: UseKind::Single(Ident::dummy()) }, HirId::INVALID, id),
    ];
    let outer = [
        (single, HirId::INVALID, id),
        (
            UseTree { prefix: &paths[3], kind: UseKind::Nested { items: &inner } },
            HirId::INVALID,
            id,
        ),
        (UseTree { prefix: &paths[3], kind: UseKind::Glob }, HirId::INVALID, id),
    ];
    let tree = UseTree { prefix: &paths[3], kind: UseKind::Nested { items: &outer } };
    let expected: Vec<_> =
        paths.iter().map(|path| path.res.into_iter().collect::<Vec<_>>()).collect();
    assert_eq!(snapshot(&tree), expected);
}

#[test]
fn use_tree_resolutions_keep_leaf_order_and_duplicates() {
    let path = |primitive| Path {
        span: DUMMY_SP,
        res: PerNS {
            type_ns: Some(Res::PrimTy(primitive)),
            value_ns: Some(Res::Err),
            macro_ns: None,
        },
        segments: &[],
    };
    let bool_path = path(PrimTy::Bool);
    let char_path = path(PrimTy::Char);
    let str_path = path(PrimTy::Str);
    let row = |tree| (tree, HirId::INVALID, LocalDefId { local_def_index: DefIndex::ZERO });
    let deepest = [row(UseTree { prefix: &str_path, kind: UseKind::Glob })];
    let middle = [
        row(UseTree { prefix: &char_path, kind: UseKind::Single(Ident::new(sym::name, DUMMY_SP)) }),
        row(UseTree { prefix: &bool_path, kind: UseKind::Nested { items: &deepest } }),
        row(UseTree { prefix: &bool_path, kind: UseKind::Nested { items: &[] } }),
    ];
    let items = [
        row(UseTree { prefix: &bool_path, kind: UseKind::Glob }),
        row(UseTree { prefix: &bool_path, kind: UseKind::Nested { items: &middle } }),
        row(UseTree { prefix: &bool_path, kind: UseKind::Single(Ident::new(sym::name, DUMMY_SP)) }),
    ];
    let tree = UseTree { prefix: &bool_path, kind: UseKind::Nested { items: &items } };
    let resolutions: Vec<_> =
        tree.resolutions().map(|res| [res.type_ns, res.value_ns, res.macro_ns]).collect();
    let expected = [PrimTy::Bool, PrimTy::Char, PrimTy::Str, PrimTy::Bool]
        .map(|primitive| [Some(Res::PrimTy(primitive)), Some(Res::Err), None]);
    assert_eq!(resolutions, expected);
}

macro_rules! define_tests {
    ($($name:ident $kind:ident $variant:ident {$($init:tt)*})*) => {$(
        #[test]
        fn $name() {
            let unambig = $kind::$variant::<'_, ()> { $($init)* };
            let unambig_to_ambig = unsafe { std::mem::transmute::<_, $kind<'_, AmbigArg>>(unambig) };

            assert!(matches!(&unambig_to_ambig, &$kind::$variant { $($init)* }));

            let ambig_to_unambig = unsafe { std::mem::transmute::<_, $kind<'_, ()>>(unambig_to_ambig) };

            assert!(matches!(&ambig_to_unambig, &$kind::$variant { $($init)* }));
        }
    )*};
}

define_tests! {
    cast_never TyKind Never {}
    cast_tup TyKind Tup { 0: &[Ty { span: DUMMY_SP, hir_id: HirId::INVALID, kind: TyKind::Never }] }
    cast_ptr TyKind Ptr { 0: &Ty { span: DUMMY_SP, hir_id: HirId::INVALID, kind: TyKind::Never }, 1: Mutability::Not }
    cast_array TyKind Array {
        0: &Ty { span: DUMMY_SP, hir_id: HirId::INVALID, kind: TyKind::Never },
        1: &ConstArg {
            hir_id: HirId::INVALID,
            kind: ConstArgKind::Anon(&AnonConst {
                hir_id: HirId::INVALID,
                def_id: LocalDefId { local_def_index: DefIndex::ZERO },
                body: BodyId { hir_id: HirId::INVALID },
                span: DUMMY_SP,
            }),
            span: DUMMY_SP,
        },
    }

    cast_anon ConstArgKind Anon {
        0: &AnonConst {
            hir_id: HirId::INVALID,
            def_id: LocalDefId { local_def_index: DefIndex::ZERO },
            body: BodyId { hir_id: HirId::INVALID },
            span: DUMMY_SP,
        }
    }
}

#[test]
fn trait_object_roundtrips() {
    trait_object_roundtrips_impl(TraitObjectSyntax::Dyn);
    trait_object_roundtrips_impl(TraitObjectSyntax::None);
}

fn trait_object_roundtrips_impl(syntax: TraitObjectSyntax) {
    let lt = Lifetime {
        hir_id: HirId::INVALID,
        ident: Ident::new(sym::name, DUMMY_SP),
        kind: LifetimeKind::Static,
        source: LifetimeSource::Other,
        syntax: LifetimeSyntax::Implicit,
    };
    let unambig = TyKind::TraitObject::<'_, ()>(&[], TaggedRef::new(&lt, syntax));
    let unambig_to_ambig = unsafe { std::mem::transmute::<_, TyKind<'_, AmbigArg>>(unambig) };

    match unambig_to_ambig {
        TyKind::TraitObject(_, tagged_ref) => {
            assert!(tagged_ref.tag() == syntax)
        }
        _ => panic!("`TyKind::TraitObject` did not roundtrip"),
    };

    let ambig_to_unambig = unsafe { std::mem::transmute::<_, TyKind<'_, ()>>(unambig_to_ambig) };

    match ambig_to_unambig {
        TyKind::TraitObject(_, tagged_ref) => {
            assert!(tagged_ref.tag() == syntax)
        }
        _ => panic!("`TyKind::TraitObject` did not roundtrip"),
    };
}

// Trust: the coroutine-free seed bridge must preserve import traversal and
// the auto traits exposed through its opaque iterator return type.
mod use_tree_resolutions {
    use super::*;

    fn path(mask: u8) -> UsePath<'static> {
        Path {
            span: DUMMY_SP,
            res: PerNS {
                value_ns: (mask & 1 != 0).then_some(Res::Err),
                type_ns: (mask & 2 != 0).then_some(Res::Err),
                macro_ns: (mask & 4 != 0).then_some(Res::Err),
            },
            segments: &[],
        }
    }

    fn entries(res: PerNS<Option<Res>>) -> [Option<Res>; 3] {
        [res.value_ns, res.type_ns, res.macro_ns]
    }

    fn child(tree: UseTree<'_>) -> (UseTree<'_>, HirId, LocalDefId) {
        (tree, HirId::INVALID, LocalDefId { local_def_index: DefIndex::ZERO })
    }

    #[test]
    fn single_and_glob_preserve_every_namespace() {
        for mask in 0..8 {
            let prefix = path(mask);
            for kind in [UseKind::Single(Ident::dummy()), UseKind::Glob] {
                let tree = UseTree { prefix: &prefix, kind };
                assert_eq!(
                    tree.resolutions().map(entries).collect::<Vec<_>>(),
                    [entries(prefix.res)]
                );
            }
        }
    }

    #[test]
    fn empty_nested_group_emits_no_prefix() {
        let prefix = path(7);
        let tree = UseTree { prefix: &prefix, kind: UseKind::Nested { items: &[] } };
        assert!(tree.resolutions().next().is_none());
    }

    #[test]
    fn nested_groups_keep_depth_first_source_order() {
        let prefixes = [path(0), path(1), path(2), path(4), path(7)];
        let empty = UseTree { prefix: &prefixes[4], kind: UseKind::Nested { items: &[] } };
        let inner = [
            child(UseTree { prefix: &prefixes[1], kind: UseKind::Single(Ident::dummy()) }),
            child(empty),
            child(UseTree { prefix: &prefixes[2], kind: UseKind::Glob }),
        ];
        let branch = UseTree { prefix: &prefixes[4], kind: UseKind::Nested { items: &inner } };
        let outer = [
            child(empty),
            child(branch),
            child(branch),
            child(UseTree { prefix: &prefixes[3], kind: UseKind::Glob }),
            child(UseTree { prefix: &prefixes[0], kind: UseKind::Single(Ident::dummy()) }),
        ];
        let tree = UseTree { prefix: &prefixes[4], kind: UseKind::Nested { items: &outer } };
        let expected = [1, 2, 1, 2, 3, 0].map(|index| entries(prefixes[index].res));
        assert_eq!(tree.resolutions().map(entries).collect::<Vec<_>>(), expected);
    }

    #[test]
    fn opaque_iterator_preserves_auto_traits() {
        fn assert_auto_traits(_: impl Send + Sync + Unpin) {}
        let prefix = path(0);
        let tree = UseTree { prefix: &prefix, kind: UseKind::Glob };
        assert_auto_traits(tree.resolutions());
    }
}
