pub mod config {
    pub trait ConfigType: Sized {
        fn doc_hint() -> String;
        fn stable_variant(&self) -> bool;
    }
}

#[allow(dead_code)]
#[allow(unused_imports)]
mod tests {
    use rustfmt_config_proc_macro::config_type;

    #[config_type]
    enum Bar {
        Foo,
        Bar,
        #[doc_hint = "foo_bar"]
        FooBar,
        FooFoo(i32),
        Named {
            value: i32,
        },
    }

    #[test]
    fn display_is_total_without_erasing_payload_shape() {
        assert_eq!(Bar::Foo.to_string(), "Foo");
        assert_eq!(Bar::FooFoo(7).to_string(), "FooFoo(..)");
        assert_eq!(Bar::Named { value: 9 }.to_string(), "Named { .. }");
    }

    #[test]
    fn serialization_rejects_payload_bearing_variants_instead_of_erasing_fields() {
        assert_eq!(serde_json::to_string(&Bar::Foo).unwrap(), r#""Foo""#);

        for value in [Bar::FooFoo(7), Bar::Named { value: 9 }] {
            let error = serde_json::to_string(&value).unwrap_err().to_string();
            assert!(
                error.contains("cannot serialize payload-bearing configuration variant"),
                "unexpected serialization error: {error}",
            );
        }
    }
}
