// Trust: machine-applicable element types must resolve at the assertion site.
#![warn(clippy::assert_is_empty)]
#![allow(clippy::const_is_empty)]

mod model {
    #[derive(Debug, PartialEq)]
    pub struct Item;

    pub type Alias = Item;
}

mod nested {
    fn paths(items: Vec<crate::model::Item>, aliases: Vec<crate::model::Alias>, strings: Vec<String>) {
        assert!(items.is_empty());
        //~^ assert_is_empty
        assert!(!aliases.is_empty());
        //~^ assert_is_empty
        debug_assert!(strings.is_empty());
        //~^ assert_is_empty
    }

    fn local_type() {
        #[derive(Debug, PartialEq)]
        struct Local;

        let items = Vec::<Local>::new();
        assert!(items.is_empty());
        //~^ assert_is_empty
    }

    fn generic<T: std::fmt::Debug + PartialEq>(items: Vec<T>) {
        assert!(!items.is_empty());
        //~^ assert_is_empty
    }
}

fn main() {}
