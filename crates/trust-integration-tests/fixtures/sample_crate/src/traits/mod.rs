// Trait definitions and dynamic dispatch.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub trait Describable {
    fn describe(&self) -> String;
}

pub fn describe_item(item: &dyn Describable) -> String {
    item.describe()
}

pub fn describe_all(items: &[&dyn Describable]) -> Vec<String> {
    items.iter().map(|i| i.describe()).collect()
}

pub trait Area {
    fn area(&self) -> f64;
}

pub fn total_area(shapes: &[Box<dyn Area>]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

pub fn largest_area(shapes: &[Box<dyn Area>]) -> f64 {
    shapes.iter().map(|s| s.area()).fold(0.0_f64, f64::max)
}

pub trait Validator {
    fn validate(&self, input: &str) -> bool;
}

pub fn validate_all(validators: &[&dyn Validator], input: &str) -> bool {
    validators.iter().all(|v| v.validate(input))
}

pub fn validate_any(validators: &[&dyn Validator], input: &str) -> bool {
    validators.iter().any(|v| v.validate(input))
}
