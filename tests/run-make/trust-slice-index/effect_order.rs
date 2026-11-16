#![allow(dead_code, unused_assignments)]

pub fn reseat_through_alias<'a>(a: &'a [u8], b: &'a [u8], index: usize) -> u8 {
    let mut current = a;
    let alias = &mut current;
    current[{ *alias = b; index }]
}

fn choose<'a>(a: &'a [u8], b: &'a [u8], second: bool) -> &'a [u8] {
    if second { b } else { a }
}

pub fn call_base_is_captured<'a>(a: &'a [u8], b: &'a [u8], index: usize) -> u8 {
    let mut second = false;
    choose(a, b, second)[{ second = true; index }]
}

pub fn base_effect_precedes_index<'a>(a: &'a [u8], b: &'a [u8]) -> u8 {
    let mut index = 0;
    choose(a, b, { index = 1; true })[{ let old = index; index = 0; old }]
}

fn counted<'a>(bytes: &'a [u8], calls: &mut usize) -> &'a [u8] {
    *calls += 1;
    bytes
}

pub fn call_base_runs_once(bytes: &[u8]) -> u8 {
    let mut calls = 0;
    counted(bytes, &mut calls)[calls]
}
