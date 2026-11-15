// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

#![feature(ergonomic_clones)]

pub enum Node {
    End,
    Next(Box<Node>),
}

pub fn fold(n: &Node) -> i64 {
    match n {
        Node::End => 0,
        Node::Next(child) => 1 + fold(child),
    }
}

pub fn one() -> i64 {
    fold(&Node::Next(Box::new(Node::End)))
}
pub fn two() -> i64 {
    fold(&Node::Next(Box::new(Node::Next(Box::new(Node::End)))))
}

// Distinct source instantiations have EXACTLY the same erased signature.
pub fn same_abi<T>(x: i64) -> i64 {
    x
}

pub trait Predicate {
    fn pred(&self) -> bool;
}
pub struct Yes;
pub struct No;
impl Predicate for Yes {
    fn pred(&self) -> bool {
        true
    }
}
impl Predicate for No {
    fn pred(&self) -> bool {
        false
    }
}
pub fn yes() -> bool {
    Yes.pred()
}
pub fn no() -> bool {
    No.pred()
}

pub enum Other {
    End,
    Next(Box<Other>),
}
pub fn other_fold(n: &Other) -> i64 {
    match n {
        Other::End => 0,
        Other::Next(child) => 1 + other_fold(child),
    }
}
pub fn other() -> i64 {
    other_fold(&Other::Next(Box::new(Other::End)))
}

pub fn borrowed<'a>(x: &'a i64) -> i64 {
    *x
}
pub fn borrow_chain<'a>(x: &'a i64) -> i64 {
    borrowed(x)
}

pub fn identity<T>(x: T) -> T {
    x
}
pub fn generic_chain<T>(x: T) -> T {
    identity(x)
}

pub trait Associated {
    type Item;
}
pub struct AliasOwner;
impl Associated for AliasOwner {
    type Item = i64;
}
pub fn associated<T: Associated>(x: T::Item) -> T::Item {
    x
}
pub fn concrete_alias(x: i64) -> i64 {
    associated::<AliasOwner>(x)
}

pub fn signed_pattern(x: i64) -> i64 {
    match x {
        -7 => 17,
        0 => 23,
        _ => 31,
    }
}

pub fn explicit_use(x: i64) -> i64 {
    x.use
}
