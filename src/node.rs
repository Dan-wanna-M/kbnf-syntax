use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use serde::Serialize;
use string_interner::symbol::SymbolU32;

#[derive(Debug, Clone, Serialize)]
pub enum Node {
    Terminal(String),
    RegexString(String),
    Nonterminal(String),
    Multiple(Vec<Node>),
    RegexExt(Box<Node>, RegexExtKind),
    Symbol(Box<Node>, SymbolKind, Box<Node>),
    Group(Box<Node>),
    EXCEPT(Excepted, Option<usize>),
}
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub enum NodeWithID {
    Terminal(SymbolU32),
    RegexString(SymbolU32),
    Nonterminal(SymbolU32),
    Multiple(Vec<NodeWithID>),
    RegexExt(Box<NodeWithID>, RegexExtKind),
    Symbol(Box<NodeWithID>, SymbolKind, Box<NodeWithID>),
    Group(Box<NodeWithID>),
    EXCEPT(ExceptedWithID, Option<usize>),
    Unknown,
}
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone)]
pub(crate) enum NoNestingNode {
    Unknown,
    Terminal(SymbolU32),
    RegexString(SymbolU32),
    Nonterminal(SymbolU32),
    Concatenations(Vec<NoNestingNode>),
    Alternations(Vec<NoNestingNode>),
    EXCEPT(ExceptedWithID, Option<usize>),
}
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum OperatorFlattenedNode {
    Terminal(SymbolU32),
    RegexString(SymbolU32),
    Nonterminal(SymbolU32),
    EXCEPT(ExceptedWithID, Option<usize>),
}
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum FinalNode {
    Terminal(SymbolU32),
    RegexString(SymbolU32),
    Nonterminal(SymbolU32),
    EXCEPT(SymbolU32, Option<usize>),
}
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Rhs {
    pub alternations: Vec<Alternation>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Alternation {
    pub concatenations: Vec<OperatorFlattenedNode>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct FinalRhs {
    pub alternations: Vec<FinalAlternation>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct FinalAlternation {
    pub concatenations: Vec<FinalNode>,
}
#[derive(Debug, Clone, Serialize)]
pub enum Excepted {
    Terminal(String),
    Nonterminal(String),
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ExceptedWithID {
    Terminal(SymbolU32),
    Nonterminal(SymbolU32),
}

#[derive(Debug, Clone, Serialize, Copy, PartialEq, Eq, Hash)]
pub enum RegexExtKind {
    Repeat0,
    Repeat1,
    Optional,
}

#[derive(Debug, Clone, Serialize)]
pub enum SymbolKind {
    Concatenation,
    Alternation,
}
