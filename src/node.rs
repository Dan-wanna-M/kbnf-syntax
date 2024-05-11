use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub enum Node {
    Terminal(String),
    RegexString(String),
    Nonterminal(String),
    Multiple(Vec<Node>),
    RegexExt(Box<Node>, RegexExtKind),
    Symbol(Box<Node>, SymbolKind, Box<Node>),
    Group(Box<Node>),
    ANY,
    EXCEPT(Excepted, Option<usize>)
}

#[derive(Debug, Clone, Serialize)]
pub(crate) enum NoNestingNode {
    Unknown,
    Terminal(String),
    RegexString(String),
    Nonterminal(String),
    Concatenations(Vec<NoNestingNode>),
    Alternations(Vec<NoNestingNode>),
    ANY,
    EXCEPT(Excepted, Option<usize>)
}

#[derive(Debug, Clone, Serialize)]
pub(crate) enum OperatorFlattenedNode {
    Terminal(String),
    RegexString(String),
    Nonterminal(String),
    ANY,
    EXCEPT(Excepted, Option<usize>)
}
#[derive(Debug, Clone, Serialize)]
pub(crate) struct RHS
{
    pub altercations:Vec<Alternation>,
}
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Alternation
{
    pub concatenations:Vec<OperatorFlattenedNode>
}

#[derive(Debug, Clone, Serialize)]
pub enum Excepted
{
    Terminal(String),
    Nonterminal(String)
}

#[derive(Debug, Clone, Serialize)]
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
