use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use serde::Serialize;
use std::mem;
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
    EarlyEndRegexString(String),
}

impl Drop for Node {
    fn drop(&mut self) {
        let mut stack = vec![];
        match self {
            Node::Terminal(_) | Node::RegexString(_) | Node::Nonterminal(_) => {}
            Node::Multiple(nodes) => {
                while let Some(node) = nodes.pop() {
                    stack.push(node);
                }
            }
            Node::RegexExt(node, _) => {
                let node = mem::replace(node.as_mut(), Node::Terminal(String::new()));
                stack.push(node);
            }
            Node::Symbol(lhs, _, rhs) => {
                let lhs = mem::replace(lhs.as_mut(), Node::Terminal(String::new()));
                let rhs = mem::replace(rhs.as_mut(), Node::Terminal(String::new()));
                stack.push(lhs);
                stack.push(rhs);
            }
            Node::Group(node) => {
                let node = mem::replace(node.as_mut(), Node::Terminal(String::new()));
                stack.push(node);
            }
            Node::EarlyEndRegexString(_) => {}
        };
        while let Some(mut node) = stack.pop() {
            match &mut node {
                Node::Multiple(nodes) => {
                    while let Some(node) = nodes.pop() {
                        stack.push(node);
                    }
                }
                Node::RegexExt(node, _) => {
                    let node = mem::replace(node.as_mut(), Node::Terminal(String::new()));
                    stack.push(node);
                }
                Node::Symbol(lhs, _, rhs) => {
                    let lhs = mem::replace(lhs.as_mut(), Node::Terminal(String::new()));
                    let rhs = mem::replace(rhs.as_mut(), Node::Terminal(String::new()));
                    stack.push(lhs);
                    stack.push(rhs);
                }
                Node::Group(node) => {
                    let node = mem::replace(node.as_mut(), Node::Terminal(String::new()));
                    stack.push(node);
                }
                _ => {}
            }
        }
    }
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
    EarlyEndRegexString(SymbolU32),
    Unknown,
}

impl Drop for NodeWithID {
    fn drop(&mut self) {
        let mut stack = vec![];
        match self {
            NodeWithID::Terminal(_) | NodeWithID::RegexString(_) | NodeWithID::Nonterminal(_) => {}
            NodeWithID::Multiple(nodes) => {
                while let Some(node) = nodes.pop() {
                    stack.push(node);
                }
            }
            NodeWithID::RegexExt(node, _) => {
                let node = mem::replace(node.as_mut(), NodeWithID::Unknown);
                stack.push(node);
            }
            NodeWithID::Symbol(lhs, _, rhs) => {
                let lhs = mem::replace(lhs.as_mut(), NodeWithID::Unknown);
                let rhs = mem::replace(rhs.as_mut(), NodeWithID::Unknown);
                stack.push(lhs);
                stack.push(rhs);
            }
            NodeWithID::Group(node) => {
                let node = mem::replace(node.as_mut(), NodeWithID::Unknown);
                stack.push(node);
            }
            NodeWithID::EarlyEndRegexString(_) => {}
            NodeWithID::Unknown => {}
        };
        while let Some(mut node) = stack.pop() {
            match &mut node {
                NodeWithID::Multiple(nodes) => {
                    while let Some(node) = nodes.pop() {
                        stack.push(node);
                    }
                }
                NodeWithID::RegexExt(node, _) => {
                    let node = mem::replace(node.as_mut(), NodeWithID::Unknown);
                    stack.push(node);
                }
                NodeWithID::Symbol(lhs, _, rhs) => {
                    let lhs = mem::replace(lhs.as_mut(), NodeWithID::Unknown);
                    let rhs = mem::replace(rhs.as_mut(), NodeWithID::Unknown);
                    stack.push(lhs);
                    stack.push(rhs);
                }
                NodeWithID::Group(node) => {
                    let node = mem::replace(node.as_mut(), NodeWithID::Unknown);
                    stack.push(node);
                }
                _ => {}
            }
        }
    }
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
    EarlyEndRegexString(SymbolU32),
}
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum OperatorFlattenedNode {
    Terminal(SymbolU32),
    RegexString(SymbolU32),
    Nonterminal(SymbolU32),
    EarlyEndRegexString(SymbolU32),
}
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Rhs {
    pub alternations: Vec<Alternation>,
}
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Alternation {
    pub concatenations: Vec<OperatorFlattenedNode>,
}
#[derive(Debug, Clone, Serialize, Copy, PartialEq, Eq, Hash)]
pub enum RegexExtKind {
    Repeat0,
    Repeat1,
    Optional,
}

#[derive(Debug, Clone, Serialize, Copy)]
pub enum SymbolKind {
    Concatenation,
    Alternation,
}
