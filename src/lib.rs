//! ebnf - A successor bnf parsing library of bnf parsing library, for parsing Extended Backus–Naur form context-free grammars
//!
//! The code is available on [GitHub](https://github.com/ChAoSUnItY/ebnf)
//!
//! ## Disclaimer:
//! There are various variants of EBNF, which uses somewhat different syntactic conventions. This library
//! takes [EBNF Evaluator](https://mdkrajnak.github.io/ebnftest/)'s example code as standard, which has
//! almost most syntactic conventions on Wikipedia's page.
//!
//! ## What does a valid EBNF grammar looks like?
//!
//! The following example is taken from EBNF Evaluator:
//!
//! ```ebnf
//! filter ::= ( first ' ' )? ( number '~ ' )? ( number '-' number ) ( ' ' number '~' )? ( ' hz' )? ( ' b' )? ( ' i' )? ( ' a' )?;
//! first  ::= #'[a-za-z][a-za-z0-9_+]*';
//! number ::= digits ( ( '.' | ',' ) digits? )?;
//! digits ::= #'[0-9]+';
//! ```
//!
//! ## How to use this library?
//!
//! ```rust
//! extern crate kbnf_syntax;
//!
//! fn main() {
//!     let source = r"
//!         filter ::= ( first ' ' )? ( number '~ ' )? ( number '-' number ) ( ' ' number '~' )? ( ' hz' )? ( ' b' )? ( ' i' )? ( ' a' )?;
//!         first  ::= #'[a-za-z][a-za-z0-9_+]*';
//!         number ::= digits ( ( '.' | ',' ) digits? )?;
//!         digits ::= #'[0-9]+';
//!     ";
//!
//!     let result = kbnf_syntax::get_grammar(source);
//! }
//! ```

extern crate alloc;
extern crate nom;
extern crate parse_hyperlinks;
use std::{iter::zip, mem};

use expression::{Expression, ExpressionWithID};
pub use grammar::Grammar;
use node::NodeWithID;
pub use node::{Node, RegexExtKind, SymbolKind};
use string_interner::{backend::StringBackend, symbol::SymbolU32, StringInterner};

pub mod config;
mod expression;
pub mod grammar;
pub mod node;
mod parser;
pub mod regex;
pub mod semantic_error;
pub mod simplified_grammar;
pub mod utils;
pub mod validated_grammar;

#[derive(Debug, Clone)]
pub struct InternedStrings {
    pub nonterminals: StringInterner<StringBackend<SymbolU32>>,
    pub terminals: StringInterner<StringBackend<SymbolU32>>,
    pub regex_strings: StringInterner<StringBackend<SymbolU32>>,
    pub sub_strings: StringInterner<StringBackend<SymbolU32>>,
}

/// Get and parse EBNF grammar source into [Grammar], returns [Err] when given grammar is invalid.
///
/// # Example
///
/// ```rust
/// use kbnf_syntax::get_grammar;
///
/// let grammar_literal = r"
///     term ::= '1';
/// ";
/// let grammar = get_grammar(grammar_literal)?;
///
/// # Ok::<(), nom::Err<nom::error::VerboseError<&str>>>(())
/// ```
pub fn get_grammar(input: &str) -> Result<Grammar, nom::Err<nom::error::VerboseError<&str>>> {
    let (interned_strings, expressions) = intern_strings(parser::parse_expressions(input)?.1);
    Ok(Grammar {
        interned_strings,
        expressions,
    })
}

fn intern_strings(expressions: Vec<Expression>) -> (InternedStrings, Vec<ExpressionWithID>) {
    let mut nonterminals = StringInterner::<StringBackend<SymbolU32>>::new();
    let mut terminals = StringInterner::<StringBackend<SymbolU32>>::new();
    let mut regex_strings = StringInterner::<StringBackend<SymbolU32>>::new();
    let mut sub_strings = StringInterner::<StringBackend<SymbolU32>>::new();
    let mut new_expressions = vec![];
    for expression in expressions {
        let lhs = nonterminals.get_or_intern(expression.lhs);
        let mut rhs = NodeWithID::Unknown;
        let node = expression.rhs;
        let mut stack = vec![(node, &mut rhs)];
        while let Some((mut node, parent)) = stack.pop() {
            match &mut node {
                Node::Terminal(terminal) => {
                    let terminal = std::mem::take(terminal);
                    *parent = NodeWithID::Terminal(terminals.get_or_intern(&terminal));
                }
                Node::RegexString(regex_string) => {
                    let regex_string = std::mem::take(regex_string);
                    *parent = NodeWithID::RegexString(regex_strings.get_or_intern(&regex_string));
                }
                Node::EarlyEndRegexString(regex_string) => {
                    let regex_string = std::mem::take(regex_string);
                    *parent =
                        NodeWithID::EarlyEndRegexString(regex_strings.get_or_intern(&regex_string));
                }
                Node::Substrings(substrings) => {
                    let substrings = std::mem::take(substrings);
                    *parent = NodeWithID::Substrings(sub_strings.get_or_intern(&substrings));
                }
                Node::Nonterminal(nonterminal) => {
                    let nonterminal = std::mem::take(nonterminal);
                    *parent = NodeWithID::Nonterminal(nonterminals.get_or_intern(&nonterminal));
                }
                Node::Multiple(nodes) => {
                    let nodes = std::mem::take(nodes);
                    let mut buffer = Vec::with_capacity(nodes.len());
                    buffer.resize(nodes.len(), NodeWithID::Unknown);
                    *parent = NodeWithID::Multiple(buffer);
                    match parent {
                        NodeWithID::Multiple(new_nodes) => {
                            for (node, new_parent) in zip(nodes, new_nodes.iter_mut()) {
                                stack.push((node, new_parent));
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                Node::RegexExt(node, e) => {
                    let node = mem::replace(node, Box::new(Node::Terminal(String::new())));
                    *parent = NodeWithID::RegexExt(Box::new(NodeWithID::Unknown), *e);
                    match parent {
                        NodeWithID::RegexExt(new_node, _) => {
                            stack.push((*node, new_node));
                        }
                        _ => unreachable!(),
                    }
                }
                Node::Symbol(lhs, symbol, rhs) => {
                    let lhs = mem::replace(lhs, Box::new(Node::Terminal(String::new())));
                    // SAFETY: The `mem::forget(node)` after the match ensures we do not double free the rhs box
                    let rhs = mem::replace(rhs, Box::new(Node::Terminal(String::new())));
                    *parent = NodeWithID::Symbol(
                        Box::new(NodeWithID::Unknown),
                        *symbol,
                        Box::new(NodeWithID::Unknown),
                    );
                    match parent {
                        NodeWithID::Symbol(l, _, r) => {
                            stack.push((*lhs, l));
                            stack.push((*rhs, r));
                        }
                        _ => unreachable!(),
                    }
                }
                Node::Group(node) => {
                    let node = mem::replace(node, Box::new(Node::Terminal(String::new())));
                    *parent = NodeWithID::Group(Box::new(NodeWithID::Unknown));
                    match parent {
                        NodeWithID::Group(new_node) => {
                            stack.push((*node, new_node));
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
        new_expressions.push((lhs, rhs));
    }
    (
        InternedStrings {
            nonterminals,
            terminals,
            regex_strings,
            sub_strings,
        },
        new_expressions
            .into_iter()
            .map(|(lhs, rhs)| ExpressionWithID { lhs, rhs })
            .collect(),
    )
}
