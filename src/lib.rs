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
//! extern crate ebnf;
//!
//! fn main() {
//!     let source = r"
//!         filter ::= ( first ' ' )? ( number '~ ' )? ( number '-' number ) ( ' ' number '~' )? ( ' hz' )? ( ' b' )? ( ' i' )? ( ' a' )?;
//!         first  ::= #'[a-za-z][a-za-z0-9_+]*';
//!         number ::= digits ( ( '.' | ',' ) digits? )?;
//!         digits ::= #'[0-9]+';
//!     ";
//!
//!     let result = ebnf::get_grammar(source);
//! }
//! ```

extern crate alloc;
extern crate nom;
extern crate parse_hyperlinks;

use std::collections::HashSet;

pub use expression::Expression;
pub use grammar::Grammar;
pub use node::{Node, RegexExtKind, SymbolKind};
use nom::error::{ErrorKind, ParseError, VerboseErrorKind};

mod expression;
mod grammar;
mod node;
mod parser;

/// Get and parse EBNF grammar source into [Grammar], returns [Err] when given grammar is invalid.
///
/// # Example
///
/// ```rust
/// use ebnf::get_grammar;
///
/// let grammar_literal = r"
///     term ::= '1';
/// ";
/// let grammar = get_grammar(grammar_literal)?;
///
/// # Ok::<(), nom::Err<nom::error::VerboseError<&str>>>(())
/// ```
pub fn get_grammar(input: &str) -> Result<Grammar, nom::Err<nom::error::VerboseError<String>>> {
    fn check_defined_nonterminals(
        defined_nonterminals: HashSet<&str>,
        expressions: &Vec<Expression>,
    ) -> Result<(), nom::Err<nom::error::VerboseError<String>>> {
        for expression in expressions.iter() {
            let mut stack = vec![&expression.rhs];
            while let Some(node) = stack.pop() {
                match node {
                    Node::Terminal(_) => {}
                    Node::RegexString(_) => {}
                    Node::Nonterminal(nonterminal) => {
                        if !defined_nonterminals.contains(nonterminal.as_str()) {
                            return Err(nom::Err::Failure(nom::error::VerboseError {
                                errors: vec![(
                                    format!("Nonterminal '{}' is not defined", nonterminal),
                                    VerboseErrorKind::Context("Nonterminal"),
                                )],
                            }));
                        }
                    }
                    Node::Multiple(nodes) => {
                        stack.extend(nodes);
                    }
                    Node::RegexExt(node, _) => {
                        stack.push(node);
                    }
                    Node::Symbol(lhs, _, rhs) => {
                        stack.push(lhs);
                        stack.push(rhs);
                    }
                    Node::Group(node) => {
                        stack.push(node);
                    }
                    Node::ANY => {}
                    Node::EXCEPT(_, _) => {}
                }
            }
        }
        Ok(())
    }
    let (_, expressions) = parser::parse_expressions(input)
        .map_err(|x| {
            x.map(|x| nom::error::VerboseError {
                errors: x
                    .errors
                    .into_iter()
                    .map(|(x, y)| (x.to_string(), y))
                    .collect(),
            })
        })?;
    let defined_nonterminals = expressions
        .iter()
        .map(|expression| expression.lhs.as_str())
        .collect::<HashSet<&str>>();
    check_defined_nonterminals(defined_nonterminals, &expressions)?;
    Ok(Grammar { expressions })
}
