use std::fmt::Display;

use serde::Serialize;
use string_interner::{symbol::SymbolU32, Symbol};

use crate::{
    node::{OperatorFlattenedNode, Rhs}, regex::FiniteStateAutomaton, suffix_automaton::SuffixAutomaton, InternedStrings
};

#[derive(Clone)]
pub struct SimplifiedGrammar {
    pub expressions: Vec<Rhs>,
    pub start_symbol: SymbolU32,
    pub interned_strings: InternedStrings,
    pub id_to_regex: Vec<FiniteStateAutomaton>,
    pub id_to_suffix_automaton: Vec<SuffixAutomaton>,
}

impl SimplifiedGrammar {
    pub fn is_empty(&self) -> bool {
        self.expressions.is_empty()
    }
}

impl Display for SimplifiedGrammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();
        buffer.push_str(&format!(
            "start_symbol: {}\n",
            self.interned_strings
                .nonterminals
                .resolve(self.start_symbol)
                .unwrap_or("None")
        ));
        for (lhs, rhs) in self.expressions.iter().enumerate() {
            let lhs = self
                .interned_strings
                .nonterminals
                .resolve(SymbolU32::try_from_usize(lhs).unwrap())
                .unwrap();
            buffer.push_str(lhs);
            buffer.push_str(" ::= ");
            for (j, alternation) in rhs.alternations.iter().enumerate() {
                for (i, concatenation) in alternation.concatenations.iter().enumerate() {
                    match concatenation {
                        OperatorFlattenedNode::Terminal(value) => {
                            let value = self.interned_strings.terminals.resolve(*value).unwrap();
                            buffer.push_str(&format!("'{}'", value));
                        }
                        OperatorFlattenedNode::Substrings(value) => {
                            let value = self.interned_strings.sub_strings.resolve(*value).unwrap();
                            buffer.push_str(&format!("#substrs\"{}\"", value));
                        }
                        OperatorFlattenedNode::RegexString(value) => {
                            let value =
                                self.interned_strings.regex_strings.resolve(*value).unwrap();
                            buffer.push_str(&format!("#\"{}\"", value));
                        }
                        OperatorFlattenedNode::EarlyEndRegexString(value) => {
                            let value =
                                self.interned_strings.regex_strings.resolve(*value).unwrap();
                            buffer.push_str(&format!("#e\"{}\"", value));
                        }
                        OperatorFlattenedNode::Nonterminal(value) => {
                            let value = self.interned_strings.nonterminals.resolve(*value).unwrap();
                            buffer.push_str(value);
                        }
                    }
                    if i + 1 < alternation.concatenations.len() {
                        buffer.push(' ');
                    }
                }
                if j + 1 < rhs.alternations.len() {
                    buffer.push_str(" | ");
                }
            }
            buffer.push_str(";\n");
        }
        write!(f, "{}", buffer)
    }
}

impl std::fmt::Debug for SimplifiedGrammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();
        buffer.push_str(&format!(
            "start_symbol: {}(ID: {})\n",
            self.interned_strings
                .nonterminals
                .resolve(self.start_symbol)
                .unwrap_or("None"),
            self.start_symbol.to_usize()
        ));
        for (lhs, rhs) in self.expressions.iter().enumerate() {
            let lhs = self
                .interned_strings
                .nonterminals
                .resolve(SymbolU32::try_from_usize(lhs).unwrap())
                .unwrap();
            buffer.push_str(lhs);
            buffer.push_str(" ::= ");
            for (j, alternation) in rhs.alternations.iter().enumerate() {
                for (i, concatenation) in alternation.concatenations.iter().enumerate() {
                    match concatenation {
                        OperatorFlattenedNode::Terminal(value) => {
                            let terminal = self.interned_strings.terminals.resolve(*value).unwrap();
                            buffer.push_str(&format!("'{}'(ID: {})", terminal, value.to_usize()));
                        }
                        OperatorFlattenedNode::Substrings(value) => {
                            let substrings =
                                self.interned_strings.sub_strings.resolve(*value).unwrap();
                            buffer.push_str(&format!(
                                "#substrs\"{}\"(ID: {})",
                                substrings,
                                value.to_usize()
                            ));
                        }
                        OperatorFlattenedNode::RegexString(value) => {
                            let regex =
                                self.interned_strings.regex_strings.resolve(*value).unwrap();
                            let regex_type = match self.id_to_regex[value.to_usize()] {
                                FiniteStateAutomaton::Dfa(_) => "DFA",
                            };
                            buffer.push_str(&format!(
                                "#\"{}\"(ID: {},type: {})",
                                regex,
                                value.to_usize(),
                                regex_type
                            ));
                        }
                        OperatorFlattenedNode::EarlyEndRegexString(value) => {
                            let regex =
                                self.interned_strings.regex_strings.resolve(*value).unwrap();
                            let regex_type = match self.id_to_regex[value.to_usize()] {
                                FiniteStateAutomaton::Dfa(_) => "DFA",
                            };
                            buffer.push_str(&format!(
                                "#e\"{}\"(ID: {},type: {})",
                                regex,
                                value.to_usize(),
                                regex_type
                            ));
                        }
                        OperatorFlattenedNode::Nonterminal(value) => {
                            let nonterminal =
                                self.interned_strings.nonterminals.resolve(*value).unwrap();
                            buffer.push_str(&format!("{}(ID: {})", nonterminal, value.to_usize()));
                        }
                    }
                    if i + 1 < alternation.concatenations.len() {
                        buffer.push(' ');
                    }
                }
                if j + 1 < rhs.alternations.len() {
                    buffer.push_str(" | ");
                }
            }
            buffer.push_str(";\n");
        }
        write!(f, "{}", buffer)
    }
}

impl Serialize for SimplifiedGrammar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_str(&self)
    }
}
