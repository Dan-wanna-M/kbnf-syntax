use std::fmt::Debug;

use alloc::vec::Vec;

use rustc_hash::{FxHashMap, FxHashSet};
use string_interner::symbol::SymbolU32;

use crate::{
    expression::ExpressionWithID,
    node::{ExceptedWithID, NodeWithID},
    regex::{FiniteStateAutomaton, FiniteStateAutomatonConfig},
    semantic_error::SemanticError,
    utils::compile_one_regex_string,
    validated_grammar::ValidatedGrammar,
    InternedStrings,
};

#[derive(Debug, Clone)]
pub struct Grammar {
    pub expressions: Vec<ExpressionWithID>,
    pub interned_strings: InternedStrings,
}

impl Grammar {
    pub fn validate_grammar(
        self,
        start_symbol: &str,
        regex_config: FiniteStateAutomatonConfig,
    ) -> Result<ValidatedGrammar, Box<SemanticError>> {
        let start = self
            .interned_strings
            .nonterminals
            .get(start_symbol)
            .unwrap();
        self.check_undefined_nonterminal(start_symbol)?;
        self.check_invalid_excepted_nonterminal()?;
        let regexes = self.compile_regex_string(regex_config)?;
        Ok(ValidatedGrammar {
            expressions: self.expressions,
            start_symbol: start,
            interned_strings: self.interned_strings,
            id_to_regex: regexes,
            id_to_excepted: FxHashMap::default(),
        })
    }

    fn check_undefined_nonterminal(&self, start_symbol: &str) -> Result<(), Box<SemanticError>> {
        fn check_defined_nonterminals(
            defined_nonterminals: &FxHashSet<SymbolU32>,
            expressions: &[ExpressionWithID],
            interned_strings: &InternedStrings,
        ) -> Result<(), Box<SemanticError>> {
            for expression in expressions.iter() {
                let mut stack = vec![&expression.rhs];
                while let Some(node) = stack.pop() {
                    match node {
                        NodeWithID::Terminal(_) => {}
                        NodeWithID::RegexString(_) => {}
                        NodeWithID::Nonterminal(nonterminal) => {
                            if !defined_nonterminals.contains(nonterminal) {
                                return Err(Box::new(SemanticError::UndefinedNonterminal(
                                    interned_strings
                                        .nonterminals
                                        .resolve(*nonterminal)
                                        .unwrap()
                                        .to_string(),
                                )));
                            }
                        }
                        NodeWithID::Multiple(nodes) => {
                            stack.extend(nodes);
                        }
                        NodeWithID::RegexExt(node, _) => {
                            stack.push(node);
                        }
                        NodeWithID::Symbol(lhs, _, rhs) => {
                            stack.push(lhs);
                            stack.push(rhs);
                        }
                        NodeWithID::Group(node) => {
                            stack.push(node);
                        }
                        NodeWithID::EXCEPT(excepted, _) => match excepted {
                            ExceptedWithID::Terminal(_) => {}
                            ExceptedWithID::Nonterminal(nonterminal) => {
                                if !defined_nonterminals.contains(nonterminal) {
                                    return Err(Box::new(SemanticError::UndefinedNonterminal(
                                        interned_strings
                                            .nonterminals
                                            .resolve(*nonterminal)
                                            .unwrap()
                                            .to_string(),
                                    )));
                                }
                            }
                        },
                        NodeWithID::Unknown => unreachable!(),
                    }
                }
            }
            Ok(())
        }
        let defined_nonterminals = self
            .expressions
            .iter()
            .map(|expression| expression.lhs)
            .collect::<FxHashSet<SymbolU32>>();
        self.interned_strings
            .nonterminals
            .get(start_symbol)
            .ok_or_else(|| SemanticError::UndefinedNonterminal(start_symbol.to_string()))?;
        check_defined_nonterminals(
            &defined_nonterminals,
            &self.expressions,
            &self.interned_strings,
        )
    }

    fn check_invalid_excepted_nonterminal(&self) -> Result<(), Box<SemanticError>> {
        for expression in self.expressions.iter() {
            let mut stack = vec![&expression.rhs];
            while let Some(node) = stack.pop() {
                match node {
                    NodeWithID::Terminal(_) => {}
                    NodeWithID::RegexString(_) => {}
                    NodeWithID::Nonterminal(_) => {}
                    NodeWithID::Multiple(nodes) => {
                        stack.extend(nodes);
                    }
                    NodeWithID::RegexExt(node, _) => {
                        stack.push(node);
                    }
                    NodeWithID::Symbol(lhs, _, rhs) => {
                        stack.push(lhs);
                        stack.push(rhs);
                    }
                    NodeWithID::Group(node) => {
                        stack.push(node);
                    }
                    NodeWithID::EXCEPT(excepted, _) => match excepted {
                        ExceptedWithID::Terminal(x) => {
                            if Some(*x) == self.interned_strings.terminals.get("") {
                                return Err(Box::new(SemanticError::InvalidExceptedTerminal(
                                    self.interned_strings
                                        .terminals
                                        .resolve(*x)
                                        .unwrap()
                                        .to_string(),
                                )));
                            }
                        }
                        ExceptedWithID::Nonterminal(nonterminal) => {
                            for expression in self
                                .expressions
                                .iter()
                                .filter(|expression| expression.lhs == *nonterminal)
                            {
                                let mut stack = vec![&expression.rhs];
                                while let Some(node) = stack.pop() {
                                    match node {
                                        NodeWithID::Terminal(x) => {
                                            if Some(*x) == self.interned_strings.terminals.get("") {
                                                return Err(Box::new(
                                                    SemanticError::InvalidExceptedTerminal(
                                                        self.interned_strings
                                                            .terminals
                                                            .resolve(*x)
                                                            .unwrap()
                                                            .to_string(),
                                                    ),
                                                ));
                                            }
                                        }
                                        NodeWithID::Multiple(nodes) => {
                                            stack.extend(nodes);
                                        }
                                        NodeWithID::Symbol(lhs, _, rhs) => {
                                            stack.push(lhs);
                                            stack.push(rhs);
                                        }
                                        NodeWithID::Unknown => unreachable!(),
                                        _ => {
                                            return Err(Box::new(
                                                SemanticError::InvalidExceptedNonterminal(
                                                    self.interned_strings
                                                        .nonterminals
                                                        .resolve(*nonterminal)
                                                        .unwrap()
                                                        .to_string(),
                                                ),
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    },
                    NodeWithID::Unknown => unreachable!(),
                }
            }
        }
        Ok(())
    }

    fn compile_regex_string(
        &self,
        config: FiniteStateAutomatonConfig,
    ) -> Result<FxHashMap<SymbolU32, FiniteStateAutomaton>, Box<SemanticError>> {
        let mut regexes = FxHashMap::default();
        for (id, regex_string) in &self.interned_strings.regex_strings {
            let regex: Result<FiniteStateAutomaton, SemanticError> =
                compile_one_regex_string(regex_string, config.clone());
            let regex = match regex {
                Ok(x) => x,
                Err(e) => return Err(Box::new(e)),
            };
            regexes.insert(id, regex);
        }
        Ok(regexes)
    }
}

#[cfg(test)]
mod test {
    use insta::assert_snapshot;
    use regex_automata::dfa::dense::Config;

    use crate::{config::CompressionConfig, get_grammar};
    #[test]
    #[should_panic]
    fn undefined_nonterminal() {
        let source = r#"
            except ::= A;
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "except",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn undefined_nonterminal2() {
        let source = r#"
             except ::= except!(A);
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "except",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn undefined_nonterminal3() {
        let source = r#"
             except ::= except!(A);
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn invalid_excepted_nonterminal() {
        let source = r#"
             except ::= except!(A);
             A ::= 'a'|('a'|'b');
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn invalid_excepted_nonterminal2() {
        let source = r#"
             except ::= except!(A);
             A ::= B;
             B ::= 'c';
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn invalid_excepted_terminal() {
        let source = r#"
             except ::= except!('');
             A ::= 'a'|'';
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    fn simplify_grammar() {
        let source = r#"
            S ::= 'ab'S? | 'jk'(((A))) | 'ef'(B)*| 'a''b''c'|'abc'|except!('c',10)|except!(C);
            A ::= 'cd'|'cd'|A'c'|'Ac';
            B ::= ('a'B)?;
            C ::= 'dc';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar2() {
        let source = r#"
            S ::= (A)? (A)? (A)? (A)? (A)? B;
            A ::= 'cd';
            B ::= A'a';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar3() {
        let source = r#"
            S ::= 'a'? 'a'? 'a'? 'a'? 'a'?;
            A ::= 'cd';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar4() {
        let source = r#"
            S ::= ((A?)*)+;
            A ::= 'cd'?;
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar5() {
        let source = r#"
            S ::= 'ab'S? | 'jk'(((A)));
            A ::= 'cd'|'cd'|A'c'|'Ac';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar6() {
        let source = r#"
            S ::= 'cd'A;
            A ::= #"";
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar9() {
        let source = r#"
            S ::= 'c'|'a'|'b'|'d';
            A ::= #"";
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn simplify_grammar10() {
        let source = r#"
            S ::= except!('c')|except!('c',10)|except!(A);
            A ::= 'a'|'B'|'qa';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn unit_production_for_start_symbol() {
        let source = r#"
            S ::= 'a';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn empty_grammar() {
        let source = r#"
            S ::= '';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn empty_grammar2() {
        let source = r#"
            S ::= S;
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn empty_grammar3() {
        let source = r#"
            S ::= ''|#'^$';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new().anchored(regex_automata::Anchored::Yes),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn indirect_right_recursive_grammar()
    {
        let source = "start::=A'\n';
        A::='x'|'x' B;
        B::='y'|'y' A;";
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "start",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 3,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                &regex_automata::util::start::Config::new().anchored(regex_automata::Anchored::Yes),
            );
        assert_snapshot!(format!("{:?}", result))
    }
}
