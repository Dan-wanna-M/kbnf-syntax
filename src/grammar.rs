use std::fmt::Debug;

use alloc::vec::Vec;

use general_sam::GeneralSam;
use rustc_hash::{FxHashMap, FxHashSet};
use string_interner::symbol::SymbolU32;

use crate::{
    expression::ExpressionWithID,
    node::NodeWithID,
    regex::{FiniteStateAutomaton, FiniteStateAutomatonConfig},
    semantic_error::SemanticError,
    suffix_automaton::SuffixAutomaton,
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
        start_nonterminal: &str,
        regex_config: FiniteStateAutomatonConfig,
    ) -> Result<ValidatedGrammar, Box<SemanticError>> {
        let start = self
            .interned_strings
            .nonterminals
            .get(start_nonterminal)
            .ok_or(SemanticError::UndefinedNonterminal(start_nonterminal.to_string()))?;
        self.check_undefined_nonterminal(start_nonterminal)?;
        let regexes = self.compile_regex_string(regex_config)?;
        let suffix_automata = self.compile_suffix_automaton();
        Ok(ValidatedGrammar {
            expressions: self.expressions,
            start_symbol: start,
            interned_strings: self.interned_strings,
            id_to_regex: regexes,
            id_to_suffix_automaton: suffix_automata,
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
                        NodeWithID::EarlyEndRegexString(_) => {}
                        NodeWithID::Substrings(_) => {}
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

    fn compile_suffix_automaton(&self) -> FxHashMap<SymbolU32, SuffixAutomaton> {
        let mut suffix_automata = FxHashMap::default();
        for (id, full_string) in &self.interned_strings.sub_strings {
            let suffix_automaton = GeneralSam::from_bytes(full_string);
            suffix_automata.insert(id, suffix_automaton);
        }
        suffix_automata
    }
}

#[cfg(test)]
mod test {
    use insta::assert_snapshot;
    use kbnf_regex_automata::dfa::dense::Config;

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
                &kbnf_regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar3() {
        let source = r#"
            S ::= 'a'? 'b'? 'c'? 'd'? 'e'?;
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn simplify_grammar6() {
        let source = r#"
            S ::= 'cd'A B;
            A ::= #"";
            B ::= #e'cd';
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new(),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn simplify_grammar11() {
        let source = r#"
__choice_food_0 ::= 'railroad' | 'orange' | 'banana';
__regex_0_0 ::= #'[0-9]+';
__regex_1_0 ::= #'[a-z]+';
__choice_ID_0 ::= __regex_0_0 | __regex_1_0;
integer ::= #"-?(0|[1-9]\\d*)";
number ::= #"-?(0|[1-9]\\d*)(\\.\\d+)?([eE][+-]?\\d+)?";
string ::= #'"([^\\\\"\u0000-\u001f]|\\\\["\\\\bfnrt/]|\\\\u[0-9A-Fa-f]{4})*"';
boolean ::= "true"|"false";
null ::= "null";
array ::= array_begin (json_value (comma json_value)*)? array_end;
object ::= object_begin (string colon json_value (comma string colon json_value)*)? object_end;
json_value ::= number|string|boolean|null|array|object;
comma ::= #"(\u0020|\u000A|\u000D|\u0009)*,(\u0020|\u000A|\u000D|\u0009)*";
colon ::= #"(\u0020|\u000A|\u000D|\u0009)*:(\u0020|\u000A|\u000D|\u0009)*";
object_begin ::= #"\\{(\u0020|\u000A|\u000D|\u0009)*";
object_end ::= #"(\u0020|\u000A|\u000D|\u0009)*\\}";
array_begin ::= #"\\[(\u0020|\u000A|\u000D|\u0009)*";
array_end ::= #"(\u0020|\u000A|\u000D|\u0009)*\\]";
__schema_json_0 ::= object_begin 'name' colon __schema_json_0_name comma 'weight' colon __schema_json_0_weight comma 'color' colon __schema_json_0_color object_end;
__schema_json_0_color ::= string;
__schema_json_0_weight ::= number;
__schema_json_0_name ::= string;

start ::= 'Today, I want to eat ' __choice_food_0 '\n' "My food's ID is " __choice_ID_0 '.\n' "\nWhat's more, indentations\nare handled\nappropriately." "Let's end with a json: " __schema_json_0 '\n';
        "#;
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new(),
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
                &kbnf_regex_automata::util::start::Config::new()
                    .anchored(kbnf_regex_automata::Anchored::Yes),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn indirect_right_recursive_grammar() {
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
                &kbnf_regex_automata::util::start::Config::new()
                    .anchored(kbnf_regex_automata::Anchored::Yes),
            );
        assert_snapshot!(format!("{:?}", result))
    }
    #[test]
    fn linked_list() {
        let source = r#"__schema_json_1_next_0 ::= __schema_json_1;

start ::= "```json\n"__schema_json_1"```\n";

__schema_json_1 ::= 
    #"\\A\\{( |\n|\r|\t)*\\z" 
    "\"value\""
    #"\\A( |\n|\r|\t)*:( |\n|\r|\t)*\\z" 
    #"\\A-?(0|[1-9]\\d*)\\z" 
    #"\\A( |\n|\r|\t)*,( |\n|\r|\t)*\\z" 
    "\"next\"" 
    #"\\A( |\n|\r|\t)*:( |\n|\r|\t)*\\z" 
    __schema_json_1_next
    #"\\A( |\n|\r|\t)*\\}\\z";

__schema_json_1_next ::= 
    "null"
    | __schema_json_1_next_0;"#;
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
                &kbnf_regex_automata::util::start::Config::new()
                    .anchored(kbnf_regex_automata::Anchored::Yes),
            );
        assert_snapshot!(format!("{:?}", result))
    }

    #[test]
    fn sub_strings() {
        let source = r#"
            S ::= B #substrs"abc" "d" | #substrs"A" "e";
            B ::= #substrs"";
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
                &kbnf_regex_automata::util::start::Config::new()
                    .anchored(kbnf_regex_automata::Anchored::Yes),
            );
        assert_snapshot!(format!("{:?}", result))
    }
}
