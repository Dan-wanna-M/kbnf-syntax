use crate::{
    node::{Alternation, OperatorFlattenedNode},
    regex::{FiniteStateAutomaton, FiniteStateAutomatonConfig},
    semantic_error::SemanticError,
    InternedStrings,
};

#[allow(clippy::result_large_err)]
pub fn compile_one_regex_string(
    regex_string: &str,
    config: FiniteStateAutomatonConfig,
) -> Result<FiniteStateAutomaton, SemanticError> {
    let regex: Result<FiniteStateAutomaton, SemanticError> = match config {
        FiniteStateAutomatonConfig::Dfa(ref config) => regex_automata::dfa::dense::Builder::new()
            .configure(config.clone())
            .build(regex_string)
            .map(FiniteStateAutomaton::Dfa)
            .map_err(SemanticError::DfaRegexBuildError),
        FiniteStateAutomatonConfig::LazyDFA(ref config) => {
            regex_automata::hybrid::dfa::Builder::new()
                .configure(config.clone())
                .build(regex_string)
                .map(FiniteStateAutomaton::LazyDFA)
                .map_err(SemanticError::LazyDfaRegexBuildError)
        }
    };
    regex
}

pub fn from_terminals_to_regex_string(
    terminals: &[Alternation],
    interned_strings: &InternedStrings,
) -> String {
    terminals
        .iter()
        .map(|x| x.concatenations.first().unwrap())
        .map(|x| match x {
            OperatorFlattenedNode::Terminal(x) => x,
            _ => unreachable!(),
        })
        .map(|x| interned_strings.terminals.resolve(*x).unwrap())
        .collect::<Vec<_>>()
        .join("|")
}
