use regex_automata::dfa::dense::BuildError;
use thiserror::Error;
#[derive(Error, Debug)]
pub enum SemanticError {
    #[error("the nonterminal`{0}` is not defined.")]
    UndefinedNonterminal(String),
    #[error("the excepted nonterminal `{0}` is invalid. It should only directly contain terminals.")]
    InvalidExceptednonterminal(String),
    #[error(transparent)]
    RegexBuildError(#[from] BuildError),
}