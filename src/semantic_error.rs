use kbnf_regex_automata::dfa::dense::BuildError;
use thiserror::Error;
#[derive(Error, Debug)]
pub enum SemanticError {
    #[error("the nonterminal `{0}` is not defined.")]
    UndefinedNonterminal(String),
    #[error(
        "the excepted nonterminal `{0}` is invalid. It should only directly contain terminals."
    )]
    InvalidExceptedNonterminal(String),
    #[error("the excepted terminal `{0}` is invalid. It should be nonempty.")]
    InvalidExceptedTerminal(String),
    #[error(transparent)]
    DfaRegexBuildError(#[from] BuildError),
    #[error(transparent)]
    LazyDfaRegexBuildError(#[from] kbnf_regex_automata::hybrid::BuildError),
}
