use regex_automata::{dfa::{self}, hybrid::{self}};
#[derive(Debug, Clone)]
pub enum FiniteStateAutomaton {
    Dfa(dfa::dense::DFA<Vec<u32>>),
    LazyDFA(hybrid::dfa::DFA),
}
impl FiniteStateAutomaton {
    pub fn has_empty(&self) -> bool {
        match self {
            Self::Dfa(dfa) => dfa::Automaton::has_empty(&dfa),
            Self::LazyDFA(dfa) => dfa.get_nfa().has_empty(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum FiniteStateAutomatonConfig
{
    Dfa(dfa::dense::Config),
    LazyDFA(hybrid::dfa::Config),
}