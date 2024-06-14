use kbnf_regex_automata::dfa::{self, Automaton};
#[derive(Debug, Clone)]
pub enum FiniteStateAutomaton {
    Dfa(dfa::dense::DFA<Vec<u32>>),
}
impl FiniteStateAutomaton {
    pub fn has_empty(&self) -> bool {
        match self {
            Self::Dfa(dfa) => dfa::Automaton::has_empty(&dfa),
        }
    }

    pub fn only_empty(&self, config: &kbnf_regex_automata::util::start::Config) -> bool {
        if !self.has_empty() {
            return false;
        }
        match self {
            Self::Dfa(dfa) => {
                let start_state = match dfa.start_state(config) {
                    Ok(x) => x,
                    Err(_) => {
                        return true;
                    }
                };
                (0..=u8::MAX).all(|byte| {
                    let next_state = dfa.next_state(start_state, byte);
                    dfa.is_dead_state(next_state) || dfa.is_quit_state(next_state)
                })
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum FiniteStateAutomatonConfig {
    Dfa(dfa::dense::Config)
}
