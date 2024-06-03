use regex_automata::{
    dfa::{self, Automaton},
    hybrid::{self},
};
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

    pub fn only_empty(&self, config: &regex_automata::util::start::Config) -> bool {
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
            Self::LazyDFA(dfa) => {
                let mut cache = dfa.create_cache();
                let start_state = match dfa.start_state(&mut cache, config) {
                    Ok(x) => x,
                    Err(_) => {
                        return true;
                    }
                };
                let mut flag = true;
                for byte in 0..=u8::MAX {
                    let next_state = match dfa.next_state(&mut cache, start_state, byte) {
                        Ok(x) => x,
                        Err(_) => return true,
                    };
                    if !(next_state.is_dead() || next_state.is_quit()) {
                        flag = false;
                        break;
                    }
                }
                flag
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum FiniteStateAutomatonConfig {
    Dfa(dfa::dense::Config),
    LazyDFA(hybrid::dfa::Config),
}
