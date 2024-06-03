use crate::regex::FiniteStateAutomatonConfig;

#[derive(Debug, Clone)]
pub struct CompressionConfig {
    pub min_terminals: usize,
    pub regex_config: FiniteStateAutomatonConfig,
}
