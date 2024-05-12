use alloc::string::String;

use serde::Serialize;
use string_interner::symbol::SymbolU32;

#[derive(Debug, Clone, Serialize)]
pub struct Expression {
    pub lhs: String,
    pub rhs: crate::Node,
}

#[derive(Debug, Clone)]
pub struct ExpressionWithID {
    pub lhs: SymbolU32,
    pub rhs: crate::node::NodeWithID,
}