use core::slice;
use std::{
    collections::{HashMap, HashSet},
    iter::{zip, Flatten},
    mem, vec,
};

use alloc::vec::Vec;

use serde::Serialize;

use crate::{
    expression::Expression,
    node::{self, Alternation, Excepted, NoNestingNode, OperatorFlattenedNode, RHS},
    Node, RegexExtKind, SymbolKind,
};

#[derive(Debug, Clone, Serialize)]
pub struct Grammar {
    pub expressions: Vec<Expression>,
}

impl Grammar {
    pub fn simplify_grammar(self, start_symbol: String) -> (Vec<(String, RHS)>) {
        let expressions = self.remove_unused_rules(&start_symbol);
        let (expressions, special_nonterminals) =
            Self::flatten_nested_rules_with_nonterminals(expressions);
        println!("{:?}", expressions);
        let expressions = Self::flatten_operators(expressions);
        expressions
    }

    fn remove_unused_rules(self, start_symbol: &str) -> Vec<Expression> {
        let mut used_nonterminals = HashSet::new();
        used_nonterminals.insert(start_symbol.to_string());
        for expression in &self.expressions {
            if expression.lhs == start_symbol {
                let node = &expression.rhs;
                let mut stack = vec![node];
                while let Some(node) = stack.pop() {
                    match node {
                        Node::Terminal(_) => {}
                        Node::RegexString(_) => {}
                        Node::Nonterminal(nonterminal) => {
                            used_nonterminals.insert(nonterminal.clone());
                        }
                        Node::Multiple(nodes) => {
                            for node in nodes {
                                stack.push(node);
                            }
                        }
                        Node::RegexExt(node, _) => {
                            stack.push(node);
                        }
                        Node::Symbol(lhs, _, rhs) => {
                            stack.push(lhs);
                            stack.push(rhs);
                        }
                        Node::Group(node) => {
                            stack.push(node);
                        }
                        Node::ANY => {}
                        Node::EXCEPT(excepted, _) => match excepted {
                            Excepted::Terminal(_) => {}
                            Excepted::Nonterminal(nonterminal) => {
                                used_nonterminals.insert(nonterminal.clone());
                            }
                        },
                    }
                }
            }
        }
        self.expressions
            .into_iter()
            .filter(|expression| used_nonterminals.contains(&expression.lhs))
            .collect()
    }

    fn flatten_nested_rules_with_nonterminals(
        mut rules: Vec<Expression>,
    ) -> (Vec<(String, NoNestingNode)>, HashMap<String, RegexExtKind>) {
        let mut flattened_rules: Vec<(String, NoNestingNode)> = Vec::with_capacity(rules.len());
        let mut special_nonterminals: HashMap<String, RegexExtKind> =
            HashMap::with_capacity(rules.len());
        let mut lhses = rules
            .iter()
            .map(|rule| rule.lhs.clone())
            .collect::<HashSet<String>>();
        let get_new_nonterminal_name =
            |nonterminal: &str, identifier: &str, lhses: &HashSet<String>| {
                let mut i = 0;
                loop {
                    let new_nonterminal = format!("{nonterminal}_{identifier}_{i}");
                    if !lhses.contains(new_nonterminal.as_str()) {
                        return new_nonterminal;
                    }
                    i += 1;
                }
            };
        let mut add_new_rule = |lhs: &str,
                                identifier: &str,
                                parent: &mut NoNestingNode,
                                node: Node,
                                rules: &mut Vec<Expression>,
                                kind: Option<RegexExtKind>| {
            let name = get_new_nonterminal_name(lhs, identifier, &lhses);
            *parent = NoNestingNode::Nonterminal(name.clone());
            if let Some(kind) = kind {
                special_nonterminals.insert(name.clone(), kind);
            }
            rules.push(Expression {
                lhs: name.clone(),
                rhs: node,
            });
            lhses.insert(name);
        };
        fn get_slice(nodes: &[Node]) -> Vec<NoNestingNode> {
            let mut buffer = Vec::with_capacity(nodes.len());
            buffer.resize(nodes.len(), NoNestingNode::Unknown);
            buffer
        }
        while !rules.is_empty() {
            let length = rules.len();
            for i in (0..length).rev() {
                let mut stack: Vec<(Node, &mut NoNestingNode)> = vec![];
                let mut root = NoNestingNode::Unknown;
                let Expression { lhs, rhs } = rules.swap_remove(i);
                stack.push((rhs, &mut root));
                while let Some((old_node, new_parent)) = stack.pop() {
                    match old_node {
                        Node::Terminal(value) => {
                            *new_parent = NoNestingNode::Terminal(value);
                        }
                        Node::RegexString(value) => {
                            *new_parent = NoNestingNode::RegexString(value);
                        }
                        Node::Nonterminal(value) => {
                            *new_parent = NoNestingNode::Nonterminal(value);
                        }
                        Node::Multiple(nodes) => {
                            *new_parent = NoNestingNode::Concatenations(get_slice(&nodes));
                            match new_parent {
                                NoNestingNode::Concatenations(new_nodes) => {
                                    for (node, new_parent) in
                                        zip(nodes.into_iter(), new_nodes.iter_mut())
                                    {
                                        stack.push((node, new_parent));
                                    }
                                }
                                _ => unreachable!(),
                            }
                        }
                        Node::RegexExt(node, ext) => {
                            add_new_rule(
                                &lhs,
                                match ext {
                                    RegexExtKind::Repeat0 => "repeat0",
                                    RegexExtKind::Repeat1 => "repeat1",
                                    RegexExtKind::Optional => "optional",
                                },
                                new_parent,
                                *node,
                                &mut rules,
                                Some(ext),
                            );
                        }
                        Node::Symbol(l, symbol, r) => {
                            let nodes = vec![*l, *r];
                            match symbol {
                                SymbolKind::Concatenation => {
                                    *new_parent = NoNestingNode::Concatenations(get_slice(&nodes));
                                    match new_parent {
                                        NoNestingNode::Concatenations(new_nodes) => {
                                            for (node, new_parent) in
                                                zip(nodes.into_iter(), new_nodes.iter_mut())
                                            {
                                                stack.push((node, new_parent));
                                            }
                                        }
                                        _ => unreachable!(),
                                    }
                                }
                                SymbolKind::Alternation => {
                                    *new_parent = NoNestingNode::Alternations(get_slice(&nodes));
                                    match new_parent {
                                        NoNestingNode::Alternations(new_nodes) => {
                                            for (node, new_parent) in
                                                zip(nodes.into_iter(), new_nodes.iter_mut())
                                            {
                                                stack.push((node, new_parent));
                                            }
                                        }
                                        _ => unreachable!(),
                                    }
                                }
                            }
                        }
                        Node::Group(node) => {
                            add_new_rule(&lhs, "group", new_parent, *node, &mut rules, None);
                        }
                        Node::ANY => {
                            *new_parent = NoNestingNode::ANY;
                        }
                        Node::EXCEPT(excepted, o) => {
                            *new_parent = NoNestingNode::EXCEPT(excepted, o);
                        }
                    }
                }
                flattened_rules.push((lhs, root));
            }
        }
        (flattened_rules, special_nonterminals)
    }

    fn flatten_operators(rules: Vec<(String, NoNestingNode)>) -> Vec<(String, RHS)> {
        let mut flattened_rules: Vec<(String, RHS)> =
            Vec::<(String, RHS)>::with_capacity(rules.len());
        for (lhs, node) in rules {
            let mut rhs = RHS {
                altercations: vec![Alternation {
                    concatenations: vec![],
                }],
            };
            let mut stack = vec![(node, 0usize)];
            while let Some((node, index)) = stack.pop() {
                match node {
                    NoNestingNode::Unknown => unreachable!("Unknown node. This should not happen."),
                    NoNestingNode::Terminal(value) => {
                        rhs.altercations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::Terminal(value));
                    }
                    NoNestingNode::RegexString(value) => {
                        rhs.altercations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::RegexString(value));
                    }
                    NoNestingNode::Nonterminal(value) => {
                        rhs.altercations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::Nonterminal(value));
                    }
                    NoNestingNode::Concatenations(mut nodes) => {
                        if nodes.is_empty() {
                            continue;
                        }
                        let new_node = nodes.remove(0); // This is not very efficient, but it works. We can optimize this later.
                        stack.push((
                            NoNestingNode::Concatenations(nodes),
                            rhs.altercations.len() - 1,
                        ));
                        stack.push((new_node, rhs.altercations.len() - 1));
                    }

                    NoNestingNode::Alternations(mut nodes) => {
                        assert!(
                            nodes.len() == 2,
                            "Alternations should only have two elements."
                        );
                        let r = nodes.pop().unwrap();
                        let l = nodes.pop().unwrap();
                        // Due to the way the EBNF parser is implemented, we can assume alternations only have two elements.
                        rhs.altercations.push(Alternation {
                            concatenations: vec![],
                        });
                        stack.push((r, rhs.altercations.len() - 1)); // put the right node to the new alternation
                        stack.push((l, rhs.altercations.len() - 2)); // put the left node to the previous alternation
                    }
                    NoNestingNode::ANY => {
                        rhs.altercations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::ANY);
                    }
                    NoNestingNode::EXCEPT(excepted, x) => {
                        rhs.altercations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::EXCEPT(excepted, x));
                    }
                }
            }
            flattened_rules.push((lhs, rhs));
        }
        flattened_rules
    }
}

#[cfg(test)]
mod test {
    use insta::assert_yaml_snapshot;

    use crate::get_grammar;

    #[test]
    fn simplify_grammar() {
        let source = r#"
            S ::= 'ab'S? | 'jk'(((A))) | 'ef'B*;
            A ::= 'c'd;
            B ::= 'a'B;
            C ::= 'dc';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .simplify_grammar("S".to_owned());
        assert_yaml_snapshot!(result)
    }
}
