use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    iter::zip,
};

use alloc::vec::Vec;

use nom::Err;
use serde::Serialize;
use string_interner::{backend::StringBackend, symbol::SymbolU32, StringInterner};

use crate::{
    expression::{Expression, ExpressionWithID}, node::{
        Alternation, Excepted, ExceptedWithID, NoNestingNode, NodeWithID, OperatorFlattenedNode,
        Rhs,
    }, semantic_error::SemanticError, InternedStrings, Node, RegexExtKind, SymbolKind
};

#[derive(Debug, Clone)]
pub struct Grammar {
    pub expressions: Vec<ExpressionWithID>,
    pub interned_strings: InternedStrings,
}

#[derive(Debug, Clone)]
pub struct ValidatedGrammar {
    pub expressions: Vec<ExpressionWithID>,
    pub interned_strings: InternedStrings,
    pub start_symbol: SymbolU32,
}

#[derive(Debug, Clone)]
pub struct SimplifiedGrammar {
    pub expressions: HashMap<SymbolU32, Rhs>,
    pub start_symbol: SymbolU32,
    pub interned_strings: InternedStrings,
}

impl Display for SimplifiedGrammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();
        for (lhs, rhs) in &self.expressions {
            let lhs = self.interned_strings.nonterminals.resolve(*lhs).unwrap();
            buffer.push_str(lhs);
            buffer.push_str(" ::= ");
            for (j, alternation) in rhs.alternations.iter().enumerate() {
                for (i, concatenation) in alternation.concatenations.iter().enumerate() {
                    match concatenation {
                        OperatorFlattenedNode::Terminal(value) => {
                            let value = self.interned_strings.terminals.resolve(*value).unwrap();
                            buffer.push_str(&format!("'{}'", value));
                        }
                        OperatorFlattenedNode::RegexString(value) => {
                            let value =
                                self.interned_strings.regex_strings.resolve(*value).unwrap();
                            buffer.push_str(&format!("\"{}\"", value));
                        }
                        OperatorFlattenedNode::Nonterminal(value) => {
                            let value = self.interned_strings.nonterminals.resolve(*value).unwrap();
                            buffer.push_str(value);
                        }
                        OperatorFlattenedNode::ANY => {
                            buffer.push_str("any!");
                        }
                        OperatorFlattenedNode::EXCEPT(excepted, _) => match excepted {
                            ExceptedWithID::Terminal(value) => {
                                let value =
                                    self.interned_strings.terminals.resolve(*value).unwrap();
                                buffer.push_str(&format!("except!({})", value));
                            }
                            ExceptedWithID::Nonterminal(value) => {
                                let value =
                                    self.interned_strings.nonterminals.resolve(*value).unwrap();
                                buffer.push_str(&format!("except!({})", value));
                            }
                        },
                    }
                    if i + 1 < alternation.concatenations.len() {
                        buffer.push(' ');
                    }
                }
                if j + 1 < rhs.alternations.len() {
                    buffer.push_str(" | ");
                }
            }
            buffer.push_str(";\n");
        }
        write!(f, "{}", buffer)
    }
}

impl Serialize for SimplifiedGrammar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_str(&self)
    }
}

impl ValidatedGrammar {
    pub fn simplify_grammar(mut self, start_symbol: String) -> SimplifiedGrammar {
        let start_symbol = self.interned_strings.nonterminals.get_or_intern(start_symbol);
        let expressions = Self::remove_unused_rules(self.expressions, start_symbol);
        let (expressions, mut special_nonterminals) =
            Self::flatten_nested_rules_with_nonterminals(expressions, &mut self.interned_strings);
        let expressions = Self::flatten_operators(expressions);
        let expressions = Self::group_same_lhs_together(expressions);
        let expressions = Self::merge_consecutive_terminals(expressions, &mut self.interned_strings);
        let expressions = Self::deduplicate_alternations(expressions);
        let expressions =
            Self::remove_unit_production(expressions, start_symbol, &mut special_nonterminals);
        let expressions = Self::expand_special_nonterminals(
            expressions,
            special_nonterminals,
            &mut self.interned_strings,
        );
        SimplifiedGrammar {
            expressions,
            start_symbol,
            interned_strings: self.interned_strings,
        }
    }

    

    fn remove_unused_rules(
        expressions: Vec<ExpressionWithID>,
        start_symbol: SymbolU32,
    ) -> Vec<ExpressionWithID> {
        let mut used_nonterminals = HashSet::new();
        used_nonterminals.insert(start_symbol);
        for ExpressionWithID { lhs, rhs:node } in &expressions {
            if *lhs == start_symbol {
                let mut stack = vec![node];
                while let Some(node) = stack.pop() {
                    match node {
                        NodeWithID::Terminal(_) => {}
                        NodeWithID::RegexString(_) => {}
                        NodeWithID::Nonterminal(nonterminal) => {
                            used_nonterminals.insert(*nonterminal);
                        }
                        NodeWithID::Multiple(nodes) => {
                            for node in nodes {
                                stack.push(node);
                            }
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
                        NodeWithID::ANY => {}
                        NodeWithID::EXCEPT(excepted, _) => match excepted {
                            ExceptedWithID::Terminal(_) => {}
                            ExceptedWithID::Nonterminal(nonterminal) => {
                                used_nonterminals.insert(*nonterminal);
                            }
                        },
                        NodeWithID::Unknown => {
                            unreachable!("Unknown node. This should not happen.")
                        }
                    }
                }
            }
        }
        expressions
            .into_iter()
            .filter(|expression| used_nonterminals.contains(&expression.lhs))
            .collect()
    }

    fn flatten_nested_rules_with_nonterminals(
        mut rules: Vec<ExpressionWithID>,
        interned_strings: &mut InternedStrings,
    ) -> (
        Vec<(SymbolU32, NoNestingNode)>,
        HashMap<SymbolU32, RegexExtKind>,
    ) {
        let mut flattened_rules: Vec<(SymbolU32, NoNestingNode)> = Vec::with_capacity(rules.len());
        let mut special_nonterminals: HashMap<SymbolU32, RegexExtKind> =
            HashMap::with_capacity(rules.len());
        let get_new_nonterminal_name =
            |nonterminal: SymbolU32, identifier: &str, interned_strings: &mut InternedStrings| {
                let mut i = 0;
                loop {
                    let nonterminal = interned_strings.nonterminals.resolve(nonterminal).unwrap();
                    let new_nonterminal = format!("{nonterminal}_{identifier}_{i}");
                    if interned_strings
                        .nonterminals
                        .get(&new_nonterminal)
                        .is_none()
                    {
                        return interned_strings.nonterminals.get_or_intern(new_nonterminal);
                    }
                    i += 1;
                }
            };
        let mut add_new_rule = |lhs: SymbolU32,
                                identifier: &str,
                                parent: &mut NoNestingNode,
                                node: NodeWithID,
                                rules: &mut Vec<ExpressionWithID>,
                                kind: Option<RegexExtKind>| {
            let name = get_new_nonterminal_name(lhs, identifier, interned_strings);
            *parent = NoNestingNode::Nonterminal(name);
            if let Some(kind) = kind {
                special_nonterminals.insert(name, kind);
            }
            rules.push(ExpressionWithID { lhs, rhs: node });
        };
        fn get_slice(nodes: &[NodeWithID]) -> Vec<NoNestingNode> {
            let mut buffer = Vec::with_capacity(nodes.len());
            buffer.resize(nodes.len(), NoNestingNode::Unknown);
            buffer
        }
        while !rules.is_empty() {
            let length = rules.len();
            for i in (0..length).rev() {
                let mut stack: Vec<(NodeWithID, &mut NoNestingNode)> = vec![];
                let mut root = NoNestingNode::Unknown;
                let ExpressionWithID { lhs, rhs } = rules.swap_remove(i);
                stack.push((rhs, &mut root));
                while let Some((old_node, new_parent)) = stack.pop() {
                    match old_node {
                        NodeWithID::Terminal(value) => {
                            *new_parent = NoNestingNode::Terminal(value);
                        }
                        NodeWithID::RegexString(value) => {
                            *new_parent = NoNestingNode::RegexString(value);
                        }
                        NodeWithID::Nonterminal(value) => {
                            *new_parent = NoNestingNode::Nonterminal(value);
                        }
                        NodeWithID::Multiple(nodes) => {
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
                        NodeWithID::RegexExt(node, ext) => {
                            add_new_rule(
                                lhs,
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
                        NodeWithID::Symbol(l, symbol, r) => {
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
                        NodeWithID::Group(node) => {
                            add_new_rule(lhs, "group", new_parent, *node, &mut rules, None);
                        }
                        NodeWithID::ANY => {
                            *new_parent = NoNestingNode::ANY;
                        }
                        NodeWithID::EXCEPT(excepted, o) => {
                            *new_parent = NoNestingNode::EXCEPT(excepted, o);
                        }
                        NodeWithID::Unknown => {
                            unreachable!("Unknown node. This should not happen.")
                        }
                    }
                }
                flattened_rules.push((lhs, root));
            }
        }
        (flattened_rules, special_nonterminals)
    }

    fn flatten_operators(rules: Vec<(SymbolU32, NoNestingNode)>) -> Vec<(SymbolU32, Rhs)> {
        let mut flattened_rules: Vec<(SymbolU32, Rhs)> =
            Vec::<(SymbolU32, Rhs)>::with_capacity(rules.len());
        for (lhs, node) in rules {
            let mut rhs = Rhs {
                alternations: vec![Alternation {
                    concatenations: vec![],
                }],
            };
            let mut stack = vec![(node, 0usize)];
            while let Some((node, index)) = stack.pop() {
                match node {
                    NoNestingNode::Unknown => unreachable!("Unknown node. This should not happen."),
                    NoNestingNode::Terminal(value) => {
                        rhs.alternations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::Terminal(value));
                    }
                    NoNestingNode::RegexString(value) => {
                        rhs.alternations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::RegexString(value));
                    }
                    NoNestingNode::Nonterminal(value) => {
                        rhs.alternations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::Nonterminal(value));
                    }
                    NoNestingNode::Concatenations(mut nodes) => {
                        if nodes.is_empty() {
                            continue;
                        }
                        if index != usize::MAX {
                            nodes.reverse();
                        }
                        let new_node = nodes.pop().unwrap();
                        stack.push((
                            NoNestingNode::Concatenations(nodes),
                            usize::MAX, // This is a signal not to reverse the nodes.
                        ));
                        stack.push((new_node, rhs.alternations.len() - 1));
                    }

                    NoNestingNode::Alternations(mut nodes) => {
                        assert!(
                            nodes.len() == 2,
                            "Alternations should only have two elements."
                        );
                        let r = nodes.pop().unwrap();
                        let l = nodes.pop().unwrap();
                        // Due to the way the EBNF parser is implemented, we can assume alternations only have two elements.
                        rhs.alternations.push(Alternation {
                            concatenations: vec![],
                        });
                        stack.push((r, rhs.alternations.len() - 1)); // put the right node to the new alternation
                        stack.push((l, rhs.alternations.len() - 2)); // put the left node to the previous alternation
                    }
                    NoNestingNode::ANY => {
                        rhs.alternations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::ANY);
                    }
                    NoNestingNode::EXCEPT(excepted, x) => {
                        rhs.alternations[index]
                            .concatenations
                            .push(OperatorFlattenedNode::EXCEPT(excepted, x));
                    }
                }
            }
            flattened_rules.push((lhs, rhs));
        }
        flattened_rules
    }

    fn group_same_lhs_together(rules: Vec<(SymbolU32, Rhs)>) -> HashMap<SymbolU32, Rhs> {
        let mut new_rules: HashMap<SymbolU32, Rhs> = HashMap::new();
        for (lhs, rhs) in rules {
            let entry = new_rules.entry(lhs).or_insert(Rhs {
                alternations: vec![],
            });
            entry.alternations.extend(rhs.alternations);
        }
        new_rules
    }

    fn merge_consecutive_terminals(
        rules: HashMap<SymbolU32, Rhs>,
        interned_strings: &mut InternedStrings,
    ) -> HashMap<SymbolU32, Rhs> {
        rules
            .into_iter()
            .map(|(lhs, rhs)| {
                (
                    lhs,
                    Rhs {
                        alternations: rhs
                            .alternations
                            .into_iter()
                            .map(|a| Alternation {
                                concatenations: a.concatenations.into_iter().fold(
                                    vec![],
                                    |mut acc, c| {
                                        if let OperatorFlattenedNode::Terminal(value) = c {
                                            if let Some(OperatorFlattenedNode::Terminal(
                                                last_value,
                                            )) = acc.last()
                                            {
                                                let last_value = interned_strings
                                                    .terminals
                                                    .resolve(*last_value)
                                                    .unwrap();
                                                let value = interned_strings
                                                    .terminals
                                                    .resolve(value)
                                                    .unwrap();
                                                let new_value = format!("{}{}", last_value, value);
                                                let new_value = interned_strings
                                                    .terminals
                                                    .get_or_intern(new_value);
                                                acc.pop();
                                                acc.push(OperatorFlattenedNode::Terminal(
                                                    new_value,
                                                ));
                                            } else {
                                                acc.push(c);
                                            }
                                        } else {
                                            acc.push(c);
                                        }
                                        acc
                                    },
                                ),
                            })
                            .collect(),
                    },
                )
            })
            .collect()
    }

    fn deduplicate_alternations(rules: HashMap<SymbolU32, Rhs>) -> HashMap<SymbolU32, Rhs> {
        let mut new_rules: HashMap<SymbolU32, HashSet<Alternation>> = HashMap::new();
        for (lhs, rhs) in rules {
            let entry = new_rules.entry(lhs).or_default();
            entry.extend(rhs.alternations.into_iter());
        }
        new_rules
            .into_iter()
            .map(|(lhs, rhs)| {
                (
                    lhs,
                    Rhs {
                        alternations: rhs.into_iter().collect(),
                    },
                )
            })
            .collect()
    }

    fn remove_unit_production(
        rules: HashMap<SymbolU32, Rhs>,
        start_nonterminal: SymbolU32,
        special_nonterminals: &mut HashMap<SymbolU32, RegexExtKind>,
    ) -> HashMap<SymbolU32, Rhs> {
        fn find_unit_chain<'a>(
            rules: &'a HashMap<SymbolU32, Rhs>,
            nonterminal_node: &'a OperatorFlattenedNode,
            nonterminal: SymbolU32,
            visited: &mut HashSet<SymbolU32>,
            special_nonterminals: &mut HashMap<SymbolU32, RegexExtKind>,
        ) -> Vec<&'a OperatorFlattenedNode> {
            let mut last_nonterminal = nonterminal;
            let mut chain = vec![nonterminal_node];
            visited.insert(nonterminal);
            loop {
                let rhs = rules.get(&last_nonterminal).unwrap();
                if rhs.alternations.len() != 1 {
                    break;
                }
                let altercation = rhs.alternations.first().unwrap();
                if altercation.concatenations.len() != 1 {
                    break;
                }
                let node = altercation.concatenations.first().unwrap();
                match node {
                    OperatorFlattenedNode::Nonterminal(next_nonterminal) => {
                        if visited.contains(next_nonterminal) {
                            break;
                        }
                        if special_nonterminals.contains_key(&last_nonterminal)
                            ^ special_nonterminals.contains_key(next_nonterminal)
                        {
                            break;
                        }
                        chain.push(node);
                        if let Some(e1) = special_nonterminals.get(&last_nonterminal) {
                            if let Some(e2) = special_nonterminals.get(next_nonterminal) {
                                match (e1, e2) {
                                    (RegexExtKind::Repeat0, RegexExtKind::Repeat0) => {}
                                    (RegexExtKind::Repeat1, RegexExtKind::Repeat1) => {}
                                    (RegexExtKind::Optional, RegexExtKind::Optional) => {}
                                    (RegexExtKind::Repeat0, RegexExtKind::Repeat1) => {}
                                    (RegexExtKind::Repeat1, RegexExtKind::Repeat0) => {
                                        *special_nonterminals.get_mut(&last_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Repeat0, RegexExtKind::Optional) => {}
                                    (RegexExtKind::Optional, RegexExtKind::Repeat0) => {
                                        *special_nonterminals.get_mut(&last_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Repeat1, RegexExtKind::Optional) => {
                                        *special_nonterminals.get_mut(&last_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Optional, RegexExtKind::Repeat1) => {
                                        *special_nonterminals.get_mut(&last_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                };
                            }
                        }
                        last_nonterminal = *next_nonterminal;
                    }
                    _ => {
                        chain.push(node);
                        break;
                    }
                }
            }
            chain
        }
        fn update_nonterminal<'a>(
            rules: &'a HashMap<SymbolU32, Rhs>,
            nonterminal_node: &'a OperatorFlattenedNode,
            nonterminal: SymbolU32,
            visited: &mut HashSet<SymbolU32>,
            src_to_dst: &mut HashMap<SymbolU32, OperatorFlattenedNode>,
            stack: &mut Vec<SymbolU32>,
            special_nonterminals: &mut HashMap<SymbolU32, RegexExtKind>,
        ) {
            let chain = find_unit_chain(
                rules,
                nonterminal_node,
                nonterminal,
                visited,
                special_nonterminals,
            );
            visited.extend(chain.iter().filter_map(|node| match node {
                OperatorFlattenedNode::Nonterminal(nonterminal) => Some(*nonterminal),
                _ => None,
            }));
            if chain.len() > 1 {
                if let OperatorFlattenedNode::Nonterminal(nonterminal) = chain.last().unwrap() {
                    stack.push(*nonterminal);
                }
                match chain.as_slice() {
                    [first @ .., last] => {
                        for node in first {
                            match node {
                                OperatorFlattenedNode::Nonterminal(nonterminal) => {
                                    src_to_dst.insert(*nonterminal, (*last).clone());
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            } else {
                stack.push(nonterminal);
            }
        }
        let mut stack = vec![start_nonterminal];
        let mut chains: HashMap<SymbolU32, OperatorFlattenedNode> = HashMap::new();
        let mut visited = HashSet::new();
        while let Some(nonterminal) = stack.pop() {
            let rhs = rules.get(&nonterminal).unwrap();
            for a in rhs.alternations.iter() {
                for c in a.concatenations.iter() {
                    if let &OperatorFlattenedNode::Nonterminal(nonterminal) = c {
                        if visited.contains(&nonterminal) {
                            continue;
                        }
                        update_nonterminal(
                            &rules,
                            c,
                            nonterminal,
                            &mut visited,
                            &mut chains,
                            &mut stack,
                            special_nonterminals,
                        );
                    } else if let &OperatorFlattenedNode::EXCEPT(
                        ExceptedWithID::Nonterminal(nonterminal),
                        _,
                    ) = c
                    {
                        if visited.contains(&nonterminal) {
                            continue;
                        }
                        update_nonterminal(
                            &rules,
                            c,
                            nonterminal,
                            &mut visited,
                            &mut chains,
                            &mut stack,
                            special_nonterminals,
                        );
                    }
                }
            }
        }
        rules
            .into_iter()
            .filter_map(|(lhs, rhs)| {
                if chains.get(&lhs).is_some() {
                    None
                } else {
                    Some((
                        lhs,
                        Rhs {
                            alternations: rhs
                                .alternations
                                .into_iter()
                                .map(|a| Alternation {
                                    concatenations: a
                                        .concatenations
                                        .into_iter()
                                        .map(|c| match c {
                                            OperatorFlattenedNode::Nonterminal(nonterminal) => {
                                                chains.get(&nonterminal).unwrap_or(&c).clone()
                                            }
                                            OperatorFlattenedNode::EXCEPT(
                                                ExceptedWithID::Nonterminal(nonterminal),
                                                _,
                                            ) => chains.get(&nonterminal).unwrap_or(&c).clone(),
                                            _ => c,
                                        })
                                        .collect::<Vec<OperatorFlattenedNode>>(),
                                })
                                .collect(),
                        },
                    ))
                }
            })
            .collect()
    }

    fn expand_special_nonterminals(
        rules: HashMap<SymbolU32, Rhs>,
        special_nonterminals: HashMap<SymbolU32, RegexExtKind>,
        interned_strings: &mut InternedStrings,
    ) -> HashMap<SymbolU32, Rhs> {
        rules
            .into_iter()
            .map(|(lhs, mut rhs)| {
                if let Some(kind) = special_nonterminals.get(&lhs) {
                    let node = rhs.alternations.remove(0).concatenations.remove(0);
                    match kind {
                        RegexExtKind::Optional => (
                            lhs,
                            Rhs {
                                alternations: vec![
                                    Alternation {
                                        concatenations: vec![node],
                                    },
                                    Alternation {
                                        concatenations: vec![OperatorFlattenedNode::Terminal(
                                            interned_strings.terminals.get_or_intern(""),
                                        )],
                                    },
                                ],
                            },
                        ),
                        RegexExtKind::Repeat0 => (
                            lhs,
                            Rhs {
                                alternations: vec![
                                    Alternation {
                                        concatenations: vec![OperatorFlattenedNode::Terminal(
                                            interned_strings.terminals.get_or_intern(""),
                                        )],
                                    },
                                    Alternation {
                                        concatenations: vec![node.clone()],
                                    },
                                    Alternation {
                                        concatenations: vec![
                                            OperatorFlattenedNode::Nonterminal(lhs),
                                            node,
                                        ],
                                    },
                                ],
                            },
                        ),
                        RegexExtKind::Repeat1 => (
                            lhs,
                            Rhs {
                                alternations: vec![
                                    Alternation {
                                        concatenations: vec![node.clone()],
                                    },
                                    Alternation {
                                        concatenations: vec![
                                            OperatorFlattenedNode::Nonterminal(lhs),
                                            node,
                                        ],
                                    },
                                ],
                            },
                        ),
                    }
                } else {
                    (lhs, rhs)
                }
            })
            .collect()
    }

    fn remove_nullable_rules(rules: HashMap<SymbolU32, Rhs>) {
        fn find_nullable_nonterminals(
            rules: &HashMap<SymbolU32, Rhs>,
            start_symbol: SymbolU32,
        ) -> HashSet<SymbolU32> {
            let mut nullable_nonterminals = HashMap::new();
            let mut stack = vec![(start_symbol, None)];
            while let Some((nonterminal, parent)) = stack.pop() {
                nullable_nonterminals.insert(nonterminal, true);
                let rhs = rules.get(&nonterminal).unwrap();
                for a in rhs.alternations.iter() {
                    for c in a.concatenations.iter() {
                        if let OperatorFlattenedNode::Nonterminal(next) = c {
                            stack.push((*next, Some(nonterminal)));
                        } else if let OperatorFlattenedNode::{
                            nullable_nonterminals.insert(nonterminal, false);
                            if let Some(parent) = parent {
                                nullable_nonterminals.insert(parent, false);
                            }
                        }
                    }
                }
            }
            nullable_nonterminals
                .into_iter()
                .filter_map(|(k, v)| if v { Some(k) } else { None })
                .collect()
        }
    }
}


impl Grammar {

    pub fn validate_grammar(self, start_symbol: &str)-> Result<ValidatedGrammar, SemanticError>
    {
        match self.check_undefined_nonterminal(start_symbol) {
            Ok(_) => {match self.check_invalid_excepted_nonterminal() {
                Ok(_) => Ok(ValidatedGrammar {
                    expressions: self.expressions,
                    interned_strings: self.interned_strings,
                    start_symbol: self.interned_strings.nonterminals.get(start_symbol).unwrap(),
                }),
                Err(e) => Err(e),
            }},
            Err(e) => Err(e),
        }
    }

    fn check_undefined_nonterminal(&self, start_symbol: &str)-> Result<(), SemanticError> {
        fn check_defined_nonterminals(
            defined_nonterminals: HashSet<SymbolU32>,
            expressions: Vec<ExpressionWithID>,
            interned_strings: InternedStrings
        ) -> Result<(), SemanticError> {
            for expression in expressions.iter() {
                let mut stack = vec![&expression.rhs];
                while let Some(node) = stack.pop() {
                    match node {
                        NodeWithID::Terminal(_) => {}
                        NodeWithID::RegexString(_) => {}
                        NodeWithID::Nonterminal(nonterminal) => {
                            if !defined_nonterminals.contains(nonterminal) {
                                return Err(SemanticError::UndefinedNonterminal(interned_strings.nonterminals.resolve(*nonterminal).unwrap().to_string()));
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
                        NodeWithID::ANY => {}
                        NodeWithID::EXCEPT(_, _) => {}
                        NodeWithID::Unknown => unreachable!(),
                    }
                }
            }
            Ok(())
        }
        let defined_nonterminals = self.expressions
            .iter()
            .map(|expression| expression.lhs)
            .collect::<HashSet<SymbolU32>>();
        self.interned_strings.nonterminals.get(start_symbol).ok_or_else(||SemanticError::UndefinedNonterminal(start_symbol.to_string()))?;
        check_defined_nonterminals(defined_nonterminals, self.expressions,self.interned_strings)
    }

    fn check_invalid_excepted_nonterminal(&self) -> Result<(), SemanticError> {
        for expression in self.expressions.iter() {
            let mut stack = vec![&expression.rhs];
            while let Some(node) = stack.pop() {
                match node {
                    NodeWithID::Terminal(_) => {}
                    NodeWithID::RegexString(_) => {}
                    NodeWithID::Nonterminal(_) => {}
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
                    NodeWithID::ANY => {}
                    NodeWithID::EXCEPT(excepted, _) => match excepted {
                        ExceptedWithID::Terminal(_) => {}
                        ExceptedWithID::Nonterminal(nonterminal) => {
                            for expression in self.expressions.iter().filter(|expression|{
                                expression.lhs == *nonterminal
                            })
                            {
                                let mut stack = vec![&expression.rhs];
                                while let Some(node) = stack.pop() {
                                    match node {
                                        NodeWithID::Terminal(_) => {}
                                        NodeWithID::Multiple(nodes) => {
                                            stack.extend(nodes);
                                        }
                                        NodeWithID::Symbol(lhs, _, rhs) => {
                                            stack.push(lhs);
                                            stack.push(rhs);
                                        }
                                        NodeWithID::Unknown => unreachable!(),
                                        _ => return Err(SemanticError::InvalidExceptednonterminal(self.interned_strings.nonterminals.resolve(*nonterminal).unwrap().to_string()))
                                    }
                                }
                            }
                            }
                    },
                    NodeWithID::Unknown => unreachable!(),
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use insta::assert_yaml_snapshot;

    use crate::get_grammar;
    #[test]
    #[should_panic]
    fn undefined_nonterminal() {
        let source = r#"
             except ::= A;
        "#;
        let _ = get_grammar(source).unwrap();
    }
    #[test]
    fn simplify_grammar() {
        let source = r#"
            S ::= 'ab'S? | 'jk'(((A))) | 'ef'(B)*| 'a''b''c'|'abc';
            A ::= 'cd'|'cd'|A'c'|'Ac';
            B ::= ('a'B)?;
            C ::= 'dc';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .simplify_grammar("S".to_owned());
        assert_yaml_snapshot!(result)
    }
}
