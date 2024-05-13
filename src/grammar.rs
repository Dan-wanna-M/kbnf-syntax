use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    iter::zip,
};

use alloc::vec::Vec;

use regex_automata::dfa::{
    self,
    dense::{Builder, Config},
    Automaton,
};
use serde::Serialize;
use string_interner::symbol::SymbolU32;

use crate::{
    expression::ExpressionWithID,
    node::{
        Alternation, ExceptedWithID, NoNestingNode, NodeWithID,
        OperatorFlattenedNode, Rhs,
    },
    semantic_error::SemanticError,
    InternedStrings, RegexExtKind, SymbolKind,
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
    pub id_to_regex: HashMap<SymbolU32, dfa::dense::DFA<Vec<u32>>>,
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
    pub fn simplify_grammar(mut self) -> SimplifiedGrammar {
        let expressions = Self::remove_unused_rules(self.expressions, self.start_symbol);
        let (expressions, mut special_nonterminals) =
            Self::flatten_nested_rules_with_nonterminals(expressions, &mut self.interned_strings);
        let expressions = Self::flatten_operators(expressions);
        let expressions = Self::group_same_lhs_together(expressions);
        let expressions =
            Self::merge_consecutive_terminals(expressions, &mut self.interned_strings);
        let expressions = Self::deduplicate_alternations(expressions);
        let expressions =
            Self::remove_unit_production(expressions, self.start_symbol, &mut special_nonterminals);
        let expressions = Self::expand_special_nonterminals(
            expressions,
            special_nonterminals,
            &mut self.interned_strings,
        );
        let expressions = Self::merge_identical_rhs_across_nonterminals(expressions);
        let expressions =
            Self::remove_nullable_rules(expressions, &self.interned_strings, &self.id_to_regex);
        SimplifiedGrammar {
            expressions,
            start_symbol: self.start_symbol,
            interned_strings: self.interned_strings,
        }
    }

    fn remove_unused_rules(
        expressions: Vec<ExpressionWithID>,
        start_symbol: SymbolU32,
    ) -> Vec<ExpressionWithID> {
        let mut used_nonterminals = HashSet::new();
        used_nonterminals.insert(start_symbol);
        for ExpressionWithID { lhs, rhs: node } in &expressions {
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
            rules.push(ExpressionWithID {
                lhs: name,
                rhs: node,
            });
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
            visited: &HashSet<SymbolU32>,
            special_nonterminals: &mut HashMap<SymbolU32, RegexExtKind>,
        ) -> Vec<&'a OperatorFlattenedNode> {
            let mut last_nonterminal = nonterminal;
            let mut chain = vec![nonterminal_node];
            loop {
                if rules.get(&last_nonterminal).is_none() {
                    panic!(
                        "The nonterminal {:?} is not defined. Chain: {:?}, rules:{:?}",
                        last_nonterminal, chain, rules
                    );
                }
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
                        if !special_nonterminals.contains_key(&last_nonterminal) {
                            chain.push(node);
                        }

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
            visited.extend(chain.iter().take(chain.len() - 1).map(|node| match node {
                OperatorFlattenedNode::Nonterminal(nonterminal) => *nonterminal,
                _ => unreachable!(),
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
                            &OperatorFlattenedNode::Nonterminal(nonterminal),
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

    fn merge_identical_rhs_across_nonterminals(
        rules: HashMap<SymbolU32, Rhs>,
    ) -> HashMap<SymbolU32, Rhs> {
        let mut rules: Vec<(SymbolU32, Rhs)> = rules.into_iter().collect();
        rules.sort_by_key(|(lhs, _)| *lhs);
        loop {
            // In worst case it has O(n^2logn) complexity. I am curious whether there exists a better solution.
            let mut updated = false;
            let mut merged_rhs_to_lhses = HashMap::new();
            let mut lhs_to_lhs = HashMap::new();
            for (lhs, mut rhs) in rules {
                rhs.alternations.sort();
                match merged_rhs_to_lhses.entry(rhs) {
                    std::collections::hash_map::Entry::Occupied(entry) => {
                        lhs_to_lhs.insert(lhs, *entry.get());
                        updated = true;
                    }
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert(lhs);
                    }
                }
            }
            rules = merged_rhs_to_lhses
                .into_iter()
                .map(|(rhs, lhs)| {
                    (
                        lhs,
                        Rhs {
                            alternations: rhs
                                .alternations
                                .into_iter()
                                .map(|alternation| Alternation {
                                    concatenations: alternation
                                        .concatenations
                                        .into_iter()
                                        .map(|concatenation| match concatenation {
                                            OperatorFlattenedNode::Nonterminal(nonterminal) => {
                                                OperatorFlattenedNode::Nonterminal(
                                                    *lhs_to_lhs
                                                        .get(&nonterminal)
                                                        .unwrap_or(&nonterminal),
                                                )
                                            }
                                            OperatorFlattenedNode::EXCEPT(
                                                ExceptedWithID::Nonterminal(nonterminal),
                                                x,
                                            ) => OperatorFlattenedNode::EXCEPT(
                                                ExceptedWithID::Nonterminal(
                                                    *lhs_to_lhs
                                                        .get(&nonterminal)
                                                        .unwrap_or(&nonterminal),
                                                ),
                                                x,
                                            ),
                                            _ => concatenation,
                                        })
                                        .collect(),
                                })
                                .collect(),
                        },
                    )
                })
                .collect();
            rules.sort_by_key(|(lhs, _)| *lhs);
            if !updated {
                break;
            }
        }
        rules.into_iter().collect()
    }

    fn remove_nullable_rules(
        rules: HashMap<SymbolU32, Rhs>,
        interned_strings: &InternedStrings,
        id_to_regex: &HashMap<SymbolU32, dfa::dense::DFA<Vec<u32>>>,
    ) -> HashMap<SymbolU32, Rhs> {
        fn find_nullable_nonterminals(
            rules: &HashMap<SymbolU32, Rhs>,
            interned_strings: &InternedStrings,
            id_to_regex: &HashMap<SymbolU32, dfa::dense::DFA<Vec<u32>>>,
        ) -> HashSet<OperatorFlattenedNode> {
            let mut nullable_symbols: HashSet<OperatorFlattenedNode> = HashSet::new();
            loop {
                // In worst case it has O(n^2) complexity. I am curious whether there exists a better solution.
                let mut updated = false;
                for (lhs, rhs) in rules {
                    if nullable_symbols.contains(&OperatorFlattenedNode::Nonterminal(*lhs)) {
                        continue;
                    }
                    if rhs.alternations.iter().any(|a| {
                        a.concatenations.iter().all(|c| match c {
                            OperatorFlattenedNode::Terminal(value) => {
                                if "" == interned_strings.terminals.resolve(*value).unwrap() {
                                    nullable_symbols.insert(c.clone());
                                    true
                                } else {
                                    false
                                }
                            }
                            OperatorFlattenedNode::RegexString(value) => {
                                if id_to_regex.get(value).unwrap().has_empty() {
                                    nullable_symbols.insert(c.clone());
                                    true
                                } else {
                                    false
                                }
                            }
                            _ => nullable_symbols.contains(c),
                        })
                    }) {
                        nullable_symbols.insert(OperatorFlattenedNode::Nonterminal(*lhs));
                        updated = true;
                    }
                }
                if !updated {
                    break;
                }
            }
            nullable_symbols
        }
        let nullable_nodes = find_nullable_nonterminals(&rules, interned_strings, id_to_regex);
        let mut new_rules = HashMap::new();
        for (lhs, Rhs { alternations }) in rules {
            let mut new_alterations = HashSet::new();
            for Alternation { concatenations } in alternations {
                let mut stack = vec![(vec![], concatenations.into_iter())];
                while let Some((mut prefix, mut iter)) = stack.pop() {
                    if let Some(node) = iter.next() {
                        if nullable_nodes.contains(&node) {
                            if matches!(node, OperatorFlattenedNode::Terminal(_)) {
                                stack.push((prefix, iter));
                            } else {
                                let without = prefix.clone();
                                prefix.push(node);
                                stack.push((prefix, iter.clone()));
                                stack.push((without, iter));
                            }
                        } else {
                            prefix.push(node);
                            stack.push((prefix, iter));
                        }
                    } else if !prefix.is_empty() {
                        prefix.reverse();
                        new_alterations.insert(Alternation {
                            concatenations: prefix,
                        });
                    }
                }
            }
            new_rules.insert(
                lhs,
                Rhs {
                    alternations: new_alterations.into_iter().collect(),
                },
            );
        }
        new_rules
    }
}

impl Grammar {
    pub fn validate_grammar(
        self,
        start_symbol: &str,
        regex_config: Config,
    ) -> Result<ValidatedGrammar, Box<SemanticError>> {
        let start = self
            .interned_strings
            .nonterminals
            .get(start_symbol)
            .unwrap();
        self.check_undefined_nonterminal(start_symbol)?;
        self.check_invalid_excepted_nonterminal()?;
        let regexes = self.compile_regex_string(regex_config)?;
        Ok(ValidatedGrammar {
            expressions: self.expressions,
            start_symbol: start,
            interned_strings: self.interned_strings,
            id_to_regex: regexes,
        })
    }

    fn check_undefined_nonterminal(&self, start_symbol: &str) -> Result<(), Box<SemanticError>> {
        fn check_defined_nonterminals(
            defined_nonterminals: &HashSet<SymbolU32>,
            expressions: &[ExpressionWithID],
            interned_strings: &InternedStrings,
        ) -> Result<(), Box<SemanticError>> {
            for expression in expressions.iter() {
                let mut stack = vec![&expression.rhs];
                while let Some(node) = stack.pop() {
                    match node {
                        NodeWithID::Terminal(_) => {}
                        NodeWithID::RegexString(_) => {}
                        NodeWithID::Nonterminal(nonterminal) => {
                            if !defined_nonterminals.contains(nonterminal) {
                                return Err(Box::new(SemanticError::UndefinedNonterminal(
                                    interned_strings
                                        .nonterminals
                                        .resolve(*nonterminal)
                                        .unwrap()
                                        .to_string(),
                                )));
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
                        NodeWithID::EXCEPT(excepted, _) => match excepted {
                            ExceptedWithID::Terminal(_) => {}
                            ExceptedWithID::Nonterminal(nonterminal) => {
                                if !defined_nonterminals.contains(nonterminal) {
                                    return Err(Box::new(SemanticError::UndefinedNonterminal(
                                        interned_strings
                                            .nonterminals
                                            .resolve(*nonterminal)
                                            .unwrap()
                                            .to_string(),
                                    )));
                                }
                            }
                        },
                        NodeWithID::Unknown => unreachable!(),
                    }
                }
            }
            Ok(())
        }
        let defined_nonterminals = self
            .expressions
            .iter()
            .map(|expression| expression.lhs)
            .collect::<HashSet<SymbolU32>>();
        self.interned_strings
            .nonterminals
            .get(start_symbol)
            .ok_or_else(|| SemanticError::UndefinedNonterminal(start_symbol.to_string()))?;
        check_defined_nonterminals(
            &defined_nonterminals,
            &self.expressions,
            &self.interned_strings,
        )
    }

    fn check_invalid_excepted_nonterminal(&self) -> Result<(), Box<SemanticError>> {
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
                            for expression in self
                                .expressions
                                .iter()
                                .filter(|expression| expression.lhs == *nonterminal)
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
                                        _ => {
                                            return Err(Box::new(
                                                SemanticError::InvalidExceptednonterminal(
                                                    self.interned_strings
                                                        .nonterminals
                                                        .resolve(*nonterminal)
                                                        .unwrap()
                                                        .to_string(),
                                                ),
                                            ));
                                        }
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

    fn compile_regex_string(
        &self,
        config: Config,
    ) -> Result<
        HashMap<SymbolU32, regex_automata::dfa::dense::DFA<std::vec::Vec<u32>>>,
        Box<SemanticError>,
    > {
        let mut regexes = HashMap::new();
        for (id, regex_string) in &self.interned_strings.regex_strings {
            let regex = Builder::new()
                .configure(config.clone())
                .build(regex_string)
                .map_err(SemanticError::RegexBuildError)?;
            regexes.insert(id, regex);
        }
        Ok(regexes)
    }
}

#[cfg(test)]
mod test {
    use insta::assert_yaml_snapshot;
    use regex_automata::dfa::dense::Config;

    use crate::get_grammar;
    #[test]
    #[should_panic]
    fn undefined_nonterminal() {
        let source = r#"
             except ::= A;
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar("except", Config::new())
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn undefined_nonterminal2() {
        let source = r#"
             except ::= except!(A);
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar("except", Config::new())
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn undefined_nonterminal3() {
        let source = r#"
             except ::= except!(A);
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar("A", Config::new())
            .unwrap();
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
            .validate_grammar("S", Config::new())
            .unwrap()
            .simplify_grammar();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn simplify_grammar2() {
        let source = r#"
            S ::= A? A? A? A? A?;
            A ::= 'cd';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar("S", Config::new())
            .unwrap()
            .simplify_grammar();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn simplify_grammar3() {
        let source = r#"
            S ::= 'a'? 'a'? 'a'? 'a'? 'a'?;
            A ::= 'cd';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar("S", Config::new())
            .unwrap()
            .simplify_grammar();
        assert_yaml_snapshot!(result)
    }
}
