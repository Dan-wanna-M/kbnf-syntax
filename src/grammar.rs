use std::{fmt::Display, iter::zip};

use alloc::vec::Vec;

use regex_automata::{
    dfa::{self},
    hybrid,
};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::Serialize;
use string_interner::{backend::StringBackend, symbol::SymbolU32, StringInterner, Symbol};

use crate::{
    expression::ExpressionWithID,
    node::{
        Alternation, ExceptedWithID, FinalAlternation, FinalNode, FinalRhs, NoNestingNode, NodeWithID, OperatorFlattenedNode, Rhs,
    },
    regex::{FiniteStateAutomaton, FiniteStateAutomatonConfig},
    semantic_error::SemanticError,
    InternedStrings, RegexExtKind, SymbolKind,
};

#[derive(Debug, Clone)]
pub struct Grammar {
    pub expressions: Vec<ExpressionWithID>,
    pub interned_strings: InternedStrings,
}
#[derive(Debug, Clone)]
pub struct CompressionConfig {
    pub min_terminals: usize,
    pub regex_config: FiniteStateAutomatonConfig,
}

#[derive(Debug, Clone)]
pub struct ValidatedGrammar {
    pub expressions: Vec<ExpressionWithID>,
    pub interned_strings: InternedStrings,
    pub start_symbol: SymbolU32,
    pub id_to_regex: FxHashMap<SymbolU32, FiniteStateAutomaton>,
    pub id_to_excepted: FxHashMap<SymbolU32, FiniteStateAutomaton>,
}

#[derive(Debug, Clone)]
pub struct SimplifiedGrammar {
    pub expressions: Vec<FinalRhs>,
    pub start_symbol: SymbolU32,
    pub interned_strings: InternedStrings,
    pub id_to_regex: Vec<FiniteStateAutomaton>,
}

impl Display for SimplifiedGrammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();
        buffer.push_str(&format!(
            "start_symbol: {}\n",
            self.interned_strings
                .nonterminals
                .resolve(self.start_symbol)
                .unwrap()
        ));
        for (lhs, rhs) in self.expressions.iter().enumerate() {
            let lhs = self
                .interned_strings
                .nonterminals
                .resolve(SymbolU32::try_from_usize(lhs).unwrap())
                .unwrap();
            buffer.push_str(lhs);
            buffer.push_str(" ::= ");
            for (j, alternation) in rhs.alternations.iter().enumerate() {
                for (i, concatenation) in alternation.concatenations.iter().enumerate() {
                    match concatenation {
                        FinalNode::Terminal(value) => {
                            let value = self.interned_strings.terminals.resolve(*value).unwrap();
                            buffer.push_str(&format!("'{}'", value));
                        }
                        FinalNode::RegexString(value) => {
                            let value =
                                self.interned_strings.regex_strings.resolve(*value).unwrap();
                            buffer.push_str(&format!("#\"{}\"", value));
                        }
                        FinalNode::Nonterminal(value) => {
                            let value = self.interned_strings.nonterminals.resolve(*value).unwrap();
                            buffer.push_str(value);
                        }
                        FinalNode::EXCEPT(excepted, r) => {
                            let value = self.interned_strings.excepteds.resolve(*excepted).unwrap();
                            let r = r.map(|r| format!(",{}", r)).unwrap_or_default();
                            buffer.push_str(&format!("except!(#'{}'{r})", value));
                        }
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
    pub fn simplify_grammar(
        mut self,
        config: CompressionConfig,
        excepted_config: FiniteStateAutomatonConfig,
    ) -> SimplifiedGrammar {
        let expressions = Self::remove_unused_rules(self.expressions, self.start_symbol);
        let (expressions, mut special_nonterminals) =
            Self::flatten_nested_rules_with_nonterminals(expressions, &mut self.interned_strings);
        let expressions = Self::flatten_operators(expressions);
        let expressions = Self::group_same_lhs_together(expressions);
        let expressions = Self::deduplicate_alternations(expressions);
        let expressions =
            Self::remove_unit_production(expressions, self.start_symbol, &mut special_nonterminals);
        let expressions =
            Self::merge_consecutive_terminals(expressions, &mut self.interned_strings);

        let expressions = Self::expand_special_nonterminals(
            expressions,
            special_nonterminals,
            &mut self.interned_strings,
        );
        let expressions = Self::merge_identical_rhs_across_nonterminals(expressions);

        let expressions =
            Self::remove_nullable_rules(expressions, &self.interned_strings, &self.id_to_regex);
        let expressions =
            Self::remove_unit_production(expressions, self.start_symbol, &mut FxHashMap::default());
        let expressions =
            Self::merge_consecutive_terminals(expressions, &mut self.interned_strings);
        let expressions = Self::remove_fixed_point_production(expressions);
        let expressions = Self::compress_terminals(
            expressions,
            &mut self.interned_strings,
            config,
            &mut self.id_to_regex,
        );
        let expressions = Self::compile_excepteds(
            expressions,
            &mut self.interned_strings,
            excepted_config,
            &mut self.id_to_excepted,
        );
        let (interned_strings, id_to_regexes, expressions, start_symbol) = Self::compact_interned(
            self.start_symbol,
            expressions,
            self.interned_strings,
            self.id_to_regex,
            self.id_to_excepted,
        );

        SimplifiedGrammar {
            expressions,
            start_symbol,
            interned_strings,
            id_to_regex: id_to_regexes,
        }
    }

    fn remove_unused_rules(
        expressions: Vec<ExpressionWithID>,
        start_symbol: SymbolU32,
    ) -> Vec<ExpressionWithID> {
        let mut used_nonterminals = FxHashSet::default();
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
        FxHashMap<SymbolU32, RegexExtKind>,
    ) {
        let mut flattened_rules: Vec<(SymbolU32, NoNestingNode)> = Vec::with_capacity(rules.len());
        let mut special_nonterminals: FxHashMap<SymbolU32, RegexExtKind> = FxHashMap::default();
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

    fn group_same_lhs_together(rules: Vec<(SymbolU32, Rhs)>) -> FxHashMap<SymbolU32, Rhs> {
        let mut new_rules: FxHashMap<SymbolU32, Rhs> = FxHashMap::default();
        for (lhs, rhs) in rules {
            let entry = new_rules.entry(lhs).or_insert(Rhs {
                alternations: vec![],
            });
            entry.alternations.extend(rhs.alternations);
        }
        new_rules
    }

    fn merge_consecutive_terminals(
        rules: FxHashMap<SymbolU32, Rhs>,
        interned_strings: &mut InternedStrings,
    ) -> FxHashMap<SymbolU32, Rhs> {
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

    fn deduplicate_alternations(rules: FxHashMap<SymbolU32, Rhs>) -> FxHashMap<SymbolU32, Rhs> {
        let mut new_rules: FxHashMap<SymbolU32, FxHashSet<Alternation>> = FxHashMap::default();
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
        rules: FxHashMap<SymbolU32, Rhs>,
        start_nonterminal: SymbolU32,
        special_nonterminals: &mut FxHashMap<SymbolU32, RegexExtKind>,
    ) -> FxHashMap<SymbolU32, Rhs> {
        fn find_unit_chain<'a>(
            rules: &'a FxHashMap<SymbolU32, Rhs>,
            nonterminal_node: &'a OperatorFlattenedNode,
            nonterminal: SymbolU32,
            visited: &FxHashSet<SymbolU32>,
            special_nonterminals: &mut FxHashMap<SymbolU32, RegexExtKind>,
        ) -> Vec<&'a OperatorFlattenedNode> {
            let mut last_nonterminal = nonterminal;
            let mut chain = vec![nonterminal_node];
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
                                    (RegexExtKind::Repeat0, RegexExtKind::Repeat1) => {
                                        *special_nonterminals.get_mut(next_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Repeat1, RegexExtKind::Repeat0) => {}
                                    (RegexExtKind::Repeat0, RegexExtKind::Optional) => {
                                        *special_nonterminals.get_mut(next_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Optional, RegexExtKind::Repeat0) => {
                                        *special_nonterminals.get_mut(next_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Repeat1, RegexExtKind::Optional) => {
                                        *special_nonterminals.get_mut(next_nonterminal).unwrap() =
                                            RegexExtKind::Repeat0;
                                    }
                                    (RegexExtKind::Optional, RegexExtKind::Repeat1) => {
                                        *special_nonterminals.get_mut(next_nonterminal).unwrap() =
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
            rules: &'a FxHashMap<SymbolU32, Rhs>,
            nonterminal_node: &'a OperatorFlattenedNode,
            nonterminal: SymbolU32,
            visited: &mut FxHashSet<SymbolU32>,
            src_to_dst: &mut FxHashMap<SymbolU32, OperatorFlattenedNode>,
            stack: &mut Vec<SymbolU32>,
            special_nonterminals: &mut FxHashMap<SymbolU32, RegexExtKind>,
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
        let mut chains: FxHashMap<SymbolU32, OperatorFlattenedNode> = FxHashMap::default();
        let mut visited = FxHashSet::default();
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
                    }
                }
            }
            visited.insert(nonterminal);
        }
        rules
            .into_iter()
            .filter_map(|(lhs, rhs)| {
                if chains.contains_key(&lhs) {
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
        rules: FxHashMap<SymbolU32, Rhs>,
        special_nonterminals: FxHashMap<SymbolU32, RegexExtKind>,
        interned_strings: &mut InternedStrings,
    ) -> FxHashMap<SymbolU32, Rhs> {
        rules
            .into_iter()
            .map(|(lhs, mut rhs)| {
                if let Some(kind) = special_nonterminals.get(&lhs) {
                    match kind {
                        RegexExtKind::Optional => {
                            rhs.alternations.push(Alternation {
                                concatenations: vec![OperatorFlattenedNode::Terminal(
                                    interned_strings.terminals.get_or_intern(""),
                                )],
                            });
                            (lhs, rhs)
                        }
                        RegexExtKind::Repeat0 => {
                            let iter = rhs
                                .alternations
                                .iter()
                                .cloned()
                                .map(|mut a| {
                                    a.concatenations
                                        .insert(0, OperatorFlattenedNode::Nonterminal(lhs));
                                    a
                                })
                                .collect::<Vec<_>>();
                            rhs.alternations.extend(iter);
                            rhs.alternations.push(Alternation {
                                concatenations: vec![OperatorFlattenedNode::Terminal(
                                    interned_strings.terminals.get_or_intern(""),
                                )],
                            });
                            (lhs, rhs)
                        }
                        RegexExtKind::Repeat1 => {
                            let iter = rhs
                                .alternations
                                .iter()
                                .cloned()
                                .map(|mut a| {
                                    a.concatenations
                                        .insert(0, OperatorFlattenedNode::Nonterminal(lhs));
                                    a
                                })
                                .collect::<Vec<_>>();
                            rhs.alternations.extend(iter);
                            (lhs, rhs)
                        }
                    }
                } else {
                    (lhs, rhs)
                }
            })
            .collect()
    }

    fn merge_identical_rhs_across_nonterminals(
        mut rules: FxHashMap<SymbolU32, Rhs>,
    ) -> FxHashMap<SymbolU32, Rhs> {
        loop {
            // In worst case it has O(n^2logn) complexity. I am curious whether there exists a better solution.
            let mut updated = false;
            let mut merged_rhs_to_lhses = FxHashMap::default();
            let mut lhs_to_lhs = FxHashMap::default();
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
            if !updated {
                break;
            }
        }
        rules.into_iter().collect()
    }

    fn remove_nullable_rules(
        rules: FxHashMap<SymbolU32, Rhs>,
        interned_strings: &InternedStrings,
        id_to_regex: &FxHashMap<SymbolU32, FiniteStateAutomaton>,
    ) -> FxHashMap<SymbolU32, Rhs> {
        #[allow(clippy::unnecessary_fold)]
        fn find_nullable_nonterminals(
            rules: &FxHashMap<SymbolU32, Rhs>,
            interned_strings: &InternedStrings,
            id_to_regex: &FxHashMap<SymbolU32, FiniteStateAutomaton>,
        ) -> FxHashSet<OperatorFlattenedNode> {
            let mut nullable_symbols: FxHashSet<OperatorFlattenedNode> = FxHashSet::default();
            loop {
                // In worst case it has O(n^2) complexity. I am curious whether there exists a better solution.
                let mut updated = false;
                for (lhs, rhs) in rules {
                    if nullable_symbols.contains(&OperatorFlattenedNode::Nonterminal(*lhs)) {
                        continue;
                    }
                    if rhs.alternations.iter().fold(false, |result, a| {
                        result
                            || a.concatenations
                                .iter()
                                .fold(true, |inner_result, c| match c {
                                    OperatorFlattenedNode::Terminal(value) => {
                                        if "" == interned_strings.terminals.resolve(*value).unwrap()
                                        {
                                            nullable_symbols.insert(c.clone());
                                            inner_result & true
                                        } else {
                                            false
                                        }
                                    }
                                    OperatorFlattenedNode::RegexString(value) => {
                                        if id_to_regex.get(value).unwrap().has_empty() {
                                            nullable_symbols.insert(c.clone());
                                            inner_result & true
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
        let mut new_rules = FxHashMap::default();
        for (lhs, Rhs { alternations }) in rules {
            let mut new_alterations = FxHashSet::default();
            for Alternation { concatenations } in alternations {
                let mut stack = vec![(vec![], concatenations.into_iter())];
                while let Some((mut prefix, mut iter)) = stack.pop() {
                    if let Some(node) = iter.next() {
                        if nullable_nodes.contains(&node) {
                            if matches!(
                                node,
                                OperatorFlattenedNode::Terminal(_)
                                    | OperatorFlattenedNode::RegexString(_)
                            ) {
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
                        // prefix.reverse();
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

    fn remove_fixed_point_production(
        rules: FxHashMap<SymbolU32, Rhs>,
    ) -> FxHashMap<SymbolU32, Rhs> {
        rules
            .into_iter()
            .filter_map(|(lhs, rhs)| {
                let new_rhs = Rhs {
                    alternations: rhs
                        .alternations
                        .into_iter()
                        .filter_map(|a| {
                            if a.concatenations.len() == 1 {
                                match a.concatenations.first().unwrap() {
                                    OperatorFlattenedNode::Nonterminal(nonterminal) => {
                                        if *nonterminal == lhs {
                                            None
                                        } else {
                                            Some(a)
                                        }
                                    }
                                    _ => Some(a),
                                }
                            } else {
                                Some(a)
                            }
                        })
                        .collect(),
                };
                if new_rhs.alternations.is_empty() {
                    None
                } else {
                    Some((lhs, new_rhs))
                }
            })
            .collect()
    }

    fn compress_terminals(
        rules: FxHashMap<SymbolU32, Rhs>,
        interned_strings: &mut InternedStrings,
        config: CompressionConfig,
        id_to_regex: &mut FxHashMap<SymbolU32, FiniteStateAutomaton>,
    ) -> FxHashMap<SymbolU32, Rhs> {
        rules
            .into_iter()
            .map(|(lhs, rhs)| {
                let (terminals, mut remaining): (Vec<_>, Vec<_>) =
                    rhs.alternations.into_iter().partition(|x| {
                        matches!(
                            x.concatenations.as_slice(),
                            [OperatorFlattenedNode::Terminal(_)]
                        )
                    });
                let alternations = if terminals.len() >= config.min_terminals {
                    let regex_string = from_terminals_to_regex_string(&terminals, interned_strings);
                    let id = interned_strings
                        .regex_strings
                        .get(&regex_string)
                        .unwrap_or_else(|| match &config.regex_config {
                            FiniteStateAutomatonConfig::Dfa(config) => {
                                let dfa = dfa::dense::Builder::new()
                                    .configure(config.clone())
                                    .build(&regex_string)
                                    .unwrap();
                                let id = interned_strings.regex_strings.get_or_intern(regex_string);
                                id_to_regex.insert(id, FiniteStateAutomaton::Dfa(dfa));
                                id
                            }
                            FiniteStateAutomatonConfig::LazyDFA(config) => {
                                let dfa = hybrid::dfa::Builder::new()
                                    .configure(config.clone())
                                    .build(&regex_string)
                                    .unwrap();
                                let id = interned_strings.regex_strings.get_or_intern(regex_string);
                                id_to_regex.insert(id, FiniteStateAutomaton::LazyDFA(dfa));
                                id
                            }
                        });
                    remaining.push(Alternation {
                        concatenations: vec![OperatorFlattenedNode::RegexString(id)],
                    });
                    remaining
                } else {
                    remaining.extend(terminals);
                    remaining
                };
                (lhs, Rhs { alternations })
            })
            .collect()
    }

    fn compile_excepteds(
        rules: FxHashMap<SymbolU32, Rhs>,
        interned_strings: &mut InternedStrings,
        config: FiniteStateAutomatonConfig,
        id_to_excepteds: &mut FxHashMap<SymbolU32, FiniteStateAutomaton>,
    ) -> FxHashMap<SymbolU32, FinalRhs> {
        rules
            .clone()
            .into_iter()
            .map(|(lhs, rhs)| {
                let alternations = rhs
                    .alternations
                    .into_iter()
                    .map(|a| {
                        let mut concatenations: Vec<FinalNode> = vec![];
                        for c in a.concatenations {
                            let mut regex_string = String::new();
                            match c {
                                OperatorFlattenedNode::EXCEPT(excepted, x) => {
                                    match excepted {
                                        ExceptedWithID::Terminal(x) => {
                                            let string =
                                                interned_strings.terminals.resolve(x).unwrap();
                                            regex_string.push_str(string);
                                        }
                                        ExceptedWithID::Nonterminal(x) => {
                                            let terminals = rules.get(&x).unwrap();
                                            if terminals.alternations.len() == 1 {
                                                if let OperatorFlattenedNode::RegexString(x) =
                                                    terminals
                                                        .alternations
                                                        .first()
                                                        .unwrap()
                                                        .concatenations
                                                        .first()
                                                        .unwrap()
                                                {
                                                    regex_string.push_str(
                                                        interned_strings
                                                            .regex_strings
                                                            .resolve(*x)
                                                            .unwrap(),
                                                    )
                                                }
                                                else {
                                                    regex_string.push_str(
                                                        &from_terminals_to_regex_string(
                                                            &terminals.alternations,
                                                            interned_strings,
                                                        ),
                                                    )
                                                }
                                            } else {
                                                regex_string.push_str(
                                                    &from_terminals_to_regex_string(
                                                        &terminals.alternations,
                                                        interned_strings,
                                                    ),
                                                )
                                            }
                                        }
                                    }
                                    let id =
                                        interned_strings.excepteds.get_or_intern(&regex_string);
                                    id_to_excepteds.insert(
                                        id,
                                        compile_one_regex_string(&regex_string, config.clone())
                                            .unwrap(),
                                    );
                                    concatenations.push(FinalNode::EXCEPT(id, x));
                                }
                                OperatorFlattenedNode::Nonterminal(x) => {
                                    concatenations.push(FinalNode::Nonterminal(x));
                                }
                                OperatorFlattenedNode::Terminal(x) => {
                                    concatenations.push(FinalNode::Terminal(x));
                                }
                                OperatorFlattenedNode::RegexString(x) => {
                                    concatenations.push(FinalNode::RegexString(x));
                                }
                            }
                        }
                        FinalAlternation { concatenations }
                    })
                    .collect();
                (lhs, FinalRhs { alternations })
            })
            .collect()
    }

    fn compact_interned(
        mut start_symbol: SymbolU32,
        rules: FxHashMap<SymbolU32, FinalRhs>,
        interned: InternedStrings,
        id_to_regex: FxHashMap<SymbolU32, FiniteStateAutomaton>,
        id_to_excepteds: FxHashMap<SymbolU32, FiniteStateAutomaton>,
    ) -> (
        InternedStrings,
        Vec<FiniteStateAutomaton>,
        Vec<FinalRhs>,
        SymbolU32,
    ) {
        let mut interned_nonterminals: StringInterner<StringBackend> = StringInterner::default();
        let mut interned_terminals: StringInterner<StringBackend> = StringInterner::default();
        let mut interned_regexes: StringInterner<StringBackend> = StringInterner::default();
        let mut interned_excepteds: StringInterner<StringBackend> = StringInterner::default();
        let mut new_id_to_regex = Vec::with_capacity(id_to_regex.len());
        let mut new_id_to_excepteds = Vec::with_capacity(id_to_excepteds.len());
        let mut new_rules: Vec<_> = Vec::with_capacity(rules.len());
        for (lhs, rhs) in rules.into_iter() {
            let id =
                interned_nonterminals.get_or_intern(interned.nonterminals.resolve(lhs).unwrap());
            if lhs == start_symbol {
                start_symbol = id;
            }
            assert!(id.to_usize() == new_rules.len());
            new_rules.push(rhs);
        }
        for rhs in new_rules.iter_mut() {
            for FinalAlternation { concatenations } in &mut rhs.alternations {
                for concatenation in concatenations {
                    match concatenation {
                        FinalNode::Nonterminal(nonterminal) => {
                            *nonterminal = interned_nonterminals.get_or_intern(
                                interned.nonterminals.resolve(*nonterminal).unwrap(),
                            );
                        }
                        FinalNode::Terminal(terminal) => {
                            *terminal = interned_terminals
                                .get_or_intern(interned.terminals.resolve(*terminal).unwrap());
                        }
                        FinalNode::RegexString(regex) => {
                            let new_id = interned_regexes
                                .get_or_intern(interned.regex_strings.resolve(*regex).unwrap());
                            if new_id.to_usize() == new_id_to_regex.len() {
                                new_id_to_regex.push(id_to_regex.get(regex).unwrap().clone());
                            }
                            *regex = new_id;
                            // Should not fail since StringBackend is contiguous.
                        }
                        FinalNode::EXCEPT(excepted, _) => {
                            let new_id = interned_excepteds
                                .get_or_intern(interned.excepteds.resolve(*excepted).unwrap());
                            if new_id.to_usize() == new_id_to_excepteds.len() {
                                new_id_to_excepteds
                                    .push(id_to_excepteds.get(excepted).unwrap().clone());
                            }
                            *excepted = new_id;
                        }
                    }
                }
            }
        }
        (
            InternedStrings {
                nonterminals: interned_nonterminals,
                terminals: interned_terminals,
                regex_strings: interned_regexes,
                excepteds: interned_excepteds,
            },
            new_id_to_regex,
            new_rules,
            start_symbol,
        )
    }
}

impl Grammar {
    pub fn validate_grammar(
        self,
        start_symbol: &str,
        regex_config: FiniteStateAutomatonConfig,
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
            id_to_excepted: FxHashMap::default(),
        })
    }

    fn check_undefined_nonterminal(&self, start_symbol: &str) -> Result<(), Box<SemanticError>> {
        fn check_defined_nonterminals(
            defined_nonterminals: &FxHashSet<SymbolU32>,
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
            .collect::<FxHashSet<SymbolU32>>();
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
                    NodeWithID::EXCEPT(excepted, _) => match excepted {
                        ExceptedWithID::Terminal(x) => {
                            if Some(*x) == self.interned_strings.terminals.get("") {
                                return Err(Box::new(SemanticError::InvalidExceptedTerminal(
                                    self.interned_strings
                                        .terminals
                                        .resolve(*x)
                                        .unwrap()
                                        .to_string(),
                                )));
                            }
                        }
                        ExceptedWithID::Nonterminal(nonterminal) => {
                            for expression in self
                                .expressions
                                .iter()
                                .filter(|expression| expression.lhs == *nonterminal)
                            {
                                let mut stack = vec![&expression.rhs];
                                while let Some(node) = stack.pop() {
                                    match node {
                                        NodeWithID::Terminal(x) => {
                                            if Some(*x) == self.interned_strings.terminals.get("") {
                                                return Err(Box::new(
                                                    SemanticError::InvalidExceptedTerminal(
                                                        self.interned_strings
                                                            .terminals
                                                            .resolve(*x)
                                                            .unwrap()
                                                            .to_string(),
                                                    ),
                                                ));
                                            }
                                        }
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
                                                SemanticError::InvalidExceptedNonterminal(
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
        config: FiniteStateAutomatonConfig,
    ) -> Result<FxHashMap<SymbolU32, FiniteStateAutomaton>, Box<SemanticError>> {
        let mut regexes = FxHashMap::default();
        for (id, regex_string) in &self.interned_strings.regex_strings {
            let regex: Result<FiniteStateAutomaton, SemanticError> =
                compile_one_regex_string(regex_string, config.clone());
            let regex = match regex {
                Ok(x) => x,
                Err(e) => return Err(Box::new(e)),
            };
            regexes.insert(id, regex);
        }
        Ok(regexes)
    }
}
#[allow(clippy::result_large_err)]
fn compile_one_regex_string(
    regex_string: &str,
    config: FiniteStateAutomatonConfig,
) -> Result<FiniteStateAutomaton, SemanticError> {
    let regex: Result<FiniteStateAutomaton, SemanticError> = match config {
        FiniteStateAutomatonConfig::Dfa(ref config) => regex_automata::dfa::dense::Builder::new()
            .configure(config.clone())
            .build(regex_string)
            .map(FiniteStateAutomaton::Dfa)
            .map_err(SemanticError::DfaRegexBuildError),
        FiniteStateAutomatonConfig::LazyDFA(ref config) => {
            regex_automata::hybrid::dfa::Builder::new()
                .configure(config.clone())
                .build(regex_string)
                .map(FiniteStateAutomaton::LazyDFA)
                .map_err(SemanticError::LazyDfaRegexBuildError)
        }
    };
    regex
}

fn from_terminals_to_regex_string(
    terminals: &[Alternation],
    interned_strings: &InternedStrings,
) -> String {
    terminals
        .iter()
        .map(|x| x.concatenations.first().unwrap())
        .map(|x| match x {
            OperatorFlattenedNode::Terminal(x) => x,
            _ => unreachable!(),
        })
        .map(|x| interned_strings.terminals.resolve(*x).unwrap())
        .collect::<Vec<_>>()
        .join("|")
}

#[cfg(test)]
mod test {
    use insta::assert_snapshot;
    use regex_automata::dfa::dense::Config;

    use crate::{get_grammar, grammar::CompressionConfig};
    #[test]
    #[should_panic]
    fn undefined_nonterminal() {
        let source = r#"
             except ::= A;
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "except",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
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
            .validate_grammar(
                "except",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
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
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn invalid_excepted_nonterminal() {
        let source = r#"
             except ::= except!(A);
             A ::= 'a'|('a'|'b');
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    #[should_panic]
    fn invalid_excepted_terminal() {
        let source = r#"
             except ::= except!('');
             A ::= 'a'|'';
        "#;
        let _ = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "A",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap();
    }
    #[test]
    fn simplify_grammar() {
        let source = r#"
            S ::= 'ab'S? | 'jk'(((A))) | 'ef'(B)*| 'a''b''c'|'abc'|except!('c',10)|except!(C);
            A ::= 'cd'|'cd'|A'c'|'Ac';
            B ::= ('a'B)?;
            C ::= 'dc';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }

    #[test]
    fn simplify_grammar2() {
        let source = r#"
            S ::= (A)? (A)? (A)? (A)? (A)? B;
            A ::= 'cd';
            B ::= A'a';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }

    #[test]
    fn simplify_grammar3() {
        let source = r#"
            S ::= 'a'? 'a'? 'a'? 'a'? 'a'?;
            A ::= 'cd';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }

    #[test]
    fn simplify_grammar4() {
        let source = r#"
            S ::= ((A?)*)+;
            A ::= 'cd'?;
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }

    #[test]
    fn simplify_grammar5() {
        let source = r#"
            S ::= 'ab'S? | 'jk'(((A)));
            A ::= 'cd'|'cd'|A'c'|'Ac';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }

    #[test]
    fn simplify_grammar6() {
        let source = r#"
            S ::= 'cd'A;
            A ::= #"";
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        println!("{:?}", result);
        assert_snapshot!(result)
    }

    #[test]
    fn simplify_grammar9() {
        let source = r#"
            S ::= 'c'|'a'|'b'|'d';
            A ::= #"";
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }
    #[test]
    fn simplify_grammar10() {
        let source = r#"
            S ::= except!('c')|except!('c',10)|except!(A);
            A ::= 'a'|'B'|'qa';
        "#;
        let result = get_grammar(source)
            .unwrap()
            .validate_grammar(
                "S",
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            )
            .unwrap()
            .simplify_grammar(
                CompressionConfig {
                    min_terminals: 2,
                    regex_config: crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
                },
                crate::regex::FiniteStateAutomatonConfig::Dfa(Config::default()),
            );
        assert_snapshot!(result)
    }
}
