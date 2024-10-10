use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;
use nom::bytes::complete::{escaped, take_until};
use nom::character::complete::none_of;
use nom::combinator::opt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete,
    combinator::recognize,
    error::{VerboseError, VerboseErrorKind},
    multi::{many0_count, many1},
    sequence::{delimited, pair, preceded, terminated},
    Err, IResult,
};
use parse_hyperlinks::take_until_unbalanced;

use crate::{
    node::{RegexExtKind, SymbolKind},
    Expression, Node,
};
type Res<T, U> = IResult<T, U, VerboseError<T>>;

fn identifier(input: &str) -> Res<&str, &str> {
    recognize(pair(
        alt((complete::alpha1, tag("_"))),
        many0_count(alt((complete::alphanumeric1, tag("_")))),
    ))(input)
}

fn remove_comment(input: &str) -> Res<&str, Option<&str>> {
    let mut remove = delimited(
        complete::multispace0,
        opt(delimited(tag("(*"), take_until("*)"), tag("*)"))),
        complete::multispace0,
    );
    let (mut input, _) = remove(input)?;
    while input.len() >= 2 && &input[..2] == "(*" {
        (input, _) = remove(input)?;
    }
    Ok((input, None))
}

fn parse_lhs(input: &str) -> Res<&str, &str> {
    let (input, lhs) = preceded(remove_comment, identifier)(input)?;
    // panic!("{:?}", input);
    let (input, _) = preceded(complete::multispace0, alt((tag("="), tag("::="))))(input)?;
    Ok((input, lhs))
}

fn parse_rhs(input: &str) -> Res<&str, Node> {
    let (input, rhs) = preceded(
        complete::multispace0,
        terminated(
            parse_multiple,
            delimited(complete::multispace0, complete::char(';'), remove_comment),
        ),
    )(input)?;

    Ok((input, rhs))
}

fn unescape<'a>(input: &'a str, context: &'a str) -> Res<&'a str, String> {
    Ok((
        context,
        unescaper::unescape(input).map_err(|_| {
            Err::Error(VerboseError {
                errors: vec![(input, VerboseErrorKind::Context("Invalid escape sequence"))],
            })
        })?,
    ))
}

fn parse_terminal(input: &str) -> Res<&str, Node> {
    let (input, string) = alt((
        delimited(
            complete::char('\''),
            opt(escaped(
                none_of("\\\'"),
                '\\',
                nom::character::complete::anychar,
            )),
            complete::char('\''),
        ),
        delimited(
            complete::char('"'),
            opt(escaped(
                none_of("\\\""),
                '\\',
                nom::character::complete::anychar,
            )),
            complete::char('"'),
        ),
    ))(input)?;
    let string = string.unwrap_or("");
    let (_, string) = unescape(string, input)?;
    Ok((input, Node::Terminal(string.to_string())))
}

fn parse_sub_string(input: &str) -> Res<&str, Node> {
    let (input, string) = alt((
        delimited(
            tag("#substrs'"),
            opt(escaped(
                none_of("\\\'"),
                '\\',
                nom::character::complete::anychar,
            )),
            complete::char('\''),
        ),
        delimited(
            tag("#substrs\""),
            opt(escaped(
                none_of("\\\""),
                '\\',
                nom::character::complete::anychar,
            )),
            complete::char('"'),
        ),
    ))(input)?;
    let string = string.unwrap_or("");
    let (_, string) = unescape(string, input)?;
    Ok((input, Node::Substrings(string.to_string())))
}

fn parse_regex_string(input: &str) -> Res<&str, Node> {
    let mut early = false;
    let result: Result<(&str, Option<&str>), Err<VerboseError<&str>>> = alt((
        delimited(
            tag("#'"),
            opt(escaped(
                none_of("\\\'"),
                '\\',
                nom::character::complete::anychar,
            )),
            complete::char('\''),
        ),
        delimited(
            tag("#\""),
            opt(escaped(
                none_of("\\\""),
                '\\',
                nom::character::complete::anychar,
            )),
            complete::char('"'),
        ),
    ))(input);
    let (input, string) = result.or_else(|_| {
        early = true;
        alt((
            delimited(
                tag("#e'"),
                opt(escaped(
                    none_of("\\\'"),
                    '\\',
                    nom::character::complete::anychar,
                )),
                complete::char('\''),
            ),
            delimited(
                tag("#e\""),
                opt(escaped(
                    none_of("\\\""),
                    '\\',
                    nom::character::complete::anychar,
                )),
                complete::char('"'),
            ),
        ))(input)
    })?;
    let string = string.unwrap_or("");
    let (_, string) = unescape(string, input)?;
    let node = if early {
        Node::EarlyEndRegexString(format!(r"\A(?:{string})\z"))
    } else {
        Node::RegexString(format!(r"\A(?:{string})\z"))
    };
    regex_syntax::ast::parse::Parser::new() // initialize 200 bytes of memory on stack for regex may not be very efficient. Maybe we need to modify it later.
        .parse(&string)
        .map_err(|_: regex_syntax::ast::Error| {
            nom::Err::Error(VerboseError {
                errors: vec![(
                    "Invalid regex string: ",
                    nom::error::VerboseErrorKind::Context(string.leak()),
                    // This is not the optimum choice but is the easiest way.
                    // And the memory leak will not be a problem unless someone has unusually big regex strings and/or repeatedly tries to parse a faulty grammar.
                )],
            })
        })
        .map(|_| (input, node))
}

fn parse_nonterminal(input: &str) -> Res<&str, Node> {
    let (input, symbol) = preceded(
        complete::multispace0,
        terminated(identifier, complete::multispace0),
    )(input)?;

    Ok((input, Node::Nonterminal(symbol.to_string())))
}

fn parse_multiple(input: &str) -> Res<&str, Node> {
    let (input, node) = preceded(complete::multispace0, many1(parse_node))(input)?;

    match node {
        _ if node.len() == 1 => Ok((input, node[0].clone())),
        _ => Ok((input, Node::Multiple(node))),
    }
}

fn parse_node(input: &str) -> Res<&str, Node> {
    let (mut input, mut left_node) = preceded(
        complete::multispace0,
        alt((
            parse_group,
            parse_optional,
            parse_repeat,
            parse_terminal,
            parse_regex_string,
            parse_nonterminal,
            parse_sub_string,
        )),
    )(input)?;

    let optional_regex_ext: Res<&str, RegexExtKind> = parse_regex_ext(input);

    if let Ok((s, regex_ext_kind)) = optional_regex_ext {
        input = s;
        left_node = Node::RegexExt(Box::new(left_node), regex_ext_kind);
    }

    let optional_symbol: Res<&str, (SymbolKind, Node)> = parse_symbol(input);

    if let Ok((input, (symbol, right_node))) = optional_symbol {
        Ok((
            input,
            Node::Symbol(Box::new(left_node), symbol, Box::new(right_node)),
        ))
    } else {
        Ok((input, left_node))
    }
}

fn parse_regex_ext(input: &str) -> Res<&str, RegexExtKind> {
    let (input, regex_ext) = preceded(
        complete::multispace0,
        alt((
            complete::char('*'),
            complete::char('+'),
            complete::char('?'),
        )),
    )(input)?;

    let regex_kind = match regex_ext {
        '*' => RegexExtKind::Repeat0,
        '+' => RegexExtKind::Repeat1,
        '?' => RegexExtKind::Optional,
        _ => unreachable!("Unexpected regex extension symbol. this should not happen"),
    };

    Ok((input, regex_kind))
}

fn parse_symbol(input: &str) -> Res<&str, (SymbolKind, Node)> {
    let (input, symbol_pair) = preceded(
        complete::multispace0,
        alt((parse_concatenation, parse_alternation)),
    )(input)?;

    Ok((input, symbol_pair))
}

fn parse_concatenation(input: &str) -> Res<&str, (SymbolKind, Node)> {
    let (input, node) = preceded(complete::char(','), parse_node)(input)?;

    Ok((input, (SymbolKind::Concatenation, node)))
}

fn parse_alternation(input: &str) -> Res<&str, (SymbolKind, Node)> {
    let (input, node) = preceded(tag("|"), parse_node)(input)?;

    Ok((input, (SymbolKind::Alternation, node)))
}

fn parse_delimited_node(
    input: &str,
    opening_bracket: char,
    closing_bracket: char,
) -> Res<&str, &str> {
    let result = delimited(
        complete::char(opening_bracket),
        take_until_unbalanced(opening_bracket, closing_bracket),
        complete::char(closing_bracket),
    )(input);
    match result {
        Ok((input, inner)) => Ok((input, inner)),
        Err(_) => Err(Err::Error(VerboseError {
            errors: vec![(
                input,
                VerboseErrorKind::Context("Incomplete delimited node"),
            )],
        })),
    }
}

fn parse_group(input: &str) -> Res<&str, Node> {
    let (input, inner) = parse_delimited_node(input, '(', ')')?;
    let (_, node) = preceded(complete::multispace0, parse_multiple)(inner)?;
    Ok((input, Node::Group(Box::new(node))))
}

fn parse_optional(input: &str) -> Res<&str, Node> {
    let (input, inner) = parse_delimited_node(input, '[', ']')?;
    let (_, node) = preceded(complete::multispace0, parse_multiple)(inner)?;

    Ok((
        input,
        Node::RegexExt(Box::new(node), RegexExtKind::Optional),
    ))
}

fn parse_repeat(input: &str) -> Res<&str, Node> {
    let (input, inner) = parse_delimited_node(input, '{', '}')?;
    let (_, node) = preceded(complete::multispace0, parse_multiple)(inner)?;

    Ok((input, Node::RegexExt(Box::new(node), RegexExtKind::Repeat0)))
}

pub(crate) fn parse_expressions(input: &str) -> Res<&str, Vec<Expression>> {
    let mut source = input;
    let mut expressions = Vec::<Expression>::new();

    while !source.is_empty() {
        let (input, lhs) = parse_lhs(source)?;
        let (input, rhs) = parse_rhs(input)?;

        expressions.push(Expression {
            lhs: lhs.to_string(),
            rhs,
        });

        source = input.trim_start();
    }

    Ok((input, expressions))
}

#[cfg(test)]
mod test {
    use insta::assert_yaml_snapshot;

    use crate::node::NodeWithID;

    use super::*;

    #[test]
    fn test_parse() {
        let src = r"
            Filter ::= ( First ' ' )? ( Number '~ ' )? ( Number '-' Number ) ( ' ' Number '~' )? ( ' Hz' )? ( ' B' )? ( ' I' )? ( ' A' )?;
            First  ::= #'[A-Za-z][A-Za-z0-9_+]*';
            Number ::= Digits ( ( '.' | ',' ) Digits? )?;
            Digits ::= #'[0-9]+';
        ";

        let (_, vec) = parse_expressions(src).unwrap();

        println!("{:#?}", vec);
    }

    #[test]
    fn simple_alternation() {
        let source = r"
            filter ::= a | b;
            a ::= 'a';
            b ::= 'b';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn space_before_semi() {
        let source = r"
             filter ::= a | b ;
             a ::= 'a';
             b ::= 'b';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn underscore() {
        let source = r"
             filter ::= a_b;
             a_b ::= 'a' | 'b';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn multiple_underscores() {
        let source = r"
             filter ::= a_b_cat;
             a_b_cat ::= 'a' | 'b';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn alternation_precidence() {
        let source = r"
             filter ::= 'a' | 'b' 'c';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn alternation_precidence_multiple() {
        let source = r"
             filter ::= 'a' | 'b' | 'c';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn alternation_precidence_nested() {
        let source = r"
             filter ::= 'a' | 'b'  'c' | 'd';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn alternation_precidence_group() {
        let source = r"
             filter ::= 'a' | ('b' 'c');
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn concat_precidence() {
        let source = r"
             filter ::= 'a' | 'b' , 'c' , 'd';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn concat_precidence_reverse() {
        let source = r"
             filter ::= 'a' , 'b' , 'c' | 'd';
        ";
        let result = parse_expressions(source).unwrap();
        assert_yaml_snapshot!(result)
    }

    #[test]
    fn escaped_nonterminal() {
        let source = r#"
single_quote ::= '\t\r\n\'\u004C';
double_quote ::= "\t\r\n\"\u004C";
regex_double_quote ::= #"\t\r\n\"\u004C";
regex_single_quote ::= #'\t\r\n\'\u004C';
string ::= #'"([^\\"\u0000-\u001f]|\\["\\bfnrt/]|\\\\u[0-9A-Fa-f]{4})*"';
        "#;
        let result = parse_expressions(source);
        assert_yaml_snapshot!(result.unwrap())
    }

    #[test]
    fn regexes() {
        let source = r#"
            filter ::= #'[a-z]+';
            filter2 ::= #"[a-z]+";
            filter3 ::= #e"[a-z]+";
            filter4 ::= #e'[a-z]+';
            "#;
        let result = parse_expressions(source);
        assert_yaml_snapshot!(result.unwrap())
    }
    #[test]
    fn sub_strings() {
        let source = r#"
            filter ::= #substrs'abc';
            filter2 ::= #substrs"abc";
            "#;
        let result = parse_expressions(source);
        assert_yaml_snapshot!(result.unwrap())
    }
    #[test]
    #[should_panic]
    fn empty1() {
        let source = r#"
             except ::= ;
        "#;
        let _ = parse_expressions(source).unwrap();
    }

    #[test]
    #[should_panic]
    fn empty2() {
        let source = r#"
             except ::= A|;
        "#;
        let _ = parse_expressions(source).unwrap();
    }
    #[test]
    fn empty3() {
        let source = r#"
             except ::='';
             except ::= #"";
        "#;
        let _ = parse_expressions(source).unwrap();
    }
    #[test]
    fn ensure_drop_work_correctly_for_node() {
        let mut node = Node::Group(Box::new(Node::Terminal("a".to_string())));
        let mut mut_ref = match &mut node {
            Node::Group(node) => &mut **node,
            _ => unreachable!(),
        };
        for _ in 0..1000000 {
            *mut_ref = Node::Group(Box::new(Node::Terminal("a".to_string())));
            mut_ref = match &mut *mut_ref {
                Node::Group(node) => node,
                _ => unreachable!(),
            };
        }
    }
    #[test]
    fn ensure_drop_work_correctly_for_node_with_ids() {
        let mut node: NodeWithID = NodeWithID::Group(Box::new(NodeWithID::Unknown));
        let mut mut_ref = match &mut node {
            NodeWithID::Group(node) => &mut **node,
            _ => unreachable!(),
        };
        for _ in 0..1000000 {
            *mut_ref = NodeWithID::Group(Box::new(NodeWithID::Unknown));
            mut_ref = match &mut *mut_ref {
                NodeWithID::Group(node) => node,
                _ => unreachable!(),
            };
        }
    }
}
