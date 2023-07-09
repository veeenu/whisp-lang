use std::ops::Deref;

use pest::Parser;
use thiserror::Error;

use crate::parser::*;

type Pair<'a> = pest::iterators::Pair<'a, Rule>;
type Pairs<'a> = pest::iterators::Pairs<'a, Rule>;
type Result<T> = std::result::Result<T, Error>;

#[derive(Error, Debug)]
pub enum Error {
    #[error("pest error")]
    PestError(Box<pest::error::Error<Rule>>),
    #[error("unexpected")]
    Unexpected(String),
    #[error("unexpected rule")]
    UnexpectedRule(Rule, usize, usize, usize, usize),
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(value: pest::error::Error<Rule>) -> Self {
        Error::PestError(Box::new(value))
    }
}

impl Error {
    pub fn unexpected_rule(value: Pair<'_>) -> Self {
        let rule = value.as_rule();
        let span = value.as_span();

        let (start_row, start_col) = span.start_pos().line_col();
        let (end_row, end_col) = span.end_pos().line_col();

        Self::UnexpectedRule(rule, start_row, start_col, end_row, end_col)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program(Vec<FunctionDeclaration>);

impl TryFrom<Pair<'_>> for Program {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        let children = match value.as_rule() {
            Rule::program => value.into_inner(),
            _ => return Err(Error::unexpected_rule(value)),
        };

        children
            .filter(|node| node.as_rule() != Rule::EOI)
            .map(FunctionDeclaration::try_from)
            .collect::<Result<Vec<_>>>()
            .map(Self)
    }
}

impl Program {
    pub fn parse(code: &str) -> Result<Self> {
        WhispParser::parse(Rule::program, code.trim()).map_err(Error::from).and_then(|mut pairs| {
            let pair = pairs.next().unwrap();
            Program::try_from(pair)
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexicalDeclaration {
    identifier: Identifier,
    expression: Expression,
}

impl TryFrom<Pair<'_>> for LexicalDeclaration {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        // Extract child nodes, or bail out if supplied node is not a lexical declaration.
        let mut children = match value.as_rule() {
            Rule::lexical_declaration => value.into_inner(),
            _ => return Err(Error::unexpected_rule(value)),
        };

        // Extract the binding identifier.
        let identifier = children
            .next()
            .ok_or_else(|| Error::Unexpected("Lexical declaration has no binding name".to_string()))
            .and_then(Identifier::try_from)?;

        let expression = children
            .next()
            .ok_or_else(|| {
                Error::Unexpected("Lexical declaration has no statement node".to_string())
            })
            .and_then(Expression::try_from)?;

        Ok(LexicalDeclaration { identifier, expression })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDeclaration {
    visibility_modifier: VisibilityModifier,
    identifier: Identifier,
    formal_parameters: Vec<Identifier>,
    statement_block: StatementBlock,
}

impl FunctionDeclaration {
    fn parse_formal_parameters(value: Pair<'_>) -> Result<Vec<Identifier>> {
        let children = match value.as_rule() {
            Rule::formal_parameters => value.into_inner(),
            _ => return Err(Error::unexpected_rule(value)),
        };

        children.map(Identifier::try_from).collect()
    }
}

impl TryFrom<Pair<'_>> for FunctionDeclaration {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        let mut children = match value.as_rule() {
            Rule::function_declaration => value.into_inner(),
            _ => return Err(Error::unexpected_rule(value)),
        };

        let visibility_modifier =
            if let Some(Rule::visibility_modifier) = children.peek().map(|pair| pair.as_rule()) {
                // Consume the visibility modifier token
                match children.next().unwrap().as_str() {
                    "pub" => VisibilityModifier::Public,
                    x => return Err(Error::Unexpected(format!("visibility modifier {x}"))),
                }
            } else {
                VisibilityModifier::Private
            };

        let identifier = children
            .next()
            .ok_or_else(|| {
                Error::Unexpected("Function declaration has no name identifier".to_string())
            })
            .and_then(Identifier::try_from)?;

        let formal_parameters = children
            .next()
            .ok_or_else(|| {
                Error::Unexpected("Function declaration has no formal parameters".to_string())
            })
            .and_then(Self::parse_formal_parameters)?;

        let statement_block = children
            .next()
            .ok_or_else(|| {
                Error::Unexpected("Function declaration has no statement block".to_string())
            })
            .and_then(StatementBlock::try_from)?;

        Ok(Self { visibility_modifier, identifier, formal_parameters, statement_block })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VisibilityModifier {
    Public,
    Private,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier(String);

impl TryFrom<Pair<'_>> for Identifier {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            Rule::identifier => Ok(Self(value.as_str().to_string())),
            _ => Err(Error::unexpected_rule(value)),
        }
    }
}

impl Deref for Identifier {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0.as_str()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementBlockItem {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatementBlock(Vec<StatementBlockItem>, Option<Expression>);

impl TryFrom<Pair<'_>> for StatementBlock {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        Self::try_from(value.into_inner())
    }
}

impl TryFrom<Pairs<'_>> for StatementBlock {
    type Error = Error;

    fn try_from(value: Pairs<'_>) -> Result<Self> {
        let mut statements = Vec::new();
        let mut tail_expr = None;

        for pair in value {
            if let Some("tail_expr") = pair.as_node_tag() {
                tail_expr = Some(Expression::try_from(pair)?);
                continue;
            }

            let statement_block_item = match pair.as_rule() {
                Rule::statement => Statement::try_from(pair).map(StatementBlockItem::Statement),
                Rule::expression => Expression::try_from(pair).map(StatementBlockItem::Expression),
                _ => Err(Error::unexpected_rule(pair)),
            }?;

            statements.push(statement_block_item);
        }

        Ok(Self(statements, tail_expr))
    }
}

impl<'a> IntoIterator for &'a StatementBlock {
    type Item = &'a StatementBlockItem;
    type IntoIter = std::slice::Iter<'a, StatementBlockItem>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl StatementBlock {
    pub fn tail_expr(&self) -> Option<&Expression> {
        self.1.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    LexicalDeclaration(LexicalDeclaration),
    FunctionDeclaration(FunctionDeclaration),
}

impl TryFrom<Pair<'_>> for Statement {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            Rule::statement => Self::try_from(value.into_inner().next().unwrap()),
            Rule::function_declaration => {
                FunctionDeclaration::try_from(value).map(Self::FunctionDeclaration)
            },
            Rule::lexical_declaration => {
                LexicalDeclaration::try_from(value).map(Self::LexicalDeclaration)
            },
            _ => Err(Error::unexpected_rule(value)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    String(WhispString),
    FunctionCall(FunctionCall),
    StatementBlock(Box<StatementBlock>),
}

impl TryFrom<Pair<'_>> for Expression {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            Rule::expression => Self::try_from(value.into_inner().next().unwrap()),
            Rule::parenthesis_expression => Self::try_from(value.into_inner().next().unwrap()),
            Rule::statement_block => {
                Ok(Self::StatementBlock(Box::new(StatementBlock::try_from(value)?)))
            },
            Rule::string => Ok(Self::String(WhispString::try_from(value)?)),
            Rule::function_call => Ok(Self::FunctionCall(FunctionCall::try_from(value)?)),
            _ => Err(Error::unexpected_rule(value)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionCall {
    function_name: Identifier,
    arguments: Vec<Expression>,
}

impl TryFrom<Pair<'_>> for FunctionCall {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        let mut children = match value.as_rule() {
            Rule::function_call => value.into_inner(),
            _ => return Err(Error::unexpected_rule(value)),
        };

        let function_name = children
            .next()
            .ok_or_else(|| Error::Unexpected("Function has no name".to_string()))
            .and_then(Identifier::try_from)?;

        let arguments = children.map(Expression::try_from).collect::<Result<Vec<_>>>()?;

        Ok(Self { function_name, arguments })
    }
}

/// Language primitive string type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhispString(String);

impl WhispString {
    /// Create a new [`WhispString`] from any string type.
    pub fn new<S: Into<String>>(s: S) -> Self {
        Self(s.into())
    }
}

impl TryFrom<Pair<'_>> for WhispString {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            // Recurse and evaluate inner node types.
            Rule::string | Rule::quoted_string_block | Rule::raw_quoted_string_block => {
                Self::try_from(value.into_inner().next().unwrap())
            },
            // Evaluate string directly.
            Rule::quoted_string | Rule::raw_quoted_string | Rule::unquoted_string => {
                Ok(Self(value.as_str().to_string()))
            },
            _ => Err(Error::unexpected_rule(value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;

    fn try_parse<'a, T>(rule: Rule, code: &'a str) -> Result<T>
    where
        T: std::fmt::Debug + TryFrom<Pair<'a>, Error = Error>,
    {
        WhispParser::parse(rule, code.trim()).map_err(Error::from).and_then(|mut pairs| {
            let pair = pairs.next().unwrap();
            T::try_from(pair)
        })
    }

    fn assert_match<'a, T>(rule: Rule, code: &'a str, target: T)
    where
        T: std::fmt::Debug + PartialEq + TryFrom<Pair<'a>, Error = Error>,
    {
        match try_parse::<T>(rule, code) {
            Ok(node) => {
                println!("{node:#?}");
                assert_eq!(node, target)
            },
            Err(e) => panic!("{e:?}"),
        }
    }

    #[test]
    fn test_string() {
        assert_match(Rule::string, r#""string""#, WhispString::new("string"));
        assert_match(Rule::string, r#""another string""#, WhispString::new("another string"));
        assert_match(Rule::string, r#"another_string"#, WhispString::new("another_string"));
        assert_match(
            Rule::string,
            r#"another_string!_no,-seriously"#,
            WhispString::new("another_string!_no,-seriously"),
        );
        assert_match(
            Rule::string,
            "r#\"I am a raw string!!!{};\"#",
            WhispString::new("I am a raw string!!!{};"),
        );
    }

    #[test]
    fn test_parse_program() {
        let r = try_parse::<Program>(Rule::program, include_str!("../examples/git_aliases.whisp"));
        println!("{r:#?}");
    }
}
