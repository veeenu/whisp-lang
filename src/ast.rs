use pest::Parser;
use thiserror::Error;

use crate::parser::*;

type Pair<'a> = pest::iterators::Pair<'a, Rule>;

#[derive(Error, Debug)]
pub enum Error {
    #[error("pest error")]
    PestError(Box<pest::error::Error<Rule>>),
    #[error("unexpected rule")]
    UnexpectedRule(Rule),
    // #[error("generic")]
    // Generic(String),
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(value: pest::error::Error<Rule>) -> Self {
        Error::PestError(Box::new(value))
    }
}

/// Language string type.
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

    fn try_from(value: Pair<'_>) -> Result<Self, Self::Error> {
        match value.as_rule() {
            // Recurse and evaluate inner node types.
            Rule::string | Rule::quoted_string_block | Rule::raw_quoted_string_block => {
                Self::try_from(value.into_inner().next().unwrap())
            },
            // Evaluate string directly.
            Rule::quoted_string | Rule::raw_quoted_string | Rule::unquoted_string => {
                Ok(Self(value.as_str().to_string()))
            },
            rule => Err(Error::UnexpectedRule(rule)),
        }
    }
}

/// Function call
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionCall {
    function_name: Identifier,
    arguments: Vec<Argument>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier(String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Argument {
    String(WhispString),
    StatementBlock(Box<StatementBlock>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatementBlock(Vec<Statement>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    LexicalDeclaration(LexicalDeclaration),
    FunctionDeclaration(FunctionDeclaration),
    FunctionCall(FunctionCall),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexicalDeclaration {
    identifier: Identifier,
    statement: Box<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDeclaration {
    identifier: Identifier,
    formal_parameters: Vec<Identifier>,
    statement_block: StatementBlock,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn try_parse<'a, T>(rule: Rule, code: &'a str) -> Result<T, Error>
    where
        T: std::fmt::Debug + TryFrom<Pair<'a>, Error = Error>,
    {
        WhispParser::parse(rule, code.trim())
            .map_err(Error::from)
            .and_then(|mut pairs| T::try_from(pairs.next().unwrap()))
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
}
