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
            rule => Err(Error::UnexpectedRule(rule)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionCall {
    function_name: Identifier,
    arguments: Vec<Argument>,
}

impl TryFrom<Pair<'_>> for FunctionCall {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        let mut children = match value.as_rule() {
            Rule::function_call => value.into_inner(),
            rule => return Err(Error::UnexpectedRule(rule)),
        };

        let function_name = children
            .next()
            .ok_or_else(|| Error::Unexpected("Function has no name".to_string()))
            .and_then(Identifier::try_from)?;

        let arguments = children.map(Argument::try_from).collect::<Result<Vec<_>>>()?;

        Ok(Self { function_name, arguments })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier(String);

impl TryFrom<Pair<'_>> for Identifier {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            Rule::identifier => Ok(Self(value.as_str().to_string())),
            rule => Err(Error::UnexpectedRule(rule)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Argument {
    String(WhispString),
    StatementBlock(Box<StatementBlock>),
}

impl TryFrom<Pair<'_>> for Argument {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            Rule::argument => Self::try_from(value.into_inner().next().unwrap()),
            Rule::statement_block => {
                Ok(Self::StatementBlock(Box::new(StatementBlock::try_from(value)?)))
            },
            Rule::string => Ok(Self::String(WhispString::try_from(value)?)),
            rule => Err(Error::UnexpectedRule(rule)),
        }
    }
}

// TODO last statement should return??
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatementBlock(Vec<Statement>);

impl TryFrom<Pair<'_>> for StatementBlock {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        Self::try_from(value.into_inner())
    }
}

impl TryFrom<Pairs<'_>> for StatementBlock {
    type Error = Error;

    fn try_from(value: Pairs<'_>) -> Result<Self> {
        value.map(Statement::try_from).collect::<Result<Vec<Statement>>>().map(Self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    LexicalDeclaration(LexicalDeclaration),
    FunctionDeclaration(FunctionDeclaration),
    FunctionCall(FunctionCall),
    String(WhispString),
}

impl TryFrom<Pair<'_>> for Statement {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {
            Rule::function_declaration => {
                FunctionDeclaration::try_from(value).map(Self::FunctionDeclaration)
            },
            Rule::lexical_declaration => {
                LexicalDeclaration::try_from(value).map(Self::LexicalDeclaration)
            },
            Rule::function_call => FunctionCall::try_from(value).map(Self::FunctionCall),
            Rule::string => WhispString::try_from(value).map(Self::String),
            rule => Err(Error::UnexpectedRule(rule)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexicalDeclaration {
    identifier: Identifier,
    statement_block: StatementBlock,
}

impl TryFrom<Pair<'_>> for LexicalDeclaration {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        // Extract child nodes, or bail out if supplied node is not a lexical declaration.
        let mut children = match value.as_rule() {
            Rule::lexical_declaration => value.into_inner(),
            rule => return Err(Error::UnexpectedRule(rule)),
        };

        // Extract the binding identifier.
        let identifier = children
            .next()
            .ok_or_else(|| Error::Unexpected("Lexical declaration has no binding name".to_string()))
            .and_then(Identifier::try_from)?;

        // Wrap a single statement in a statement block, or extract all the
        // statements together as a block.
        let statement_block =
            if let Some(Rule::statement) = children.peek().map(|pair| pair.as_rule()) {
                // Get first child. We can unwrap here as we just peeked for
                // the existence of the node.
                let statement = Statement::try_from(children.next().unwrap())?;

                StatementBlock(vec![statement])
            } else {
                StatementBlock::try_from(children)?
            };

        Ok(LexicalDeclaration { identifier, statement_block })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDeclaration {
    identifier: Identifier,
    formal_parameters: Vec<Identifier>,
    statement_block: StatementBlock,
}

impl TryFrom<Pair<'_>> for FunctionDeclaration {
    type Error = Error;

    fn try_from(value: Pair<'_>) -> Result<Self> {
        match value.as_rule() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn try_parse<'a, T>(rule: Rule, code: &'a str) -> Result<T>
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
