use std::fmt::Debug;
use std::ops::Deref;

use from_pest::{ConversionError, FromPest, Void};
use pest::{Parser, Span};
use pest_ast::FromPest;
use thiserror::Error;

use crate::parser::*;

type Result<T> = std::result::Result<T, Error>;

#[derive(Error, Debug)]
pub enum Error {
    #[error("pest error")]
    PestError(Box<pest::error::Error<Rule>>),
    #[error("pest conversion error")]
    ConversionError(String),
    #[error("unexpected")]
    Unexpected(String),
    #[error("unexpected rule")]
    UnexpectedRule(Rule, usize, usize, usize, usize),
}

impl<T: Debug> From<ConversionError<T>> for Error {
    fn from(value: ConversionError<T>) -> Self {
        Error::ConversionError(format!("{value:?}"))
    }
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(value: pest::error::Error<Rule>) -> Self {
        Error::PestError(Box::new(value))
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::EOI))]
struct Eoi;

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::program))]
pub struct Program {
    declarations: Vec<FunctionDeclaration>,
    eoi: Eoi,
}

impl<'a> IntoIterator for &'a Program {
    type IntoIter = std::slice::Iter<'a, FunctionDeclaration>;
    type Item = &'a FunctionDeclaration;

    fn into_iter(self) -> Self::IntoIter {
        self.declarations.iter()
    }
}

impl Program {
    pub fn parse(code: &str) -> Result<Self> {
        WhispParser::parse(Rule::program, code.trim())
            .map_err(Error::from)
            .and_then(|mut pairs| Program::from_pest(&mut pairs).map_err(Error::from))
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::lexical_declaration))]
pub struct LexicalDeclaration {
    pub identifier: Identifier,
    pub expression: Expression,
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::function_declaration))]
pub struct FunctionDeclaration {
    pub identifier: Identifier,
    pub formal_parameters: FormalParameters,
    pub statement_block: StatementBlock,
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::identifier))]
pub struct Identifier(#[pest_ast(outer(with(span_into_string)))] String);

impl Deref for Identifier {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0.as_str()
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::quoted_string))]
pub struct QuotedString(#[pest_ast(inner(with(span_into_string)))] String);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::raw_quoted_string))]
pub struct RawQuotedString(#[pest_ast(inner(with(span_into_string)))] String);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::unquoted_string))]
pub struct UnquotedString(#[pest_ast(outer(with(span_into_string)))] String);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::unquoted_list))]
pub struct UnquotedList(pub Vec<UnquotedString>);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::number))]
pub enum Number {
    Int(Int),
    Float(Float),
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::int))]
pub struct Int(#[pest_ast(outer(with(Int::parse)))] pub i64);

impl Int {
    fn parse(span: Span) -> i64 {
        span.as_str().parse().expect("Failed to parse int")
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::float))]
pub struct Float(#[pest_ast(outer(with(Float::parse)))] pub f64);

impl Float {
    fn parse(span: Span) -> f64 {
        span.as_str().parse().expect("Failed to parse float")
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::formal_parameters))]
pub struct FormalParameters(pub Vec<Identifier>);

fn span_into_string(span: Span) -> String {
    span.as_str().to_string()
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::statement_block))]
pub struct StatementBlock {
    items: Vec<StatementBlockItem>,
    tail: Option<Expression>,
}

impl<'a> IntoIterator for &'a StatementBlock {
    type IntoIter = std::slice::Iter<'a, StatementBlockItem>;
    type Item = &'a StatementBlockItem;

    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}

impl StatementBlock {
    pub fn tail_expr(&self) -> Option<&Expression> {
        self.tail.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::statement_block_item))]
pub enum StatementBlockItem {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::statement))]
pub enum Statement {
    FunctionDeclaration(FunctionDeclaration),
    LexicalDeclaration(LexicalDeclaration),
    Break(BreakStmt),
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::expression))]
pub enum Expression {
    #[pest_ast(outer(with(WhispString::from_pest)))]
    String(WhispString),
    Number(Number),
    UnquotedList(UnquotedList),
    FunctionCall(FunctionCall),
    ParenthesisExpression(ParenthesisExpression),
    StatementBlock(Box<StatementBlock>),
    IfExpr(IfExpr),
    Loop(LoopExpr),
    Identifier(Identifier),
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::parenthesis_expression))]
pub struct ParenthesisExpression(pub Box<Expression>);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::function_call))]
pub struct FunctionCall {
    function_name: Identifier,
    arguments: FunctionArgs,
}

impl FunctionCall {
    pub fn new<S: Into<String>>(function_name: S, arguments: Vec<Expression>) -> Self {
        Self { function_name: Identifier(function_name.into()), arguments: FunctionArgs(arguments) }
    }

    pub fn function_name(&self) -> &Identifier {
        &self.function_name
    }

    pub fn arguments(&self) -> &[Expression] {
        &self.arguments.0
    }
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::function_args))]
pub struct FunctionArgs(Vec<Expression>);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::if_expr))]
pub struct IfExpr {
    pub if_cond: Box<IfCond>,
    pub else_if_conds: Vec<ElseIfCond>,
    pub else_cond: Option<Box<ElseCond>>,
}

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::if_cond))]
pub struct IfCond(pub ParenthesisExpression, pub StatementBlock);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::else_if_cond))]
pub struct ElseIfCond(pub ParenthesisExpression, pub StatementBlock);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::else_cond))]
pub struct ElseCond(pub StatementBlock);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::loop_expr))]
pub struct LoopExpr(pub Box<StatementBlock>);

#[derive(Debug, Clone, PartialEq, FromPest)]
#[pest_ast(rule(Rule::break_stmt))]
pub struct BreakStmt(pub Option<Expression>);

//
// Support types
//

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhispString(String);

impl Deref for WhispString {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0.as_str()
    }
}

impl<'pest> FromPest<'pest> for WhispString {
    type Rule = Rule;
    type FatalError = Void;

    fn from_pest(
        pest: &mut pest::iterators::Pairs<'pest, Self::Rule>,
    ) -> std::result::Result<Self, ConversionError<Self::FatalError>> {
        if let Ok(quoted_string) = QuotedString::from_pest(pest) {
            Ok(WhispString::from(quoted_string))
        } else if let Ok(raw_quoted_string) = RawQuotedString::from_pest(pest) {
            Ok(WhispString::from(raw_quoted_string))
        } else {
            Err(ConversionError::NoMatch)
        }
    }
}

impl From<QuotedString> for WhispString {
    fn from(value: QuotedString) -> Self {
        WhispString(value.0)
    }
}

impl From<RawQuotedString> for WhispString {
    fn from(value: RawQuotedString) -> Self {
        WhispString(value.0)
    }
}

impl From<UnquotedString> for WhispString {
    fn from(value: UnquotedString) -> Self {
        WhispString(value.0)
    }
}

#[cfg(test)]
mod tests {
    use std::f64::consts::PI;

    use pest::Parser;

    use super::*;
    use crate::tests::*;

    fn parse_rule<'pest, T>(rule: Rule, code: &'pest str) -> T
    where
        T: std::fmt::Debug + FromPest<'pest, Rule = Rule>,
        <T as from_pest::FromPest<'pest>>::FatalError: std::fmt::Debug,
    {
        let mut pairs = WhispParser::parse(rule, code.trim()).unwrap();
        let r = T::from_pest(&mut pairs);
        assert!(r.is_ok(), "\"{code}\" for {rule:?} -> \n  {r:?} \n  {pairs:?}");
        println!("\x1b[32;1m{rule:?}\x1b[0m: \x1b[34;1m{code}\x1b[0m\n  {r:?}");
        r.unwrap()
    }

    macro_rules! p {
        ($ty:ty, $rule:expr, $code:expr, $pat:pat $(if $guard:expr)?) => {
            assert!(matches!(parse_rule::<$ty>($rule, $code), $pat $(if $guard)?));
        };
    }

    #[test]
    fn test_parse_all_cases() {
        init_test_log();

        p!(
            LexicalDeclaration,
            Rule::lexical_declaration,
            "let foo = (bar);",
            LexicalDeclaration {
                identifier: Identifier(_),
                expression: Expression::ParenthesisExpression(_)
            }
        );
        p!(FunctionDeclaration, Rule::function_declaration, "fn foo() {}", _);
        p!(Identifier, Rule::identifier, "baz123_", _);
        p!(QuotedString, Rule::quoted_string, "\"foo\"", _);
        p!(RawQuotedString, Rule::raw_quoted_string, "r#\"foo\"#", _);
        p!(UnquotedString, Rule::unquoted_string, "r#foo#", _);
        p!(UnquotedList, Rule::unquoted_list, "[[]]", _);
        p!(UnquotedList, Rule::unquoted_list, "[[git]]", _);
        p!(UnquotedList, Rule::unquoted_list, "[[ git ]]", _);
        p!(UnquotedList, Rule::unquoted_list, "[[ git! ]]", _);
        p!(UnquotedList, Rule::unquoted_list, "[[git rebase origin main]]", _);
        p!(Number, Rule::number, "314", Number::Int(Int(i)) if i == 314);
        p!(Number, Rule::number, "3.14", Number::Float(Float(x)) if (x - PI).abs() < 0.01);
        p!(FormalParameters, Rule::formal_parameters, "(foo)", _);
        p!(FormalParameters, Rule::formal_parameters, "(foo, bar, baz)", _);
        p!(FormalParameters, Rule::formal_parameters, "(foo, bar, baz,)", _);
        p!(
            StatementBlock,
            Rule::statement_block,
            "{ foo; bar (baz, quux); }",
            StatementBlock { tail: None, .. }
        );
        p!(
            StatementBlock,
            Rule::statement_block,
            "{ foo; bar (baz, quux); quux }",
            StatementBlock { tail: Some(_), .. }
        );
        p!(
            StatementBlock,
            Rule::statement_block,
            "{ quux }",
            StatementBlock { tail: Some(Expression::Identifier(quux)), .. }
            if quux.0 == "quux"
        );
        p!(StatementBlock, Rule::statement_block, "{ }", StatementBlock { tail: None, .. });
        p!(
            StatementBlockItem,
            Rule::statement_block_item,
            "let foo = (bar);",
            StatementBlockItem::Statement(Statement::LexicalDeclaration(LexicalDeclaration {
                expression: Expression::ParenthesisExpression(_),
                ..
            }))
        );
        p!(
            StatementBlockItem,
            Rule::statement_block_item,
            "foo;",
            StatementBlockItem::Expression(Expression::Identifier(_))
        );
        p!(Statement, Rule::statement, "fn foo() {}", Statement::FunctionDeclaration(_));
        p!(Statement, Rule::statement, "let foo = bar;", Statement::LexicalDeclaration(_));
        p!(Statement, Rule::statement, "break", Statement::Break(BreakStmt(None)));
        p!(Statement, Rule::statement, "break;", Statement::Break(BreakStmt(None)));
        p!(Statement, Rule::statement, "break foo", Statement::Break(BreakStmt(Some(_))));
        p!(Statement, Rule::statement, "break foo;", Statement::Break(BreakStmt(Some(_))));
        p!(Expression, Rule::expression, "\"foo\"", Expression::String(s) if s.deref() == "foo");
        p!(Expression, Rule::expression, "r#\"foo\"#", Expression::String(s) if s.deref() == "foo");
        p!(Expression, Rule::expression, "{}", Expression::StatementBlock(_));
        p!(Expression, Rule::expression, "({})", Expression::ParenthesisExpression(_));
        p!(Expression, Rule::expression, "run (foo, bar, baz);", Expression::FunctionCall(_));
        p!(Expression, Rule::expression, "if (foo) {}", Expression::IfExpr(_));
        p!(Expression, Rule::expression, "loop {}", Expression::Loop(_));
        p!(Expression, Rule::expression, "foo", Expression::Identifier(x) if x.0 == "foo");
        p!(ParenthesisExpression, Rule::parenthesis_expression, "(foo)", _);
        p!(FunctionCall, Rule::function_call, "foo()", _);
        p!(FunctionCall, Rule::function_call, "foo(bar)", _);
        p!(FunctionCall, Rule::function_call, "foo(bar, baz)", _);
        p!(FunctionArgs, Rule::function_args, "()", _);
        p!(FunctionArgs, Rule::function_args, "(foo)", _);
        p!(FunctionArgs, Rule::function_args, "(foo, bar)", _);
        p!(FunctionArgs, Rule::function_args, "(foo, bar,)", _);
        p!(FunctionArgs, Rule::function_args, "( foo,bar, )", _);
        p!(
            IfExpr,
            Rule::if_expr,
            "if (foo) { bar } else if (bar) { baz } else if (bar) { baz }else { quux }",
            IfExpr { else_if_conds, else_cond: Some(_), .. } if else_if_conds.len() == 2
        );
        p!(IfCond, Rule::if_cond, "if (foo) { bar }", _);
        p!(ElseIfCond, Rule::else_if_cond, "else if (foo) { bar }", _);
        p!(ElseCond, Rule::else_cond, "else { bar }", _);
        p!(LoopExpr, Rule::loop_expr, "loop { bar }", _);
        p!(BreakStmt, Rule::break_stmt, "break", BreakStmt(None));
        p!(BreakStmt, Rule::break_stmt, "break foo", BreakStmt(Some(Expression::Identifier(x))) if x.0 == "foo");
    }

    #[test]
    fn test_parse_program() {
        init_test_log();
        p!(Program, Rule::program, include_str!("../examples/git_aliases.whisp"), _);
    }
}
