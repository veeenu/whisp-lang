use std::ops::Deref;
use std::rc::{Rc, Weak};

use ahash::AHashMap as HashMap;
use thiserror::Error;

use crate::ast::{
    Error as ParseError, Expression, FunctionCall, Identifier, Program, Statement, StatementBlock,
    StatementBlockItem, WhispString,
};

#[derive(Debug, Error)]
pub enum Error {
    #[error("parse error")]
    ParseError(#[from] ParseError),
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub enum Object {
    String(WhispString),
    List(Vec<Object>),
    Dict(HashMap<String, Object>),
    Option(Option<Weak<Object>>),
    Function(Weak<Function>),
    Builtin(Builtin),
}

#[derive(Debug, Clone)]
pub struct Function {
    formal_parameters: Vec<Identifier>,
    statements: StatementBlock,
}

#[derive(Debug, Clone, Copy)]
pub enum Builtin {
    Run,
    Spawn,
    Print,
}

#[derive(Debug)]
pub struct Interpreter {
    stack: ScopeStack,
}

impl Interpreter {
    pub fn new(code: &str) -> Result<Self> {
        let program = Program::parse(code).map_err(Error::from)?;
        let stack = ScopeStack::new();

        Ok(Self { stack })
    }
}

#[derive(Default, Debug)]
pub struct Scope {
    names: HashMap<String, Rc<Object>>,
}

impl Scope {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn declare_object(&mut self, identifier: &Identifier, object: Object) -> Weak<Object> {
        self.names.insert(identifier.to_string(), Rc::new(object));
        self.lookup(identifier).unwrap()
    }

    pub fn lookup(&self, identifier: &Identifier) -> Option<Weak<Object>> {
        self.names.get(identifier.deref()).map(Rc::downgrade)
    }
}

#[derive(Debug)]
pub struct ScopeStack(Vec<Scope>);

impl Default for ScopeStack {
    fn default() -> Self {
        Self(vec![Scope::new()])
    }
}

impl ScopeStack {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn push(&mut self) -> &mut Scope {
        self.0.push(Scope::new());
        self.current()
    }

    pub fn pop(&mut self) {
        if self.0.len() > 1 {
            self.0.pop();
        }
    }

    pub fn current(&mut self) -> &mut Scope {
        self.0.last_mut().unwrap()
    }

    pub fn lookup(&mut self, identifier: &Identifier) -> Option<Weak<Object>> {
        self.0.iter_mut().rev().find_map(|scope| scope.lookup(identifier))
    }

    pub fn evaluate_statement_block(&mut self, block: &StatementBlock) -> Object {
        for block_item in block {
            match block_item {
                StatementBlockItem::Statement(statement) => self.evaluate_statement(statement),
                StatementBlockItem::Expression(expression) => self.evaluate_expression(expression),
            };
        }

        if let Some(tail_expr) = block.tail_expr() {
            self.evaluate_expression(tail_expr)
        } else {
            Object::Option(None)
        }
    }

    pub fn evaluate_statement(&mut self, expr: &Statement) -> Object {
        Object::Option(None)
    }

    pub fn evaluate_expression(&mut self, expr: &Expression) -> Object {
        match expr {
            Expression::String(s) => Object::String(s.clone()),
            Expression::FunctionCall(function_call) => self.function_call(function_call),
            Expression::StatementBlock(block) => self.evaluate_statement_block(block),
        }
    }

    pub fn lexical_declaration() {}
    pub fn function_declaration() {}
    pub fn function_call(&mut self, foo: &FunctionCall) -> Object {
        Object::Option(None)
    }
}
