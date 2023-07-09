use std::ops::Deref;
use std::rc::{Rc, Weak};

use ahash::AHashMap as HashMap;
use thiserror::Error;

use crate::ast::{Error as ParseError, Identifier, Program, StatementBlock, WhispString};

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

pub struct Interpreter {
    stack: (),
}

impl Interpreter {
    pub fn new(code: &str) -> Result<Self> {
        let program = Program::parse(code).map_err(Error::from)?;
        let mut stack = ();

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
        Rc::downgrade(&self.names.get(identifier.deref()).unwrap())
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
}
