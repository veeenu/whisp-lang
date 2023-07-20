use std::fmt::Display;
use std::ops::Deref;
use std::rc::{Rc, Weak};

use ahash::AHashMap as HashMap;
use thiserror::Error;

use crate::ast::{
    Error as ParseError, Expression, FunctionCall, FunctionDeclaration, Identifier,
    LexicalDeclaration, Program, Statement, StatementBlock, StatementBlockItem, WhispString,
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
    Option(Option<Box<Object>>),
    Function(Function),
    Builtin(Builtin),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::String(s) => write!(f, "{}", s.deref()),
            x => write!(f, "{x:#?}"),
        }
    }
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

impl Builtin {
    pub fn matches(name: &Identifier) -> Option<Builtin> {
        match name.deref() {
            "run" =>  Some( Builtin::Run ),
            "spawn" => Some( Builtin::Spawn ),
            "print" => Some( Builtin::Print ),
            _ => None
        }
    }

    pub fn run(&self, arguments: Vec<Rc<Object>>) -> Rc<Object> {
        match self {
            Builtin::Run => self.call_print(arguments),
            Builtin::Spawn => self.call_print(arguments),
            Builtin::Print => self.call_print(arguments),
        }
    }

    fn call_print(&self, arguments: Vec<Rc<Object>>) -> Rc<Object> {
        if arguments.is_empty() {
            return Rc::new(Object::Option(None));
        }

        let mut arguments = arguments.into_iter();
        print!("{}", arguments.next().unwrap());
        for arg in arguments {
            print!(" {arg}");
        }
        println!();
        Rc::new(Object::Option(None))
    }
}

#[derive(Debug)]
pub struct Interpreter {
    stack: ScopeStack,
}

impl Interpreter {
    pub fn new(code: &str) -> Result<Self> {
        let program = Program::parse(code).map_err(Error::from)?;
        let mut stack = ScopeStack::new();
        for decl in &program {
            stack.function_declaration(decl);
        }

        Ok(Self { stack })
    }

    pub fn call_function(&mut self, name: &str) -> Rc<Object> {
        self.stack.function_call(&FunctionCall::new(name, Vec::new()))
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

    pub fn declare_object(&mut self, identifier: &Identifier, object: Rc<Object>) -> Weak<Object> {
        self.names.insert(identifier.to_string(), object);
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

    pub fn evaluate_statement_block(&mut self, block: &StatementBlock) -> Rc<Object> {
        for block_item in block {
            match block_item {
                StatementBlockItem::Statement(statement) => self.evaluate_statement(statement),
                StatementBlockItem::Expression(expression) => self.evaluate_expression(expression),
            };
        }

        if let Some(tail_expr) = block.tail_expr() {
            self.evaluate_expression(tail_expr)
        } else {
            Rc::new(Object::Option(None))
        }
    }

    pub fn evaluate_statement(&mut self, statement: &Statement) -> Rc<Object> {
        match statement {
            Statement::LexicalDeclaration(decl) => self.lexical_declaration(decl),
            Statement::FunctionDeclaration(decl) => self.function_declaration(decl),
        }

        Rc::new(Object::Option(None))
    }

    pub fn evaluate_expression(&mut self, expr: &Expression) -> Rc<Object> {
        match expr {
            Expression::String(s) => Rc::new(Object::String(s.clone())),
            Expression::FunctionCall(function_call) => self.function_call(function_call),
            Expression::StatementBlock(block) => self.evaluate_statement_block(block),
        }
    }

    pub fn lexical_declaration(
        &mut self,
        LexicalDeclaration { identifier, expression }: &LexicalDeclaration,
    ) {
        let object = self.evaluate_expression(expression);
        self.current().declare_object(identifier, object);
    }

    pub fn function_declaration(
        &mut self,
        FunctionDeclaration { 
            identifier, 
            formal_parameters, 
            statement_block 
        }: &FunctionDeclaration,
    ) {
        let function = Function {
            formal_parameters: formal_parameters.to_vec(),
            statements: statement_block.clone()
        };

        self.current().declare_object(identifier, Rc::new(Object::Function(function)));
    }

    pub fn function_call(&mut self, call: &FunctionCall) -> Rc<Object> {
        let arguments = call
            .arguments()
            .iter()
            .map(|arg| self.evaluate_expression(arg))
            .collect::<Vec<_>>();

        self.push();

        let return_value = if let Some(builtin) = Builtin::matches(call.function_name()) {
            builtin.run(arguments)
        } else if let Some(lookup) = self.lookup(call.function_name()) {
            let lookup = Weak::upgrade(&lookup).unwrap();

            match lookup.deref() {
                Object::String(_) => Rc::clone(&lookup),
                Object::Function(function) => {
                    for (identifier, value) in function.formal_parameters.iter().zip(arguments) {
                        self.current().declare_object(identifier, value);
                    }

                    self.evaluate_statement_block(&function.statements)
                }
                Object::Builtin(_) => unreachable!(),
                e => {
                    eprintln!("Tried to call non function object: {e:?}");
                    Rc::new(Object::Option(None))
                }
            }
        } else {
            eprintln!("Function not found: {:?}", call.function_name());
            Rc::new( Object::Option(None) )
        };

        self.pop();

        return_value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_program() {
        let mut program = Interpreter::new(
            r#"
            fn main() {
                print Ciao, come stai?;
            }
            "#
        ).unwrap();

        // let mut program = Interpreter::new(
        //     r#"
        //     pub fn main() {
        //         fn call_ls(path) {
        //             let output = run ls (path);
        //             print Output is (output);
        //             output
        //         }
        //
        //         print Ciao, come stai?;
        //         let repo_dir = run git rev-parse --show-toplevel;
        //         print Current directory is {repo_dir};
        //         let other_output = call_ls {repo_dir};
        //         print Other output is (other_output);
        //     }
        //     "#
        // ).unwrap();

        program.call_function("main");
    }
}
