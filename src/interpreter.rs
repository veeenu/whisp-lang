use std::fmt::Display;
use std::ops::Deref;
use std::process::Command;
use std::rc::{Rc, Weak};

use ahash::AHashMap as HashMap;
use thiserror::Error;

use crate::ast::{
    BreakStmt, ElseIfCond, Error as ParseError, Expression, FunctionCall, FunctionDeclaration,
    Identifier, IfExpr, LexicalDeclaration, LoopExpr, Number, Program, Statement, StatementBlock,
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
    Bool(bool),
    String(WhispString),
    Int(i64),
    Float(f64),
    List(Vec<Object>),
    Dict(HashMap<String, Object>),
    Option(Option<Box<Object>>),
    Function(Function),
    Builtin(Builtin),
    Ref(Rc<Object>),
    Null,
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::String(s) => write!(f, "{}", s.deref()),
            Object::Ref(obj) => obj.fmt(f),
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
    Check,
}

impl Builtin {
    pub fn matches(name: &Identifier) -> Option<Builtin> {
        match name.deref() {
            "run" => Some(Builtin::Run),
            "spawn" => Some(Builtin::Spawn),
            "print" => Some(Builtin::Print),
            "check" => Some(Builtin::Check),
            _ => None,
        }
    }

    pub fn run(&self, arguments: Vec<Object>) -> Object {
        match self {
            Builtin::Run => self.call_run(arguments),
            Builtin::Spawn => self.call_print(arguments),
            Builtin::Print => self.call_print(arguments),
            Builtin::Check => self.call_check(arguments),
        }
    }

    fn call_run(&self, arguments: Vec<Object>) -> Object {
        let mut arguments = arguments.into_iter().map(|arg| arg.to_string());

        let Some(program) = arguments.next() else {
            panic!("`run` called with no arguments");
        };

        let mut handle = match Command::new(program).args(arguments).spawn() {
            Ok(handle) => handle,
            Err(e) => panic!("running command failed: {e}"),
        };

        if let Err(e) = handle.wait() {
            panic!("command failed: {e}");
        }

        Object::Null
    }

    fn call_print(&self, arguments: Vec<Object>) -> Object {
        let mut arguments = arguments.into_iter();

        if let Some(arg) = arguments.next() {
            print!("{arg}");
        }

        for arg in arguments {
            print!(" {arg}");
        }

        println!();

        Object::Null
    }

    fn call_check(&self, _arguments: Vec<Object>) -> Object {
        Object::Bool(true)
    }
}

#[derive(Debug, Clone)]
pub enum StatementValue {
    BreakWith(Object),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub enum StatementBlockValue {
    BreakWith(Object),
    Break,
    Value(Object),
    None,
}

impl From<StatementBlockValue> for Object {
    fn from(value: StatementBlockValue) -> Self {
        match value {
            StatementBlockValue::BreakWith(v) => v,
            StatementBlockValue::Break | StatementBlockValue::None => Object::Null,
            StatementBlockValue::Value(v) => v,
        }
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

    pub fn call_function(&mut self, name: &str) -> Object {
        self.stack.function_call(&FunctionCall::new(name, Vec::new()))
    }

    pub fn pub_functions(&self) -> impl Iterator<Item = (&str, Rc<Object>)> {
        self.stack.current().iter()
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
        if let Object::Ref(object) = object {
            self.names.insert(identifier.to_string(), Rc::clone(&object));
        } else {
            self.names.insert(identifier.to_string(), Rc::new(object));
        }

        self.lookup(identifier).unwrap()
    }

    pub fn lookup(&self, identifier: &Identifier) -> Option<Weak<Object>> {
        self.names.get(identifier.deref()).map(Rc::downgrade)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, Rc<Object>)> {
        self.names.iter().map(|(name, obj)| (name.as_str(), Rc::clone(obj)))
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
        self.current_mut()
    }

    pub fn pop(&mut self) {
        if self.0.len() > 1 {
            self.0.pop();
        }
    }

    pub fn current(&self) -> &Scope {
        self.0.last().unwrap()
    }

    pub fn current_mut(&mut self) -> &mut Scope {
        self.0.last_mut().unwrap()
    }

    pub fn lookup(&mut self, identifier: &Identifier) -> Option<Weak<Object>> {
        self.0.iter_mut().rev().find_map(|scope| scope.lookup(identifier))
    }

    pub fn evaluate_statement_block(&mut self, block: &StatementBlock) -> StatementBlockValue {
        for block_item in block {
            match block_item {
                StatementBlockItem::Statement(statement) => {
                    match self.evaluate_statement(statement) {
                        StatementValue::BreakWith(value) => {
                            return StatementBlockValue::BreakWith(value)
                        },
                        StatementValue::Break => return StatementBlockValue::Break,
                        StatementValue::Continue => {},
                    }
                },
                StatementBlockItem::Expression(expression) => {
                    self.evaluate_expression(expression);
                },
            };
        }

        block
            .tail_expr()
            .map(|tail_expr| StatementBlockValue::Value(self.evaluate_expression(tail_expr)))
            .unwrap_or(StatementBlockValue::None)
    }

    pub fn evaluate_statement(&mut self, statement: &Statement) -> StatementValue {
        match statement {
            Statement::LexicalDeclaration(decl) => {
                self.lexical_declaration(decl);
                StatementValue::Continue
            },
            Statement::FunctionDeclaration(decl) => {
                self.function_declaration(decl);
                StatementValue::Continue
            },
            Statement::Break(BreakStmt(None)) => StatementValue::Break,
            Statement::Break(BreakStmt(Some(expr))) => {
                StatementValue::BreakWith(self.evaluate_expression(expr))
            },
        }
    }

    pub fn evaluate_if_expr(&mut self, expr: &IfExpr) -> Object {
        if let Object::Bool(true) = self.evaluate_expression(&expr.if_cond.0 .0) {
            return self.evaluate_statement_block(&expr.if_cond.1).into();
        }
        for ElseIfCond(expr, statement_block) in &expr.else_if_conds {
            if let Object::Bool(true) = self.evaluate_expression(&expr.0) {
                return self.evaluate_statement_block(statement_block).into();
            }
        }
        if let Some(else_cond) = &expr.else_cond {
            return self.evaluate_statement_block(&else_cond.0).into();
        }

        Object::Null
    }

    pub fn evaluate_loop_expr(&mut self, LoopExpr(block): &LoopExpr) -> Object {
        loop {
            match self.evaluate_statement_block(block) {
                StatementBlockValue::BreakWith(v) => return v,
                StatementBlockValue::Break => return Object::Null,
                StatementBlockValue::Value(_) | StatementBlockValue::None => continue,
            }
        }
    }

    pub fn evaluate_expression(&mut self, expr: &Expression) -> Object {
        match expr {
            Expression::ParenthesisExpression(expr) => self.evaluate_expression(&expr.0),
            Expression::String(s) => Object::String(s.clone()),
            Expression::FunctionCall(function_call) => self.function_call(function_call),
            Expression::StatementBlock(block) => self.evaluate_statement_block(block).into(),
            Expression::IfExpr(if_expr) => self.evaluate_if_expr(if_expr),
            Expression::Loop(loop_expr) => self.evaluate_loop_expr(loop_expr),
            Expression::Number(num) => match num {
                Number::Int(i) => Object::Int(i.0),
                Number::Float(f) => Object::Float(f.0),
            },
        }
    }

    pub fn lexical_declaration(
        &mut self,
        LexicalDeclaration { identifier, expression }: &LexicalDeclaration,
    ) {
        let object = self.evaluate_expression(expression);
        self.current_mut().declare_object(identifier, object);
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
            formal_parameters: formal_parameters.0.to_vec(),
            statements: statement_block.clone(),
        };

        self.current_mut().declare_object(identifier, Object::Function(function));
    }

    pub fn function_call(&mut self, call: &FunctionCall) -> Object {
        let arguments = call
            .arguments()
            .iter()
            .map(|arg| self.evaluate_expression(arg.into()))
            .collect::<Vec<_>>();

        self.push();

        let return_value: Object = if let Some(builtin) = Builtin::matches(call.function_name()) {
            builtin.run(arguments)
        } else if let Some(lookup) = self.lookup(call.function_name()) {
            let lookup = Weak::upgrade(&lookup).unwrap();

            match lookup.deref() {
                Object::String(_) => Object::Ref(Rc::clone(&lookup)),
                Object::Function(function) => {
                    for (identifier, value) in function.formal_parameters.iter().zip(arguments) {
                        self.current_mut().declare_object(identifier, value);
                    }

                    self.evaluate_statement_block(&function.statements).into()
                },
                Object::Builtin(_) => unreachable!(),
                e => {
                    panic!("Tried to call non function object: {e:?}");
                },
            }
        } else {
            panic!("Function not found: {:?}", call.function_name());
        };

        self.pop();

        return_value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::*;

    #[test]
    fn test_run_hello_world() {
        init_test_log();

        let mut program = Interpreter::new(
            r#"
            fn main() {
                print Ciao, come stai?;
            }
            "#,
        )
        .unwrap();

        program.call_function("main");
    }

    #[test]
    fn test_run_program_with_ifs_and_loop() {
        init_test_log();

        // This print is interpreted incorrectly: the first (foo) is evaluated but the
        // one in the statement block {foo} is not.
        let mut program = Interpreter::new(
            r#"
            fn main() {
                let foo = (loop {
                    print Ciao, come stai?;
                    break "ciao ciao";
                });

                if (check foo) {
                    print "I should be printed";
                } else {
                    print "I shouldn't be printed";
                };

                if (foo) {
                    print "I shouldn't be printed";
                } else {
                    print "I should be printed";
                };

                print (foo) {foo}
            }
            "#,
        )
        .unwrap();
        program.call_function("main");
    }
}
