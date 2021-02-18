use std::collections::HashMap;

use lazy_static::lazy_static;

use super::lex::{Token, TokenKind};

lazy_static! {
    pub static ref INFIX: HashMap<TokenKind, u8> = {
        let mut ops = HashMap::new();
        ops.insert(TokenKind::EqEq, 1);
        ops.insert(TokenKind::NotEq, 1);
        ops
    };
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Def {
    pub name: Token,
    pub block: Vec<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Stmt {
    Loop { times: LoopTimes, block: Vec<Stmt> },
    Thread(Vec<Stmt>),
    ChildThread(Vec<Stmt>),
    If { condition: Expr, then_block: Vec<Stmt>, else_block: Option<Vec<Stmt>> },
    SetVars { vars: Vec<Token>, value: Expr, eq: Token },
    AddVar { var: Token, value: Expr },
    SubVar { var: Token, value: Expr },
    MulVar { var: Token, value: Expr },
    DivVar { var: Token, value: Expr },
    ModVar { var: Token, value: Expr },
    Call { callee: Token, args: Vec<Expr> },
    Exec { callee: Token },
    ExecWait { callee: Token },
    Return,
    Sleep(Expr),
    SleepSecs(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Identifier(Token),
    Int { value: i32, token: Token },
    Float { token: Token },
    Call { callee: Token, args: Vec<Expr> },
    Infix(Box<Expr>, Token, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LoopTimes {
    Infinite,
    Num(Expr),
}
