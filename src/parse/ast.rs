use super::lex::Token;

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
    SetVars { vars: Vec<Token>, value: Expr, eq: Token },
    AddVar { var: Token, value: Expr },
    Call { callee: Token, args: Vec<Expr> },
    Exec { callee: Token },
    ExecWait { callee: Token },
    Sleep(Expr),
    SleepSecs(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Identifier(Token),
    Int { value: i32, token: Token },
    Float { token: Token },
    Call { callee: Token, args: Vec<Expr> },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LoopTimes {
    Infinite,
    Num(Expr),
}
