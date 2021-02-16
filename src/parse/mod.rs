pub mod ast;
pub mod lex;

use std::fmt;
use std::iter::Peekable;

use ast::*;
use lex::{Lexer, Token, TokenKind};

pub struct Parser<'input> {
    pub input: &'input str,
    lex: Peekable<Lexer<'input>>, // LL(1)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Error {
    UnexpectedToken {
        token: Token,
        pos: (usize, usize),
        expected: &'static str,
    },
    ParseInt {
        token: Token,
        pos: (usize, usize),
    },
    UnexpectedEof,
}

pub type Result<T> = std::result::Result<T, Error>;

impl<'input> Parser<'input> {
    pub fn new(input: &'input str) -> Self {
        Self {
            lex: Lexer::new(input).peekable(),
            input,
        }
    }

    fn next(&mut self) -> Result<Token> {
        if let Some(token) = self.lex.next() {
            Ok(token)
        } else {
            Err(Error::UnexpectedEof)
        }
    }

    fn peek(&mut self) -> Result<&Token> {
        if let Some(token) = self.lex.peek() {
            Ok(token)
        } else {
            Err(Error::UnexpectedEof)
        }
    }

    fn expect(&mut self, token_kind: TokenKind) -> Result<Token> {
        let token = self.next()?;
        if token.kind == token_kind {
            Ok(token)
        } else {
            Err(self.unexpected_token(token, "other token")) // XXX
        }
    }

    fn accept(&mut self, token_kind: TokenKind) -> Result<Option<Token>> {
        if self.peek()?.kind == token_kind {
            Ok(Some(self.next()?))
        } else {
            Ok(None)
        }
    }

    pub fn is_eof(&mut self) -> bool {
        self.lex.peek().is_none()
    }

    fn unexpected_token(&self, token: Token, expected: &'static str) -> Error {
        Error::UnexpectedToken {
            pos: token.position(self.input),
            token,
            expected,
        }
    }

    pub fn parse_def(&mut self) -> Result<Def> {
        self.expect(TokenKind::Def)?;
        let name = self.expect(TokenKind::Identifier)?;
        //self.expect(TokenKind::OpenParen)?;
        //self.expect(TokenKind::CloseParen)?;
        self.expect(TokenKind::Colon)?;
        self.expect(TokenKind::Newline)?;
        let block = self.parse_indented_block()?;

        Ok(Def {
            name,
            block,
        })
    }

    pub fn parse_indented_block(&mut self) -> Result<Vec<Stmt>> {
        self.expect(TokenKind::Indent)?;

        let mut block = Vec::with_capacity(1);

        loop {
            let token = self.next()?;
            match token.kind {
                // pass
                TokenKind::Pass => {
                    // Does nothing
                    self.expect(TokenKind::Newline)?;
                }

                // loop:
                // loop n:
                TokenKind::Loop => {
                    block.push(Stmt::Loop {
                        times: if self.accept(TokenKind::Colon)?.is_some() {
                            self.expect(TokenKind::Newline)?;
                            LoopTimes::Infinite
                        } else {
                            let expr = self.parse_expression()?;
                            self.expect(TokenKind::Colon)?;
                            self.expect(TokenKind::Newline)?;
                            LoopTimes::Num(expr)
                        },
                        block: self.parse_indented_block()?,
                    });
                    self.accept(TokenKind::Newline)?;
                }

                // thread:
                TokenKind::Thread => {
                    self.expect(TokenKind::Colon)?;
                    self.expect(TokenKind::Newline)?;
                    block.push(Stmt::Thread(self.parse_indented_block()?));
                    self.accept(TokenKind::Newline)?;
                }

                // childthread:
                TokenKind::ChildThread => {
                    self.expect(TokenKind::Colon)?;
                    self.expect(TokenKind::Newline)?;
                    block.push(Stmt::ChildThread(self.parse_indented_block()?));
                    self.accept(TokenKind::Newline)?;
                }

                // exec identifier
                TokenKind::Exec => {
                    block.push(Stmt::Exec {
                        callee: self.expect(TokenKind::Identifier)?,
                    });
                    self.accept(TokenKind::Newline)?;
                }

                // execwait identifier
                TokenKind::ExecWait => {
                    block.push(Stmt::ExecWait {
                        callee: self.expect(TokenKind::Identifier)?,
                    });
                    self.accept(TokenKind::Newline)?;
                }

                TokenKind::Identifier | TokenKind::ExternalIdentifier => {
                    let operator = self.next()?;
                    match operator.kind {
                        // foo = expr
                        TokenKind::Equals => {
                            block.push(Stmt::SetVars {
                                vars: vec![token],
                                value: self.parse_expression()?,
                                eq: operator,
                            });
                            self.expect(TokenKind::Newline)?;
                        }

                        // foo, bar = expr
                        TokenKind::Comma  => {
                            let mut vars = vec![token];
                            let eq = loop {
                                vars.push(self.expect(TokenKind::Identifier)?);

                                let token = self.next()?;
                                match token {
                                    Token { kind: TokenKind::Comma, .. } => continue,
                                    Token { kind: TokenKind::Equals, .. } => break token,
                                    token => return Err(self.unexpected_token(token, "comma (followed by another var), or equals (followed by expression)")),
                                }
                            };

                            block.push(Stmt::SetVars {
                                vars,
                                value: self.parse_expression()?,
                                eq,
                            });
                            self.expect(TokenKind::Newline)?;
                        }

                        // foo += expr
                        TokenKind::PlusEquals => {
                            block.push(Stmt::AddVar {
                                var: token,
                                value: self.parse_expression()?,
                            });
                            self.expect(TokenKind::Newline)?;
                        }

                        // foo(...)
                        TokenKind::OpenParen => {
                            block.push(Stmt::Call {
                                callee: token,
                                args: self.parse_comma_separated_expressions_until(TokenKind::CloseParen)?,
                            });
                            self.expect(TokenKind::Newline)?;
                        }

                        _ => return Err(self.unexpected_token(operator, "assignment or function call")),
                    }
                }

                TokenKind::Newline => {}, // Empty line 

                TokenKind::Dedent => break,
                _ => return Err(self.unexpected_token(token, "statement")),
            }
        }

        Ok(block)
    }

    pub fn parse_expression(&mut self) -> Result<Expr> {
        let token = self.next()?;
        match token.kind {
            TokenKind::Identifier | TokenKind::ExternalIdentifier => {
                if self.accept(TokenKind::OpenParen)?.is_some() {
                    Ok(Expr::Call {
                        callee: token,
                        args: self.parse_comma_separated_expressions_until(TokenKind::CloseParen)?,
                    })
                } else {
                    Ok(Expr::Identifier(token))
                }
            },

            TokenKind::Int => {
                Ok(Expr::Int {
                    value: match i32::from_str_radix(&self.input[token.span.clone()], 10) {
                        Ok(i) => i,
                        Err(_) => return Err(Error::ParseInt {
                            pos: token.position(self.input),
                            token,
                        }),
                    },
                    token,
                })
            }

            TokenKind::HexInt => {
                Ok(Expr::Int {
                    value: match i32::from_str_radix(&self.input[token.span.clone()].replace("0x", ""), 16) {
                        Ok(i) => i,
                        Err(_) => return Err(Error::ParseInt {
                            pos: token.position(self.input),
                            token,
                        }),
                    },
                    token,
                })
            }

            TokenKind::Float => {
                Ok(Expr::Float {
                    token,
                })
            }

            _ => Err(self.unexpected_token(token, "expression")),
        }
    }

    pub fn parse_comma_separated_expressions_until(&mut self, ending: TokenKind) -> Result<Vec<Expr>> {
        let mut list = Vec::new();

        if self.accept(ending)?.is_some() {
            return Ok(list);
        }

        list.push(self.parse_expression()?);

        loop {
            let token = self.next()?;
            match token.kind {
                TokenKind::Comma => {
                    if self.accept(ending)?.is_some() {
                        break;
                    }

                    list.push(self.parse_expression()?);
                },
                kind if kind == ending => break,
                _ => return Err(self.unexpected_token(token, "comma or end of comma-separated list")),
            }
        }

        Ok(list)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::UnexpectedEof => write!(f, "Unexpected end-of-file"),
            Error::UnexpectedToken { pos, token, expected } => {
                write!(f, "Invalid syntax on line {} column {} (found {:?}, expected {})", pos.0, pos.1, token.kind, expected)
            },
            Error::ParseInt { pos, .. } => {
                write!(f, "Overflowing int literal on line {} column {}", pos.0, pos.1)
            },
        }
    }
}

impl std::error::Error for Error {}

#[cfg(test)]
mod test {
    use indoc::indoc;
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn def_pass() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                pass
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn expr_int() {
        let mut p = Parser::new("100");

        assert_eq!(p.parse_expression(), Ok(Expr::Int {
            token: Token { kind: TokenKind::Int, span: 0..3 },
            value: 100,
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn expr_int_negative() {
        let mut p = Parser::new("-100");

        assert_eq!(p.parse_expression(), Ok(Expr::Int {
            token: Token { kind: TokenKind::Int, span: 0..4 },
            value: -100,
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn expr_int_hex() {
        let mut p = Parser::new("0xDEAD");

        assert_eq!(p.parse_expression(), Ok(Expr::Int {
            token: Token { kind: TokenKind::HexInt, span: 0..6 },
            value: 0xDEAD,
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn expr_int_hex_negative() {
        let mut p = Parser::new("-0xBEEF");

        assert_eq!(p.parse_expression(), Ok(Expr::Int {
            token: Token { kind: TokenKind::HexInt, span: 0..7 },
            value: -0xBEEF,
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn loop_infinite() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                loop:
                    pass
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::Loop {
                    times: LoopTimes::Infinite,
                    block: vec![],
                }
            ],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn loop_finite() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                loop 20:
                    pass
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::Loop {
                    times: LoopTimes::Num(Expr::Int {
                        token: Token { kind: TokenKind::Int, span: 20..22 },
                        value: 20,
                    }),
                    block: vec![],
                }
            ],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn call_no_args() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                bar()
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::Call {
                    callee: Token { kind: TokenKind::Identifier, span: 15..18 },
                    args: vec![],
                }
            ],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn call_with_args() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                bar(1, 2)
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::Call {
                    callee: Token { kind: TokenKind::Identifier, span: 15..18 },
                    args: vec![
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 19..20 },
                            value: 1,
                        },
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 22..23 },
                            value: 2,
                        },
                    ],
                }
            ],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn call_with_many_args() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                Bar(1, 2, 3)
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::Call {
                    callee: Token { kind: TokenKind::Identifier, span: 15..18 },
                    args: vec![
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 19..20 },
                            value: 1,
                        },
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 22..23 },
                            value: 2,
                        },
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 25..26 },
                            value: 3,
                        },
                    ],
                }
            ],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn call_with_args_multiline_trailing_comma() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                bar(
                    1,
                    2,
                )
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::Call {
                    callee: Token { kind: TokenKind::Identifier, span: 15..18 },
                    args: vec![
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 28..29 },
                            value: 1,
                        },
                        Expr::Int {
                            token: Token { kind: TokenKind::Int, span: 39..40 },
                            value: 2,
                        },
                    ],
                }
            ],
        }));
        assert!(p.is_eof());
    }

    #[test]
    fn set_call() {
        let mut p = Parser::new(indoc! {r#"
            def foo():
                a, b = bar(x, y)
        "#});

        assert_eq!(p.parse_def(), Ok(Def {
            name: Token { kind: TokenKind::Identifier, span: 4..7 },
            block: vec![
                Stmt::SetVars {
                    vars: vec![
                        Token { kind: TokenKind::Identifier, span: 15..16 }, // a
                        Token { kind: TokenKind::Identifier, span: 18..19 }, // b
                    ],
                    eq: Token { kind: TokenKind::Equals, span: 20..21 },
                    value: Expr::Call {
                        callee: Token { kind: TokenKind::Identifier, span: 22..25 },
                        args: vec![
                            Expr::Identifier(Token { kind: TokenKind::Identifier, span: 26..27 }), // x
                            Expr::Identifier(Token { kind: TokenKind::Identifier, span: 29..30 }), // y
                        ],
                    }
                }
            ],
        }));
        assert!(p.is_eof());
    }
}
