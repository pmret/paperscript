use std::iter::Peekable;

use logos::{Logos, Span};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Logos, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    #[token("def")]
    Def,

    #[token("loop")]
    Loop,

    #[token("for")]
    For,

    #[token("while")]
    While,

    #[token("if")]
    If,

    #[token("else")]
    Else,

    #[token("elif")]
    Elif,

    #[token("and")]
    And,

    #[token("or")]
    Or,

    #[token("not")]
    Not,

    #[token("switch")]
    Switch,

    #[token("case")]
    Case,

    #[token("range")]
    Range,

    #[token("default")]
    Default,

    #[token("var")]
    Var,

    #[token("bool")]
    Bool,

    #[token("int")]
    KwInt,

    #[token("float")]
    KwFloat,

    #[token("const")]
    Const,

    #[token("global")]
    Global,

    #[token("local")]
    Local,

    #[token("pass")]
    Pass,

    #[token(":")]
    Colon,

    #[token(",")]
    Comma,

    #[token("=")]
    Equals,

    #[token("+=")]
    PlusEquals,

    #[token("(")]
    OpenParen,

    #[token(")")]
    CloseParen,

    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
    Identifier,

    /// External identifiers include basic C macro invocations like "LW(0)" or "STORY_PROGRESS".
    /// These are treated as black boxes (single tokens) and can typically be used in place of variables.
    #[regex(r"[A-Z][A-Z0-9]+(_[a-zA-Z0-9_]+)?(\([^)]+\))?")]
    ExternalIdentifier,

    #[token("true")]
    True,

    #[token("false")]
    False,

    #[regex(r"[+-]?[0-9]+")]
    Int,

    #[regex(r"[+-]?0x[0-9a-fA-F]+")]
    HexInt,

    #[regex(r"[+-]?[0-9]+\.[0-9]+")]
    Float,

    #[regex(r"//[^\r\n]+")]
    LineComment,

    /// Horizontal whitespace
    #[regex(r"[ \t\f]+")]
    Whitespace,

    /// Vertical whitespace (at least one newline)
    #[regex(r"(\r?\n)+")]
    Newline,

    Indent,
    Dedent,

    #[error]
    IllegalCharError,

    BadIndentError,
}

pub struct Lexer<'input> {
    input: &'input str,
    logos: Peekable<logos::SpannedIter<'input, TokenKind>>,
    indent_level: isize,
    paren_depth: isize,
    queue: Vec<Token>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Self {
            input,
            logos: TokenKind::lexer(input).spanned().peekable(),
            indent_level: 0,
            paren_depth: 0,
            queue: Vec::with_capacity(4),
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.queue.pop() {
            return Some(token);
        }

        let next = self.logos.next();

        // Like Python, indentation is ignored within parentheses
        if self.paren_depth == 0 {
            // Handle indentation (Newline followed by Whitespace)
            if let Some((TokenKind::Newline, span)) = &next {
                match self.logos.peek() {
                    // Indentation is changing
                    Some((TokenKind::Whitespace, span)) => {
                        // Complain if the whitespace is not purely spaces
                        for ch in self.input[span.clone()].chars() {
                            if ch != ' ' {
                                self.queue.push(Token {
                                    kind: TokenKind::BadIndentError,
                                    span: span.clone(),
                                });
                                return next.map(|(kind, span)| Token {
                                    kind,
                                    span,
                                });
                            }
                        }

                        let num_spaces = (span.end - span.start) as isize;

                        // Complain if the number of spaces is not a multiple of 4 (4 spaces = 1 indent/dedent)
                        if num_spaces % 4 != 0 {
                            self.queue.push(Token {
                                kind: TokenKind::BadIndentError,
                                span: span.clone(),
                            });
                            return next.map(|(kind, span)| Token {
                                kind,
                                span,
                            });
                        }

                        let delta = (num_spaces / 4) - self.indent_level;

                        for _ in 0..delta {
                            self.queue.push(Token {
                                kind: TokenKind::Indent,
                                span: span.clone(),
                            });
                        }

                        for _ in delta..0 {
                            self.queue.push(Token {
                                kind: TokenKind::Dedent,
                                span: span.clone(),
                            });
                        }

                        self.indent_level += delta;
                    }

                    // Output Dedent until indent_level is zero
                    Some(_) | None => {
                        for _ in 0..self.indent_level {
                            self.queue.push(Token {
                                kind: TokenKind::Dedent,
                                span: span.end..span.end,
                            });
                        }

                        self.indent_level = 0;
                    }
                }
            }
        }

        if let Some((kind, span)) = next {
            match kind {
                // Discard
                TokenKind::Whitespace | TokenKind::LineComment => self.next(),

                // Discard newlines if inside parens
                TokenKind::Newline if self.paren_depth != 0 => self.next(),

                // Track parenthesis depth
                TokenKind::OpenParen => {
                    self.paren_depth += 1;
                    Some(Token {
                        kind,
                        span,
                    })
                }
                TokenKind::CloseParen => {
                    self.paren_depth -= 1;
                    Some(Token {
                        kind,
                        span,
                    })
                }

                kind => Some(Token {
                    kind,
                    span,
                })
            }
        } else {
            None
        }
    }
}

impl Token {
    pub fn position(&self, input: &str) -> (usize, usize) {
        let mut line = 1;
        let mut col = 1;

        for ch in input[..self.span.start].chars() {
            match ch {
                '\n' => {
                    line += 1;
                    col = 1;
                }

                _ => {
                    col += 1;
                }
            }
        }

        (line, col)
    }

    pub fn source<'a>(&self, input: &'a str) -> &'a str {
        &input[self.span.clone()]
    }
}

#[cfg(test)]
mod test {
    use indoc::indoc;
    use pretty_assertions::assert_eq;

    use super::*;
    use TokenKind::*;

    #[test]
    fn indent_dedent() {
        let toks: Vec<Token> = Lexer::new(indoc! {r#"
            def foo:
                pass
            pass
        "#}).collect();
        assert_eq!(toks, vec![
            Token { kind: Def, span: 0..3 },
            Token { kind: Identifier, span: 4..7 },
            Token { kind: Colon, span: 7..8 },
            Token { kind: Newline, span: 8..9 },
            Token { kind: Indent, span: 9..13 },
            Token { kind: Pass, span: 13..17 },
            Token { kind: Newline, span: 17..18 },
            Token { kind: Dedent, span: 18..18 },
            Token { kind: Pass, span: 18..22 },
            Token { kind: Newline, span: 22..23 },
        ]);
    }

    #[test]
    fn dedent_at_eof() {
        let toks: Vec<Token> = Lexer::new(indoc! {r#"
            def foo:
                pass
        "#}).collect();
        assert_eq!(toks, vec![
            Token { kind: Def, span: 0..3 },
            Token { kind: Identifier, span: 4..7 },
            Token { kind: Colon, span: 7..8 },
            Token { kind: Newline, span: 8..9 },
            Token { kind: Indent, span: 9..13 },
            Token { kind: Pass, span: 13..17 },
            Token { kind: Newline, span: 17..18 },
            Token { kind: Dedent, span: 18..18 },
        ]);
    }

    #[test]
    fn tabs_error() {
        let toks: Vec<Token> = Lexer::new(indoc! {"
            def foo:
            \tpass
        "}).collect();
        assert_eq!(toks, vec![
            Token { kind: Def, span: 0..3 },
            Token { kind: Identifier, span: 4..7 },
            Token { kind: Colon, span: 7..8 },
            Token { kind: Newline, span: 8..9 },
            Token { kind: BadIndentError, span: 9..10 },
            Token { kind: Pass, span: 10..14 },
            Token { kind: Newline, span: 14..15 },
        ]);
    }

    #[test]
    fn non_4spaces_error() {
        let toks: Vec<Token> = Lexer::new(indoc! {"
            def foo:
               pass
        "}).collect();
        assert_eq!(toks, vec![
            Token { kind: Def, span: 0..3 },
            Token { kind: Identifier, span: 4..7 },
            Token { kind: Colon, span: 7..8 },
            Token { kind: Newline, span: 8..9 },
            Token { kind: BadIndentError, span: 9..12 },
            Token { kind: Pass, span: 12..16 },
            Token { kind: Newline, span: 16..17 },
        ]);
    }

    #[test]
    fn no_indent_newline_in_parens() {
        let toks: Vec<Token> = Lexer::new(indoc! {"
            def foo:(
                )pass
        "}).collect();
        assert_eq!(toks, vec![
            Token { kind: Def, span: 0..3 },
            Token { kind: Identifier, span: 4..7 },
            Token { kind: Colon, span: 7..8 },
            Token { kind: OpenParen, span: 8..9 },
            Token { kind: CloseParen, span: 14..15 },
            Token { kind: Pass, span: 15..19 },
            Token { kind: Newline, span: 19..20 },
        ]);
    }

    #[test]
    fn others_in_parens() {
        let toks: Vec<Token> = Lexer::new(indoc! {"
            (a(b))
        "}).collect();
        assert_eq!(toks, vec![
            Token { kind: OpenParen, span: 0..1 },
            Token { kind: Identifier, span: 1..2 },
            Token { kind: OpenParen, span: 2..3 },
            Token { kind: Identifier, span: 3..4 },
            Token { kind: CloseParen, span: 4..5 },
            Token { kind: CloseParen, span: 5..6 },
            Token { kind: Newline, span: 6..7 },
        ]);
    }

    #[test]
    fn double_dedent() {
        let toks: Vec<Token> = Lexer::new(indoc! {r#"
            pass
                pass
                    pass
        "#}).collect();
        assert_eq!(toks, vec![
            Token { kind: Pass, span: 0..4 },
            Token { kind: Newline, span: 4..5 },
            Token { kind: Indent, span: 5..9 }, // 1
            Token { kind: Pass, span: 9..13 },
            Token { kind: Newline, span: 13..14 },
            Token { kind: Indent, span: 14..22 }, // 2
            Token { kind: Pass, span: 22..26 },
            Token { kind: Newline, span: 26..27 },
            Token { kind: Dedent, span: 27..27 }, // 2
            Token { kind: Dedent, span: 27..27 }, // 1
        ]);
    }

    #[test]
    fn identifier() {
        let toks: Vec<Token> = Lexer::new("a").collect();
        assert_eq!(toks, vec![
            Token { kind: Identifier, span: 0..1 },
        ]);
    }

    #[test]
    fn extern_identifier() {
        let toks: Vec<Token> = Lexer::new("AA").collect();
        assert_eq!(toks, vec![
            Token { kind: ExternalIdentifier, span: 0..2 },
        ]);
    }

    #[test]
    fn extern_identifier_func_macro() {
        let toks: Vec<Token> = Lexer::new("LW(0)").collect();
        assert_eq!(toks, vec![
            Token { kind: ExternalIdentifier, span: 0..5 },
        ]);
    }

    #[test]
    fn identifier_not_func_macro() {
        let toks: Vec<Token> = Lexer::new("Aa()").collect();
        assert_eq!(toks, vec![
            Token { kind: Identifier, span: 0..2 },
            Token { kind: OpenParen, span: 2..3 },
            Token { kind: CloseParen, span: 3..4 },
        ]);
    }
}
