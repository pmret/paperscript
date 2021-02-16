use std::io::Write;

mod parse;
mod warning;
pub mod api;

pub use warning::Warning;
pub use api::Api;

use std::fmt;
use std::collections::{HashMap, BTreeSet};

use parse::ast::{Stmt, Expr, LoopTimes};
use parse::lex::{Token, TokenKind};
use parse::Parser;

const LW_COUNT: usize = 16;

struct Compiler<'input, 'output, 'api, 'warn, O, F>
where
    O: Write,
    F: FnMut(Warning),
{
    input: &'input str,
    output: &'output mut O,
    api: &'api Api,
    handle_warning: &'warn mut F,
    parser: Parser<'input>,
}

#[derive(Debug, Clone, Default)]
struct Context {
    vars: HashMap<String, Var>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Var {
    LocalWord(u8),
    Extern(String),
    Function(String, api::Function),
}

#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Parse(parse::Error),
    TooManyLocalWords { var_name: String, pos: (usize, usize) },
    UnknownVar { var_name: String, pos: (usize, usize) },
    CallNonFunction { callee: String, pos: (usize, usize) },
    CallOutNumMismatch { num_outs: usize, num_vars: usize, pos: (usize, usize) },
    UnsupportedExpression { pos: (usize, usize) },
}

pub type Result<T> = std::result::Result<T, Error>;

pub fn compile<O, F>(input: &str, output: &mut O, api: &Api, handle_warning: &mut F) -> Result<()>
where
    O: Write,
    F: FnMut(Warning),
{
    let mut compiler = Compiler::new(input, output, api, handle_warning);
    compiler.compile()
}

impl<'input, 'output, 'api, 'warn, O, F> Compiler<'input, 'output, 'api, 'warn, O, F>
where
    O: Write,
    F: FnMut(Warning)
{
    fn new(input: &'input str, output: &'output mut O, api: &'api Api, handle_warning: &'warn mut F) -> Self {
        Self {
            parser: Parser::new(input),
            input,
            output,
            api,
            handle_warning,
        }
    }

    fn lookup_var(&self, ctx: &Context, var_name_token: &Token) -> Result<Var> {
        let var_name = var_name_token.source(self.input);

        if var_name_token.kind == TokenKind::ExternalIdentifier {
            return Ok(Var::Extern(var_name.to_string()))
        }

        if let Some(var) = ctx.vars.get(var_name) {
            return Ok(var.clone());
        }

        if let Some(func) = self.api.functions.get(var_name) {
            return Ok(Var::Function(var_name.to_string(), func.clone()));
        }

        Err(Error::UnknownVar {
            var_name: var_name.to_owned(),
            pos: var_name_token.position(self.input),
        })
    }

    fn lookup_or_declare_lw(&mut self, ctx: &mut Context, var_name_token: &Token) -> Result<Var> {
        match self.lookup_var(ctx, var_name_token) {
            Ok(var) => Ok(var),

            Err(Error::UnknownVar { .. }) => {
                let var_name = var_name_token.source(self.input);

                let mut unused_lws = BTreeSet::new();
                for i in 0..LW_COUNT {
                    unused_lws.insert(i as u8);
                }

                for var in ctx.vars.values() {
                    if let Var::LocalWord(n) = var {
                        unused_lws.remove(n);
                    }
                }

                if let Some(var) = unused_lws.iter().next() {
                    let var = Var::LocalWord(*var);
                    ctx.vars.insert(var_name.to_owned(), var.clone());
                    Ok(var)
                } else {
                    Err(Error::TooManyLocalWords {
                        var_name: var_name.to_owned(),
                        pos: var_name_token.position(self.input),
                    })
                }
            }

            Err(error) => Err(error),
        }
    }

    // TODO: don't fail fast on blocks with errors, use handle_warning or similar
    fn compile(&mut self) -> Result<()> {
        while !self.parser.is_eof() {
            let def = self.parser.parse_def()?;
            let script_name = def.name.source(self.input);
            let mut ctx = Context::default();

            writeln!(self.output, "Bytecode N({})[] = {{", script_name)?;
            self.compile_block(&mut ctx, def.block)?;
            writeln!(self.output, "}};")?;
        }

        Ok(())
    }

    fn compile_block(&mut self, ctx: &mut Context, block: Vec<Stmt>) -> Result<()> {
        for stmt in block {
            match stmt {
                Stmt::Loop { times, block } => {
                    match times {
                        LoopTimes::Num(expr) => {
                            let expr = self.compile_expression(ctx, &expr)?;
                            writeln!(self.output, "SI_CMD(OP_DO, {}),", expr)?;
                        }
                        LoopTimes::Infinite => writeln!(self.output, "SI_CMD(OP_DO, 0),")?,
                    }
                    self.compile_block(ctx, block)?;
                    writeln!(self.output, "SI_CMD(OP_WHILE),")?;
                }

                Stmt::SetVars { vars, value, eq } => {
                    let vars = vars
                        .into_iter()
                        .map(|var| self.lookup_or_declare_lw(ctx, &var))
                        .collect::<Result<Vec<Var>>>()?;

                    if vars.len() == 1 {
                        let value = self.compile_expression(ctx, &value)?;
                        writeln!(self.output, "SI_CMD(OP_SET, {}, {}),", vars[0], value)?;
                    } else if let Expr::Call { callee: callee_token, args } = value {
                        let callee = self.lookup_var(ctx, &callee_token)?;
                        if let Var::Function(_, func_desc) = &callee {
                            let (outs_desc, args_desc): (Vec<api::Arg>, Vec<api::Arg>) = func_desc.args.clone()
                                .into_iter()
                                .partition(|arg| arg.out);
                        
                            if outs_desc.len() != vars.len() {
                                return Err(Error::CallOutNumMismatch {
                                    num_outs: outs_desc.len(),
                                    num_vars: vars.len(),
                                    pos: eq.position(self.input),
                                });
                            }

                            let mut args = self.compile_call_args(ctx, &args, &args_desc)?.into_iter();
                            let mut vars = vars.into_iter();

                            write!(self.output, "SI_CMD(OP_USER_FUNC, {}", callee)?;
                            for arg in &func_desc.args {
                                if arg.out {
                                    write!(self.output, ", {}", vars.next().unwrap())?;
                                } else {
                                    write!(self.output, ", {}", args.next().unwrap())?;
                                }
                            }
                            writeln!(self.output, ");")?;
                        } else {
                            return Err(Error::CallNonFunction {
                                callee: callee_token.source(self.input).to_owned(),
                                pos: callee_token.position(self.input),
                            });
                        }
                    } else {
                        return Err(Error::UnsupportedExpression {
                            pos: eq.position(self.input),
                        });
                    }
                }
                Stmt::AddVar { var, value } => {
                    let var = self.lookup_var(ctx, &var)?;
                    let value = self.compile_expression(ctx, &value)?;
                    writeln!(self.output, "SI_CMD(OP_ADD, {}, {}),", var, value)?;
                }

                Stmt::Call { callee: callee_token, args } => {
                    let callee = self.lookup_var(ctx, &callee_token)?;
                    if let Var::Function(_, func_desc) = &callee {
                        let args = self.compile_call_args(ctx, &args, &func_desc.args)?;

                        write!(self.output, "SI_CMD(OP_USER_FUNC, {}", callee)?;
                        for arg in args {
                            write!(self.output, ", {}", arg)?;
                        }
                        writeln!(self.output, ");")?;
                    } else {
                        return Err(Error::CallNonFunction {
                            callee: callee_token.source(self.input).to_owned(),
                            pos: callee_token.position(self.input),
                        });
                    }
                }
            }
        }
        Ok(())
    }

    fn compile_expression(&mut self, ctx: &Context, expr: &Expr) -> Result<String> {
        match expr {
            Expr::Identifier(var) => Ok(format!("{}", self.lookup_var(ctx, var)?)),
            Expr::Int { value, .. } => Ok(format!("{}", value)),
            Expr::Float { token, .. } => Ok(format!("SI_FIXED({})", token.source(self.input))),
            Expr::Call { callee, .. } => Err(Error::UnsupportedExpression { pos: callee.position(self.input) }),
        }
    }

    fn compile_call_args(&mut self, ctx: &Context, args: &[Expr], desc: &[api::Arg]) -> Result<Vec<String>> {
        let mut arg_list = Vec::with_capacity(args.len());

        // TODO: check args and desc have the same length

        for (_desc, arg) in desc.iter().zip(args) {
            // TODO: typechecking

            let expr = self.compile_expression(ctx, &arg)?;
            arg_list.push(expr);
        }

        Ok(arg_list)
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Var::LocalWord(n) => write!(f, "LW({})", n),
            Var::Extern(ext) => write!(f, "(Bytecode)({})", ext),
            Var::Function(name, _) => write!(f, "(Bytecode)(&{})", name),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(source) => write!(f, "{}", source),
            Error::Io(source) => write!(f, "{}", source),
            Error::TooManyLocalWords { var_name, pos } =>
                write!(f, "No space to allocate variable {:?} on line {} column {} (max is LW({}))", var_name, pos.0, pos.1, LW_COUNT),
            Error::UnknownVar { var_name, pos } =>
                write!(f, "Use of unknown variable {:?} on line {} column {}", var_name, pos.0, pos.1),
            Error::CallNonFunction { callee, pos } =>
                write!(f, "Attempt to call {:?} on line {} column {}, but it is not a function or a script", callee, pos.0, pos.1),
            Error::CallOutNumMismatch { num_outs, num_vars, pos } =>
                write!(f, "Call on line {} sets {} vars, but the callee returns {}", pos.0, num_vars, num_outs),
            Error::UnsupportedExpression { pos } =>
                write!(f, "Complex expression on line {} column {} is not yet supported", pos.0, pos.1),
        }
    }
}

impl From<parse::Error> for Error {
    fn from(source: parse::Error) -> Self {
        Error::Parse(source)
    }
}

impl From<std::io::Error> for Error {
    fn from(source: std::io::Error) -> Self {
        Error::Io(source)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Parse(source) => Some(source),
            Error::Io(source) => Some(source),
            _ => None,
        }
    }
}
