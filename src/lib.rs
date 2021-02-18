use std::io::Write;

mod parse;
mod warning;
pub mod api;

pub use warning::Warning;
pub use api::{Api, Datatype};

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
    Script(String, api::Script),
}

#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Parse(parse::Error),
    TooManyLocalWords { var_name: String, pos: (usize, usize) },
    UnknownVar { var_name: String, pos: (usize, usize) },
    CallNonFunction { callee: String, pos: (usize, usize) },
    ExecNonScript { callee: String, pos: (usize, usize) },
    MissingFunctionSignature { callee: String, pos: (usize, usize) },
    CallOutNumMismatch { num_outs: usize, num_vars: usize, pos: (usize, usize) },
    UnsupportedExpression,
    AssignmentTypeMismatch { pos: (usize, usize) },
}

pub type Result<T> = std::result::Result<T, Error>;

pub fn compile<O, F>(input: &str, output: &mut O, api: &Api, handle_warning: &mut F) -> Result<()>
where
    O: Write,
    F: FnMut(Warning),
{
    writeln!(output, "#include \"script_api.h\"")?;
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
            let name = if func.namespace {
                format!("N({})", var_name)
            } else {
                var_name.to_owned()
            };
            return Ok(Var::Function(name, func.clone()));
        }

        if let Some(script) = self.api.scripts.get(var_name) {
            let name = if script.namespace {
                format!("N({})", var_name)
            } else {
                var_name.to_owned()
            };
            return Ok(Var::Script(name, script.clone()));
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
        let mut global_ctx = Context::default();
        let mut defs = Vec::new();

        while !self.parser.is_eof() {
            let def = self.parser.parse_def()?;
            let script_name = def.name.source(self.input);

            let namespace = if let Some(script) = self.api.scripts.get(script_name) {
                script.namespace
            } else if def.name.kind == TokenKind::ExternalIdentifier {
                false
            } else {
                // Add the script var to context so it can be referenced from now on
                let var = Var::Script(script_name.to_owned(), api::Script { namespace: true });
                global_ctx.vars.insert(script_name.to_owned(), var);

                true
            };

            if namespace {
                writeln!(self.output, "extern Bytecode N({})[];", script_name)?;
            } else {
                writeln!(self.output, "extern Bytecode {}[];", script_name)?;
            }

            defs.push((script_name, def, namespace));
        }

        for (script_name, def, namespace) in defs {
            let mut ctx = global_ctx.clone();

            if namespace {
                writeln!(self.output, "Bytecode N({})[] = {{", script_name)?;
            } else {
                writeln!(self.output, "Bytecode {}[] = {{", script_name)?;
            }

            self.compile_block(&mut ctx, def.block)?;

            writeln!(self.output, "SI_CMD(OP_RETURN),")?;
            writeln!(self.output, "SI_CMD(OP_END),")?;

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
                            let (expr, _) = self.compile_expression(ctx, &expr)?;
                            writeln!(self.output, "SI_CMD(OP_BEGIN_LOOP, {}),", expr)?;
                        }
                        LoopTimes::Infinite => writeln!(self.output, "SI_CMD(OP_BEGIN_LOOP, 0),")?,
                    }
                    self.compile_block(ctx, block)?;
                    writeln!(self.output, "SI_CMD(OP_END_LOOP),")?;
                }

                Stmt::Thread(block) => {
                    writeln!(self.output, "SI_CMD(OP_BEGIN_THREAD),")?;
                    self.compile_block(ctx, block)?;
                    writeln!(self.output, "SI_CMD(OP_END_THREAD),")?;
                }

                Stmt::ChildThread(block) => {
                    writeln!(self.output, "SI_CMD(OP_BEGIN_CHILD_THREAD),")?;
                    self.compile_block(ctx, block)?;
                    writeln!(self.output, "SI_CMD(OP_END_CHILD_THREAD),")?;
                }

                Stmt::If { condition, then_block, else_block, .. } => {
                    // Simple expression (single boolean infix)
                    let done = if let Expr::Infix(lhs, op_token, rhs) = &condition {
                        match op_token.kind {
                            TokenKind::EqEq => {
                                let (lhs, _) = self.compile_expression(ctx, lhs)?;
                                let (rhs, _) = self.compile_expression(ctx, rhs)?;
                                writeln!(self.output, "SI_CMD(OP_IF_EQ, {}, {}),", lhs, rhs)?;
                                true
                            }
                            // TODO more
                            _ => false,
                        }
                    } else {
                        false
                    };

                    // Complex expression (compile expression to temp, then check that)
                    if !done {
                        let (condition, _datatype) = self.compile_expression(ctx, &condition)?;

                        // TODO: warn if datatype is not bool

                        writeln!(self.output, "SI_CMD(OP_IF_EQ, {}, TRUE),", condition)?;
                    }

                    self.compile_block(ctx, then_block)?;

                    if let Some(else_block) = else_block {
                        writeln!(self.output, "SI_CMD(OP_ELSE),")?;
                        self.compile_block(ctx, else_block)?;
                    }

                    writeln!(self.output, "SI_CMD(OP_END_IF),")?;
                }

                Stmt::SetVars { vars, value, eq } => {
                    let vars = vars
                        .into_iter()
                        .map(|var| self.lookup_or_declare_lw(ctx, &var))
                        .collect::<Result<Vec<Var>>>()?;

                    if let Expr::Call { callee: callee_token, args } = value {
                        let callee = self.lookup_var(ctx, &callee_token)?;
                        match &callee {
                            Var::Function(_, func_desc) => {
                                if let Some(func_args) = &func_desc.args {
                                    let (outs_desc, args_desc): (Vec<api::Arg>, Vec<api::Arg>) = func_args.clone()
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
    
                                    write!(self.output, "SI_CMD(OP_CALL_FUNC, {}", callee)?;
                                    for arg in func_args {
                                        if arg.out {
                                            write!(self.output, ", {}", vars.next().unwrap())?;
                                        } else {
                                            write!(self.output, ", {}", args.next().unwrap())?;
                                        }
                                    }
                                    writeln!(self.output, ");")?;
                                } else {
                                    return Err(Error::MissingFunctionSignature {
                                        callee: callee_token.source(self.input).to_owned(),
                                        pos: callee_token.position(self.input),
                                    });
                                }
                            }
                            
                            _ => {
                                return Err(Error::CallNonFunction {
                                    callee: callee_token.source(self.input).to_owned(),
                                    pos: callee_token.position(self.input),
                                });
                            }
                        }
                    } else if vars.len() == 1 {
                        let (value, datatype) = self.compile_expression(ctx, &value)?;
                        match datatype {
                            Datatype::Int | Datatype::Bool => writeln!(self.output, "SI_CMD(OP_SET, {}, {}),", vars[0], value)?,
                            Datatype::Float => writeln!(self.output, "SI_CMD(OP_SET_F, {}, {}),", vars[0], value)?,
                            Datatype::Const => writeln!(self.output, "SI_CMD(OP_SET_CONST, {}, {}),", vars[0], value)?,
                        }
                    } else {
                        return Err(Error::UnsupportedExpression);
                    }
                }
                Stmt::AddVar { var: var_token, value } => {
                    let var = self.lookup_var(ctx, &var_token)?;
                    let (value, datatype) = self.compile_expression(ctx, &value)?;
                    match datatype {
                        Datatype::Int | Datatype::Const => writeln!(self.output, "SI_CMD(OP_ADD, {}, {}),", var, value)?,
                        Datatype::Float => writeln!(self.output, "SI_CMD(OP_ADD_F, {}, {}),", var, value)?,
                        Datatype::Bool => return Err(Error::AssignmentTypeMismatch {
                            pos: var_token.position(self.input),
                        }),
                    }
                }
                Stmt::SubVar { var: var_token, value } => {
                    let var = self.lookup_var(ctx, &var_token)?;
                    let (value, datatype) = self.compile_expression(ctx, &value)?;
                    match datatype {
                        Datatype::Int | Datatype::Const => writeln!(self.output, "SI_CMD(OP_SUB, {}, {}),", var, value)?,
                        Datatype::Float => writeln!(self.output, "SI_CMD(OP_SUB_F, {}, {}),", var, value)?,
                        Datatype::Bool => return Err(Error::AssignmentTypeMismatch {
                            pos: var_token.position(self.input),
                        }),
                    }
                }
                Stmt::MulVar { var: var_token, value } => {
                    let var = self.lookup_var(ctx, &var_token)?;
                    let (value, datatype) = self.compile_expression(ctx, &value)?;
                    match datatype {
                        Datatype::Int | Datatype::Const => writeln!(self.output, "SI_CMD(OP_MUL, {}, {}),", var, value)?,
                        Datatype::Float => writeln!(self.output, "SI_CMD(OP_MUL_F, {}, {}),", var, value)?,
                        Datatype::Bool => return Err(Error::AssignmentTypeMismatch {
                            pos: var_token.position(self.input),
                        }),
                    }
                }
                Stmt::DivVar { var: var_token, value } => {
                    let var = self.lookup_var(ctx, &var_token)?;
                    let (value, datatype) = self.compile_expression(ctx, &value)?;
                    match datatype {
                        Datatype::Int | Datatype::Const => writeln!(self.output, "SI_CMD(OP_DIV, {}, {}),", var, value)?,
                        Datatype::Float => writeln!(self.output, "SI_CMD(OP_DIV_F, {}, {}),", var, value)?,
                        Datatype::Bool => return Err(Error::AssignmentTypeMismatch {
                            pos: var_token.position(self.input),
                        }),
                    }
                }
                Stmt::ModVar { var: var_token, value } => {
                    let var = self.lookup_var(ctx, &var_token)?;
                    let (value, datatype) = self.compile_expression(ctx, &value)?;
                    match datatype {
                        Datatype::Int | Datatype::Const | Datatype::Float => writeln!(self.output, "SI_CMD(OP_MOD, {}, {}),", var, value)?,
                        Datatype::Bool => return Err(Error::AssignmentTypeMismatch {
                            pos: var_token.position(self.input),
                        }),
                    }
                }

                Stmt::Call { callee: callee_token, args } => {
                    if let Ok(callee) = self.lookup_var(ctx, &callee_token) {
                        if let Var::Function(_, func_desc) = &callee {
                            let args = if let Some(func_args) = &func_desc.args {
                                self.compile_call_args(ctx, &args, &func_args)?
                            } else {
                                self.compile_call_args_no_desc(ctx, &args)?
                            };

                            write!(self.output, "SI_CMD(OP_CALL_FUNC, {}", callee)?;
                            for arg in args {
                                write!(self.output, ", {}", arg)?;
                            }
                            writeln!(self.output, "),")?;
                        } else {
                            return Err(Error::CallNonFunction {
                                callee: callee_token.source(self.input).to_owned(),
                                pos: callee_token.position(self.input),
                            });
                        }
                    } else {
                        (self.handle_warning)(Warning::CallUndeclaredFunc(callee_token.source(self.input).to_owned()));

                        let args = self.compile_call_args_no_desc(ctx, &args)?;

                        write!(self.output, "SI_CMD(OP_CALL_FUNC, (Bytecode)(&{})", callee_token.source(self.input))?;
                        for arg in args {
                            write!(self.output, ", {}", arg)?;
                        }
                        writeln!(self.output, "),")?;
                    }
                }

                Stmt::Exec { callee: callee_token } => {
                    if let Ok(callee) = self.lookup_var(ctx, &callee_token) {
                        if let Var::Function(_, _) = &callee {
                            return Err(Error::ExecNonScript {
                                callee: callee_token.source(self.input).to_owned(),
                                pos: callee_token.position(self.input),
                            });
                        } else {
                            writeln!(self.output, "SI_CMD(OP_EXEC, {}),", callee)?;
                        }
                    } else {
                        // Implicit declaration!
                        writeln!(self.output, "SI_CMD(OP_EXEC, (Bytecode)(N({}))),", callee_token.source(self.input))?;
                    }
                }

                Stmt::ExecWait { callee: callee_token } => {
                    if let Ok(callee) = self.lookup_var(ctx, &callee_token) {
                        if let Var::Function(_, _) = &callee {
                            return Err(Error::ExecNonScript {
                                callee: callee_token.source(self.input).to_owned(),
                                pos: callee_token.position(self.input),
                            });
                        } else {
                            writeln!(self.output, "SI_CMD(OP_EXEC_WAIT, {}),", callee)?;
                        }
                    } else {
                        // Implicit declaration!
                        writeln!(self.output, "SI_CMD(OP_EXEC_WAIT, (Bytecode)(N({}))),", callee_token.source(self.input))?;
                    }
                }

                Stmt::Sleep(expr) => {
                    let (expr, _) = self.compile_expression(ctx, &expr)?;
                    writeln!(self.output, "SI_CMD(OP_SLEEP_FRAMES, {}),", expr)?;
                }

                Stmt::SleepSecs(expr) => {
                    let (expr, _) = self.compile_expression(ctx, &expr)?;
                    writeln!(self.output, "SI_CMD(OP_SLEEP_SECS, {}),", expr)?;
                }

                Stmt::Return => {
                    writeln!(self.output, "SI_CMD(OP_RETURN),")?;
                }
            }
        }
        Ok(())
    }

    fn compile_expression(&mut self, ctx: &Context, expr: &Expr) -> Result<(String, Datatype)> {
        match expr {
            Expr::Identifier(var) => Ok((format!("{}", self.lookup_var(ctx, var)?), Datatype::Int)), // TODO: use datatype of var
            Expr::Int { value, .. } => Ok((format!("{}", value), Datatype::Int)),
            Expr::Float { token, .. } => Ok((format!("SI_FIXED({}f)", token.source(self.input)), Datatype::Float)),
            _ => Err(Error::UnsupportedExpression),
        }
    }

    fn compile_call_args(&mut self, ctx: &Context, args: &[Expr], desc: &[api::Arg]) -> Result<Vec<String>> {
        let mut arg_list = Vec::with_capacity(args.len());

        // TODO: check args and desc have the same length

        for (_desc, arg) in desc.iter().zip(args) {
            // TODO: typechecking

            let (expr, _) = self.compile_expression(ctx, &arg)?;
            arg_list.push(expr);
        }

        Ok(arg_list)
    }

    fn compile_call_args_no_desc(&mut self, ctx: &Context, args: &[Expr]) -> Result<Vec<String>> {
        let mut arg_list = Vec::with_capacity(args.len());

        for arg in args {
            let (expr, _) = self.compile_expression(ctx, &arg)?;
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
            Var::Script(name, _) => write!(f, "(Bytecode)({})", name),
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
                write!(f, "Attempt to call {:?} on line {} column {}, but it is not a function (hint: use 'exec' or 'execwait' to run scripts)", callee, pos.0, pos.1),
            Error::ExecNonScript { callee, pos } =>
                write!(f, "Attempt to exec {:?} on line {} column {}, but it is not a script", callee, pos.0, pos.1),
            Error::MissingFunctionSignature { callee, pos } =>
                write!(f, "Attempt to call {:?} on line {} column {}, but it does not have a known signature", callee, pos.0, pos.1),
            Error::CallOutNumMismatch { num_outs, num_vars, pos } =>
                write!(f, "Call on line {} sets {} vars, but the callee returns {}", pos.0, num_vars, num_outs),
            Error::UnsupportedExpression =>
                write!(f, "Complex expressions are not supported"),
            Error::AssignmentTypeMismatch { pos } =>
                write!(f, "Assignment on line {} illegally mixes types", pos.0),
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
