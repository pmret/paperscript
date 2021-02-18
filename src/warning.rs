use std::fmt;

#[derive(Debug, Clone)]
pub enum Warning {
    CallUndeclaredFunc(String),
}

impl fmt::Display for Warning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Warning::CallUndeclaredFunc(func) => write!(f, "Use of undeclared function {:?} (consider adding it to the API toml)", func),
        }
    }
}

impl std::error::Error for Warning {}
