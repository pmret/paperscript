use std::fmt;

#[derive(Debug, Clone)]
pub enum Warning {
    VarRedeclaration { var_name: String, pos: (usize, usize) },
}

impl fmt::Display for Warning {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl std::error::Error for Warning {}
