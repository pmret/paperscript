use std::collections::HashMap;

use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct Api {
    pub functions: HashMap<String, Function>,
    pub scripts: HashMap<String, Script>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    #[serde(default)]
    pub namespace: bool,

    pub args: Option<Vec<Arg>>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Script {
    #[serde(default)]
    pub namespace: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Arg {
    pub name: String,

    #[serde(rename = "type")]
    pub datatype: Datatype,

    #[serde(default)]
    pub out: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
#[serde(rename_all = "snake_case")]
pub enum Datatype {
    Int,
    Float,
    Const,
    Bool,
}

impl Api {
    pub fn union(&mut self, other: Api) {
        for (name, function) in other.functions {
            self.functions.insert(name, function);
        }
        for (name, script) in other.scripts {
            self.scripts.insert(name, script);
        }
    }
}
