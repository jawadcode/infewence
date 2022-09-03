use crate::expr::{Expr, Lit};
use crate::infer::Type;

pub trait ToSexpr {
    fn to_sexpr(&self) -> String;
}

impl ToSexpr for Expr {
    fn to_sexpr(&self) -> String {
        let mut buffer = String::new();

        match self {
            Expr::Var(var) => buffer += var,
            Expr::Lit(lit) => buffer += &lit.to_sexpr(),
            Expr::App { fun, arg } => {
                buffer.push('(');
                buffer += &fun.to_sexpr();
                buffer.push(' ');
                buffer += &arg.to_sexpr();
                buffer.push(')');
            }
            Expr::Abs { arg, body } => {
                buffer += "(fun [";
                buffer += arg;
                buffer += "] ";
                buffer += &body.to_sexpr();
                buffer.push(')');
            }
            Expr::Let { name, value, body } => {
                buffer += "(let ";
                buffer.push('[');
                buffer += name;
                buffer.push(' ');
                buffer += &value.to_sexpr();
                buffer += "] ";
                buffer += &body.to_sexpr();
                buffer.push(')');
            }
        }

        buffer
    }
}

impl ToSexpr for Lit {
    fn to_sexpr(&self) -> String {
        match self {
            Lit::Int(int) => int.to_string(),
            Lit::Bool(b) => b.to_string(),
        }
    }
}

impl ToSexpr for Type {
    fn to_sexpr(&self) -> String {
        let mut buffer = String::new();

        match self {
            Type::Var(var) => buffer += var,
            Type::Int => buffer += "Int",
            Type::Bool => buffer += "Bool",
            Type::Fun { in_, out } => {
                buffer += "(Fun ";
                buffer += &in_.to_sexpr();
                buffer.push(' ');
                buffer += &out.to_sexpr();
                buffer.push(')');
            }
        }

        buffer
    }
}
