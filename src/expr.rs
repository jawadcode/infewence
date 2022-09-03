pub type Ident = String;

/// A lambda calculus expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expr {
    /// References a variable which is in scope
    Var(Ident),
    /// A literal expression, e.g. `123` or `false`
    Lit(Lit),
    /// A function application, usually represented in the form: `fun arg` where `fun` is called
    /// with `arg`
    App { fun: Box<Self>, arg: Box<Self> },
    /// A function abstraction, usually represented in the form: `λarg. body`, i.e. an anonymous
    /// function which takes in `arg` and returns `body`
    Abs { arg: Ident, body: Box<Self> },
    /// A let-binding, usually represented in the form: `let name = value in body`, where a new
    /// scope is introduced which contains a variable `name` with the value `body` for the
    /// expression `body`
    Let {
        name: Ident,
        value: Box<Self>,
        body: Box<Self>,
    },
}

/// A literal expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Lit {
    /// An integer literal, e.g. `123`
    Int(i64),
    /// A boolean literal: `true` or `false`
    Bool(bool),
}
