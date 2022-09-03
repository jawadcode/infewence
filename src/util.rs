#[macro_export]
macro_rules! exp {
    (var $ident:literal) => {
        $crate::expr::Expr::Var($ident.to_string())
    };
    (lit $lit:expr) => {
        $crate::expr::Expr::Lit($lit)
    };
    (app $fun:expr, $arg:expr) => {
        $crate::expr::Expr::App {
            fun: Box::new($fun),
            arg: Box::new($arg),
        }
    };
    (abs $ident:literal => $body:expr) => {
        $crate::expr::Expr::Abs {
            arg: $ident.to_string(),
            body: Box::new($body),
        }
    };
    (let $ident:literal $value:expr; $body:expr) => {
        $crate::expr::Expr::Let {
            name: $ident.to_string(),
            value: Box::new($value),
            body: Box::new($body),
        }
    };
}

#[macro_export]
macro_rules! ty {
    (Var $ident:literal) => {
        $crate::infer::Type::Var($ident.to_string())
    };
    (Int) => {
        $crate::infer::Type::Int
    };
    (Bool) => {
        $crate::infer::Type::Bool
    };
    (Fun $in:expr => $out:expr) => {
        $crate::infer::Type::Fun {
            in_: Box::new($in),
            out: Box::new($out),
        }
    };
}
