use infer::TypeEnv;
use print::ToSexpr;

mod expr;
mod infer;
mod print;

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

fn main() {
    // \a -> \x -> a x x
    let expr = exp!(abs
        "a" => exp!(abs
            "x" => exp!(app
                exp!(app
                    exp!(var "a"),
                    exp!(var "x")),
                exp!(var "x"))));
    println!("Expression:\n{}\n", expr.to_sexpr());

    let env = TypeEnv::default();
    let ty = env.infer_type(&expr);
    println!("Type:\n{}", ty.to_sexpr());
}
