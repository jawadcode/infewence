mod expr;
mod infer;
mod print;
mod util;

use expr::Expr;
use infer::{Type, TypeEnv};
use print::ToSexpr;

use crate::expr::Lit;

struct Test {
    name: &'static str,
    expr: Expr,
    expected: Type,
}

impl Test {
    fn test(&self) {
        let got = TypeEnv::default().infer_type(&self.expr);
        println!("\x1b[1;32m{}\x1b[0m:", self.name);
        println!("  Expr:     {}", self.expr.to_sexpr());
        println!("  Expected: {}", self.expected.to_sexpr());
        println!("  Got:      {}\n", got.to_sexpr());
        assert_eq!(self.expected, got);
    }
}

fn main() {
    let tests = [
        Test {
            name: "Idiot",
            expr: exp!(abs "x" =>
                       exp!(var "x")),
            expected: ty!(Fun ty!(Var "'t0") => ty!(Var "'t0")),
        },
        Test {
            name: "Kestrel",
            expr: exp!(abs "x" =>
                       exp!(abs "y" =>
                            exp!(var "x"))),
            expected: ty!(Fun
                          ty!(Var "'t0") =>
                          ty!(Fun
                              ty!(Var "'t1") =>
                              ty!(Var "'t0"))),
        },
        Test {
            name: "Bluebird",
            expr: exp!(abs "f" => 
                       exp!(abs "g" =>
                            exp!(abs "x" =>
                                 exp!(app exp!(var "f"),
                                      exp!(app exp!(var "g"),
                                           exp!(var "x")))))),
            expected: ty!(Fun
                          ty!(Fun
                              ty!(Var "'t4") =>
                              ty!(Var "'t3")) =>
                          ty!(Fun
                              ty!(Fun
                                  ty!(Var "'t2") =>
                                  ty!(Var "'t4")) =>
                              ty!(Fun
                                  ty!(Var "'t2") =>
                                  ty!(Var "'t3")))),
        },
        Test {
            name: "Applicator",
            expr: exp!(abs "f" =>
                       exp!(abs "x" =>
                            exp!(app
                                 exp!(var "f"),
                                 exp!(var "x")))),
            // ((a -> b) -> (a -> b))
            expected: ty!(Fun
                          ty!(Fun
                              ty!(Var "'t1") =>
                              ty!(Var "'t2")) =>
                          ty!(Fun
                              ty!(Var "'t1") =>
                              ty!(Var "'t2"))),
        },
        Test {
            name: "Let Idiot - Int",
            expr: exp!(let
                       "id"
                       exp!(abs "x" =>
                            exp!(var "x"));
                       exp!(app
                            exp!(var "id"),
                            exp!(lit Lit::Int(42)))),
            expected: Type::Int,
        },
        Test {
            name: "Let Idiot - Bool",
            expr: exp!(let
                       "id"
                       exp!(abs "x" =>
                            exp!(var "x"));
                       exp!(app
                            exp!(var "id"),
                            exp!(lit Lit::Bool(true)))),
            expected: Type::Bool,
        },
        Test {
            name: "Let Kestrel",
            expr: exp!(let
                       "const"
                       exp!(abs "x" =>
                            exp!(abs "y" =>
                                 exp!(var "x")));
                       exp!(app
                            exp!(var "const"),
                            exp!(lit Lit::Int(42)))),
            expected: ty!(Fun
                          ty!(Var "'t4") =>
                          ty!(Int)),
        },
    ];

    println!("Running tests\n");
    for test in tests {
        test.test();
    }
}
