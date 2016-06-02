pub use self::Stmt::*;
pub use self::Expr::*;
pub use self::ArithOp::*;

#[derive(Debug)]
pub enum Stmt {
    Move(Name, Expr),
    Ret(Expr),
    Seq(Vec<Stmt>),
    If(Expr, BStmt, BStmt),
    While(Expr, BStmt),
}

#[derive(Debug)]
pub enum Expr {
    Arith(ArithOp, BExpr, BExpr),
    Var(Name),
    Lit(i64),
}

#[derive(Debug, Copy, Clone)]
pub enum ArithOp {
    Add,
    Sub,
    Lt,
}

pub type Name = String;
pub type BStmt = Box<Stmt>;
pub type BExpr = Box<Expr>;

pub struct Sample;

fn s(s: &str) -> String {
    s.to_owned()
}

fn v(s_: &str) -> BExpr {
    Box::new(Var(s(s_)))
}

fn l(v: i64) -> BExpr {
    Box::new(Lit(v))
}

impl Sample {
    pub fn sum() -> Stmt {
        Seq(vec![
            Move(s("n"), *l(0)),
            Move(s("s"), *l(10)),

            While(Arith(Lt, l(0), v("n")), Box::new(Seq(vec![
                Move(s("s"), Arith(Add, v("s"), v("n"))),
                Move(s("n"), Arith(Sub, v("n"), l(1))),
            ]))),

            Ret(*v("s")),
        ])
    }
}
