package com.github.overmind.seaofnodes.ast

object Samples {
  import Stmt._
  import Expr._
  import BinaryOp._

  val loopSum = begin(
    Assign("s", Lit(0)),
    Assign("n", Lit(10)),
    While(Binary(LessThan, Lit(0), Var("n")),
      begin(
        Assign("s", add(Var("s"), Var("n"))),
        Assign("n", sub(Var("n"), Lit(1)))
      )
    ),
    Ret(Var("s"))
  )

  val ifs = begin(
    Assign("a", Lit(0)),
    Assign("b", Lit(1)),
    If(Binary(LessThan, Lit(0), Var("a")),
      Assign("b", Lit(1)),
      If(Binary(LessThan, Lit(1), Var("a")),
        Assign("b", Lit(2)),
        Assign("b", Lit(3)))
    ),
    Ret(Var("b"))
  )

  val unreachableCode = begin(
    Ret(Lit(0)),
    Ret(Lit(1)),
    Ret(Lit(2))
  )

  val unreachableCodeInLoop = begin(
    Assign("s", Lit(0)),
    Assign("n", Lit(10)),
    While(Binary(LessThan, Lit(0), Var("n")),
      begin(
        Assign("s", add(Var("s"), Var("n"))),
        Assign("n", sub(Var("n"), Lit(1))),
        Ret(Var("s"))
      )
    ),
    Ret(Var("s"))
  )

  val returns = begin(
    Assign("a", Lit(0)),
    Assign("b", Lit(1)),
    If(Binary(LessThan, Lit(0), Var("a")),
      Ret(Var("b")),
      If(Binary(LessThan, Lit(1), Var("a")),
        Ret(Var("b")),
        Ret(Var("b")))
    )
  )

  val whileIf = begin(
    Assign("s", Lit(0)),
    Assign("n", Lit(10)),
    While(Binary(LessThan, Lit(0), Var("n")),
      begin(
        Assign("s", add(Var("s"), Var("n"))),
        Assign("n", sub(Var("n"), Lit(1))),
        If(Binary(LessThan, Var("n"), Var("s")),
          Assign("s", add(Var("s"), Var("n"))),
          Assign("n", sub(Var("n"), Lit(1))))
      )
    ),
    Ret(Var("s"))
  )

}
