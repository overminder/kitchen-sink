package com.github.overmind.seaofnodes.ast

object Samples {
  import Stmt._
  import Expr._
  import BinaryOp._

  val loopSum = begin(
    Assign("s", Lit(0)),
    Assign("n", Lit(10)),
    While(Binary(LessThan, Lit(0), LVar("n")),
      begin(
        Assign("s", add(LVar("s"), LVar("n"))),
        Assign("n", sub(LVar("n"), Lit(1)))
      )
    ),
    Ret(LVar("s"))
  )

  val ifs = begin(
    Assign("a", Lit(0)),
    Assign("b", Lit(1)),
    If(Binary(LessThan, Lit(0), LVar("a")),
      Assign("b", Lit(1)),
      If(Binary(LessThan, Lit(1), LVar("a")),
        Assign("b", Lit(2)),
        Assign("b", Lit(3)))
    ),
    Ret(LVar("b"))
  )

  val unreachableCode = begin(
    Ret(Lit(0)),
    Ret(Lit(1)),
    Ret(Lit(2))
  )

  val unreachableCodeInLoop = begin(
    Assign("s", Lit(0)),
    Assign("n", Lit(10)),
    While(Binary(LessThan, Lit(0), LVar("n")),
      begin(
        Assign("s", add(LVar("s"), LVar("n"))),
        Assign("n", sub(LVar("n"), Lit(1))),
        Ret(LVar("s"))
      )
    ),
    Ret(LVar("s"))
  )

  val returns = begin(
    Assign("a", Lit(0)),
    Assign("b", Lit(1)),
    If(Binary(LessThan, Lit(0), LVar("a")),
      Ret(LVar("b")),
      If(Binary(LessThan, Lit(1), LVar("a")),
        Ret(LVar("b")),
        Ret(LVar("b")))
    )
  )

  val whileIf = begin(
    Assign("s", Lit(0)),
    Assign("n", Lit(10)),
    While(Binary(LessThan, Lit(0), LVar("n")),
      begin(
        Assign("s", add(LVar("s"), LVar("n"))),
        Assign("n", sub(LVar("n"), Lit(1))),
        If(Binary(LessThan, LVar("n"), LVar("s")),
          Assign("s", add(LVar("s"), LVar("n"))),
          Assign("n", sub(LVar("n"), Lit(1))))
      )
    ),
    Ret(LVar("s"))
  )

}
