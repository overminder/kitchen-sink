package com.github.overmind.seaofnodes.ast

sealed trait Stmt

object Stmt {
  def begin(ss: Stmt*) = Begin(ss)
}

case class Begin(ss: Seq[Stmt]) extends Stmt
case class Assign(v: Loc, e: Expr) extends Stmt
object Assign {
  def apply(v: String, e: Expr): Stmt = {
    Assign(LVar(v), e)
  }
}
case class If(cond: Expr, t: Stmt, f: Stmt) extends Stmt
case class While(cond: Expr, body: Stmt) extends Stmt
case class Ret(e: Expr) extends Stmt

case class FuncDef(args: Seq[String], body: Stmt)