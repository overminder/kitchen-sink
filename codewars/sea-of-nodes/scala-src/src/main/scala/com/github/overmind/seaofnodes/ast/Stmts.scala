package com.github.overmind.seaofnodes.ast

sealed trait Stmt

object Stmt {
  def begin(ss: Stmt*) = Begin(ss)
}

case class Begin(ss: Seq[Stmt]) extends Stmt
case class Assign(v: String, e: Expr) extends Stmt
case class If(cond: Expr, t: Stmt, f: Stmt) extends Stmt
case class While(cond: Expr, body: Stmt) extends Stmt
case class Ret(e: Expr) extends Stmt
case class WriteArray(base: Expr, index: Expr, value: Expr) extends Stmt
