package com.github.overmind.seaofnodes.ast

sealed trait Expr

case class Lit(v: Long) extends Expr
case class Var(v: String) extends Expr
case class Binary(op: BinaryOp, lhs: Expr, rhs: Expr) extends Expr

case class AllocArray(n: Int) extends Expr
case class ReadArray(base: Expr, index: Expr) extends Expr

object Expr {
  def add(lhs: Expr, rhs: Expr) = Binary(BinaryOp.Add, lhs, rhs)
  def sub(lhs: Expr, rhs: Expr) = Binary(BinaryOp.Sub, lhs, rhs)
  def lessThan(lhs: Expr, rhs: Expr) = Binary(BinaryOp.LessThan, lhs, rhs)
}

sealed trait BinaryOp

object BinaryOp {
  case object Add extends BinaryOp
  case object Sub extends BinaryOp
  case object LessThan extends BinaryOp
}
