package com.github.overmind.seaofnodes

// A low-level imperative AST.
object Ast {
  import Stmt._
  import Expr._
  import BinaryOp._

  type Env = Map[String, Value]
  type Value = Long

  def execRootStmt(s: Stmt): Value = {
    try {
      throw DidntReturn(execStmt(emptyEnv, s))
    } catch {
      case ReturnFrom(_, v) => v
    }
  }

  def execStmt(env: Env, s: Stmt): Env = {
    s match {
      case Begin(ss) => ss.foldLeft(env)(execStmt)
      case Assign(v, e) => env + (v -> evalExpr(env, e))
      case If(cond, t, f) =>
        if (Value.isTruthy(evalExpr(env, cond))) {
          execStmt(env, t)
        } else {
          execStmt(env, f)
        }
      case While(cond, body) =>
        var env_ = env
        while (Value.isTruthy(evalExpr(env_, cond))) {
          env_ = execStmt(env_, body)
        }
        env_
      case Ret(e) =>
        throw ReturnFrom(env, evalExpr(env, e))
    }
  }

  def evalExpr(env: Env, e: Expr): Value = {
    e match {
      case Binary(op, lhs, rhs) => denoteOp(op)(evalExpr(env, lhs), evalExpr(env, rhs))
      case Lit(lit) => lit
      case Var(v) => env.getOrElse(v, throw UndefinedVar(env, v))
    }
  }

  def denoteOp(op: BinaryOp): (Value, Value) => Value = {
    op match {
      case Add => _ + _
      case Sub => _ - _
      case LessThan => (lhs, rhs) => if (lhs < rhs) { 1 } else { 0 }
    }
  }

  val emptyEnv: Env = Map.empty

  sealed trait Stmt

  case class ReturnFrom(env: Env, value: Value) extends Exception
  case class UndefinedVar(env: Env, name: String) extends Exception
  case class DidntReturn(env: Env) extends Exception

  object Stmt {
    case class Begin(ss: Array[Stmt]) extends Stmt
    case class Assign(v: String, e: Expr) extends Stmt
    case class If(cond: Expr, t: Stmt, f: Stmt) extends Stmt
    case class While(cond: Expr, body: Stmt) extends Stmt
    case class Ret(e: Expr) extends Stmt

    def begin(ss: Stmt*) = Begin(ss.toArray)
  }

  sealed trait Expr

  object Expr {
    case class Lit(v: Long) extends Expr
    case class Var(v: String) extends Expr
    case class Binary(op: BinaryOp, lhs: Expr, rhs: Expr) extends Expr

    def add(lhs: Expr, rhs: Expr) = Binary(BinaryOp.Add, lhs, rhs)
    def sub(lhs: Expr, rhs: Expr) = Binary(BinaryOp.Sub, lhs, rhs)
    def lessThan(lhs: Expr, rhs: Expr) = Binary(BinaryOp.LessThan, lhs, rhs)
  }

  object Value {
    def isTruthy(v: Value): Boolean = v != 0L
  }

  sealed trait BinaryOp

  object BinaryOp {
    case object Add extends BinaryOp
    case object Sub extends BinaryOp
    case object LessThan extends BinaryOp
  }

  object Sample {
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
  }

}

