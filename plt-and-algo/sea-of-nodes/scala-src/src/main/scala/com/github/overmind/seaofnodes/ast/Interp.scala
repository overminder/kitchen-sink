package com.github.overmind.seaofnodes.ast

import com.github.overmind.seaofnodes.ast.BinaryOp._

object Interp {
  type Env = Map[String, Value]

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
      case Assign(v, e) => v match {
        case LVar(v) =>
          env + (v -> evalExpr(env, e))
        case LIndex(base, index) =>
          evalExpr(env, base).setAt(evalExpr(env, index), evalExpr(env, e))
          env
      }
      case If(cond, t, f) =>
        if (evalExpr(env, cond).asBoolean) {
          execStmt(env, t)
        } else {
          execStmt(env, f)
        }
      case While(cond, body) =>
        var env_ = env
        while (evalExpr(env_, cond).asBoolean) {
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
      case Lit(lit) => LongValue(lit)
      case LVar(v) => env.getOrElse(v, throw UndefinedVar(env, v))
      case LIndex(base, index) => evalExpr(env, base).at(evalExpr(env, index))
      case AllocArray(len) => ArrayValue.create(len)
    }
  }

  def denoteOp(op: BinaryOp): (Value, Value) => Value = {
    op match {
      case Add => _ + _
      case Sub => _ - _
      case LessThan => (lhs, rhs) => lhs < rhs
    }
  }

  val emptyEnv: Env = Map.empty

  case class ReturnFrom(env: Env, value: Value) extends Exception
  case class UndefinedVar(env: Env, name: String) extends Exception
  case class DidntReturn(env: Env) extends Exception
}
