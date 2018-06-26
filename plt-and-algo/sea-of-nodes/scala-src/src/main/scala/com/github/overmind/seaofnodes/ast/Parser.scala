package com.github.overmind.seaofnodes.ast

object Parser {
  def parseStmt(source: String) = {
    ParserInternal.stmtEnd.parse(source).get.value
  }

  def parseFuncDef(source: String) = {
    ParserInternal.funcDefEnd.parse(source).get.value
  }
}

private object ParserInternal {
  import fastparse.WhitespaceApi
  val White = WhitespaceApi.Wrapper {
    import fastparse.all._
    NoTrace(CharIn("\n\r\t ").rep)
  }
  import fastparse.noApi._
  import White._

  val (ident, number) = {
    import fastparse.all._
    val alpha = P(CharIn('a' to 'z') | CharIn('A' to 'Z'))
    val digit = P(CharIn('0' to '9'))

    val ident = P(alpha ~ (alpha | digit).rep).!
    val number = P(digit.rep(1)).!.map(_.toLong)

    (ident, number)
  }
  // val ident = P(alpha).repX(1).!
  val varE: P[Loc] = ident.map(LVar)
  val litE: P[Expr] = number.map(Lit)
  val parenE = P("(" ~/ expr ~ ")")
  val factor: P[Expr] = P(varE | litE | parenE)

  // Complex exprs
  val funCall = P(factor ~ (("(" ~/ expr ~/ ")").map(mkCall) |
    ("[" ~/ expr ~/ "]").map(mkIndex)).rep).map(mkFold)
  val addSub = P(funCall ~ (CharIn("+-").! ~/ funCall).rep).map(mkBinaryOp)
  val cmp = P(addSub ~ (CharIn("<").! ~/ addSub).rep).map(mkBinaryOp)
  val expr: P[Expr] = cmp

  val ifS: P[Stmt] = P("if" ~/ expr ~/ "then" ~/ stmt ~/ "else" ~/ stmt).map(mkIf)
  val whileS = P("while" ~/ expr ~/ "do" ~/ stmt).map(mkWhile)
  val retS = P("ret" ~/ expr).map(Ret)
  val assignS = P(funCall ~ "=" ~/ expr).map(mkAssign)
  val blockS = P("{" ~/ stmt.rep ~ "}").map(Stmt.begin)
  val stmt: P[Stmt] = P(ifS | whileS | blockS | retS | assignS)

  val stmtEnd = P(stmt ~ End)

  val funcDef = P("(" ~/ ident.rep ~/ ")" ~/ "=>" ~/ stmt).map(FuncDef.tupled)
  val funcDefEnd = P(funcDef ~ End)

  def mkCall(args: Expr)(base: Expr): Expr = {
    (args, base) match {
      case (Lit(len), LVar("newArray")) =>
        AllocArray(len.toInt)
      case _ =>
        sys.error(s"Unknown call: $args, $base")
    }
  }

  def mkIndex(index: Expr)(base: Expr): Expr = {
    LIndex(base, index)
  }

  def mkFold(tree: (Expr, Seq[Expr => Expr])): Expr = {
    tree._2.foldLeft(tree._1) { case (base, op) =>
      op(base)
    }
  }

  def mkBinaryOp(tree: (Expr, Seq[(String, Expr)])): Expr = {
    tree match {
      case (lhs, rhss) =>
        rhss.foldLeft(lhs) { case (lhs, (op, rhs)) =>
          op match {
            case "+" => Expr.add(lhs, rhs)
            case "-" => Expr.sub(lhs, rhs)
            case "<" => Expr.lessThan(lhs, rhs)
            case _ => sys.error(s"Unknown op: $op")
          }
        }
    }
  }

  def mkIf(cap: (Expr, Stmt, Stmt)): Stmt = {
    If(cap._1, cap._2, cap._3)
  }

  def mkWhile(cap: (Expr, Stmt)): Stmt = {
    While(cap._1, cap._2)
  }

  def mkAssign(cap: (Expr, Expr)): Stmt = {
    // XXX unsafe
    Assign(cap._1.asInstanceOf[Loc], cap._2)
  }
}

