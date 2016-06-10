package com.github.overmind.seaofnodes.ast

object Parser {
  def parseStmt(source: String) = {
    ParserInternal.stmtEnd.parse(source).get.value
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

  val ident = P(CharIn('a' to 'z')).repX(1).!
  val number = P(CharIn('0' to '9').repX(1)).!.map(_.toLong)
  val varE = ident.map(Var)
  val litE = number.map(Lit)
  val parenE = P("(" ~/ expr ~ ")")
  val factor: P[Expr] = P(varE | litE | parenE)
  val addSub = P(factor ~ (CharIn("+-").! ~/ factor).rep).map(mkBinaryOp)
  val cmp = P(addSub ~ (CharIn("<").! ~/ addSub).rep).map(mkBinaryOp)
  val expr: P[Expr] = cmp

  val ifS: P[Stmt] = P("if" ~/ expr ~/ "then" ~/ stmt ~/ "else" ~/ stmt).map(mkIf)
  val whileS = P("while" ~/ expr ~/ "do" ~/ stmt).map(mkWhile)
  val retS = P("ret" ~/ expr).map(Ret)
  val assignS = P(ident ~ "=" ~/ expr).map(mkAssign)
  val blockS = P("{" ~/ stmt.rep ~ "}").map(Stmt.begin)
  val stmt: P[Stmt] = P(ifS | whileS | blockS | retS | assignS)

  val stmtEnd = P(stmt ~ End)

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

  def mkAssign(cap: (String, Expr)): Stmt = {
    Assign(cap._1, cap._2)
  }
}

