package com.github.overmind.seaofnodes

import java.io.FileWriter

import com.github.overmind.seaofnodes.hir._
import com.github.overmind.seaofnodes.hir.nodes.Node

import scala.io.Source

object Main {
  def interpAst(s: ast.Stmt): Unit = {
    val res = ast.Interp.execRootStmt(s)
    println(s"res: $res")
  }

  def buildGraph(s: ast.Stmt, name: String): Unit = {
    // Opt.simplifyControl(entry.successor.asInstanceOf[RegionNode], builder)
    // println(s"interp($name) => ${Graph.interp(entry)}")

    val g = GraphFromAst.build(s)
    // Opt.simplifyControl(g.entry, g)
    renderNodeToDot(g.entry, name)
    println(s"Interp => ${Interp.interp(g.entry)}")

    // val lgb = lir.GraphBuilder(entry)
    // val lg = lgb.build()
    // println(lg)
  }

  def writeFile(path: String, content: String): Unit = {
    new FileWriter(path).append(content).close()
  }

  def readFile(path: String): String = {
    Source.fromFile(path).mkString
  }

  def renderNodeToDot(s: Node, name: String): Unit = {
    writeFile(s"dots/$name.dot", DotFromNode.gen(name, s))
  }

  def main(args: Array[String]): Unit = {
    val fileName = if (args.length == 0) {
      "ast-src/fibo-iter.ast"
    } else {
      args(0)
    }
    // buildShallowRegion(Ast.Sample.returns)
    val prog = ast.Parser.parseStmt(readFile(fileName))
    println(s"AST: $prog")
    buildGraph(prog, "loopSum")
  }
}