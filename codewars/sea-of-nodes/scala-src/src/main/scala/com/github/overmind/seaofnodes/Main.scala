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
    val builder = GraphFromAst.Builder(s)
    builder.buildRoot()
    // Opt.simplifyControl(entry.successor.asInstanceOf[RegionNode], builder)
    // println(s"interp($name) => ${Graph.interp(entry)}")

    renderNodeToDot(builder.end, name)

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
    writeFile(s"dots/$name.dot", DotFromNode.gen(name, s, showBackedges = true))
  }

  def main(args: Array[String]): Unit = {
    // buildShallowRegion(Ast.Sample.returns)
    val prog = ast.Parser.parseStmt(readFile(args(0)))
    println(s"AST: $prog")
    buildGraph(prog, "loopSum")
  }
}